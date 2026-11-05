# Milnor, proof by proof

*Every proof of the book, of its Appendix and of its seventeen problems, told as the Lean 4 formalization actually carries it out. Each step carries a tag naming the declaration that proves it; the concordance at the end gives every cited declaration with its line and its exact formal statement.*

## Prologue. What we have done

Between the seventh and the seventeenth of September 2026, every numbered result of John Milnor's *Topology from the Differentiable Viewpoint*, the consequence of the Appendix on one-manifolds that the book uses, and all seventeen problems at the end of the book were proved in the Lean 4 proof assistant, on top of the Mathlib library. On the twenty-eighth of September twenty-seven further results were added: first the side remarks and unnumbered lemmas that the first pass had set aside, among them Milnor's Lemmas 2, 4 and 5 of §6, the Euler number of the sphere, and the classification of the maps of a non-orientable manifold by the degree modulo 2; and then, in nine stages, the one theorem of the book that had been out of reach, the classification of one-manifolds, which in turn deleted the last superfluous hypothesis from that mod 2 theorem. The proofs occupy 62,849 lines in 176 files. Lean's kernel has checked every line. No step is left unproved, and the 175 principal theorems listed in the project's test file depend only on the three standard axioms of Mathlib: propositional extensionality, the axiom of choice, and the soundness of quotients.

The work was divided in the obvious way. A mathematician read, questioned and signed off the statements, always in ordinary mathematical language and never in Lean. The formal proofs were written by Claude, working with many helper agents in parallel, each given a precise mathematical specification and each checked by the Lean kernel. Where a specification was wrong, the machine refused it, and the refusal was usually instructive. Several of the hidden hypotheses recorded in this book were found exactly that way.

Three companion texts now accompany the formal proof.

- **The retelling** (`Exposition/Chapter1.md` to `Chapter8.md` and `Appendix.md`) tells Milnor's book for a curious reader, with a physical question at the start of each chapter and complete proofs.
- **The verified edition** (`Exposition/Verification.md`) is the audit record. It lists which statements are verified, restates each one in prose, flags every hidden hypothesis and deviation, and labels the results V1.1 to V8.17′. Its sign-off list is where the mathematician confirms that a formal statement says what Milnor means.
- **This book, the proof in words**, goes one level deeper. It translates the formal proofs themselves into mathematics that can be read with pleasure. Every step of substance carries a trace tag naming the Lean declaration that proves it, so that any sentence can be checked against the source.

### The formal proof in numbers

| Part of the book | Files | Lines of Lean |
|:--|--:|--:|
| §1 Smooth manifolds, the fundamental theorem of algebra | 5 | 1,304 |
| §2 Regular values, manifolds with boundary, Brouwer | 10 | 2,247 |
| §3 Sard's theorem | 6 | 1,112 |
| §4 The degree modulo 2 | 5 | 894 |
| §5 Orientation and the Brouwer degree | 13 | 3,096 |
| §6 Vector fields and the Poincaré–Hopf theorem | 26 | 7,153 |
| §7 Framed cobordism, the Pontryagin construction, the Hopf theorem | 68 | 19,823 |
| §8 The seventeen problems | 31 | 16,166 |
| Appendix: the classification of one-manifolds | 12 | 11,054 |
| **Total** | **176** | **62,849** |

The counts are by directory; a few files serve more than one chapter. The last two chapters are much larger than Milnor's text would suggest. Framed cobordism and the problems of §8 rely on constructions that the book compresses into a sentence: product neighbourhoods, gluing homotopies, orientations of preimages, linking numbers in the sphere. Each of these had to be built.

Of the total, 17,546 lines are the work of the twenty-eighth of September: 142 in §2, 2,089 in §6, 6,039 in §7 and 9,276 in the Appendix. The proportions measure how much a sentence can hide. Milnor's mod 2 remark at the end of §7 is one clause of his text and a third of that figure, because it presupposes the notion of an orientable manifold, which existed neither in Mathlib nor in this project nor in the book; and the Appendix theorem, which Milnor proves in two pages, is more than half of it, and is the largest single addition the project has had.

### What the machine found

A formal proof cannot leave a hypothesis unstated, so the formalization is also a close reading of the book. The findings are gathered in the verified edition. The most interesting of them recur in this book, where one can see exactly where in the proof each one is needed.

- **Hidden hypotheses.** Milnor's manifolds live in Euclidean space, so they are automatically Hausdorff and second countable. In the formal setting these become explicit assumptions wherever they are used: Brown's theorem needs second countability, finiteness of preimages needs points to be closed, and the degree needs compact domains and connected targets. Some of §8's problems carry hypotheses the book does not state, and only some of these are genuinely needed. The linking number of Problem 13 needs total dimension $k > 0$: for $k = 0$ the target $S^0$ is not connected, and the degree is not defined in the book's sense. The linking number in the sphere needs both manifolds of positive dimension: for a point and a great sphere the answer depends on where one projects from, a standard example that is not itself formalized. Accordingly the Hopf invariant is formalized for $p \ge 2$, where the fibres have positive dimension. Other hypotheses are only assumed by the formal statements. Those of the intersection product of framed cobordism classes assume $p, q \ge 1$, although transverse representatives and their uniqueness need only $p \ge 1$.
- **Different routes.** The sphere $S^2$ of Milnor's proof of the fundamental theorem of algebra is replaced by the Riemann sphere $\mathbb C \cup \{\infty\}$. In §6, Milnor's appeal to his Lemma 2, that an orientation-preserving diffeomorphism of $\mathbb R^m$ is smoothly isotopic to the identity, is replaced by a direct computation of signs; the lemma itself is now proved as well (V6.12), and nothing in the development uses it. The index of a vector field on a submanifold is defined through the extension to a tubular neighbourhood, and Milnor's own definition through a chart is then formalized beside it and shown to agree at a non-degenerate zero (V6.14). A framed cobordism is a submanifold of $M \times \mathbb R$ with product ends rather than a manifold with boundary. Homotopies are smooth maps on $X \times \mathbb R$. The consequence of the Appendix, that a compact one-manifold has an even number of boundary points, is proved twice over: once for topological one-manifolds, where arc length is replaced by monotone transitions and a finite induction, which is stronger than the book (V.A); and once as Milnor draws it, from the classification of one-manifolds, which is now proved in full, in his own four cases and with his arc-length parametrizations (V.J).
- **One notion had to be invented.** Milnor closes §7 with a remark that turns on an orientation-reversing loop. Orientability of a manifold existed neither in Mathlib nor in this project nor in the book, and its characterization by loops is *false* for the book's own notion of an orientation until the loops are made to run through balls (V7.18, V7.19). The clause cost more lines than the whole of Milnor's §5. What made it possible at all is a second finding: the framed machinery of §7 is almost entirely orientation-free already, and the orientation enters in exactly one definition, the sign of a frame, where it splits off as a factor depending on the point and not on the frame (V7.20).
- **One generalization needs an extra hypothesis.** In Problem 14 a), the formal statement for two different maps $f \ne g$ assumes that the preimages $g^{-1}(y)$ and $f^{-1}(z)$ are disjoint. Without that assumption, moving $y$ can push $g^{-1}(y)$ through $f^{-1}(z)$ and change the linking number. This is an informal observation; no counterexample is formalized. Milnor's own statement, for a single map, holds as he states it.
- **One value.** With the book's conventions taken literally, the Hopf fibration has Hopf invariant $-1$, not $+1$ as Milnor states. The difference is a convention, and Part X shows exactly which conventions flip it.

What remains is two statements, both in §6, and the first of them cannot be written down at all: that the integer of Poincaré–Hopf is the Euler characteristic. Mathlib has no Euler characteristic of a space, no Betti numbers and no homology of a space whose ranks could be alternated, so $\chi(S^n) = 1 + (-1)^n$ is not a statement this library can express, although the integer itself is computed and equals $1 + (-1)^n$ (V6.15). That is a missing definition, not a missing proof, and Milnor does not prove it either; he refers to Hopf's theorem and to the literature. Beside it stands the agreement of the two definitions of the index at an arbitrary isolated zero (V6.14). At a non-degenerate zero the two are proved equal, which is what Milnor's Lemma 5 gives and all that the book uses; in general they are degrees of maps of spheres of *different* dimensions, so comparing them needs a suspension formula for the degree, which the book does not prove either. Nothing else is left. The classification theorem of the Appendix, which stood here until the twenty-eighth of September, is now proved in full, with all of Milnor's four cases and all six of their mutual exclusions: Part XII sets it out, and the last section of Part VII records the hypothesis its arrival deleted.

## Part 0. The formal definitions

This part makes the book self-contained. It defines every notion that the later parts use, exactly as the formal proof defines it, in ordinary mathematical language. Where a definition comes from Mathlib, its trace tag points into Mathlib's source, and those tags begin with `Mathlib/`. Where the project defines it, the tag points into the project's own files. The parts that follow add the special definitions of each chapter: linking numbers, the Hopf invariant, cohomotopy classes and so on. Everything they build on is here.

### 0.1 How to read this book

A Lean proof is a term that Lean's kernel type-checks against the statement. Nothing is taken on trust except the kernel and three axioms: propositional extensionality, the axiom of choice, and the soundness of quotients. When this book says that a statement is proved, it means three things: the declaration named in its trace tag exists, the displayed statement is its translation into mathematics, and the kernel accepted its proof. When the book says *how* a statement is proved, it describes the proof in the file, not the proof in Milnor's book and not a proof one might prefer. Where the two agree the text says so briefly, and where they differ it says how.

A trace tag such as ⟦Chapter7/Lemma2 · framedCobordant_of_regularValues⟧ names a file and a declaration in it. The path is relative to the folder `Milnor/` of the project, or to Mathlib when it begins with `Mathlib/`. The declaration proves, or defines, what the sentence to which the tag is attached says. Every tag has been checked mechanically: the file exists and declares that name. The **concordance** at the end lists every cited declaration with its line number. In the web edition it also shows the exact formal statement, so that a sentence of this book can be compared with the Lean it translates.

Results carry the labels V1.1, …, V8.17′ of the verified edition, so that one can move between the two texts: the verified edition says *what* is proved, this book says *how*. Theorems are named as Milnor names them. Some file names and docstrings of the project use an older lettering, and the parts point this out where it happens. For example, the file `ThmB.lean` holds Milnor's Theorem C of §7.

### 0.2 Spaces, derivatives and smoothness

Vector spaces are normed and, except in parts of Chapter 1 noted below, real. Most are finite-dimensional, and the book says so each time it matters, because the formal statements carry that assumption explicitly. The space $\mathbb R^n$ is the Euclidean space of functions $\{0, \dots, n-1\} \to \mathbb R$ with the norm $\|x\| = (\sum x_i^2)^{1/2}$ and the inner product $\langle x, y\rangle = \sum x_i y_i$ ⟦Mathlib/Analysis/InnerProductSpace/PiL2 · EuclideanSpace⟧. The formal text numbers coordinates from $0$. Some parts of this book number them from $1$, as is customary, and some keep the formal numbering; the north pole of a sphere is in every case the last standard basis vector.

A map $f : E \to F$ has **derivative** $L$ at $x$, a continuous linear map, when $f(x + h) = f(x) + L h + o(\|h\|)$ ⟦Mathlib/Analysis/Calculus/FDeriv/Defs · HasFDerivAt⟧. The formal derivative $Df(x)$ is this $L$ when it exists and $0$ otherwise ⟦Mathlib/Analysis/Calculus/FDeriv/Defs · fderiv⟧. The derivative *within* a set $s$ uses only increments that stay in $s$, which is how derivatives are taken at boundary points ⟦Mathlib/Analysis/Calculus/FDeriv/Defs · fderivWithin⟧. Within a set several linear maps may qualify, for instance at an isolated point of $s$; the formal definition then takes $0$ if $0$ qualifies and a chosen one otherwise. For the manifold derivative of §0.4 the set is the image of a model with corners (§0.3), which is convex with nonempty interior, and there the derivative within is unique ⟦Mathlib/Geometry/Manifold/IsManifold/Basic · ModelWithCorners.uniqueDiffOn⟧. A map is **of class $C^n$** when its derivatives up to order $n$ exist and are continuous, and **smooth** when this holds for all finite $n$ ⟦Mathlib/Analysis/Calculus/ContDiff/Defs · ContDiff⟧. At a point the notion is local and order by order: $f$ is smooth at $x$, within a set $s$, when for each finite $k$ it has continuous derivatives up to order $k$ on some neighbourhood of $x$ in $s \cup \{x\}$, the neighbourhood depending on $k$ ⟦Mathlib/Analysis/Calculus/ContDiff/Defs · ContDiffWithinAt⟧. So smoothness at every point of an open set is smoothness on it, but smoothness at one point gives no single neighbourhood on which $f$ is smooth. The same notions exist on a set and within a set at a point, and the book uses them without further comment. Mathlib writes smoothness as $C^\infty$ and reserves $C^\omega$ for analytic maps. From Chapter 2 on, manifolds carry $C^\infty$ structures and the main theorems concern $C^\infty$ maps; some auxiliary lemmas need less. Several results of Chapter 1 are proved for manifolds and maps of any order $n \ne 0$, analytic included, over $\mathbb R$ or $\mathbb C$; over $\mathbb C$ differentiability is complex differentiability, so the manifolds are complex manifolds.

Topological notions have their usual meaning. The book writes them out because the formal statements do: *Hausdorff*; *$T_1$*, which means that points are closed ⟦Mathlib/Topology/Separation/Basic · T1Space⟧; *first countable*, every point having a countable basis of neighbourhoods ⟦Mathlib/Topology/Bases · FirstCountableTopology⟧; *second countable*, a countable basis of open sets; *compact*; *preconnected*, which means not the union of two disjoint nonempty open sets; and *locally connected*, every neighbourhood of a point containing an open connected one ⟦Mathlib/Topology/Connected/LocallyConnected · LocallyConnectedSpace⟧. Connected means preconnected and nonempty. Many formal statements assume only preconnectedness, which also admits the empty space. The **connected component** of $x$ is the union of all preconnected sets containing $x$ ⟦Mathlib/Topology/Connected/Basic · connectedComponent⟧. The component of $x$ *in a subset* $F$ is its component in the subspace $F$, and is empty when $x \notin F$ ⟦Mathlib/Topology/Connected/Basic · connectedComponentIn⟧. The distance from a point to a set is the infimum of the distances to its points ⟦Mathlib/Topology/MetricSpace/HausdorffDistance · Metric.infDist⟧. The **one-point compactification** $X \cup \{\infty\}$ of a space $X$ has as open sets the open sets of $X$ and the sets $U \ni \infty$ such that $U \cap X$ is open and $X \setminus U$ is compact ⟦Mathlib/Topology/Compactification/OnePoint/Basic · OnePoint⟧; Chapter 1 uses $\mathbb C \cup \{\infty\}$.

Some linear algebra is used throughout. The **dimension** of $E$ is its rank as a natural number, set to $0$ when $E$ is infinite-dimensional ⟦Mathlib/LinearAlgebra/Dimension/Finrank · Module.finrank⟧; the statements that use it also assume finite dimension. A basis of $\mathbb R^p$ appears in two forms: as a linearly independent $p$-tuple, as in the Pontryagin construction (§0.9), or as Mathlib's bundled basis, whose vectors are indexed by $\{0, \dots, p-1\}$ ⟦Mathlib/LinearAlgebra/Basis/Defs · Module.Basis⟧. $GL^+(m)$ denotes the real $m \times m$ matrices of positive determinant; the formal proof works with such matrices directly, and joins each of them to the identity by a path of such matrices with smooth entries ⟦Chapter7/GLplus · exists_glPath⟧. The inner product of $\mathbb R^n$ gives the **orthogonal complement** $K^\perp = \{v : \langle u, v\rangle = 0 \text{ for all } u \in K\}$ of a subspace ⟦Mathlib/Analysis/InnerProductSpace/Orthogonal · Submodule.orthogonal⟧ and the **adjoint** $A^* : F \to E$ of a linear map $A : E \to F$ between such spaces, with $\langle A^*y, x\rangle = \langle y, Ax\rangle$ ⟦Mathlib/Analysis/InnerProductSpace/Adjoint · ContinuousLinearMap.adjoint⟧. The **gradient** $\nabla g(x)$ of a real function on a Euclidean space is the vector with $\langle \nabla g(x), h\rangle = dg_x(h)$ for all $h$, and $0$ where $g$ is not differentiable ⟦Mathlib/Analysis/Calculus/Gradient/Basic · gradient⟧. A continuous linear map is *invertible* when it is a bijection with continuous inverse ⟦Mathlib/Topology/Algebra/Module/Equiv · ContinuousLinearMap.IsInvertible⟧, which is automatic for bijections in finite dimension. A product $E \times F$ of normed spaces carries the norm $\max(\|x\|, \|y\|)$, not a Euclidean one ⟦Mathlib/Analysis/Normed/Group/Constructions · Prod.toNorm⟧; this is why Chapter 7 introduces an inner product on $\mathbb R^k \times \mathbb R$ by hand (§0.9).

Sard's theorem (Part II) uses Mathlib's measures. A measure assigns a value in $[0, \infty]$ to *every* subset: it is an outer measure that is countably additive on measurable sets ⟦Mathlib/MeasureTheory/Measure/MeasureSpaceDef · MeasureTheory.Measure⟧, so a subset of a null set is null, measurable or not. The measurable sets are those of a chosen σ-algebra, which Sard's theorem requires to be the **Borel** σ-algebra, generated by the open sets ⟦Mathlib/MeasureTheory/Constructions/BorelSpace/Basic · BorelSpace⟧. An **additive Haar measure** on a finite-dimensional space is a translation-invariant measure that is finite on compact sets and positive on nonempty open sets ⟦Mathlib/MeasureTheory/Group/Measure · Measure.IsAddHaarMeasure⟧; Lebesgue measure on $\mathbb R^n$ is one. The $d$-dimensional **Hausdorff measure** of a set is the limit, as $\delta \to 0$, of the infimum of $\sum_i (\operatorname{diam} U_i)^d$ over countable covers by sets $U_i$ of diameter at most $\delta$, with no normalizing constant ⟦Mathlib/MeasureTheory/Measure/Hausdorff · Measure.hausdorffMeasure⟧. The **Hausdorff dimension** of a set is the supremum of the $d \ge 0$ for which its $d$-dimensional Hausdorff measure is infinite ⟦Mathlib/Topology/MetricSpace/HausdorffDimension · dimH⟧. Without a normalizing constant, the $p$-dimensional Hausdorff measure agrees with Lebesgue measure on the space of functions $\{0, \dots, p-1\} \to \mathbb R$ with the maximum norm, and not, for $p \ge 2$, on Euclidean $\mathbb R^p$; that is why the measure estimate of Sard's theorem passes to the former space ⟦Chapter3/Basic · addHaar_eq_zero_of_dimH_lt_finrank⟧. A map is **Hölder** on $s$ with constant $C$ and exponent $r$ when $|f(x) - f(y)| \le C|x - y|^r$ for $x, y \in s$ ⟦Mathlib/Topology/MetricSpace/Holder · HolderOnWith⟧.

### 0.3 Manifolds

Mathlib's manifolds are abstract spaces covered by charts. The charts take values in a *model space*, which is where the difference between manifolds with and without boundary is encoded.

A **model with corners** is a map $I : H \to E$ from a topological space $H$ into a normed space $E$. It is a homeomorphism onto its image, and the image is convex with nonempty interior ⟦Mathlib/Geometry/Manifold/IsManifold/Basic · ModelWithCorners⟧. Many results are proved for an arbitrary model, often assumed *boundaryless* (defined below), and two models are used explicitly. The identity model has $H = E$ and $I = \mathrm{id}$ ⟦Mathlib/Geometry/Manifold/IsManifold/Basic · modelWithCornersSelf⟧. It is used for manifolds without boundary, which the formal texts call *boundaryless*: the image of the model is all of $E$ ⟦Mathlib/Geometry/Manifold/IsManifold/Basic · ModelWithCorners.Boundaryless⟧. The half-space model, used for manifolds with boundary, is the project's own. Its model space is $H = \{(t, z) \in \mathbb R \times Z : t \ge 0\}$, included in $\mathbb R \times Z$ ⟦Chapter2/Boundary · HalfSpace⟧ ⟦Chapter2/Boundary · halfSpaceModel⟧. A product of two models is a model for the product space ⟦Mathlib/Geometry/Manifold/IsManifold/Basic · ModelWithCorners.prod⟧, which is how $M \times N$ and $M \times \mathbb R$ become manifolds: the charts of $M \times N$ are the products of charts, its preferred chart at $(x, y)$ is the product of the preferred charts at $x$ and $y$ ⟦Mathlib/Geometry/Manifold/ChartedSpace · prodChartedSpace⟧, and it is a smooth manifold when $M$ and $N$ are ⟦Mathlib/Geometry/Manifold/IsManifold/Basic · IsManifold.prod⟧.

A **charted space** modelled on $H$ is a topological space $M$ with an *atlas*, a set of homeomorphisms from open subsets of $M$ onto open subsets of $H$. Formally each chart is an *open partial homeomorphism*: a pair of maps $e : M \to H$ and $e^{-1} : H \to M$, defined everywhere but meaningful only on an open *source* and an open *target*, which they map into each other, inversely to each other and continuously ⟦Mathlib/Topology/OpenPartialHomeomorph/Defs · OpenPartialHomeomorph⟧. It also has, for each point $x$, a *preferred chart* in the atlas whose domain contains $x$ ⟦Mathlib/Geometry/Manifold/ChartedSpace · ChartedSpace⟧. The preferred chart matters, because every derivative below is read in it.

A charted space is a **smooth manifold** when any two charts $e, e'$ of the atlas are smoothly compatible: the transition map $I \circ e' \circ e^{-1} \circ I^{-1}$ is smooth on the part of the image of $I$ where it is defined ⟦Mathlib/Geometry/Manifold/IsManifold/Basic · contDiffPregroupoid⟧ ⟦Mathlib/Geometry/Manifold/IsManifold/Basic · IsManifold⟧. (The definition carries an order of smoothness; "smooth manifold" means order $C^\infty$.) Nothing else is required: a manifold need not be Hausdorff, second countable or finite-dimensional unless a statement says so. The **extended chart** at $x$ is the preferred chart followed by $I$, a map from an open neighbourhood of $x$ in $M$ into $E$ ⟦Mathlib/Geometry/Manifold/IsManifold/ExtChartAt · extChartAt⟧. It is written $\varphi_x$ below. An open subset of a manifold is again a manifold, with the restricted charts ⟦Mathlib/Geometry/Manifold/HasGroupoid · Opens.instChartedSpace⟧. The formal proofs use this for maps that are smooth only on an open set, such as $v/|v|$ away from the zeros of a vector field $v$; orientations restrict to such open sets without change ⟦Chapter6/Opens · Orient.restrict⟧.

### 0.4 Smooth maps, derivatives and tangent spaces

Let $M$ and $N$ be manifolds with models $I : H \to E$ and $J : G \to F$. For $f : M \to N$ and $x \in M$, the **local representative** of $f$ at $x$ is
$$
f_x = \varphi_{f(x)} \circ f \circ \varphi_x^{-1},
$$
defined near $\varphi_x(x)$ on the image of $I$ ⟦Mathlib/Geometry/Manifold/IsManifold/ExtChartAt · writtenInExtChartAt⟧.

- $f$ is **smooth at $x$** when it is continuous at $x$ and $f_x$ is smooth at $\varphi_x(x)$ within the image of $I$, in the order-by-order sense of §0.2 ⟦Mathlib/Geometry/Manifold/ContMDiff/Defs · ContMDiffAt⟧ ⟦Mathlib/Geometry/Manifold/ContMDiff/Defs · contMDiffAt_iff⟧. Smoothness on a set, or within a set at a point, is defined in the same way through charts ⟦Mathlib/Geometry/Manifold/ContMDiff/Defs · contMDiffWithinAt_iff⟧. It is **smooth** when it is smooth at every point ⟦Mathlib/Geometry/Manifold/ContMDiff/Defs · ContMDiff⟧.
- $f$ is **differentiable at $x$** when it is continuous at $x$ and $f_x$ is differentiable within the image of $I$ at $\varphi_x(x)$ ⟦Mathlib/Geometry/Manifold/MFDeriv/Defs · MDifferentiableAt⟧ ⟦Mathlib/Geometry/Manifold/MFDeriv/Defs · mdifferentiableAt_iff⟧.
- The **tangent space** of $M$ at $x$ is, by definition, the vector space $E$ itself ⟦Mathlib/Geometry/Manifold/IsManifold/Basic · TangentSpace⟧.
- The **derivative** of $f$ at $x$ is the linear map $df_x : E \to F$ equal to the derivative of $f_x$ at $\varphi_x(x)$, taken within the image of $I$, when $f$ is differentiable at $x$. It is $0$ when $f$ is not ⟦Mathlib/Geometry/Manifold/MFDeriv/Defs · mfderiv⟧. The project restates it with the type "linear map from $E$ to $F$" and nothing else ⟦Chapter5/Orient · mfd⟧. For a boundaryless model the image of $I$ is all of $E$, and $df_x$ is simply the ordinary derivative of $f_x$.

Three remarks keep this definition honest. First, $df_x$ depends on the preferred charts at $x$ and $f(x)$, but only up to composition with the invertible derivatives of chart transitions. Whether $df_x$ is surjective or bijective does not depend on them, and signs are measured with orientations expressed in the same charts (§0.7). Second, the value $0$ at non-differentiable points never matters, because every map to which the theorems apply is smooth. Third, the chain rule $d(g \circ f)_x = dg_{f(x)} \circ df_x$ holds whenever $g$ is differentiable at $f(x)$ and $f$ at $x$ ⟦Mathlib/Geometry/Manifold/MFDeriv/Basic · mfderiv_comp⟧. It is the tool behind every comparison between derivatives in this book.

A **diffeomorphism** is a bijection that is smooth with a smooth inverse ⟦Mathlib/Geometry/Manifold/Diffeomorph · Diffeomorph⟧. A **partial diffeomorphism** is a bijection between open subsets, smooth in both directions ⟦Mathlib/Geometry/Manifold/LocalDiffeomorph · PartialDiffeomorph⟧. A map is a **local diffeomorphism at $x$** when it restricts to a partial diffeomorphism on an open neighbourhood of $x$ ⟦Mathlib/Geometry/Manifold/LocalDiffeomorph · IsLocalDiffeomorphAt⟧.

### 0.5 Milnor's manifolds: submanifolds of Euclidean space

Milnor's manifolds are subsets of $\mathbb R^k$. The formal proof represents them through **slice charts**. Let $S$ be a subset of a smooth manifold $M$, with any model $I : H \to E$ (in most uses $M$ is $\mathbb R^k$ or a manifold built earlier), and let $Z$ and $W$ be real normed spaces. A slice chart for $S$ is a partial diffeomorphism $\varphi$ from an open subset of $M$ onto an open subset of $Z \times W$ such that, on its domain,
$$
p \in S \iff \text{the } W\text{-component of } \varphi(p) \text{ is } 0 .
$$
It comes with a base point of $S$ in its domain ⟦Chapter2/Submanifold · SliceChart⟧. The set $S$ is a **submanifold modelled on $Z$** if every point of $S$ lies in the domain of some slice chart ⟦Chapter2/Submanifold · IsSliceSubmanifold⟧.

Such an $S$ is a manifold in its own right. Its charts are the maps $p \mapsto$ ($Z$-component of $\varphi(p)$), restricted to $S$, and its preferred chart at a point is built from a slice chart chosen for that point ⟦Chapter2/Submanifold · chartedSpace⟧. The transitions are smooth ⟦Chapter2/Submanifold · isManifold⟧, and the inclusion $\iota : S \to M$ is smooth ⟦Chapter2/Submanifold · contMDiff_val⟧. When $E$ is finite-dimensional and $M$ has no boundary, $\iota$ has injective derivative ⟦Chapter2/LevelSet · injective_mfderiv_val⟧.

Milnor's "smooth manifold $M \subseteq \mathbb R^k$ of dimension $m$" is a submanifold of $\mathbb R^k$ modelled on $\mathbb R^m$, with complementary space $\mathbb R^w$ (some parts call it the normal model, or the complement). Such an $M$ is Hausdorff and second countable, as a subspace of $\mathbb R^k$. Compactness, nonemptiness and the like are assumed separately where needed. Level sets have a different complementary space: the preimage of a regular value gets the model space of the target, $\mathbb R$ for the sphere. The other manifolds of the book are built the same way, as slice submanifolds of a Euclidean space or of a manifold built earlier: spheres and other level sets, preimages of regular values, products and graphs, tangent bundles, submanifolds $N \subseteq M$, and cobordisms $S \subseteq M \times \mathbb R$, where $M \times \mathbb R$ carries the product structure of §0.3. The **tangent space** of $M$ at $x$ in Milnor's sense is the image of the derivative of the inclusion, a linear subspace $TM_x \subseteq \mathbb R^k$ ⟦Chapter7/Framed · tangentM⟧.

*Milnor's derivative.* Milnor defines $df_x : TM_x \to TN_{f(x)}$ by restricting to $TM_x$ the derivative $dF_x$ of a smooth extension $F$ of $f$ to an open subset of $\mathbb R^k$. Near $x$ one has $\iota_N \circ f = F \circ \iota_M$, so the chain rule gives $d\iota_N \circ df_x = dF_x \circ d\iota_M$. Since $d\iota_M$ is injective with image $TM_x$, Milnor's derivative is $d\iota_N \circ df_x \circ (d\iota_M)^{-1}$ on $TM_x$. It is the chart derivative of §0.4, transported by the inclusions. The formal proofs apply this identity wherever they need it rather than through a single general lemma. Problem 10 packages Milnor's derivative as a smooth map of tangent bundles ⟦Chapter8/TangentBundle · tangentMap⟧ ⟦Chapter8/TangentBundle · contMDiff_tangentMap⟧.

*The nearest-point retraction.* Chapter 6 proves Milnor's $\varepsilon$-neighbourhood theorem in the following form. Let $N \subseteq \mathbb R^k$ be a compact, nonempty submanifold. There are $\varepsilon > 0$ and a map $r : \mathbb R^k \to N$ such that $|x - r(x)|$ is the distance from $x$ to $N$ for every $x$, and $r$ is the identity on $N$. Where the distance from $x$ to $N$ is less than $\varepsilon$, $r(x)$ is the only nearest point, $r$ is smooth near $x$, $x - r(x)$ is orthogonal to $TN_{r(x)}$, and $dr_x$ takes values in $TN_{r(x)}$. Finally $r(x + sv) = x$ for $x \in N$, $v \perp TN_x$ and $s$ near $0$ ⟦Chapter6/Tubular3 · tubular⟧. The **tubular radius** $\varepsilon$ and the **nearest-point retraction** $r$ are then fixed once and for all by choice, and $N_\varepsilon = \{x : \operatorname{dist}(x, N) < \varepsilon\}$ is the **tubular neighbourhood** ⟦Chapter6/Tubular4 · tubε⟧ ⟦Chapter6/Tubular4 · tubr⟧ ⟦Chapter6/Tubular4 · Nε⟧. The parts write $\varepsilon_M$, $\varepsilon_0$ or $\varepsilon$ for the radius, according to context.

*Manifolds with boundary.* Let $X$ and $B$ be subsets of a smooth manifold $M$, again with any model. A **half-slice chart** is a partial diffeomorphism $\Phi$ from an open subset of $M$ onto an open subset of $\mathbb R \times Z$ such that, on its domain, $p \in X$ if and only if the $\mathbb R$-component of $\Phi(p)$ is $\ge 0$, and $p \in B$ if and only if it is $= 0$. Like a slice chart, it comes with a base point of $X$ in its domain ⟦Chapter2/Boundary · HalfSliceChart⟧. The set $X$ is a **manifold with boundary $B$** if every point of $X$ lies in the domain of a half-slice chart ⟦Chapter2/Boundary · IsHalfSliceSubmanifold⟧. It then carries charts into the half-space model, the restrictions of the half-slice charts, with a chosen one at each point ⟦Chapter2/Boundary · chartedSpace⟧, smoothly compatible ⟦Chapter2/Boundary · isManifold⟧. For this structure the **boundary** of $X$ in Mathlib's sense, the points that the preferred chart sends to the frontier $\{t = 0\}$ of the half-space ⟦Mathlib/Geometry/Manifold/IsManifold/InteriorBoundary · ModelWithCorners.IsBoundaryPoint⟧, consists exactly of the points of $X$ that lie in $B$ ⟦Chapter2/Boundary · boundary_eq⟧. Requiring every half-slice chart to send exactly $B$ to $\{t = 0\}$ builds the well-definedness of the boundary into the definition.

### 0.6 Regular values

A point $x$ is a **regular point** of $f : M \to N$ if $df_x$ is surjective ⟦Chapter1/RegularValue · IsRegularPoint⟧, and a **critical point** otherwise ⟦Chapter1/RegularValue · IsCriticalPoint⟧. A point $y \in N$ is a **regular value** if every point of $f^{-1}(y)$ is a regular point ⟦Chapter1/RegularValue · IsRegularValue⟧, and a **critical value** if it is the image of a critical point ⟦Chapter1/RegularValue · IsCriticalValue⟧. Points outside the image are regular values, as in Milnor. The formal proof uses surjectivity from the start, which is Milnor's §2 definition. Between manifolds of the same dimension it coincides with his §1 definition, where $df_x$ is nonsingular.

### 0.7 Spheres, orientations and degrees

The **unit sphere** $S^n$ is the set $\{x \in \mathbb R^{n+1} : \langle x, x \rangle - 1 = 0\}$ ⟦Chapter5/HairyBall · sphG⟧ ⟦Chapter5/HairyBall · Sph⟧. It is a submanifold modelled on $\mathbb R^n$ as the level set of a regular value, with complementary space $\mathbb R$ ⟦Chapter5/HairyBall · sphS⟧. Its preferred chart at $y$, written $\varphi_y$ (Part V writes $c_y$), is therefore induced by a slice chart chosen by the axiom of choice, as for every submanifold of §0.5; it is not a stereographic projection. The same set also appears with other formal structures, for instance as the metric sphere $\{|x| = 1\}$ bounding the unit disk in Chapter 2; the sets agree ⟦Chapter5/HairyBall · preimage_eq_sphere⟧, but the charts differ. Its **north** and **south poles** are $\pm e_{n+1}$, the last standard basis vector and its negative (the vector of index $n$ in the formal numbering) ⟦Chapter7/StdMap · north⟧ ⟦Chapter7/StdMap · south⟧.

An **orientation** of an $n$-dimensional vector space $E$ is an equivalence class of nonzero alternating $n$-forms on $E$ ⟦Mathlib/LinearAlgebra/Orientation · Orientation⟧. Two forms are equivalent when one is a positive multiple of the other ⟦Mathlib/LinearAlgebra/Ray · SameRay⟧ ⟦Mathlib/LinearAlgebra/Ray · Module.Ray⟧. The orientation of a basis $e$ is the class of its determinant form $\det_e$, and $e$ is **positive** for an orientation $a$ when its orientation is $a$; two bases have the same orientation exactly when the matrix relating them has positive determinant ⟦Mathlib/LinearAlgebra/Orientation · Module.Basis.orientation⟧ ⟦Mathlib/LinearAlgebra/Orientation · Module.Basis.orientation_eq_iff_det_pos⟧. The **standard orientation** of $\mathbb R^n$ is that of its standard basis ⟦Chapter7/Hopf0 · stdOr⟧. For orientations $a$ of $E$ and $b$ of $F$ in the same dimension, the **sign** of a linear map $T : E \to F$ is computed from representatives: choose forms $\omega$ for $a$ and $\eta$ for $b$ and a tuple $v$ with $\omega(v) \ne 0$. The sign is the sign of $\eta(Tv_1, \dots, Tv_n)\,\omega(v_1, \dots, v_n)$ ⟦Chapter5/OrSign · orSign⟧. If the pullback of $\eta$ by $T$ is $c\,\omega$, the sign is that of $c$, whatever the representatives ⟦Chapter5/OrSign · orSign_eq_sgn⟧. So it is $+1$ if $T$ *carries $a$ to $b$*, that is, maps bases positive for $a$ to bases positive for $b$; it is $-1$ if $T$ carries $a$ to $-b$; and it is $0$ if $T$ is singular.

An **orientation of a manifold** $M$ modelled on a finite-dimensional $E$ assigns an orientation of $E$ to each point. (Formally the number $n$ of indices of the forms is a parameter of the definition, and the theorems add $\dim E = n$.) It is required to be continuous in the following sense: for each $x$, the derivative at nearby points $y$ of the extended chart at $x$ carries the orientation at $y$ to the orientation at $x$, that is, the sign is $+1$ for all $y$ near $x$ ⟦Chapter5/Orient · Orient⟧. The manifold is **orientable** when it carries such an orientation ⟦Chapter7/Orientable · IsOrientable⟧; that this is the same as carrying no orientation-reversing loop is proved in Part VII, and is less easy than the words suggest. With orientations fixed on $M$ and $N$ of the same dimension:

- the **sign of $f$ at $x$** is the sign of $df_x$ ⟦Chapter5/Orient · signAt⟧;
- the **signed count** at $y$, written $\deg(f; y)$, is $\sum_{x \in f^{-1}(y)} \operatorname{sign}_x f$, a finite sum. The formal finite sum is taken to be $0$ when infinitely many terms are nonzero ⟦Chapter5/DegreeAt · degAt⟧ ⟦Mathlib/Algebra/BigOperators/Finprod · finsum⟧;
- the **degree** is the signed count at a regular value chosen once and for all, or $0$ if $f$ has no regular value ⟦Chapter5/Degree · deg⟧. Milnor's Theorem A of §5 shows that under his hypotheses the choice does not matter;
- the **degree modulo 2** is the parity of the number of preimages of a chosen regular value, or $0$ if there is none ⟦Chapter4/Degree · degMod2⟧. The number of elements of a set is the formal one, which is $0$ for an infinite set ⟦Mathlib/Data/Set/Card · Set.ncard⟧. The theorem of §4 shows that the choice does not matter.

Two orientations of the sphere occur. The orientation of Chapter 5 is the orientation of a level set $g^{-1}(0)$, "outward vector first": a basis $z$ of $T_qS^n$ is positive when $(\nu, d\iota_q z_1, \dots, d\iota_q z_n)$ is a positive basis of $\mathbb R^{n+1}$, where the outward vector $\nu = -\sum_i dg_q(e_i)\,e_i$ satisfies $dg_q(\nu) < 0$ ⟦Chapter5/LevelOrient · outward⟧ ⟦Chapter5/LevelOrient · levelOrient⟧ ⟦Chapter5/HairyBall · sphOr⟧. Both $e$ and the orientation of $\mathbb R^{n+1}$ come from a basis that Mathlib chooses by the axiom of choice from the bare fact $\dim \mathbb R^{n+1} = n + 1$, which the parts call the *reference basis* ⟦Mathlib/LinearAlgebra/Dimension/Free · Module.finBasisOfFinrankEq⟧; it is not provably the standard basis. For $g(x) = \langle x, x\rangle - 1$ the outward vector points into the ball, so the sphere is oriented as the boundary of $\{\langle x, x\rangle \ge 1\}$. Its relation to Milnor's orientation is therefore not fixed, and it is not needed: the theorems of Chapters 5 and 6 are stated and proved for this orientation of the sphere, and none of their statements requires knowing how it compares with Milnor's. Chapter 7 uses the same orientation for the positive bases of Pontryagin manifolds and for the degrees in the Hopf theorem, and so do Problems 16 and 17 of Chapter 8 through the results of Chapter 7 ⟦Chapter7/Lemma2 · exists_posBasis⟧. Linking numbers and the Hopf invariant do need Milnor's convention. Chapter 8 therefore defines the orientation of the sphere as the boundary of the disk: outward normal first, relative to the standard orientation of $\mathbb R^{n+1}$ ⟦Chapter8/OrientFrame · stdOrE⟧ ⟦Chapter8/OrientFrame · sphOrStd⟧. Part IX explains the construction.

### 0.8 Homotopies and isotopies

A **smooth homotopy** from $f$ to $g$ is a smooth map $H : X \times \mathbb R \to Y$ with $H(\cdot, 0) = f$ and $H(\cdot, 1) = g$ ⟦Chapter7/Homotopy · SmoothHomotopic⟧. Using all of $\mathbb R$ instead of $[0, 1]$ keeps the domain a manifold without boundary. For merely continuous maps the book uses Mathlib's notion: a **homotopy** from $f$ to $g$ is a continuous $F : [0, 1] \times X \to Y$ with $F(0, \cdot) = f$ and $F(1, \cdot) = g$, time coming first ⟦Mathlib/Topology/Homotopy/Basic · ContinuousMap.Homotopy⟧, and $f$, $g$ are **homotopic** if one exists ⟦Mathlib/Topology/Homotopy/Basic · ContinuousMap.Homotopic⟧. Continuous maps into a sphere that are smoothly homotopic are homotopic ⟦Chapter8/Approx · SmoothHomotopic.homotopic⟧. When a proof needs to glue homotopies, a smooth reparametrization of time makes $H(x, t) = f(x)$ for $t \le \varepsilon$ and $H(x, t) = g(x)$ for $t \ge 1 - \varepsilon$, for any given $0 < \varepsilon < \tfrac12$ ⟦Chapter7/Homotopy · SmoothHomotopic.exists_const_near_ends⟧. Points $y$ and $z$ of $N$ are **isotopic** if some diffeomorphism $h$ of $N$ carries $y$ to $z$ and there is a smooth $H : N \times \mathbb R \to N$ with $H(\cdot, 0) = \mathrm{id}$, $H(\cdot, 1) = h$, and every stage $H(\cdot, t)$, $t \in \mathbb R$, a diffeomorphism ⟦Chapter4/Homogeneity · Isotopic⟧.

### 0.9 Framed submanifolds and framed cobordisms

Let $M \subseteq \mathbb R^k$ be a manifold of dimension $m$ in the sense of §0.5. Every theorem of Chapter 7 that involves Pontryagin manifolds also assumes $M$ compact and nonempty, and writes $k = K + 1 \ge 1$; symmetry and transitivity of framed cobordism, for example, need neither. A **framed submanifold** of $M$ of dimension $n$ and codimension $p$, where $n + p = m$, is a compact subset $N \subseteq M$ that is a slice submanifold of $M$ modelled on $\mathbb R^n$ with complement $\mathbb R^p$. It carries smooth maps $v_1, \dots, v_p : N \to \mathbb R^k$ that are tangent to $M$ ($v_i(x) \in TM_x$), orthogonal to the tangent spaces $TN_x \subseteq \mathbb R^k$ of $N$ (the images of the derivatives of the inclusions $N \to M \to \mathbb R^k$) ⟦Chapter7/Framed · tangentN⟧, and linearly independent at every point ⟦Chapter7/Framed · FramedSub⟧.

A **framed cobordism** from $(N_0, v)$ to $(N_1, w)$, both of dimension $n$ and codimension $p$, is a slice submanifold $S \subseteq M \times \mathbb R$ modelled on $\mathbb R^{n+1}$ with complement $\mathbb R^p$, together with a number $0 < \varepsilon < \tfrac12$, such that:

- $S$ coincides with $N_0 \times \mathbb R$ where $t < \varepsilon$ and with $N_1 \times \mathbb R$ where $t > 1 - \varepsilon$;
- the part of $S$ over $[0, 1]$ is compact;
- $S$ carries a framing: smooth maps $u_1, \dots, u_p : S \to \mathbb R^k \times \mathbb R$ whose first components are tangent to $M$, which are orthogonal to the tangent spaces of $S$ in $\mathbb R^k \times \mathbb R$ ⟦Chapter7/Framed · tangentS⟧ for the inner product $\langle (a, s), (b, t)\rangle = \langle a, b\rangle + st$ on $\mathbb R^k \times \mathbb R$ ⟦Chapter7/Framed · ipXR⟧, which are independent, and which equal $(v_i, 0)$ where $t < \varepsilon$ and $(w_i, 0)$ where $t > 1 - \varepsilon$ ⟦Chapter7/Framed · FramedCob⟧.

Two framed submanifolds are **framed cobordant** if such an $S$ exists ⟦Chapter7/Framed · FramedCobordant⟧. Milnor's cobordism is the part of $S$ over $[0,1]$. The formal definition builds his "product near the ends" into the object, so that gluing never meets a boundary.

For $M \subseteq \mathbb R^{K+1}$ compact and nonempty, a smooth $f : M \to S^p$ with $n + p = m$, a regular value $y$ and a basis $b$ of $\mathbb R^p$, the model space of $S^p$ at $y$, the **Pontryagin manifold** is $f^{-1}(y)$ with the framing $f^*b$ pulled back from $b$ ⟦Chapter7/Pontryagin · pontryagin⟧. The framing is explicit. With $r$ the nearest-point retraction of a tubular neighbourhood of $M$ and $\varphi_y$ the chart of $S^p$ at $y$, the map $\tilde F = \varphi_y \circ f \circ r$ extends $f$, read in the chart at $y$, to a neighbourhood of $M$, and $f^*b_i(x) = A^*(AA^*)^{-1}b_i$ with $A = d\tilde F_x$ ⟦Chapter7/Pontryagin · pontV⟧. So $df_x$ carries $f^*b_i(x)$ to $b_i$ in the chart at $y$. Part V gives the details.

### 0.10 Conventions of the formal language

Four features of the formal language recur throughout and are worth knowing once.

- **Every function is total.** Where mathematics leaves a value undefined, the formal definition picks one. Division by $0$ gives $0$, the inverse of a non-invertible linear map is $0$ ⟦Mathlib/Algebra/GroupWithZero/Units/Basic · Ring.inverse⟧, a derivative that does not exist is $0$, a finite sum over an infinite support is $0$, and the number of elements of an infinite set is $0$. The normalization $y \mapsto y / \|y\|$ sends $0$ to a fixed point of the sphere ⟦Chapter6/Region · nv0⟧. Every theorem in this book is stated where these defaults play no role, and the book says so when a hypothesis is there only to exclude them.
- **Definitions by choice.** Some definitions choose a witness: the preferred chart of a submanifold, the regular value at which the degree is computed, the rotation used to define a linking number in the sphere. A theorem then shows that the result does not depend on the choice. The same pattern is common in informal mathematics, but in the formal proof it is always explicit.
- **Subsets as spaces.** A subset $S$ of $M$ is also a space in its own right, whose points are points of $M$ together with a proof that they lie in $S$. The inclusion $\iota : S \to M$ forgets the proof. This is why the book sometimes distinguishes a point of $S$ from the same point of $M$.
- **Universes.** A few theorems require their model spaces to lie in the same *universe*, a size bound on types, and one requires the lowest universe. The condition has no mathematical content for spaces like $\mathbb R^n$, but it is part of the formal statements, and the book mentions it where it occurs.

### 0.11 A map of the book

The parts follow the dependencies of the formal proof, which almost always follow Milnor's order.

- **Part I** covers manifolds, regular values and manifolds with boundary (§1–§2), the fundamental theorem of algebra, and Brouwer's theorem.
- **Part II** proves Sard's theorem with Milnor's argument, then the homotopy and homogeneity lemmas and the degree modulo 2 (§3–§4).
- **Part III** covers orientation and the Brouwer degree (§5). Its key step, Lemma 1, walks along the arcs of the Appendix.
- **Part IV** proves the Poincaré–Hopf theorem (§6), together with the $\varepsilon$-neighbourhood theorem that Milnor postpones to §8, and ends with the six side results of §6: Lemmas 2, 4 and 5, Hadamard's lemma, the chart definition of the index, and the Euler number of the sphere.
- **Parts V–VII** cover framed cobordism (§7). Part V gives the lemmas, Theorem A and the first half of Theorem B. Part VI gives the Product Neighborhood Theorem, Theorem C and the second half of Theorem B. Part VII gives the Hopf theorem, and then orientability, the reversing loop of balls and Milnor's classification of the maps of a non-orientable manifold by the degree modulo 2, ending with the orientability of one-manifolds, which is what leaves that theorem with no dimension hypothesis at all.
- **Parts VIII–XI** are the seventeen problems (§8): degrees and bundles, linking numbers, the Hopf invariant with the computation for the Hopf fibration, and transversality with the group of framed cobordism classes.
- **Part XII** is the Appendix, and it has two halves. The first is the boundary count that the book uses — a compact one-manifold has an even number of boundary points — proved for merely topological one-manifolds, and Parts I–III depend on it: Brouwer's no-retraction lemma and the homotopy lemma count boundary points ⟦Appendix/HalfSpace · IsHalfSliceSubmanifold.even_ncard_boundary⟧, and Lemma 1 of §5 follows arcs. The second is Milnor's classification theorem itself, in nine stages, ending with the four cases and their six exclusions ⟦Appendix/Smooth/Main · nonempty_diffeomorph_or⟧ ⟦Appendix/Smooth/Main · models_pairwise_not_diffeomorph⟧; nothing in the book depends on it, though Part VII does, for the dimension of a non-orientable manifold.


## Part I. Manifolds, regular values and the first theorems (Milnor §1–§2)

Milnor's first two sections build the machinery the book runs on (derivatives, regular values, the inverse function theorem, the finiteness and local constancy of the number of preimages of a regular value) and draw two dividends from it: the fundamental theorem of algebra and Brouwer's fixed point theorem. The formal proofs follow Milnor's closely, but Mathlib's manifolds are abstract spaces with atlases, not subsets of $\mathbb R^k$, and this creates work the book never needed. Hausdorffness becomes a hypothesis. Every subset that Milnor calls a manifold (a level set, a sphere, a disk, a region $\{g \ge 0\}$) must be given an atlas; this Part does it once and for all with *slice charts*, shaped after the diffeomorphisms of Milnor's own proofs. Steps the book cites or calls easy are proved in full. The largest departure from the book is that the fundamental theorem of algebra is proved on $\mathbb C \cup \{\infty\}$ rather than on $S^2$; smaller ones are flagged where they occur.

**Map.**

- `Chapter1/InverseFunction`: the inverse function theorem between manifolds, from the Euclidean one.
- `Chapter1/RegularValue`: regular values; finiteness and local constancy of the fibre count, with two strengthenings.
- `Chapter1/Counting`: a connected set of regular values that meets the image lies in the image.
- `Chapter1/RiemannSphere`: $\mathbb C \cup \{\infty\}$ as a smooth surface with the charts $z$ and $1/z$.
- `Chapter1/FTA`: the fundamental theorem of algebra.
- `Chapter2/Submanifold`: slice charts and the manifold structure they induce on a subset.
- `Chapter2/LevelSet`: Lemmas 1 and 2, level sets of regular values and their tangent spaces.
- `Chapter2/Normal`: the second clause of Lemma 2, the normal isomorphism.
- `Chapter2/Boundary`: the half-space model and half-slice charts (manifolds with boundary inside a manifold).
- `Chapter2/WithBoundary`: Lemmas 3 and 4.
- `Chapter2/Disk`: the closed ball, with boundary the sphere.
- `Chapter2/Corestrict`: maps with values in a slice submanifold.
- `Chapter2/Retraction`: the retraction formula of Lemma 6, verified.
- `Chapter2/Brouwer`: the smooth fixed point theorem (Lemmas 5 and 6 for the disk) and Brouwer's theorem.

### Conventions: abstract manifolds and derivatives read in charts

A Mathlib manifold is a space $M$ with an atlas of charts onto open subsets of a model space $H$, together with a *model with corners* $I : H \to E$ embedding $H$ in a normed space $E$. The image of $I$ is all of $E$ for a *boundaryless* model and a half-space for a manifold with boundary; $M$ is $C^n$ when the transition maps, read in $E$, are $C^n$. At each $x$ the atlas designates a preferred chart, which composed with $I$ is the *extended chart* $\varphi_x$, a partially defined map $M \to E$.

Derivatives are read in these charts. For $f : M \to N$, with $\psi$ the extended chart of $N$ at $f(x)$, the derivative $df_x : E \to F$ is the derivative of $\psi \circ f \circ \varphi_x^{-1}$ at $\varphi_x(x)$, taken within the image of $I$. Thus $T_xM$ is the model space $E$, and $df_x$ is a linear map between model spaces. To compare $df_x$ with $f$ written in other charts, the proofs use a small lemma: on a manifold without boundary, the derivative of an extended chart at any point of its domain is invertible, by the chain rule applied to $\varphi^{-1} \circ \varphi = \mathrm{id}$ and $\varphi \circ \varphi^{-1} = \mathrm{id}$ ⟦Chapter2/LevelSet · isInvertible_mfderiv_extChartAt⟧.

A *partial diffeomorphism* is a $C^n$ diffeomorphism between open subsets of $M$ and $N$, and $f$ is a *local diffeomorphism at $x$* if it agrees with one on a domain containing $x$. Both notions are Mathlib's; the project adds restriction to an open subset of the domain ⟦Chapter2/Submanifold · PartialDiffeomorph.restrOpen⟧.

Two more conventions matter. Mathlib's "$C^\infty$ at $x$" means $C^k$ on some neighbourhood for each $k$, the neighbourhood depending on $k$; it does not provide a neighbourhood on which the map is $C^\infty$, so theorems that need one assume smoothness at every point of a neighbourhood ⟦Chapter1/InverseFunction · isLocalDiffeomorphAt_of_isInvertible_mfderiv⟧. And abstract manifolds need not be Hausdorff or second countable; the statements below list these hypotheses where Milnor uses them silently.

### V1.1 The inverse function theorem on manifolds

Milnor cites the Euclidean inverse function theorem and applies it between manifolds without comment. Mathlib listed the manifold version as an open item; the project proves it, more generally than the book needs.

**Theorem (V1.1).** Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$ and $1 \le n \le \omega$ ($n$ finite, $\infty$, or $\omega$ for analytic). Let $M$, $N$ be $C^n$ manifolds without boundary modelled on normed $\mathbb K$-spaces $E$, $F$, with $E$ complete. If $f : M \to N$ is $C^n$ at every point of a neighbourhood of $x$ and $df_x : E \to F$ is invertible as a continuous linear map, then $f$ is a $C^n$ local diffeomorphism at $x$. ⟦Chapter1/InverseFunction · isLocalDiffeomorphAt_of_isInvertible_mfderiv⟧

For $f$ globally $C^n$ the neighbourhood hypothesis is automatic, and for finite $n$ or $n = \omega$ being $C^n$ at $x$ suffices ⟦Chapter1/InverseFunction · ContMDiff.isLocalDiffeomorphAt_of_isInvertible_mfderiv⟧ ⟦Chapter1/InverseFunction · ContMDiffAt.isLocalDiffeomorphAt_of_isInvertible_mfderiv⟧.

*The idea.* Read $f$ in charts and apply the Euclidean theorem. Its local inverse is known to be $C^n$ only at the base point, so one first shrinks to a neighbourhood on which the derivative stays invertible, then carries everything back through the charts.

*The proof as formalized.*

1. Let $\varphi$, $\psi$ be the extended charts at $x$ and $f(x)$, and $g = \psi \circ f \circ \varphi^{-1}$. As the model of $M$ is boundaryless, $\varphi$ carries neighbourhoods of $x$ to neighbourhoods of $\varphi(x)$; so $g$ is $C^n$ at every point near $\varphi(x)$ ⟦Chapter1/InverseFunction · eventually_contDiffAt_writtenInExtChartAt⟧, and $Dg(\varphi(x)) = df_x$ ⟦Chapter1/InverseFunction · hasFDerivAt_writtenInExtChartAt⟧.
2. $Dg$ is continuous at $\varphi(x)$ and the isomorphisms form an open set, so $Dg(u)$ is invertible for all $u$ near $\varphi(x)$ ⟦Chapter1/InverseFunction · eventually_isInvertible_fderiv⟧.
3. The Euclidean theorem gives a partial homeomorphism $\Phi$ of $E$ into $F$, defined near $\varphi(x)$, whose forward map is $g$.
4. Let $T$ be the interior of the set of points of the domain of $\varphi$ at which $f$ is $C^n$ and lands in the domain of $\psi$; $x \in T$. Choose an open $V \ni \varphi(x)$ on which $g$ is $C^n$ with invertible derivative, contained in the domain of $\Phi$ and in the image of $\varphi$, with $\varphi^{-1}(V) \subseteq T$.
5. The partial diffeomorphism is $f$ from $U = \varphi^{-1}(V)$ onto $U' = \psi^{-1}(\Phi(V))$ (open, since $\Phi$ is a partial homeomorphism), with inverse $\varphi^{-1} \circ \Phi^{-1} \circ \psi$; the inverse identities follow from $\psi \circ f = \Phi \circ \varphi$ on $U$. The map $f$ is $C^n$ on $U \subseteq T$. The inverse is $C^n$ as a composite, because $\Phi^{-1}$ is $C^n$ at each $\Phi(u)$, $u \in V$: the inverse of a partial homeomorphism is $C^n$ at the image of any point where the map is $C^n$ with invertible derivative. Step 2 makes this available at every point of $V$, not only at $\varphi(x)$. ⟦Chapter1/InverseFunction · isLocalDiffeomorphAt_of_isInvertible_mfderiv⟧

*A subtlety of the formal definitions, not of the book.* For $n = \infty$ the neighbourhood hypothesis cannot be weakened to smoothness at $x$: a map that is $C^\infty$ at $x$ in Mathlib's sense need not be $C^\infty$ on any neighbourhood of $x$, and then it agrees near $x$ with no $C^\infty$ diffeomorphism. Milnor's maps are smooth everywhere, so for the book nothing is lost.

### V1.2 Regular points and regular values

Milnor defines regular points by invertibility of $df_x$ in §1 (equal dimensions) and by surjectivity in §2. The formal text uses the §2 definition throughout.

**Definition (V1.2).** A point $x$ is a *regular point* of $f$ if $df_x$ is surjective, a *critical point* otherwise; $y$ is a *regular value* if every point of $f^{-1}(y)$ is regular, a *critical value* if it is the image of a critical point. ⟦Chapter1/RegularValue · IsRegularPoint⟧ ⟦Chapter1/RegularValue · IsRegularValue⟧ ⟦Chapter1/RegularValue · IsCriticalValue⟧

Each $y$ is exactly one of the two ⟦Chapter1/RegularValue · isRegularValue_iff_not_isCriticalValue⟧, and points outside $f(M)$ are regular values ⟦Chapter1/RegularValue · IsRegularValue.of_notMem_range⟧. For $E$, $F$ finite-dimensional of equal dimension, rank–nullity makes surjectivity equivalent to invertibility ⟦Chapter1/RegularValue · IsRegularPoint.isInvertible_mfderiv⟧ ⟦Chapter1/RegularValue · IsRegularPoint.of_isInvertible_mfderiv⟧. This recovers the §1 notion and brings V1.1 to bear: a $C^n$ map ($n \ge 1$) between manifolds without boundary of equal finite dimension is a local diffeomorphism at each regular point ⟦Chapter1/RegularValue · IsRegularPoint.isLocalDiffeomorphAt⟧.

### V1.3 A regular fibre is finite

**Theorem (V1.3).** Let $\mathbb K \in \{\mathbb R, \mathbb C\}$, $1 \le n \le \omega$, and let $M$, $N$ be $C^n$ manifolds without boundary modelled on finite-dimensional $\mathbb K$-spaces of equal dimension, with $M$ compact and the points of $N$ closed. If $f : M \to N$ is $C^n$ and $y$ is a regular value, then $f^{-1}(y)$ is finite. ⟦Chapter1/RegularValue · IsRegularValue.finite_preimage⟧

*The idea.* The fibre is compact, and by the inverse function theorem each of its points has a neighbourhood containing no other point of it.

*The proof as formalized.* The fibre is closed, since points of $N$ are, and hence compact. Each of its points $x$ has an open neighbourhood $U_x$, the domain of the local diffeomorphism of V1.2, on which $f$ is injective ⟦Chapter1/RegularValue · IsRegularPoint.isLocalDiffeomorphAt⟧. Finitely many $U_{x_1}, \dots, U_{x_k}$ cover the fibre, and a point $z$ of the fibre lying in $U_{x_i}$ has $f(z) = f(x_i)$, hence $z = x_i$. So the fibre lies in $\{x_1, \dots, x_k\}$. Milnor's appeal to compactness and discreteness becomes a direct subcover argument. *Hidden hypothesis:* points of $N$ are closed.

### V1.4 The count is locally constant

**Theorem (V1.4).** In the setting of V1.3, assume also that $M$ and $N$ are Hausdorff. Then $\#f^{-1}(y') = \#f^{-1}(y)$ for all $y'$ in a neighbourhood of $y$. ⟦Chapter1/RegularValue · IsRegularValue.eventually_ncard_preimage_eq⟧

*The idea.* Near each of the finitely many preimages of $y$, $f$ has a local inverse. For $y'$ close to $y$, the preimages of $y'$ are exactly the images of $y'$ under these local inverses.

*The proof as formalized* is Milnor's, with every set named.

1. Let $x_1, \dots, x_k$ be the points of $f^{-1}(y)$, and $L_i$ the local inverse of $f$ at $x_i$: a diffeomorphism from an open neighbourhood of $y$ onto one of $x_i$, with $L_i(y) = x_i$ and $f \circ L_i = \mathrm{id}$.
2. $M$ being Hausdorff, take pairwise disjoint open sets $W_i \ni x_i$. Put $U_i = W_i \cap (\text{image of } L_i)$ and $V_i = L_i^{-1}(U_i)$, an open set (it is $f(U_i)$).
3. $C = f(M \setminus \bigcup_i U_i)$ is compact, hence closed as $N$ is Hausdorff, and $y \notin C$. Put $V = \bigcap_i V_i \setminus C$.
4. For $y' \in V$, the map $x_i \mapsto L_i(y')$ is a bijection $f^{-1}(y) \to f^{-1}(y')$: it lands in the fibre as $f \circ L_i = \mathrm{id}$; it is injective as the $W_i$ are disjoint; it is onto because a preimage $b$ of $y'$ lies in some $U_i$ (else $y' \in C$), so $b = L_i(f(b)) = L_i(y')$. ⟦Chapter1/RegularValue · IsRegularValue.eventually_ncard_preimage_eq⟧

*Deviation (stronger).* Milnor lets $y'$ range over regular values only; the formal statement covers all $y'$ near $y$. The same construction gives the two forms that later chapters use. All $y'$ near $y$ are regular values, since their preimages lie where $f$ is a local diffeomorphism ⟦Chapter1/RegularValue · IsRegularValue.eventually_isRegularValue_and_ncard⟧ (Chapter 4). And for $w : M \to \mathbb Z$ locally constant near each $x_i$, the weighted count $\sum_{x \in f^{-1}(y')} w(x)$ is constant near $y$: shrink each $U_i$ to where $w$ is constant ⟦Chapter1/RegularValue · IsRegularValue.eventually_finsum_preimage_eq⟧ (the signed counts of Chapter 5).

### V1.5 The counting principle

**Theorem (V1.5).** Let $\mathbb K$, $n$, $M$, $N$, $f$ be as in V1.3, with $M$ compact and $M$, $N$ Hausdorff. (a) If $R \subseteq N$ is a connected set of regular values containing a point of $f(M)$, then $R \subseteq f(M)$. (b) If the set of all regular values is connected and meets $f(M)$, then $f$ is onto. ⟦Chapter1/Counting · subset_range_of_isPreconnected⟧ ⟦Chapter1/Counting · surjective_of_isPreconnected_regularValues⟧

The formal hypothesis is preconnectedness, which for a nonempty set is connectedness. The theorem isolates the end of Milnor's proof of the fundamental theorem of algebra, which uses nothing about polynomials.

*The idea.* A locally constant function on a connected set is constant, and here it is positive at one point.

*The proof as formalized.* By V1.4, $y \mapsto \#f^{-1}(y)$ is locally constant on $R$, hence continuous into the discrete space $\mathbb N$, hence constant on $R$ ⟦Chapter1/Counting · ncard_preimage_eq_of_isPreconnected⟧. At the given $y_0 \in R \cap f(M)$ the fibre is finite ⟦Chapter1/RegularValue · IsRegularValue.finite_preimage⟧ and nonempty, so every count on $R$ is positive. For (b), critical values lie in $f(M)$ by definition. That $R$ meets the image is Milnor's remark that the count cannot vanish identically; in the fundamental theorem it has to be earned.

### V1.6 The fundamental theorem of algebra

**Theorem (V1.6).** Every complex polynomial $P$ of positive degree has a root: $P(z) = 0$ for some $z \in \mathbb C$. ⟦Chapter1/FTA · fundamental_theorem_of_algebra⟧

*The idea* is Milnor's. Extend $P$ to a smooth self-map $f$ of a compact surface. It has finitely many critical values, so a connected set of regular values remains, on which the count is constant and somewhere nonzero. So $f$ is onto, and $0$ has a preimage.

#### The Riemann sphere in place of $S^2$

*Where the formal proof departs from Milnor.* Instead of $S^2 \subset \mathbb R^3$ with stereographic projection, the formal proof uses the one-point compactification $\hat{\mathbb C} = \mathbb C \cup \{\infty\}$, compact and Hausdorff by general topology, with two charts: $z \mapsto z$ on $\hat{\mathbb C} \setminus \{\infty\}$ and $p \mapsto 1/p$ on $\hat{\mathbb C} \setminus \{0\}$ ⟦Chapter1/RiemannSphere · chart₀⟧ ⟦Chapter1/RiemannSphere · chartInf⟧. The second is the first composed with the inversion exchanging $0$ and $\infty$ ⟦Chapter1/RiemannSphere · invert⟧, a homeomorphism because $1/z \to 0$ as $z \to \infty$ and $1/z \to \infty$ as $z \to 0$ ⟦Chapter1/RiemannSphere · continuous_invert⟧. The preferred chart is $1/p$ at $\infty$ and $z$ elsewhere ⟦Chapter1/RiemannSphere · instChartedSpace⟧. The transition maps are the identity and $z \mapsto 1/z$ on $\mathbb C \setminus \{0\}$, so $\hat{\mathbb C}$, modelled on $\mathbb C$ as a real vector space, is a smooth real surface without boundary ⟦Chapter1/RiemannSphere · instIsManifold⟧. Stereographic projection extends to a diffeomorphism $S^2 \cong \hat{\mathbb C}$, so the two surfaces are the same manifold; this identification is not formalized and not needed, since the theorem concerns $P$ alone. The gain is that the chart $1/p$ reads $f$ with the original coefficients, without the complex conjugates of Milnor's formula.

#### The polynomial as a smooth self-map

Write $P(z) = \sum_{k=0}^n c_k z^k$ with $n = \deg P \ge 1$ and $c_n \ne 0$, and let
$$\tilde P(w) = w^n P(1/w) = \sum_{k=0}^n c_{n-k} w^k$$
be the reversed polynomial, so $\tilde P(0) = c_n \ne 0$. Put $f(z) = P(z)$ on $\mathbb C$ and $f(\infty) = \infty$ ⟦Chapter1/FTA · polyMap⟧; $f$ is continuous at $\infty$ because $|P(z)| \to \infty$ as $|z| \to \infty$ ⟦Chapter1/FTA · continuousAt_polyMap_infty⟧. In the chart $z$ at both ends, $f$ is $P$, which is $C^\infty$ over $\mathbb R$ ⟦Chapter1/FTA · contDiff_eval⟧ ⟦Chapter1/FTA · contMDiffAt_polyMap_coe⟧. Near $\infty$, in the chart $1/p$ at both ends, everything rests on the identity
$$P(1/w) = \tilde P(w)\, w^{-n} \qquad (w \ne 0)$$
⟦Chapter1/FTA · eval_inv_eq⟧. On the open set $\{\tilde P \ne 0\}$, which contains $0$, the chart expression of $f$ therefore equals $Q(w) = w^n / \tilde P(w)$: at $w = 0$ both vanish since $n \ge 1$, and for $w \ne 0$ the identity gives $P(1/w) \ne 0$ and $1/P(1/w) = Q(w)$. $Q$ is complex-smooth at $0$, hence real-smooth, and $f$ is smooth everywhere ⟦Chapter1/FTA · contMDiffAt_polyMap_infty⟧ ⟦Chapter1/FTA · contMDiff_polyMap⟧.

#### Finitely many bad values, a connected complement

At $z \in \mathbb C$ the derivative $df_z$ is multiplication by $P'(z)$, as a real-linear map of $\mathbb C$ ⟦Chapter1/FTA · hasMFDerivAt_polyMap_coe⟧, and it is onto when $P'(z) \ne 0$ ⟦Chapter1/FTA · isRegularPoint_polyMap_coe⟧. Let
$$K = \{\infty\} \cup P(\{z : P'(z) = 0\}).$$
$K$ is finite, $P'$ being a nonzero polynomial ⟦Chapter1/FTA · finite_zeros_derivative⟧ ⟦Chapter1/FTA · critVals_finite⟧. It lies in the image of $f$ ⟦Chapter1/FTA · critVals_subset_range⟧, and every $y \notin K$ is a regular value, its preimages being points $z \in \mathbb C$ with $P'(z) \ne 0$ ⟦Chapter1/FTA · isRegularValue_of_notMem_critVals⟧.

*A choice the formal proof makes.* Milnor observes that $P$ fails to be a local diffeomorphism only at the zeros of $P'$, and concludes that $f$ has finitely many critical points without discussing the north pole, which is in fact critical when $n \ge 2$ (the chart expression $Q$ above has vanishing derivative at $0$). The formal proof never decides whether $\infty$ is critical. It puts $\infty$ into $K$ ⟦Chapter1/FTA · critVals⟧ and applies the counting principle to the connected set $\hat{\mathbb C} \setminus K$ of regular values rather than to the set of all regular values, which is why V1.5(a) allows an arbitrary connected $R$.

The set $\hat{\mathbb C} \setminus K$ is the image of $\mathbb C \setminus P(\{P' = 0\})$ under the inclusion ⟦Chapter1/FTA · compl_critVals_eq⟧. The complement of a countable set in a real vector space of dimension at least two is path-connected (a Mathlib theorem), so its image $\hat{\mathbb C} \setminus K$ is connected; the formal statement records preconnectedness, the form V1.5 uses ⟦Chapter1/FTA · isPreconnected_compl_critVals⟧.

*What the book leaves implicit.* The count must be nonzero somewhere on $\hat{\mathbb C} \setminus K$. Each fibre $\{P = c\}$ is finite, as the zero set of the nonzero polynomial $P - c$ ⟦Chapter1/FTA · finite_fiber⟧, so $P(\mathbb C)$ is infinite ⟦Chapter1/FTA · infinite_range_eval⟧ and contains a value outside the finite set $P(\{P' = 0\})$. That value is a regular value in the image ⟦Chapter1/FTA · exists_regularValue_mem_range⟧.

#### Conclusion

By V1.5(a) with $M = N = \hat{\mathbb C}$ and $R = \hat{\mathbb C} \setminus K$ ⟦Chapter1/Counting · subset_range_of_isPreconnected⟧, and since $K$ lies in the image, $f$ is onto. A preimage of $0$ is not $\infty$, as $f(\infty) = \infty$; so it is some $z \in \mathbb C$ with $P(z) = 0$ ⟦Chapter1/FTA · exists_root⟧.

### V2.1 Slice submanifolds: how a subset becomes a manifold

Milnor's proof of Lemma 1 produces a diffeomorphism from a neighbourhood of a point of $f^{-1}(y)$ onto an open set, carrying $f^{-1}(y)$ to a coordinate hyperplane, and concludes that $f^{-1}(y)$ is a manifold; for subsets of $\mathbb R^k$ this is immediate from the definition. Mathlib has no notion of an embedded submanifold of an abstract manifold, so the project defines one, and it takes exactly what Milnor's proof produces: a subset covered by straightening diffeomorphisms ⟦Chapter2/Submanifold · IsSliceSubmanifold⟧. One construction turns such a family into an atlas, so every later "is a manifold" (level sets, spheres, the level set in Brouwer's theorem) reduces to exhibiting straightening diffeomorphisms. Nothing is lost mathematically, since a manifold in Milnor's sense admits such charts in $\mathbb R^k$ by the inverse function theorem; but that general fact is not formalized, and in this Part the charts are always constructed explicitly.

**Definition (V2.1).** Let $M$ be a smooth manifold modelled on a real normed space (boundary allowed), let $Z$, $W$ be real normed spaces, and $S \subseteq M$. A *slice chart* for $S$ is a smooth diffeomorphism $\varphi$ from an open set $U \subseteq M$ onto an open subset of $Z \times W$, with a base point $x_0 \in S \cap U$, such that for all $p \in U$
$$p \in S \iff \varphi(p) \in Z \times \{0\}.$$
$S$ is a *slice submanifold* (modelled on $Z$, with normal model $W$) if every point of $S$ lies in the domain of a slice chart. ⟦Chapter2/Submanifold · SliceChart⟧ ⟦Chapter2/Submanifold · IsSliceSubmanifold⟧

The base point is a formal device: the inverse chart must be a map defined everywhere, and $x_0$ is its value off the chart's image ⟦Chapter2/Submanifold · invChart⟧.

**Theorem (V2.1).** A slice submanifold $S$, with the subspace topology and the atlas of charts induced by all its slice charts, is a smooth manifold without boundary modelled on $Z$, and the inclusion $S \to M$ is smooth. ⟦Chapter2/Submanifold · chartedSpace⟧ ⟦Chapter2/Submanifold · isManifold⟧ ⟦Chapter2/Submanifold · contMDiff_val⟧

*The idea.* Forget the normal coordinate: a slice chart restricted to $S$ and followed by the projection to $Z$ is a chart of $S$, and two such charts differ by a smooth map.

*The proof as formalized.* A slice chart $\varphi$ induces the chart $p \mapsto \mathrm{pr}_Z\,\varphi(p)$ on $S \cap U$, with open image $\{z : (z, 0) \in \varphi(U)\}$ and inverse $z \mapsto \varphi^{-1}(z, 0)$, which lies in $S$ by the slice condition ⟦Chapter2/Submanifold · symm_mem⟧. For $p \in S \cap U$ one has $\varphi(p) = (\mathrm{pr}_Z\,\varphi(p), 0)$; this shows that the chart lands in its image and that $\varphi^{-1}(\mathrm{pr}_Z\,\varphi(p), 0) = p$, while the other inverse identity is $\varphi(\varphi^{-1}(z, 0)) = (z, 0)$ ⟦Chapter2/Submanifold · mk_zero_mem_target⟧ ⟦Chapter2/Submanifold · toChart⟧. The preferred chart at $p$ comes from a slice chart chosen around $p$. Transition maps are $z \mapsto \mathrm{pr}_Z\,\varphi_2(\varphi_1^{-1}(z, 0))$, composites of smooth maps ⟦Chapter2/Submanifold · contDiffOn_trans⟧, and in charts the inclusion is $z \mapsto \varphi_M(\varphi^{-1}(z, 0))$ for a chart $\varphi_M$ of $M$.

Two features matter later. The atlas consists of the charts induced by all slice charts of $S$, not only the chosen ones ⟦Chapter2/Submanifold · mem_atlas_iff⟧, so any slice chart may be used to compute in $S$; within this Part, Lemma 2 (V2.3) and corestriction (V2.8) need only the chart chosen at the point in question ⟦Chapter2/LevelSet · injective_mfderiv_val⟧ ⟦Chapter2/Corestrict · extChartAt_eq⟧. And the dimension of $S$ is that of $Z$: Milnor's dimension count $m - n$ becomes a hypothesis on $Z$, such as $\dim Z + \dim F = \dim E$.

### V2.2 Lemma 1: the level set of a regular value

**Theorem (V2.2, Lemma 1).** Let $M$, $N$ be smooth manifolds without boundary modelled on finite-dimensional real spaces $E$, $F$; let $Z$ be a finite-dimensional real space with $\dim Z + \dim F = \dim E$; let $f : M \to N$ be smooth and $y$ a regular value. Then $f^{-1}(y)$ is a slice submanifold of $M$ modelled on $Z$ with normal model $F$, hence a manifold of dimension $\dim M - \dim N$. More precisely, each $x \in f^{-1}(y)$ lies in the domain of a slice chart whose second component is $p \mapsto \psi(f(p)) - \psi(y)$, where $\psi$ is the extended chart of $N$ at $y$. ⟦Chapter2/LevelSet · isSliceSubmanifold_preimage⟧ ⟦Chapter2/LevelSet · exists_sliceChart_preimage⟧

Lemma 3 uses the refined form.

*The idea* is Milnor's: complete $f$ by a linear map $L$ that is nonsingular on the kernel of the derivative, invert $(L, f)$ locally, and see the level set as a coordinate slice. Reading $N$ through $\psi$ turns Milnor's map $\xi \mapsto (f(\xi), L(\xi)) \in N \times \mathbb R^{m-n}$ into a map to the vector space $Z \times F$.

*The proof as formalized.*

1. With $\varphi$ the extended chart at $x$, let $\tilde f = \psi \circ f \circ \varphi^{-1}$, smooth where defined, and $D = D\tilde f(\varphi(x))$.
2. $D = d\psi \circ df_x \circ d(\varphi^{-1})$ is onto: $d\psi$ is invertible and $d(\varphi^{-1})$ is onto ⟦Chapter2/LevelSet · isInvertible_mfderiv_extChartAt⟧ ⟦Chapter2/LevelSet · surjective_mfderiv_extChartAt_symm⟧, and $df_x$ is onto because $y$ is regular.
3. By rank–nullity $\mathcal N = \ker D$ has dimension $\dim E - \dim F = \dim Z$. Choose an isomorphism $j : \mathcal N \to Z$ and a complement of $\mathcal N$, and let $L = j \circ \mathrm{pr}$, with $\mathrm{pr}$ the projection onto $\mathcal N$ along the complement: Milnor's map nonsingular on the null space.
4. $(L, D) : E \to Z \times F$ is injective (if $Dv = 0$ then $v \in \mathcal N$ and $Lv = j(v)$), hence an isomorphism by dimension count.
5. $\Phi(p) = \big(L(\varphi(p)),\ \psi(f(p)) - \psi(y)\big)$ is smooth on the open set $U_1$ of points in the domain of $\varphi$ that $f$ sends into the domain of $\psi$, and $d\Phi_x = (L, D) \circ d\varphi_x$ is invertible.
6. By V1.1, $\Phi$ agrees with a partial diffeomorphism on a domain containing $x$ ⟦Chapter1/InverseFunction · isLocalDiffeomorphAt_of_isInvertible_mfderiv⟧; restrict it to $U_1$ ⟦Chapter2/Submanifold · PartialDiffeomorph.restrOpen⟧.
7. On that domain, $p \in f^{-1}(y)$ iff $\psi(f(p)) = \psi(y)$ iff the second component of $\Phi(p)$ vanishes. The first equivalence uses that $\psi$ is injective on its domain, which contains $f(p)$ and $y$; this is why the domain was cut down to $U_1$. ⟦Chapter2/LevelSet · exists_sliceChart_preimage⟧

### V2.3 Lemma 2: the tangent space of a level set

**Theorem (V2.3, Lemma 2).** In the setting of V2.2, give $f^{-1}(y)$ the structure of V2.1 and let $\iota : f^{-1}(y) \to M$ be the inclusion. For $p \in f^{-1}(y)$ and $v \in E = T_pM$,
$$v \in \operatorname{im}(d\iota_p) \iff df_p(v) = 0.$$
⟦Chapter2/LevelSet · mem_range_mfderiv_val_iff⟧

The statement is elementwise because the two tangent spaces are different model spaces, $Z$ and $E$.

*The idea.* The tangent space of the level set lies in $\ker df_p$ because $f$ is constant on the level set, and both have dimension $\dim Z$.

*The proof as formalized* is Milnor's. Since $f \circ \iota$ is constant, $df_p \circ d\iota_p = 0$ ⟦Chapter2/LevelSet · mfderiv_comp_val_eq_zero⟧. For any slice submanifold, $d\iota_p$ is injective: if $\varphi$ is the slice chart chosen at $p$, then $\mathrm{pr}_Z \circ \varphi \circ \iota$ is the preferred chart at $p$, whose derivative there is the identity ⟦Chapter2/LevelSet · injective_mfderiv_val⟧. So $\operatorname{im} d\iota_p \subseteq \ker df_p$, and both have dimension $\dim Z$, the second because $df_p$ is onto; they are equal.

#### V2.12 The second clause of Lemma 2: the normal isomorphism

Milnor's Lemma 2 has a second sentence, which follows "therefore" from the first: the derivative carries the orthogonal complement of the tangent space of the level set isomorphically onto the tangent space of the target. Write $T = \operatorname{im}(d\iota_p)$ for the tangent space of the level set as a subspace of the model space $E$, which is what the equivalence above describes ⟦Chapter2/Normal · tangentSubspace⟧ ⟦Chapter2/Normal · mem_tangentSubspace_iff⟧.

**Theorem (V2.12).** In the setting of V2.2, $df_p$ is injective on $T^\perp$ and carries it onto $F = T_yN$, so it restricts to a linear isomorphism $T^\perp \to F$, whose underlying map is $df_p$ itself. ⟦Chapter2/Normal · mfderiv_injOn_tangent_orthogonal⟧ ⟦Chapter2/Normal · mfderiv_surjOn_tangent_orthogonal⟧ ⟦Chapter2/Normal · normalEquiv⟧

*The proof as formalized* is the dimension count Milnor leaves to the reader. By V2.3, $T$ is the kernel of $df_p$, of dimension $\dim E - \dim F$ because $y$ is regular, so $T^\perp$ has dimension $\dim F$ ⟦Chapter2/Normal · finrank_tangentSubspace_orthogonal⟧. Injectivity on $T^\perp$ is V2.3 together with $T \cap T^\perp = 0$, and an injective map between spaces of the same finite dimension is onto.

One hypothesis is added that Milnor would not state. The orthogonal complement needs an inner product on the model space $E$ of the source, where V2.2 and V2.3 ask for a norm only; Milnor has it for nothing, his manifolds being subsets of $\mathbb R^k$. The target needs none, and $M$, $N$ and the boundaryless model are otherwise as general as in V2.3.

### V2.4 Manifolds with boundary: the half-space model and half-slice charts

Mathlib represents manifolds with boundary through a model with corners whose image is not the whole vector space. The formal text builds one and repeats the slice construction with half-spaces.

**Definitions (V2.4).** For a real normed space $Z$ the half-space is $H(Z) = \{(t, z) \in \mathbb R \times Z : t \ge 0\}$, Milnor's $H^m$ with the distinguished coordinate first ⟦Chapter2/Boundary · HalfSpace⟧. The model is the inclusion into $\mathbb R \times Z$, with formal inverse $(t, z) \mapsto (\max(t, 0), z)$ ⟦Chapter2/Boundary · halfSpaceModel⟧; its image has interior $\{t > 0\}$ and frontier $\{t = 0\}$ ⟦Chapter2/Boundary · interior_range_halfSpaceModel⟧ ⟦Chapter2/Boundary · frontier_range_halfSpaceModel⟧. Let $M$ be a smooth manifold modelled on a real normed space and $X, B \subseteq M$. A *half-slice chart* for $X$ with boundary $B$ is a smooth diffeomorphism $\Phi$ from an open $U \subseteq M$ onto an open subset of $\mathbb R \times Z$, with a base point in $X \cap U$, such that for all $p \in U$, with $\Phi_1$ the $\mathbb R$-component,
$$p \in X \iff \Phi_1(p) \ge 0, \qquad p \in B \iff \Phi_1(p) = 0.$$
$X$ is a *half-slice submanifold* over $Z$ with boundary $B$ if every point of $X$ lies in the domain of such a chart. ⟦Chapter2/Boundary · HalfSliceChart⟧ ⟦Chapter2/Boundary · IsHalfSliceSubmanifold⟧

**Theorem (V2.4).** Such an $X$, with the subspace topology and the charts induced by all its half-slice charts, is a smooth manifold with boundary modelled on $H(Z)$; its boundary in Mathlib's sense is $X \cap B$; and the inclusion $X \to M$ is smooth. ⟦Chapter2/Boundary · isManifold⟧ ⟦Chapter2/Boundary · boundary_eq⟧ ⟦Chapter2/Boundary · contMDiff_val⟧

*The idea* is that of V2.1, with half-spaces in place of slices; the boundary comes out right because the charts are required to respect it.

*The proof as formalized.* The induced chart is $p \mapsto \Phi(p) \in H(Z)$ with inverse $h \mapsto \Phi^{-1}(h)$ ⟦Chapter2/Boundary · toChart⟧, and transition maps are restrictions to the half-space of maps smooth on open subsets of $\mathbb R \times Z$ ⟦Chapter2/Boundary · contDiffOn_trans⟧. Mathlib calls a point a boundary point when its preferred extended chart sends it into the frontier $\{t = 0\}$ of the model's image; by the second condition this happens exactly on $B$ ⟦Chapter2/Boundary · boundary_eq⟧.

*Where the formal proof departs from Milnor.* Milnor remarks that $\partial X$ is well defined, which needs an argument that diffeomorphisms between open subsets of $H^m$ preserve boundary points. The formal definition sidesteps it: $B$ is prescribed, and every chart must send exactly $B$ to $\{t = 0\}$ ⟦Chapter2/Boundary · HalfSliceChart⟧. The manifolds with boundary built in the book (Lemmas 3 and 4) come with such charts.

### V2.5 Lemma 3: the region $\{g \ge 0\}$

**Theorem (V2.5, Lemma 3).** Let $M$ be a smooth manifold without boundary modelled on a finite-dimensional real space $E$, let $Z$ be a finite-dimensional real space with $\dim Z + 1 = \dim E$, and let $g : M \to \mathbb R$ be smooth with $0$ a regular value. Then $\{g \ge 0\}$ is a half-slice submanifold over $Z$ with boundary $\{g = 0\}$. ⟦Chapter2/WithBoundary · isHalfSliceSubmanifold_of_regularValue⟧

*The idea.* Milnor says the proof is like that of Lemma 1, and the formal proof makes this literal: at a boundary point, the slice chart of Lemma 1 for $g$, with its factors swapped, has $g$ as first coordinate. At an interior point any chart will do, once translated so that its first coordinate is positive.

*The proof as formalized.* Let $g(p) \ge 0$.

*Boundary points*, $g(p) = 0$. The refined Lemma 1 for $g$ ⟦Chapter2/LevelSet · exists_sliceChart_preimage⟧ gives a slice chart $\varphi : U \to Z \times \mathbb R$ at $p$ whose second component is $\psi(g(q)) - \psi(0)$ for the chart $\psi$ of $\mathbb R$ at $0$, which is the identity; so the second component is $g$. Composing with the swap $Z \times \mathbb R \to \mathbb R \times Z$ ⟦Chapter2/WithBoundary · PartialDiffeomorph.ofHomeomorph⟧ gives a chart whose first coordinate is $g$, and both half-slice conditions hold by definition.

*Interior points*, $g(p) > 0$. Take the extended chart of $M$ at $p$, a partial diffeomorphism onto an open subset of $E$ because $M$ has no boundary ⟦Chapter2/WithBoundary · PartialDiffeomorph.ofExtChartAt⟧. Follow it by a linear isomorphism $E \to \mathbb R \times Z$ and a translation by $(c, 0)$ that puts $p$ at first coordinate $1$, and restrict to the open set where $g$ and the first coordinate are both positive. There both membership conditions are true and both boundary conditions false, so this is a half-slice chart without boundary points. Regularity of $0$ is used only at boundary points.

### V2.6 Lemma 4: level sets in a manifold with boundary

In Milnor's Lemma 4, $X$ is an $m$-manifold with boundary, $f : X \to N$ is smooth with $m > n$, and $y$ is regular both for $f$ and for $f|\partial X$; the conclusion is that $f^{-1}(y)$ is an $(m-n)$-manifold with boundary $f^{-1}(y) \cap \partial X$.

**Theorem (V2.6, Lemma 4).** Let $M$, $N$ be smooth manifolds without boundary modelled on finite-dimensional real spaces $E$, $F$; let $Z$, $Z'$ be finite-dimensional real spaces with $\dim Z + \dim F = \dim E$ and $\dim Z' + 1 = \dim Z$; let $f : M \to N$ be smooth with $y$ a regular value, and $g : M \to \mathbb R$ smooth. Assume that for every $x$ with $f(x) = y$ and $g(x) = 0$ some $v \in T_xM$ satisfies
$$df_x(v) = 0, \qquad dg_x(v) \ne 0.$$
Then, inside the manifold $f^{-1}(y)$ of V2.2 (modelled on $Z$), the set $\{g \ge 0\}$ is a half-slice submanifold over $Z'$ with boundary $\{g = 0\}$. So $f^{-1}(y) \cap \{g \ge 0\}$ is a manifold of dimension $\dim M - \dim N$ with boundary $f^{-1}(y) \cap \{g = 0\}$. ⟦Chapter2/WithBoundary · isHalfSliceSubmanifold_levelSet⟧

*Where the formal statement departs from Milnor.* The manifold with boundary is $X = \{g \ge 0\}$ inside a manifold without boundary on which $f$ is defined; this suffices for every application in the formal text, beginning with the disk (V2.10) and the cylinder of §4. Regularity of $y$ for $f|\partial X$ becomes the displayed transversality condition, which is what Milnor's proof extracts from it: the null space of $df_x$ is not contained in the tangent space of the boundary. Further, $y$ must be regular for $f$ on all of $M$, not only on $X$, while $0$ need not be a regular value of $g$, since transversality already forces $dg_x \ne 0$ where it matters. Milnor's $m > n$ is the existence of $Z'$. ⟦Chapter2/WithBoundary · isHalfSliceSubmanifold_levelSet⟧

*The idea* is Milnor's: $f^{-1}(y)$ is a manifold without boundary (Lemma 1), transversality says that $g$ restricted to it has $0$ as a regular value (Lemma 2), and Lemma 3 finishes.

*The proof as formalized.* By V2.2 and V2.1, $f^{-1}(y)$ is a manifold modelled on $Z$ with smooth inclusion $\iota$, so $\pi = g \circ \iota$ is smooth. At $q$ with $g(q) = 0$, take $v$ as in the hypothesis: Lemma 2 writes $v = d\iota_q(w)$ ⟦Chapter2/LevelSet · mem_range_mfderiv_val_iff⟧, and $d\pi_q(w) = dg_q(v) \ne 0$, so $d\pi_q$ is onto $\mathbb R$ and $0$ is a regular value of $\pi$. Lemma 3, applied to $f^{-1}(y)$, $\pi$ and $Z'$, concludes ⟦Chapter2/WithBoundary · isHalfSliceSubmanifold_of_regularValue⟧ ⟦Chapter2/WithBoundary · isHalfSliceSubmanifold_levelSet⟧.

### V2.7 The disk

**Theorem (V2.7).** Let $E$ be a finite-dimensional real inner product space and $Z$ a finite-dimensional real space with $\dim Z + 1 = \dim E$. Then the closed unit ball of $E$ is a half-slice submanifold over $Z$ with boundary the unit sphere. In particular, for every $m \ge 0$ the closed unit ball of $\mathbb R^{m+1}$ is a manifold with boundary $S^m$, modelled on the half-space over $\mathbb R^m$. ⟦Chapter2/Disk · isHalfSliceSubmanifold_closedBall⟧ ⟦Chapter2/Disk · isHalfSliceSubmanifold_unitDisk⟧

This is Lemma 3 for the smooth function $g(x) = 1 - \|x\|^2$ ⟦Chapter2/Disk · diskFun⟧ ⟦Chapter2/Disk · contMDiff_diskFun⟧, whose derivative at $x$ is $v \mapsto -2\langle x, v\rangle$. On the sphere, $v = -\tfrac t2 x$ is sent to $t$, so $0$ is a regular value ⟦Chapter2/Disk · isRegularValue_diskFun⟧.

### V2.8 Corestriction

**Theorem (V2.8).** Let $S$ be a slice submanifold of $M$, let $M'$ be a smooth manifold modelled on a real normed space, and let $F : M' \to M$ be smooth with $F(M') \subseteq S$. Then $F$ is smooth as a map $M' \to S$. ⟦Chapter2/Corestrict · contMDiff_codRestrict⟧

In the chart of $S$ at $F(x)$, which is induced by a slice chart $\varphi$ ⟦Chapter2/Corestrict · extChartAt_eq⟧, the map reads $\mathrm{pr}_Z \circ \varphi \circ F$. Milnor uses this silently whenever a map into $\partial X \subseteq X$ is regarded as a map into the manifold $\partial X$.

### V2.9 Lemma 6: the retraction formula, verified

Milnor writes down the retraction determined by a fixed-point-free $P$ and leaves its properties to the reader. The formal text checks them, by calculus in a real inner product space $E$. For $P : E \to E$ put
$$u = \frac{x - P(x)}{\|x - P(x)\|}, \qquad \Delta = 1 - \|x\|^2 + \langle x, u\rangle^2, \qquad t = -\langle x, u\rangle + \sqrt{\Delta}$$
⟦Chapter2/Retraction · uVec⟧ ⟦Chapter2/Retraction · rad⟧ ⟦Chapter2/Retraction · tVal⟧. The retraction is $r(x) = x + t\,u$, considered on $\Omega_P = \{x : x \ne P(x),\ \Delta(x) > 0\}$ ⟦Chapter2/Retraction · retr⟧ ⟦Chapter2/Retraction · good⟧.

**Theorem (V2.9).** Let $E$ be a real inner product space with closed unit ball $D$, and $P : E \to E$.

- (a) On $\Omega_P$, $\|r(x)\| = 1$. ⟦Chapter2/Retraction · norm_retr⟧
- (b) If $x \in \Omega_P$, $\|x\| = 1$ and $\|P(x)\| \le 1$, then $r(x) = x$. ⟦Chapter2/Retraction · retr_eq_self⟧
- (c) If $P(D) \subseteq D$ and $P$ has no fixed point in $D$, then $D \subseteq \Omega_P$. ⟦Chapter2/Retraction · closedBall_subset_good⟧
- (d) If $P$ is continuous, $\Omega_P$ is open; if $P$ is smooth, $r$ is smooth on $\Omega_P$. ⟦Chapter2/Retraction · isOpen_good⟧ ⟦Chapter2/Retraction · contDiffOn_retr⟧

*The idea.* The parameter $t$ solves $\|x + tu\| = 1$ by the quadratic formula, and each claim is an identity or inequality about that root.

*The proof as formalized.* For (a), let $a = \langle x, u\rangle$ and $s = \sqrt\Delta$, so $t = s - a$ and $\|u\| = 1$; then $\|x + tu\|^2 = \|x\|^2 + 2ta + t^2 = \|x\|^2 + s^2 - a^2 = 1$. For (b), $a = (1 - \langle x, Px\rangle)/\|x - Px\| \ge 0$ by Cauchy–Schwarz, which is where $\|Px\| \le 1$ enters ⟦Chapter2/Retraction · inner_uVec⟧; so $\sqrt\Delta = a$ and $t = 0$. For (c), $x \ne Px$ by hypothesis; if moreover $\Delta(x) \le 0$ with $\|x\| \le 1$, both $1 - \|x\|^2$ and $a^2$ vanish, so $\|x\| = 1$ and $\langle x, Px\rangle = 1$; then $\|x - Px\|^2 = \|Px\|^2 - 1 \le 0$ and $Px = x$. For (d), the norm is smooth away from $0$ and the square root on $(0, \infty)$.

### V2.10 Lemma 5 for the disk and the smooth Brouwer theorem

**Theorem (V2.10).** Let $E$ be a finite-dimensional real inner product space with closed unit ball $D$, and let $P : E \to E$ be smooth with $P(D) \subseteq D$. Then $P(x) = x$ for some $x \in D$. ⟦Chapter2/Brouwer · exists_fixedPoint_of_contDiff⟧

Smoothness on all of $E$ is how a smooth self-map of the disk is represented; V2.11 removes the assumption. Milnor's Lemma 5, that a compact manifold with boundary has no smooth retraction onto its boundary, is proved inside this proof and for the disk only.

*The idea* is Milnor's. A fixed-point-free $P$ yields a smooth retraction $f$ of $D$ onto the sphere. For a regular value $y$, the set $f^{-1}(y) \cap D$ is a compact 1-manifold with boundary $\{y\}$, whereas compact 1-manifolds have an even number of boundary points. Two adjustments make this formal: the retraction is extended by a cutoff to all of $E$, so that no manifold with boundary is ever a domain, and it is corestricted to the sphere (V2.8).

*The proof as formalized.* Suppose $P$ has no fixed point in $D$.

1. If $\dim E = 0$, then $0$ is fixed. Otherwise let $n = \dim E$ and fix $e \ne 0$. The model spaces of dimensions $n - 1$, $1$ and $0$ are taken inside $E$: the hyperplane $e^\perp$, the line $\mathbb R e$ and the zero subspace.
2. With $g(x) = 1 - \|x\|^2$, the sphere $S = g^{-1}(0)$ is a slice submanifold modelled on $e^\perp$, by Lemma 1 and the regular value of V2.7 ⟦Chapter2/LevelSet · isSliceSubmanifold_preimage⟧ ⟦Chapter2/Disk · isRegularValue_diskFun⟧.
3. By V2.9, $\Omega_P$ is open and contains the compact set $D$, so it contains the closed ball of radius $1 + \delta$ for some $\delta > 0$ ⟦Chapter2/Brouwer · closedBall_subset_cthickening_closedBall⟧. With $h$ Mathlib's smooth transition function ($0$ on $(-\infty, 0]$, $1$ on $[1, \infty)$, values in $[0, 1]$), the cutoff
$$\chi_\delta(x) = \Big(1 - h\Big(\frac{\|x\|^2 - 1}{(1 + \delta)^2 - 1}\Big)\Big)\, x$$
is smooth, is the identity on $D$, and takes values in that ball ⟦Chapter2/Brouwer · cutoff_contDiff⟧ ⟦Chapter2/Brouwer · cutoff_eq_self⟧ ⟦Chapter2/Brouwer · norm_cutoff_le⟧. So $F = r \circ \chi_\delta : E \to E$ is smooth, $\|F(x)\| = 1$ everywhere, and $F(x) = x$ on $S$ by V2.9(b), since $\chi_\delta$ fixes $D$ and $P(D) \subseteq D$.
4. By V2.8, $F$ is a smooth map $f : E \to S$ with $f \circ \iota = \mathrm{id}_S$, where $\iota : S \to E$ is the inclusion ⟦Chapter2/Corestrict · contMDiff_codRestrict⟧.
5. $E$ is second countable, so by Brown's theorem (Part II) the regular values of $f$ are dense in $S$, which is nonempty as it contains $f(0)$; pick one, $y$ ⟦Chapter2/Brown · dense_regularValues⟧.
6. *Transversality.* For $x \in S$ with $f(x) = y$, the map $df_x : E \to e^\perp$ is onto and $\dim E > \dim e^\perp$, so it kills some $v \ne 0$. If $dg_x(v) = 0$, Lemma 2 for $S$ gives $v = d\iota_x(w)$ ⟦Chapter2/LevelSet · mem_range_mfderiv_val_iff⟧, and differentiating $f \circ \iota = \mathrm{id}$ gives $w = df_x(v) = 0$, so $v = 0$. Hence $df_x(v) = 0 \ne dg_x(v)$. This is Milnor's observation that $y$ is regular for $f$ on the boundary, where $f$ is the identity, in the form Lemma 4 needs.
7. By V2.6 with $Z = \mathbb R e$ and $Z' = 0$, inside the 1-manifold $f^{-1}(y)$ the set $X = \{g \ge 0\}$ is a half-slice submanifold over the zero space with boundary $B = \{g = 0\}$ ⟦Chapter2/WithBoundary · isHalfSliceSubmanifold_levelSet⟧.
8. $X$ is compact: the inclusion $f^{-1}(y) \to E$ is an embedding carrying $X$ onto $f^{-1}(y) \cap D$, a closed subset of $D$. The half-space over the zero space is a half-line, and the Appendix, in the form proved for this situation, says that a compact half-slice submanifold over a zero-dimensional space, in a Hausdorff manifold and with $B \subseteq X$, has finitely many boundary points, an even number ⟦Appendix/HalfSpace · IsHalfSliceSubmanifold.even_ncard_boundary⟧. But $B = \{y\}$: a point $q \in B$ lies on $S$, where $f(q) = q$, while $f(q) = y$; and $f(y) = y$. One boundary point is not an even number, which is the contradiction. ⟦Chapter2/Brouwer · exists_fixedPoint_of_contDiff⟧

*Where the formal proof departs from Milnor.* Besides the cutoff ⟦Chapter2/Brouwer · cutoff⟧ and the restriction of Lemma 5 to the disk, every fact Milnor takes for granted is proved: the retraction is smooth, lands in the sphere and fixes it; the level set is compact; $y$ is regular for the restriction to the boundary.

### V2.11 Brouwer's fixed point theorem

**Theorem (V2.11).** Let $E$ be a finite-dimensional real inner product space with closed unit ball $D$, and let $G : E \to E$ be continuous on $D$ with $G(D) \subseteq D$. Then $G(x) = x$ for some $x \in D$. ⟦Chapter2/Brouwer · exists_fixedPoint⟧

*The idea* is Milnor's reduction to the smooth case by approximation, with one substitution: the approximating map is smooth rather than polynomial, and comes from the Stone–Weierstrass theorem.

*The proof as formalized.*

1. Suppose not. The continuous function $x \mapsto \|G(x) - x\|$ attains its minimum $\mu$ on the compact set $D$, and $\mu > 0$.
2. The functions on $D$ that extend to smooth functions on $E$ form a subalgebra of $C(D, \mathbb R)$ ⟦Chapter2/Brouwer · smoothSubalgebra⟧, and it separates points: for $x \ne y$, the linear function $z \mapsto \langle z, y - x\rangle$ takes different values at $x$ and $y$ ⟦Chapter2/Brouwer · smoothSubalgebra_separatesPoints⟧. Let $b_1, \dots, b_N$ be an orthonormal basis, $N = \dim E$. By Stone–Weierstrass on the compact set $D$, each coordinate $\langle b_i, G\rangle$ is within $\varepsilon/(N + 1)$ of some smooth $F_i$ on $D$, so $P_1 = \sum_i F_i\, b_i$ is smooth and on $D$
$$\|P_1 - G\| \le \sum_i |F_i - \langle b_i, G\rangle| \le \frac{N\varepsilon}{N + 1} < \varepsilon$$
⟦Chapter2/Brouwer · exists_contDiff_approx⟧. Take $\varepsilon = \mu/2$.
3. With $c = 1 + \mu/2$ put $P = P_1/c$. On $D$, $\|P_1\| \le \|G\| + \mu/2 \le c$, so $P(D) \subseteq D$, and $P$ is smooth.
4. By V2.10, $P(x) = x$ for some $x \in D$ ⟦Chapter2/Brouwer · exists_fixedPoint_of_contDiff⟧. Now $\|P(x) - P_1(x)\| = (1 - c^{-1})\|P_1(x)\| \le c - 1 = \mu/2$, so
$$\|G(x) - x\| = \|P(x) - G(x)\| \le \|P(x) - P_1(x)\| + \|P_1(x) - G(x)\| < \mu,$$
contradicting the minimality of $\mu$. ⟦Chapter2/Brouwer · exists_fixedPoint⟧

Milnor approximates by a polynomial map with error $\varepsilon$ and divides by $1 + \varepsilon$; the formal proof does the same with $\varepsilon = \mu/2$ and a smooth map.

### What the formalization taught us

- **Separation axioms become hypotheses.** Finiteness of a regular fibre needs points of the target closed; local constancy needs both manifolds Hausdorff ⟦Chapter1/RegularValue · IsRegularValue.finite_preimage⟧ ⟦Chapter1/RegularValue · IsRegularValue.eventually_ncard_preimage_eq⟧.
- **The inverse function theorem between manifolds had to be proved**, with smoothness on a neighbourhood rather than at a point, and with invertibility of the derivative propagated to a neighbourhood so that the Euclidean inverse is smooth on an open set ⟦Chapter1/InverseFunction · eventually_isInvertible_fderiv⟧.
- **Local constancy is stronger than stated**: the count is constant for all values near a regular value, and those values are automatically regular ⟦Chapter1/RegularValue · IsRegularValue.eventually_isRegularValue_and_ncard⟧.
- **The fundamental theorem of algebra** is proved on $\mathbb C \cup \{\infty\}$, which removes Milnor's conjugates ⟦Chapter1/FTA · contMDiffAt_polyMap_infty⟧; $\infty$ is put among the bad values instead of being classified; and the existence of a regular value in the image, which Milnor takes for granted, is proved from the infinitude of $P(\mathbb C)$ ⟦Chapter1/FTA · exists_regularValue_mem_range⟧.
- **Submanifolds must be built.** The slice charts are exactly the diffeomorphisms of Milnor's proof of Lemma 1, with a base point added for formal reasons ⟦Chapter2/Submanifold · SliceChart⟧, and dimensions are carried by the choice of model spaces ⟦Chapter2/LevelSet · isSliceSubmanifold_preimage⟧.
- **Well-definedness of the boundary is replaced by construction**: charts must send exactly the prescribed boundary to $\{t = 0\}$ ⟦Chapter2/Boundary · boundary_eq⟧.
- **Lemma 4's hypothesis is transversality**, the region is $\{g \ge 0\}$ in a manifold without boundary, $y$ must be regular on the whole ambient manifold, and $0$ need not be regular for $g$ ⟦Chapter2/WithBoundary · isHalfSliceSubmanifold_levelSet⟧.
- **Silent identifications are lemmas**: maps into a slice submanifold are smooth into it ⟦Chapter2/Corestrict · contMDiff_codRestrict⟧, and the regularity of $y$ on the boundary in the Brouwer argument is derived from Lemma 2 and the chain rule ⟦Chapter2/Brouwer · exists_fixedPoint_of_contDiff⟧.
- **What Milnor leaves to the reader in Lemma 6 is a page of inequalities**: positivity of the radicand rests on the fact that $\|x\| = 1$, $\|Px\| \le 1$ and $\langle x, Px\rangle = 1$ force $Px = x$ ⟦Chapter2/Retraction · closedBall_subset_good⟧, and a cutoff extends the retraction to all of $E$ ⟦Chapter2/Brouwer · cutoff⟧.
- **Stone–Weierstrass replaces Weierstrass**, applied to the functions on the ball that extend smoothly to $E$ ⟦Chapter2/Brouwer · exists_contDiff_approx⟧.


## Part II. Sard's theorem and the degree modulo 2 (Milnor §3–§4)

Milnor's §3 proves that critical values are rare, and §4 turns this into the first global invariant of the book, the degree modulo 2. The formal proof of Sard's theorem keeps Milnor's induction on the dimension of the domain, and his Steps 1 and 2 almost line by line, made coordinate-free; Step 3, the cube count, becomes a Hölder estimate for Hausdorff dimension taken from Mathlib. Brown's theorem carries the result to manifolds, with second countability made explicit. In §4 the Homotopy Lemma is Lemma 4 on a cylinder plus the Appendix; the Homogeneity Lemma is proved with explicit bump-function diffeomorphisms of a chart instead of flows; the theorem of §4, which Milnor states as a single unlettered Theorem with two assertions, follows as in the book, with the degree defined through a chosen regular value. The docstrings of the formal source call its two assertions "Theorem B" and "Theorem A"; here they are the first and second assertions of the Theorem of §4. Throughout, manifolds are modelled on finite-dimensional real normed spaces, "without boundary" means that the model has no boundary, smooth means $C^\infty$, and Hausdorff or second countable is said whenever it is assumed.

**Map.**
- `Chapter3/Basic`: Milnor's sets $C$ and $C_1 \supseteq C_2 \supseteq \cdots$, the statement proved by induction, closedness of $C$ in $U$, and "Hausdorff dimension below $\dim F$ implies Haar-null".
- `Chapter3/Straighten`: the coordinate change $h(x) = (w(x), x_2, \dots, x_n)$, without coordinates.
- `Chapter3/Step1`: Step 1, $f(C \setminus C_1)$ is null, by Fubini.
- `Chapter3/Step2`: Step 2, $f(C_k \setminus C_{k+1})$ is null; the countable-cover lemma.
- `Chapter3/Step3`: Step 3, a Taylor bound and the Hölder estimate for $f(C_k)$.
- `Chapter3/Sard`: the induction, Sard's theorem, density of regular values.
- `Chapter2/Brown`: Brown's theorem on manifolds.
- `Chapter4/Cylinder`: Lemma 4 with two boundary functions.
- `Chapter4/Homotopy`: transversality at the ends of the cylinder; the Homotopy Lemma.
- `Chapter4/BumpDiffeo`: for a bump function $\varphi$ and small $c$, $u \mapsto u + \varphi(u)c$ is a diffeomorphism of the model space.
- `Chapter4/Homogeneity`: transport through a chart, isotopy, the Homogeneity Lemma.
- `Chapter4/Degree`: the Theorem of §4 (independence of the regular value and homotopy invariance), the degree modulo 2, maps of nonzero degree are onto.

### V3.1 Sard's theorem

> **Theorem.** Let $E$ and $F$ be finite-dimensional real normed spaces and $\mu$ an additive Haar measure on the Borel sets of $F$. Let $U \subseteq E$ be open, $f : E \to F$ of class $C^\infty$ on $U$, and $C = \{x \in U : df_x \text{ is not surjective}\}$. Then $\mu(f(C)) = 0$. ⟦Chapter3/Sard · sard⟧

The map is defined on all of $E$ for convenience; its values off $U$ play no role. (Formally $E$ and $F$ must also lie in one type universe, here and in most statements below; this is bookkeeping without mathematical content.)

*The idea.* Induct on $n = \dim E$. Let $C_k$ be the set where all derivatives of orders $1$ to $k$ vanish; $C$ is covered by $C \setminus C_1$, the layers $C_i \setminus C_{i+1}$, and $C_k$. On the first two kinds of piece a straightening coordinate reduces the problem to dimension $n - 1$, through Fubini's theorem for $C \setminus C_1$ and directly for the layers. On $C_k$, for $k$ large, a Taylor estimate makes $f$ so flat that the image is too thin to carry measure. Every piece is treated near one point and globalized by a countable cover.

#### The objects, and the statement proved by induction

The formal $C$ and $C_k$ are Milnor's: $C$ is the set of $x \in U$ at which the Fréchet derivative $df_x$ is not onto, and
$$C_k = \{x \in U : D^j f(x) = 0 \text{ for } 1 \le j \le k\},$$
with $D^j f(x)$ the $j$-th derivative as a $j$-linear map, so that $C_0 = U$ and the $C_k$ decrease ⟦Chapter3/Basic · critSet⟧ ⟦Chapter3/Basic · vanishSet⟧ ⟦Chapter3/Basic · vanishSet_antitone⟧. Of Milnor's decomposition only the inclusion $C \subseteq (C \setminus C_1) \cup \bigcup_{1 \le i < k} (C_i \setminus C_{i+1}) \cup C_k$ is proved, by taking the last $i$ with $x \in C_i$ ⟦Chapter3/Basic · critSet_subset_union⟧.

The induction runs over the statement $S(n)$: *for every finite-dimensional real normed space $E$ of dimension $n$, every finite-dimensional $F$ with any Haar measure $\mu$, every open $U \subseteq E$ and every $f$ of class $C^\infty$ on $U$, $\mu(f(C)) = 0$* ⟦Chapter3/Basic · SardStatement⟧. The quantification over all targets and all Haar measures is forced by the proof. Step 1 applies the hypothesis to a map from a hyperplane $K \subseteq E$ to a hyperplane $F_1 \subseteq F$, with a freshly chosen Haar measure on $F_1$; Step 2 applies it to a map from $K$ into $F$ with the original $\mu$. Neither hyperplane is $\mathbb R^{n-1}$ or $\mathbb R^{p-1}$ on the nose, and admitting every Haar measure makes the choice of measure on them irrelevant.

#### Null sets, measurability, countable covers, smoothness

Three devices carry the measure theory.

*Countable covers.* For any measure $\mu$ on $F$, any map $f$ and any sets $S, T \subseteq E$: if every $x \in S$ has a neighbourhood $V$ with $\mu(f(T \cap V)) = 0$, then $\mu(f(T \cap S)) = 0$, because $E$ is second countable and countably many of the $V$ cover $S$ ⟦Chapter3/Step2 · measure_image_eq_zero_of_locally⟧. This is Milnor's "covered by countably many such sets $V$", invoked once for each step.

*Measurability, only where Fubini needs it.* Mathlib's measures are defined on all subsets and a subset of a null set is null, so Steps 2 and 3 never ask whether a set is measurable. Step 1 does. Where Milnor writes his set of critical values as a countable union of compact sets, the formal proof takes its neighbourhood to be a closed ball $B$ and uses that $C \cap B$ is compact. This holds for every compact $B \subseteq U$ once $f$ is $C^1$, because surjectivity is an open condition on linear maps: if $LR = 1$, then $L'R$ is invertible for $L'$ near $L$ ⟦Chapter3/Basic · isOpen_setOf_surjective⟧ ⟦Chapter3/Basic · isCompact_critSet_inter⟧.

*Dimension and Haar measure.* A set $s \subseteq F$ of Hausdorff dimension less than $p = \dim F$ is null for every Haar measure: a linear isomorphism from $F$ onto the space of functions $\{0, \dots, p-1\} \to \mathbb R$ with the maximum norm does not raise dimension; for that norm the $p$-dimensional Hausdorff measure equals Lebesgue measure (for the Euclidean norm the two would differ by a constant factor), so the image is Lebesgue-null; and Haar measures are mutually absolutely continuous ⟦Chapter3/Basic · addHaar_eq_zero_of_dimH_lt_finrank⟧.

*Smoothness.* The hypothesis is $C^\infty$ on $U$ (not analyticity), and the proof never counts derivatives. It needs $C^\infty$ to keep the induction closed: the maps to which $S(n-1)$ is applied are composites of $f$ with the inverse of a straightening, and in Step 2 the function straightened is built from $D^k f$, which is $C^\infty$ because $f$ is ⟦Chapter3/Step2 · contDiffOn_iteratedFDeriv⟧. Individual lemmas ask for less (closedness of $C$ is proved for $C^1$ maps), but no finite-smoothness version of the theorem is attempted.

#### The induction

1. *Zero target.* If $F = 0$, every linear map to $F$ is onto and $C = \emptyset$ ⟦Chapter3/Sard · critSet_eq_empty_of_subsingleton⟧. In each case of the induction it is dispatched first. On the zero space a Haar measure is a positive multiple of the point mass, and the arguments below use $F \ne 0$ in three places: points must be null, a vanishing derivative must be critical ⟦Chapter3/Step2 · mem_critSet_of_fderiv_eq_zero⟧, and Step 3 needs $p \ge 1$. The theorem survives only because $C$ is empty.
2. *$n = 0$, $F \ne 0$.* $E$ is a point, so $f(C)$ has at most one point, which is null.
3. *$n = m + 1$, $p = \dim F \ge 1$.* Take $k = n$; then $(k+1)p > n$. Milnor asks only for $k > n/p - 1$; the uniform choice costs extra layers in Step 2 and nothing else.
4. *Assembly.* $f(C \setminus C_1)$ is null by the cover lemma and Step 1; each $f(C_i \setminus C_{i+1})$, $1 \le i < k$, by the cover lemma and Step 2; $f(C_k)$ by the cover lemma and Step 3 on a closed ball inside $U$ around each point of $C_k$ ⟦Chapter3/Sard · sardStatement⟧. Theorem V3.1 is $S(\dim E)$ ⟦Chapter3/Sard · sard⟧.

When $p = 1$, Step 1 lands in the zero target $F_1 = 0$, where the induction hypothesis is case 1; no separate treatment is needed.

#### The straightening

Milnor's coordinate change $h(x) = (w(x), x_2, \dots, x_n)$ becomes: given $w$ of class $C^\infty$ on an open set $U$ and $x_0 \in U$ with $\ell = dw_{x_0} \ne 0$, choose $v$ with $\ell(v) = 1$, let $K = \ker \ell$ (so $\dim K + 1 = \dim E$) and $P(x) = x - \ell(x)v$, and set
$$H(x) = (w(x), P(x)) \in \mathbb R \times K .$$
Its derivative at $x_0$ is $(\ell, P)$, with inverse $(t, z) \mapsto z + tv$. The inverse function theorem of Chapter 1 (V1.1) yields open sets $V \ni x_0$ in $U$ and $V' \subseteq \mathbb R \times K$ and a $C^\infty$ map $G : V' \to V$ inverse to $H|_V$; the first coordinate of $H(x)$ is $w(x)$ for every $x$ ⟦Chapter3/Straighten · Straightening⟧ ⟦Chapter3/Straighten · exists_straightening⟧.

#### Step 1: $f(C \setminus C_1)$ is null

> **Step 1.** Assume $S(n-1)$, $n = \dim E$. Let $F \neq 0$ carry a Haar measure $\mu$, let $f$ be $C^\infty$ on the open set $U$, and $x_0 \in C \setminus C_1$. Then $x_0$ has a neighbourhood $V$ with $\mu(f(C \cap V)) = 0$. ⟦Chapter3/Step1 · step1_local⟧

1. *The coordinate.* As $x_0 \notin C_1$, $df_{x_0}u \ne 0$ for some $u$, and Hahn–Banach gives a functional $\ell_0$ on $F$ with $\ell_0(df_{x_0}u) = \|df_{x_0}u\|$. The function $w = \ell_0 \circ f$, which plays the role of Milnor's $f_1$, has $dw_{x_0} \ne 0$ and is straightened.
2. *The target.* Put $y_0 = df_{x_0}u / \ell_0(df_{x_0}u)$, $F_1 = \ker \ell_0$ and $Q(y) = y - \ell_0(y)y_0$; then $e(y) = (\ell_0(y), Q(y))$ is a linear isomorphism $F \to \mathbb R \times F_1$. The level sets of $\ell_0$ replace Milnor's hyperplanes $t \times \mathbb R^{p-1}$, and $Q$ identifies them with $F_1$.
3. *The slices.* $g = f \circ G$ is $C^\infty$ on $V'$ with $\ell_0(g(t,z)) = t$: $g$ carries hyperplanes into hyperplanes. With $V_t = \{z \in K : (t,z) \in V'\}$ and $g^t(z) = Q(g(t,z))$, the hypothesis $S(n-1)$, for a Haar measure $\mu_1$ on $F_1$, makes the critical values of each $g^t$ a $\mu_1$-null set.
4. *Half of the block-matrix remark.* If $(t, z)$ is critical for $g$, then $z$ is critical for $g^t$. With $D = dg_{(t,z)}$, differentiating $\ell_0 \circ g = \mathrm{pr}_1$ gives $\ell_0 \circ D = \mathrm{pr}_1$, and $d(g^t)_z u = Q\,D(0,u)$. If $d(g^t)_z$ is onto and $y \in F$, choose $u'$ with $Q\,D(0,u') = Q(y - D(\ell_0(y), 0))$; both vectors lie in $\ker \ell_0$, where $Q$ is the identity, so $D(\ell_0(y), u') = y$. Milnor states an equivalence; the converse is neither needed nor proved.
5. *A compact neighbourhood.* Take a closed ball $B \subseteq V$ around $x_0$; then $T = f(C \cap B)$ is compact.
6. *Slices of $e(T)$.* For every $t$, the slice $\{y_1 : (t, y_1) \in e(T)\}$ lies in the critical values of $g^t$. If $y_1$ comes from $x \in C \cap B$, then $H(x) = (t, z)$ with $g(H(x)) = f(x)$; $H(x)$ is critical for $g$, since $dg_{H(x)} = df_x \circ dG_{H(x)}$ and $df_x$ is not onto; so $z$ is critical for $g^t$ by step 4, and $g^t(z) = Q(f(x)) = y_1$.
7. *Fubini.* $e(T)$ is compact, hence measurable, and all its slices are $\mu_1$-null, so $(\lambda \otimes \mu_1)(e(T)) = 0$, $\lambda$ Lebesgue measure. The image of $\mu$ under $e$ is a Haar measure on $\mathbb R \times F_1$, hence absolutely continuous with respect to $\lambda \otimes \mu_1$, and $\mu(T) = 0$: the ball $B$ is the neighbourhood sought.

The hypothesis $F \ne 0$ is automatic here, since $df_{x_0} \ne 0$.

#### Step 2: $f(C_k \setminus C_{k+1})$ is null

> **Step 2.** Assume $S(n-1)$. Let $F \ne 0$ carry a Haar measure $\mu$, let $f$ be $C^\infty$ on the open set $U$, $k \ge 1$, and $x_0 \in C_k \setminus C_{k+1}$. Then $x_0$ has a neighbourhood $V$ with $\mu(f(C_k \cap V)) = 0$. ⟦Chapter3/Step2 · step2_local⟧

1. *The function to straighten.* Since $D^{k+1}f(x_0) \ne 0$ (as $x_0 \notin C_{k+1}$), choose $m_0, \dots, m_k \in E$ and a functional $\ell_0$ with $\ell_0(D^{k+1}f(x_0)(m_0, \dots, m_k)) \ne 0$, and put $w(x) = \ell_0(D^k f(x)(m_1, \dots, m_k))$, Milnor's $\partial^k f_r / \partial x_{s_2} \cdots \partial x_{s_{k+1}}$ without coordinates. Then $w$ is $C^\infty$, vanishes on $C_k$, and $dw_{x_0}(m_0) \ne 0$ by the identity $D^{k+1}f(x)(m_0, \dots, m_k) = (D(D^kf)(x)\,m_0)(m_1, \dots, m_k)$.
2. *Restriction to the hyperplane.* Straighten $w$. As $w = 0$ on $C_k$, $H$ maps $C_k \cap V$ into $\{0\} \times K$. Let $V_0 = \{z : (0,z) \in V'\}$ and $\bar g(z) = f(G(0,z))$; the hypothesis $S(n-1)$ is applied to $\bar g : V_0 \to F$ with the original $\mu$.
3. *Critical points.* For $x \in C_k \cap V$ write $H(x) = (0, z)$; then $\bar g(z) = f(x)$ and $d\bar g_z = df_x \circ d(G \circ \iota)_z = 0$, with $\iota(z) = (0,z)$, because $df_x = 0$; a zero map to $F \ne 0$ is not onto ⟦Chapter3/Step2 · fderiv_eq_zero_of_mem_vanishSet⟧ ⟦Chapter3/Step2 · mem_critSet_of_fderiv_eq_zero⟧. Hence $f(C_k \cap V)$ lies in the null set of critical values of $\bar g$.

The neighbourhood is the open set $V$ itself; no measurability is involved. Milnor's reason, "since all derivatives of order $\le k$ vanish", is more than is used: only $df_x = 0$ matters.

#### Step 3: the cube estimate as a Hölder estimate

Milnor cuts a cube of edge $\delta$ into $r^n$ subcubes, notes that each subcube meeting $C_k$ is mapped into a cube of edge $a/r^{k+1}$, and bounds the total volume by $a^p r^{n-(k+1)p} \to 0$. The formal proof separates two ingredients: a Taylor bound, saying that $f$ is Hölder of exponent $k+1$ on $C_k$, and the library theorem that a map Hölder of exponent $\alpha$ multiplies Hausdorff dimension by at most $1/\alpha$, whose proof is the same covering argument.

> **Taylor bound.** Let $G$ be a real normed space, $f : E \to G$ of class $C^\infty$ on the open set $U$, $A \subseteq U$ convex, $\|D^{k+1}f\| \le c$ on $A$, and $x \in A$ with $D^j f(x) = 0$ for $1 \le j \le k$. Then $\|f(y) - f(x)\| \le c\,\|y - x\|^{k+1}$ for all $y \in A$. ⟦Chapter3/Step3 · norm_sub_le_of_iteratedFDeriv_eq_zero⟧

The proof is an induction on $k$ in which the target changes, which is why the statement quantifies over all $G$. For $k = 0$ it is the mean value inequality on the segment $[x, y] \subseteq A$. For $k + 1$, apply the case $k$ to $df : E \to L(E, G)$, using $\|D^j(df)\| = \|D^{j+1}f\|$ and $df_x = 0$, to get $\|df_z\| \le c\,\|z - x\|^{k+1}$ on $A$; on the segment $\|z - x\| \le \|y - x\|$ ⟦Chapter3/Step3 · norm_sub_le_of_mem_segment⟧, and the mean value inequality gives $c\,\|y-x\|^{k+2}$. The constant is $c$, not Taylor's $c/(k+1)!$: bounding by the supremum on the segment gives the factorial away, harmlessly.

> **Step 3.** Let $\mu$ be a Haar measure on $F$, $f$ of class $C^\infty$ on the open set $U$, $n < (k+1)p$, and $A \subseteq U$ compact and convex. Then $\mu(f(C_k \cap A)) = 0$. ⟦Chapter3/Step3 · measure_image_vanishSet_inter_eq_zero⟧

For nonempty $A$ let $c$ bound $\|D^{k+1}f\|$ on $A$. The Taylor bound gives $\|f(y) - f(x)\| \le c\,\|y - x\|^{k+1}$ for $x, y \in C_k \cap A$, so $\dim_H f(C_k \cap A) \le \dim_H (C_k \cap A)/(k+1) \le n/(k+1) < p$, and the set is null.

*Where the formal proof departs from Milnor.* The counting is done once, for Hausdorff dimension, in the library, and Milnor's cubes become closed balls, the natural compact convex neighbourhoods in a space without coordinates.

### V3.2 Density of regular values

> **Theorem.** Let $E$, $F$ be finite-dimensional real normed spaces, $F$ with its Borel σ-algebra, $U \subseteq E$ open, $f$ of class $C^\infty$ on $U$, and $C$ as in V3.1. Then $F \setminus f(C)$ is dense in $F$. ⟦Chapter3/Sard · dense_compl_image_critSet⟧

Choose any Haar measure: $f(C)$ is null by V3.1, and a Haar measure charges every nonempty open set, so $f(C)$ has empty interior.

### V3.3 Brown's theorem

> **Theorem.** Let $M$ and $N$ be smooth manifolds without boundary, modelled on finite-dimensional real normed spaces $E$ and $F$ of arbitrary dimensions, with $M$ second countable, and let $f : M \to N$ be smooth. Then the regular values of $f$ are dense in $N$. ⟦Chapter2/Brown · dense_regularValues⟧

A point $x$ is critical if $df_x$, read in charts, is not onto; $y$ is a regular value if every point of $f^{-1}(y)$ is regular. So a point outside $f(M)$ is a regular value, and the regular values are the complement of the image of the critical set ⟦Chapter2/Brown · critPoints⟧ ⟦Chapter1/RegularValue · IsRegularValue⟧ ⟦Chapter2/Brown · regularValues_eq_compl_image_critPoints⟧.

*The idea.* Milnor's proof is the clause that $M$ is covered by countably many neighbourhoods diffeomorphic to open subsets of $\mathbb R^m$. The formal proof argues by contradiction inside a single chart of $N$, so only the source needs countability.

1. Suppose a nonempty open $W \subseteq N$, containing $y_1$, consists of critical values. Let $\psi$ be the chart of $N$ at $y_1$, with values in $F$, and $\mu$ a Haar measure on $F$.
2. By second countability, countably many chart domains $\operatorname{dom}\varphi_{x_0}$, $x_0 \in S$, cover $M$.
3. For each $x_0$ the set $U_{x_0}$ of points $u$ in the (open) image of $\varphi_{x_0}$ with $f(\varphi_{x_0}^{-1}(u)) \in \operatorname{dom}\psi$ is open, and $\psi \circ f \circ \varphi_{x_0}^{-1}$ is $C^\infty$ on it; by V3.1 its critical values are $\mu$-null.
4. If $x$ is critical, $x \in \operatorname{dom}\varphi_{x_0}$ and $f(x) \in \operatorname{dom}\psi$, then $\varphi_{x_0}(x)$ is critical for $\psi \circ f \circ \varphi_{x_0}^{-1}$: in the chain rule $d\psi \circ df_x \circ d(\varphi_{x_0}^{-1})$ the factor $d\psi$ is injective, with left inverse $d(\psi^{-1})$, so surjectivity of the composite would force that of $df_x$ ⟦Chapter2/Brown · mfderiv_extChartAt_injective⟧ ⟦Chapter2/Brown · mem_critSet_of_mem_critPoints⟧. Only this direction is proved.
5. Hence $\psi(W \cap \operatorname{dom}\psi)$ lies in a countable union of null sets. But it is a neighbourhood of $\psi(y_1)$, as $N$ has no boundary, and so has positive measure: contradiction.

*What the book leaves implicit.* Second countability of $M$, automatic for subsets of $\mathbb R^k$. Nothing else: no Hausdorff property, no relation between $\dim M$ and $\dim N$, no countability of $N$, which only supplies one chart and a measure on its model space.

### V4.1 Lemma 4 for the cylinder

*Two conventions.* A smooth homotopy is a smooth $F : M \times \mathbb R \to N$ on the product manifold, with ends $F(\cdot, 0)$ and $F(\cdot, 1)$. Its domain is thus a manifold without boundary, to which Lemma 4 in the form V2.6 and Brown's theorem apply directly, and level sets are cut down to $M \times [0,1]$ by hand ⟦Chapter4/Homotopy · homotopy_lemma_of_isRegularValue⟧ ⟦Chapter4/Homotopy · homotopy_lemma⟧. A manifold with boundary is a *half-slice submanifold* (V2.4): a set $X$ with boundary $B$ inside an ambient manifold (here always one without boundary), each point of $X$ lying in the domain of a diffeomorphism onto an open subset of $\mathbb R \times Z'$ under which, on that domain, $X$ corresponds to $\{t \ge 0\}$ and $B$ to $\{t = 0\}$ ⟦Chapter2/Boundary · HalfSliceChart⟧ ⟦Chapter2/Boundary · IsHalfSliceSubmanifold⟧.

> **Lemma.** Let $M$, $N$ be smooth manifolds without boundary, $f : M \to N$ smooth, $y$ a regular value, and $Z$, $Z'$ finite-dimensional with $\dim Z + \dim N = \dim M$ and $\dim Z' + 1 = \dim Z$. Let $g_0, g_1 : M \to \mathbb R$ be smooth, such that (i) for $i = 0, 1$ and each $x \in f^{-1}(y)$ with $g_i(x) = 0$ some $v$ has $df_x v = 0$ and $(dg_i)_x v \ne 0$, and (ii) $g_0$ and $g_1$ never vanish together on $f^{-1}(y)$. Then, inside the manifold $f^{-1}(y)$ modelled on $Z$ (Lemma 1), the set $\{g_0 \ge 0,\ g_1 \ge 0\}$ is a half-slice submanifold over $Z'$ with boundary $\{g_0 = 0\} \cup \{g_1 = 0\}$. ⟦Chapter4/Cylinder · isHalfSliceSubmanifold_levelSet_two⟧

*The idea.* Being a manifold with boundary is local, and near each point at most one of the two functions matters.

*Proof as formalized.* Lemma 4 (V2.6) for $g_0$ and for $g_1$ gives half-slice structures for $\{g_0 \ge 0\}$ and $\{g_1 \ge 0\}$ in $f^{-1}(y)$ ⟦Chapter2/WithBoundary · isHalfSliceSubmanifold_levelSet⟧. A locality lemma restricts a half-slice chart to an open set on which two pairs $(X, B)$ agree ⟦Chapter4/Cylinder · IsHalfSliceSubmanifold.of_local⟧. At a point with $g_1 > 0$, use a chart for $g_0$ restricted to $\{g_1 > 0\}$, where the set is $\{g_0 \ge 0\}$ and the boundary $\{g_0 = 0\}$; at a point with $g_1 = 0$, (ii) gives $g_0 > 0$ and the roles are exchanged. The dimension hypotheses encode Milnor's $m > n$.

### V4.2 Transversality at the ends

> **Lemma.** Let $M$, $N$ be smooth manifolds without boundary of the same dimension, $M$ modelled on $E$. Let $F : M \times \mathbb R \to N$ be smooth, $y$ a regular value of $F$ and of $F(\cdot, c)$, and $F(x, c) = y$. Then some $v = (v_1, v_2) \in E \times \mathbb R$ has $dF_{(x,c)}v = 0$ and $v_2 \ne 0$. ⟦Chapter4/Homotopy · cylinder_transversality⟧

This makes precise the hypothesis of Milnor's Lemma 4 that $y$ be regular for the restriction of $F$ to $\partial(M \times [0,1])$: it is hypothesis (i) of V4.1 for $g_0 = t$ at $c = 0$ and $g_1 = 1 - t$ at $c = 1$. *Proof.* $dF_{(x,c)}$ maps a space of dimension $n + 1$ to one of dimension $n$, so it kills some $v \ne 0$; this step does not need $y$ to be regular for $F$, and the formal proof in fact never uses that hypothesis. If $v_2 = 0$ then, since $x \mapsto (x, c)$ has derivative $(\mathrm{id}, 0)$ ⟦Chapter4/Homotopy · hasMFDerivAt_inl⟧, $d(F(\cdot,c))_x v_1 = 0$; that derivative is a surjection between spaces of equal dimension, hence injective, so $v = 0$.

### V4.3 The Homotopy Lemma

> **Theorem.** Let $M$ be a compact, Hausdorff, second countable smooth manifold without boundary, $N$ a Hausdorff smooth manifold without boundary of the same dimension, $F : M \times \mathbb R \to N$ smooth, $f = F(\cdot, 0)$, $g = F(\cdot, 1)$. If $y$ is a regular value of $f$ and of $g$, then $\#f^{-1}(y) + \#g^{-1}(y)$ is even. ⟦Chapter4/Homotopy · homotopy_lemma⟧

The formal cardinality is $0$ on infinite sets, but every fibre counted in this part is finite, by compactness and regularity ⟦Chapter1/RegularValue · IsRegularValue.finite_preimage⟧.

*The idea.* Milnor's: if $y$ is also regular for $F$, then $F^{-1}(y) \cap (M \times [0,1])$ is a compact 1-manifold whose boundary is the two fibres, and a compact 1-manifold has an even number of boundary points. Otherwise, move $y$ a little.

*Case 1: $y$ regular for $F$ as well* (compactness and Hausdorff, no countability) ⟦Chapter4/Homotopy · homotopy_lemma_of_isRegularValue⟧.
1. $F^{-1}(y)$ is a 1-manifold modelled on $Z = \mathbb R$, as $\dim (M \times \mathbb R) - \dim N = 1$. Take $Z' = 0$, $g_0(x,t) = t$, $g_1(x,t) = 1 - t$.
2. V4.2 at $c = 0$ and $c = 1$ gives hypothesis (i) of V4.1, since $dg_0 v = v_2$ and $dg_1 v = -v_2$; (ii) holds because $t$ and $1 - t$ never vanish together. So $X = F^{-1}(y) \cap (M \times [0,1])$ is a half-slice submanifold of $F^{-1}(y)$ over the zero space, with boundary $B = F^{-1}(y) \cap (M \times \{0, 1\})$.
3. $X$ is compact: it is closed in $M \times [0,1]$, since points of $N$ are closed.
4. The Appendix (V.A′), for the Hausdorff 1-manifold $F^{-1}(y)$, shows $B$ finite with an even number of points ⟦Appendix/HalfSpace · IsHalfSliceSubmanifold.even_ncard_boundary⟧.
5. $B$ is the disjoint union of $f^{-1}(y) \times \{0\}$ and $g^{-1}(y) \times \{1\}$, both finite, so $\#B = \#f^{-1}(y) + \#g^{-1}(y)$.

*Case 2: general $y$.* Local constancy in its strengthened form (V1.4) gives an open $W \ni y$ of regular values of $f$ and of $g$ with the counts of $y$ ⟦Chapter1/RegularValue · IsRegularValue.eventually_isRegularValue_and_ncard⟧. Brown's theorem for the homotopy itself, on the second countable but noncompact $M \times \mathbb R$, gives a regular value $y' \in W$ of $F$, and Case 1 at $y'$ finishes.

*What the book leaves implicit.* The Hausdorff hypotheses, for finiteness, for local constancy and for the Appendix (applied to a level set in $M \times \mathbb R$); second countability, whose only use here is Brown's theorem for $F$; and the meaning of "regular on the boundary", which is V4.2.

### V4.4 The Homogeneity Lemma

> **Theorem.** Let $N$ be a Hausdorff, preconnected smooth manifold without boundary. For all $y, z \in N$ there are a diffeomorphism $h : N \to N$ with $h(y) = z$ and a smooth $H : N \times \mathbb R \to N$ with $H(\cdot, 0) = \mathrm{id}$, $H(\cdot, 1) = h$, and every $H(\cdot, t)$ a diffeomorphism. ⟦Chapter4/Homogeneity · Isotopic⟧ ⟦Chapter4/Homogeneity · isotopic_of_preconnected⟧

Preconnected means connected or empty, so for nonempty $N$ this is Milnor's hypothesis. The formal definition of "isotopic" records Milnor's full conclusion, an isotopy through diffeomorphisms.

*The idea.* "Isotopic" is an equivalence relation with open classes, and connectedness leaves one class. Openness is local: every point of a small chart neighbourhood of $y$ is reached from $y$ by a compactly supported diffeomorphism isotopic to the identity. Milnor obtains it from the flow of the vector field $u \mapsto \varphi(u)\,c$, $\varphi$ a bump function; the formal proof uses instead the explicit map
$$\mathrm{sh}_c(u) = u + \varphi(u)\,c$$
of the model space $V$ of $N$ ⟦Chapter4/BumpDiffeo · shift⟧.

*Why not the flow.* The flow needs the time-$t$ map of a compactly supported vector field to be smooth in the initial point and jointly in time; as the verified edition records, Mathlib lacks smooth dependence of flows on initial conditions. The shift needs only the contraction principle and the inverse function theorem, and $u + \sigma(t)\varphi(u)c$ is visibly smooth in $(u, t)$: it is one explicit Euler step for Milnor's vector field. The price is that $\mathrm{sh}_c$ is a diffeomorphism only for small $c$, so it moves $y$ only to nearby points, which is all the argument uses.

1. *The shift.* Let $\varphi$ be smooth and $L$-Lipschitz with $\|d\varphi\| \le L$ (a compactly supported smooth $\varphi$ has such an $L$ ⟦Chapter4/BumpDiffeo · exists_lipschitz_of_hasCompactSupport⟧), and $L\|c\| < 1$. Then $\mathrm{sh}_c$ is injective, because $u - v = \varphi(v)c - \varphi(u)c$ has norm at most $L\|c\|\,\|u - v\|$; surjective, because $u \mapsto w - \varphi(u)c$ is a contraction whose fixed point solves $\mathrm{sh}_c(u) = w$; and its inverse is smooth by the inverse function theorem, as $d\,\mathrm{sh}_c = 1 + d\varphi \otimes c$ is invertible by the Neumann series, $\|d\varphi \otimes c\| \le L\|c\| < 1$ ⟦Chapter4/BumpDiffeo · shift_injective⟧ ⟦Chapter4/BumpDiffeo · shift_surjective⟧ ⟦Chapter4/BumpDiffeo · shift_symm_contDiff⟧.
2. *Transport through a chart.* For the chart $\kappa$ at $y$, with open image in $V$, and $g : V \to V$, let $\tau(g)(p) = \kappa^{-1}(g(\kappa(p)))$ on the chart domain and $\tau(g)(p) = p$ elsewhere ⟦Chapter4/Homogeneity · transport⟧. If $g$ is smooth, maps the image of $\kappa$ into itself, and is the identity outside a compact subset $A$ of that image, then $\tau(g)$ is smooth: on the chart domain it is a composite of smooth maps, and near a point off the chart domain it is the identity, because $\kappa^{-1}(A)$ is compact and hence closed. This is the single use of the Hausdorff hypothesis ⟦Chapter4/Homogeneity · isClosed_image_symm_of_isCompact⟧ ⟦Chapter4/Homogeneity · contMDiff_transport⟧. Transports of mutually inverse maps are mutually inverse ⟦Chapter4/Homogeneity · transport_transport⟧.
3. *The local construction.* Choose $\varepsilon > 0$ with the $\varepsilon$-ball about $\kappa(y)$ inside the image of $\kappa$, let $\varphi$ be the smooth bump equal to $1$ on the $\varepsilon/4$-ball and $0$ outside the $\varepsilon/2$-ball, and take $L$ as in step 1. For $z$ in the chart domain with $\|\kappa(z) - \kappa(y)\| < 1/(L+1)$ put $c = \kappa(z) - \kappa(y)$, so $L\|c\| < 1$. With $\sigma$ Mathlib's smooth transition function ($0$ on $(-\infty,0]$, $1$ on $[1,\infty)$, values in $[0,1]$), every $\sigma(t)c$ is admissible. Each $\mathrm{sh}_{\sigma(t)c}$ and its inverse are the identity outside the $\varepsilon/2$-ball and injective, hence map the image of $\kappa$ into itself ⟦Chapter4/BumpDiffeo · mapsTo_of_eq_id_outside⟧. So $h = \tau(\mathrm{sh}_c)$ and each $H(\cdot,t) = \tau(\mathrm{sh}_{\sigma(t)c})$ are diffeomorphisms; $H$ is jointly smooth ⟦Chapter4/Homogeneity · contMDiff_transport_shift⟧; $H(\cdot,0) = \mathrm{id}$, $H(\cdot,1) = h$, and $h(y) = \kappa^{-1}(\kappa(y) + c) = z$ because $\varphi(\kappa(y)) = 1$ ⟦Chapter4/Homogeneity · eventually_isotopic⟧.
4. *Globalization.* The relation is reflexive (the identity), transitive ($H_2(H_1(x,t),t)$) and symmetric ($h^{-1}(H(x,1-t))$), each construction keeping every slice a diffeomorphism ⟦Chapter4/Homogeneity · Isotopic.refl⟧ ⟦Chapter4/Homogeneity · Isotopic.trans⟧ ⟦Chapter4/Homogeneity · Isotopic.symm⟧. By step 3 the class of $y$ and its complement are open, and preconnectedness makes the class all of $N$ ⟦Chapter4/Homogeneity · isotopic_of_preconnected⟧.

### V4.5 Diffeomorphisms preserve regular values

> **Lemma.** Let $M$, $N$ be smooth manifolds without boundary, $f : M \to N$ smooth, $h$ a diffeomorphism of $N$ and $y$ a regular value of $f$. Then $h(y)$ is a regular value of $h \circ f$, and $(h \circ f)^{-1}(h(y)) = f^{-1}(y)$. ⟦Chapter4/Degree · IsRegularValue.diffeomorph_comp⟧ ⟦Chapter4/Degree · preimage_diffeomorph_comp⟧

The chain rule on $h^{-1} \circ h = \mathrm{id}$ makes $dh$ injective, hence onto, being an endomorphism of the model space ⟦Chapter4/Degree · surjective_mfderiv_diffeomorph⟧; then $d(h \circ f)_x = dh_{f(x)} \circ df_x$ is a composite of surjections.

### V4.6 The Theorem of §4, first assertion: the parity does not depend on the regular value

> **Theorem (§4, first assertion).** Let $M$ be a compact, Hausdorff, second countable smooth manifold without boundary, $N$ a Hausdorff, preconnected smooth manifold without boundary of the same dimension, and $f : M \to N$ smooth. If $y$ and $z$ are regular values of $f$, then $\#f^{-1}(y) + \#f^{-1}(z)$ is even. ⟦Chapter4/Degree · even_ncard_add_ncard_of_isRegularValue⟧

*Proof, as in the book.* V4.4 gives $h$ and $H$ with $h(y) = z$, and $F(x,t) = H(f(x),t)$ is a smooth homotopy from $f$ to $h \circ f$. The value $z$ is regular for $f$ by hypothesis and for $h \circ f$ by V4.5, with $(h \circ f)^{-1}(z) = f^{-1}(y)$; the Homotopy Lemma at $z$ gives the parity. The slice-wise diffeomorphism clause of V4.4 is not needed here; Chapter 5 uses it (V5.5).

### V4.7 The degree modulo 2

For any map $f : M \to N$,
$$\deg_2 f = \#f^{-1}(y_0) \bmod 2, \qquad y_0 \text{ a regular value of } f \text{ chosen by the axiom of choice},$$
and $\deg_2 f = 0$ if $f$ has no regular value ⟦Chapter4/Degree · degMod2⟧. For smooth $f$ on a second countable $M$, Brown's theorem supplies a regular value whenever $N$ is nonempty, so there the junk value serves only $N = \emptyset$.

> **Theorem.** For $M$, $N$, $f$ as in V4.6 and every regular value $y$ of $f$, $\deg_2 f = \#f^{-1}(y) \bmod 2$. ⟦Chapter4/Degree · degMod2_eq⟧

The first assertion compares $y$ with the chosen $y_0$, and an even sum means equal residues ⟦Chapter4/Degree · natCast_zmod_two_eq_of_even_add⟧.

### V4.8 The Theorem of §4, second assertion: homotopy invariance

> **Theorem (§4, second assertion).** For $M$, $N$ as in V4.6 and $F : M \times \mathbb R \to N$ smooth, $\deg_2 F(\cdot,0) = \deg_2 F(\cdot,1)$. ⟦Chapter4/Degree · degMod2_eq_of_homotopy⟧

*Proof.* If $N$ is nonempty, the two ends have a common regular value: those of $F(\cdot,0)$ form an open set by local constancy ⟦Chapter4/Degree · isOpen_isRegularValue⟧, nonempty because dense by Brown's theorem, and those of $F(\cdot,1)$ are dense, hence meet it ⟦Chapter4/Degree · exists_common_isRegularValue⟧. V4.7 and the Homotopy Lemma at that value conclude. If $N$ is empty, neither end has a regular value and both degrees are $0$ by definition.

### V4.9 Maps of nonzero degree are onto

> **Corollary.** For $M$, $N$, $f$ as in V4.6, if $\deg_2 f \ne 0$ then $f$ is surjective. ⟦Chapter4/Degree · surjective_of_degMod2_ne_zero⟧

A point outside the image is a regular value with empty fibre and would give $\deg_2 f = 0$ ⟦Chapter4/Degree · degMod2_eq_zero_of_notMem_range⟧.

### What the formalization taught us

- **The induction statement must be general.** Sard is proved for all finite-dimensional targets and all Haar measures, because the induction passes to hyperplanes of both domain and target ⟦Chapter3/Basic · SardStatement⟧.
- **The zero target is a genuine special case.** There a Haar measure is a multiple of the point mass; the theorem holds only because $C = \emptyset$, and this is settled before the main argument ⟦Chapter3/Sard · critSet_eq_empty_of_subsingleton⟧ ⟦Chapter3/Sard · sardStatement⟧.
- **Measurability is needed once**, for Fubini in Step 1, and comes from a closed-ball neighbourhood and the closedness of $C$ ⟦Chapter3/Basic · isCompact_critSet_inter⟧ ⟦Chapter3/Step1 · step1_local⟧.
- **Milnor proves more than he uses.** Step 1 needs half of the block-matrix remark, Step 2 only $df = 0$ on $C_k$ ⟦Chapter3/Step1 · step1_local⟧ ⟦Chapter3/Step2 · fderiv_eq_zero_of_mem_vanishSet⟧.
- **The cube count is a dimension estimate**, with Taylor's constant lacking its factorial, balls for cubes, and $k = n$ ⟦Chapter3/Step3 · measure_image_vanishSet_inter_eq_zero⟧ ⟦Chapter3/Step3 · norm_sub_le_of_iteratedFDeriv_eq_zero⟧.
- **Brown's theorem has one hidden hypothesis**, second countability of the source; no Hausdorff property, no dimension relation, one chart of the target ⟦Chapter2/Brown · dense_regularValues⟧.
- **Regularity on the boundary is transversality**: a kernel vector with nonzero time component, which needs $\dim M = \dim N$ ⟦Chapter4/Homotopy · cylinder_transversality⟧.
- **Second countability enters the Homotopy Lemma only through Brown's theorem for the homotopy**, on the noncompact $M \times \mathbb R$ ⟦Chapter4/Homotopy · homotopy_lemma⟧.
- **A flow is replaced by one Euler step**, $u \mapsto u + \sigma(t)\varphi(u)c$, still an isotopy through diffeomorphisms; Hausdorff is used once, to make the image of a compact ball under the inverse chart closed ⟦Chapter4/Homogeneity · eventually_isotopic⟧ ⟦Chapter4/Homogeneity · isClosed_image_symm_of_isCompact⟧.
- **The degree is a chosen parity with a junk value**, so homotopy invariance (V4.8) treats $N = \emptyset$ separately; "connected" is formalized as preconnected ⟦Chapter4/Degree · degMod2⟧ ⟦Chapter4/Degree · degMod2_eq_of_homotopy⟧.


## Part III. Orientation and the Brouwer degree (Milnor §5)

Mathlib has orientations of vector spaces but no oriented manifolds, no sign of a derivative and no degree. This part builds all three and follows Milnor's §5 to the hairy ball theorem. Most proofs are short once the definitions are in place; the exception is Lemma 1, which Milnor proves by walking along an arc of a one-manifold and watching an oriented tangent vector turn from inward to outward. The arcs supplied by the formal Appendix are only homeomorphisms onto intervals, with no derivative, so the walk is redone with local coordinates and monotone functions. That argument fills a third of the chapter and is the centre of this part.

**Map.**
- `Chapter5/OrSign`: the sign of a linear map, the orientation of $E \times \mathbb R$, two determinant formulas.
- `Chapter5/OrSignAlg`: algebraic consequences of the definition of the sign.
- `Chapter5/Orient`: oriented manifolds, the sign of a derivative and its local constancy, the orientation of $M \times \mathbb R$.
- `Chapter5/DegreeAt`: the signed count at a point and its local constancy.
- `Chapter5/ChartFun`: chart functions along a one-dimensional level set; the sign of the pair map $(f, c)$.
- `Chapter5/MonoAt`: the monotonicity sign of a real function.
- `Chapter5/LevelArc`: transitions between chart functions; the boundary function as a chart function.
- `Chapter5/ArcSign`: the invariant along an arc; opposite signs at the two ends.
- `Chapter5/LemmaOne`: Lemma 1 in ambient form.
- `Chapter5/HomotopyInv`: homotopy invariance at a common regular value (Milnor's Lemma 2), the core of Theorem B.
- `Chapter5/Degree`: isotopies preserve orientation, Theorem A (independence of the regular value), the degree and Theorem B.
- `Chapter5/LevelOrient`: the orientation of a level set in a vector space.
- `Chapter5/HairyBall`: the sphere, the antipodal map, the hairy ball theorem and its converse.

*Standing conventions.* $M$ and $N$ are smooth manifolds without boundary, modelled on finite-dimensional real normed spaces $E$ and $F$. Mathlib identifies $T_xM$ with $E$ through the chart $\varphi_x$ at $x$, and $df_x : E \to F$ is the derivative read in the charts at $x$ and $f(x)$ ⟦Chapter5/Orient · mfd⟧. Further hypotheses are stated with each result. From Lemma 1 on (V5.3, V5.4, V5.6, V5.7) the formal statements also require $E$ and $F$ to lie in a common universe, the size condition of Part 0 (§0.10), harmless for Euclidean spaces; the displayed statements record it.

### V5.0 Orientations: signs of linear maps and oriented manifolds

The verified edition asks its reader to confirm one definition of this chapter, that of an oriented manifold. It rests on the sign of a linear map.

#### The sign of a linear map

For Mathlib, an orientation of $E$ with respect to $n$ indices is a class of nonzero alternating $n$-forms on $E$ up to positive multiples, and each class carries a representative $\omega_a$ picked by choice. When $\dim E = n$ every $n$-form is a multiple of any nonzero one, and a nonzero one vanishes on no basis ⟦Chapter5/OrSign · exists_eq_smul_of_finrank⟧ ⟦Chapter5/OrSign · ne_zero_of_basis⟧.

Let $a$ orient $E$ and $b$ orient $F$, and fix by choice a tuple $v = (v_1, \dots, v_n)$ with $\omega_a(v) \neq 0$ ⟦Chapter5/OrSign · orTuple⟧. The **sign** of a linear map $T : E \to F$ is
$$\operatorname{sign}_{a,b}(T) = \operatorname{sgn}\bigl(\omega_b(Tv_1, \dots, Tv_n)\,\omega_a(v_1, \dots, v_n)\bigr) \in \{1, -1, 0\}$$
⟦Chapter5/OrSign · orSign⟧, the sign of a ratio written as a product. The choices disappear at once. If $\omega$, $\eta$ are any representatives of $a$, $b$ and the pullback of $\eta$ by $T$ is $c\,\omega$, then $\operatorname{sign}_{a,b}(T) = \operatorname{sgn} c$, with no hypothesis on dimensions ⟦Chapter5/OrSign · orSign_eq_sgn⟧. When $\dim E = n$ the sign can be computed with any representatives on any tuple where $\omega$ does not vanish ⟦Chapter5/OrSign · orSign_eq_sgn_mul⟧. Every sign in the chapter is computed through these two lemmas.

Assume $\dim E = \dim F = n$. For $S : F \to G$ and an orientation $d$ of $G$ the sign is multiplicative, $\operatorname{sign}_{a,d}(ST) = \operatorname{sign}_{b,d}(S)\operatorname{sign}_{a,b}(T)$; it equals $1$ for the identity, and changes when either orientation is reversed ⟦Chapter5/OrSign · orSign_comp⟧ ⟦Chapter5/OrSign · orSign_id⟧ ⟦Chapter5/OrSign · orSign_neg_right⟧. It is nonzero exactly when $T$ is bijective, since in bases $e$ of $E$ and $e'$ of $F$ the constant $c$ is a nonzero multiple of $\det_{e'}(Te_1, \dots, Te_n)$ ⟦Chapter5/OrSign · orSign_ne_zero_iff⟧. A companion file adds the expected algebra: values $\pm 1$ on bijections, $\operatorname{sign}_{a,b} = \operatorname{sign}_{b,a}$ for bijective endomorphisms, and $\operatorname{sign}_{a,a}(T) = \operatorname{sgn}\det T$ for $n > 0$ ⟦Chapter5/OrSignAlg · orSign_eq_one_or_neg_one⟧ ⟦Chapter5/OrSignAlg · orSign_symm⟧ ⟦Chapter5/OrSignAlg · orSign_self_eq_sgn_det'⟧.

Explicit representatives come from bases: with $\epsilon_e(a) = 1$ if the basis $e$ is positive for $a$ and $-1$ otherwise, $\epsilon_e(a)\det_e$ represents $a$ ⟦Chapter5/OrSign · orEpsB⟧ ⟦Chapter5/OrSign · rayOfNeZero_orEpsB_det⟧. The basis used is usually the **reference basis**, which Mathlib extracts by choice from the bare fact $\dim E = n$. It need not be any standard basis. Among the orientations defined in this part, only that of the sphere depends on which basis was chosen (V5.9).

The orientation $\hat a$ of $E \times \mathbb R$ is represented by $\epsilon_e(a)$ times the determinant of the basis $(e_1, 0), \dots, (e_n, 0), (0, 1)$, $e$ the reference basis. So a positive basis of $E$ followed by $(0, 1)$ is positive ⟦Chapter5/OrSign · orProd⟧. Two determinant formulas are proved for it.

- *Block formula.* If $\dim E = \dim F = n$ and $T(v, t) = (Av + tw,\ ct)$, then $\operatorname{sign}_{\hat a, \hat b}(T) = \operatorname{sign}_{a,b}(A)\,\operatorname{sgn}(c)$, because the matrix of $T$ is block triangular ⟦Chapter5/OrSign · orSign_orProd⟧.
- *Kernel formula.* Let $\dim E = n + 1$, $\dim F = n$, and let $T, T' : E \to F \times \mathbb R$ have the same surjective first component $P$. For every $v \neq 0$ with $Pv = 0$,
$$\operatorname{sign}_{a, \hat b}(T)\,\operatorname{sign}_{a, \hat b}(T') = \operatorname{sgn}\bigl((Tv)_2\,(T'v)_2\bigr).$$
The proof uses a right inverse $R$ of $P$ and the basis $(v, Re'_1, \dots, Re'_n)$ of $E$, $e'$ the reference basis of $F$. Against it and the product basis of $F \times \mathbb R$, either map $S$ has first column $(0, \dots, 0, (Sv)_2)$, and deleting that column and the last row leaves the identity. So its determinant is $(-1)^n (Sv)_2$, and all other factors appear in both signs and cancel ⟦Chapter5/OrSign · orSign_prodReal_mul⟧.

The kernel formula carries Lemma 1; the block formula carries products, Lemma 2 (V5.4) and the isotopy argument of V5.5.

#### Oriented manifolds

**Definition.** An orientation of $M$ assigns to each $x$ an orientation $o_x$ of $E$ such that every $x$ has a neighbourhood whose points $y$ satisfy
$$\operatorname{sign}_{o_y,\, o_x}\bigl(d(\varphi_x)_y\bigr) = 1$$
⟦Chapter5/Orient · Orient⟧. Since $T_yM$ is $E$ read through $\varphi_y$, the map $d(\varphi_x)_y$ is the derivative of the transition $\varphi_x \circ \varphi_y^{-1}$ at $\varphi_y(y)$. So the condition says that near each point, the transitions into the chart at that point carry the orientation at $y$ to that at $x$. (Mathlib's chart at $x$ is a chart of the atlas whose domain contains $x$; it need not send $x$ to $0$.) Equivalently, $\varphi_x$ is orientation preserving near $x$ when its target $E$ is given the constant orientation $o_x$. This is Milnor's definition (p. 26), up to composing each chart with a linear isomorphism from $(E, o_x)$ to $\mathbb R^m$ with its standard orientation. There is no oriented atlas, and the dimension $n$ is a parameter; theorems add $\dim E = n$.

The **sign of $f$ at $x$** is $\operatorname{sign} df_x = \operatorname{sign}_{o_x,\, o'_{f(x)}}(df_x)$ ⟦Chapter5/Orient · signAt⟧. When $\dim E = \dim F = n$ it is nonzero exactly when $df_x$ is bijective, hence $\pm 1$ at regular points ⟦Chapter5/Orient · signAt_ne_zero_iff⟧ ⟦Chapter5/Orient · IsRegularPoint.signAt_ne_zero⟧.

The product $M \times \mathbb R$ is oriented by $(x, t) \mapsto \hat o_x$ ⟦Chapter5/Orient · Orient.prodReal⟧. The formal proof has to check the condition: the chart at $(x, t)$ is $\varphi_x \times \mathrm{id}$, and the block formula reduces the condition to that of $M$. The same formula computes the sign of any map $M \times \mathbb R \to N \times \mathbb R$ whose derivative has the form $(v, t) \mapsto (Av + tw,\ ct)$ ⟦Chapter5/Orient · signAt_prodReal⟧.

### V5.1 Local constancy of the sign

> **Theorem.** Let $\dim E = \dim F = n$, let $M$ and $N$ be oriented, $f : M \to N$ smooth, and $x_0$ a regular point of $f$. Then $\operatorname{sign} df_x = \operatorname{sign} df_{x_0}$ for all $x$ near $x_0$ ⟦Chapter5/Orient · eventually_signAt_eq⟧.

The proof is written for $f$ smooth only on an open $W \ni x_0$, a variant that Lemma 1 needs ⟦Chapter5/Orient · eventually_signAt_eq_of_contMDiffOn⟧.

*The idea.* In the fixed charts at $x_0$ and $f(x_0)$, the sign of $df_x$ is the sign of the derivative of the local representative, measured against the fixed orientations $o_{x_0}$ and $o'_{f(x_0)}$. That is the sign of a determinant, continuous in $x$ and nonzero at $x_0$.

*The proof as formalized.*
1. A family $L(u)$ of linear maps, continuous at $u_0$ with $\operatorname{sign}_{a,b} L(u_0) \neq 0$, has constant sign near $u_0$: in the reference bases $e$, $e'$ of $E$, $F$ the sign is $\operatorname{sgn}\bigl(\epsilon_{e'}(b)\det_{e'}(L(u)e)\,\epsilon_e(a)\bigr)$ ⟦Chapter5/Orient · eventually_orSign_eq_of_continuousAt⟧.
2. Let $g = \varphi_{f(x_0)} \circ f \circ \varphi_{x_0}^{-1}$, smooth on an open $U \subseteq E$. For $x$ near $x_0$ the chain rule gives $d(\varphi_{f(x_0)})_{f(x)} \circ df_x = dg_{\varphi_{x_0}(x)} \circ d(\varphi_{x_0})_x$.
3. Take signs. By the orientation condition of $N$ at $f(x_0)$, applied at $f(x)$, which is near $f(x_0)$, the left side has sign $\operatorname{sign} df_x$. By the condition of $M$ at $x_0$, the right side has sign $\operatorname{sign}_{o_{x_0}, o'_{f(x_0)}}(dg_{\varphi_{x_0}(x)})$. Step 1 applies to $u \mapsto dg_u$, continuous because $g$ is $C^\infty$ on $U$.

*What the book leaves implicit.* This continuity is used without comment on p. 27. The orientation conditions are used only at $x_0$ and $f(x_0)$, which is why the local form of the definition suffices.

### V5.2 The signed count and its local constancy

For $y \in N$ put $\deg(f; y) = \sum_{x \in f^{-1}(y)} \operatorname{sign} df_x$ ⟦Chapter5/DegreeAt · degAt⟧. This is Mathlib's finite sum, which is $0$ by convention when infinitely many terms are nonzero. For a smooth map on a compact manifold, with $\dim E = \dim F$ and $N$ a $T_1$ space, the preimage of a regular value is finite (V1.3) ⟦Chapter1/RegularValue · IsRegularValue.finite_preimage⟧, and outside the image the count is $0$ ⟦Chapter5/DegreeAt · degAt_of_notMem_range⟧.

> **Theorem.** Let $M$ be compact and Hausdorff, $N$ Hausdorff, $\dim E = \dim F = n$, both oriented, $f$ smooth and $y$ a regular value. Then $\deg(f; y') = \deg(f; y)$ for all $y'$ near $y$ ⟦Chapter5/DegreeAt · IsRegularValue.eventually_degAt_eq⟧.

The points $y'$ need not be regular. Chapter 1 proves a weighted form of the local constancy of $\#f^{-1}(y)$ (V1.4), valid for any integer weight that is locally constant near each point of $f^{-1}(y)$ ⟦Chapter1/RegularValue · IsRegularValue.eventually_finsum_preimage_eq⟧, and V5.1 says that the sign is such a weight.

### V5.3 Lemma 1 in ambient form

> **Theorem.** Let $\dim E = n + 1$ and $\dim F = n$, with $E$ and $F$ in a common universe, let $M$ and $N$ be Hausdorff and oriented, $f : M \to N$ smooth with a regular value $y$, and $g : M \to \mathbb R$ smooth. Suppose that at every $x$ with $f(x) = y$ and $g(x) = 0$ some $v$ has $df_x v = 0$ and $dg_x v \neq 0$, and that $f^{-1}(y) \cap \{g \ge 0\}$ is compact. Then $f^{-1}(y) \cap \{g = 0\}$ is finite and
> $$\sum_{x \in f^{-1}(y) \cap \{g = 0\}} \operatorname{sign} d(f, g)_x = 0,$$
> the signs of the pair map $(f, g) : M \to N \times \mathbb R$ being taken for the orientation of $M$ and the product orientation of $N \times \mathbb R$ ⟦Chapter5/LemmaOne · lemmaOne_ambient'⟧ ⟦Chapter5/LemmaOne · lemmaOne_ambient⟧.

Finiteness is stated because for an infinite set the finite-sum convention would make the identity trivially true. The number $0$ need not be a regular value of $g$. The transversality condition stands in for Milnor's hypothesis that $y$ is a regular value of $f|\partial X$, in the form that Lemma 4 of §2 (V2.6) uses. Only the Hausdorff property of $M$ is used, through the level set, which the Appendix needs to be Hausdorff; that of $N$ is a hypothesis of the statement which the proof never uses.

*Relation to Milnor.* His Lemma 1 concerns an abstract compact $X$ with boundary and asserts $\deg(f|\partial X; y) = 0$ for the boundary orientation. Here $X = \{g \ge 0\}$ sits inside the boundaryless $M$, and the boundary signs are those of the ambient pair map. For $X$ in an oriented vector space, with $0$ a regular value of $g$, Chapter 6 proves $\operatorname{sign} d(f|\partial X)_x = (-1)^{n+1}\operatorname{sign} d(f, g)_x$ for the orientation of V5.8, at every $x \in \partial X$ where $f$ is differentiable ⟦Chapter6/LevelSign · signAt_levelOrient_eq'⟧. Under the hypotheses of the theorem above it deduces Milnor's form, $\deg(f|\partial X; y) = 0$ ⟦Chapter6/LevelSign · degAt_levelOrient_eq_zero⟧.

*The idea.* $A = f^{-1}(y) \cap \{g \ge 0\}$ is a compact one-manifold with boundary $B = f^{-1}(y) \cap \{g = 0\}$. The Appendix pairs the points of $B$ by arcs, and the two ends of an arc have opposite signs. Milnor proves the last claim by orienting the arc and following its positive unit tangent vector, which points inward at one end and outward at the other. The formal arcs have no tangent vector. Local coordinates of the level set replace it, and "points inward" becomes "the coordinate increases".

#### Chart functions

Let $\dim E = n + 1$, $\dim F = n$, $f$ smooth and $y$ a regular value. At $m \in f^{-1}(y)$ the kernel $K_m$ of $df_m$ is a line ⟦Chapter5/ChartFun · exists_ne_zero_of_surjective⟧ ⟦Chapter5/ChartFun · exists_smul_eq_of_ker⟧. A **chart function** at $m$ is a function $c : M \to \mathbb R$, smooth on an open $W \ni m$, with $dc_m \neq 0$ on $K_m \setminus 0$ ⟦Chapter5/ChartFun · ChartFun⟧. The pair map $(f, c) : M \to N \times \mathbb R$ then has surjective derivative at $m$ ⟦Chapter5/ChartFun · isRegularPoint⟧, so $\varepsilon_c(m) = \operatorname{sign} d(f, c)_m$ is $\pm 1$ ⟦Chapter5/ChartFun · sign⟧ ⟦Chapter5/ChartFun · sign_ne_zero⟧. Four facts are proved.

1. *Two chart functions.* For $v \in K_m \setminus 0$, $\ \varepsilon_c(m)\,\varepsilon_{c'}(m) = \operatorname{sgn}\bigl(dc_m(v)\,dc'_m(v)\bigr)$: the kernel formula with $P = df_m$ ⟦Chapter5/ChartFun · sign_mul_sign⟧.
2. *Local constancy.* Near $m$, $\operatorname{sign} d(f, c) = \varepsilon_c(m)$ by V5.1 for the pair map on $W$ ⟦Chapter5/ChartFun · eventually_signAt_eq⟧, and $c$ remains a chart function at nearby points ⟦Chapter5/ChartFun · move⟧ ⟦Chapter5/ChartFun · eventually_move⟧.
3. *Existence.* A coordinate $\lambda \circ \varphi_m$ of the chart at $m$ is a chart function, for a coordinate functional $\lambda$ of the reference basis that does not vanish on $d(\varphi_m)_m(K_m)$ ⟦Chapter5/ChartFun · exists_chartFun⟧.
4. *The boundary function.* At a point of $f^{-1}(y) \cap \{g = 0\}$ the function $g$ is a chart function with $W = M$; this is exactly the transversality hypothesis ⟦Chapter5/LevelArc · gChartFun⟧.

#### The monotonicity sign

Let $s$ be a nontrivial interval containing $t_0$ and $h : \mathbb R \to \mathbb R$. Put $\mu_s(h, t_0) = 1$ if $h$ is strictly increasing on $s \cap (t_0 - \delta, t_0 + \delta)$ for some $\delta > 0$, and $-1$ otherwise ⟦Chapter5/MonoAt · monoAt⟧. A continuous injective function on an interval is strictly monotone, by a lemma of the Appendix ⟦Appendix/OneManifold · strictMonoOn_or_strictAntiOn_of_ordConnected⟧, so for such $h$ the value $-1$ means strictly decreasing ⟦Chapter5/MonoAt · exists_strictAntiOn_of_monoAt_eq_neg_one⟧. The sign is locally constant where $h$ is strictly monotone, and it depends only on $h$ near $t_0$ ⟦Chapter5/MonoAt · monoAt_eq_of_near⟧ ⟦Chapter5/MonoAt · monoAt_congr⟧. Composition with a strictly increasing function preserves it, and composition with a strictly decreasing one reverses it ⟦Chapter5/MonoAt · monoAt_comp_of_strictMonoOn⟧ ⟦Chapter5/MonoAt · monoAt_comp_of_strictAntiOn⟧. Finally, let $h$ be continuous and injective near $t_0$, with its minimum over $s$ at $t_0$. Then $\mu_s(h, t_0) = 1$ if $t_0$ is the left end of $s$, and $-1$ if it is the right end ⟦Chapter5/MonoAt · monoAt_eq_one_of_left_min⟧ ⟦Chapter5/MonoAt · monoAt_eq_neg_one_of_right_min⟧.

#### Transitions between chart functions

Let $S$ be a one-manifold and $\iota : S \to M$ smooth with $f \circ \iota = y$, the image of each $d\iota_a$ being $K_{\iota(a)}$; for $S = f^{-1}(y)$ this is Lemma 2 of §2 (V2.3). Then $v = d\iota_a(1)$ is a nonzero vector of the kernel line ⟦Chapter5/LevelArc · mfd_ι_one_ne_zero⟧ ⟦Chapter5/LevelArc · mfd_f_mfd_ι⟧.

> **Lemma.** Let $c$, $c'$ be chart functions at $\iota(a)$. There are an open $V \ni a$ on which $c \circ \iota$ is injective, a set $D$ (in fact an open interval) and a function $k$, with $c(\iota(z)) \in D$ and $k(c(\iota(z))) = c'(\iota(z))$ for $z \in V$, such that either $k$ is strictly increasing on $D$ and $dc(v)\,dc'(v) > 0$, or $k$ is strictly decreasing on $D$ and $dc(v)\,dc'(v) < 0$ ⟦Chapter5/LevelArc · exists_transition⟧.

Since $d(c \circ \iota)_a(1) = dc(v) \neq 0$, the inverse function theorem (V1.1) makes $c \circ \iota$ a local diffeomorphism $\Phi$ near $a$ ⟦Chapter1/InverseFunction · isLocalDiffeomorphAt_of_isInvertible_mfderiv⟧. The function $k = c' \circ \iota \circ \Phi^{-1}$ has derivative $dc'(v)/dc(v)$ at $c(\iota(a))$. The derivative is continuous, so of one sign on an interval $D$, and the mean value theorem makes $k$ strictly monotone there.

#### The invariant along an arc

An **arc** of $A$, in the sense of the Appendix, is a homeomorphism $\gamma$ from a bounded nontrivial interval $J$ onto an open subset of $A$, under which the points of $B$ correspond to the endpoints of $J$ that lie in $J$ ⟦Appendix/OneManifold · Arc⟧. It is an arc *from* $p$ if $\gamma(0) = p$ and $J \subseteq [0, \infty)$ ⟦Appendix/OneManifold · IsFrom⟧. Nothing about $\gamma$ is smooth.

Write $\beta(x) = \operatorname{sign} d(f, g)_x$ ⟦Chapter5/ArcSign · bdrySign⟧. For $t \in J$ choose a chart function $c_t$ at $\gamma(t)$ ⟦Chapter5/ArcSign · cfAt⟧ and put
$$\varepsilon(t) = \varepsilon_{c_t}(\gamma(t)) \cdot \mu_J(c_t \circ \gamma,\ t)$$
⟦Chapter5/ArcSign · arcEps⟧. Up to a constant sign, $\varepsilon_c$ tells whether $c$ increases in the positive direction of Milnor's orientation of the arc, and $\mu_J$ tells whether $c$ increases with the parameter. The product compares that orientation with the parameter, and $c$ drops out. This takes three steps.

1. *Any chart function will do.* For every chart function $c$ at $\gamma(t)$, $\ \varepsilon_c(\gamma(t))\,\mu_J(c \circ \gamma, t) = \varepsilon(t)$ ⟦Chapter5/ArcSign · sign_mul_monoAt_eq⟧. Near $t$ the function $c \circ \gamma$ is continuous and injective, hence strictly monotone ⟦Chapter5/ArcSign · exists_ball_good⟧, and $c_t \circ \gamma = k \circ (c \circ \gamma)$ for the transition $k$. If $k$ increases, $\mu_J$ is unchanged and $\varepsilon_c = \varepsilon_{c_t}$ by the first fact about chart functions; if $k$ decreases, both factors change sign.
2. *Local constancy.* $\varepsilon$ is constant near each $t_0 \in J$ ⟦Chapter5/ArcSign · eventually_arcEps_eq⟧. Keep $c = c_{t_0}$. For $t$ near $t_0$ it is a chart function at $\gamma(t)$ with the same sign, by the second fact, and $\mu_J(c \circ \gamma, t) = \mu_J(c \circ \gamma, t_0)$ because $c \circ \gamma$ is strictly monotone around $t_0$. Step 1 at $t$ finishes.
3. *The ends.* If the arc from $p$ is closed, $J = [0, T]$, then $q = \gamma(T)$ lies in $B$ and $\beta(p) = -\beta(q)$ ⟦Chapter5/ArcSign · bdrySign_end_eq_neg⟧. Indeed $\varepsilon$ is constant on the connected interval $J$. At both ends use the chart function $g$. Since $g \ge 0$ on $A$ and $g(p) = g(q) = 0$, the function $g \circ \gamma$ has its minimum at both ends of $J$, so $\mu_J(g \circ \gamma, 0) = 1$ and $\mu_J(g \circ \gamma, T) = -1$. Hence $\beta(p) = \varepsilon(0) = \varepsilon(T) = -\beta(q)$.

#### The proof of Lemma 1 as formalized

1. $S = f^{-1}(y)$ is a one-manifold (V2.2) ⟦Chapter2/LevelSet · isSliceSubmanifold_preimage⟧ with tangent line $K_x$ at $x$ (V2.3) ⟦Chapter2/LevelSet · mem_range_mfderiv_val_iff⟧. Inside it, $A = S \cap \{g \ge 0\}$ is a manifold with boundary $B = S \cap \{g = 0\}$ (V2.6), all of whose charts send exactly $B$ to $0$ ⟦Chapter2/WithBoundary · isHalfSliceSubmanifold_levelSet⟧ ⟦Appendix/HalfSpace · IsHalfSliceSubmanifold.boundaryCompatible⟧. It is compact by hypothesis.
2. For $p \in B$ the Appendix supplies a closed arc from $p$, whose image is then the whole component of $p$ ⟦Appendix/OneManifold · exists_closed_arc⟧ ⟦Appendix/OneManifold · IsFrom.source_eq_of_mem⟧. That component meets $B$ in exactly $\{p, q\}$, with $q = \gamma(T) \neq p$ ⟦Appendix/OneManifold · IsFrom.boundary_inter_component⟧. The arc argument, with $\iota$ the inclusion of $S$, gives $\beta(p) = -\beta(q)$.
3. Choosing $q$ for each $p$ defines $\pi : B \to B$. It is an involution: $\pi(\pi(p))$ lies in the component of $p$, hence in $\{p, \pi(p)\}$, and it differs from $\pi(p)$.
4. $B$ is finite: it is closed in the compact $A$, and each arc at a boundary point meets $B$ only there ⟦Appendix/OneManifold · finite_boundary⟧. As $\pi$ permutes $B$, $\sum_B \beta = \sum_B \beta \circ \pi = -\sum_B \beta$, so the sum vanishes, and the inclusion carries it to $M$.

*Where the formal proof departs from Milnor.* No orientation of the arc and no tangent field is constructed, and boundary points are paired by "the other end of my component" rather than by a decomposition into arcs and circles. Both changes come from the Appendix being proved for topological one-manifolds (V.A). The monotonicity sign is the price: two hundred lines of real analysis replace Milnor's one-line observation about the unit tangent field.

### V5.4 Theorem B at a common regular value (Milnor's Lemma 2)

> **Theorem.** Let $M$ be compact, Hausdorff and second countable, $N$ Hausdorff, $\dim E = \dim F = n$ with $E$ and $F$ in a common universe, both oriented, $\Phi : M \times \mathbb R \to N$ smooth, $f_0 = \Phi(\cdot, 0)$, $f_1 = \Phi(\cdot, 1)$, and $y$ a regular value of $f_0$ and of $f_1$. Then $\deg(f_0; y) = \deg(f_1; y)$ ⟦Chapter5/HomotopyInv · degAt_eq_of_homotopy⟧.

In the book this is Lemma 2 of §5, Theorem B at a common regular value, from which Milnor derives both theorems; Theorem B for the degree itself is the second item of V5.7. The letters A and B here are Milnor's (p. 28); the docstrings of the formal source use the opposite lettering. The section comes before Theorem A because the proof of A uses it, in the formal text as in the book.

*The idea.* Apply Lemma 1 to the cylinder $M \times [0, 1] = \{t(1 - t) \ge 0\}$ in $M \times \mathbb R$, whose boundary signs are $\operatorname{sign} df_0$ and $-\operatorname{sign} df_1$. A perturbation of $y$ handles the general case.

*The proof as formalized.*
1. Suppose first that $y$ is also a regular value of $\Phi$ ⟦Chapter5/HomotopyInv · degAt_eq_of_homotopy_of_isRegularValue⟧. Orient $M \times \mathbb R$ by $\hat o$ and take $g(x, t) = t(1 - t)$, with $dg_{(x,t)}(v, s) = (1 - 2t)s$ ⟦Chapter5/HomotopyInv · mfd_cyl⟧. At $(x, c) \in \Phi^{-1}(y)$ with $c \in \{0, 1\}$, V4.2 gives a kernel vector of $d\Phi$ with nonzero $\mathbb R$-component $s$, on which $dg = \pm s \neq 0$ ⟦Chapter4/Homotopy · cylinder_transversality⟧. The set $\Phi^{-1}(y) \cap (M \times [0, 1])$ is compact, so Lemma 1 applies.
2. The boundary set is the disjoint union of $f_0^{-1}(y) \times \{0\}$ and $f_1^{-1}(y) \times \{1\}$, both finite (V1.3).
3. Write $f_c = \Phi(\cdot, c)$. At $(x, c)$ the derivative of $(\Phi, g)$ is $(v, s) \mapsto \bigl(d(f_c)_x v + s\,w,\ (1 - 2c)s\bigr)$ with $w = d\Phi_{(x,c)}(0, 1)$ ⟦Chapter5/HomotopyInv · mfd_prod_apply⟧. The block formula gives the sign $\operatorname{sign} d(f_c)_x \cdot \operatorname{sgn}(1 - 2c)$, and Lemma 1 reads $\deg(f_0; y) - \deg(f_1; y) = 0$.
4. In general, V1.4 (strengthened) and V5.2 give a neighbourhood $U$ of $y$ consisting of regular values of $f_0$ and $f_1$ with the same signed counts ⟦Chapter1/RegularValue · IsRegularValue.eventually_isRegularValue_and_ncard⟧ ⟦Chapter5/DegreeAt · IsRegularValue.eventually_degAt_eq⟧. Brown's theorem (V3.3) gives a regular value of $\Phi$ in $U$ ⟦Chapter2/Brown · dense_regularValues⟧, where steps 1–3 apply.

One function presents both ends of the cylinder, so the two-function Lemma 4 for the cylinder (V4.1), which served the degree modulo 2, is not needed. Second countability enters only in step 4, through Brown's theorem, which is also stated for model spaces in a common universe.

### V5.5 Isotopies preserve orientation

*What the book leaves implicit.* Milnor observes that a diffeomorphism isotopic to the identity preserves orientation. The formal proof needs every stage of the isotopy to be a diffeomorphism, and the Homogeneity Lemma (V4.4) was strengthened to supply it. Points $y$, $z$ are *isotopic* if there are a diffeomorphism $h$ with $h(y) = z$ and a smooth $H : N \times \mathbb R \to N$ with $H(\cdot, 0) = \mathrm{id}$, $H(\cdot, 1) = h$ and every $H(\cdot, t)$ a diffeomorphism ⟦Chapter4/Homogeneity · Isotopic⟧.

> **Theorem.** Let $\dim F = n$, $N$ Hausdorff and oriented, and $y$, $z$ isotopic. Then there are a diffeomorphism $h$ with $h(y) = z$ and a smooth $H : N \times \mathbb R \to N$ with $H(\cdot, 0) = \mathrm{id}$ and $H(\cdot, 1) = h$ such that $\operatorname{sign} dh_x = 1$ for all $x \in N$ ⟦Chapter5/Degree · exists_isotopy_signAt_eq_one⟧.

The proof keeps the $h$ and $H$ of the isotopy and does not use the Hausdorff property. By the block formula with $c = 1$, the sign at $(w, t)$ of $G(w, t) = (H(w, t), t)$, a self-map of $N \times \mathbb R$, is that of $H(\cdot, t)$ at $w$ ⟦Chapter5/Orient · signAt_prodReal⟧. It is nonzero because $H(\cdot, t)$ is a diffeomorphism ⟦Chapter4/Degree · surjective_mfderiv_diffeomorph⟧. So V5.1 applies to $G$ at every point, and $t \mapsto \operatorname{sign} d(H(\cdot, t))_x$ is locally constant on $\mathbb R$, hence constant, equal to its value $1$ at the identity ⟦Chapter5/Degree · signAt_id⟧.

### V5.6 Theorem A: the signed count does not depend on the regular value

For smooth $f : M \to N$ and $h : N \to P$, with $P$ an oriented manifold modelled like $N$, $\dim E = \dim F = n$ and $E$, $F$ in a common universe, the chain rule for signs holds: $\operatorname{sign} d(h \circ f)_x = \operatorname{sign} dh_{f(x)} \cdot \operatorname{sign} df_x$ ⟦Chapter5/Degree · signAt_comp⟧.

> **Theorem.** Let $M$ be compact, Hausdorff and second countable, $N$ Hausdorff and preconnected, $\dim E = \dim F = n$ with $E$ and $F$ in a common universe, both oriented, and $f : M \to N$ smooth. For any two regular values $y$, $z$ of $f$, $\ \deg(f; y) = \deg(f; z)$ ⟦Chapter5/Degree · degAt_eq_of_isRegularValue⟧.

*The proof as formalized* is Milnor's.
1. By V4.4 and V5.5 there are $h$ and $H$ with $h(y) = z$ and $\operatorname{sign} dh = 1$ ⟦Chapter4/Homogeneity · isotopic_of_preconnected⟧.
2. $(h \circ f)^{-1}(z) = f^{-1}(y)$ ⟦Chapter4/Degree · preimage_diffeomorph_comp⟧, and the chain rule makes the signs agree, so $\deg(h \circ f; z) = \deg(f; y)$.
3. $(x, t) \mapsto H(f(x), t)$ is a smooth homotopy from $f$ to $h \circ f$. The point $z$ is a regular value of $f$ by hypothesis and of $h \circ f$ by V4.5 ⟦Chapter4/Degree · IsRegularValue.diffeomorph_comp⟧, so Lemma 2 (V5.4) gives $\deg(f; z) = \deg(h \circ f; z)$.

"Preconnected" admits the empty manifold, harmlessly.

### V5.7 The Brouwer degree

The **degree** of $f$ is $\deg(f; y_0)$ for a regular value $y_0$ picked by choice, and $0$ if there is none ⟦Chapter5/Degree · deg⟧. It is a number for every map; the theorems say when it is Milnor's. Under the hypotheses of V5.6:

- $\deg f = \deg(f; y)$ for every regular value $y$, the final form of Theorem A ⟦Chapter5/Degree · deg_eq⟧;
- smoothly homotopic maps have the same degree, Theorem B as Milnor states it ⟦Chapter5/Degree · deg_eq_of_homotopy⟧: for $N \neq \emptyset$ the two ends have a common regular value, by Brown's theorem and the openness of regular values (V1.4) ⟦Chapter4/Degree · exists_common_isRegularValue⟧, where V5.4 applies, and for $N = \emptyset$ both degrees are $0$ by definition;
- a map of nonzero degree is surjective, since a point outside the image is a regular value with empty preimage ⟦Chapter5/Degree · deg_eq_zero_of_notMem_range⟧ ⟦Chapter5/Degree · surjective_of_deg_ne_zero⟧.

For $N$ compact, Hausdorff, second countable, preconnected, nonempty and oriented, with $\dim F = n$, the identity has degree $1$ ⟦Chapter5/Degree · deg_id⟧.

### V5.8 The induced orientation of a level set

Let $E$ have dimension $n + 1$ and orientation $a_0$, let $\dim Z = n$, and let $g : E \to \mathbb R$ be smooth with $0$ a regular value. By V2.2, $S = g^{-1}(0)$ is a manifold modelled on $Z$; let $d\iota_q : Z \to E$ be the derivative of its inclusion at $q$.

- The **contraction** of an $(n+1)$-form $\omega$ by $\nu \in E$ along a linear $T : Z \to E$ is the $n$-form $(z_1, \dots, z_n) \mapsto \omega(\nu, Tz_1, \dots, Tz_n)$ ⟦Chapter5/LevelOrient · contractForm⟧. If $T$ is injective with image in a hyperplane $\ker\lambda$ and $\lambda(\nu) \neq 0$, then $(\nu, Tu_1, \dots, Tu_n)$ is a basis of $E$ for every basis $u$ of $Z$, so the contraction of $\omega \neq 0$ vanishes on no basis ⟦Chapter5/LevelOrient · contractForm_basis_ne_zero⟧. Its class does not depend on the representative of $a_0$ ⟦Chapter5/LevelOrient · contractOr⟧ ⟦Chapter5/LevelOrient · rayOfNeZero_contractForm⟧. A vanishing contraction would give a default value, the orientation of the reference basis; this never happens on a level set.
- The **outward vector** is $\nu(x) = -\sum_i dg_x(e_i)\,e_i$ for the reference basis $e$ of $E$ ⟦Chapter5/LevelOrient · outward⟧. It is continuous in $x$, and $dg_x(\nu(x)) = -\sum_i dg_x(e_i)^2 < 0$ when $dg_x \neq 0$ ⟦Chapter5/LevelOrient · continuous_outward⟧ ⟦Chapter5/LevelOrient · fderiv_outward_neg⟧.

> **Theorem.** The contractions of $a_0$ by $\nu(q)$ along $d\iota_q$, for $q \in S$, form an orientation of $S$ in the sense of V5.0 ⟦Chapter5/LevelOrient · levelOrient⟧ ⟦Chapter5/LevelOrient · levelOrient_cont⟧.

A basis $z$ is positive at $q$ exactly when $(\nu(q), d\iota_q z_1, \dots, d\iota_q z_n)$ is positive for $a_0$. As $\nu$ points out of $X = \{g \ge 0\}$, this is Milnor's boundary orientation of $\partial X$, outward normal first. Milnor allows any outward vector, while the formal definition fixes one. Any $w$ with $dg_q(w) < 0$ gives the same orientation, since $w$ is a positive multiple of $\nu(q)$ plus a tangent vector, which does not change the contraction; that lemma is proved in Chapter 6, where it is needed ⟦Chapter6/SignLemmas · contractForm_eq_smul⟧.

*The idea.* Near $q_0$, compare every orientation with one fixed $n$-form on $Z$, through a chart of $S$.

*The proof of continuity as formalized.* Fix $q_0$, the chart $\psi_0$ of $S$ at $q_0$, and $\psi = \iota \circ \psi_0^{-1}$.
1. The chain rule gives $d\iota_q = d\psi_{\psi_0(q)} \circ D_q$, with $D_q = d(\psi_0)_q$ invertible and $D_{q_0} = \mathrm{id}$ ⟦Chapter5/LevelOrient · mfd_extChartAt_self⟧.
2. Let $\Lambda(q)$ be the contraction of $\omega = \epsilon_e(a_0)\det_e$ by $\nu(q)$ along $d\psi_{\psi_0(q)}$, an $n$-form on the fixed space $Z$. On the reference basis $u$ of $Z$, $\Lambda(q)(u)$ is a determinant whose columns are continuous in $q$.
3. Top forms on $Z$ are proportional, so $\Lambda(q) = \kappa(q)\Lambda(q_0)$ with $\kappa(q) = \Lambda(q)(u)/\Lambda(q_0)(u)$. This is continuous and equal to $1$ at $q_0$, hence positive nearby.
4. The orientations at $q$ and $q_0$ are represented by $\Lambda(q) \circ D_q$ and $\Lambda(q_0)$. Evaluating the sign of $D_q$ on $D_q^{-1}u$ gives $\operatorname{sgn}\bigl(\kappa(q)\Lambda(q_0)(u)^2\bigr) = 1$.

This covers level sets in a vector space only; Chapter 6 repeats the construction inside an oriented manifold (V6.1).

### V5.9 The sphere and the antipodal map

The sphere $S^n$ is the level set $g^{-1}(0)$ of $g(x) = \langle x, x\rangle - 1$ on Euclidean $\mathbb R^{n+1}$, where $dg_x(v) = 2\langle x, v\rangle$ and $0$ is a regular value ⟦Chapter5/HairyBall · fderiv_sphG⟧ ⟦Chapter5/HairyBall · isRegularValue_sphG⟧. It is a compact manifold modelled on $\mathbb R^n$ (V2.2), preconnected for $n \ge 1$ ⟦Chapter5/HairyBall · sphS⟧ ⟦Chapter5/HairyBall · preconnectedSpace⟧.

**How the orientation of $S^n$ is chosen.** It is the level-set orientation of V5.8 for the orientation of $\mathbb R^{n+1}$ given by the reference basis $e$ ⟦Chapter5/HairyBall · sphOr⟧. It does not come from Milnor's convention for the sphere. Plainly:
- The reference basis is produced by the axiom of choice, as an unspecified basis of a space of dimension $n + 1$. It need not be the standard basis, and whether it is positive for the standard orientation is never decided.
- The outward vector $\nu(q) = -2\sum_i \langle q, e_i\rangle e_i$ has $\langle q, \nu(q)\rangle < 0$: it points into the ball, and $\{g \ge 0\}$ is the exterior of the ball. So even for the standard ambient orientation this would be the opposite of Milnor's orientation of $S^n = \partial D^{n+1}$.

The orientation is therefore one of the two, and the formalization does not know which. Nothing in this part depends on it: every statement here uses it on both source and target, and reversing both leaves every sign unchanged ⟦Chapter5/OrSign · orSign_neg_left⟧ ⟦Chapter5/OrSign · orSign_neg_right⟧.

The antipodal map $\alpha(q) = -q$ is smooth by corestriction (V2.8) ⟦Chapter5/HairyBall · contMDiff_antip⟧.

> **Theorem.** With this orientation on both sides: for every $n$ and $q \in S^n$, $\ \operatorname{sign} d\alpha_q = (-1)^{n+1}$; for $n \ge 1$, $\ \deg \alpha = (-1)^{n+1}$ ⟦Chapter5/HairyBall · signAt_antip⟧ ⟦Chapter5/HairyBall · deg_antip⟧.

*Where the formal proof departs from Milnor.* Milnor composes $n + 1$ reflections of degree $-1$. The formal proof reads the sign off the contracted form, using $\nu(-x) = -\nu(x)$ and $d\iota_{-q} \circ d\alpha_q = -d\iota_q$, which follows from $\iota \circ \alpha = -\iota$ ⟦Chapter5/HairyBall · outward_neg⟧ ⟦Chapter5/HairyBall · mfd_val_comp_antip⟧. The form representing the orientation at $-q$, pulled back by $d\alpha_q$ and evaluated on the reference basis $u$ of $\mathbb R^n$, is
$$\omega\bigl(-\nu(q), -d\iota_q u_1, \dots, -d\iota_q u_n\bigr) = (-1)^{n+1}\,\omega\bigl(\nu(q), d\iota_q u_1, \dots, d\iota_q u_n\bigr),$$
so the sign is $(-1)^{n+1}$ times the sign of a square. Every point is then a regular value ⟦Chapter5/HairyBall · isRegularValue_antip⟧, the preimage of $y$ is $\{-y\}$, and V5.7 gives the degree.

### V5.10 The hairy ball theorem

> **Theorem.** Let $n$ be even and positive, and let $v : S^n \to \mathbb R^{n+1}$ be smooth with $\langle q, v(q)\rangle = 0$ for all $q$. Then $v(q) = 0$ for some $q$ ⟦Chapter5/HairyBall · hairy_ball⟧.

*The proof as formalized* is Milnor's. Suppose that $v$ has no zero.
1. $w = v/|v|$ is a smooth tangent field of unit vectors, the norm being smooth away from $0$.
2. $F(q, t) = \cos(\pi t)\,q + \sin(\pi t)\,w(q)$ has $|F|^2 = \cos^2(\pi t) + \sin^2(\pi t) = 1$ because $\langle q, w(q)\rangle = 0$. It is smooth into $\mathbb R^{n+1}$, hence into $S^n$ ⟦Chapter2/Corestrict · contMDiff_codRestrict⟧, with $F(\cdot, 0) = \mathrm{id}$ and $F(\cdot, 1) = \alpha$.
3. By V5.7 and V5.9, $1 = \deg \mathrm{id} = \deg \alpha = (-1)^{n+1} = -1$.

*The converse* is proved too. For $n$ odd, write $n + 1 = 2(m + 1)$ and $x = (a, b)$ with $a$ the first and $b$ the last $m + 1$ coordinates. Then $v(a, b) = (b, -a)$ is smooth, tangent because $\langle x, v(x)\rangle = \sum_j a_j b_j - \sum_j b_j a_j = 0$, and of norm $1$ ⟦Chapter5/HairyBall · exists_nonvanishing_field⟧. It pairs the two halves of the coordinates, not adjacent coordinates.

### What the formalization taught us

- **Orientation through chart transitions.** Near each point the transitions into the chart at that point must preserve the chosen orientations; this is the definition a reader must confirm ⟦Chapter5/Orient · Orient⟧.
- **Hidden hypotheses.** $M$ and $N$ Hausdorff for the local constancy of the signed count ⟦Chapter5/DegreeAt · IsRegularValue.eventually_degAt_eq⟧; $M$ Hausdorff in Lemma 1, for the Appendix ⟦Chapter5/LemmaOne · lemmaOne_ambient'⟧; $M$ second countable in Theorems A and B, for Brown's theorem ⟦Chapter5/HomotopyInv · degAt_eq_of_homotopy⟧; from Lemma 1 on, $E$ and $F$ in a common universe, a formality. The Hausdorff property of $N$ is assumed in Lemma 1 but not used there.
- **Lemma 1 is ambient.** Its boundary signs are those of $(f, g)$, which differ from Milnor's boundary-orientation signs by $(-1)^{n+1}$ ⟦Chapter6/LevelSign · signAt_levelOrient_eq'⟧.
- **The arc argument is a third of the chapter.** Topological arcs force Milnor's tangent field to be replaced by the product of the sign of $(f, c)$ and the monotonicity sign of $c$, shown to be independent of $c$, locally constant, and opposite at the two ends ⟦Chapter5/ArcSign · sign_mul_monoAt_eq⟧ ⟦Chapter5/ArcSign · bdrySign_end_eq_neg⟧.
- **Isotopies must be isotopies.** Orientation preservation needs every stage to be a diffeomorphism, which forced a strengthening of the Homogeneity Lemma ⟦Chapter5/Degree · exists_isotopy_signAt_eq_one⟧.
- **One cylinder function,** $t(1 - t)$, presents both ends in Lemma 2, the core of Theorem B ⟦Chapter5/HomotopyInv · degAt_eq_of_homotopy_of_isRegularValue⟧.
- **The degree is total,** $0$ when there is no regular value ⟦Chapter5/Degree · deg⟧.
- **The sphere's orientation is unknown and irrelevant.** It comes from a basis chosen by the axiom of choice and an outward vector pointing into the ball, and it is used on both sides of every statement of this part ⟦Chapter5/HairyBall · sphOr⟧.
- **Direct computations:** the antipodal sign without reflections, and for odd $n$ a field pairing the two halves of the coordinates ⟦Chapter5/HairyBall · signAt_antip⟧ ⟦Chapter5/HairyBall · exists_nonvanishing_field⟧.


## Part IV. Vector fields and the Poincaré–Hopf theorem (Milnor §6)

This part covers Milnor's §6: the index of an isolated zero, its invariance under diffeomorphisms, Hopf's lemma for compact regions of $\mathbb R^{n+1}$, and the Poincaré–Hopf theorem for a compact submanifold $N \subseteq \mathbb R^{K+1}$. The formal proof keeps Milnor's architecture: every index computation reduces to Lemma 1 of §5 (a map that extends over a compact region has degree zero on its boundary) and to the homotopy invariance of the degree. It departs from the book in three places. Lemma 1 of §5 is extended, in boundary form, to level sets in manifolds and to maps smooth only on an open set, because $v/|v|$ is smooth only where $v \ne 0$. Milnor's Lemma 2 (an orientation-preserving diffeomorphism of $\mathbb R^m$ is smoothly isotopic to the identity, through its derivative and then through $GL^+$) is replaced by a sign computation built on one new lemma about maps between level sets (V6.2). And the $\varepsilon$-neighbourhood theorem, which Milnor quotes from §8, is proved here with the inverse function theorem. Because the index of a tangent field on $N$ is *defined* through its extension to a tubular neighbourhood, the formal Poincaré–Hopf theorem does not use the invariance lemma.

Six sections at the end of the part, V6.10 to V6.15, close the remarks of §6 that the first pass left aside: Lemma 4, the index at a non-degenerate zero; Hadamard's lemma; Lemma 2 itself, which is thus proved although the development has replaced it; Lemma 5 and the derivative of the retraction; Milnor's own chart definition of the index, with its agreement with the definition used here at a non-degenerate zero; and the Euler number $1 + (-1)^n$ of $S^n$. One sentence of the section still cannot be written down, and V6.15 says which.

**Map.** The files, in logical order (all in `Chapter6/`):

- `LevelSign`: level sets in a vector space; signs on the level set versus signs of the pair map $(f, G)$.
- `Index`: the sphere map and the index; independence of the radius; homotopy invariance.
- `Opens`: orientations and signs restricted to an open subset.
- `SignLemmas`: the chain rule for signs; tangential changes of the outward vector do not matter.
- `LevelOrientM`: the level-set orientation in an oriented manifold, and its continuity.
- `LevelSignM`: level-set signs versus pair-map signs, in a manifold.
- `RegularOpen`: openness of regular values for compact domains; common regular values.
- `LevelMap`: the sign of a map between level sets (V6.2); degrees and bijections.
- `LevelZero`: opposite orientations, the product rule, transversality, Lemma 1 of §5 on an open set.
- `Region`: the region lemma (V6.3).
- `Extend`: extension of a locally smooth field by a cut-off.
- `Compose`: degrees under composition with bijections of constant sign.
- `Hopf`: Hopf's lemma (V6.4).
- `Tubular1`: local parametrizations of a submanifold of $\mathbb R^k$.
- `Tubular2`: the nearest-point equation and the inverse function theorem.
- `Tubular3`: the nearest-point retraction (V6.6).
- `Tubular4`: the region $N_{\varepsilon/2}$ and the extended field (V6.7).
- `PoincareHopf`: germs, the index on $N$ (V6.8), the theorem (V6.9).
- `DetSign`: constancy of $\operatorname{sgn}\det df$ on a ball.
- `Radial`: the matrix determinant lemma; the sign of $u \mapsto Au/|Au|$.
- `Invariance1`: region functions, sphere parametrizations, transfer of regular values.
- `Invariance`: invariance of the index under diffeomorphisms (V6.5).
- `Nondegenerate`: the index at a non-degenerate zero, Milnor's Lemma 4 (V6.10).
- `Hadamard`: smoothness of a parametric integral, and Hadamard's lemma (V6.11).
- `ChartIndex`: the derivative of the retraction, Lemma 5, the chart index and the agreement (V6.13, V6.14).
- `EulerSphere`: the Euler number of $S^n$ (V6.15).
- `Chapter7/Isotopy`: Lemma 2 of §6 (V6.12), which sits in Chapter 7 because its last step is the $GL^+$ path proved there.

### Conventions: spheres, signs and degrees

Except in V6.1 and V6.2, where $E$ is any real normed space of dimension $n + 1$, $E = \mathbb R^{n+1}$ with its Euclidean norm; $S^n = \{x : |x|^2 = 1\}$ is a compact submanifold, connected when $n \ge 1$ ⟦Chapter5/HairyBall · Sph⟧ ⟦Chapter5/HairyBall · preconnectedSpace⟧. For oriented manifolds of equal dimension, $\operatorname{sign}_x f$ is $\pm 1$ at a regular point and $0$ at a critical one; $\deg(f; y)$ sums the signs over $f^{-1}(y)$; and $\deg f$ is $\deg(f; y)$ at a regular value $y$ chosen by the axiom of choice, or $0$ if there is none ⟦Chapter5/Orient · signAt⟧ ⟦Chapter5/DegreeAt · degAt⟧ ⟦Chapter5/Degree · deg⟧. For a compact, Hausdorff, second countable domain and a preconnected Hausdorff target, $\deg f = \deg(f; y)$ at every regular value, and smoothly homotopic maps have equal degrees ⟦Chapter5/Degree · deg_eq⟧ ⟦Chapter5/Degree · deg_eq_of_homotopy⟧.

The reference orientation $a_0$ of $E$ is that of a basis chosen by the library, not provably the standard one; $o_E$ is the constant orientation it defines on the manifold $E$ ⟦Chapter6/LevelSign · Orient.const⟧. When $0$ is a regular value of $g$, the level-set orientation of $g^{-1}(0)$ puts first an outward vector $\nu_q$ with $dg_q(\nu_q) < 0$: it is the boundary orientation of $\{g \ge 0\}$. The sphere carries $o_{S^n}$, the level-set orientation of $|x|^2 - 1$ for $a_0$ ⟦Chapter5/HairyBall · sphOr⟧. Its outward vector $\nu_x = -2\sum_i \langle x, e_i\rangle e_i$, built from the reference basis $(e_i)$, satisfies $\langle x, \nu_x\rangle < 0$ and so points into the ball: $o_{S^n}$ is the boundary orientation of the *complement* of the ball, the opposite of Milnor's convention for the same ambient orientation. Every degree below is taken between two orientations of the same kind, so the numbers are Milnor's. Replacing $a_0$ by $-a_0$ reverses both orientations in each degree, so the library's choice is immaterial; no proof needs this remark.

Write $\hat y = y/|y|$. The formal normalization sends $0$ to a fixed base point, so $\hat v = v/|v|$ is defined everywhere and smooth where $v \ne 0$ ⟦Chapter6/Region · nv0⟧ ⟦Chapter6/Region · contMDiff_nv0_comp⟧. Homotopies are reparametrized by Mathlib's smooth transition function $\tau$ ($0$ on $(-\infty, 0]$, $1$ on $[1, \infty)$), because the formal homotopy invariance asks for a smooth map on $M \times \mathbb R$.

### V6.0 The index of an isolated zero

For a smooth $v : \mathbb R^{n+1} \to \mathbb R^{n+1}$, a point $z$ and a real $\varepsilon$, the *sphere map* is
$$s_{v,z,\varepsilon} : S^n \to S^n, \qquad u \mapsto \frac{v(z + \varepsilon u)}{|v(z + \varepsilon u)|},$$
with the value $u$ where $v(z + \varepsilon u) = 0$, and $\operatorname{ind}_\varepsilon(v; z) := \deg s_{v,z,\varepsilon}$ for $o_{S^n}$ on both sides ⟦Chapter6/Index · sphMap⟧ ⟦Chapter6/Index · indexAt⟧. The point $z$ is an *isolated zero of radius $r$* if $v(z) = 0$ and $v(x) \ne 0$ whenever $0 < |x - z| \le r$ ⟦Chapter6/Index · IsolatedZero⟧. The *index* $\operatorname{ind}(v; z)$ is $\operatorname{ind}_r(v; z)$ for some $r > 0$ of this kind, chosen by the axiom of choice, and $0$ if no such $r$ exists ⟦Chapter6/Index · index⟧.

> **Theorem (V6.0).** Let $n \ge 1$ and let $v : \mathbb R^{n+1} \to \mathbb R^{n+1}$ be smooth.
>
> (a) If $z$ is an isolated zero of $v$ of radius $r > 0$ and $0 < \varepsilon \le r$, then $\operatorname{ind}(v; z) = \operatorname{ind}_\varepsilon(v; z)$.
>
> (b) If $V : \mathbb R^{n+1} \times \mathbb R \to \mathbb R^{n+1}$ is smooth and $V(z + \varepsilon u, t) \ne 0$ for all $u \in S^n$ and $t \in \mathbb R$, then $\operatorname{ind}_\varepsilon(V(\cdot, 0); z) = \operatorname{ind}_\varepsilon(V(\cdot, 1); z)$.
>
> (c) If $w, w'$ are smooth, agree on a neighbourhood of $z$, and $z$ is an isolated zero of $w$ of some radius $r > 0$, then $\operatorname{ind}(w; z) = \operatorname{ind}(w'; z)$.

**The idea.** All three statements are homotopy invariance of the degree of maps $S^n \to S^n$, available because $S^n$ is compact and, for $n \ge 1$, connected.

**The proof as formalized.** If $v$ has no zero on the spheres of radius $\rho(t)$ for a smooth family of radii $\rho$, then $(u, t) \mapsto s_{v,z,\rho(t)}(u)$ is a smooth map $S^n \times \mathbb R \to S^n$: the formula is smooth into $\mathbb R^{n+1}$, lands in the sphere, and the slice structure of $S^n$ makes the corestriction smooth ⟦Chapter6/Index · contMDiff_sphMap_family⟧. For radii $\varepsilon_1, \varepsilon_2 \in (0, r]$, the family $\rho(t) = \varepsilon_1 + \tau(t)(\varepsilon_2 - \varepsilon_1)$ stays between $\min(\varepsilon_1, \varepsilon_2)$ and $r$, so the degrees at $t = 0$ and $t = 1$ agree ⟦Chapter6/Index · indexAt_eq_of_radii⟧. Comparing both the chosen radius and $\varepsilon$ with the smaller of the chosen radius and $r$ gives (a) ⟦Chapter6/Index · index_eq⟧. For (b), $(u, t) \mapsto \widehat{V}(z + \varepsilon u, t)$ is the homotopy; this is Milnor's remark on p. 33 ⟦Chapter6/Index · indexAt_eq_of_homotopy⟧. For (c), if $w = w'$ on the $\delta$-ball, then $z$ is an isolated zero of $w'$ of radius $\varepsilon = \min(r, \delta/2)$, the two sphere maps of radius $\varepsilon$ coincide, and (a) applies to both fields ⟦Chapter6/PoincareHopf · index_eq_of_eventuallyEq⟧.

*Where the formal statement departs from Milnor.* Milnor's field lives on an open set; the formal field is defined on all of $\mathbb R^{n+1}$. By (c) nothing is lost: a map $v$ smooth on an open $W$ agrees near any compact $K \subseteq W$ with the global smooth map equal to $\chi v$ on $W$ and to $0$ elsewhere, where the smooth Urysohn function $\chi$ is $1$ near $K$ and $0$ near the complement of $W$ ⟦Chapter6/Extend · exists_extension⟧. The tubular field of V6.7 becomes global this way.

### V6.1 Level-set orientations in a manifold, and Lemma 1 of §5 in boundary form

The region lemma applies Lemma 1 of §5 to $\hat v$ on the open set $\{v \ne 0\}$, a manifold with charts in $E$ but not a vector space, so the level-set orientation of Chapter 5 had to be rebuilt for manifolds.

**Setting.** $M$ is a smooth manifold with charts in $E$, $\dim E = n + 1$, oriented by $o_M$; $g : M \to \mathbb R$ is smooth with $0$ a regular value; $S = g^{-1}(0)$ is a slice submanifold modelled on a space $Z$ of dimension $n$, with inclusion $\iota$. For $q \in S$ let
$$\nu_q = -\sum_i dg_q(e_i)\, e_i, \qquad dg_q(\nu_q) = -\sum_i dg_q(e_i)^2 < 0,$$
where $dg_q$ is read in the chart of $M$ at $q$ and $(e_i)$ is the reference basis of $E$ ⟦Chapter6/LevelOrientM · outwardM⟧. The orientation of $S$ at $q$ is the class of the $n$-form
$$(\zeta_1, \dots, \zeta_n) \mapsto \omega(\nu_q, d\iota_q \zeta_1, \dots, d\iota_q \zeta_n),$$
$\omega$ a representative of $o_M(q)$ ⟦Chapter5/LevelOrient · contractOr⟧ ⟦Chapter6/LevelOrientM · levelOrientM⟧. The form is nonzero: $d\iota_q$ is injective with image $\ker dg_q$ and $dg_q(\nu_q) \ne 0$, so $(\nu_q, d\iota_q\zeta)$ is a basis of $E$ whenever $\zeta$ is a basis of $Z$ ⟦Chapter6/LevelOrientM · levelOrientM_rep_ne_zero⟧. For $M = E$ with $o_E$ this is the orientation of Chapter 5; in particular $o_{S^n}$ is an instance ⟦Chapter6/LevelZero · levelOrient_eq_levelOrientM⟧.

> **Theorem (V6.1, the orientation).** These orientations vary continuously: for $q$ near $q_0$ in $S$, the derivative at $q$ of the chart of $S$ at $q_0$ carries the orientation at $q$ to the orientation at $q_0$. ⟦Chapter6/LevelOrientM · levelOrientM_cont⟧

**The idea.** Read in fixed charts at $q_0$, the orientation at a nearby $q$ is a positive multiple of a form that depends continuously on $q$ and has the right sign at $q_0$.

**The proof as formalized.**
1. Fix the charts $\varphi$ of $M$ and $c_0$ of $S$ at $q_0$ and a representative $\omega_0$ of $o_M(q_0)$. In these charts put $\hat g = g \circ \varphi^{-1}$, $\psi = \varphi \circ \iota \circ c_0^{-1}$, $\hat\nu(q) = -\sum_i d\hat g_{\varphi(q)}(e_i)\, e_i$ and $\Lambda(q)(\zeta) = \omega_0(\hat\nu(q), d\psi_{c_0(q)}\zeta)$. For a fixed basis $u_0$ of $Z$, $q \mapsto \Lambda(q)(u_0)$ is continuous near $q_0$, being a determinant with continuous entries.
2. Near $q_0$ the derivative $D\varphi_q$ of the fixed chart carries $o_M(q)$ to $o_M(q_0)$, because $o_M$ is an orientation; so $\omega_0 \circ D\varphi_q = \kappa\, \omega_q$ with $\kappa > 0$, $\omega_q$ the chosen representative of $o_M(q)$ ⟦Chapter6/LevelOrientM · exists_pos_smul_of_orSign_eq_one⟧. Pullbacks move inside the contraction: contracting $\omega \circ L$ with $(\nu, T)$ is contracting $\omega$ with $(L\nu, L T)$ ⟦Chapter6/LevelOrientM · contractForm_pullback⟧. Next, $D\varphi_q(\nu_q) = a\, \hat\nu(q) + t$ with $a = d\hat g(D\varphi_q\nu_q)/d\hat g(\hat\nu(q))$, which is positive because both values are negative, and with $t \in \ker d\hat g$, which is the image $D\varphi_q(d\iota_q Z)$ of the tangent space. A tangent summand contributes nothing, as $n + 1$ vectors in an $n$-dimensional image are dependent ⟦Chapter6/SignLemmas · contractForm_eq_smul⟧. With the chain rule $D\varphi_q \circ d\iota_q = d\psi_{c_0(q)} \circ Dc_0(q)$, the representative at $q$ is a positive multiple of $\Lambda(q) \circ Dc_0(q)$.
3. Top forms on $Z$ form a line, so $\Lambda(q) = \big(\Lambda(q)u_0/\Lambda(q_0)u_0\big)\Lambda(q_0)$, with a ratio that is positive near $q_0$ by step 1. At $q_0$ both chart derivatives are the identity. Evaluating the two representatives on $Dc_0(q)^{-1}u_0$ gives positive factors times $(\Lambda(q_0)u_0)^2$, so the sign is $+1$ ⟦Chapter6/LevelOrientM · levelOrientM_cont⟧.

**The bridge to pair maps.** Let $N$ be a smooth manifold without boundary modelled on a space $F$ of dimension $n$, with $E$ and $F$ in a common universe, oriented by $o_N$, and $f : M \to N$ differentiable at $q \in S$. Then
$$\operatorname{sign}_q(f|_S) = (-1)^{n+1} \operatorname{sign}_q(f, g),$$
the left side for the level-set orientation and $o_N$, the right side for $o_M$ and the product orientation of $N \times \mathbb R$ (a positive basis of $TN$ followed by $\partial_t$) ⟦Chapter5/Orient · Orient.prodReal⟧ ⟦Chapter6/LevelSignM · signAt_levelOrientM_eq'⟧. Both signs are evaluated on the basis $(\nu_q, d\iota_q u_0)$ of $E$. On the left one gets the sign of $\eta(df_q\, d\iota_q u_0) \cdot \omega(\nu_q, d\iota_q u_0)$, with $\eta$ representing $o_N(f(q))$. On the right, the matrix of $d(f, g)_q$ on that basis has last row $(dg_q\nu_q, 0, \dots, 0)$ because $dg_q \circ d\iota_q = 0$. Expanding along that row gives $(-1)^n dg_q(\nu_q) \det(df_q\, d\iota_q u_0)$, and $dg_q(\nu_q) < 0$ supplies the last factor $-1$. The same computation in a vector space is ⟦Chapter6/LevelSign · signAt_levelOrient_eq'⟧.

> **Theorem (V6.1, Lemma 1 of §5 on an open set).** In the setting above, with $N$, $F$ as in the bridge ($E$ and $F$ in a common universe), let $M$ and $N$ be Hausdorff, $U \subseteq M$ open with $g^{-1}(0) \subseteq U$, $f$ smooth on $U$, and $y$ a regular value of $f|_U$. Assume transversality: for every $x \in g^{-1}(0)$ with $f(x) = y$ there is $w$ with $df_x w = 0$ and $dg_x w \ne 0$. If $\{x \in U : f(x) = y,\ g(x) \ge 0\}$ is compact, then $(f|_S)^{-1}(y)$ is finite and $\deg(f|_S; y) = 0$ for the level-set orientation. ⟦Chapter6/LevelZero · degAt_level_eq_zero_of_opens⟧

**The proof as formalized.** Chapter 5's ambient Lemma 1 says that the signed count of $f^{-1}(y) \cap g^{-1}(0)$, with the signs of the pair map $(f, g)$, is finite and vanishes ⟦Chapter5/LemmaOne · lemmaOne_ambient'⟧. It is applied to the manifold $U$ with the restricted orientation ⟦Chapter6/Opens · Orient.restrict⟧. The inclusion of $U$ has identity derivative in the restricted charts, so signs in $U$ and in $M$ agree ⟦Chapter6/Opens · signAt_restrict⟧. Since $g^{-1}(0) \subseteq U$, the sum over $U$ is the sum over $M$, and the bridge turns each pair-map sign into $(-1)^{n+1}$ times a level-set sign.

Transversality is how the formal Lemma 1 says that $y$ is a regular value of $f$ on the boundary. In the region lemma (V6.3) it is derived from regularity of the restriction: if $f|_S$ is regular at $q$, a nonzero vector of $\ker df_q$ (one exists by counting dimensions) cannot be tangent to $S$, for $f|_S$ would kill its preimage ⟦Chapter6/LevelZero · exists_mfd_eq_zero_of_isRegularPoint_level⟧. That lemma also assumes $f$ regular at $q$, which its proof never uses.

### V6.2 The sign of a map between level sets

> **Theorem (V6.2).** Let $M, M'$ be smooth manifolds with charts in $E$, $\dim E = n + 1$, oriented by $o_M, o_{M'}$, and let $G : M \to \mathbb R$, $G' : M' \to \mathbb R$ be smooth with $0$ as a regular value, both level sets being modelled on a space $Z$ of dimension $n$ as in V6.1. Let $\Phi : M \to M'$ map $G^{-1}(0)$ into $G'^{-1}(0)$, with $\Phi|_{G^{-1}(0)} : G^{-1}(0) \to M'$ smooth and $\Phi$ differentiable at $q \in G^{-1}(0)$. If $dG'_{\Phi(q)} \circ d\Phi_q = c\, dG_q$ with $c \ne 0$, then
> $$\operatorname{sign}_q\big(\Phi : G^{-1}(0) \to G'^{-1}(0)\big) = \operatorname{sgn}(c)\, \operatorname{sign}_q \Phi,$$
> with the level-set orientations on the left and $o_M, o_{M'}$ on the right. ⟦Chapter6/LevelMap · signAt_levelOrientM_map'⟧

The case $c > 0$ is stated separately ⟦Chapter6/LevelMap · signAt_levelOrientM_map⟧.

**The idea.** $d\Phi_q$ sends the outward vector at $q$ to $a$ times the outward vector at $\Phi(q)$ plus a tangent vector, with $\operatorname{sgn} a = \operatorname{sgn} c$, and tangent vectors are invisible to the contracted form.

**The proof as formalized.** Let $T, T'$ be the derivatives of the two inclusions and $\Phi_S$ the restricted map, so that $T' \circ d\Phi_S = d\Phi_q \circ T$. Write $d\Phi_q(\nu) = a\nu' + t$ with $a = dG'(d\Phi_q \nu)/dG'(\nu')$; then $dG'(t) = 0$, so $t$ lies in the image of $T'$. Since $dG'(d\Phi_q\nu) = c\, dG(\nu)$ and both $dG(\nu)$ and $dG'(\nu')$ are negative, $\operatorname{sgn} a = \operatorname{sgn} c$. With $\omega' \circ d\Phi_q = c'\omega$, so that $\operatorname{sign}_q \Phi = \operatorname{sgn} c'$,
$$\omega'(\nu', T' d\Phi_S \zeta) = a^{-1}\omega'(d\Phi_q \nu, d\Phi_q T\zeta) = a^{-1}c'\, \omega(\nu, T\zeta).$$
The first equality drops $t$, because $t$ and all the $d\Phi_q T\zeta$ lie in the $n$-dimensional image of $T'$ ⟦Chapter6/LevelMap · contractForm_eq_smul_of_mem⟧. The sign is therefore $\operatorname{sgn}(a^{-1}c') = \operatorname{sgn}(c) \operatorname{sign}_q\Phi$.

*This lemma has no counterpart in the book.* It is the single tool through which the formalization moves degrees between level sets, applied to four kinds of map: to the inclusion of a boundary component ($\Phi = \mathrm{id}$, $c$ the product of the other factors), to the parametrization $u \mapsto z + \varepsilon u$ of a sphere ($c = 1$), to a diffeomorphism $f$ ($c = -r^2$) and to the radial map $\Theta$ ($c = 1$), the last two in V6.5. Ambient signs come from one fact: for a self-map of an oriented vector space the sign is $\operatorname{sgn}\det$ ⟦Chapter6/LevelMap · orSign_self_eq_sgn_det⟧. For the degrees, composing on either side with a bijection of constant sign $\sigma = \pm 1$ multiplies $\deg(\cdot\,; y)$ by $\sigma$, the point $y$ being moved by the bijection when it acts on the left ⟦Chapter6/LevelMap · degAt_comp_bij⟧ ⟦Chapter6/Compose · degAt_comp_bij'⟧ ⟦Chapter6/Compose · degAt_comp_bij_left⟧.

### V6.3 The region lemma

> **Theorem (V6.3).** Let $n \ge 1$ and $v : \mathbb R^{n+1} \to \mathbb R^{n+1}$ smooth. Let $G : \mathbb R^{n+1} \to \mathbb R$ be smooth with $0$ a regular value and $X = \{G \ge 0\}$ compact. Let $\varepsilon > 0$ and $z_1, \dots, z_k$ be points with $G > 0$ on each closed ball $\bar B_\varepsilon(z_i)$ and $|z_i - z_j| > 2\varepsilon$ for $i \ne j$, and suppose every zero of $v$ in $X$ is one of the $z_i$. Then
> $$\sum_{i=1}^k \operatorname{ind}_\varepsilon(v; z_i) = \deg\big(\hat v : G^{-1}(0) \to S^n\big),$$
> where $G^{-1}(0)$ carries the level-set orientation for $o_E$, reversed, and $S^n$ carries $o_{S^n}$. ⟦Chapter6/Region · sum_indexAt_eq_deg⟧

Milnor assumes the zeros in $X$ are exactly the $z_i$; the formal statement needs only that they lie among them.

**The idea.** As in Milnor's proof of Hopf's lemma (his Lemma 3): delete small open balls around the zeros, apply Lemma 1 of §5 to $\hat v$ on what remains, and split the boundary into $\partial X$ and the small spheres, each of which contributes an index.

**The proof as formalized.**
1. *The region with holes as one sublevel set.* Put $G_i(x) = |x - z_i|^2/\varepsilon^2 - 1$ and $g = G \prod_i G_i$ ⟦Chapter6/Region · Gsph⟧ ⟦Chapter6/Region · gProd⟧. At a zero of one factor every other factor is positive, because the balls are disjoint and lie in $\{G > 0\}$ ⟦Chapter6/Region · Gf_pos_of_ne⟧. So $g^{-1}(0)$ is the disjoint union of $G^{-1}(0)$ and the spheres $S_\varepsilon(z_i)$. At a zero of one factor, $dg$ is the derivative of that factor times the product of the others, a positive coefficient ⟦Chapter6/LevelZero · mfd_prod_of_eq_zero⟧, so $0$ is a regular value of $g$. Moreover $g \ge 0$ forces $G \ge 0$ and $|x - z_i| \ge \varepsilon$ for all $i$ ⟦Chapter6/Region · mem_K_of_gProd_nonneg⟧, and $v \ne 0$ on $g^{-1}(0)$ ⟦Chapter6/Region · ne_zero_of_gProd_eq_zero⟧.
2. *A common regular value.* The proof picks $y \in S^n$ regular for $\hat v$ on the open set $U = \{v \ne 0\}$, for $\hat v$ on $G^{-1}(0)$, and for each sphere map $s_{v, z_i, \varepsilon}$. The first set of regular values is dense by Brown's theorem ⟦Chapter2/Brown · dense_regularValues⟧. The others are open and dense because the domains are compact: the critical points form a closed set, since the sign is locally constant near a regular point, and their image is compact ⟦Chapter6/RegularOpen · isOpen_regularValues⟧. A dense set meets finitely many open dense sets in the Baire space $S^n$ ⟦Chapter6/RegularOpen · exists_mem_of_dense_of_isOpen⟧. Regularity of $\hat v$ on $S_\varepsilon(z_i)$ follows from that of $s_{v,z_i,\varepsilon} = \hat v|_{S_\varepsilon(z_i)} \circ \psi_i$, where $\psi_i(u) = z_i + \varepsilon u$.
3. *Transversality and compactness.* A point $x \in g^{-1}(0)$ with $\hat v(x) = y$ lies on exactly one component, the zero set of one factor $G_\ast$ (either $G$ or some $G_i$), where both $\hat v$ and its restriction are regular. The transversality lemma of V6.1 gives $w \in \ker d\hat v_x$ with $dG_\ast(w) \ne 0$, hence $dg(w) \ne 0$. The set $\{x \in U : \hat v(x) = y,\ g(x) \ge 0\}$ is closed in the compact set $X \cap \bigcap_i \{|x - z_i| \ge \varepsilon\}$, on which $v$ has no zero.
4. *Lemma 1.* V6.1 on $M = \mathbb R^{n+1}$ with $o_E$ and the open set $U$ gives $\deg(\hat v|_{g^{-1}(0)}; y) = 0$ for the level-set orientation of $g$.
5. *Splitting.* By V6.2 with $\Phi = \mathrm{id}$ and $c > 0$ the product of the other factors, the inclusion of each component $G^{-1}(0)$ or $G_i^{-1}(0)$ into $g^{-1}(0)$ has sign $+1$ everywhere. By the chain rule for signs ⟦Chapter6/SignLemmas · signAt_comp'⟧, the vanishing count splits as
$$0 = \deg(\hat v|_{G^{-1}(0)}; y) + \sum_i \deg(\hat v|_{S_\varepsilon(z_i)}; y),$$
each component carrying the level-set orientation of its own function.
6. *The pieces.* The first term is $\deg(\hat v|_{G^{-1}(0)})$, since $G^{-1}(0)$ is compact. On the sphere $S_\varepsilon(z_i) = G_i^{-1}(0)$, the bijection $\psi_i$ from $S^n$ has sign $+1$ by V6.2 with $c = 1$: $G_i \circ \psi_i$ is exactly $|u|^2 - 1$, and the ambient sign of $u \mapsto z_i + \varepsilon u$ is $\operatorname{sgn}\varepsilon^{n+1} = 1$ ⟦Chapter6/Region · signAt_aff⟧. So the $i$-th term is $\deg(s_{v,z_i,\varepsilon}; y) = \operatorname{ind}_\varepsilon(v; z_i)$. Hence $\sum_i \operatorname{ind}_\varepsilon(v; z_i) = -\deg(\hat v|_{G^{-1}(0)})$, the degree for the reversed orientation ⟦Chapter6/LevelZero · Orient.neg⟧ ⟦Chapter6/LevelZero · deg_neg_left⟧.

*Where the formal proof departs from Milnor.* In both proofs the small spheres, as part of $\partial X'$, carry the orientation opposite to that of boundaries of balls: here each is a component of $g^{-1}(0)$ with the level-set orientation of $G_i$. Milnor's index uses the ball convention, so he moves the spheres to the other side of the equation. The formal index uses $o_{S^n}$, which has the complement convention as well; the level-set orientation of $G_i$ is $o_{S^n}$ transported by $\psi_i$, the spheres keep their sign, and the reversal lands on $\partial X$ instead.

*What the book leaves implicit.* Milnor uses one regular value for all these maps at once. Its existence needs the openness of regular values for compact domains. Chapter 4 already had it, through V1.4 ⟦Chapter4/Degree · isOpen_isRegularValue⟧; the proof here uses a second version, proved through the local constancy of the sign and therefore stated for oriented manifolds ⟦Chapter6/RegularOpen · isOpen_regularPoints⟧ ⟦Chapter6/RegularOpen · isOpen_regularValues⟧.

### V6.4 Hopf's lemma

> **Theorem (V6.4).** Under the hypotheses of V6.3 (with $G$ smooth), suppose also that $dG_x(v(x)) < 0$ whenever $G(x) = 0$. Then
> $$\sum_{i=1}^k \operatorname{ind}_\varepsilon(v; z_i) = \deg\Big(x \mapsto \frac{-\nabla G(x)}{|\nabla G(x)|} : G^{-1}(0) \to S^n\Big),$$
> with the orientations of V6.3. ⟦Chapter6/Hopf · hopf_lemma⟧

The right-hand side does not involve $v$.

**The proof as formalized.** V6.3 rewrites the left side as the degree of $\hat v$ on $G^{-1}(0)$. On $G^{-1}(0) \times \mathbb R$ put $w(q, t) = (1 - \tau(t))\, v(q) + \tau(t)(-\nabla G(q))$. Since $dG_q(h) = \langle \nabla G(q), h\rangle$ ⟦Chapter6/Hopf · fderiv_apply_eq_inner_gradient⟧,
$$dG_q(w(q,t)) = (1 - \tau)\, dG_q(v(q)) - \tau\, |\nabla G(q)|^2 < 0,$$
because both terms are $\le 0$ and one is negative: the first when $\tau \le 1/2$, the second when $\tau > 1/2$, as $\nabla G \ne 0$ on $G^{-1}(0)$ by regularity. So $\hat w$ is a smooth homotopy on the compact manifold $G^{-1}(0)$ from $\hat v$ to the Gauss map, and the degrees agree. This is Milnor's proof of Lemma 3 (p. 35); the reparametrization by $\tau$ lets the homotopy be defined for all times.

### V6.5 Invariance of the index under diffeomorphisms (Milnor's Lemma 1)

> **Theorem (V6.5).** Let $n \ge 1$, $U, U' \subseteq \mathbb R^{n+1}$ open, and $f, g : \mathbb R^{n+1} \to \mathbb R^{n+1}$ with $f$ smooth on $U$, $f(U) \subseteq U'$, $g$ smooth on $U'$, $g(U') \subseteq U$, $g \circ f = \mathrm{id}$ on $U$ and $f \circ g = \mathrm{id}$ on $U'$. Let $v$ be smooth on $\mathbb R^{n+1}$ with an isolated zero at $z$ of radius $r > 0$, where $\bar B_r(z) \subseteq U$. Let $w$ be smooth on $\mathbb R^{n+1}$ with $w(y) = df_{g(y)}\big(v(g(y))\big)$ for $y \in f(\bar B_r(z))$. Then $\operatorname{ind}(w; f(z)) = \operatorname{ind}(v; z)$. ⟦Chapter6/Invariance · index_eq_of_diffeo⟧

The formal Poincaré–Hopf theorem (V6.9) does not use this result.

**The idea.** Milnor derives the lemma from his Lemma 2, that an orientation-preserving diffeomorphism of $\mathbb R^m$ is smoothly isotopic to the identity (first through $f(tx)/t$ to its derivative, then through $GL^+$), and treats reflections directly. The formal proof instead tracks signs. The region lemma turns $\operatorname{ind}(w; f(z))$ into a degree over $f(S_r(z))$; pulling back by $f$ costs $-\sigma$, with $\sigma = \operatorname{sgn}\det df$; a homotopy freezes the derivative at $z$; and $A = df_z$ acts on directions with sign $\sigma$. The two factors $\sigma$ cancel.

**The proof as formalized.**
1. *Linear algebra of $f$.* The relations $dg_{f(x)} \circ df_x = \mathrm{id}$ on $U$ and $df_{g(y)} \circ dg_y = \mathrm{id}$ on $U'$ make $df_x$ bijective on $U$. Let $\sigma = \operatorname{sgn}\det df_z$. It is also the sign of $\det df_x$ for every $x \in \bar B_r(z)$: along the segment from $z$ to $x$ the determinant is continuous and never zero, so the intermediate value theorem applies ⟦Chapter6/DetSign · continuous_det_clm⟧ ⟦Chapter6/DetSign · sgn_det_fderiv_eq⟧.
2. *The image region.* $G_0(y) = r^2 - |g(y) - z|^2$ is smooth on $U'$, and $f(\bar B_r(z)) = \{y \in U' : G_0(y) \ge 0\}$. With a cut-off $\chi$ equal to $1$ near this compact set and $0$ near the complement of $U'$, the function $G' = \chi G_0 + (\chi - 1)$ on $U'$, $G' = -1$ elsewhere, is smooth, with $\{G' \ge 0\} = f(\bar B_r(z))$ and $G' = G_0$ nearby ⟦Chapter6/Invariance1 · exists_region_fun⟧. Its zero set is $f(S_r(z))$, and $0$ is a regular value because $dG_0(df_x(x - z)) = -2|x - z|^2 \ne 0$.
3. *The index of $w$ by the region lemma.* Since $w(f(x)) = df_x(v(x))$, the only zero of $w$ in $f(\bar B_r(z))$ is $f(z)$. The set $f(B_r(z)) = U' \cap g^{-1}(B_r(z))$ is open, so it contains a closed ball about $f(z)$ of some radius $\varepsilon$, on which $G' > 0$. V6.3 with $k = 1$ gives $\operatorname{ind}_\varepsilon(w; f(z)) = -\deg(\hat w|_{f(S_r(z))})$ for the level-set orientation of $G'$.
4. *Pulling back by $f$ and $\psi$.* The restriction $f_S : S_r(z) \to f(S_r(z))$ is a bijection with sign $-\sigma$ at every point, by V6.2 with $c = -r^2$: near the sphere $G'(f(x)) = r^2 - |x - z|^2 = -r^2(|x - z|^2/r^2 - 1)$, and the ambient sign of $f$ is $\sigma$. The parametrization $\psi(u) = z + ru$ of $S_r(z)$ has sign $+1$ ⟦Chapter6/Invariance1 · ψaff⟧ ⟦Chapter6/Invariance1 · signAt_ψaff⟧. A regular value $y$ of $\hat w|_{f(S_r(z))}$ (Brown) stays regular after precomposition with maps whose derivatives are surjective ⟦Chapter6/Invariance1 · IsRegularValue.comp_of_surjective⟧. So $\deg(u \mapsto \hat w(f(z + ru))) = -\sigma \deg(\hat w|_{f(S_r(z))}; y)$.
5. *Freezing the derivative.* $H(u, t) = df_{z + \tau(t) r u}\big(v(z + ru)\big)$ never vanishes, since $v \ne 0$ on the sphere and $df$ is invertible on the ball. At $t = 1$ it equals $w(f(z + ru))$. At $t = 0$ it is $A\,v(z + ru)$ with $A = df_z$, whose normalization is $h(s_{v,z,r}(u))$ for $h(u) = Au/|Au|$, because normalization ignores positive factors ⟦Chapter6/Invariance1 · nv0_smul⟧. Homotopy invariance equates the two degrees.
6. *The linear end.* $h$ is a bijection of $S^n$, with inverse $u \mapsto \widehat{A^{-1}u}$, of sign $\sigma$ at every point (next subsection). For a regular value $y''$ of $h \circ s_{v,z,r}$, the point $y_0 = h^{-1}(y'')$ is regular for $s_{v,z,r}$ because $dh$ is injective ⟦Chapter6/Invariance1 · IsRegularValue.of_comp_injective⟧, and $\deg(h \circ s_{v,z,r}) = \sigma \deg(s_{v,z,r}; y_0) = \sigma \operatorname{ind}_r(v; z)$.
7. *Assembly.* Steps 4–6 give $-\sigma \deg(\hat w|_{f(S_r(z))}; y) = \sigma \operatorname{ind}_r(v; z)$, and $\sigma^2 = 1$. As $f(z)$ is an isolated zero of $w$ of radius $\varepsilon$, $\operatorname{ind}(w; f(z)) = \operatorname{ind}_\varepsilon(w; f(z)) = -\deg(\hat w|_{f(S_r(z))}) = \operatorname{ind}_r(v; z) = \operatorname{ind}(v; z)$.

#### Replacing Lemma 2: the radial map

> **Proposition.** For a bijective linear map $A$ of $\mathbb R^{n+1}$ and every $u \in S^n$, the sign at $u$ of $u \mapsto Au/|Au|$, for $o_{S^n}$ on both sides, is $\operatorname{sgn}\det A$. ⟦Chapter6/Radial · signAt_nv0_linear⟧

**The proof as formalized.** The map is the restriction to $S^n$ of $\Theta(x) = \lambda(x)\,Ax$ with $\lambda(x) = |x|/|Ax|$ ⟦Chapter6/Radial · lam⟧ ⟦Chapter6/Radial · Θ⟧. $\Theta$ preserves $|x|$, hence the defining function $|x|^2 - 1$ ⟦Chapter6/Radial · sphG_Θ⟧, so V6.2 with $c = 1$ makes the sign on the sphere equal to $\operatorname{sgn}\det d\Theta_u$. Now
$$d\Theta_u = \lambda(u)A + d\lambda_u \otimes Au = \big(\lambda(u)\,\mathrm{id} + \mu \otimes Au\big) \circ A, \qquad \mu = d\lambda_u \circ A^{-1}.$$
Because $\lambda$ is homogeneous of degree $0$, Euler's identity $d\lambda_u(u) = 0$ holds ⟦Chapter6/Radial · fderiv_lam_self⟧, that is, $\mu(Au) = 0$. The matrix determinant lemma $\det(\mathrm{id} + \mu \otimes p) = 1 + \mu(p)$ ⟦Chapter6/Radial · det_id_add_smulRight⟧ gives $\det(c\,\mathrm{id} + \mu \otimes p) = c^{n+1}$ when $\mu(p) = 0$ ⟦Chapter6/Radial · det_smul_id_add_smulRight⟧. Hence $\det d\Theta_u = \lambda(u)^{n+1}\det A$ with $\lambda(u) > 0$ ⟦Chapter6/Radial · det_fderiv_Θ⟧.

*Where the formal proof departs from Milnor.* Neither deformation of Lemma 2 is used. The deformation of $f$ through $f(tx)/t$ into $df_z$ is replaced by the homotopy of step 5, which moves only the base point of the derivative, and the isotopy of $df_z$ through $GL^+$ by the sign computation above. That $GL^+$ is connected by smooth paths is proved only later, for §7 ⟦Chapter7/GLplus · exists_glPath⟧. Lemma 2 itself is a theorem of this development (V6.12 below), reached through Hadamard's lemma (V6.11); nothing depends on it, and this proof does not go through it.

### V6.6 The ε-neighbourhood theorem

> **Theorem (V6.6).** Let $N \subseteq \mathbb R^k$ be a slice submanifold with model $\mathbb R^n$ and complement $\mathbb R^m$, compact and nonempty. There are $\varepsilon > 0$ and $r : \mathbb R^k \to N$ such that:
>
> (i) $|x - r(x)| = \operatorname{dist}(x, N)$ for every $x$;
>
> (ii) if $\operatorname{dist}(x, N) < \varepsilon$, every nearest point of $N$ to $x$ equals $r(x)$;
>
> (iii) $r(x) = x$ for $x \in N$;
>
> and for every $x$ with $\operatorname{dist}(x, N) < \varepsilon$:
>
> (iv) $r$ is smooth at $x$;
>
> (v) $x - r(x) \perp T_{r(x)}N$;
>
> (vi) $dr_x$ takes values in $T_{r(x)}N$;
>
> finally, (vii) if $x \in N$ and $v \perp T_xN$, then $r(x + sv) = x$ for all $s$ near $0$. ⟦Chapter6/Tubular3 · tubular⟧

Here $T_qN$ is the image of the derivative of the inclusion in the slice charts ⟦Chapter2/Submanifold · IsSliceSubmanifold⟧. Milnor quotes the theorem from §8 (Problems 11 and 12), where it comes from the normal bundle; the formal proof uses nearest points.

**The idea.** A nearest point $\varphi(z)$ of $x$ satisfies $(d\varphi_z)^*(x - \varphi(z)) = 0$. The inverse function theorem solves this equation uniquely and smoothly near each point of $N$, and compactness makes the radius uniform.

**The proof as formalized.**
1. *Parametrizations.* For $p \in N$ choose a slice chart $\sigma_p$ containing $p$ ⟦Chapter6/Tubular1 · σ⟧, and let $\Omega_p = \{z \in \mathbb R^n : (z, 0) \in \operatorname{target}\}$ ⟦Chapter6/Tubular1 · Ω⟧. Put $\varphi_p(z) = \sigma_p^{-1}(z, 0) \in N$ ⟦Chapter6/Tubular1 · φ⟧, and let $c_p(q)$ be the first component of $\sigma_p(q)$ ⟦Chapter6/Tubular1 · c⟧. Since $\sigma_p \circ \varphi_p$ is $z \mapsto (z, 0)$, $d\varphi_p$ is injective ⟦Chapter6/Tubular1 · injective_fderiv_φ⟧, and $T_qN$ is the image of $d\varphi_p$ at $c_p(q)$ ⟦Chapter6/Tubular1 · range_mfd_val⟧.
2. *The equation.* $F(z, x) = (d\varphi_z)^*(x - \varphi(z))$ ⟦Chapter6/Tubular2 · A⟧ ⟦Chapter6/Tubular2 · Fn⟧. If $q = \varphi(c_p(q))$ is a nearest point to $x$, then $z \mapsto |x - \varphi(z)|^2$ has a local minimum at $c_p(q)$, so $\langle x - \varphi(z), d\varphi_z a\rangle = 0$ for all $a$, which is $F(c_p(q), x) = 0$ ⟦Chapter6/Tubular2 · Fn_eq_zero_of_nearest⟧.
3. *The inverse function theorem.* $\Phi(z, x) = (F(z, x), x)$ ⟦Chapter6/Tubular2 · Φ⟧ has derivative $(a, b) \mapsto \big((d\varphi_{z_0})^*(b - d\varphi_{z_0}a),\, b\big)$ at $(z_0, \varphi(z_0))$; the term from differentiating $z \mapsto (d\varphi_z)^*$ is multiplied by $x - \varphi(z_0) = 0$ ⟦Chapter6/Tubular2 · hasFDerivAt_Φ⟧. It is injective, since $b = 0$ and $(d\varphi)^*d\varphi\, a = 0$ give $|d\varphi\, a|^2 = 0$, hence $a = 0$ by step 1 ⟦Chapter6/Tubular2 · injective_DΦ⟧. Let $U(x)$ be the first component of $\Phi^{-1}(0, x)$ ⟦Chapter6/Tubular2 · U⟧. Then $F(U(x), x) = 0$ for $x$ near $\varphi(z_0)$ ⟦Chapter6/Tubular2 · eventually_Fn_U⟧, and every solution near $(z_0, \varphi(z_0))$ has $z = U(x)$ ⟦Chapter6/Tubular2 · eventually_eq_U⟧. The library's inverse function theorem gives smoothness of the local inverse only at the one image point; smoothness on a neighbourhood follows because invertibility of $d\Phi$ is an open condition and the inverse is smooth wherever it holds ⟦Chapter6/Tubular2 · exists_contDiffOn_U⟧.
4. *A good radius at each point.* For each $p \in N$ there is $\delta_p > 0$ such that, for $|x - p| < \delta_p$, every nearest point of $x$ is $\varphi_p(U_p(x))$, and $U_p$ solves the equation and is smooth at $x$. A nearest point $q$ satisfies $|q - p| \le 2|x - p|$, so it lies in the chart with $c_p(q)$ near $z_0$, and Fermat's condition with uniqueness gives $c_p(q) = U_p(x)$ ⟦Chapter6/Tubular3 · exists_good⟧.
5. *A uniform radius.* Some $\varepsilon > 0$ has the property that $\operatorname{dist}(x, N) < \varepsilon$ implies $|x - p| < \delta_p$ for some $p \in N$ ⟦Chapter6/Tubular3 · exists_eps⟧. Otherwise there are $x_j$ with $\operatorname{dist}(x_j, N) < 1/(j+1)$ and $|x_j - p| \ge \delta_p$ for all $p$. Their nearest points have a subsequence converging to some $p \in N$, along which $x_j \to p$: a contradiction. The radii $\delta_p$ are chosen with no continuity in $p$, and the sequential argument needs none.
6. *Conclusion.* $r(x)$ is a nearest point chosen for every $x$, using compactness and nonemptiness ⟦Chapter6/Tubular3 · nearestPt⟧. Near any $x$ with $\operatorname{dist}(x, N) < \varepsilon$, $r = \varphi_p \circ U_p$, which gives (ii) and (iv); (v) is $\langle x - \varphi(U(x)), d\varphi\, a\rangle = \langle F(U(x), x), a\rangle = 0$, and (vi) is $dr_x = d\varphi \circ dU_x$. For (vii), $F(z_0, x + sv) = s\,(d\varphi_{z_0})^*v = 0$, and uniqueness gives $U(x + sv) = z_0$. Clause (vii) serves Chapter 7, not this chapter.

*Hidden hypotheses.* $N$ is nonempty, and the model and complement are Euclidean spaces, so that adjoints exist.

### V6.7 The region $N_{\varepsilon/2}$ and the extended field

Take $N \subseteq \mathbb R^{K+1}$ and fix $\varepsilon$ and $r$ from V6.6, chosen by the axiom of choice ⟦Chapter6/Tubular4 · tubε⟧ ⟦Chapter6/Tubular4 · tubr⟧. Let $N_\varepsilon = \{\operatorname{dist}(\cdot, N) < \varepsilon\}$ ⟦Chapter6/Tubular4 · Nε⟧ and $X = \{\operatorname{dist}(\cdot, N) \le \varepsilon/2\}$, compact because closed and bounded ⟦Chapter6/Tubular4 · X⟧ ⟦Chapter6/Tubular4 · isCompact_X⟧. A *tangent field* is a smooth $v : N \to \mathbb R^{K+1}$ with $v(q) \in T_qN$ for all $q$.

> **Theorem (V6.7).** (a) There is a smooth $G : \mathbb R^{K+1} \to \mathbb R$ with $\{G \ge 0\} = X$, $G = G_0 := (\varepsilon/2)^2 - |x - r(x)|^2$ near $X$, and $0$ a regular value ⟦Chapter6/Tubular4 · exists_G⟧ ⟦Chapter6/Tubular4 · isRegularValue_G⟧. (b) For a smooth $v : N \to \mathbb R^{K+1}$, the field $w(x) = v(r(x)) + (x - r(x))$ ⟦Chapter6/Tubular4 · w₀⟧ is smooth on $N_\varepsilon$ and equals $v$ on $N$. If $v$ is a tangent field, the zeros of $w$ in $N_\varepsilon$ are the zeros of $v$, and $dG_0(w(x)) = -2|x - r(x)|^2$ on $N_\varepsilon$.

**The proof as formalized.** On $N_\varepsilon$, $dG_0(h) = -2\langle x - r(x), h - dr_x h\rangle = -2\langle x - r(x), h\rangle$, because $dr_x h \in T_{r(x)}N$ is orthogonal to $x - r(x)$ ⟦Chapter6/Tubular4 · fderiv_G₀_apply⟧. This is Milnor's "easy computation" $\operatorname{grad}\varphi = 2(x - r(x))$ on p. 38. The function $G$ is $\chi G_0 + (\chi - 1)$ on $N_\varepsilon$ and $-1$ elsewhere, with $\chi$ smooth, $1$ near $X$ and $0$ near the complement of $N_\varepsilon$. Outside $X$, $G \ge 0$ would force $\chi = 1$ and then $G = G_0 < 0$. At a zero of $G$, $|x - r(x)| = \varepsilon/2$ and $dG(x - r(x)) = -2|x - r(x)|^2 \ne 0$. On $N$ the retraction is the identity, so $w = v$ there ⟦Chapter6/Tubular4 · w₀_of_mem⟧. For a tangent field $v$, $v(r(x))$ is tangent at $r(x)$, hence orthogonal to $x - r(x)$, so $\langle w(x), x - r(x)\rangle = |x - r(x)|^2$, and a zero of $w$ has $x = r(x) \in N$ and $v(x) = 0$ ⟦Chapter6/Tubular4 · w₀_eq_zero⟧. The same orthogonality gives $dG_0(w)$ ⟦Chapter6/Tubular4 · fderiv_G₀_w₀⟧. Smoothness holds because $r$ is smooth from $N_\varepsilon$ into the manifold $N$ ⟦Chapter6/Tubular4 · contMDiffOn_w₀⟧.

### V6.8 The index of a tangent field on $N$

For a smooth $v : N \to \mathbb R^{K+1}$, let $\tilde w$ be a global smooth field that agrees with $w$ near $X$, chosen through the cut-off lemma ⟦Chapter6/PoincareHopf · wext⟧. The index of $v$ at $q \in N$ is *defined* as $\operatorname{ind}_N(v; q) := \operatorname{ind}(\tilde w; q)$ ⟦Chapter6/PoincareHopf · indexN⟧.

> **Proposition (V6.8).** Let $K \ge 1$, $v : N \to \mathbb R^{K+1}$ smooth and $q \in N$. If $w'$ is smooth on $\mathbb R^{K+1}$ and agrees with $w$ near $q$, and $q$ is an isolated zero of $\tilde w$ of some radius $r > 0$, then $\operatorname{ind}_N(v; q) = \operatorname{ind}(w'; q)$. ⟦Chapter6/PoincareHopf · indexN_eq⟧

Indeed $\tilde w = w$ near $q$, because $q \in N \subseteq X$, and V6.0(c) applies. So $\operatorname{ind}_N$ depends only on the germ of $w$ at $q$, which is determined by $v$ and by the nearest-point retraction, canonical on $N_\varepsilon$.

*Where the formal definition departs from Milnor.* Milnor defines the index through a chart, needs his Lemma 1 (V6.5) for it to be well defined, and remarks on p. 38 that it equals the index of $w$. Here the second quantity is the definition, and the theorem below is proved for it. The chart definition is formalized too, and the two are proved equal at a non-degenerate zero (V6.14), which is Milnor's Lemma 5 and is what his own arguments use. At an arbitrary isolated zero the agreement is not proved and cannot be with what this development has; V6.14 says what it would need, and Milnor does not prove it either. For the theorem below the difference does not arise, its content being the independence of the index sum from $v$.

### V6.9 The Poincaré–Hopf theorem

> **Theorem (V6.9).** Let $N \subseteq \mathbb R^{K+1}$, $K \ge 1$, be a slice submanifold with model $\mathbb R^n$ and complement $\mathbb R^m$, compact and nonempty. There is an integer $\chi$ with the following property. Let $v : N \to \mathbb R^{K+1}$ be smooth with $v(q) \in T_qN$ for all $q$, and let $z_1, \dots, z_j$ be distinct points of $N$ with $\{q : v(q) = 0\} = \{z_1, \dots, z_j\}$. Then
> $$\sum_{i=1}^j \operatorname{ind}_N(v; z_i) = \chi.$$
> ⟦Chapter6/PoincareHopf · poincare_hopf⟧

**The idea.** As on Milnor's p. 38: the extended field points outward along $\partial N_{\varepsilon/2}$, so Hopf's lemma computes its index sum as the degree of a Gauss map that does not involve $v$.

**The proof as formalized.**
1. With $G$ from V6.7, let $\chi$ be the degree of $x \mapsto -\nabla G(x)/|\nabla G(x)|$ on $G^{-1}(0) = \partial X$, with the reversed level-set orientation and $o_{S^K}$ on the target. It is defined before $v$ is given.
2. Given $v$ and its zeros, let $d$ be the least distance between two distinct zeros ($d = 1$ if there are fewer than two), and $\varepsilon' = \min(\varepsilon/4, d/4)$.
3. Hopf's lemma applies to $\tilde w$, $X = \{G \ge 0\}$, the centres $z_i$ and the radius $\varepsilon'$. A point within $\varepsilon'$ of $z_i$ lies within $\varepsilon/4$ of $N$, hence in $X$, where $G = G_0 = (\varepsilon/2)^2 - \operatorname{dist}(x, N)^2 > 0$. Next, $2\varepsilon' < d \le |z_i - z_{i'}|$. A zero of $\tilde w$ in $X$ is a zero of $w$, hence of $v$, hence one of the $z_i$. On $\partial X$, $dG(\tilde w) = -2|x - r(x)|^2 < 0$.
4. Hopf's lemma gives $\sum_i \operatorname{ind}_{\varepsilon'}(\tilde w; z_i) = \chi$.
5. Each $z_i$ is an isolated zero of $\tilde w$ of radius $\varepsilon'$: $\tilde w(z_i) = v(z_i) = 0$, and any other zero in the ball would be some $z_{i'}$ at distance more than $2\varepsilon'$. So $\operatorname{ind}_N(v; z_i) = \operatorname{ind}_{\varepsilon'}(\tilde w; z_i)$ by V6.0(a).

*Not formalized.* The identification of $\chi$ with the Euler characteristic, which Milnor quotes; and manifolds not given inside a Euclidean space, which would need Whitney's embedding theorem (Milnor also works with $N \subseteq \mathbb R^k$). For $N = S^n$ the integer is computed: it is $1 + (-1)^n$ (V6.15).

### V6.10 The index of a non-degenerate zero (Milnor's Lemma 4)

**Theorem (V6.10).** Let $n \ge 1$ and let $v : \mathbb R^{n+1} \to \mathbb R^{n+1}$ be smooth with $v(z) = 0$ and $dv_z$ bijective. Then
$$\operatorname{ind}(v; z) = \operatorname{sgn}\det dv_z,$$
so the index is $+1$ or $-1$ according as the determinant is positive or negative, which is Milnor's own form of the lemma. ⟦Chapter6/Nondegenerate · index_eq_sgn_det⟧ ⟦Chapter6/Nondegenerate · index_nondegenerate⟧

That $z$ is an isolated zero is not assumed; it is part of what is proved.

*The idea* is Milnor's. Deform $v$ to its linear part along a straight line, which changes nothing by V6.0(b), and read off the sign of the resulting linear field from the radial computation of V6.5.

*The proof as formalized.* Write $A = dv_z$.

1. *One estimate does two jobs.* A bijective linear map is bounded below, $\|Ay\| \ge c\|y\|$ with $c > 0$ ⟦Chapter6/Nondegenerate · exists_lower_bound_of_bijective⟧, and $v(x) = A(x - z) + o(|x - z|)$. So there is a radius $r > 0$ on which no combination
$$A(x - z) + b\,\big(v(x) - A(x - z)\big), \qquad 0 \le b \le 1,$$
vanishes off $z$ ⟦Chapter6/Nondegenerate · exists_radius_of_nondegenerate⟧. The case $b = 1$ says that $z$ is an isolated zero of radius $r$; the whole range says that the straight-line homotopy from the linear field to $v$ keeps the $r$-sphere free of zeros ⟦Chapter6/Nondegenerate · linHomotopy⟧. By V6.0(b) and V6.0(a) the index of $v$ at $z$ is the index at $z$ of $x \mapsto A(x - z)$. Milnor takes both steps in one phrase.
2. *From a constant sign to a degree.* The sphere map of the linear field is $u \mapsto Au/|Au|$, whose sign at every point of $S^n$ is $\operatorname{sgn}\det A$ — the proposition of V6.5, which is what stands in this development for Milnor's appeal to Lemma 2. A constant pointwise sign is not yet a degree, and the passage is new here: the map is a bijection of $S^n$, so every point is a regular value with exactly one preimage, and the degree is that one sign ⟦Chapter6/Nondegenerate · deg_nv0_linear⟧.

*Hidden hypothesis.* $n \ge 1$, as everywhere in this part, the index being a degree on $S^n$.

### V6.11 Hadamard's lemma, and a parametric integral

Milnor's isotopy in Lemma 2 of §6 is $F(x, t) = f(tx)/t$, and the whole difficulty is smoothness at $t = 0$. It rests on a factorization $f(x) = L(x)\,x$ with $L$ smooth, and that rests on a fact Mathlib does not have.

**Theorem (V6.11).** Let $E$ and $F$ be real normed spaces with $F$ complete.

(a) If $h : E \times \mathbb R \to F$ is of class $C^n$, then so is $x \mapsto \int_0^1 h(x, t)\,dt$; likewise for $C^\infty$. ⟦Chapter6/Hadamard · contDiff_intervalIntegral⟧ ⟦Chapter6/Hadamard · contDiff_intervalIntegral_infty⟧

(b) *Hadamard's lemma.* A smooth $f : E \to F$ with $f(0) = 0$ factors as $f(x) = L(x)\,x$ with $L(x) = \int_0^1 df_{tx}\,dt$ smooth and $L(0) = df_0$. ⟦Chapter6/Hadamard · exists_hadamard⟧

(c) Hence $t^{-1}f(tx)$ extends to a smooth map of $E \times \mathbb R$ with value $df_0(x)$ at $t = 0$ — as an existence statement, and for the explicit formula "$df_0(x)$ if $t = 0$, else $t^{-1}f(tx)$" in which the isotopy is written. ⟦Chapter6/Hadamard · exists_contDiff_extension⟧ ⟦Chapter6/Hadamard · contDiff_ite_smul_inv⟧

**The idea.** Mathlib has the integral form of Taylor's theorem but no theorem saying that an integral over a fixed interval depends smoothly on a parameter, so (a) comes first. It is proved by induction on $n$, differentiating under the integral sign and dominating on a tube around the compact segment $\{x\} \times [0,1]$; the template is Mathlib's convolution file. Because the domination is on a tube and not on a compact set of the parameter, neither finite dimension nor local compactness is needed. Then (b) is the fundamental theorem of calculus along the segment from $0$ to $x$, $f(x) = \int_0^1 \frac{d}{dt}f(tx)\,dt = \int_0^1 df_{tx}(x)\,dt$, with (a) supplying the smoothness of the result in $x$; and (c) is (b) applied at $tx$.

*The one hypothesis Milnor would not state* is completeness of the target, so that the Bochner integrals exist; his spaces are $\mathbb R^m$. Otherwise the statements are more general than the book's, being about smooth maps between real normed spaces.

### V6.12 Lemma 2 of §6: an orientation-preserving diffeomorphism is isotopic to the identity

**Theorem (V6.12).** Every diffeomorphism $f$ of $\mathbb R^m$ — and more generally of a finite-dimensional real normed space $E$ — whose Jacobian determinant is positive at one point is smoothly isotopic to the identity. ⟦Chapter7/Isotopy · lemma2_of_sec6⟧ ⟦Chapter7/Isotopy · smoothIsotopicMap_id⟧

A diffeomorphism is given unbundled, as a smooth map with a smooth two-sided inverse, as in V6.5 ⟦Chapter7/Isotopy · IsDiffeoSelf⟧; an isotopy is a smooth $H : E \times \mathbb R \to E$ with $H(\cdot, 0) = f$, $H(\cdot, 1) = \mathrm{id}$ and *every* time slice a diffeomorphism, the shape already used in V4.4 ⟦Chapter7/Isotopy · SmoothIsotopicMap⟧. Positivity of the Jacobian at one point is positivity at every point, the sign of the determinant of the derivative of a diffeomorphism being constant ⟦Chapter7/Isotopy · IsDiffeoSelf.sgn_det_fderiv_const⟧.

**Nothing in the development depends on this lemma.** §6 replaced Milnor's appeal to it by the sign computation of V6.5, and it is formalized because it is a theorem of the book. The Lean file sits in `Chapter7/` because its last step is the $GL^+$ path of Chapter 7 and Chapter 6 may not import Chapter 7.

*The proof as formalized* is Milnor's, in three steps composed by transitivity. Translation carries $f$ to $x \mapsto f(x) - f(0)$ ⟦Chapter7/Isotopy · smoothIsotopicMap_sub_apply_zero⟧. A diffeomorphism fixing the origin is isotopic to its derivative there by $F(x, t) = f(tx)/t$, smooth by V6.11(c) ⟦Chapter7/Isotopy · smoothIsotopicMap_fderiv⟧. And a linear automorphism of positive determinant is isotopic to the identity along the $GL^+$ path of V7.3 ⟦Chapter7/Isotopy · smoothIsotopicMap_id_of_det_pos⟧ ⟦Chapter7/GLplus · exists_glPath⟧.

Three things Milnor passes over. Transitivity of isotopy needs the two isotopies made constant near the join before they are glued ⟦Chapter7/Isotopy · SmoothIsotopicMap.trans⟧. The slices at *negative* times must be diffeomorphisms too, because the definition asks for every real time. And invertibility of the derivative, which the first two steps use, comes from the chain rule applied to the two-sided inverse ⟦Chapter7/Isotopy · IsDiffeoSelf.bijective_fderiv⟧.

*Stronger than the book.* The statement is for any finite-dimensional real normed space, and positivity of the dimension is not needed.

### V6.13 Lemma 5, and the derivative of the retraction

Let $N \subseteq \mathbb R^{K+1}$ be a compact nonempty submanifold of dimension $n$, and $r$ the nearest-point retraction of V6.6.

**Theorem (V6.13).**

(a) At $q \in N$ the derivative $dr_q$ is the *orthogonal projection* of $\mathbb R^{K+1}$ onto $T_qN$: it is the identity on $T_qN$, its image is $T_qN$, it is idempotent, and its kernel is exactly $(T_qN)^\perp$. ⟦Chapter6/ChartIndex · Tub.dret⟧ ⟦Chapter6/ChartIndex · Tub.dret_apply_of_mem_tanN⟧ ⟦Chapter6/ChartIndex · Tub.ker_dret⟧

(b) *Milnor's Lemma 5.* If $v$ is a smooth tangent field on $N$ with $v(q) = 0$, the derivative of $v$ at $q$ carries $T_qN$ into itself — both in the ambient reading, the derivative at $q$ of $x \mapsto v(r(x))$, and in the intrinsic one, the derivative of $v : N \to \mathbb R^{K+1}$ on the image of the derivative of the inclusion. ⟦Chapter6/ChartIndex · Tub.dvr_mem_tanN⟧ ⟦Chapter6/ChartIndex · Tub.mfd_mem_tanN⟧

(c) Hence, at a zero of $v$, the derivative of the extended field $w = v \circ r + (\mathrm{id} - r)$ of V6.7 is $dv_q \circ dr_q + (\mathrm{id} - dr_q)$, which in the splitting $\mathbb R^{K+1} = T_qN \oplus (T_qN)^\perp$ is $dv_q$ on the tangent part and the identity on the normal one. So $\det dw_q$ is the determinant of the restriction $dv_q|_{T_qN}$, and $dw_q$ is invertible exactly when that restriction is. ⟦Chapter6/ChartIndex · Tub.dvT⟧ ⟦Chapter6/ChartIndex · Tub.det_fderiv_w₀⟧ ⟦Chapter6/ChartIndex · Tub.bijective_fderiv_w₀_iff⟧

**The idea.** V6.6 gives $x - r(x) \perp T_{r(x)}N$ and $dr_x$ with values in $T_{r(x)}N$; differentiating those two facts at a point of $N$, where $r$ is the identity, yields (a). For (b), differentiate the identity $(\mathrm{id} - dr)(v \circ r) = 0$ rather than the field itself.

*Where the route differs from Milnor's.* Milnor proves Lemma 5 by writing the field in a basis of coefficient fields and differentiating, which presumes the smoothness of the coefficients. Here nothing is written in coordinates: the identity $(\mathrm{id} - dr)(v \circ r) = 0$ holds because $v \circ r$ takes values in the tangent spaces, and differentiating it at a zero of $v$ kills the term in which $dr$ is differentiated, because it is multiplied by $v(q) = 0$.

*What Milnor leaves implicit* is what "the derivative of a field on a submanifold" means at all. Both readings are given, and their agreement is a theorem, not a convention.

*Hidden hypotheses.* $N$ compact and nonempty, because the retraction of V6.6 exists only then; Lemma 5 itself needs no compactness. The hypothesis $v(q) = 0$ is essential in (b) and is Milnor's: without it the derivative of $v$ at $q$ has no invariant meaning as an endomorphism of $T_qN$.

### V6.14 The chart definition of the index, and the agreement of the two

Milnor defines the index of a zero of a field on a manifold through a parametrization (p. 33): a local parametrization $\psi : \Omega \to N$, with $\Omega \subseteq \mathbb R^n$ open and $\psi(u_0) = q$, pulls $v$ back to a field on $\Omega$, and the index of $v$ at $q$ is the index of the pull-back at $u_0$. The formal version pulls back through the slice-chart parametrization of V6.6, extends the result to a global field by the cut-off of V6.0, and takes its index ⟦Chapter6/ChartIndex · Tub.chartField⟧ ⟦Chapter6/ChartIndex · Tub.chartIndexN⟧.

**Theorem (V6.14).** Let $N \subseteq \mathbb R^{K+1}$ be compact and nonempty, of dimension $n$.

(a) *The chart index depends neither on the parametrization nor on the extension.* For **any** smooth local parametrization $\psi$ of $N$ at $q$ with a smooth ambient left inverse $\chi$ and with $d\psi_u$ spanning the tangent space, and **any** globally smooth field on $\mathbb R^n$ that agrees near $u_0$ with the pull-back and has an isolated zero there, the index at $u_0$ is the chart index of $v$ at $q$. ⟦Chapter6/ChartIndex · Tub.index_eq_chartIndexN⟧

(b) At a non-degenerate zero both definitions are the sign of one determinant: the index of the extended field is $\operatorname{sgn}\det(dv_q|_{T_qN})$ by V6.13(c) and V6.10, and so is the chart index, because $d\varphi_q$ conjugates the derivative of the pulled-back field into that restriction. ⟦Chapter6/ChartIndex · Tub.indexN_eq_sgn_det⟧ ⟦Chapter6/ChartIndex · Tub.chartIndexN_eq_sgn_det⟧

(c) Hence **the chart definition agrees with the definition of V6.8 at every non-degenerate zero** (Milnor, pp. 33 and 37). ⟦Chapter6/ChartIndex · Tub.chartIndexN_eq_indexN⟧

Part (a) is Milnor's Lemma 1 (V6.5) applied to the transition $\chi_q \circ \psi$ between two parametrizations; it is what makes the chart index well defined, and it is exactly the use Milnor makes of his Lemma 1.

*Hidden hypotheses, and they are two.* The ambient index needs $K \ge 1$ and the chart index needs $n \ge 2$, because the two are degrees on spheres of *different* dimensions, $S^K$ and $S^{n-1}$; also $N$ compact and nonempty, as in V6.13.

*What is not proved, and why it is not a matter of effort.* The agreement at an arbitrary isolated zero. Since the two numbers are degrees of maps of spheres of different dimensions, no appeal to invariance under diffeomorphisms compares them. What is needed first is a suspension formula — that the index of a field of the shape $(u, y) \mapsto (\tilde v(u), y)$ on $\mathbb R^n \times \mathbb R^{K+1-n}$ is the index of $\tilde v$ — which this development does not have and which Milnor does not prove either. At a non-degenerate zero the question does not arise, and that is the case his arguments use.

### V6.15 The Euler number of the sphere

**Theorem (V6.15).** Let $n \ge 1$. For *every* smooth tangent field $v$ on $S^n$ whose zeros are finitely many distinct points $z_1, \dots, z_j$,
$$\sum_{i=1}^j \operatorname{ind}_{S^n}(v; z_i) = 1 + (-1)^n,$$
which is $2$ for $n$ even and $0$ for $n$ odd. ⟦Chapter6/EulerSphere · Sphere.indexSum_sph⟧ ⟦Chapter6/EulerSphere · Sphere.indexSum_sph_even⟧ ⟦Chapter6/EulerSphere · Sphere.indexSum_sph_odd⟧

This is Milnor's example on p. 39, with pp. 32–33. The integer of V6.9 is thereby not merely bounded but pinned down: any integer with the property that V6.9 asserts of $\chi$ equals $1 + (-1)^n$ ⟦Chapter6/EulerSphere · Sphere.eq_of_indexSum_sph⟧ ⟦Chapter6/EulerSphere · Sphere.poincare_hopf_sph⟧.

*The proof as formalized* is Milnor's. The field is the gradient on $S^n$ of the height function, $v(x) = e - \langle e, x\rangle x$ for a unit vector $e$ ⟦Chapter6/EulerSphere · Sphere.gradHeight⟧ ⟦Chapter6/EulerSphere · Sphere.gradSph⟧, whose zeros are exactly the two poles $e$ and $-e$. By V6.13 the derivative on the tangent space is minus the identity at $e$, of determinant $(-1)^n$, and the identity at $-e$, of determinant $1$ ⟦Chapter6/EulerSphere · Sphere.dvT_gradSph_pos⟧ ⟦Chapter6/EulerSphere · Sphere.dvT_gradSph_neg⟧, so V6.10 and V6.14 give the indices $(-1)^n$ and $1$ ⟦Chapter6/EulerSphere · Sphere.indexSum_gradSph⟧, and V6.9 transfers their sum to every field.

*The odd case is checked a second way.* For $n$ odd the sphere carries a nowhere-zero field, by the converse half of V5.10 rebuilt here ⟦Chapter6/EulerSphere · Sphere.exists_perp_linear⟧ ⟦Chapter6/EulerSphere · Sphere.exists_nonvanishing_tangent⟧, so the index sum is an empty sum and the integer is $0$ ⟦Chapter6/EulerSphere · Sphere.indexSum_sph_of_nonvanishing⟧; a third theorem derives $1 + (-1)^n = 0$ from the two computations, as it must ⟦Chapter6/EulerSphere · Sphere.indexSum_sph_odd_agree⟧.

*What had to be added.* §6's tubular machinery is written for slice charts whose *complement* model is a Euclidean space $\mathbb R^m$, whereas Chapter 5 presents $S^n$ as the level set of a real-valued function and so with the line itself as complement. The two are isomorphic but not the same model, so the presentation was redone with complement model $\mathbb R^1$ ⟦Chapter6/EulerSphere · Sphere.sphSub⟧, together with the tangent space at $q$ as $q^\perp$ for that structure ⟦Chapter6/EulerSphere · Sphere.mem_tanN_iff⟧ and the derivative through the retraction of a field coming from the ambient space ⟦Chapter6/EulerSphere · dvr_of_ambient⟧. For the same reason the nowhere-zero field of V5.10 had to be rebuilt here as an ambient linear map, some forty duplicated lines. A general lemma saying that two slice structures on the same set have the same smooth maps would remove them, and the project has none.

*Not formalized, and not writable.* That this integer is the **Euler characteristic** of $S^n$. This is a gap in vocabulary, not in effort: Mathlib has no Euler characteristic of a space, no Betti numbers and no cellular homology, so the sentence $\chi(S^n) = 1 + (-1)^n$ cannot be formed at all. Every statement here is about index sums of vector fields, and Milnor himself proves no more, referring to Hopf's theorem and to the literature. It is the one place where this edition is further from the book than a page count suggests.

### What the formalization taught us

- **The index is a total function**: $0$ at a point that is not an isolated zero, with junk values for the sphere map and the normalization where $v$ vanishes. Every theorem assumes the nonvanishing it needs, so these values never enter a result ⟦Chapter6/Index · index⟧ ⟦Chapter6/Index · sphMap⟧.
- **The sphere carries the complement convention**, so the region lemma reverses the orientation of $\partial X$, and the numbers are Milnor's ⟦Chapter5/HairyBall · sphOr⟧ ⟦Chapter6/Region · sum_indexAt_eq_deg⟧.
- **Lemma 1 of §5 was generalized twice**, to level sets in manifolds and to maps smooth only on an open set, at the price of a chart-level continuity proof ⟦Chapter6/LevelOrientM · levelOrientM_cont⟧ ⟦Chapter6/LevelZero · degAt_level_eq_zero_of_opens⟧.
- **A common regular value is not free.** It takes Brown's theorem, openness of regular values for compact domains (re-proved here through the sign, hence for oriented manifolds, although V1.4 already gives it), and the Baire property of $S^n$ ⟦Chapter6/RegularOpen · isOpen_regularPoints⟧ ⟦Chapter6/RegularOpen · exists_mem_of_dense_of_isOpen⟧.
- **One transport lemma replaces an isotopy.** V6.2 handles inclusions, affine parametrizations, the diffeomorphism and the radial map ⟦Chapter6/LevelMap · signAt_levelOrientM_map'⟧.
- **Milnor's Lemma 2 is not needed.** A homogeneous radial map, Euler's identity and the matrix determinant lemma compute the sign directly, and the intermediate value theorem keeps $\operatorname{sgn}\det df$ constant on a ball ⟦Chapter6/Radial · signAt_nv0_linear⟧ ⟦Chapter6/DetSign · sgn_det_fderiv_eq⟧. The lemma is nonetheless proved, and its cost is almost all in one fact Mathlib lacks: that an integral over a fixed interval depends smoothly on a parameter ⟦Chapter6/Hadamard · contDiff_intervalIntegral⟧ ⟦Chapter7/Isotopy · lemma2_of_sec6⟧.
- **The derivative of the retraction is the orthogonal projection.** That one identification carries Lemma 5, the determinant of the extended field, and both index computations of V6.14 ⟦Chapter6/ChartIndex · Tub.ker_dret⟧ ⟦Chapter6/ChartIndex · Tub.det_fderiv_w₀⟧.
- **Two indices, two sphere dimensions.** The extended field gives a degree on $S^K$ and a parametrization a degree on $S^{n-1}$, which is why the two definitions can be compared at a non-degenerate zero and not, as yet, anywhere else ⟦Chapter6/ChartIndex · Tub.chartIndexN_eq_indexN⟧.
- **The $\varepsilon$-neighbourhood theorem is proved, not quoted.** It needs $N$ nonempty, a separate proof that the local inverse is smooth on a neighbourhood, and a sequential compactness argument for the uniform radius ⟦Chapter6/Tubular2 · exists_contDiffOn_U⟧ ⟦Chapter6/Tubular3 · exists_eps⟧.
- **The index on $N$ is defined through the extension**, so Poincaré–Hopf does not depend on the invariance lemma; Milnor's chart definition is formalized beside it, and the two agree wherever his own arguments compare them ⟦Chapter6/PoincareHopf · indexN⟧ ⟦Chapter6/ChartIndex · Tub.chartIndexN⟧.
- **The exact hypotheses of Poincaré–Hopf:** ambient dimension at least $2$, $N$ compact and nonempty, finitely many zeros listed without repetition. The integer $\chi$ is a degree; for $S^n$ it is computed to be $1 + (-1)^n$, and calling it the Euler characteristic is a sentence this library cannot yet form ⟦Chapter6/PoincareHopf · poincare_hopf⟧ ⟦Chapter6/EulerSphere · Sphere.indexSum_sph⟧.
- **Two statements are slightly stronger than the book's, one hypothesis is idle.** The region lemma and Hopf's lemma need the zeros only to lie among the $z_i$; the transversality lemma assumes a regularity of $f$ that its proof never uses ⟦Chapter6/Hopf · hopf_lemma⟧ ⟦Chapter6/LevelZero · exists_mfd_eq_zero_of_isRegularPoint_level⟧.


## Part V. Framed cobordism, Theorem A and the first half of Theorem B (Milnor §7)

This part runs from framed submanifolds to Milnor's Theorem A and the first half of his Theorem B. Theorem A says the framed cobordism class of the Pontryagin manifold depends on neither the regular value nor the positive basis. The first half of Theorem B says smoothly homotopic maps $M \to S^p$ have framed cobordant Pontryagin manifolds. The formal text spends seventeen files on this, partly because it proves four facts the book quotes. Framed cobordism is symmetric and transitive; regular values form an open set; $GL^+(p,\mathbb R)$ is smoothly path connected; and a homotopy can be made constant near its ends without losing a regular value. Two definitional choices shape everything. A cobordism is a boundaryless submanifold of $M \times \mathbb R$. Every framing built from a map is an explicit formula, a pseudo-inverse of an ambient derivative, so its smoothness reduces to that of the ingredients.

**Map.** Paths are relative to `Milnor/`.

- `Chapter7/Transition`: a time change $\rho$, $0$ below $\varepsilon$, $1$ above $1-\varepsilon$, $\rho' > 0$ between.
- `Chapter7/Framed`: ambient tangent spaces, framed submanifolds, framed cobordisms.
- `Chapter7/Pontryagin`: the pseudo-inverse, the extension $\tilde F = c_y \circ f \circ r$, the Pontryagin manifold.
- `Chapter7/AdjXR`: adjoint and pseudo-inverse on $\mathbb R^{K+1} \times \mathbb R$.
- `Chapter7/Reparam`: a homotopy made constant near its ends.
- `Chapter7/Cobordism`: the cobordism $F^{-1}(z)$ inside Lemmas 2 and 3.
- `Chapter7/GLplus`: smooth paths in $GL^+(p,\mathbb R)$.
- `Chapter7/BasisPath`: smooth paths of bases.
- `Chapter7/Lemma1`: Lemma 1, general form.
- `Chapter7/RegOpen`: regular values of $M \to S^p$ form an open set.
- `Chapter7/Rotation`: planar rotations of $S^p$.
- `Chapter7/Transport`: time changes, locality of tangent spaces, gluing.
- `Chapter7/Equiv`: symmetry and transitivity.
- `Chapter7/Compose`: composing with a map of the sphere.
- `Chapter7/RotHomotopy`: rotating the target.
- `Chapter7/Lemma2`: Lemma 2 along an arc, then Theorem A.
- `Chapter7/ThmA`: the first half of Theorem B.

Letters follow Milnor. The file names, the project's docstrings and the verified edition use an older lettering: their "Lemma 2" is Theorem A, their "Lemma 3" is the construction of V7.2, their "Theorem A, first half" is the first half of Theorem B, their "Theorem B" is Theorem C, and their "Theorem C" is Milnor's unlettered product neighbourhood theorem.

### Standing conventions

$M \subseteq \mathbb R^{K+1}$ is a slice submanifold modelled on $\mathbb R^m$ (normal model $\mathbb R^w$), with the manifold structure induced by its slice charts ⟦Chapter2/Submanifold · IsSliceSubmanifold⟧. *The standing hypotheses* add that $M$ is compact and **nonempty** and that $n + p = m$. Nonemptiness is required by the tubular neighbourhood of Chapter 6, on which every framing is built. Hausdorffness and second countability come free for a subset of Euclidean space. Tangent spaces are subspaces of the ambient space: $T_xM \subseteq \mathbb R^{K+1}$ is the range of the derivative of the inclusion, and likewise for $N \subseteq M$ and, inside $\mathbb R^{K+1} \times \mathbb R$, for $S \subseteq M \times \mathbb R$ ⟦Chapter7/Framed · tangentM⟧ ⟦Chapter7/Framed · tangentN⟧ ⟦Chapter7/Framed · tangentS⟧. $S^p \subseteq \mathbb R^{p+1}$ is the zero set of $|x|^2 - 1$ with the slice structure of Chapter 2 and the orientation of Chapter 5 ⟦Chapter5/HairyBall · Sph⟧ ⟦Chapter5/HairyBall · sphOr⟧. Derivatives into $S^p$ are read in charts. So a "basis of $T_yS^p$" is a basis of the model space $\mathbb R^p$. It is *positive at $y$* when its orientation equals the orientation of the sphere read in the chart $c_y$ at $y$.

### V7.0 Framed submanifolds and framed cobordism

**Definition (framed submanifold).** Let $M \subseteq \mathbb R^k$ be a slice submanifold modelled on $\mathbb R^m$. A framed submanifold of dimension $n$ and codimension $p$ is a set $N \subseteq M$ together with maps $v_1, \dots, v_p : N \to \mathbb R^k$ such that:

- $N$ is a slice submanifold of $M$ modelled on $\mathbb R^n$ with normal model $\mathbb R^p$;
- $n + p = m$, and $N$ is compact;
- each $v_i$ is smooth for the induced structure on $N$;
- for every $x \in N$, $v_i(x) \in T_xM$ and $\langle v_i(x), w\rangle = 0$ for all $w \in T_xN$;
- $v_1(x), \dots, v_p(x)$ are linearly independent ⟦Chapter7/Framed · FramedSub⟧.

Only independence is asked; that the $v_i(x)$ then span the normal space of $N$ in $M$ follows by counting dimensions.

**Definition (framed cobordism).** Let $(N_0, v^0)$ and $(N_1, v^1)$ be framed submanifolds of $M$ of dimension $n$ and codimension $p$. A framed cobordism from the first to the second consists of the following data.

1. A slice submanifold $S$ of the product manifold $M \times \mathbb R$, modelled on $\mathbb R^{n+1}$ with normal model $\mathbb R^p$.
2. A number $\varepsilon$ with $0 < \varepsilon < \tfrac12$. For $t < \varepsilon$, $(x,t) \in S$ if and only if $x \in N_0$. For $t > 1 - \varepsilon$, $(x,t) \in S$ if and only if $x \in N_1$.
3. $S \cap (M \times [0,1])$ is compact.
4. Smooth maps $u_1, \dots, u_p : S \to \mathbb R^k \times \mathbb R$. At $q = (x,t)$, the $\mathbb R^k$-component of each $u_i(q)$ lies in $T_xM$. The $u_i(q)$ are orthogonal to $T_qS$ for $\langle (a,s),(b,t)\rangle = \langle a,b\rangle + st$ and linearly independent.
5. $u_i(x,t) = (v^0_i(x), 0)$ when $x \in N_0$ and $t < \varepsilon$, and $u_i(x,t) = (v^1_i(x), 0)$ when $x \in N_1$ and $t > 1-\varepsilon$.

Two framed submanifolds are *framed cobordant* if a framed cobordism exists ⟦Chapter7/Framed · FramedCob⟧ ⟦Chapter7/Framed · FramedCobordant⟧. The inner product on $\mathbb R^k \times \mathbb R$ is written out by hand, because Mathlib gives the product the sup norm and no inner product structure ⟦Chapter7/Framed · ipXR⟧.

*Where the formal definition departs from Milnor.* Milnor's cobordism is a compact manifold with boundary $X \subseteq M \times [0,1]$, a product near both ends. The formal $S$ has no boundary and lives for all times. Milnor's $X$ is $S \cap (M \times [0,1])$, and nothing here ever needs $X$ to be a manifold with boundary. The choice pays off twice and costs nothing.

- Cobordisms built from maps are level sets, which the regular value theorem of Chapter 2 makes slice submanifolds of a boundaryless manifold ⟦Chapter2/LevelSet · isSliceSubmanifold_preimage⟧. V7.2 uses $F^{-1}(z)$ for a homotopy on all of $M \times \mathbb R$. Lemma 1 uses $f^{-1}(y) \times \mathbb R$, realized as $(f \circ \mathrm{pr}_1)^{-1}(y)$.
- Symmetry and transitivity become preimages under $(x,t) \mapsto (x, at+c)$ and gluing along an *open* strip. With boundaries, gluing end to end is exactly where collars are needed.
- Nothing is lost: below $\varepsilon$, $S$ is exactly $N_0 \times (-\infty,\varepsilon)$, and above $1-\varepsilon$ exactly $N_1 \times (1-\varepsilon,\infty)$. Milnor's assumed product structure is built in.

### V7.1 The Pontryagin manifold

**Construction.** Assume the standing hypotheses. Let $f : M \to S^p$ be smooth, let $y$ be a regular value of $f$, and let $b_1, \dots, b_p \in \mathbb R^p$ be linearly independent. The Pontryagin manifold $(f^{-1}(y), f^*b)$ is the framed submanifold of dimension $n$ and codimension $p$ with underlying set $f^{-1}(y)$ and framing
$$v_i(x) = A_x^*(A_xA_x^*)^{-1}b_i, \qquad A_x = d\tilde F_x, \qquad \tilde F = c_y \circ f \circ r,$$
where $r$ is the nearest-point retraction onto $M$ and $c_y$ the chart of $S^p$ at $y$. It satisfies $A_xv_i(x) = b_i$ ⟦Chapter7/Pontryagin · pontryagin⟧ ⟦Chapter7/Pontryagin · At_pontV⟧. The basis need not be positive: orientations of bases enter with Lemma 1, and positivity with Theorem A.

*The idea.* Milnor takes the unique normal vector $v$ with $df_x(v) = b_i$ and leaves its smoothness to the reader; the formal text writes it as a formula. Extended off $M$ through $r$, the ambient derivative $A_x$ kills the normal space of $M$ and the tangent space of $N$. So the minimal-norm solution of $A_xv = b_i$ is tangent to $M$ and normal to $N$, and it is smooth because each ingredient is.

*The proof as formalized.*

1. *Linear algebra.* For a surjective linear map $A : E \to F$ of finite-dimensional inner product spaces, $AA^*$ is invertible. If $AA^*c = 0$, then $|A^*c|^2 = \langle c, AA^*c\rangle = 0$, and writing $c = Av$ gives $|Av|^2 = \langle v, A^*c\rangle = 0$. So $AA^*$ is injective, hence bijective ⟦Chapter7/Pontryagin · isUnit_comp_adjoint⟧. Put $A^+ = A^*(AA^*)^{-1}$ ⟦Chapter7/Pontryagin · pinv⟧. Then $AA^+c = c$ ⟦Chapter7/Pontryagin · comp_pinv⟧. Also $\langle A^+c, v\rangle = \langle (AA^*)^{-1}c, Av\rangle = 0$ whenever $Av = 0$ ⟦Chapter7/Pontryagin · inner_pinv_eq_zero⟧.
2. *The extension.* Chapter 6 supplies $\varepsilon_M > 0$ and a map $r : \mathbb R^{K+1} \to M$. It is the identity on $M$ and smooth on $N_\varepsilon = \{\operatorname{dist}(\cdot, M) < \varepsilon_M\}$. It is also constant along short normal segments: if $x \in M$ and $v \perp T_xM$, then $r(x+sv) = x$ for $s$ near $0$ ⟦Chapter6/Tubular4 · tubr_spec⟧. Put $\tilde F(z) = c_y(f(r(z)))$. It is smooth on the open set $\tilde W$ of $z \in N_\varepsilon$ with $f(r(z))$ in the domain of $c_y$, and equals $c_y \circ f$ on $M$ ⟦Chapter7/Pontryagin · Ft⟧ ⟦Chapter7/Pontryagin · contDiffOn_Ft⟧ ⟦Chapter7/Pontryagin · Ft_of_mem⟧. Let $A_z$ be its derivative at $z$ ⟦Chapter7/Pontryagin · At⟧.
3. *Four facts at $x \in N = f^{-1}(y)$.*
   - (a) The chain rule along $M$ gives $A_x \circ d(\iota)_x = d(c_y)_{f(x)} \circ df_x$, where $\iota$ is the inclusion ⟦Chapter7/Pontryagin · At_comp_mfd_val⟧.
   - (b) Hence $A_x$ is surjective, since $df_x$ is and the chart derivative is invertible ⟦Chapter7/Pontryagin · surjective_At⟧.
   - (c) $A_x$ vanishes on $(T_xM)^\perp$, because $s \mapsto \tilde F(x+sv)$ is constant near $0$ ⟦Chapter7/Pontryagin · At_normal_eq_zero⟧.
   - (d) $A_x$ vanishes on $T_xN$, because $\tilde F$ is constant on $N$ ⟦Chapter7/Pontryagin · At_tangentN_eq_zero⟧.
4. *The framing* $v_i(x) = A_x^+b_i$ ⟦Chapter7/Pontryagin · pontV⟧. Step 1 gives $A_xv_i = b_i$, so the $v_i$ are independent because their images are ⟦Chapter7/Pontryagin · pontV_indep⟧. Orthogonality to $T_xN$ follows from (d) ⟦Chapter7/Pontryagin · pontV_normal⟧. For tangency, $v_i \in (\ker A_x)^\perp \subseteq ((T_xM)^\perp)^\perp = T_xM$ by (c) ⟦Chapter7/Pontryagin · pontV_tangent⟧.
5. *Smoothness.* $z \mapsto A_z$ is smooth on $\tilde W$. Adjoints are a continuous linear operation, and inversion is smooth near an invertible operator. So $z \mapsto A_z^+b_i$ is smooth near $N$, and $v_i$ is its composite with the inclusion $N \to \mathbb R^{K+1}$ ⟦Chapter7/Pontryagin · contMDiff_pontV⟧.
6. *The set.* $N$ is a slice submanifold of codimension $p$ by the regular value theorem, and compact as a closed subset of $M$ ⟦Chapter7/Pontryagin · isSliceSubmanifold_level⟧ ⟦Chapter7/Pontryagin · isCompact_level⟧.

### V7.2 The cobordism $F^{-1}(z)$: the construction inside Lemmas 2 and 3

**Theorem.** Assume the standing hypotheses and let $0 < \varepsilon < \tfrac12$. Let $F : M \times \mathbb R \to S^p$ be smooth with regular value $z$. Let $f, g : M \to S^p$ be smooth, each with regular value $z$, such that $F(x,t) = f(x)$ for $t \le \varepsilon$ and $F(x,t) = g(x)$ for $t \ge 1-\varepsilon$. Let $b_1, \dots, b_p \in \mathbb R^p$ be linearly independent. Then $(f^{-1}(z), f^*b)$ and $(g^{-1}(z), g^*b)$ are framed cobordant ⟦Chapter7/Cobordism · framedCobordant_of_homotopy⟧.

*The idea.* Frame $S = F^{-1}(z)$ by the construction of V7.1 one dimension up. Near the ends $F$ ignores $t$, so there the framing is the Pontryagin framing of $f$ or $g$ with time component $0$.

*The adjoint on $\mathbb R^{K+1} \times \mathbb R$.* For $A : \mathbb R^{K+1} \times \mathbb R \to \mathbb R^p$ with partial maps $A_1 = A(\cdot, 0)$ and $A_2 = A(0, \cdot)$, set $A^\dagger c = (A_1^*c, A_2^*c)$. Then $\langle A^\dagger c, v\rangle = \langle c, Av\rangle$ for the product inner product ⟦Chapter7/AdjXR · adjXR⟧ ⟦Chapter7/AdjXR · ipXR_adjXR⟧. The pseudo-inverse $A^\dagger(AA^\dagger)^{-1}$ has the properties of step 1 of V7.1 ⟦Chapter7/AdjXR · isUnit_comp_adjXR⟧ ⟦Chapter7/AdjXR · comp_pinvXR⟧ ⟦Chapter7/AdjXR · ipXR_pinvXR_eq_zero⟧. It has one more, which makes the ends work: if $A = B \circ \mathrm{pr}_1$ ignores time, it sends $c$ to $(B^+c, 0)$ ⟦Chapter7/AdjXR · pinvXR_comp_fst⟧.

*The proof as formalized.*

1. $S = F^{-1}(z)$ is a slice submanifold of $M \times \mathbb R$ modelled on $\mathbb R^{n+1}$, by the regular value theorem and $(n+1) + p = m + 1$ ⟦Chapter7/Cobordism · levelDimXR⟧ ⟦Chapter7/Cobordism · isSliceSubmanifold_levelXR⟧.
2. Extend by $\hat F(z', t) = c_z(F(r(z'), t))$, smooth where $z' \in N_\varepsilon$ and $F(r(z'),t)$ lies in the domain of $c_z$. Let $\hat A_q : \mathbb R^{K+1} \times \mathbb R \to \mathbb R^p$ be its derivative ⟦Chapter7/Cobordism · Fh⟧ ⟦Chapter7/Cobordism · Ah⟧. Facts (a)–(c) of V7.1 carry over: the chain rule along $M \times \mathbb R$, surjectivity on $S$, and $\hat A_q(v, 0) = 0$ for $v \perp T_xM$ ⟦Chapter7/Cobordism · Ah_comp_mfd_embXR⟧ ⟦Chapter7/Cobordism · surjective_Ah⟧ ⟦Chapter7/Cobordism · Ah_normal_eq_zero⟧. So does (d): $\hat A_q$ vanishes on $T_qS$ ⟦Chapter7/Cobordism · Ah_tangentS_eq_zero⟧.
3. The framing is $u_i(q) = \hat A_q^\dagger(\hat A_q\hat A_q^\dagger)^{-1}b_i$ ⟦Chapter7/Cobordism · uh⟧. It is normal to $T_qS$, independent and smooth, as in V7.1 ⟦Chapter7/Cobordism · uh_normal⟧ ⟦Chapter7/Cobordism · uh_indep⟧ ⟦Chapter7/Cobordism · contMDiff_uh⟧. Its $\mathbb R^{K+1}$-component lies in $T_xM$, since for $v \perp T_xM$ it pairs with $v$ to $\langle u_i, (v,0)\rangle = 0$ ⟦Chapter7/Cobordism · uh_tangent⟧.
4. *The ends.* If $F(x,t) = f(x)$ for $t$ in an open set $O$, then on $\mathbb R^{K+1} \times O$ the extension $\hat F$ equals $\tilde F_f \circ \mathrm{pr}_1$, with $\tilde F_f$ the extension of $f$ for the same chart. Hence $\hat A_{(x,t)} = A_x \circ \mathrm{pr}_1$ when $t \in O$ and $f(x) = z$ ⟦Chapter7/Cobordism · Ah_eq_At_of_const⟧. The extra property of the pseudo-inverse then gives $u_i(x,t) = (v_i(x), 0)$, with $v$ the Pontryagin framing of $f$ ⟦Chapter7/Cobordism · uh_end⟧. Take $O = (-\infty, \varepsilon)$ and $O = (1-\varepsilon, \infty)$.
5. For $t < \varepsilon$, $F(x,t) = z$ if and only if $f(x) = z$, and likewise for $g$ at the top. $S \cap (M \times [0,1])$ is closed in the compact $M \times [0,1]$ ⟦Chapter7/Cobordism · framedCobordant_of_homotopy⟧.

*Where the formal proof departs from Milnor.* This step is the heart of Milnor's proofs of Lemmas 2 and 3. His Lemma 3 starts from a value $y$ regular for $f$ and $g$ and moves, by Lemma 2, to a nearby regular value $z$ of the homotopy. Here $z$ is given; the moving happens in V7.5 and V7.6, and Lemma 3 is the case $y = z$ of V7.6. Regularity for $f$ and $g$ is assumed because the Pontryagin manifolds need it, though it follows from regularity for $F$.

#### Making a homotopy constant near its ends

**Proposition.** Let $M \subseteq \mathbb R^k$ be a slice submanifold modelled on $\mathbb R^m$; compactness is not needed. Let $F : M \times \mathbb R \to S^p$ be smooth, let $z$ be a regular value of $F$, of $F(\cdot,0)$ and of $F(\cdot,1)$, and let $0 < \varepsilon < \tfrac12$. Then there is a smooth $F' : M \times \mathbb R \to S^p$ such that:

- $F'(x,t) = F(x,0)$ for $t \le \varepsilon$;
- $F'(x,t) = F(x,1)$ for $t \ge 1-\varepsilon$;
- $z$ is a regular value of $F'$ ⟦Chapter7/Reparam · exists_reparam⟧.

*The proof as formalized.* Put $F'(x,t) = F(x, \rho(t))$ with $\rho(t) = \sigma\big((t-\varepsilon)/(1-2\varepsilon)\big)$, where $\sigma(s) = \psi(s)/(\psi(s) + \psi(1-s))$ is Mathlib's transition function and $\psi(s) = e^{-1/s}$ for $s > 0$, $\psi(s) = 0$ otherwise. From $\psi'(s) = s^{-2}\psi(s)$ the formal text computes
$$\sigma'(s) = \frac{\psi'(s)\psi(1-s) + \psi(s)\psi'(1-s)}{(\psi(s)+\psi(1-s))^2},$$
which is positive on $(0,1)$ ⟦Chapter7/Transition · hasDerivAt_smoothTransition⟧ ⟦Chapter7/Transition · deriv_smoothTransition_pos⟧. So $\rho$ is $0$ for $t \le \varepsilon$, $1$ for $t \ge 1-\varepsilon$, takes values in $[0,1]$, and has $\rho' > 0$ on $(\varepsilon, 1-\varepsilon)$ ⟦Chapter7/Transition · exists_timeTransition⟧. At a point with $F'(x,t) = z$,
$$dF'_{(x,t)}(a,s) = dF_{(x,\rho(t))}(a, \rho'(t)s).$$
If $\rho(t) \in \{0,1\}$, the vectors $(a,0)$ already suffice, because the $x$-derivative is that of $F(\cdot,0)$ or $F(\cdot,1)$. Otherwise $\varepsilon < t < 1-\varepsilon$ and $\rho'(t) > 0$, so $(a,s) \mapsto (a, \rho'(t)s)$ is bijective and the surjectivity of $dF$ transfers ⟦Chapter7/Reparam · exists_reparam⟧.

*Why these hypotheses.* The lemma keeps a regular value chosen *before* the time change. A transition function merely constant near the ends could have $\rho' = 0$ at an interior point where only the time direction made $dF$ onto; hence $\rho' > 0$. For $t \le \varepsilon$ and $t \ge 1-\varepsilon$, where $\rho' = 0$, the time direction is lost, so the end maps must be regular themselves. Milnor reparametrizes first and then chooses the regular value, which makes regularity at the ends automatic; the formal proof of V7.6 takes the other order.

### V7.3 Lemma 1: the basis does not matter

**Theorem (Lemma 1, general form).** Assume the standing hypotheses. Let $f, g : M \to S^p$ be smooth, with $y$ a regular value of $f$ and $z$ a regular value of $g$. Let $b$ and $c$ be linearly independent $p$-tuples in $\mathbb R^p$, and let $A$ be a $p \times p$ matrix with $\det A > 0$. Suppose $g^{-1}(z) = f^{-1}(y)$ and $g^*c = f^*(A\cdot b)$ at every point of this set, where $(A \cdot b)_j = \sum_i A_{ij}b_i$. Then $(g^{-1}(z), g^*c)$ and $(f^{-1}(y), f^*b)$ are framed cobordant ⟦Chapter7/Lemma1 · framedCobordant_of_det_pos'⟧.

With $g = f$, $z = y$ and $c = b' = A\cdot b$ it gives $(f^{-1}(y), f^*b') \sim (f^{-1}(y), f^*b)$. Bases $b, b'$ with the same orientation are related by such an $A$, and this is Milnor's Lemma 1 ⟦Chapter7/Lemma1 · framedCobordant_of_det_pos⟧ ⟦Chapter7/Lemma1 · framedCobordant_of_orientation_eq⟧. The general form serves V7.5, where the Pontryagin manifold of $r \circ f$ at $r(y)$, for a rotation $r$, has the same underlying set as that of $f$ at $y$ and a framing of the form $f^*(\cdot)$.

*The idea.* Join $A \cdot b$ to $b$ by a smooth path of bases $B(t)$, and frame $f^{-1}(y) \times \mathbb R$ by $f^*B(t)$ at time $t$. Milnor quotes the connectedness of $GL^+$; the formal text builds the path.

#### Smooth paths in $GL^+(p, \mathbb R)$

**Theorem.** Every real $p \times p$ matrix $A$ with $\det A > 0$ is joined to the identity by a map $G : \mathbb R \to M_p(\mathbb R)$ with smooth entries, $G(0) = A$, $G(1) = I$, and $\det G(t) > 0$ for $0 \le t \le 1$ ⟦Chapter7/GLplus · exists_glPath⟧.

*The proof as formalized.*

1. Mathlib's Gaussian elimination gives $A = L\,D\,L'$, with $L, L'$ products of transvections $I + cE_{ij}$ ($i \ne j$) and $D = \operatorname{diag}(d_1, \dots, d_p)$. Each transvection is joined to $I$ by $I + tcE_{ij}$, of determinant $1$. Multiplying along the lists joins $L$ and $L'$ to $I$ within determinant $1$ ⟦Chapter7/GLplus · transPath⟧ ⟦Chapter7/GLplus · listPath⟧ ⟦Chapter7/GLplus · det_listPath⟧.
2. Since $\det D = \det A > 0$, the $d_i$ are nonzero and evenly many are negative ⟦Chapter7/GLplus · even_card_neg⟧. The negative indices are paired off ⟦Chapter7/GLplus · exists_matching⟧.
3. The rotation $R_{ij}(\theta) = I + (\cos\theta - 1)(E_{ii} + E_{jj}) + \sin\theta\,(E_{ji} - E_{ij})$ ⟦Chapter7/GLplus · rot⟧ is $I + P(CP^{T})$, with $P$ the $p \times 2$ matrix with columns $e_i, e_j$ and $C = \begin{pmatrix}\cos\theta - 1 & -\sin\theta\\ \sin\theta & \cos\theta - 1\end{pmatrix}$. As $P^TP = I_2$, $\det(I + XY) = \det(I + YX)$ gives $\det R_{ij}(\theta) = \det(I_2 + C) = \cos^2\theta + \sin^2\theta = 1$ ⟦Chapter7/GLplus · det_rot⟧. And $R_{ij}(\pi)$ is diagonal with $-1$ exactly at $i$ and $j$ ⟦Chapter7/GLplus · rot_pi⟧.
4. The diagonal path is $\prod_{\text{pairs}} R_{ij}(\pi t) \cdot \operatorname{diag}\big((1-t)d_i + t\operatorname{sgn} d_i\big)$ ⟦Chapter7/GLplus · diagPath⟧. It is $D$ at $t = 0$, and $I$ at $t = 1$ because each negative index lies in exactly one pair ⟦Chapter7/GLplus · diagPath_one⟧. Its determinant is $\prod_i\big((1-t)d_i + t\operatorname{sgn}d_i\big)$, positive for $0 \le t \le 1$ since each factor keeps the sign of $d_i$ ⟦Chapter7/GLplus · det_diagPath⟧ ⟦Chapter7/GLplus · prod_diagScale_pos⟧.
5. $G(t)$ is the $L$-path at $1-t$, times the diagonal path at $t$, times the $L'$-path at $1-t$ ⟦Chapter7/GLplus · exists_glPath⟧.

The determinant is known to be positive only on $[0,1]$, so the path of bases composes $G$ with the transition function $\rho$, whose values lie in $[0,1]$. For $b$ independent, $\det A > 0$ and $0 < \varepsilon < \tfrac12$, the map $B(t) = G(\rho(t)) \cdot b$ is smooth and independent for every $t$. It equals $A\cdot b$ for $t \le \varepsilon$ and $b$ for $t \ge 1-\varepsilon$ ⟦Chapter7/BasisPath · exists_basisPath⟧ ⟦Chapter7/BasisPath · linearIndependent_mulTuple⟧. Bases with the same orientation differ by a change-of-basis matrix of positive determinant ⟦Chapter7/BasisPath · exists_det_pos_of_orientation_eq⟧.

#### The cobordism

*The proof as formalized.*

1. The cobordism is $f^{-1}(y) \times \mathbb R$, the level set of $(x,t) \mapsto f(x)$, for which $y$ is again regular ⟦Chapter7/Lemma1 · isRegularValue_comp_fst⟧. Take $\varepsilon = \tfrac14$.
2. The framing is $u_i(x,t) = \hat A^\dagger(\hat A\hat A^\dagger)^{-1}B(t)_i$, with $\hat A$ the derivative of the extension of $(x,t) \mapsto f(x)$ ⟦Chapter7/Lemma1 · uht⟧. Pointwise it is the framing of V7.2 with the basis frozen at $B(t)$, so tangency, normality and independence are quoted. Only smoothness uses the variation of $B$ ⟦Chapter7/Lemma1 · contMDiff_uht⟧.
3. *The ends.* For $t < \tfrac14$ the end lemma of V7.2 gives $u_i = (f^*(A \cdot b)_i, 0) = (g^*c_i, 0)$, and $S$ matches $g^{-1}(z) = f^{-1}(y)$. For $t > \tfrac34$ it gives $u_i = (f^*b_i, 0)$ ⟦Chapter7/Lemma1 · framedCobordant_of_det_pos'⟧.

### V7.4 Framed cobordism is symmetric and transitive

**Theorem.** Let $M \subseteq \mathbb R^{K+1}$ be a slice submanifold modelled on $\mathbb R^m$; compactness is not needed. Let $F_0, F_1, F_2$ be framed submanifolds of $M$ of dimension $n$ and codimension $p$. If $F_0$ is framed cobordant to $F_1$, then $F_1$ is framed cobordant to $F_0$. If moreover $F_1$ is framed cobordant to $F_2$, then $F_0$ is framed cobordant to $F_2$ ⟦Chapter7/Equiv · FramedCobordant.symm⟧ ⟦Chapter7/Equiv · FramedCobordant.trans⟧.

Reflexivity is not proved here, and this part does not need it. In general it comes only in Chapter 8, by a detour: Theorem C writes $F$ as a Pontryagin manifold, and V7.2 applies to the constant homotopy ⟦Chapter8/FramedOps · framedCobordant_refl⟧. For framed points the same detour is taken later in Chapter 7 ⟦Chapter7/Reach · FramedCobordant.refl'⟧.

*The idea.* Symmetry reverses time. Transitivity shifts the second cobordism to $[1,2]$, glues along the common product strip at $t = 1$, and compresses $[0,2]$ to $[0,1]$. Milnor asserts all this without proof. The formal work is to show each operation yields a slice submanifold and a framing.

#### Transport and gluing

1. *Preimages.* The preimage of a slice submanifold under an ambient diffeomorphism $\tau$ is a slice submanifold: compose its slice charts with $\tau$ ⟦Chapter7/Transport · isSliceSubmanifold_preimage_diffeomorph⟧. The time changes $\tau(x,t) = (x, at+c)$, $a \neq 0$, are diffeomorphisms of $M \times \mathbb R$ ⟦Chapter7/Transport · affineXR⟧ ⟦Chapter7/Transport · isSliceSubmanifold_preimage_affine⟧.
2. *Tangent spaces.* With $D_a(v,s) = (v, as)$, $T_{\tau(q)}S = D_a\big(T_q\,\tau^{-1}(S)\big)$ ⟦Chapter7/Transport · dtXR⟧ ⟦Chapter7/Transport · tangentS_affine⟧. This follows from the chain rule, since the derivative of $\tau^{-1}(S) \to S$ is surjective, the map having a smooth inverse ⟦Chapter7/Transport · surjective_mfd_ιaff⟧.
3. *Locality.* If $S \cap U = T \cap U$ with $U$ open, then $S$ and $T$ have the same tangent spaces on $U$ ⟦Chapter7/Transport · tangentS_eq_of_inter_eq⟧.
4. *Gluing.* If $S_1, S_2$ agree on the strip $c' < t < c$, then $(S_1 \cap \{t < c\}) \cup (S_2 \cap \{t > c'\})$ is a slice submanifold. Slice charts of $S_1$ restrict to $\{t < c\}$, and those of $S_2$ to $\{t > c'\}$ ⟦Chapter7/Transport · glueS⟧ ⟦Chapter7/Transport · isSliceSubmanifold_glueS⟧.

A framing without end conditions ⟦Chapter7/Equiv · Framing⟧ is transported by $u'_i(q) = D_a u_i(\tau(q))$ ⟦Chapter7/Equiv · Framing.transport⟧. Tangent vectors come back from $\tau(q)$ to $q$ by $D_a^{-1}$; normal vectors come back by the transpose of $D_a$, and $D_a$ is its own transpose, $\langle D_au, w\rangle = \langle u, D_aw\rangle$ ⟦Chapter7/Equiv · ipXR_dtXR⟧. So if $u \perp T_{\tau(q)}S$ and $w \in T_q\tau^{-1}(S)$, then $D_aw \in T_{\tau(q)}S$ and $\langle D_au, w\rangle = \langle u, D_aw\rangle = 0$. $D_a$ is injective and fixes the $\mathbb R^{K+1}$-component, so independence and tangency survive. Framings agreeing on the strip glue with a cut at $c_0 \in (c', c)$: $u_1$ below $c_0$, $u_2$ from $c_0$ on ⟦Chapter7/Equiv · glueU⟧. The result is $u_1$ on the open set $\{t < c_0\}$ and $u_2$ on the open set $\{t > c'\}$, hence smooth, and it is normal by locality ⟦Chapter7/Equiv · Framing.glue⟧.

#### Symmetry and transitivity

*Symmetry.* Take $\tau^{-1}(S)$ for $\tau(x,t) = (x, 1-t)$, with the same $\varepsilon$. Time components of the framing change sign, which leaves the end framings $(v_i, 0)$ alone. The middle piece is the image of the old one under $\tau$ ⟦Chapter7/Equiv · FramedCobordant.symm⟧.

*Transitivity.* Let $X$ run from $F_0$ to $F_1$ with margin $\varepsilon_X$, and $Y$ from $F_1$ to $F_2$ with $\varepsilon_Y$.

1. Shift $Y$ to $[1,2]$: take its preimage under $(x,t) \mapsto (x, t-1)$.
2. On $1 - \varepsilon_X < t < 1 + \varepsilon_Y$, both $X$ and the shifted $Y$ are $N_1 \times$ strip, framed by $(v^1_i, 0)$. Glue with $c_0 = 1$.
3. Compress: take the preimage under $(x,t) \mapsto (x, 2t)$. This doubles the time components of the framing; the new margin is $\varepsilon = \min(\varepsilon_X, \varepsilon_Y)/2$.
4. The glued piece over $[0,2]$ is $X \cap (M \times [0,1])$ together with the shifted $Y \cap (M \times [0,1])$, hence compact ⟦Chapter7/Equiv · FramedCobordant.trans⟧.

### V7.5 Theorem A: neither the regular value nor the positive basis matters

**Theorem (Theorem A).** Assume the standing hypotheses and $p \ge 1$. Let $f : M \to S^p$ be smooth and let $y, z$ be regular values of $f$. Let $e_0$ be a positive basis at $y$ and $e$ a positive basis at $z$. Then $(f^{-1}(y), f^*e_0)$ and $(f^{-1}(z), f^*e)$ are framed cobordant ⟦Chapter7/Lemma2 · framedCobordant_of_regularValues⟧.

Milnor's Lemma 2 is the local case, $z$ near $y$, proved by rotating the sphere. His proof of Theorem A takes one rotation $r$ with $r(y) = z$ and applies Lemma 3 to $f \simeq r \circ f$; Lemma 3 in turn moves regular values by Lemma 2. The formal proof builds four tools, proves Lemma 2 along an arc, and runs the rest as one explicit chain.

#### The regular values form an open set

**Proposition.** Let $M$ be compact and nonempty, as in the standing hypotheses, and let $f : M \to S^p$ be smooth. Then the regular points of $f$ form an open subset of $M$, and the regular values form an open subset of $S^p$ ⟦Chapter7/RegOpen · isOpen_regularPoints_sph⟧ ⟦Chapter7/RegOpen · isOpen_regularValues_sph⟧.

*The idea.* $df_x$ is read in the chart at $f(x)$, which moves with $x$, so there is no continuous family to perturb. Fix instead $y = f(x_0)$ and the extension $\tilde F$ of V7.1 for the chart $c_y$. Then $x \mapsto A_x$ is continuous.

*The proof as formalized.*

1. For $x \in M$ with $f(x)$ in the domain of $c_y$, $df_x$ is onto if and only if $A_x$ is ⟦Chapter7/RegOpen · surjective_At_of_isRegularPoint⟧. For the converse, write $v = t + \nu$ with $t \in T_xM$ and $\nu \perp T_xM$; then $A_x\nu = 0$, and the chart derivative is injective ⟦Chapter7/RegOpen · isRegularPoint_of_surjective_At⟧.
2. $A$ is onto if and only if $AA^*$ is invertible, and invertible operators form an open set ⟦Chapter7/RegOpen · surjective_iff_isUnit_comp_adjoint⟧ ⟦Chapter7/RegOpen · isOpen_surjective⟧.
3. So regular points form an open set. Critical points are closed in the compact $M$, hence compact, and so the critical values are compact and closed.

#### Planar rotations of the sphere

For orthonormal $u, v \in \mathbb R^{p+1}$ let
$$R_\theta x = x + (\cos\theta - 1)\big(\langle u,x\rangle u + \langle v,x\rangle v\big) + \sin\theta\big(\langle u,x\rangle v - \langle v,x\rangle u\big)$$
⟦Chapter7/Rotation · rotCLM⟧. These form a one-parameter group of isometries ⟦Chapter7/Rotation · rotCLM_add⟧ ⟦Chapter7/Rotation · norm_rotCLM⟧. Each has positive determinant, by continuity: $\theta \mapsto \det R_\theta$ never vanishes, since $\det R_{-\theta}\det R_\theta = 1$, and equals $1$ at $0$ ⟦Chapter7/Rotation · det_rotCLM_pos⟧. The induced map $r_\theta$ of $S^p$ is defined by normalizing, so it needs no hypotheses. For orthonormal $u, v$ it is the restriction of $R_\theta$ ⟦Chapter7/Rotation · rotS⟧ ⟦Chapter7/Rotation · rotS_val⟧. The family $(x,t) \mapsto r_{\rho(t)}(x)$ is smooth for smooth $\rho$ ⟦Chapter7/Rotation · contMDiff_rotS_family⟧. Each $r_\theta$ has sign $+1$ everywhere, by Chapter 6's formula $\operatorname{sgn}\det$ for normalized linear maps ⟦Chapter7/Rotation · signAt_rotS⟧ ⟦Chapter6/Radial · signAt_nv0_linear⟧.

**Lemma (rotation paths).** Let $p \ge 1$ and $y, y' \in S^p$. There are orthonormal $u, v$ and $\theta_0 \in [0,\pi]$ with $R_{\theta_0}y = y'$ and $|R_{t\theta_0}y - y| \le |y' - y|$ for $0 \le t \le 1$ ⟦Chapter7/Rotation · exists_rotation_path⟧.

*The proof as formalized.* Take $u = y$, $a = \langle y, y'\rangle$ and $w = y' - ay$, so that $w \perp y$ and $|w|^2 = 1 - a^2$. Let $v = w/|w|$ if $w \ne 0$, and otherwise any unit vector orthogonal to $y$, which exists because $p \ge 1$ ⟦Chapter7/Rotation · exists_unit_orthogonal⟧. With $\theta_0 = \arccos a$, $R_{\theta_0}y = ay + |w|v = y'$. The chord $|R_\theta y - y|^2 = 2 - 2\cos\theta$ increases on $[0,\pi]$ ⟦Chapter7/Rotation · dist_rotCLM_u_sq⟧ ⟦Chapter7/Rotation · dist_rotCLM_u⟧.

#### Composing with a map of the sphere

**Proposition.** Assume the standing hypotheses. Let $f$ be smooth with regular value $y$. Let $r : S^p \to S^p$ be smooth with $dr_y$ bijective and of sign $+1$, and such that $r(f(x)) = r(y)$ implies $f(x) = y$. Let $e$ be positive at $r(y)$ and $e_0$ positive at $y$. Then $r(y)$ is a regular value of $r \circ f$, and $((r\circ f)^{-1}(r(y)), (r \circ f)^*e)$ is framed cobordant to $(f^{-1}(y), f^*e_0)$ ⟦Chapter7/Compose · isRegularValue_comp⟧ ⟦Chapter7/Compose · framedCobordant_comp⟧.

$r$ need not be a diffeomorphism; only conditions at $y$ and on the fibre are asked.

*The proof as formalized.*

1. Near $x \in f^{-1}(y)$ the extension of $r \circ f$ is $(c_{r(y)} \circ r \circ c_y^{-1}) \circ \tilde F_f$. Hence $A^{r\circ f}_x = dr_y \circ A^f_x$, with $dr_y$ read in charts ⟦Chapter7/Compose · hasFDerivAt_written⟧ ⟦Chapter7/Compose · At_comp⟧.
2. For surjective $A$ and bijective $D$, $(DA)^+c = A^+(D^{-1}c)$. Indeed $A^+c$ is the unique vector in the range of $A^*$ mapped to $c$, and $(DA)^*$ has the range of $A^*$ ⟦Chapter7/Compose · pinv_unique⟧ ⟦Chapter7/Compose · pinv_comp⟧. So $(r \circ f)^*e = f^*(dr_y^{-1}e)$ ⟦Chapter7/Compose · pontV_comp⟧.
3. Sign $+1$ means $dr_y$ carries the orientation at $y$ to that at $r(y)$ ⟦Chapter7/Compose · orientation_map_of_orSign_eq_one⟧. So $dr_y^{-1}e = A \cdot e_0$ with $\det A > 0$, and the general Lemma 1 applies: the level sets coincide by the fibre hypothesis, the framings by step 2 ⟦Chapter7/Compose · framedCobordant_comp⟧.

#### Rotating the target

**Proposition.** Let $M \subseteq \mathbb R^{K+1}$ be a slice submanifold modelled on $\mathbb R^m$. Let $f : M \to S^p$ be smooth, let $u, v$ be orthonormal, let $\theta_0 \in \mathbb R$ and $0 < \varepsilon < \tfrac12$. Then there is a smooth $F : M \times \mathbb R \to S^p$ such that:

- $F(x,t) = f(x)$ for $t \le \varepsilon$;
- $F(x,t) = r_{\theta_0}(f(x))$ for $t \ge 1-\varepsilon$;
- for every $y$, if $\theta_0 \ge 0$ and every $r_\tau(y)$ with $0 \le \tau \le \theta_0$ is a regular value of $f$, then $r_{\theta_0}(y)$ is a regular value of $F$ ⟦Chapter7/RotHomotopy · exists_rotHomotopy⟧.

*The proof as formalized.* Put $F(x,t) = r_{\theta_0\rho(t)}(f(x))$. If $F(x,t) = r_{\theta_0}(y)$, then $f(x) = r_{\theta_0(1-\rho(t))}(y)$ lies on the arc ⟦Chapter7/RotHomotopy · rotS_add⟧. So $df_x$ is onto, and so is $dr \circ df_x$, which is $dF$ on vectors $(a,0)$. Only space directions are used; the monotonicity of $\rho$ plays no role.

#### Lemma 2 along an arc, then Theorem A

**Proposition (Lemma 2).** Assume the standing hypotheses. Let $f$ be smooth, $u, v$ orthonormal and $\theta_0 \ge 0$. Suppose $y$, every $r_\tau(y)$ with $\tau \in [0,\theta_0]$, and $r_{\theta_0}(y)$ are regular values of $f$. Let $e$ be positive at $r_{\theta_0}(y)$ and $e_0$ positive at $y$. Then $(f^{-1}(r_{\theta_0}(y)), f^*e)$ and $(f^{-1}(y), f^*e_0)$ are framed cobordant ⟦Chapter7/Lemma2 · framedCobordant_arc⟧.

The proof is Milnor's. Take the rotation homotopy with $\varepsilon = \tfrac14$. V7.2 at $z = r_{\theta_0}(y)$ joins $f^{-1}(z)$ to $(r_{\theta_0} \circ f)^{-1}(z)$, and the composition rule joins that to $f^{-1}(y)$.

*Proof of Theorem A as formalized.*

1. The regular values of $f$ contain balls of radius $\delta$ around $y$ and $z$ ⟦Chapter7/RegOpen · isOpen_regularValues_sph⟧. Take a rotation $r = r_{\theta_0}$ with $r(y) = z$ and the rotation homotopy $F$ from $f$ to $r \circ f$; its regularity clause is not used.
2. By Brown's theorem the regular values of $F$, $f$ and $r \circ f$ are dense, and the last two sets are open ⟦Chapter2/Brown · dense_regularValues⟧. So their intersection is dense and contains some $z'$ with $|z' - z| < \delta$.
3. Put $y' = r^{-1}(z')$. Then $|y' - y| = |z' - z| < \delta$, so $y'$ is regular ⟦Chapter7/RotHomotopy · dist_rotS⟧. Pick positive bases $e_1$ at $y'$ and $e_2$ at $z'$ ⟦Chapter7/Lemma2 · exists_posBasis⟧.
4. Chain four framed cobordisms:
   - $f^{-1}(y) \sim f^{-1}(y')$, by Lemma 2 along a rotation path that stays in the ball ⟦Chapter7/Lemma2 · arc_bound⟧;
   - $f^{-1}(y') \sim (r \circ f)^{-1}(z')$, by the composition rule;
   - $(r \circ f)^{-1}(z') \sim f^{-1}(z')$, by V7.2 for $F$;
   - $f^{-1}(z') \sim f^{-1}(z)$, by Lemma 2 from $z$ to $z'$.

   Symmetry and transitivity combine them. A bookkeeping lemma rewrites Pontryagin manifolds along equalities such as $r(y') = z'$ ⟦Chapter7/Lemma2 · pontryagin_congr⟧.

Unlike the book, the chain applies Lemma 2 only to $f$: it moves from $y$ to $y' = r^{-1}(z')$ before composing with $r$, where the book, inside Lemma 3, moves along an arc for $r \circ f$.

*Where $p \ge 1$ enters.* It enters twice. Every rotation path is built from a unit vector orthogonal to its starting point; when the two ends are equal or antipodal they determine no such vector, and one exists only because $p \ge 1$ ⟦Chapter7/Rotation · exists_unit_orthogonal⟧. And positive bases must be found at $y'$ and $z'$ ⟦Chapter7/Lemma2 · exists_posBasis⟧. The hypothesis serves the proof rather than the statement. For $p = 0$ the outward vectors at the two points of $S^0$ are opposite ⟦Chapter5/HairyBall · outward_neg⟧, so the sphere's orientation differs at the two points and the empty basis of $\mathbb R^0$ is positive at exactly one of them. Positive bases at $y$ and $z$ then force $y = z$, and the claim becomes that a Pontryagin manifold is framed cobordant to itself, which V7.2 gives for the constant homotopy ⟦Chapter7/Cobordism · framedCobordant_of_homotopy⟧. This is an observation about the definitions, not a formal theorem.

### V7.6 Theorem B, first half: homotopic maps have cobordant Pontryagin manifolds

**Theorem.** Assume the standing hypotheses and $p \ge 1$. Let $F : M \times \mathbb R \to S^p$ be smooth, and write $f = F(\cdot,0)$, $g = F(\cdot,1)$. The statement also assumes $f$ and $g$ smooth, which already follows. Let $y$ be a regular value of $f$ and $z$ one of $g$, with $e_0$ positive at $y$ and $e$ positive at $z$. Then $(f^{-1}(y), f^*e_0)$ and $(g^{-1}(z), g^*e)$ are framed cobordant ⟦Chapter7/ThmA · framedCobordant_of_homotopic⟧.

Milnor's Lemma 3 is the case $y = z$, $e_0 = e$.

*The proof as formalized.*

1. *A common regular value $z'$ of $F$, $f$ and $g$.* By Brown's theorem each set of regular values is dense ⟦Chapter2/Brown · dense_regularValues⟧. Those of $f$ and $g$ are open ⟦Chapter7/RegOpen · isOpen_regularValues_sph⟧. Those of $F$ need not be, as $M \times \mathbb R$ is not compact. A dense set meets a dense open set in a dense set, so the triple intersection is nonempty.
2. Reparametrize $F$ at $z'$ with $\varepsilon = \tfrac14$ ⟦Chapter7/Reparam · exists_reparam⟧, and pick a positive basis $e'$ at $z'$.
3. V7.2 gives $(f^{-1}(z'), f^*e') \sim (g^{-1}(z'), g^*e')$ ⟦Chapter7/Cobordism · framedCobordant_of_homotopy⟧.
4. Theorem A for $f$ (from $y$ to $z'$) and for $g$ (from $z'$ to $z$) completes the chain ⟦Chapter7/Lemma2 · framedCobordant_of_regularValues⟧ ⟦Chapter7/Equiv · FramedCobordant.trans⟧.

*Where the formal proof departs from Milnor.* Milnor reparametrizes first; here $z'$ is chosen for the original homotopy and kept through the reparametrization, which is why that lemma needs regular end maps and $\rho' > 0$. Openness of regular values is what makes the three dense sets meet.

### What the formalization taught us

- **Cobordisms without boundary.** Product ends are built in, and level sets, reversal and gluing need no boundary theory ⟦Chapter7/Framed · FramedCob⟧.
- **Framings as formulas.** Every framing built from a map is $A^*(AA^*)^{-1}b$ for an ambient derivative $A$, with a hand-built adjoint on $\mathbb R^{K+1} \times \mathbb R$ ⟦Chapter7/Pontryagin · pontV⟧ ⟦Chapter7/AdjXR · adjXR⟧.
- **Reparametrization.** It needs $\rho' > 0$ in the middle and regular end maps ⟦Chapter7/Reparam · exists_reparam⟧.
- **Openness, twice.** It supplies Lemma 2's arcs and makes dense sets of regular values meet; its proof uses the ambient derivative, since $df_x$ moves with its chart ⟦Chapter7/RegOpen · isOpen_regularValues_sph⟧ ⟦Chapter7/ThmA · framedCobordant_of_homotopic⟧.
- **$GL^+$ made explicit.** Transvections, rotations by $\pi$ and a scaling give a path whose determinant is known to be positive only on $[0,1]$ ⟦Chapter7/GLplus · exists_glPath⟧.
- **Self-adjoint transport.** Under a time change, framings are pulled back by $D_a$ itself, its own transpose: normal time components scale by $a$ while tangent ones scale by $1/a$ ⟦Chapter7/Equiv · Framing.transport⟧ ⟦Chapter7/Transport · tangentS_affine⟧.
- **Reflexivity absent.** In general it comes only in Chapter 8, through Theorem C ⟦Chapter8/FramedOps · framedCobordant_refl⟧.
- **Weak composition hypotheses.** Sign $+1$ at one point and a fibre condition suffice ⟦Chapter7/Compose · framedCobordant_comp⟧.
- **Hidden and redundant hypotheses.** $M$ must be nonempty, since the retraction on which every framing is built is a map into $M$ ⟦Chapter6/Tubular4 · tubr⟧. The proof of Theorem A uses $p \ge 1$, though its statement would survive without it ⟦Chapter7/Rotation · exists_unit_orthogonal⟧ ⟦Chapter7/Lemma2 · exists_posBasis⟧. Smooth end maps in V7.6, and smooth and regular end maps in V7.2, are implied by the other hypotheses ⟦Chapter7/ThmA · framedCobordant_of_homotopic⟧ ⟦Chapter7/Cobordism · framedCobordant_of_homotopy⟧.
- **Milnor rearranged.** V7.2 takes the good regular value as given; all moves between regular values happen in explicit chains ⟦Chapter7/Lemma2 · framedCobordant_of_regularValues⟧.


## Part VI. The product neighbourhood, Theorem C and the second half of Theorem B (Milnor §7)

This part runs Pontryagin's construction backwards: a framed submanifold becomes a map to the sphere (Theorem C), a framed cobordism becomes a homotopy, and with the lemmas of Part V this gives the second half of Theorem B: maps with framed cobordant Pontryagin manifolds are homotopic. Milnor's pages 46–49 rest on three constructions he sketches or takes for granted: a product neighbourhood, a map $\mathbb R^p \to S^p$ collapsing the outside of a ball, and the smoothness of maps given by a formula near $N$ and a constant elsewhere. All three are built here. The product neighbourhood theorem is proved once, for an abstract map and a compact set outside which injectivity is known, so that it also serves the non-compact cobordisms of the formal definition. Because the collapse map is fixed, Theorem C realises the framing only for a multiple $c\,b$, $c > 0$, of the chosen basis. Lemma 4 is proved by another route, with a first-order estimate in place of Milnor's second-order Taylor bound. (Letters follow Milnor: Theorem B is the homotopy classification, Theorem C the realisation, and the product neighbourhood theorem is unlettered. The file names, the project's docstrings and the verified edition use an older lettering, in which the realisation is Theorem B, the classification Theorem A and the product neighbourhood theorem Theorem C.)

The files, in logical order:

- `Chapter7/StdMap`: the standard collapse map $\pi : \mathbb R^p \to S^p$.
- `Chapter7/ProdNbhd`: local injectivity and a uniform injectivity radius for an abstract $G : N \times \mathbb R^p \to X$.
- `Chapter7/ProdNbhd2`: bijectivity of $dG$ on a tube, open image, smooth inverse.
- `Chapter7/Clamp`: a smooth radial clamp.
- `Chapter7/ProdNbhdM`: the tube map of a framed $N \subseteq M$ and its derivative along $N$.
- `Chapter7/PontFrame`: the kernel of $d\tilde F_x$ and a characterisation of the Pontryagin framing.
- `Chapter7/Collapse`: the collapse map with prescribed derivative.
- `Chapter7/ThmB`: Theorem C, every framed submanifold is a Pontryagin manifold.
- `Chapter7/Stereo`: the straight-line homotopy in stereographic coordinates.
- `Chapter7/Taylor`: a uniform first-order estimate on a tube.
- `Chapter7/Homotopy`: smooth homotopy is an equivalence relation.
- `Chapter7/TubeData`: the product neighbourhood of $(N, v)$, packaged for reuse.
- `Chapter7/Deform`: the deformation lemma.
- `Chapter7/ProdNbhdS`: the tube map of a framed cobordism $S \subseteq M \times \mathbb R$.
- `Chapter7/SamePont`: maps with the same Pontryagin manifold are homotopic (Lemma 4).
- `Chapter7/Identify`: recognising a Pontryagin manifold from its values along the framing.
- `Chapter7/CobMap`: the map of a framed cobordism.
- `Chapter7/ThmAconv`: the second half of Theorem B.

### Setting

Throughout, $M \subseteq \mathbb R^{K+1}$ is a compact, nonempty slice submanifold of dimension $m$ with its induced structure. Chapter 6 provides $\varepsilon_M > 0$ and the nearest-point retraction $r : \mathbb R^{K+1} \to M$: smooth on $U_M = \{z : \operatorname{dist}(z, M) < \varepsilon_M\}$, the identity on $M$, and constant on short normal segments, $r(x + sw) = x$ for small $s$ when $x \in M$ and $w \perp T_xM$ ⟦Chapter6/Tubular4 · tubr_spec⟧. A framed submanifold $(N, v)$ has dimension $n$ and codimension $p$ with $n + p = m$; $N$ is compact, and $v_1, \dots, v_p$ are smooth, tangent to $M$, orthogonal to $N$ and independent at each point ⟦Chapter7/Framed · FramedSub⟧. Tangent spaces are subspaces of $\mathbb R^{K+1}$, images of derivatives of inclusions ⟦Chapter7/Framed · tangentN⟧.

The Pontryagin manifold is defined through an extension (Part V). For $f : M \to S^p$ smooth, $y$ a regular value and $\varphi_y$ the chart of $S^p$ at $y$, put $\tilde F = \varphi_y \circ f \circ r$ and $A_x = d\tilde F_x$ ⟦Chapter7/Pontryagin · Ft⟧ ⟦Chapter7/Pontryagin · At⟧. For a linearly independent family $b = (b_1, \dots, b_p)$ in $\mathbb R^p$ the framing is $f^*b_i(x) = A_x^*(A_xA_x^*)^{-1}b_i$ ⟦Chapter7/Pontryagin · pontV⟧, and the Pontryagin manifold is $(f^{-1}(y), f^*b)$ ⟦Chapter7/Pontryagin · pontryagin⟧. Two framed submanifolds with the same set and the same fields are equal ⟦Chapter7/ThmB · FramedSub.ext'⟧, and every "is the Pontryagin manifold" below is such a literal equality. The north pole of $S^p \subseteq \mathbb R^{p+1}$ is the last basis vector $e_{p+1}$, the south pole is $-e_{p+1}$ ⟦Chapter7/StdMap · north⟧. A basis of $\mathbb R^p$ is *positive at $y$* if its orientation is that of $S^p$ at $y$ ⟦Chapter5/HairyBall · sphOr⟧. $B_\varepsilon$ and $\bar B_\varepsilon$ are the open and closed balls about $0$ in $\mathbb R^p$.

### V7.9, first part: the collapse map $\pi : \mathbb R^p \to S^p$

Milnor's proof of Theorem C uses a map $\mathbb R^p \to S^p$ sending the outside of the unit ball to a point and the open ball diffeomorphically onto the rest of the sphere. The formal proof needs less: one explicit map, never required to be injective.

**Proposition (the standard map).** Let $\tau$ be Mathlib's smooth transition function ($0$ on $(-\infty, 0]$, $1$ on $[1, \infty)$) and $\psi(s) = 1 - \tau\bigl((16s - 1)/3\bigr)$, so $0 \le \psi \le 1$, $\psi = 1$ on $(-\infty, \tfrac1{16}]$, and $\psi(s) = 0$ exactly when $s \ge \tfrac14$. For $t \in \mathbb R^p$ put
$$W(t) = \psi(|t|^2)\,(t, 0) + \bigl(2\psi(|t|^2) - 1\bigr)\,e_{p+1}, \qquad \pi(t) = W(t)/|W(t)|.$$
Then $W$ never vanishes and $\pi$ is smooth; $\pi(t) = (t, 1)/|(t, 1)|$ for $|t| \le \tfrac14$; $\pi(t)$ is north if and only if $t = 0$ and south if and only if $|t| \ge \tfrac12$; $d\pi_0$ is bijective; and north is a regular value of $\pi$ ⟦Chapter7/StdMap · stdMap⟧.

*Proof.* The vertical component of $W$ is $2\psi - 1$, the horizontal one $\psi\,t$; both vanish only if $\psi = \tfrac12$ and $t = 0$, impossible since $\psi(0) = 1$ ⟦Chapter7/StdMap · stdW_ne_zero⟧. So $\pi$, the normalisation of a smooth nonvanishing map, is smooth ⟦Chapter7/StdMap · contMDiff_stdMap⟧. The same components decide the level sets: $\pi(t)$ is a pole only if $\psi(|t|^2)\,|t|^2 = 0$, so $t = 0$ (north) or $|t| \ge \tfrac12$ (south) ⟦Chapter7/StdMap · stdMap_eq_north_iff⟧ ⟦Chapter7/StdMap · stdMap_eq_south_iff⟧. Near $0$, $\pi$ is the central projection of the tangent plane at the north pole ⟦Chapter7/StdMap · stdMap_eq_of_small⟧, and since $(t, 0) \perp e_{p+1}$ its derivative into $\mathbb R^{p+1}$ is $t \mapsto (t, 0)$ ⟦Chapter7/StdMap · hasFDerivAt_stdMap_val_zero⟧. So $d\pi_0$ is injective, hence bijective, and north is a regular value because $0$ is its only preimage ⟦Chapter7/StdMap · mfd_stdMap_zero_bijective⟧ ⟦Chapter7/StdMap · isRegularValue_stdMap_north⟧.

**The collapse map with prescribed derivative.** For linearly independent $b$ let $Bs = \sum_i s_i b_i$ ⟦Chapter7/Collapse · basisCLM⟧ and $A = (d\pi_0)^{-1} \circ B$ ⟦Chapter7/Collapse · Ae⟧, and for $c \in \mathbb R$ put $\pi_c(t) = \pi(c\,At)$ ⟦Chapter7/Collapse · collapse⟧. Then $\pi_c$ is smooth ⟦Chapter7/Collapse · contMDiff_collapse⟧, for $c \ne 0$ it takes the value north exactly at $t = 0$ ⟦Chapter7/Collapse · collapse_eq_north_iff⟧, and in the chart at the north pole
$$\frac{d}{ds}\Big|_{s=0} \varphi_{\mathrm{north}}\bigl(\pi_c(sw)\bigr) = c\,Bw$$
⟦Chapter7/Collapse · hasDerivAt_chart_collapse⟧. For every $\varepsilon > 0$, the constant $c = 2(\|A^{-1}\| + 1)/\varepsilon$ makes $\pi_c$ the south pole outside $B_{\varepsilon/2}$, because then $|cAt| \ge \tfrac12$ there ⟦Chapter7/Collapse · exists_scale⟧.

This is the origin of the scalar $c$ in Theorem C. The product neighbourhood exists only over some ball $B_\varepsilon$, and squeezing the fixed map $\pi$ into $B_{\varepsilon/2}$ by a linear rescaling multiplies its derivative at $0$ by $c$. Milnor avoids this by parametrising his product neighbourhood by all of $\mathbb R^p$.

### V7.7 The product neighbourhood theorem

Milnor's statement: a neighbourhood of $N$ in $M$ is diffeomorphic to $N \times \mathbb R^p$, with $x$ corresponding to $(x, 0)$ and the frame to the standard basis. The formal proof separates an abstract theorem from the concrete tube maps.

#### The abstract theorem

**Theorem (uniform injectivity radius).** Let $N$ be a smooth manifold modelled on $\mathbb R^n$ with first countable topology, and $X$ a Hausdorff smooth manifold modelled, without boundary, on a finite-dimensional (hence complete) real normed space. Let $G : N \times \mathbb R^p \to X$ be smooth, $K \subseteq N$ compact and $\varepsilon_0 > 0$, and assume:

1. $dG_{(x,0)}$ is bijective for every $x \in K$;
2. $G(x, 0) = G(x', 0)$ implies $x = x'$, for all $x, x' \in N$;
3. if $|s|, |s'| < \varepsilon_0$, $x \notin K$ and $G(x, s) = G(x', s')$, then $(x, s) = (x', s')$.

Then there is $\varepsilon$ with $0 < \varepsilon \le \varepsilon_0$ such that $G$ is injective on $N \times B_\varepsilon$ ⟦Chapter7/ProdNbhd · exists_injOn⟧.

**Theorem (tube, open image, smooth inverse).** In the same setting:

- (a) if $dG_{(x,0)}$ is bijective for all $x$ in a compact $K$, then for some $\varepsilon > 0$, $dG_{(x,t)}$ is bijective for $x \in K$, $|t| < \varepsilon$ ⟦Chapter7/ProdNbhd2 · exists_ball_bijective⟧;
- (b) if $dG$ is bijective on $N \times B_\varepsilon$, then $G(N \times B_\varepsilon)$ is open ⟦Chapter7/ProdNbhd2 · isOpen_image_tube⟧;
- (c) if moreover $N \ne \emptyset$ and $G$ is injective on $N \times B_\varepsilon$, then the inverse $G^{-1} : X \to N \times \mathbb R^p$ (the preimage in the tube on the image, an arbitrary point elsewhere) is smooth at every point of $G(N \times B_\varepsilon)$ ⟦Chapter7/ProdNbhd2 · Ginv⟧ ⟦Chapter7/ProdNbhd2 · contMDiffAt_Ginv⟧.

*The idea.* Locally this is the inverse function theorem in charts. The uniform radius is Milnor's compactness argument run with sequences; hypothesis 3 lets the compact set be smaller than $N$, as the non-compact cobordism of V7.10(c) requires.

*The proof as formalized.*

1. *Local injectivity.* Let $w = \phi' \circ G \circ \phi^{-1}$ be the representative of $G$ in the charts $\phi$ at $q_0$ and $\phi'$ at $G(q_0)$ ⟦Chapter7/ProdNbhd · wr⟧. As the model of $X$ has no boundary, $w$ is an ordinary map of vector spaces near $\phi(q_0)$, and if $dG_{q_0}$ is bijective the inverse function theorem gives $w'$ with $w'(w(\xi)) = \xi$ on a ball around $\phi(q_0)$. On the part of the chart domain mapped into that ball, $G(q) = G(q')$ gives $w(\phi q) = w(\phi q')$, so $\phi q = \phi q'$ and $q = q'$ ⟦Chapter7/ProdNbhd · exists_injOn_nhds⟧.
2. *The uniform radius.* If no $\varepsilon$ works, there are $q_k \ne q'_k$ with $G(q_k) = G(q'_k)$ and second coordinates of norm below $\min(\varepsilon_0, 1/(k+1))$. By hypothesis 3 their first coordinates lie in $K$, so a subsequence of the pairs converges in the compact set $(K \times \bar B_{\varepsilon_0})^2$, to $(l, l')$ say; extracting it uses sequential compactness, hence first countability of $N$. The second coordinates tend to $0$, $G(l) = G(l')$ because limits in the Hausdorff space $X$ are unique, and hypothesis 2 gives $l = l'$. For large $k$, $q_k$ and $q'_k$ then lie in the neighbourhood of $l$ where step 1 (with hypothesis 1) makes $G$ injective: a contradiction ⟦Chapter7/ProdNbhd · exists_injOn⟧.
3. *Bijectivity on a tube.* Bijective linear maps between finite-dimensional spaces form an open set ⟦Chapter7/ProdNbhd2 · isOpen_bijective_clm⟧. Near $q_0$, the derivative of $w$ at $\phi(q)$ is $dG_q$ composed on both sides with invertible chart derivatives ⟦Chapter7/ProdNbhd2 · fderiv_wr_eq⟧, and it is continuous in $q$. So bijectivity of $dG$ is an open condition ⟦Chapter7/ProdNbhd2 · isOpen_bijective_mfd⟧, and the tube lemma around $K \times \{0\}$ gives (a).
4. *Open image.* Near $G(q_0)$, $q_0$ in the tube, the map $\mathcal L = \phi^{-1} \circ w' \circ \phi'$ is a right inverse of $G$ with values in the tube ⟦Chapter7/ProdNbhd2 · eventually_L⟧. So the image is a neighbourhood of each of its points.
5. *Smooth inverse.* $G^{-1}$ is chosen as an inverse of $G$ on the tube, and choosing needs a point of $N$ ⟦Chapter7/ProdNbhd2 · Ginv⟧. By injectivity on the tube, $G^{-1}(z) = G^{-1}(G(\mathcal L z)) = \mathcal L z$ near $G(q_0)$, so $G^{-1}$ is smooth there ⟦Chapter7/ProdNbhd2 · contMDiffAt_Ginv⟧.

*What the book leaves implicit.* Milnor's argument is step 2 with $K = N$; the hypotheses on $N$ and $X$ are the ones it uses without saying so.

#### The tube map of a framed submanifold

The point $x + \sum_i s_i v_i(x)$ stays in the domain $U_M$ of $r$ only for small $s$, so the formal proof clamps $s$.

**Lemma (the clamp).** Let $E$ be a real inner product space, $a > 0$ and $2a \le b$. There is a smooth $\lambda : E \to E$ with $\lambda(t) = t$ for $|t| \le a$, $|\lambda(t)| \le b$, and $\lambda(t) = \gamma(t)\,t$ with $0 < \gamma(t) \le 1$; namely $\lambda(t) = g(t)^{-1/2}\,t$ with $g(t) = 1 + \theta(|t|^2)\,|t|^2/b^2$, where $\theta(s) = \tau\bigl((s - a^2)/(3a^2)\bigr)$ ⟦Chapter7/Clamp · exists_clamp⟧.

**Theorem (product neighbourhood of a framed submanifold).** Let $(N, v)$ be a framed submanifold of $M$, $a_0 > 0$, and $\lambda : \mathbb R^p \to \mathbb R^p$ smooth with $\lambda(t) = t$ for $|t| \le a_0$ and $x + \sum_i \lambda(t)_i v_i(x) \in U_M$ for all $x \in N$, $t \in \mathbb R^p$. Put
$$G(x, t) = r\Bigl(x + \sum_i \lambda(t)_i\,v_i(x)\Bigr).$$
Then $G : N \times \mathbb R^p \to M$ is smooth, $G(x, 0) = x$, and there is $\varepsilon$ with $0 < \varepsilon \le a_0$ such that $G$ is injective and $dG$ is bijective on $N \times B_\varepsilon$ ⟦Chapter7/TubeData · exists_tubeData_of_lam⟧. Such $a_0$ and $\lambda$ exist ⟦Chapter7/TubeData · exists_tubeData⟧. Hence $V = G(N \times B_\varepsilon)$ is an open neighbourhood of $N$, and for $N \ne \emptyset$, $G^{-1}$ is smooth on $V$ ⟦Chapter7/TubeData · isOpen_V⟧ ⟦Chapter7/TubeData · contMDiffAt_Ginv⟧.

On $N \times B_\varepsilon$ the clamp is the identity, so there $G(x, s) = r(x + \sum_i s_i v_i(x))$.

*The proof as formalized.*

1. *The clamp exists.* By compactness, $|v_i(x)| \le C$ for some $C > 0$ ⟦Chapter7/ProdNbhdM · exists_bound_v⟧. With $a_0 = \varepsilon_M/(8(pC + 1))$ and the clamp for $a = a_0$, $b = 2a_0$, the displacement is at most $p\,|\lambda(t)|\,C \le 2pa_0C < \varepsilon_M$ ⟦Chapter7/ProdNbhdM · Gamb_mem_Nε⟧. So $G$ is smooth ⟦Chapter7/ProdNbhdM · contMDiff_Gx⟧ and $G(x, 0) = r(x) = x$ ⟦Chapter7/ProdNbhdM · Gx_zero⟧.
2. *The ambient derivative.* As $\lambda$ is the identity near $0$, $(x, t) \mapsto x + \sum_i \lambda(t)_i v_i(x)$ has derivative $D(a, s) = d\iota_x(a) + \sum_i s_i v_i(x)$ at $(x, 0)$, with $\iota : N \to \mathbb R^{K+1}$ the inclusion ⟦Chapter7/ProdNbhdM · hasMFDerivAt_Gamb_zero⟧. $D$ is injective, since its summands are orthogonal (the $v_i$ are normal to $N$) and injective in $a$ and in $s$ respectively ⟦Chapter7/ProdNbhdM · Dg_injective⟧; its values lie in $T_xM$ ⟦Chapter7/ProdNbhdM · Dg_mem_tangentM⟧.
3. *The retraction fixes tangent vectors.* Differentiating $r \circ \iota_M = \iota_M$ gives $dr_x w = w$ for $w \in T_xM$ ⟦Chapter7/ProdNbhdM · fderiv_tubr_of_mem⟧. So $dG_{(x,0)}$, followed by the inclusion of $M$, is $dr_x \circ D = D$ ⟦Chapter7/ProdNbhdM · mfd_val_Gx_zero⟧. Hence $dG_{(x,0)}$ is injective, and bijective since $n + p = m$ ⟦Chapter7/ProdNbhdM · bijective_mfd_Gx_zero⟧.
4. *The abstract theorem* with $K = N$: hypothesis 3 is vacuous, and $G(x, 0) = x$ gives hypothesis 2. Part (a) gives $\varepsilon_1$, and the uniform radius with $\varepsilon_0 = \min(\varepsilon_1, a_0)$ gives $\varepsilon$ ⟦Chapter7/TubeData · exists_tubeData_of_lam⟧.

The data $(\lambda, a_0, \varepsilon, G)$ form a structure, reused by the deformation lemma and the cobordism with a prescribed clamp ⟦Chapter7/TubeData · TubeData⟧.

*Where the formal proof departs from Milnor.* The book's diffeomorphism $N \times \mathbb R^p \to V$ becomes a map that is smooth everywhere but a diffeomorphism only from the tube $N \times B_\varepsilon$ onto $V$. Nothing later needs more.

#### The tube map of a framed cobordism

A framed cobordism between $(N_0, v^0)$ and $(N_1, v^1)$ is a submanifold $S \subseteq M \times \mathbb R$ of dimension $n + 1$, with a constant $0 < \varepsilon_S < \tfrac12$, such that $S$ agrees with $N_0 \times \mathbb R$ for $t < \varepsilon_S$ and with $N_1 \times \mathbb R$ for $t > 1 - \varepsilon_S$, its part over $[0, 1]$ is compact, and its framing $u_i$ in $\mathbb R^{K+1} \times \mathbb R$ (smooth, normal to $S$, independent, with first component tangent to $M$) is $(v^0_i, 0)$, resp. $(v^1_i, 0)$, on the ends ⟦Chapter7/Framed · FramedCob⟧. Its tube map is
$$G_S(q, t) = (r \times \mathrm{id})\Bigl(q + \sum_i \lambda(t)_i\,u_i(q)\Bigr), \qquad q \in S$$
⟦Chapter7/ProdNbhdS · GxS⟧. The facts about $N$ carry over, each with a twist.

- *Boundedness.* $S$ is not compact, but $u$ is bounded, being the framing of $N_0$ or $N_1$ on the ends and living on a compact set in between ⟦Chapter7/ProdNbhdS · exists_bound_u⟧.
- *The derivative.* $dG_S$ is bijective at $(q, 0)$, by steps 2–3 with the inner product $\langle a, b\rangle + a_t b_t$ on $\mathbb R^{K+1} \times \mathbb R$, since $d(r \times \mathrm{id})$ fixes vectors whose first component is tangent to $M$ ⟦Chapter7/ProdNbhdS · DgS_injective⟧ ⟦Chapter7/ProdNbhdS · fderiv_tubr'_of_mem⟧ ⟦Chapter7/ProdNbhdS · bijective_mfd_GxS_zero⟧.
- *The ends.* Where $u_i = (v_i, 0)$, $G_S$ is the tube map of $N_0$ or $N_1$ times the identity in time ⟦Chapter7/CobMap · GxS_end0⟧; everywhere it shifts time by at most $p\,|\lambda(t)|\,C$ ⟦Chapter7/CobMap · abs_snd_GxS_sub_le⟧. And $S \cap (M \times [a, b])$ is compact for $a \le 0$, $b \ge 1$: it is $N_0 \times [a, 0]$, the compact middle and $N_1 \times [1, b]$ ⟦Chapter7/CobMap · isCompact_S_Icc⟧.

**Theorem (injectivity radius of a cobordism).** Let $a_0 > 0$ and $\lambda$ be smooth with $\lambda(t) = t$ for $|t| \le a_0$, such that the $\mathbb R^{K+1}$-component of $q + \sum_i \lambda(t)_i u_i(q)$ always lies in $U_M$. Let $C > 0$ bound all $|u_i|$, and let the ends have product-neighbourhood data built with the same $\lambda$, with radii $\varepsilon^{(0)}$, $\varepsilon^{(1)}$. Then there is $\varepsilon > 0$ with $\varepsilon \le a_0$, $\varepsilon \le \varepsilon^{(0)}, \varepsilon^{(1)}$ and $p\,\varepsilon\,C < \varepsilon_S/4$, such that $G_S$ is injective on $S \times B_\varepsilon$ and $dG_S$ is bijective at every $(q, t)$ with $|t| < \varepsilon$ and the time of $q$ in $[-3, 4]$ ⟦Chapter7/CobMap · exists_injRadius_S⟧.

*Proof.* Apply the abstract theorem with $K = S \cap (M \times [-3, 4])$, compact as noted above, and $\varepsilon_0 = \min(\varepsilon^{(0)}, \varepsilon^{(1)}, a_0, \varepsilon_S/(8(pC+1)))$, so that no point moves in time by as much as $\varepsilon_S/4$; part (a), with the same $K$, supplies the bijectivity. The ends enter through hypothesis 3. If $q$ has time below $-3$ and $G_S(q, s) = G_S(q', s')$, both points have time below $\varepsilon_S$, where $G_S$ is the tube map of $N_0$ times the identity, injective on its tube ⟦Chapter7/CobMap · eq_of_GxS_eq_end0⟧; above time $4$ one uses $N_1$ ⟦Chapter7/CobMap · eq_of_GxS_eq_end1⟧.

Bijectivity of $dG_S$ on the whole tube is *not* obtained, since the tube lemma needs a compact set; V7.10(c) restricts $G_S$ to an open piece of $S$ instead.

### V7.8 Identification of the framing

**Proposition.** Let $f : M \to S^p$ be smooth, $y$ a regular value, $n + p = m$, $N = f^{-1}(y)$ and $x \in N$. Then
$$\ker A_x = T_xN + (T_xM)^\perp.$$
Consequently, if $v \in T_xM$, $v \perp T_xN$ and $A_x v = b_i$, then $v = f^*b_i(x)$ ⟦Chapter7/PontFrame · ker_At_eq⟧ ⟦Chapter7/PontFrame · pontV_eq_of⟧.

*Proof.* Both summands lie in the kernel, since $\tilde F$ is constant on $N$ and, like $r$, on short normal segments to $M$ ⟦Chapter7/Pontryagin · At_tangentN_eq_zero⟧ ⟦Chapter7/Pontryagin · At_normal_eq_zero⟧. Equality is a dimension count: $A_x$ is onto $\mathbb R^p$ ⟦Chapter7/Pontryagin · surjective_At⟧, so its kernel has dimension $K + 1 - p$, while the summands meet only in $0$ (as $T_xN \subseteq T_xM$) and have dimensions $n$ and $K + 1 - m$ ⟦Chapter7/PontFrame · finrank_tangentN_level⟧. For the consequence, $\operatorname{range} A_x^* = (\ker A_x)^\perp$ ⟦Chapter7/PontFrame · range_adjoint_eq⟧ contains $v$, and $A_x^*(A_xA_x^*)^{-1}b_i$ is the only vector of that range mapped to $b_i$ ⟦Chapter7/Compose · pinv_unique⟧.

This links Milnor's definition (the unique normal vector with prescribed image) to the formula for the framing. Theorem C applies it directly; the map of a cobordism uses it through a corollary.

**Corollary.** Let $(N, v)$ be a framed submanifold, $k : M \to S^p$ smooth with $k^{-1}(\mathrm{north}) = N$, $b$ linearly independent, $c > 0$ and $\varepsilon' > 0$, and suppose
$$k\bigl(r(x + s\,v_i(x))\bigr) = \pi_c(s\,e_i) \qquad (x \in N,\ |s| < \varepsilon',\ i = 1, \dots, p).$$
Then north is a regular value of $k$, and the Pontryagin manifold of $k$ at north with basis $c\,b$ is $(N, v)$ ⟦Chapter7/Identify · pontryagin_eq_of_collapse⟧.

*Proof.* Differentiating $s \mapsto \tilde F(x + s\,v_i(x)) = \varphi_{\mathrm{north}}(\pi_c(s e_i))$ at $0$ gives $A_x v_i(x) = c\,b_i$. So $A_x$ is onto, and $x$ is a regular point of $k$ ⟦Chapter7/RegOpen · isRegularPoint_of_surjective_At⟧. The $v_i(x)$ are tangent to $M$ and normal to $N$, whose tangent space is that of $k^{-1}(\mathrm{north})$ ⟦Chapter7/ThmB · tangentN_congr⟧, and the proposition identifies them with the Pontryagin framing.

### V7.9 Theorem C: every framed submanifold is a Pontryagin manifold

**Theorem C.** Let $(N, v)$ be a framed submanifold of $M$ of dimension $n$ and codimension $p$, and $b = (b_1, \dots, b_p)$ linearly independent in $\mathbb R^p$. There are a smooth $f : M \to S^p$ with north as a regular value and a constant $c > 0$ such that the Pontryagin manifold of $f$ at north with basis $c\,b$ is $(N, v)$ ⟦Chapter7/ThmB · exists_map_of_framedSub⟧.

*The idea.* Take the product neighbourhood on its injectivity tube $N \times B_\varepsilon$, choose $c$ so that $\pi_c$ collapses outside $B_{\varepsilon/2}$, and set $f = \pi_c \circ \mathrm{pr}_2 \circ G^{-1}$ on $V$, south elsewhere. Along the framing line $x + s\,v_i(x)$ the map is $\pi_c(s e_i)$, and V7.8 does the rest.

*The proof as formalized.*

1. *The empty case.* If $N = \emptyset$, the constant map south works with $c = 1$: north has no preimage, so it is a regular value ⟦Chapter7/ThmB · south_ne_north⟧.
2. *The tube.* The four steps of V7.7, carried out inline, give $\varepsilon \le a_0$ with $G$ injective and $dG$ bijective on $N \times B_\varepsilon$, so $V$ is open and $G^{-1}$ is smooth on $V$ ⟦Chapter7/ProdNbhd2 · isOpen_image_tube⟧ ⟦Chapter7/ProdNbhd2 · contMDiffAt_Ginv⟧.
3. *The map.* Take $c > 0$ with $\pi_c = \mathrm{south}$ outside $B_{\varepsilon/2}$ ⟦Chapter7/Collapse · exists_scale⟧, and let $f(z) = \pi_c(\mathrm{pr}_2\,G^{-1}(z))$ for $z \in V$, $f(z) = \mathrm{south}$ otherwise.
4. *Smoothness.* On $V$, $f$ is a composite of smooth maps. The compact set $G(N \times \bar B_{\varepsilon/2})$ lies in $V$, and $f$ is the south pole off it, so $f$ is locally constant at points outside $V$. This closed-core argument replaces Milnor's one-line assertion that $f$ is smooth.
5. *The level set.* $f(z) = \mathrm{north}$ forces $z \in V$ and $\mathrm{pr}_2\,G^{-1}(z) = 0$, so $z = G(x, 0) = x \in N$; conversely $G^{-1}(x) = (x, 0)$ for $x \in N$.
6. *The framing.* For $|s| < \min(a_0, \varepsilon)$ the clamp is the identity, so $f(r(x + s\,v_i(x))) = f(G(x, s e_i)) = \pi_c(s e_i)$. Differentiating in the chart at north gives $A_x v_i(x) = c\,b_i$. Hence north is a regular value, and V7.8 identifies the framing ⟦Chapter7/PontFrame · pontV_eq_of⟧ ⟦Chapter7/ThmB · exists_map_of_framedSub⟧.

Step 6, with the level set of step 5 as a hypothesis, is what the corollary of V7.8 packages for the two ends of a cobordism ⟦Chapter7/Identify · pontryagin_eq_of_collapse⟧.

*Where the formal proof departs from Milnor.* The basis $b$ is arbitrary, not necessarily positive, but it is realised only up to the factor $c > 0$. As $c\,b$ and $b$ have the same orientation, nothing is lost: Lemma 4 is proved for proportional bases.

### Three tools for V7.10 and V7.11

**The straight line in stereographic coordinates.** Let $\sigma_y(u) = (1 - \langle u, y\rangle)^{-1}\bigl(u - \langle u, y\rangle\,y\bigr)$ be stereographic projection from $y \in S^p$ onto $y^\perp$, with inverse $\sigma_y^{-1}(w) = \bigl(2w + (|w|^2 - 1)\,y\bigr)/(|w|^2 + 1)$ ⟦Chapter7/Stereo · stereo⟧ ⟦Chapter7/Stereo · stereoInv⟧.

**Proposition.** Let $X$ be a smooth manifold (any model), $f, g : X \to S^p$ smooth, and $U \subseteq X$ open with $f = g$ on $U$, and suppose $f(x) \ne y \ne g(x)$ for $x \notin U$. Then there is a smooth $H : X \times \mathbb R \to S^p$ with $H(\cdot, 0) = f$, $H(\cdot, 1) = g$ and $H(x, t) = f(x)$ for $x \in U$, $t \in \mathbb R$ ⟦Chapter7/Stereo · exists_homotopy_of_eqOn⟧.

*Proof.* Put $H(x, t) = f(x)$ for $x \in U$ and $H(x, t) = \sigma_y^{-1}\bigl((1 - t)\,\sigma_y(f(x)) + t\,\sigma_y(g(x))\bigr)$ otherwise. The segment lies in $y^\perp$, so $\sigma_y^{-1}$ puts it on the sphere for every real $t$, and $\sigma_y^{-1}\sigma_y = \mathrm{id}$ away from $y$ gives the end values ⟦Chapter7/Stereo · stereoInv_stereo⟧. Smoothness is checked on two open sets. On $U \times \mathbb R$, $H = f \circ \mathrm{pr}_1$. On $\{f \ne y,\ g \ne y\} \times \mathbb R$, which contains every point with $x \notin U$, $H$ is given by the stereographic formula (at points of $U$ the segment is constant), and $\sigma_y$ is smooth where $\langle u, y\rangle < 1$ ⟦Chapter7/Stereo · contDiffAt_stereo⟧. This is the first step of Milnor's proof of Lemma 4, with the two open sets made explicit.

**Smooth homotopy.** $f \simeq g$ means a smooth $H : X \times \mathbb R \to Y$ with $H(\cdot, 0) = f$, $H(\cdot, 1) = g$ ⟦Chapter7/Homotopy · SmoothHomotopic⟧. The relation is reflexive on smooth maps and symmetric by $t \mapsto 1 - t$ ⟦Chapter7/Homotopy · SmoothHomotopic.refl⟧ ⟦Chapter7/Homotopy · SmoothHomotopic.symm⟧. For transitivity, a smooth step ($0$ for $t \le \tfrac14$, $1$ for $t \ge \tfrac34$) makes both homotopies constant near the ends ⟦Chapter7/Homotopy · SmoothHomotopic.exists_const_near_ends⟧; then $H_1(x, 2t)$ for $t \le \tfrac12$ is glued to $H_2(x, 2t - 1)$ for $t > \tfrac12$, and the result equals the first formula for $t < \tfrac58$ and the second for $t > \tfrac38$ ⟦Chapter7/Homotopy · SmoothHomotopic.trans⟧.

**Lemma (uniform first-order estimate).** Let $N$ be a compact smooth manifold (any model), $P$ a finite-dimensional and $F$ an arbitrary real normed space, and $W \subseteq N \times P$ open with $N \times \{0\} \subseteq W$. Let $\Phi : N \times P \to F$ be smooth on $W$ with $\Phi(x, 0) = 0$, and let $s \mapsto \Phi(x, s)$ have derivative $L$ at $0$ for every $x$ (one fixed linear $L$). Then for every $\kappa > 0$ there is $\delta > 0$ with
$$|\Phi(x, s) - Ls| \le \kappa\,|s| \qquad (x \in N,\ |s| < \delta)$$
⟦Chapter7/Taylor · exists_uniform_taylor⟧.

*Proof.* The $s$-derivative of $R(x, s) = \Phi(x, s) - Ls$ is jointly continuous on $W$, as the derivative of a smooth family, and vanishes on $N \times \{0\}$. So $\{|\partial_s R| < \kappa\}$ is an open set containing $N \times \{0\}$, hence, by the tube lemma, some $N \times B_\delta$. The mean value inequality on the convex ball $B_\delta$ finishes. No second derivatives appear, whereas Milnor's bound $|F(x, u) - u| \le c_1|u|^2$ needs them bounded on a compact set.

### V7.10 Lemma 4 and the map of a cobordism

#### (a) The deformation lemma

**Lemma (deformation).** Let $(N, v)$ be a framed submanifold with $N \ne \emptyset$ and product-neighbourhood data $(\lambda, a_0, \varepsilon, G)$ as in V7.7. Let $y \in S^p$ with chart $\varphi = \varphi_y$, and $k : M \to S^p$ smooth with $k^{-1}(y) = N$. Let $b$ be linearly independent, $c > 0$, and $A_x v_i(x) = c\,b_i$ for all $x \in N$ and all $i$, where $A_x = d\tilde F_x$ is formed with $k$ and $y$. Then there are a smooth $H : M \times \mathbb R \to S^p$ and $\delta$ with $0 < \delta \le \varepsilon$ such that

- $H(z, 0) = k(z)$ for all $z \in M$;
- $H(G(x, s), 1) = \varphi^{-1}\bigl(\varphi(y) + Bs\bigr)$ for $x \in N$, $|s| < \delta$, where $Bs = \sum_i s_i b_i$;
- $H(z, 1) \ne y$ for $z \notin N$

⟦Chapter7/Deform · exists_deform⟧.

*The idea.* In the chart at $y$ and the coordinates $G$, $k$ becomes $\Phi(x, s) \approx c\,Bs$, uniformly in $x$. Interpolate from $\Phi$ to $Bs$ by a bump in $s$ and a step in time; each interpolant is within $\kappa|s|$ of a multiple of $Bs$ of size at least $2\kappa|s|$, so no zeros appear off $N$.

*The proof as formalized.*

1. *Coordinates.* $W_0 = \{(x, s) \in N \times B_\varepsilon : k(G(x, s)) \in \operatorname{dom}\varphi\}$ is open and contains $N \times \{0\}$, hence, $N$ being compact, a tube $N \times B_{\delta_0}$ ⟦Chapter7/Deform · exists_tube_subset⟧. On $W_0$ put $\Phi(x, s) = \varphi(k(G(x, s))) - \varphi(y)$, smooth with $\Phi(x, 0) = 0$.
2. *The fibre derivative is $c\,B$.* It suffices to check basis vectors. For $|s| \le a_0$, $G(x, s e_i) = r(x + s\,v_i(x))$ ⟦Chapter7/TubeData · G_line⟧, so $\Phi(x, s e_i) = \tilde F(x + s\,v_i(x)) - \varphi(y)$, with derivative $A_x v_i(x) = c\,b_i$ at $0$.
3. *Constants.* $|Bs| \ge m_0|s|$ with $m_0 = 1/(\|B^{-1}\| + 1)$. Let $\kappa = \min(1, c)\,m_0/2$, and take $\delta_1$ from the uniform estimate: $|\Phi(x, s) - cBs| \le \kappa|s|$ for $|s| < \delta_1$. If the chart target contains the ball of radius $\varrho$ about $\varphi(y)$, put $\delta_2 = \varrho/(\kappa + c\|B\| + \|B\| + 1)$ and $\delta^* = \min(\delta_0, \delta_1, \delta_2, \varepsilon)$; then $|\Phi(x, s)| < \varrho$ and $|Bs| < \varrho$ for $|s| < \delta^*$.
4. *The homotopy.* Let $\chi : \mathbb R^p \to [0, 1]$ be a smooth bump, $1$ on $\bar B_{\delta^*/4}$ and $0$ outside $B_{\delta^*/2}$, and $\rho : \mathbb R \to [0, 1]$ a smooth step, $0$ for $\tau \le \tfrac14$ and $1$ for $\tau \ge \tfrac34$ ⟦Chapter7/Transition · exists_timeTransition⟧. With $\theta = \rho(\tau)\,\chi(s)$ put
$$\Psi(x, s, \tau) = \Phi(x, s) + \theta\,\bigl(Bs - \Phi(x, s)\bigr) = (1 - \theta)\,\Phi(x, s) + \theta\,Bs,$$
of norm below $\varrho$ for $|s| < \delta^*$. Let $H(z, \tau) = \varphi^{-1}\bigl(\varphi(y) + \Psi(G^{-1}(z), \tau)\bigr)$ on $V_{\delta^*} = G(N \times B_{\delta^*})$ and $H(z, \tau) = k(z)$ elsewhere.
5. *Smoothness, $\tau = 0$ and $\tau = 1$.* On $V_{\delta^*} \times \mathbb R$ the formula is smooth. Off the compact set $G(N \times \bar B_{\delta^*/2})$, $\chi = 0$ and $H(z, \tau) = k(z)$, which settles the points outside $V_{\delta^*}$. At $\tau = 0$, $\rho = 0$ and $H = k$; at $\tau = 1$ and $|s| < \delta^*/4$, $\Psi = Bs$. The lemma's $\delta$ is $\delta^*/4$.
6. *No new preimages.* Let $z \notin N$ with $H(z, 1) = y$. Then $z \in V_{\delta^*}$, since elsewhere $H(z, 1) = k(z) \ne y$, and $G^{-1}(z) = (x, s)$ with $s \ne 0$, since $s = 0$ gives $z = x \in N$. Then $\Psi = 0$, that is,
$$\bigl((1 - \theta)\,c + \theta\bigr)\,Bs = -(1 - \theta)\,\bigl(\Phi(x, s) - cBs\bigr).$$
The left side has norm at least $\min(1, c)\,m_0|s| = 2\kappa|s|$, the right side at most $\kappa|s|$, which is impossible for $s \ne 0$ ⟦Chapter7/Deform · exists_deform⟧.

*Where the formal proof departs from Milnor.* Milnor deforms $f$ until it agrees with $g$ near $N$, interpolating between their expressions in stereographic coordinates from the antipode of $y$, kept in a common half-space by a second-order Taylor bound. The formal proof deforms each map separately to a standard form fixed by $B$, which allows the derivatives $b$ and $c\,b$; it works in the chart at $y$ and needs only the first-order estimate. Its statement controls the zero set only at time $1$, which is all that is used.

#### (b) Same Pontryagin manifold, homotopic maps

**Theorem (Lemma 4).** Let $n + p = m$, $f, g : M \to S^p$ smooth with a common regular value $y$, $b$ linearly independent and $c > 0$. If the Pontryagin manifold of $f$ at $y$ with basis $b$ equals that of $g$ at $y$ with basis $c\,b$, then $f \simeq g$ ⟦Chapter7/SamePont · smoothHomotopic_of_pontryagin_eq⟧.

*Proof.* Let $(N, v)$ be the common framed submanifold. If $N = \emptyset$, both maps avoid $y$ and the stereographic homotopy with $U = \emptyset$ joins them. Otherwise take product-neighbourhood data for $(N, v)$ ⟦Chapter7/TubeData · exists_tubeData⟧. The Pontryagin framing satisfies $A_x v_i(x) = b_i$ for $f$ and $A_x v_i(x) = c\,b_i$ for $g$ ⟦Chapter7/Pontryagin · At_pontV⟧, so the deformation lemma, with constants $1$ and $c$, gives $f \simeq f_1$ and $g \simeq g_1$. With $\delta$ the smaller radius, $f_1$ and $g_1$ both equal $\varphi_y^{-1}(\varphi_y(y) + Bs)$ on the open neighbourhood $U = G(N \times B_\delta)$ of $N$, and neither takes the value $y$ off $N$. The straight-line homotopy gives $f_1 \simeq g_1$, and symmetry and transitivity finish.

#### (c) The map of a cobordism

**Theorem.** Let $(S, u)$ be a framed cobordism between framed submanifolds $F_0 = (N_0, v^0)$ and $F_1 = (N_1, v^1)$ of $M$, and $b$ linearly independent. There are a smooth $H : M \times \mathbb R \to S^p$ and $c > 0$ such that north is a regular value of $H(\cdot, 0)$ and of $H(\cdot, 1)$, and their Pontryagin manifolds at north with basis $c\,b$ are $F_0$ and $F_1$ ⟦Chapter7/CobMap · exists_cobMap⟧.

*The idea.* Run the proof of Theorem C for $S \subseteq M \times \mathbb R$. As $dG_S$ is known to be bijective only over $S \cap (M \times [-3, 4])$, $S$ is cut to an open piece; the resulting map is smooth on a strip of times, and time is clamped into the strip.

*The proof as formalized.*

1. *Shared data.* A bound $C$ for $u$ bounds $v^0$ and $v^1$ too ⟦Chapter7/CobMap · bound_v0_of_bound_u⟧. One clamp, with $a_0 = \varepsilon_M/(8(pC + 1))$, serves $S$, $N_0$ and $N_1$. It yields product-neighbourhood data for the ends and then the radius $\varepsilon$ for $S$. As $\varepsilon_S < \tfrac12$, the time shift over the $\varepsilon$-tube is below $\tfrac18$.
2. *The open piece.* $S^\circ = S \cap (M \times (-3, 4))$ is open in $S$, hence a manifold, and the restriction $G^\circ$ of $G_S$ to $S^\circ \times \mathbb R^p$ has the same derivative ⟦Chapter7/CobMap · mfd_restrict_prod⟧. So $G^\circ$ is injective with bijective derivative on $S^\circ \times B_\varepsilon$, its image $V^\circ$ is open, and $(G^\circ)^{-1}$ is smooth on $V^\circ$. If $S^\circ = \emptyset$ then $N_0 = N_1 = \emptyset$, as $N_0 \times \{0\}$ and $N_1 \times \{1\}$ lie in $S^\circ$, and $H \equiv \mathrm{south}$ works.
3. *The map on a strip.* With $c$ from the collapse map for the radius $\varepsilon$, let $H_0 = \pi_c \circ \mathrm{pr}_2 \circ (G^\circ)^{-1}$ on $V^\circ$ and $H_0 = \mathrm{south}$ elsewhere. It is smooth on the strip $M \times (-2, 3)$: a point of $V^\circ$ with time in $(-2, 3)$ and $|s| < \varepsilon/2$ comes from a point of $S$ with time within $\tfrac18$, so within the strip $H_0$ is south off the compact set $G^\circ\bigl((S \cap (M \times [-\tfrac52, \tfrac72])) \times \bar B_{\varepsilon/2}\bigr)$.
4. *Clamping time.* Let $\lambda_1$ be the clamp on $\mathbb R$ with $a = \tfrac34$, $b = \tfrac32$, and $\rho(t) = \tfrac12 + \lambda_1(t - \tfrac12)$. Then $\rho(t) = t$ on $[-\tfrac14, \tfrac54]$ and $\rho(\mathbb R) \subseteq [-1, 2]$, so $H(z, t) = H_0(z, \rho(t))$ is smooth on $M \times \mathbb R$ and agrees with $H_0$ at $t = 0, 1$.
5. *The ends.* $H_0(z, t)$ is north exactly when $(z, t) \in S^\circ$, so $H(z, 0)$ is north exactly for $z \in N_0$ and $H(z, 1)$ exactly for $z \in N_1$. For $x \in N_0$ and $|s| < \varepsilon$, the product form of the end and the clamp give $G_S((x, 0), s e_i) = (r(x + s\,v^0_i(x)), 0)$ ⟦Chapter7/TubeData · Gx_line⟧, so $H(r(x + s\,v^0_i(x)), 0) = \pi_c(s e_i)$, and likewise at $t = 1$. The corollary of V7.8 at both ends, with the same $c$, finishes ⟦Chapter7/Identify · pontryagin_eq_of_collapse⟧ ⟦Chapter7/CobMap · exists_cobMap⟧.

*What the book leaves implicit.* Milnor calls this construction analogous to his proof of Theorem C. Formally it is not a copy: the cobordism is not compact, injectivity far out comes from the ends' product neighbourhoods, built with the same clamp, and cutting and clamping replace bijectivity on the whole tube.

### V7.11 Theorem B, second half: framed cobordant maps are homotopic

**Theorem.** Let $n + p = m$ and $p \ge 1$. Let $f, g : M \to S^p$ be smooth, $y$ a regular value of $f$ and $y'$ one of $g$, and $e$, $e'$ bases of $\mathbb R^p$ positive at $y$ and at $y'$. If $(f^{-1}(y), f^*e)$ and $(g^{-1}(y'), g^*e')$ are framed cobordant, then $f \simeq g$ ⟦Chapter7/ThmAconv · smoothHomotopic_of_framedCobordant⟧.

*The idea.* Milnor's proof, after moving both regular values to the north pole: equalise the bases by Lemma 1, realise the cobordism by a map, and apply Lemma 4 at both ends.

*The proof as formalized.*

1. *Rotate to north.* A rotation $R$ of $S^p$ in a plane through $y$ carries $y$ to north; when $y = \pm\,\mathrm{north}$, finding the plane needs a unit vector orthogonal to $y$, the only use of $p \ge 1$ ⟦Chapter7/Rotation · exists_rotation_path⟧. Rotating through a smoothly varying angle gives $f \simeq f' = R \circ f$ ⟦Chapter7/RotHomotopy · exists_rotHomotopy⟧, and north is a regular value of $f'$. The basis $e_1 = dR_y\,e$ is positive at north, as $dR$ has sign $+1$ ⟦Chapter7/Rotation · signAt_rotS⟧, and $(R \circ f)^*e_1 = f^*(dR_y^{-1}e_1) = f^*e$, so the Pontryagin manifolds agree ⟦Chapter7/Compose · pontV_comp⟧ ⟦Chapter7/ThmAconv · exists_rotate_to_north⟧. Likewise $g$ gives $g'$ and $e_2$.
2. *Equal bases.* $e_1$ and $e_2$ are both positive at north, so by Lemma 1 the Pontryagin manifolds of $g'$ for $e_1$ and $e_2$ are framed cobordant ⟦Chapter7/Lemma1 · framedCobordant_of_orientation_eq⟧. Symmetry and transitivity of framed cobordism ⟦Chapter7/Equiv · FramedCobordant.symm⟧ ⟦Chapter7/Equiv · FramedCobordant.trans⟧ give a framed cobordism between the Pontryagin manifolds of $f'$ and $g'$ at north, both with basis $e_1$.
3. *The map of the cobordism.* V7.10(c) gives $H$ and $c > 0$ such that the Pontryagin manifolds of $H(\cdot, 0)$ and $H(\cdot, 1)$ for $c\,e_1$ are those of $f'$ and $g'$ for $e_1$.
4. *Chain.* Lemma 4 with the proportional bases $e_1$ and $c\,e_1$ gives $f' \simeq H(\cdot, 0)$ and $g' \simeq H(\cdot, 1)$, and $H$ joins $H(\cdot, 0)$ to $H(\cdot, 1)$. So $f \simeq f' \simeq H(\cdot, 0) \simeq H(\cdot, 1) \simeq g' \simeq g$ ⟦Chapter7/SamePont · smoothHomotopic_of_pontryagin_eq⟧ ⟦Chapter7/ThmAconv · smoothHomotopic_of_framedCobordant⟧.

Positivity is carried through step 1 and used in step 2; $p \ge 1$ is used only in step 1.

### What the formalization taught us

- **Topological hypotheses.** The uniform injectivity radius uses sequential compactness (first countable $N$), unique limits (Hausdorff target) and the inverse function theorem in charts (target model without boundary) ⟦Chapter7/ProdNbhd · exists_injOn⟧.
- **A compact set, not a compact manifold.** Injectivity known outside a compact $K$ lets the abstract theorem serve the non-compact cobordism $S$ ⟦Chapter7/CobMap · exists_injRadius_S⟧.
- **Glued maps.** Theorem C, the deformation and the cobordism map are smooth by a closed-core argument: off a compact subset of the open set where the formula holds, the map is constant or unchanged ⟦Chapter7/ThmB · exists_map_of_framedSub⟧ ⟦Chapter7/Deform · exists_deform⟧.
- **Empty submanifolds.** The inverse of the tube map is a choice function, so the empty case is treated separately three times ⟦Chapter7/ProdNbhd2 · Ginv⟧ ⟦Chapter7/SamePont · smoothHomotopic_of_pontryagin_eq⟧.
- **The scalar $c$.** A fixed collapse map realises the framing for $c\,b$, $c > 0$, not for $b$, so Lemma 4 is proved for proportional bases ⟦Chapter7/Collapse · exists_scale⟧ ⟦Chapter7/SamePont · smoothHomotopic_of_pontryagin_eq⟧.
- **The framing by a dimension count.** Milnor's unique normal vector with prescribed image is recognised through $\ker d\tilde F_x = T_xN + (T_xM)^\perp$ ⟦Chapter7/PontFrame · ker_At_eq⟧.
- **Lemma 4 by another route.** Each map is deformed separately to a standard form in the chart at $y$, with a first-order estimate instead of a second-order one ⟦Chapter7/Taylor · exists_uniform_taylor⟧ ⟦Chapter7/Deform · exists_deform⟧.
- **Cutting and clamping.** For a cobordism, $dG_S$ is shown bijective only over a compact piece, so $S$ is cut to times in $(-3, 4)$ and time is clamped into $(-2, 3)$ ⟦Chapter7/CobMap · exists_cobMap⟧.
- **The hypotheses of the second half of Theorem B.** $p \ge 1$ serves only to rotate a regular value to north, and positivity of the bases only to apply Lemma 1 ⟦Chapter7/ThmAconv · exists_rotate_to_north⟧ ⟦Chapter7/ThmAconv · smoothHomotopic_of_framedCobordant⟧.


## Part VII. The Hopf theorem (Milnor §7, end)

This part proves Hopf's theorem. Let $M \subseteq \mathbb R^{K+1}$ be a compact, connected, oriented $m$-dimensional submanifold with $m \ge 1$. Two smooth maps $M \to S^m$ are smoothly homotopic exactly when they have the same degree, and every integer is a degree. After Parts V and VI the first statement reduces, as in Milnor, to one about framed $0$-manifolds: two finite sets of framed points with the same signed count are framed cobordant. Milnor calls this "not difficult to see" and sketches it: move points along paths, and cancel pairs of opposite sign along an arc. The formal proof takes another route, governed by one design principle.

**No cobordism is built by hand.** Each elementary operation (moving a framed point, changing its frame, cancelling a pair) is a homotopy of maps $M \to S^m$. It agrees with a fixed map outside a chart ball and is an explicit formula in chart coordinates inside it. The north pole is a regular value of the homotopy, so the construction V7.2 of Part V turns it into a framed cobordism between the Pontryagin manifolds of its two ends ⟦Chapter7/Cobordism · framedCobordant_of_homotopy⟧. The characterization of Pontryagin framings (V7.8) then identifies the ends. Two tools carry the cost: a form of Milnor's Theorem C whose map is the south pole outside a prescribed open set, and a lemma that glues a family on a chart ball into a global homotopy. Milnor's "since $M$ is connected" becomes a precise neighbour lemma. Matching points needs chains of neighbours, because on a circle points cannot pass one another.

Milnor closes §7 with one clause about the non-orientable case: for connected non-orientable $M$ the maps to $S^m$ are classified by the degree modulo 2, because a framed point carried round an orientation-reversing loop comes back with its frame reversed, so that only the parity of the number of points survives. Sections V7.18 to V7.28 prove it, and until the Appendix was finished they were the longest single addition to this book. The reason the clause hides is that it presupposes what an orientable manifold is and that a non-orientable one carries a reversing loop; neither notion existed in Mathlib, in this project, or in the book. It hides one thing more, which the last two sections settle: Milnor states his theorem with no condition on the dimension, and the proof wants $2 \le m$ at one point, so the dimension has to be *derived* from non-orientability, which is a fact about one-manifolds and therefore about the Appendix. What did *not* have to be redone is almost everything else: a survey of the chapter found that framed submanifolds, framed cobordism, the Pontryagin construction, Theorem C and the converse of Theorem B take no orientation of $M$ at all, and that the orientation enters in exactly one definition, the sign of a frame, and in the endgame that cancels a plus against a minus.

**Map of the part.**

- `Chapter7/Hopf0`: finiteness; the sign of a framed point; the signed count is the degree.
- `Chapter7/ThmBsupp`: Theorem C with support in a prescribed open set and scale bounded below.
- `Chapter7/Scale`: large collapse scales; the derivative of the collapse map at $0$.
- `Chapter7/Glue`: chart balls; gluing a chart-local family; framings depend only on germs.
- `Chapter7/Neighbour`: the neighbour lemma.
- `Chapter7/Segment`: the segment property of chart balls; the neighbour lemma in $M$.
- `Chapter7/Chain`: chains of neighbours.
- `Chapter7/TuplePath`: smooth paths of bases, bounded below.
- `Chapter7/MoveMap`: the moving collapse map.
- `Chapter7/CancelMap`: the cancelling family $s_1^2 - a^2\rho(t)$ and its regularity.
- `Chapter7/MoveAux`: frames in the chart of a ball; dual tuples.
- `Chapter7/MoveH`: the glued moving homotopy.
- `Chapter7/Move`: moving a framed point (V7.13).
- `Chapter7/CancelH`: the glued cancelling homotopy.
- `Chapter7/Cancel`: cancelling a pair (V7.14).
- `Chapter7/Reach`: reflexivity, frames of both signs, good balls, reaching a component.
- `Chapter7/Gather`: matching frames; gathering along shortest chains.
- `Chapter7/CancelStep`: cancelling a neighbouring pair of opposite signs.
- `Chapter7/Main`: equal signed counts give framed cobordant $0$-manifolds (V7.16).
- `Chapter7/AddPoint`: adding a framed point.
- `Chapter7/Hopf`: the Hopf theorem and maps of every degree (V7.17).

For the mod 2 theorem of V7.18 to V7.28:

- `Chapter7/OrientTransport`: transport of an orientation through a chart; hops and chains (V7.18).
- `Chapter7/Orientable`: orientability, reversing loops, the chart-level dichotomy (V7.18).
- `Chapter7/OrientBall`: chart balls, ball chains, the exact dichotomy (V7.19).
- `Chapter7/ChartSign`: the chart sign, the self sign, the Jacobian sign, and the bridge (V7.20).
- `Chapter7/BallChainSign`: the sign of a chain, the transition cocycle, chains avoiding a set (V7.21).
- `Chapter7/Puncture`: punctured balls, and the reversing loop away from a finite set (V7.22).
- `Chapter7/Slide`: the slide and the flip, Milnor's clause (V7.23).
- `Chapter7/CancelFree`: cancellation with no condition on the frames (V7.24).
- `Chapter7/CountMod2`: the count modulo 2 and the parity classification (V7.25).
- `Chapter7/HopfMod2`: Milnor's theorem of p. 50 (V7.26).
- `Chapter7/OneManifoldOrientable`: orientations pulled back, the four models of the Appendix oriented, and the orientability of every connected one-manifold (V7.27, V7.28).

**Standing notation.** $M \subseteq \mathbb R^{K+1}$ is a compact, nonempty submanifold of dimension $m$, given by slice charts, with the manifold structure they induce. It is automatically Hausdorff and second countable. $o$ is an orientation of $M$ (V5.0), used wherever signs occur. Connectedness and $m \ge 1$ are assumed only where stated. $S^m \subseteq \mathbb R^{m+1}$ is the unit sphere with the orientation of Chapter 5 (Part 0, §0.7); all degrees and positive bases of this part refer to it. This part numbers standard basis vectors from $1$, so the north and south poles are $\pm e_{m+1}$; a basis of $\mathbb R^m$ is *positive at $y$* if its orientation is that of $S^m$ at $y$ (Part VI) ⟦Chapter5/HairyBall · sphOr⟧ ⟦Chapter7/StdMap · north⟧. $\varphi_x$ is the preferred chart at $x \in M$, with values in $\mathbb R^m$. For a tuple $b$ in $\mathbb R^p$, $B_b$ is the linear map $e_i \mapsto b_i$ ⟦Chapter7/Collapse · basisCLM⟧. A *frame* at $x$ is an $m$-tuple of independent vectors of $T_xM \subseteq \mathbb R^{K+1}$. A *framed $0$-manifold* is a framed submanifold of dimension $0$ and codimension $m$, and $\sim$ denotes framed cobordism (V7.0). V7.2 is the construction of Part V: if a smooth $H : M \times \mathbb R \to S^p$ satisfies $H(x, t) = H(x, 0)$ for $t \le \varepsilon$ and $H(x, t) = H(x, 1)$ for $t \ge 1 - \varepsilon$, for some $0 < \varepsilon < \tfrac12$, and $z$ is a regular value of $H$ and of both ends, then $H^{-1}(z)$ with its pulled-back framing is a framed cobordism between the Pontryagin manifolds of the two ends at $z$, for any common basis ⟦Chapter7/Cobordism · framedCobordant_of_homotopy⟧. The project's docstrings call it Lemma 3; it is the construction inside Milnor's Lemmas 2 and 3. Theorem letters are Milnor's. In §7, Theorem B says that two maps are smoothly homotopic exactly when their Pontryagin manifolds are framed cobordant, and Theorem C that every compact framed submanifold is a Pontryagin manifold; the product neighbourhood theorem has no letter. The file names `ThmB.lean` and `ThmBsupp.lean` follow an older lettering of the project, in which Theorem C was called Theorem B.

### V7.12 Framed points, their signs, and the signed count

A compact $0$-dimensional slice submanifold of any smooth manifold is finite. Around each of its points a slice chart sends it into $\mathbb R^0 \times 0$, a single point, so the chart domain meets it only there, and finitely many such domains cover it. No Hausdorff hypothesis is needed ⟦Chapter7/Hopf0 · IsSliceSubmanifold.finite_of_dim_zero⟧ ⟦Chapter7/Hopf0 · FramedSub.finite_N⟧. The tangent space of such a submanifold is zero ⟦Chapter7/Hopf0 · tangentN_eq_bot_of_dim_zero⟧, so the orthogonality condition on a framing is empty. A framed $0$-manifold is thus a finite set $N$ with a frame $v(x)$ at each point.

*Definition (the sign of a frame).* Let $v = (v_1, \dots, v_m)$ be tangent to $M$ at $x$. The *chart coordinates* of $v_i$ form the vector $w_i \in \mathbb R^m$ with $d\iota_x(w_i) = v_i$, where $\iota$ is the inclusion of $M$ and $d\iota_x$ is read in the chart at $x$ ⟦Chapter7/Hopf0 · chartCoord⟧. The sign of $v$ at $x$ is the sign of $B_w$ from the standard orientation of $\mathbb R^m$ to $o_x$ ⟦Chapter7/Hopf0 · frameSign⟧. For a frame it is nonzero, hence $\pm 1$ ⟦Chapter7/Hopf0 · frameSign_ne_zero⟧ ⟦Chapter7/Gather · frameSign_mem⟧. The *signed count* of $(N, v)$ is $\sum_{x \in N} \operatorname{sign} v(x)$ ⟦Chapter7/Hopf0 · count⟧.

**Theorem (V7.12).** Let $m \ge 1$, let $f : M \to S^m$ be smooth, let $y$ be a regular value of $f$, and let $e$ be a basis of $\mathbb R^m$ that is positive for the orientation of $S^m$ at $y$. Then the signed count of the Pontryagin manifold $(f^{-1}(y), f^*e)$ is $\deg f$. ⟦Chapter7/Hopf0 · count_pontryagin⟧

*The idea.* $df_x$ carries the Pontryagin frame to the positive basis $e$, so the two signs multiply to $+1$.

*The proof as formalized.* The Pontryagin frame satisfies $d\tilde F_x(v_i) = e_i$, where $\tilde F = \varphi_y \circ f \circ r$, with $r$ the nearest-point retraction onto $M$, extends $f$ read in the chart $\varphi_y$ of $S^m$ at $y$ to a neighbourhood of $M$ (V7.1) ⟦Chapter7/Pontryagin · At_pontV⟧. Since $d\tilde F_x \circ d\iota_x = df_x$ in the charts at $x$ and $y$ ⟦Chapter7/Pontryagin · At_comp_mfd_val⟧, we get $df_x \circ B_w = B_e$. The sign of $B_e$ from the standard orientation to the orientation of $e$ is $1$ ⟦Chapter7/Hopf0 · orSign_stdOr_basisCLM⟧. Signs multiply ⟦Chapter5/OrSign · orSign_comp⟧, so $1 = \operatorname{sign} df_x \cdot \operatorname{sign} v(x)$, and two integers with product $1$ are equal ⟦Chapter7/Hopf0 · frameSign_pontryagin⟧. Summing gives $\deg(f; y)$. This is $\deg f$, because $S^m$ is connected for $m \ge 1$ and the degree can be computed at any regular value, by Milnor's Theorem A of §5 ⟦Chapter5/Degree · deg_eq⟧. This is Milnor's argument.

### Theorem C with control of the support

A move changes a map inside a chart ball and keeps it outside. The map kept outside must be the south pole near the frontier of the ball, so that the pieces glue. It must also use the same collapse map as the local modification, so that all framings refer to one basis. A sharpened Theorem C provides both.

**Proposition.** Let $(N, v)$ be a framed submanifold of $M$ of dimension $n$ and codimension $p$, with $n + p = m$. Let $b$ be a basis of $\mathbb R^p$, $W \subseteq M$ an open set containing $N$, and $\underline c \in \mathbb R$. There are a smooth $f : M \to S^p$ with the north pole as a regular value, a number $c > 0$ with $c \ge \underline c$, and a compact $K \subseteq W$ with $f = \mathrm{south}$ outside $K$, such that the Pontryagin manifold of $f$ at the north pole for the basis $cb$ is $(N, v)$. ⟦Chapter7/ThmBsupp · exists_map_of_framedSub_subset⟧

*The idea.* Run the construction of Theorem C (V7.9) with a tube thin enough to lie in $W$ and a collapse scale at least $\underline c$.

*The proof as formalized.* If $N$ is empty, the constant map south works, with $c = \max(\underline c, 1)$ and $K = \emptyset$. Otherwise take the tube map $G(x, s) = r\bigl(x + \sum_i \lambda(s)_i v_i(x)\bigr)$ of the product neighbourhood theorem (V7.7), where $r$ is the retraction onto $M$ and $\lambda$ a smooth clamp equal to the identity near $0$ ⟦Chapter7/Clamp · exists_clamp⟧. The radius $\varepsilon$ of the tube is so small that $\lambda$ is the identity on it, and $dG$ is bijective and $G$ injective on it (V7.7). New here, it also makes $G(N \times B_\varepsilon) \subseteq W$, which the tube lemma allows because $N$ is compact and $G(x, 0) = x$ ⟦Chapter7/Deform · exists_tube_subset⟧. Then $V = G(N \times B_\varepsilon)$ is open.

The collapse map is $\pi_{b,c}(t) = \pi(cAt)$ ⟦Chapter7/Collapse · collapse⟧. Here $\pi$ is the standard map of V7.9, with $\pi^{-1}(\mathrm{north}) = \{0\}$ and $\pi = \mathrm{south}$ for $|t| \ge 1/2$, and $A = (d\pi_0)^{-1}B_b$. It is south for $|t| \ge \varepsilon/2$ once $c \ge 2(\|A^{-1}\| + 1)/\varepsilon$, so a suitable $c \ge \underline c$ exists ⟦Chapter7/Scale · exists_scale_ge⟧. Put $f = \pi_{b,c} \circ \mathrm{pr}_2 \circ G^{-1}$ on $V$ and $f = \mathrm{south}$ elsewhere. Then $f$ is south outside the compact core $K = G(N \times \bar B_{\varepsilon/2}) \subseteq V \subseteq W$. This gives the support statement, and smoothness at points outside $V$. Also $f^{-1}(\mathrm{north}) = N$. Along a framing line $f(r(x + sv_i(x))) = \pi_{b,c}(se_i)$ for small $s$, and in the chart at the north pole this has derivative $cb_i$ at $s = 0$ ⟦Chapter7/Collapse · hasDerivAt_chart_collapse⟧. So the extension of $f$ sends $v_i(x)$ to $cb_i$. The north pole is regular, and by V7.8 the frame $v$ is the Pontryagin frame for $cb$ ⟦Chapter7/PontFrame · pontV_eq_of⟧.

The moves use a uniform scale. There is a threshold $c_1$ such that every $c \ge c_1$ makes $\pi_{b,c}$ south outside $B_{\varepsilon/2}$ ⟦Chapter7/Scale · exists_scale_all⟧. A move fixes $c_1$ for its local family, then calls the proposition with $\underline c = c_1$. The local family and the Theorem-C map then share $\pi_{b,c}$, and hence the basis $cb$. The chart derivative of $\pi_{b,c}$ at $0$ is $cB_b$ ⟦Chapter7/Scale · hasMFDerivAt_collapse_zero⟧.

### Gluing a chart-local homotopy into a global map

For $x_c \in M$, $\varphi = \varphi_{x_c}$ and $R > 0$, the *chart ball* $U_R = \{x \in \operatorname{dom}\varphi : |\varphi(x) - \varphi(x_c)| < R\}$ is open ⟦Chapter7/Glue · ballU⟧ ⟦Chapter7/Glue · isOpen_ballU⟧. Suppose $\bar B(\varphi(x_c), R)$ lies in the image of $\varphi$. Its image under $\varphi^{-1}$ is compact, hence closed, so it contains $\overline{U_R}$ ⟦Chapter7/Glue · closure_ballU_subset⟧. So a frontier point of $U_R$ lies in the chart, at distance at least $R$ from the centre ⟦Chapter7/Glue · frontier_ballU⟧. Without this hypothesis the frontier could leave the chart.

**Proposition (gluing).** Let $M \subseteq \mathbb R^{K+1}$ be an $m$-dimensional submanifold (compactness is not needed). Let $x_c \in M$, $\varphi = \varphi_{x_c}$, and $R > 0$ with $\bar B(\varphi(x_c), R)$ in the image of $\varphi$. Let $\Phi : \mathbb R^m \times \mathbb R \to S^m$ be smooth with $\Phi(s, t) = \mathrm{south}$ whenever $|s - \varphi(x_c)| \ge R/2$. Let $k : M \to S^m$ be smooth and equal to south on an open set $O \supseteq \overline{U_R} \setminus U_R$. Then
$$H(x, t) = \begin{cases} \Phi(\varphi(x), t), & x \in U_R, \\ k(x), & x \notin U_R, \end{cases}$$
is smooth on $M \times \mathbb R$. ⟦Chapter7/Glue · glueH⟧ ⟦Chapter7/Glue · contMDiff_glueH⟧

*The idea.* Near a point outside $U_R$, the nearby part of $U_R$ lies where both $\Phi$ and $k$ are south.

*The proof as formalized.* On $U_R \times \mathbb R$ the map is $\Phi \circ (\varphi \times \mathrm{id})$. Let $z \notin U_R$, and let $A = \{x \in \operatorname{dom}\varphi : |\varphi(x) - \varphi(x_c)| > R/2\}$, an open annulus ⟦Chapter7/Glue · isOpen_annulus⟧. The open set $N_0 = (O \cap A) \cup (M \setminus \overline{U_R})$ contains $z$: either $z \notin \overline{U_R}$, or $z$ is a frontier point, in $O$ and at chart distance $\ge R$. A point of $N_0$ inside $U_R$ lies in $O \cap A$, where $\Phi$ and $k$ are both south. So $H = k \circ \mathrm{pr}_1$ on $N_0 \times \mathbb R$ ⟦Chapter7/Glue · glueH_eventually_eq_of_notMem⟧, and this map is smooth.

Two facts complete the toolkit. First, the Pontryagin framing at a point depends only on the germ of the map, because it is computed from $\varphi_y \circ f \circ r$ and $r$ is continuous with $r(x) = x$ on $M$ ⟦Chapter7/Glue · At_congr⟧ ⟦Chapter7/Glue · pontV_congr⟧. A time slice of $H$ agrees with $k$ near each point outside $U_R$, so it has the framing of $k$ there ⟦Chapter7/Glue · glueH_slice_eventually_eq_of_notMem⟧. Second, on $U_R$ the derivative of a time slice is $d(\Phi(\cdot, t))_{\varphi(x)} \circ d\varphi_x$ ⟦Chapter7/Glue · hasMFDerivAt_glueH_slice_of_mem⟧.

### V7.15 The neighbour lemma and chains

Milnor moves points "since $M$ is connected". In dimension $1$ this is not enough, because a point on a circle cannot move past another. The formal proof uses only what connectedness gives. Let $N$ be a finite subset of a space $X$. For $x \in N$, $C(x)$ is the connected component of $x$ in $X \setminus (N \setminus \{x\})$, the region where $x$ can travel without meeting the other points ⟦Chapter7/Neighbour · compl'⟧. A point $z \in N$ is a *neighbour* of $x \in N$ if $z \in \overline{C(x)}$ ⟦Chapter7/Chain · adjN⟧.

**Theorem (V7.15, the neighbour lemma).** Let $X$ be a connected, locally connected $T_1$ space and $N \subseteq X$ finite. Suppose every $x \in N$ has an open neighbourhood $J$ with $J \cap N \subseteq \{x\}$ and $J \setminus \{x\} \subseteq C(x)$. If $B \subseteq N$ and $N \setminus B$ are both nonempty, some $x \in B$ has a neighbour in $N \setminus B$. ⟦Chapter7/Neighbour · exists_neighbour⟧

*The idea.* Otherwise $B$ together with its regions $C(x)$ would be a nonempty, proper, clopen set.

*The proof as formalized.* Each $C(x)$ is open, as a component of an open set in a locally connected space; $N \setminus \{x\}$ is closed because it is finite and points are closed ⟦Chapter7/Neighbour · isOpen_compl'⟧. Moreover $\overline{C(x)} \subseteq C(x) \cup (N \setminus \{x\})$: a limit point outside $N \setminus \{x\}$ has a connected open neighbourhood avoiding $N \setminus \{x\}$, which meets $C(x)$ and so joins it ⟦Chapter7/Neighbour · closure_compl'_subset⟧. Now suppose no point of $B$ has a neighbour in $N \setminus B$, and put $A = B \cup \bigcup_{x \in B} C(x)$. $A$ is open: it contains the given $J$ around each $x \in B$, and each open $C(x)$. $A$ is closed: its closure is the finite union $B \cup \bigcup_{x \in B} \overline{C(x)}$, whose extra points lie in $N$, but not in $N \setminus B$ by assumption, hence in $B$. $A$ is nonempty and misses $N \setminus B$. This contradicts connectedness.

In $M$ the hypothesis on $J$ is a *segment property* of chart balls. Small chart balls lie in any neighbourhood of their centre, with the closed ball inside the chart image ⟦Chapter7/Segment · exists_ballU_subset⟧. Let such a ball $U_r$ around $x \in N$ meet $N$ only in $x$, and let $y \ne x$ lie in it. The chart segment $s \mapsto \varphi^{-1}\bigl(\varphi(x) + s(\varphi(y) - \varphi(x))\bigr)$, $0 < s \le 1$, stays in $U_r \setminus \{x\}$, is connected, and has $x$ in its closure. With $x$ added it is a connected subset of $M \setminus (N \setminus \{x\})$, so $y \in C(x)$ ⟦Chapter7/Segment · ballU_diff_subset_compl'⟧ ⟦Chapter7/Segment · exists_segment_ball⟧. $M$ is locally connected ⟦Chapter7/Segment · locallyConnectedSpace_M⟧ and $T_1$, so the neighbour lemma holds for finite subsets of a connected $M$, compact or not ⟦Chapter7/Segment · exists_neighbour_M⟧.

The same argument gives chains. A *chain of length $k$ from $x$ to $z$ with interior in $A$* is a sequence $x = u_0, \dots, u_k = z$ in $N$ with each $u_{j+1}$ a neighbour of $u_j$ and $u_0, \dots, u_{k-1} \in A$ ⟦Chapter7/Chain · chainRel⟧. Under the hypotheses of the neighbour lemma, let $x_0 \in B \subseteq N$ with $N \setminus B$ nonempty. Then a chain with interior in $B$ leads from $x_0$ to $N \setminus B$. Otherwise the set $Q$ of points so reachable lies in $B$, and the neighbour lemma for $Q$ and $N \setminus Q$ extends some chain out of $Q$ ⟦Chapter7/Chain · exists_chainRel⟧. A combinatorial lemma adds: if no chain shorter than $k$ reaches $w$, a chain of length $k$ ending at $w$ does not visit $w$ earlier ⟦Chapter7/Chain · chainRel_diff'⟧. This lets a point step out of the way without breaking the chain behind it.

### V7.13 Moving a framed point

The first operation moves one framed point inside a chart ball and gives it any frame of the same sign. Milnor slides the point along a path and carries the frame along. Here a homotopy of maps does it.

**Theorem (V7.13, moving a point).** Let $m \ge 1$ and let $(N, v)$ be a framed $0$-manifold. Let $x_c \in M$, $\varphi = \varphi_{x_c}$, and $R > 0$. Assume $\bar B(\varphi(x_c), R)$ lies in the image of $\varphi$, and $\varphi$ preserves orientation (is *positive*) on $U_R$: for $z \in U_R$, $d\varphi_z$ has sign $1$ from $o_z$ to $o_{x_c}$. Let $x_0 \in N \cap U_{R/4}$ be the only point of $N$ in $\overline{U_R}$. Let $x_1 \in U_{R/4}$, and let $v_1$ be a frame at $x_1$ with $\operatorname{sign} v_1 = \operatorname{sign} v(x_0)$. Then $(N, v)$ is framed cobordant to the framed $0$-manifold with points $(N \setminus \{x_0\}) \cup \{x_1\}$, frame $v_1$ at $x_1$, and frame $v$ elsewhere. ⟦Chapter7/Move · exists_move⟧

*The idea.* On $U_R$, replace the Theorem-C map of $(N, v)$ by a collapse map. Its centre moves from $\varphi(x_0)$ to $\varphi(x_1)$, and its linear part moves from the inverse chart matrix of $v(x_0)$ to that of $v_1$. The north pole stays regular, and V7.2 does the rest.

*The proof as formalized.*

1. *Frames in the chart.* For a frame $\xi$ at $x \in U_R$ with chart coordinates $w$, let $B_\xi = d\varphi_x \circ B_w$, the matrix of $\xi$ in the chart $\varphi$ ⟦Chapter7/MoveAux · chartFrameCLM⟧. As $\varphi$ is positive at $x$, $B_\xi$ is invertible, and its sign from the standard orientation to $o_{x_c}$ is the sign of $\xi$ ⟦Chapter7/MoveAux · orSign_chartFrameCLM⟧. The *dual tuple* $\tau$ is the tuple of columns of $B_\xi^{-1}$: a basis with $B_\tau = B_\xi^{-1}$ and the same sign ⟦Chapter7/MoveAux · exists_dualTuple⟧. The dual tuples $\tau_0$ of $v(x_0)$ and $\tau_1$ of $v_1$ thus have the same orientation ⟦Chapter7/MoveAux · orientation_eq_of_orSign_basisCLM_eq⟧.

2. *Paths.* A smooth path of bases $\tau(t)$, equal to $\tau_0$ for $t \le 1/4$ and to $\tau_1$ for $t \ge 3/4$, comes from a path in $GL^+(m)$ (V7.3) acting on $\tau_1$ ⟦Chapter7/BasisPath · exists_basisPath⟧. By compactness of $[0,1] \times S^{m-1}$, $|B_{\tau(t)}z| \ge \mu|z|$ for some $\mu > 0$ ⟦Chapter7/TuplePath · exists_tuplePath⟧. The centre moves along $\gamma(t) = \varphi(x_0) + \sigma(t)(\varphi(x_1) - \varphi(x_0))$, with $\sigma$ the transition function ($0$ for $t \le 1/4$, $1$ for $t \ge 3/4$) ⟦Chapter7/Transition · exists_timeTransition⟧. By convexity $|\gamma(t) - \varphi(x_c)| < R/4$.

3. *The local family.* With $b$ the standard basis ($B_b = \mathrm{id}$), put $\Phi(s, t) = \pi_{b,c}\bigl(B_{\tau(t)}(s - \gamma(t))\bigr)$ ⟦Chapter7/MoveMap · moveΦ⟧. It is smooth ⟦Chapter7/MoveMap · contMDiff_moveΦ⟧. It equals north exactly at $s = \gamma(t)$ ⟦Chapter7/MoveMap · moveΦ_eq_north_iff⟧, with $s$-derivative $cB_{\tau(t)}$ there ⟦Chapter7/MoveMap · hasMFDerivAt_moveΦ_slice⟧. Let $c_1$ be the threshold beyond which $\pi_{b,c}$ is south outside the ball of radius $\mu R/4$. For $c \ge c_1$ and $|s - \varphi(x_c)| \ge R/2$ we have $|s - \gamma(t)| \ge R/4$, so $|B_{\tau(t)}(s - \gamma(t))| \ge \mu R/4$ and $\Phi(s, t) = \mathrm{south}$ ⟦Chapter7/MoveH · moveΦ_south_of_le⟧.

4. *The map outside.* The open set $W = (M \setminus \overline{U_R}) \cup U_{R/2}$ contains $N$. Theorem C with control of the support, with $\underline c = c_1$, gives $c \ge c_1$ and a smooth $k$ with Pontryagin manifold $(N, v)$ at the north pole for $cb$, south outside a compact $K \subseteq W$. The frontier of $U_R$ misses $W$, so $O = M \setminus K$ contains it ⟦Chapter7/ThmBsupp · exists_map_of_framedSub_subset⟧ ⟦Chapter7/Move · exists_move⟧.

5. *The homotopy.* By the gluing lemma, $H$ ($\Phi \circ (\varphi \times \mathrm{id})$ on $U_R \times \mathbb R$, $k \circ \mathrm{pr}_1$ elsewhere) is smooth ⟦Chapter7/MoveH · contMDiff_moveH⟧. Every time slice has the north pole as a regular value: at the moving point its derivative is the bijection $cB_{\tau(t)} \circ d\varphi_x$ ⟦Chapter7/MoveH · mfd_moveH_slice_of_mem⟧ ⟦Chapter7/MoveH · isRegularValue_moveH_slice⟧, and elsewhere it agrees with $k$ locally. The north pole is also a regular value of $H$, since the derivative of $\Phi$ is already onto on $\mathbb R^m \times 0$ ⟦Chapter7/MoveMap · surjective_mfderiv_moveΦ⟧ ⟦Chapter7/MoveH · isRegularValue_moveH⟧. $H$ is independent of $t$ for $t \le 1/4$ and for $t \ge 3/4$.

6. *The cobordism and its ends.* By V7.2, the Pontryagin manifolds of $H(\cdot, 0)$ and $H(\cdot, 1)$ at the north pole, for $cb$, are framed cobordant ⟦Chapter7/Cobordism · framedCobordant_of_homotopy⟧. The preimage of north under $H(\cdot, t)$ is $(N \setminus U_R) \cup \{\varphi^{-1}(\gamma(t))\}$ ⟦Chapter7/Move · moveH_slice_preimage⟧: $N$ at $t = 0$, $(N \setminus \{x_0\}) \cup \{x_1\}$ at $t = 1$. Off $U_R$ the framing is that of $k$, namely $v$ ⟦Chapter7/Move · pontV_moveH_slice_of_notMem⟧. At the moving point, V7.8 identifies the frame as $v(x_0)$ at $t = 0$ and $v_1$ at $t = 1$. For $\xi = v(x_0)$ at $t = 0$ and $\xi = v_1$ at $t = 1$, the slice derivative sends the chart coordinates of the $i$-th vector of $\xi$ to $cB_{\tau(t)}B_\xi e_i = ce_i$, because $B_{\tau(t)} = B_\xi^{-1}$ there, and orthogonality is empty in dimension $0$ ⟦Chapter7/Move · pontV_moveH_slice_of_mem⟧.

*Where the formal proof departs from Milnor.* No path in $M$ is followed and no frame is transported. A pure change of frame is the case $x_1 = x_0$, where only the linear part moves ⟦Chapter7/Move · exists_move⟧.

#### Reaching the whole component

Moves in chart balls are chained by an open–closed argument instead of a path.

**Theorem (V7.13, reach).** Let $m \ge 1$, let $(N, v)$ be a framed $0$-manifold, and let $x_0 \in N$. Let $y \in C(x_0)$, the component of $x_0$ in $M \setminus (N \setminus \{x_0\})$, and let $v_y$ be a frame at $y$ with $\operatorname{sign} v_y = \operatorname{sign} v(x_0)$. Then $(N, v)$ is framed cobordant to the framed $0$-manifold with points $(N \setminus \{x_0\}) \cup \{y\}$, frame $v_y$ at $y$, and frame $v$ elsewhere. ⟦Chapter7/Reach · exists_reach⟧

*The idea.* The set of points $x_0$ can reach is open and closed in $C(x_0)$.

*The proof as formalized.* Three preparations come first. Framed cobordism of framed $0$-manifolds is reflexive: the constant homotopy $k \circ \mathrm{pr}_1$ of a Theorem-C map $k$ has the north pole as a regular value ⟦Chapter7/Lemma1 · isRegularValue_comp_fst⟧, and V7.2 applies ⟦Chapter7/Reach · FramedCobordant.refl'⟧. Even this product cobordism is never written down. Every point carries frames of both signs. If $\varepsilon_x$ is the sign of the identity from the standard orientation to $o_x$, the frame $d\iota_x(e_i)$ has sign $\varepsilon_x$. The frame $d\iota_x(Te_i)$ has sign $-\varepsilon_x$, where $T = I - 2e_1e_1^{\top}$ is a reflection, the matrix $T_{-1/2}$ of the cancellation below ⟦Chapter7/Reach · exists_frame_of_sign⟧.

Finally, there are good balls. Let $P$ be finite, $C$ open, and $y \in C \setminus P$. A *good ball* around $y$ is a chart ball $U_R$ centred at $y$, with closed ball in the chart image and $\varphi_y$ preserving orientation on it, such that $\overline{U_R} \cap P = \emptyset$ and $U_R \subseteq C$. Chart-continuity of orientations (V5.0) makes the set where $\varphi_y$ is positive a neighbourhood of $y$. A chart ball of half the radius inside it, inside $C$ and away from $P$, is good ⟦Chapter7/Reach · exists_goodBall⟧. In a good ball for $P = N \setminus \{x_0\}$, V7.13 moves a point of $U_{R/4}$ to any other point of $U_{R/4}$, with any frame of the same sign ⟦Chapter7/Reach · move_in_ball⟧.

Let $s$ be the sign of $v(x_0)$. Let $\mathcal R$ be the set of $z$ such that $(N, v)$ is framed cobordant to a framed $0$-manifold with points $(N \setminus \{x_0\}) \cup \{z\}$, a frame of sign $s$ at $z$, and $v$ elsewhere. Reflexivity gives $x_0 \in \mathcal R$. $C(x_0) \cap \mathcal R$ is open: from a reachable $z$, a good ball around $z$ inside $C(x_0)$ reaches its quarter ball, and transitivity (V7.4) composes the cobordisms ⟦Chapter7/Equiv · FramedCobordant.trans⟧. $C(x_0) \setminus \overline{\mathcal R}$ is open. A point of $C(x_0) \cap \overline{\mathcal R}$ is reached from a reachable point in the quarter ball of a good ball around it. So the connected $C(x_0)$ lies in $\mathcal R$. A last move at $y$, from $y$ to itself, installs $v_y$. Connectedness of $M$ is not used.

### V7.14 Cancelling a pair of opposite signs

In Milnor's picture two points of opposite sign are joined by an arc in $M \times [0, 1]$ that turns back in time. In the formal proof that arc is the preimage of the north pole under a homotopy, and nobody ever looks at it.

#### The family $s_1^2 - a^2\rho(t)$

Fix a unit vector $w \in \mathbb R^m$, a centre $c_0 \in \mathbb R^m$ and $a > 0$. Let $\rho : \mathbb R \to [-1, 1]$ be smooth, with $\rho = 1$ for $t \le 1/4$, $\rho = -1$ for $t \ge 3/4$, and $\rho'(t) \ne 0$ wherever $\rho(t) = 0$. The formal proof takes $\rho = 1 - 2\sigma$, with $\sigma$ the transition function, whose derivative is positive on $(1/4, 3/4)$ ⟦Chapter7/CancelMap · exists_rho⟧. Write $s_1 = \langle w, z\rangle$ and $z' = z - s_1w$, and put
$$G_t(z) = \bigl(s_1^2 - a^2\rho(t)\bigr)w + z', \qquad \Psi(s, t) = \pi_{b,c}\bigl(G_t(s - c_0)\bigr)$$
⟦Chapter7/CancelMap · cancelG⟧ ⟦Chapter7/CancelMap · cancelΦ⟧. In coordinates adapted to $w$, $G_t(s_1, z') = (s_1^2 - a^2\rho(t), z')$.

- *Zeros.* $G_t(z) = 0$ exactly when $z = lw$ with $l^2 = a^2\rho(t)$ ⟦Chapter7/CancelMap · cancelG_eq_zero_iff⟧. So $\Psi(\cdot, t)$ equals north at $c_0 \pm aw$ for $t \le 1/4$ and nowhere for $t \ge 3/4$ ⟦Chapter7/CancelMap · cancelΦ_eq_north_iff⟧.
- *Far field.* If $2a \le r \le |z|$, then $|G_t(z)| \ge \min(r/2, r^2/4)$: either $|z'|^2 \ge r^2/2$, or $s_1^2 - a^2\rho(t) \ge r^2/2 - r^2/4$ ⟦Chapter7/CancelMap · norm_cancelG_ge⟧. So $\Psi$ is south far from $c_0$ when the collapse scale is large ⟦Chapter7/CancelMap · cancelΦ_eq_south⟧.
- *Slices.* At $lw$ the derivative of $G_t$ is $T_l = 2l\,P_w + (I - P_w)$, with $P_w$ the orthogonal projection onto $\mathbb Rw$ ⟦Chapter7/CancelMap · Tcan⟧ ⟦Chapter7/CancelMap · hasFDerivAt_cancelG_slice⟧. It is diagonal in an orthonormal basis extending $w$, so $\det T_l = 2l$ ⟦Chapter7/CancelMap · det_Tcan⟧, and $T_l$ is invertible for $l \ne 0$ ⟦Chapter7/CancelMap · Tcan_bijective⟧.
- *The merging moment.* When $\rho(t^*) = 0$ the zeros merge at $l = 0$, and $T_0 = I - P_w$ kills $w$. The slice $\Psi(\cdot, t^*)$ does not have north as a regular value, but $\Psi$ does. At a zero $(c_0 + lw, t)$ the full derivative of $(s, t) \mapsto G_t(s - c_0)$ is $(h, \theta) \mapsto T_lh - \theta a^2\rho'(t)w$ ⟦Chapter7/CancelMap · Dcan⟧ ⟦Chapter7/CancelMap · hasFDerivAt_cancelG_full⟧, and that of $\Psi$ is $cB_b$ composed with it. For $l = 0$, a vector $q$ is the image of $h = q - \langle w, q\rangle w$ and $\theta = -\langle w, q\rangle/(a^2\rho'(t^*))$ ⟦Chapter7/CancelMap · surjective_Dcan⟧ ⟦Chapter7/CancelMap · surjective_mfderiv_cancelΦ⟧. This is exactly where $\rho' \ne 0$ at the zeros of $\rho$ is used.

Now let $x_c$, $\varphi$ and $R$ be as in V7.13, with $|c_0 - \varphi(x_c)| < R/8$ and $8a \le R$. With $r = 3R/8$, $\Psi$ is south where $|s - \varphi(x_c)| \ge R/2$, provided the collapse is south outside the ball of radius $\min(3R/16, 9R^2/256)$ ⟦Chapter7/CancelH · cancelΦ_south_of_le⟧. The glued homotopy is then smooth ⟦Chapter7/CancelH · contMDiff_cancelH⟧. A slice with $\rho(t) \ne 0$ has north as a regular value, since its zeros have $l \ne 0$ and invertible derivative $cB_bT_l \circ d\varphi$ ⟦Chapter7/CancelH · mfd_cancelH_slice_of_mem⟧ ⟦Chapter7/CancelH · isRegularValue_cancelH_slice⟧. The homotopy has north as a regular value at all times ⟦Chapter7/CancelH · isRegularValue_cancelH⟧.

#### The cancellation

**Theorem (V7.14).** Let $m \ge 1$ and let $(N, v)$ be a framed $0$-manifold. Let $x_c$, $\varphi$ and $R > 0$ be as in V7.13: $\bar B(\varphi(x_c), R)$ lies in the image of $\varphi$, and $\varphi$ preserves orientation on $U_R$. Let $w \in \mathbb R^m$ be a unit vector, $a > 0$ with $8a \le R$, and $c_0 \in \mathbb R^m$ with $|c_0 - \varphi(x_c)| < R/8$. Let $x_1, x_2 \in N$ lie in the domain of $\varphi$, with $\varphi(x_1) = c_0 + aw$ and $\varphi(x_2) = c_0 - aw$, and let no other point of $N$ lie in $\overline{U_R}$. Let $\varepsilon$ be the sign of the identity of $\mathbb R^m$ from $o_{x_c}$ to the standard orientation. Then there are framed $0$-manifolds $(N, v^0)$ and $(N \setminus \{x_1, x_2\}, v')$, both with frame $v$ at the points other than $x_1, x_2$, such that $\operatorname{sign} v^0(x_1) = \varepsilon$, $\operatorname{sign} v^0(x_2) = -\varepsilon$, and $(N, v^0) \sim (N \setminus \{x_1, x_2\}, v')$. ⟦Chapter7/Cancel · exists_cancel⟧

*The idea.* Run the cancelling family inside $U_R$ on top of a Theorem-C map of $(N, v)$, and let V7.2 produce the cobordism. At $x_1$ and $x_2$ the family produces "standard" frames, whose signs can be computed, rather than $v$.

*The proof as formalized.* Both points lie in $U_{R/4}$. Take $b$ the standard basis, $\rho$ as above, the threshold $c_1$ for the radius $\min(3R/16, 9R^2/256)$, and a Theorem-C map $k$ of $(N, v)$ with $c \ge c_1$, south outside a compact subset of $W = (M \setminus \overline{U_R}) \cup U_{R/2}$. Glue and apply V7.2. At $t = 0$ ($\rho = 1$) the preimage of north is $(N \setminus U_R) \cup \{x_1, x_2\} = N$ ⟦Chapter7/Cancel · cancelH_slice_preimage_zero⟧. At $t = 1$ ($\rho = -1$) the equation $l^2 = -a^2$ has no solution, and the preimage is $N \setminus \{x_1, x_2\}$ ⟦Chapter7/Cancel · cancelH_slice_preimage_one⟧. Off $U_R$ the frames are those of $k$, that is, $v$ ⟦Chapter7/Cancel · pontV_cancelH_slice_of_notMem⟧.

At a zero $x_t = \varphi^{-1}(c_0 + lw)$ of a regular slice, let $D$ be the slice derivative and $B$ the matrix of chart coordinates of the Pontryagin frame. Then $D \circ B = c\,\mathrm{id}$ and $D = cT_l \circ d\varphi_{x_t}$. Now $\operatorname{sign}(cT_l) = \operatorname{sgn}(c^m \cdot 2l) = \operatorname{sgn} l$, so the frame read in the chart of the ball has determinant of sign $\operatorname{sgn} l$, with no orientation anywhere in the statement ⟦Chapter7/Cancel · chartSign_cancelH_slice⟧. Since $\varphi$ is positive on $U_R$, the bridge of V7.20 multiplies that chart sign by one factor $\varepsilon$, the same for the whole ball, to give the frame sign ⟦Chapter7/ChartSign · Framed.frameSign_eq_orEps_hub_mul_chartSign⟧; $l = \pm a$ gives the signs $\pm\varepsilon$.

*What the book leaves implicit.* The pair must carry the standard frames, whose signs depend on the chart through $\varepsilon$. So cancelling two given points needs two changes of frame first, and the direction of $w$ must match the signs ⟦Chapter7/CancelStep · cancel_step⟧.

**Proposition (cancelling neighbours).** Let $m \ge 1$ and let $(N, v)$ be a framed $0$-manifold. Let $x_0 \ne z$ in $N$ satisfy $\operatorname{sign} v(z) = -\operatorname{sign} v(x_0)$, with $z$ a neighbour of $x_0$, that is, $z \in \overline{C(x_0)}$. Then $(N, v)$ is framed cobordant to $N \setminus \{x_0, z\}$ with the frames $v$. ⟦Chapter7/CancelStep · cancel_step⟧

*The idea.* Bring $x_0$ close to $z$, then cancel the pair in a chart ball around $z$.

*The proof as formalized.*

1. Take a good ball $U_R$ around $z$ whose closure avoids $N \setminus \{z\}$. As $z \in \overline{C(x_0)}$, some $u \in U_{R/4}$ lies in $C(x_0)$, and $u \notin N$ ⟦Chapter7/Reach · exists_goodBall⟧. By reach, move $x_0$ to $u$ with a frame of the sign $s$ of $v(x_0)$ ⟦Chapter7/Reach · exists_reach⟧.
2. In the chart at $z$, $\varphi(u)$ and $\varphi(z)$ are $c_0 \pm aw_0$, with $c_0$ their midpoint, $a = |\varphi(u) - \varphi(z)|/2$, and $w_0$ the unit vector from $\varphi(z)$ to $\varphi(u)$. As $|\varphi(u) - \varphi(z)| < R/4$, we get $|c_0 - \varphi(z)| = a < R/8$ and $8a \le R$.
3. Let $\varepsilon$ be the sign of V7.14 for the chart at $z$, that of the identity of $\mathbb R^m$ from $o_z$ to the standard orientation. If $s = \varepsilon$, cancel with $w = w_0$, $x_1 = u$, $x_2 = z$. If $s = -\varepsilon$, cancel with $w = -w_0$, $x_1 = z$, $x_2 = u$. Either way the standard frames have the signs of the current frames, so two changes of frame, each a reach from a point to itself, install them ⟦Chapter7/CancelStep · framedCobordant_of_frames⟧. The cancellation is V7.14 ⟦Chapter7/Cancel · exists_cancel⟧, and transitivity chains the move, the two frame changes, and the cancellation ⟦Chapter7/Equiv · FramedCobordant.trans⟧.

Removing a pair of opposite signs leaves the signed count unchanged ⟦Chapter7/CancelStep · count_of_remove_two⟧.

### V7.16 Framed 0-manifolds with the same signed count

**Theorem (V7.16).** Let $m \ge 1$ and let $M$ be connected. Two framed $0$-manifolds of $M$ with the same signed count are framed cobordant. ⟦Chapter7/Main · framedCobordant_of_count_eq⟧

*The idea.* Cancel neighbouring pairs of opposite sign until each side has one sign. Equal counts then force the same sign and the same number of points. Match the frames at common points, then gather the remaining points of one side onto the other.

*The proof as formalized.* The proof is an induction on the total number of points $|F| + |G|$ ⟦Chapter7/Main · framedCobordant_of_count_eq⟧.

1. *Both signs occur in $F$.* Apply the neighbour lemma in $M$ to the set $B$ of points with the sign of a given point. It yields $x_0 \in B$ with a neighbour $z \notin B$, necessarily of the opposite sign ⟦Chapter7/Main · exists_opposite_neighbour⟧. The cancel step removes both. The count is unchanged and the number of points drops by two ⟦Chapter7/Main · card_of_remove_two⟧. The same is done for $G$, using symmetry (V7.4) ⟦Chapter7/Equiv · FramedCobordant.symm⟧.
2. *One sign on each side.* If $F$ is empty, so is $G$, as a nonempty $G$ has count $|G|s_G \ne 0$; then $F = G$ ⟦Chapter7/Main · count_of_empty⟧. Likewise with $F$ and $G$ exchanged. Otherwise the counts are $|F|s_F$ and $|G|s_G$ ⟦Chapter7/Gather · count_of_const_sign⟧, and equality forces $s_F = s_G =: s$ and $|F| = |G|$.
3. *Matching frames.* At a common point where the frames differ, a reach from the point to itself installs the frame of $G$. Induction on the number of such points gives $F' \sim F$ with all signs $s$, $|F'| = |G|$, and the frames of $G$ at common points ⟦Chapter7/Gather · GInv⟧ ⟦Chapter7/Gather · exists_matched⟧.
4. *Gathering.* Then $F' \sim G$ ⟦Chapter7/Gather · gather⟧, by induction on the number of *unmatched* points of $F'$, those not in $G$. If there are none, the sets coincide (same cardinality), so do the frames, and reflexivity applies. Otherwise, within one gathering step, neighbours are taken relative to the fixed set $N = F' \cup G$. The chain lemma with $B = F'$ gives a chain with interior in $F'$ from an unmatched point $x$ of $F'$ to an unmatched point $z$ of $G$ ⟦Chapter7/Chain · exists_chainRel⟧. Take a shortest one, ending in $\dots, w, z$.

   One step is always possible. If $u \in F'$ has a neighbour $z \in G \setminus F'$ relative to $N$, then $z$ lies in the component of $u$ relative to $F'$, since removing fewer points only enlarges components. So reach moves $u$ onto $z$ with the frame of $G$ ⟦Chapter7/Gather · gather_move⟧. If $w$ is unmatched, moving $w$ onto $z$ leaves one unmatched point fewer. If $w \in G$, move $w$ onto $z$ anyway. The unmatched points do not change, but the old place of $w$ is now a vacant point of $G$. By minimality the chain from $x$ to $w$ did not visit $w$ earlier ⟦Chapter7/Chain · chainRel_diff'⟧, so it is a strictly shorter chain in the new configuration. An inner induction on the length of the shortest chain concludes ⟦Chapter7/Gather · gather_step⟧.

*Why chains are needed, and when.* For $m \ge 2$ the complement of a finite set in a connected manifold is connected, every point of $N$ is a neighbour of every other, and shortest chains have length one. On a circle, $C(x)$ is the open arc between the two points of $N$ adjacent to $x$. Let $F = \{x, p, q\}$ and $G = \{p, q, z\}$ lie in the cyclic order $p, x, q, z$. The unmatched $x$ has only matched neighbours and cannot reach $z$. The chain $x, q, z$ first moves $q$ onto $z$, then $x$ onto the old place of $q$. The formal proof is uniform in the dimension: it neither knows nor needs that chains are short when $m \ge 2$ ⟦Chapter7/Gather · gather_step⟧.

### V7.17 The Hopf theorem

**Theorem (V7.17).** Degrees are taken with respect to $o$ and the orientation of Chapter 5 on $S^m$.

(a) Let $m \ge 1$ and let $M$ be connected. If $f, g : M \to S^m$ are smooth and $\deg f = \deg g$, then $f$ and $g$ are smoothly homotopic. ⟦Chapter7/Hopf · hopf_homotopic⟧

(b) Let $m \ge 1$. For every $d \in \mathbb Z$ there is a smooth $f : M \to S^m$ with $\deg f = d$. ⟦Chapter7/Hopf · exists_map_of_deg⟧

Nonemptiness of $M$ is a standing hypothesis; in (a) connectedness implies it. Part (b) does not assume connectedness ⟦Chapter7/Hopf · exists_map_of_deg⟧.

*The idea.* For (a), degrees are signed counts, equal counts give framed cobordant Pontryagin manifolds, and these come from homotopic maps. For (b), build a framed $0$-manifold with the right count and realize it by Theorem C.

*Proof of (a).* By Brown's theorem $f$ and $g$ have regular values $y$ and $y'$ ⟦Chapter2/Brown · dense_regularValues⟧, and since $m \ge 1$ there are positive bases $e$ at $y$ and $e'$ at $y'$ ⟦Chapter7/Lemma2 · exists_posBasis⟧. By V7.12 the two Pontryagin manifolds have signed counts $\deg f = \deg g$. By V7.16 they are framed cobordant, and the "if" half of Milnor's Theorem B (V7.11) gives a smooth homotopy ⟦Chapter7/ThmAconv · smoothHomotopic_of_framedCobordant⟧. The converse, that smoothly homotopic maps have equal degrees, is Milnor's Theorem B of §5 (V5.7) ⟦Chapter5/Degree · deg_eq_of_homotopy⟧.

*Adding a point.* Let $m \ge 1$, let $(N, v)$ be a framed $0$-manifold, let $x \notin N$, and let $v_x$ be a frame at $x$. There is a framed $0$-manifold with points $N \cup \{x\}$, frame $v$ on $N$, and frame $v_x$ at $x$ ⟦Chapter7/AddPoint · exists_add_point⟧. Take a good ball around $x$ avoiding $N$, the dual tuple $\tau_0$ of $v_x$, and a lower bound for $B_{\tau_0}$ ⟦Chapter7/AddPoint · exists_lower_bound_basisCLM⟧. Glue the moving family with constant tuple $\tau_0$ and constant centre $\varphi_x(x)$ onto a Theorem-C map of $(N, v)$ that is south outside a compact subset of $M \setminus \overline{U_R}$. At time $0$ the glued map has north as a regular value with preimage $N \cup \{x\}$, frames $v$ on $N$ (germs), and $v_x$ at $x$ (V7.8). Only a map is involved here, no cobordism.

*Proof of (b).* A finite set always misses a point of $M$. $M$ is nonempty, and for $m \ge 1$ the chart segment $t \mapsto \varphi^{-1}(\varphi(y_0) + te_1)$, $0 < t < r$, is injective, so $M$ is infinite ⟦Chapter7/Hopf · exists_notMem_finite⟧. Let $s = 1$ if $d \ge 0$ and $s = -1$ otherwise. Starting from the empty framed $0$-manifold ⟦Chapter7/Hopf · emptyFramed⟧, add $|d|$ points with frames of sign $s$ ⟦Chapter7/Hopf · exists_framedSub_of_card⟧. Theorem C with $W = M$ realizes the result $F$ as the Pontryagin manifold of a map $k$ at the north pole for the basis $ce'$, with $e'$ positive there. V7.12 is stated for $e'$ itself. The Pontryagin frames for $ce'$ are $c$ times those for $e'$, and positive rescaling keeps signs, since $\det(cI) = c^m > 0$ ⟦Chapter7/Hopf · frameSign_smul⟧ ⟦Chapter7/Hopf · count_pontryagin_smul⟧. So $\deg k$ is the signed count of $F$, namely $|d|s = d$.

### V7.18 and V7.19 Orientability, transport, and the reversing loop of balls

Milnor's clause at the end of §7 needs a vocabulary his book does not build. An orientation of a manifold is V5.0, his own notion; what is missing is orientability as a property, and its characterization by loops. For this section and the four that follow, $M$ is a manifold modelled on a finite-dimensional $E$ with $\dim E = m$ — for the theorem at the end, the submanifold of the standing notation, but the machinery asks for nothing of the kind. Call $M$ *orientable* if it carries an orientation in the sense of V5.0 ⟦Chapter7/Orientable · IsOrientable⟧.

*Transport.* The derivative at $y$ of the extended chart centred at $x$ is a linear isomorphism, so exactly one orientation of the model space at $y$ is carried by it to a given orientation at $x$: the *transport* $\operatorname{tr}_{x \to y}$ through that chart, an involution which anticommutes with reversal ⟦Chapter7/OrientTransport · orTransport⟧. An orientation of $M$ is exactly a family of orientations of $E$, one at each point, which near every point is the transport of its value at that point — the continuity condition of V5.0 read backwards ⟦Chapter7/OrientTransport · Orient.isTransportSection⟧ ⟦Chapter7/OrientTransport · Orient.ofTransportSection⟧.

*Hops and chains.* A *hop* from $x$ to $y$ is a chart whose source contains both, together with a record of which chart it is ⟦Chapter7/OrientTransport · ChartHop⟧; a *chain* is a finite sequence of hops ⟦Chapter7/OrientTransport · ChartChain⟧. Chains compose and reverse, transport along a composite is the composite of the transports, and transport along the reverse undoes the chain. In a connected manifold any two points are joined by a chain, the reachable set being open and closed. A chain-loop *reverses* if its transport carries some orientation at the base point to the opposite one; which of the two is tested is immaterial ⟦Chapter7/Orientable · ChartChain.Reverses⟧. *A step the design did not foresee:* a hop must record which chart it travels through. The naive relation "some chart contains both points" induces no well-defined transport, and the obvious symmetric repair is wrong, precisely because two charts can disagree on a disconnected overlap.

**Theorem (V7.18).** Let $M$ be connected. If no chain-loop at a point of $M$ reverses, then $M$ is orientable: transport a fixed orientation from the base point, the answer being unambiguous because two chains to the same point differ by a loop ⟦Chapter7/Orientable · isOrientable_of_forall_not_reverses⟧. Contrapositively, a connected non-orientable manifold carries at every point a chain-loop that reverses *every* orientation there ⟦Chapter7/Orientable · exists_reverses_of_not_isOrientable⟧. A connected orientable manifold has exactly two orientations, a given one and its pointwise reverse ⟦Chapter7/Orientable · Orient.or_eq_or_eq_neg⟧.

*A warning, and it is a genuine one.* The other direction — that an orientable $M$ admits no reversing chain-loop — is **false** for an orientation in the sense of V5.0, whose compatibility is a condition only *near* each point. On $\mathbb R$ take the atlas consisting of the identity together with the chart that is $x$ on $(-1, 0)$ and $3 - x$ on $(1, 2)$. This is a smooth structure on $\mathbb R$, which is orientable; yet the orientation that is standard except reversed on $(1, 2)$ satisfies the condition of V5.0, while the loop out through the second chart and back through the identity reverses. The culprit is that a chart source may be disconnected. The converse does hold for the stronger notion of an orientation coherent with every chart on the *whole* of that chart's source, and for connected $M$ the absence of reversing chain-loops is equivalent to the existence of such an orientation ⟦Chapter7/Orientable · IsChartCoherent⟧ ⟦Chapter7/Orientable · exists_isChartCoherent_iff_forall_not_reverses⟧.

*The repair.* A *chart ball* about $c$ is the preimage under the extended chart at $c$ of a round ball about the chart image of $c$; when that ball lies in the chart's target, the chart ball is connected, which is the one property a chart source lacks ⟦Chapter7/OrientBall · chartBall⟧ ⟦Chapter7/OrientBall · isPreconnected_chartBall⟧. A *ball hop* is a hop through such a ball containing both its endpoints, a *ball chain* a chain all of whose hops are of that kind ⟦Chapter7/OrientBall · BallHop⟧ ⟦Chapter7/OrientBall · ChartChain.IsBall⟧. The whole transport algebra applies verbatim; only the predicate has to be shown closed under the constructions.

**The key lemma.** *Every* orientation of $M$ is ball-coherent: transport along a ball hop carries the orientation at one end to the orientation at the other ⟦Chapter7/OrientBall · BallHop.transport_or⟧. On a chart ball about $c$ the sign of the orientation at $z$ against the orientation at $c$, read through the derivative of the chart at $c$, takes only the values $\pm 1$, is locally constant by the continuity condition of V5.0, and equals $1$ at $c$; and a locally constant function on a connected set is constant. For a chart source the conclusion fails, and the counterexample above is exactly why.

**Theorem (V7.19), the exact dichotomy.** For connected $M$ and any base point, $M$ is orientable *if and only if* no loop of chart balls at that point reverses ⟦Chapter7/OrientBall · isOrientable_iff_forall_not_reverses_isBall⟧ ⟦Chapter7/OrientBall · ballReachable_of_preconnectedSpace⟧, and a connected non-orientable $M$ carries at every point a ball loop reversing every orientation there ⟦Chapter7/OrientBall · exists_isBall_reverses_of_not_isOrientable⟧.

Two things are gained. Unlike V7.18 the equivalence now holds with no auxiliary notion, so a reversing ball loop is a genuine obstruction to orientability and not a symptom of a badly chosen atlas; and the loops run through round balls, which is what the moving machinery of V7.13 can follow.

*Hidden hypotheses.* V7.18 needs none at all: no boundarylessness, no Hausdorffness, no second countability, and $M$ may be empty. V7.19 needs the model boundaryless, on 24 of its 61 declarations and for two independent reasons, both of which are that a chart target must be open: a ball inside the target has to exist at all, and the sign of a chart derivative has to be locally constant. Everything about a chart ball that is *given* needs it not.

### V7.20 and V7.21 The chart sign of a frame, and the sign of a chain

The sign of a frame (V7.12) is measured against an orientation of $M$, which a non-orientable $M$ does not have. So the local lemmas must be restated with a sign that mentions none, and the chains of V7.19 must be given an arithmetic.

*Three signs, no orientation.* The *chart sign* of a frame $v$ at $x$ relative to a centre $x_c$ is the sign of the determinant of $v$ read in the chart at $x_c$ ⟦Chapter7/ChartSign · Framed.chartSign⟧; the *self sign* is the case $x_c = x$ ⟦Chapter7/ChartSign · Framed.selfSign⟧; the *Jacobian sign* is the sign of the determinant of the derivative at $x$ of the chart at $x_c$ ⟦Chapter7/ChartSign · Framed.jacSign⟧. All three are $\pm 1$ for a tangent independent frame at a point of the chart's source, none mentions an orientation, and
$$\text{chart sign} = \text{Jacobian sign} \cdot \text{self sign},$$
with Jacobian sign $1$ at the centre ⟦Chapter7/ChartSign · Framed.chartSign_eq_jacSign_mul_selfSign⟧.

**The bridge (V7.20).** For any orientation $o$ of $M$,
$$\operatorname{sign} v(x) = \varepsilon(x)\cdot\text{self sign}(v, x),$$
where $\varepsilon(x)$ is the sign of the identity of $\mathbb R^m$ read from the standard orientation to $o_x$, and so depends on the point and not on the frame ⟦Chapter7/ChartSign · Framed.orEps⟧ ⟦Chapter7/ChartSign · Framed.frameSign_eq_orEps_mul_selfSign⟧. *The sign of a frame against an orientation of the manifold is the determinant sign of the frame read in one chart, times a factor depending only on the point.* That is what lets the local machinery run without an orientation, since every local proof compares a product of two such signs and the factor cancels. On a chart ball the same holds with the hub's factor ⟦Chapter7/ChartSign · Framed.frameSign_eq_orEps_hub_mul_chartSign⟧, so equality of frame signs at two points of a ball is equality of their chart signs relative to the hub.

Two consequences remove case splits from the sections above. Frames of both chart signs exist at *every* point, with no reference to a global sign ⟦Chapter7/ChartSign · Framed.exists_frame_of_selfSign⟧ — the proof of "frames of both signs at a point" collapses from sixty-five lines to one — and a frame at $x$ may be carried to any other point of the same chart's source as the same frame read in that chart, hence with the same chart sign ⟦Chapter7/ChartSign · Framed.exists_frame_transport⟧.

*What this does to V7.13, V7.14 and V7.15.* They are restated in these terms. The glued moving and cancelling homotopies no longer mention an orientation at all: six theorems lose two hypotheses each, and a lemma asserting that a chart derivative is bijective, whose hypothesis "the chart preserves orientation" was spurious, is deleted in favour of the general one. The sign of the frame at a zero of the cancelling map becomes flatly the sign of the signed distance, where before it carried a factor depending on the orientation. Four declarations cannot be restated in place, because the cancel step and the Hopf theorem call them in their oriented form; the sign-free statement then carries the proof and the oriented one is a short corollary beside it, so that no proof is duplicated. The bookkeeping costs 131 lines and buys everything below. *A better primitive than expected:* the self sign needs no chart-membership hypothesis, which is what makes it usable in the open-and-closed arguments of V7.23.

**The sign dictionary (V7.21).** Transport across a chart is multiplication by the Jacobian sign ⟦Chapter7/BallChainSign · jacSign⟧; the sign of a hop is the product of the two Jacobian signs of its chart at the two endpoints ⟦Chapter7/BallChainSign · hopSign⟧; the sign of a chain is the product of the signs of its hops ⟦Chapter7/BallChainSign · chainSign⟧. The sign of a composite is the product, a chain and its reverse have the same sign, transport along a chain is multiplication by its sign, and **a loop reverses exactly when its sign is $-1$** ⟦Chapter7/BallChainSign · chainSign_comp⟧ ⟦Chapter7/BallChainSign · chainSign_reverse⟧ ⟦Chapter7/BallChainSign · ChartChain.transport_eq_signAct⟧ ⟦Chapter7/BallChainSign · ChartChain.reverses_iff_chainSign⟧. The dichotomy of V7.19 thereby becomes arithmetic. All of it holds for arbitrary chart chains, not only ball ones, at no extra cost.

**The transition cocycle.** For two chart centres $p$, $q$ and a point $y$ in both their sources, the product of the two Jacobian signs at $z$ is locally constant in $z$ near $y$ ⟦Chapter7/BallChainSign · eventually_jacSign_mul_jacSign_eq⟧. Neither factor is: each reads a fixed chart through the moving chart at $z$. But in the product the moving chart cancels, and what is left is the determinant sign of the fixed smooth transition $\varphi_p \circ \varphi_q^{-1}$, continuous and invertible, hence of locally constant sign. This is the technical key of the two sections that follow.

**Chains that avoid a set.** A hop *runs inside* a set $C$ if the closed chart ball of its radius lies in $C$ ⟦Chapter7/BallChainSign · ChartChain.IsBallIn⟧. For $C$ open and preconnected any two of its points are joined by a chain of hops running inside $C$ ⟦Chapter7/BallChainSign · exists_isBallIn⟧, and such a chain automatically avoids every set disjoint from $C$ — indeed each of its closed balls does ⟦Chapter7/BallChainSign · exists_isBallIn_avoiding⟧. Two hypotheses are weaker than the design asked: the avoided set need not be closed, only disjoint from the region, and the region need only be preconnected. One had to be added: avoidance is phrased through the *closed chart ball* and not through the topological closure of the ball, because on a non-Hausdorff manifold the closure of a chart ball need not lie in its chart — on the line with two origins, the closure of an interval about one origin contains the other. The closure form is given separately under Hausdorffness, which is free in this chapter.

### V7.22 The reversing loop away from a finite set

A framed $0$-manifold is a finite set of points, and the loop that is to flip the frame at one of them must not disturb the others. So the dichotomy has to be run on the complement of a finite set.

**Theorem (V7.22).** Let $2 \le m$. A punctured chart ball is connected ⟦Chapter7/Puncture · isConnected_chartBall_diff_singleton⟧; the complement of a finite set in a connected $M$ is connected ⟦Chapter7/Puncture · isConnected_compl_finite⟧, and nonempty as soon as $0 < m$, a nonempty open subset of a manifold of positive dimension being infinite ⟦Chapter7/Puncture · infinite_of_isOpen⟧; and a family of orientations that is ball-coherent on the complement of a finite set $P$ agrees off $P$ with an orientation of the whole of $M$ ⟦Chapter7/Puncture · IsBallCoherentOn⟧ ⟦Chapter7/Puncture · extend_ballCoherent⟧. Hence **the punctured dichotomy:** a connected non-orientable manifold of dimension at least two has, at every point outside a given finite set, a loop of chart balls at that point missing the set and of chain sign $-1$. ⟦Chapter7/Puncture · HasReversingBallLoop⟧ ⟦Chapter7/Puncture · hasReversingBallLoop_of_not_isOrientable⟧

**The idea.** Everything rests on the extension lemma, and that is where the cocycle of V7.21 earns its keep. The value of the extended orientation at a puncture $p$ is the value at a nearby point, transported back to $p$. It is well defined because that assignment is locally constant on a punctured ball about $p$ — the two Jacobian signs being separately discontinuous and jointly locally constant — and because a punctured ball is connected.

*Two things came out cleaner than expected.* Well-definedness holds at *every* point, not only at the punctures, so the extension is one total function with no case split, and the transport condition is then checked at every point at once. And no separation hypothesis is needed anywhere: charts give $T_1$ for free.

*The dimension hypothesis is sharp, not a convenience.* For $m = 1$ a punctured ball is an interval minus an interior point, and $\mathbb R \setminus \{0\}$ is a disconnected complement of a finite set in a connected $1$-manifold; for $m = 0$ a punctured ball is empty. This section therefore keeps $2 \le m$, and keeps it sharply. It is the only place in the whole of the mod 2 theory that wants it, which is why V7.28 can delete it from everything above: the theorems that appeal to this one *derive* the hypothesis from non-orientability instead of assuming it.

*Two small facts had to be proved:* that no point of a manifold of positive dimension is isolated, and that a locally constant function on a connected set is constant — Mathlib's version of the latter wants a discrete target, and the two orientations of a vector space carry no topology.

### V7.23 to V7.25 The slide, the flip, and the count modulo 2

Now Milnor's clause itself, and then the endgame without signs. Throughout, $m \ge 1$ and $(N, v)$ is a framed $0$-manifold of $M$.

**The slide (V7.23).** Given a chain of chart balls from a point $x_0$ of $N$ to $y$, none of whose balls meets any other point of $N$, $(N, v)$ is framed cobordant to a framed $0$-manifold with point set $(N \setminus \{x_0\}) \cup \{y\}$, the same frames elsewhere, and self sign at $y$ equal to the chain sign of V7.21 times the self sign at $x_0$. ⟦Chapter7/Slide · Framed.exists_slide⟧

**The flip.** If the chain is a *loop* at $x_0$ of chain sign $-1$, the point set and all the other frames are literally unchanged and the self sign at $x_0$ is reversed. ⟦Chapter7/Slide · Framed.exists_flip⟧ **This is Milnor's clause.**

With a reversing loop in hand, the frame at a point may then be replaced by *any* tangent independent frame, and the point may be moved anywhere in its component of $M \setminus (N \setminus \{x_0\})$ with any frame: this is V7.13 with the orientation and its sign hypothesis simply deleted ⟦Chapter7/Slide · Framed.exists_reach_any⟧ ⟦Chapter7/Slide · Framed.exists_frame_free⟧ ⟦Chapter7/Slide · Framed.exists_reach_free⟧. No orientation, no connectedness, no $2 \le m$ and no Hausdorffness occur in the file; the only dimension hypothesis is $0 < m$, and the reversing loop is a hypothesis, in exactly the form V7.22 produces it, so the two halves join with no glue.

*Where one ball hop is not one move.* A move of V7.13 needs its two points inside a quarter-radius ball whose closed ball fits in the chart, while the endpoints of a hop can be almost a full diameter apart, and the chart target need not contain a ball four times as large. So each hop is subdivided, and the sign must be shown not to notice the subdivision. That needs an open-set form of the cocycle lemma and a change-of-hub lemma, and it is where the invariant carried across a hop turns out to be the chart sign at the hop's own hub. *An improvement on the design:* the sign-free reach lemma needs the reversing loop only at the starting point, not at the target.

**Cancellation with no condition on the frames (V7.24).** Two framed $0$-manifolds with the same point set and the same frames away from two distinct points are framed cobordant, with **no** condition relating the frames at those two points ⟦Chapter7/CancelFree · Framed.framedCobordant_of_frames_free⟧. Hence *any* two distinct points of $N$, one in the closure of the component of the other, can be cancelled — V7.14 with its opposite-sign hypothesis deleted outright ⟦Chapter7/CancelFree · Framed.cancel_step_free⟧ — and if $N$ has two distinct points and $M$ is connected, some two of them are neighbours in that sense, which is V7.15 with the partition $\{x\} \sqcup (N \setminus \{x\})$ in place of a partition by sign ⟦Chapter7/CancelFree · Framed.exists_neighbour_pair⟧.

*This is where the design was most wrong, and the error is instructive.* It prescribed choosing an arriving frame of the opposite sign and replacing the old case split by a new one. Neither is needed. The cancelling homotopy supplies its own two frames, of chart signs $+1$ and $-1$ — that is the computation of V7.14 read through V7.20 — and "frames are free at two points" connects any configuration to that one. So the arriving frame may be arbitrary, and the case split *disappears* rather than being replaced. The sign-free cancel step is therefore shorter than the signed one.

**The count modulo 2 (V7.25).** The *count modulo 2* of a framed $0$-manifold is the cardinality of its point set read in $\mathbb Z/2$; no orientation occurs in the definition, in contrast with V7.12 ⟦Chapter7/CountMod2 · Framed.countMod2⟧. Two framed $0$-manifolds of a connected $M$ with the same count modulo 2 are framed cobordant, given reversing ball loops off every finite set ⟦Chapter7/CountMod2 · Framed.framedCobordant_of_countMod2_eq⟧; and the count modulo 2 of the Pontryagin manifold of $f : M \to S^m$ at a regular value is $\deg_2 f$, both being the parity of $\#f^{-1}(y)$ ⟦Chapter7/CountMod2 · Framed.countMod2_pontryagin⟧. Unlike V7.12 this bridge needs nothing of the framing, so the frame may be any independent tuple and not a positive basis. Together these are Milnor's statement that the framed cobordism class is determined by the number of points modulo 2, and they are V7.16 with the signed count replaced by the parity.

*The induction is simpler than the signed one.* V7.16 can cancel only while both signs occur, and needs a separate gathering argument when they do not. Here the induction runs on the cruder condition "two or more points", there is no gathering step at all, and it stops when each side has at most one point, which is then carried onto the other by the reach lemma. That is exactly where the improvement noted above is used: the loop is needed only at the point that moves.

### V7.26 Milnor's theorem for a non-orientable manifold

**Theorem (V7.26).** Let $M \subseteq \mathbb R^{K+1}$ be a compact, nonempty, connected, **non-orientable** submanifold of dimension $m$. Two smooth maps $f, g : M \to S^m$ are smoothly homotopic **if and only if** they have the same degree modulo 2. ⟦Chapter7/HopfMod2 · Framed.hopf_homotopic_mod2⟧

This is the counterpart, at the end of Milnor's §7, of the Hopf theorem V7.17.

*Proof of the easy half.* It is the homotopy invariance of the mod 2 degree, the second assertion of the Theorem of §4 (V4.8), transcribed into the homotopy relation of this chapter ⟦Chapter7/HopfMod2 · degMod2_eq_of_smoothHomotopic⟧ ⟦Chapter7/HopfMod2 · Framed.degMod2_eq_of_smoothHomotopic_sph⟧. It needs no orientation of any kind, no connectedness, and nothing of the dimension beyond $0 < m$, which is only what the mod 2 degree asks of its target.

*Proof of the substantial half, which is Milnor's remark.* By Brown's theorem $f$ and $g$ have regular values $y$ and $y'$ ⟦Chapter2/Brown · dense_regularValues⟧, and since $m \ge 1$ there are positive bases $e$ at $y$ and $e'$ at $y'$ ⟦Chapter7/Lemma2 · exists_posBasis⟧. Form the two Pontryagin manifolds (V7.1). By the parity bridge of V7.25 their counts modulo 2 are $\deg_2 f$ and $\deg_2 g$, hence equal; with the loops supplied by V7.22, the parity classification makes them framed cobordant ⟦Chapter7/HopfMod2 · Framed.framedCobordant_of_card_parity⟧; and the converse half of Theorem B (V7.11), which is itself orientation-free, turns that into a smooth homotopy ⟦Chapter7/HopfMod2 · Framed.smoothHomotopic_of_degMod2_eq⟧.

*Where the orientations are.* The only orientations in the whole argument are orientations of the **target sphere**, which the Pontryagin construction and the converse of Theorem B require. The source carries none, and is assumed not to have one. That is the point of V7.20, and it is what makes every earlier local lemma of this part usable here.

*No hypothesis on the dimension, and how it went.* The statement above has none, as Milnor's has none. Each half wants $0 < m$, which is all the mod 2 degree asks of its target, and each half now gets it from non-orientability along with everything else. Earlier editions of this section carried $2 \le m$ and called it vacuous but unavoidable: vacuous because a connected $1$-manifold is diffeomorphic to the circle or to an interval and all of those are orientable, so that a connected non-orientable manifold has dimension at least two of its own accord; unavoidable because that sentence quotes the classification of one-manifolds, which was not formalized. It now is (Part XII), the deduction is V7.28 below, and because the hypothesis enters at exactly one point — the appeal to V7.22 — each of the three statements of this section that mentions non-orientability derives the bound there in one line instead of assuming it ⟦Chapter7/OneManifoldOrientable · two_le_of_not_isOrientable_slice⟧. V7.22 itself keeps $2 \le m$, sharply, as a statement about punctured balls.

### V7.27 and V7.28 One-manifolds are orientable, and the hypothesis goes

Five statements, whose only purpose is the sentence *a connected non-orientable manifold has dimension at least two*. They are the one place where the rest of the book depends on the Appendix for anything but the boundary count and its arcs, and they are what makes the theorem above match Milnor's, which carries no condition on the dimension. Orientation and orientability are as before: an orientation of $M$ is V5.0's, a choice $o(x)$ of orientation of each tangent space which near every point is carried to the value at that point by the derivative of the chart centred there, and $M$ is orientable when it has one ⟦Chapter7/Orientable · IsOrientable⟧.

*Pulling an orientation back.* For an invertible continuous linear map $T : E \to F$ between spaces of dimension $n$ and an orientation $b$ of $F$, exactly one orientation of $E$ is carried by $T$ to $b$ ⟦Chapter7/OneManifoldOrientable · orPull⟧ ⟦Chapter7/OneManifoldOrientable · orSign_orPull⟧ ⟦Chapter7/OneManifoldOrientable · eq_orPull⟧. Uniqueness holds because a space of dimension $n$ has exactly two orientations, and an isomorphism cannot carry both of them to the same one.

*Two orientations that cost nothing.* If all the charts of $M$ are literally the same partial homeomorphism, every transition is the identity, every sign is $+1$, and a constant family is an orientation ⟦Chapter7/OneManifoldOrientable · Orient.ofConst⟧. And a manifold of dimension $0$ is orientable whatever its charts, because in dimension $0$ every linear map preserves every orientation: the only tuple to test is the empty one ⟦Chapter7/OneManifoldOrientable · orSign_self_eq_one_of_zero⟧ ⟦Chapter7/OneManifoldOrientable · Orient.ofZero⟧.

**Theorem (V7.27), transport.** Let $\Phi : M \to N$ be smooth between manifolds of the same dimension $n$, let $N$ carry an orientation $o_N$, and let $d\Phi_x$ be invertible at every $x$. Then $x \mapsto \operatorname{orPull}(o_N(\Phi x),\, d\Phi_x)$ is an orientation of $M$ ⟦Chapter7/OneManifoldOrientable · Orient.comap⟧ ⟦Chapter7/OneManifoldOrientable · IsOrientable.comap⟧. Nothing else is asked of $\Phi$: it need be neither injective nor surjective nor a local diffeomorphism. In particular orientability travels *backwards* along a diffeomorphism, whose derivative is invertible ⟦Chapter7/OneManifoldOrientable · bijective_mfd_diffeomorph⟧ ⟦Chapter7/OneManifoldOrientable · IsOrientable.of_diffeomorph⟧, and that is the direction the classification hands out.

*The proof is V5.1 read backwards* ⟦Chapter7/OneManifoldOrientable · eventually_orSign_eq_one_of_pullback⟧. Write $\Phi$ in the charts at $x_0$ and at $\Phi x_0$ as a map $g$ of open subsets of the model space. For $x$ near $x_0$ the transition of $N$ at $\Phi x$ composed with $d\Phi_x$ equals $dg$ composed with the transition of $M$ at $x$. The left-hand side has sign $1$, by the definition of the pulled-back family and the compatibility of $o_N$; the right-hand side splits as the sign of $dg$ — locally constant, and $1$ at $x_0$, where $dg = d\Phi_{x_0}$ — times the sign of the transition of $M$. So that last sign is $1$, which is the condition of V5.0.

*The four models of Part XII are oriented.* The line and the closed half-line by constant families, since each carries a single chart ⟦Chapter7/OneManifoldOrientable · orientReal⟧ ⟦Chapter7/OneManifoldOrientable · orientIci⟧. The unit interval **not** by a constant family: Mathlib's manifold structure on $[0,1]$ has two charts, $z \mapsto z$ on $[0,1)$ and $z \mapsto 1 - z$ on $(0,1]$, and their transition reverses orientation, so the family has to flip at the right-hand endpoint and that one transition derivative has to be computed — which is done by factoring the chart at $1$ through the chart at an interior point and the reflection of the model space, an affine map ⟦Chapter7/OneManifoldOrientable · mfd_extChartAt_Icc_top⟧ ⟦Chapter7/OneManifoldOrientable · orientIcc⟧. And the circle not through its own charts at all, but through the unit circle $S^1 \subseteq \mathbb R^2$, which Chapter 8 orients as the boundary of the disk ⟦Chapter8/OrientFrame · sphOrStd⟧: $S^1$ is a nonempty compact Hausdorff connected boundaryless smooth one-manifold, so V.H hands over a diffeomorphism of it with Mathlib's circle and transport carries the orientation across ⟦Chapter7/OneManifoldOrientable · isOrientable_circle⟧ ⟦Chapter7/OneManifoldOrientable · isOrientable_models⟧. That is shorter than either direct route — the transition of the two stereographic charts, or a descent along the periodic parametrization of V.H — because the sphere is oriented already.

**Theorem (V7.27), the consequence.** Every connected Hausdorff σ-compact smooth one-manifold over a boundaryless model is orientable ⟦Chapter7/OneManifoldOrientable · isOrientable_of_finrank_eq_one⟧. The classification (V.J) makes such an $M$ diffeomorphic to the circle if it is compact and to $\mathbb R$ if it is not — the two interval models are excluded because the boundary of $M$ is empty — and orientability travels back along that diffeomorphism ⟦Appendix/Smooth/Main · nonempty_diffeomorph_cases⟧.

**Theorem (V7.28).** With the same hypotheses on $M$ and with $\dim E = m$: if $M$ is **not** orientable then $2 \le m$ ⟦Chapter7/OneManifoldOrientable · two_le_of_not_isOrientable⟧. Dimension $0$ is excluded by the cheap orientation above and dimension $1$ by the theorem just stated; there is nothing else to say.

*In the vocabulary of this part*, with every side hypothesis free: let $M$ be a compact connected slice submanifold of a Euclidean space, charted on $\mathbb R^m$. It is Hausdorff as a subspace of a metric space, σ-compact because it is compact, and its model is boundaryless, so its boundary is empty; if it is non-orientable then $2 \le m$ ⟦Chapter7/OneManifoldOrientable · two_le_of_not_isOrientable_slice⟧. That is the form V7.26 calls, once in each of its three statements.

*The one restriction, and why it costs nothing.* Every transport statement assumes the model of the **source** boundaryless, and it is used in exactly one way: a chart target of the source has to be open in the model space, so that the map read in charts is defined on an open set, has a genuine derivative there, and that derivative is continuous in the point. For a model with boundary the argument would have to be rerun with the derivative within the model's range, and it is not. So the orientability of one-manifolds is available for boundaryless models only — even though all four models of Part XII, the two with boundary included, are oriented above. Nothing in the book needs more: the manifolds of Chapters 7 and 8 are compact slice submanifolds of a Euclidean space, whose model is boundaryless.

### What the formalization taught us

- **No cobordism is built by hand.** Every move, frame change and cancellation is V7.2 applied to a homotopy glued into a chart ball, and even reflexivity is V7.2 applied to a constant homotopy. Milnor's U-shaped arc exists only as a preimage of the north pole ⟦Chapter7/Cancel · exists_cancel⟧ ⟦Chapter7/Reach · FramedCobordant.refl'⟧.
- **Theorem C needs two more parameters.** The map must be south outside a prescribed open set, so that it glues near the frontier of a ball. Its scale must be bounded below, so that the local family and the Theorem-C map share the basis $cb$ ⟦Chapter7/ThmBsupp · exists_map_of_framedSub_subset⟧ ⟦Chapter7/Scale · exists_scale_all⟧.
- **"Since $M$ is connected" is the neighbour lemma.** It uses local connectedness, closed points, and a segment property of chart balls ⟦Chapter7/Neighbour · exists_neighbour⟧ ⟦Chapter7/Segment · ballU_diff_subset_compl'⟧.
- **Dimension one forces chains.** Points of a circle cannot pass one another, so gathering moves the last point of a shortest chain first ⟦Chapter7/Gather · gather_step⟧.
- **Paths become an open–closed argument** on the reachable points of a component. Moves happen only in chart balls where the chart preserves orientation, which exist by chart-continuity of orientations ⟦Chapter7/Reach · exists_reach⟧ ⟦Chapter7/Reach · exists_goodBall⟧.
- **When the two points merge, regularity comes from time.** The slice is singular there, so the time profile must satisfy $\rho' \ne 0$ where $\rho = 0$ ⟦Chapter7/CancelMap · surjective_Dcan⟧ ⟦Chapter7/CancelMap · exists_rho⟧.
- **Standard frames have chart-dependent signs** $\pm\varepsilon$, so a cancellation needs two frame changes first ⟦Chapter7/Cancel · chartSign_cancelH_slice⟧ ⟦Chapter7/CancelStep · framedCobordant_of_frames⟧. The factor $\varepsilon$ is where the orientation enters, and V7.20 shows that it is the only place.
- **The scalar $c$ of Theorem C reaches the degree computation.** It is harmless, because positive rescaling keeps signs ⟦Chapter7/Hopf · count_pontryagin_smul⟧.
- **Every degree is realized without connectedness.** Adding points one at a time needs a point outside every finite set, that is, $M$ infinite, and this is one place where $m \ge 1$ and nonemptiness enter ⟦Chapter7/Hopf · exists_map_of_deg⟧ ⟦Chapter7/Hopf · exists_notMem_finite⟧.
- **Finiteness of framed $0$-manifolds needs no Hausdorff hypothesis.** Compact and discrete suffice ⟦Chapter7/Hopf0 · IsSliceSubmanifold.finite_of_dim_zero⟧.
- **Orientability had to be invented before Milnor's clause could be read.** Neither Mathlib nor this project had it, and the notion of V5.0 is too weak for the converse: an orientation may be compatible near every point and still be reversed by a loop, because a chart source can be disconnected. Chart balls repair it exactly ⟦Chapter7/Orientable · exists_isChartCoherent_iff_forall_not_reverses⟧ ⟦Chapter7/OrientBall · isOrientable_iff_forall_not_reverses_isBall⟧.
- **One sign is only locally constant in company.** Each Jacobian sign reads a fixed chart through the moving chart and jumps; their product reads a fixed transition and does not. Every orientation extended across a puncture rests on that ⟦Chapter7/BallChainSign · eventually_jacSign_mul_jacSign_eq⟧ ⟦Chapter7/Puncture · extend_ballCoherent⟧.
- **Removing a hypothesis shortened the proof.** With the signs deleted the cancel step keeps no case split at all, the cancelling homotopy supplying the two frames the argument needs, and the induction of V7.16 loses its gathering step ⟦Chapter7/CancelFree · Framed.cancel_step_free⟧ ⟦Chapter7/CountMod2 · Framed.framedCobordant_of_countMod2_eq⟧.
- **A vacuous hypothesis is not a cheap one.** $2 \le m$ said nothing, and deleting it cost the whole classification of one-manifolds, because the sentence that makes it vacuous — a connected one-manifold is orientable — is a theorem of the Appendix and not a remark ⟦Chapter7/OneManifoldOrientable · isOrientable_of_finrank_eq_one⟧ ⟦Chapter7/OneManifoldOrientable · two_le_of_not_isOrientable_slice⟧.
- **Orientability travels backwards along any map with invertible derivative**, not only along a diffeomorphism, and that generality is what lets the circle be oriented through the sphere, which Chapter 8 has already oriented, instead of through its own two charts ⟦Chapter7/OneManifoldOrientable · Orient.comap⟧ ⟦Chapter7/OneManifoldOrientable · isOrientable_circle⟧.


## Part VIII. Problems 1–12: degrees, approximation and bundles (Milnor §8)

Milnor's first twelve problems fall into three groups. Problems 1, 2, 6 and 7 compute degrees. Problems 3, 4, 5 and the second half of 12 replace continuous maps and homotopies, into a sphere or a compact manifold, by smooth ones. Problems 8 to 11 build new manifolds in Euclidean space: products, graphs, tangent and normal bundles. The third group rests on one criterion, proved once: a set that is locally the zero set of a submersion is a submanifold, whose tangent space is the kernel of the derivative. The approximation theorems rest on one analytic tool, a Stone–Weierstrass theorem for restrictions of smooth functions. Problem 11 reuses the nearest-point retraction of Part IV and adds the compactness argument that makes $(x, v) \mapsto x + v$ injective on a tube of uniform thickness.

**Map of the part.**

- `Chapter8/DegComp`: Problem 1, the degree of a composition.
- `Chapter8/PolyDeg`: an orientation of the Riemann sphere, and Problem 2.
- `Chapter8/NearMaps`: Problem 3, the normalized-chord homotopy.
- `Chapter8/Approx`: smooth Stone–Weierstrass on compact sets; normalizing a nearby vector.
- `Chapter8/Smoothing`: Problems 4 and 5.
- `Chapter8/SphereMaps`: Problems 6 and 7; even maps have even degree.
- `Chapter8/LocalSlice`: local zero sets of submersions are submanifolds (V8.0 (i)).
- `Chapter8/ProdGraph`: Problems 8 and 9.
- `Chapter8/TangentBundle`: Problem 10.
- `Chapter8/NormalBundle`: Problem 11, including $r(x + v) = x$.
- `Chapter8/Retraction`: the retraction as a smooth map into $M$; the approximation half of Problem 12.
- `Chapter8/Nearest`: the nearest-point half of Problem 12.

*Conventions.* The sphere $S^p$ is the level set $\{y \in \mathbb R^{p+1} : \langle y, y \rangle = 1\}$ with its slice structure; in degree computations it carries the orientation of §5 on both sides ⟦Chapter5/HairyBall · Sph⟧ ⟦Chapter5/HairyBall · sphOr⟧. The normalization $\nu(y) = y/\|y\|$ is completed by a fixed base point at $y = 0$; composed with a smooth map that never vanishes, it gives a smooth map into $S^p$ ⟦Chapter6/Region · nv0⟧ ⟦Chapter6/Region · contMDiff_nv0_comp⟧. The smooth step is Mathlib's $\sigma(t) = e^{-1/t}/(e^{-1/t} + e^{-1/(1-t)})$ on $(0,1)$, with $\sigma = 0$ for $t \le 0$ and $\sigma = 1$ for $t \ge 1$. Smooth homotopies are maps on $X \times \mathbb R$ (§0.8), so every straight-line homotopy below is reparametrized by $\sigma$: the parameter then only takes values in $[0,1]$, where the estimates hold, and the ends are still $t = 0$ and $t = 1$.

### V8.1 Problem 1: the degree of a composition

> **Theorem.** Let $M$, $N$, $P$ be oriented smooth manifolds without boundary, modelled on real vector spaces of the same finite dimension $n$ that lie in a common universe. Let $M$ and $N$ be compact, Hausdorff and second countable, $P$ Hausdorff, and $N$ and $P$ preconnected (connected or empty). For smooth $f : M \to N$ and $g : N \to P$,
> $$\deg(g \circ f) = \deg g \cdot \deg f.$$
> ⟦Chapter8/DegComp · deg_comp⟧

The universe condition is a formality: the degree of Part III is defined for model spaces in one universe, as all Euclidean spaces are.

*The idea.* Count the preimages of a point $z$ that is regular for both $g$ and $g \circ f$. They fall into groups according to their image under $f$, and each group is a signed count for $f$.

*The proof as formalized.*

1. If $P$ is empty, there is no regular value, and both sides are $0$ by the definition of the degree ⟦Chapter5/Degree · deg⟧.
2. The regular values of $g \circ f$ are dense by Brown's theorem, which uses that $M$ is second countable. Those of $g$ form an open set, as $N$ is compact and $P$ Hausdorff, and this set is nonempty, being dense in $P \ne \emptyset$ by Brown's theorem again ($N$ is second countable). So some $z$ is regular for both maps ⟦Chapter2/Brown · dense_regularValues⟧ ⟦Chapter6/RegularOpen · isOpen_regularValues⟧.
3. Every $y \in g^{-1}(z)$ is a regular value of $f$. For $x \in f^{-1}(y)$ the map $d(g\circ f)_x = dg_y \circ df_x$ is onto, hence one-to-one since the dimensions agree; so $df_x$ is one-to-one, hence onto. This step does not use the regularity of $z$ for $g$ ⟦Chapter8/DegComp · isRegularValue_of_isRegularValue_comp⟧.
4. The fibres $g^{-1}(z)$ and $(g \circ f)^{-1}(z)$ are finite (regular values, compact domains), hence so is every $f^{-1}(y) \subseteq (g \circ f)^{-1}(z)$, and $(g \circ f)^{-1}(z)$ is the disjoint union of the $f^{-1}(y)$, $y \in g^{-1}(z)$.
5. Compute both degrees at $z$, and $\deg f$ at each $y$ separately. Regrouping the finite sum over the disjoint union gives
$$\deg(g\circ f) = \sum_{y \in g^{-1}(z)}\ \sum_{x \in f^{-1}(y)} \operatorname{sign} d(g\circ f)_x, \qquad \deg g \cdot \deg f = \sum_{y \in g^{-1}(z)} \operatorname{sign} dg_y \sum_{x \in f^{-1}(y)} \operatorname{sign} df_x,$$
and the two double sums agree term by term because signs multiply, $\operatorname{sign} d(g\circ f)_x = \operatorname{sign} dg_{f(x)} \cdot \operatorname{sign} df_x$ ⟦Chapter6/SignLemmas · signAt_comp'⟧.

*What the book leaves implicit.* $N$ must be compact for $\deg g$ to make sense, and the same compactness makes the regular values of $g$ open, which is how the common regular value is found ⟦Chapter8/DegComp · deg_comp⟧.

### V8.2 Problem 2: polynomials on the Riemann sphere

As in Part I, the Gauss sphere is replaced by the Riemann sphere $\hat{\mathbb C} = \mathbb C \cup \{\infty\}$ with the charts $z$ and $1/z$, and a polynomial $P$ of positive degree by its extension $\hat P$ with $\hat P(\infty) = \infty$, which is smooth ⟦Chapter1/FTA · polyMap⟧ ⟦Chapter1/FTA · contMDiff_polyMap⟧. Positive degree is used in the proof of smoothness at $\infty$. (For a constant polynomial the extension is not even continuous there; this remark is not formalized.)

The sphere must first be oriented: every point gets the standard orientation $(1, i)$ of $\mathbb C = \mathbb R^2$ ⟦Chapter8/PolyDeg · riemannOr⟧. Continuity asks that near each point $x$ the derivative of the chart at $x$, read in the chart at a nearby point, have sign $+1$. The formal proof computes it case by case: it is the identity when both charts are of the same kind, and multiplication by $-1/u^2$ when the chart at $\infty$ is read near a finite point $u \ne 0$ ⟦Chapter8/PolyDeg · exists_hasMFDerivAt_extChartAt⟧. Multiplication by $w \ne 0$ is a real-linear map of determinant $|w|^2 > 0$, so its sign is $+1$ ⟦Chapter8/PolyDeg · det_cmul⟧ ⟦Chapter8/PolyDeg · orSign_complexMul⟧. The Riemann sphere is compact, Hausdorff, connected, and second countable as a compact manifold modelled on $\mathbb C$, so Part III applies ⟦Chapter8/PolyDeg · instSecondCountableTopologyRiemannSphere⟧.

> **Theorem.** If $P \in \mathbb C[z]$ has degree $n \ge 1$, then $\deg \hat P = n$, for the orientation above on both sides. ⟦Chapter8/PolyDeg · deg_polyMap⟧

*The idea.* Over a regular value $y \in \mathbb C$ the preimages are the simple roots of $P - y$, each counted with sign $+1$ because complex multiplication preserves orientation.

*The proof as formalized.* The candidate critical values, $\infty$ and the values of $P$ at the zeros of $P'$, form a finite set; as $\mathbb C$ is infinite, some $y \in \mathbb C$ avoids it and is a regular value ⟦Chapter1/FTA · critVals_finite⟧ ⟦Chapter1/FTA · isRegularValue_of_notMem_critVals⟧. The fibre $\hat P^{-1}(y)$ is the set of roots of $P - y$. At each root $z$, $P'(z) \ne 0$ and the derivative of $\hat P$ is multiplication by $P'(z)$, of sign $+1$ ⟦Chapter8/PolyDeg · signAt_polyMap_coe⟧. So $\deg \hat P$ is the number of distinct roots of $P - y$. A multiple root would be a zero of $P'$ where $P$ takes the value $y$, which the choice of $y$ excludes; so the roots are simple, and their number is $\deg(P - y) = n$ by algebraic closedness ⟦Chapter8/PolyDeg · deg_polyMap⟧.

### V8.3 Problem 3: the normalized chord

> **Theorem.** Let $f, g : X \to S^p$ satisfy $\|f(x) - g(x)\| < 2$ for all $x$. If $X$ is a topological space and $f$, $g$ are continuous, they are homotopic. If $X$ is a smooth manifold, modelled on any real normed space (no Hausdorff, countability or boundary assumptions), and $f$, $g$ are smooth, they are smoothly homotopic. ⟦Chapter8/NearMaps · homotopic_of_norm_sub_lt_two⟧ ⟦Chapter8/NearMaps · smoothHomotopic_of_norm_sub_lt_two⟧

*The idea.* On the unit sphere, $\|a - b\| < 2$ means $b \ne -a$. The chord from $a$ to $b$ then misses the origin and can be projected radially onto the sphere.

*The proof as formalized.* The one lemma: for unit vectors $a$, $b$ with $\|a - b\| < 2$ and $0 \le s \le 1$, $(1-s)a + sb \ne 0$. If it vanished, taking norms would give $1 - s = s$, so $s = \tfrac12$ and $a = -b$, whence $\|a - b\| = 2$ ⟦Chapter8/NearMaps · chord_ne_zero⟧. The continuous homotopy is $(t, x) \mapsto \nu((1-t)f(x) + t\,g(x))$ on $[0,1] \times X$. The smooth one is
$$H(x, t) = \nu\big((1 - \sigma(t))\,f(x) + \sigma(t)\,g(x)\big), \qquad (x,t) \in X \times \mathbb R.$$
The lemma applies since $\sigma(t) \in [0,1]$, so the chord never vanishes and $H$ is smooth; and $\nu$ fixes unit vectors, so $H(\cdot, 0) = f$ and $H(\cdot, 1) = g$ ⟦Chapter8/NearMaps · nv0_sph⟧.

### V8.4 Problem 4: uniform approximation and smoothing of homotopies

Where the retelling uses Weierstrass polynomials, the formal proof proves a smooth Stone–Weierstrass theorem on an arbitrary compact set.

> **Theorem (smooth approximation).** Let $E$, $F$ be finite-dimensional real normed spaces, $S \subseteq E$ compact, $G : E \to F$ continuous on $S$, and $\varepsilon > 0$. There is a smooth $Q : E \to F$ with $\|Q(x) - G(x)\| < \varepsilon$ for all $x \in S$. ⟦Chapter8/Approx · exists_contDiff_approx_of_isCompact⟧

*The idea.* Restrictions of smooth functions form a point-separating subalgebra of $C(S, \mathbb R)$, so Stone–Weierstrass approximates each coordinate of $G$.

*The proof as formalized.* The restrictions to $S$ of smooth functions $E \to \mathbb R$ form a subalgebra of $C(S, \mathbb R)$ ⟦Chapter8/Approx · smoothSubalgebraOn⟧. It separates points, since continuous linear functionals do (Hahn–Banach) and they are smooth ⟦Chapter8/Approx · smoothSubalgebraOn_separatesPoints⟧. As $S$ is compact, Stone–Weierstrass makes it uniformly dense. Fix a basis $b_1, \dots, b_d$ of $F$, put $C = \sum_i \|b_i\| + 1$, and approximate each coordinate $G_i$ of $G$ within $\varepsilon / C$ by a smooth $P_i$. Then $Q = \sum_i P_i b_i$ satisfies, on $S$,
$$\|Q - G\| \le \sum_i |P_i - G_i|\,\|b_i\| \le \tfrac{\varepsilon}{C}\,(C - 1) < \varepsilon.$$
The finite dimensionality of $E$ plays no role in the argument.

Two small facts adapt this to spheres. For a unit vector $a$ and $q \ne 0$, $\|\nu(q) - a\| \le 2\|q - a\|$, because $\|\nu(q) - q\| = |1 - \|q\|| \le \|q - a\|$ ⟦Chapter8/Approx · norm_nv0_sub_le⟧. And a smooth homotopy restricts to a continuous one on $[0,1] \times X$ ⟦Chapter8/Approx · SmoothHomotopic.homotopic⟧.

> **Theorem (Problem 4).** Let $M \subseteq \mathbb R^{K+1}$ be a compact submanifold, given by slice charts modelled on $\mathbb R^m$. (a) For every continuous $G : M \to S^p$ and every $\varepsilon > 0$ there is a smooth $f : M \to S^p$ with $\|f(x) - G(x)\| < \varepsilon$ for all $x$. (b) Two smooth maps $M \to S^p$ that are homotopic are smoothly homotopic. ⟦Chapter8/Smoothing · exists_smooth_approx⟧ ⟦Chapter8/Smoothing · smoothHomotopic_of_homotopic⟧

*The idea.* Approximate in the ambient space and normalize. For homotopies, approximate on $M \times [0,1]$ and close the gaps at the ends with Problem 3.

*Proof of (a).* Extend $G$ by $0$ off $M$; the extension is continuous on the compact set $M$. With $\delta = \min(\varepsilon/2, 1/2)$, take a smooth $Q$ within $\delta$ of $G$ on $M$. Since $\|G\| = 1$, $Q$ does not vanish on $M$, so $f = \nu \circ Q$ is smooth on $M$, and $\|f - G\| \le 2\|Q - G\| < 2\delta \le \varepsilon$ ⟦Chapter8/Smoothing · exists_smooth_approx⟧.

*Proof of (b), as formalized.*

1. Regard a homotopy $H : [0,1] \times M \to S^p$ from $f$ to $g$ as a function on the compact set $M \times [0,1] \subseteq \mathbb R^{K+1} \times \mathbb R$, extended by $0$, and take a smooth $Q$ within $1/4$ of it there.
2. Put $\tilde H(x, t) = \nu(Q(x, \sigma(t)))$ on $M \times \mathbb R$. As $\sigma(t) \in [0,1]$, $Q(x, \sigma(t))$ lies within $1/4$ of a unit vector, so it is nonzero and $\tilde H$ is smooth.
3. Since $\sigma(0) = 0$ and $H(0, \cdot) = f$, $\|f(x) - \tilde H(x, 0)\| \le 2\|Q(x, 0) - f(x)\| < \tfrac12 < 2$, and Problem 3 joins $f$ to $\tilde H(\cdot, 0)$. Likewise $g$ is joined to $\tilde H(\cdot, 1)$.
4. $\tilde H$ joins $\tilde H(\cdot, 0)$ to $\tilde H(\cdot, 1)$; symmetry and transitivity of smooth homotopy close the chain ⟦Chapter7/Homotopy · SmoothHomotopic.trans⟧ ⟦Chapter8/Smoothing · smoothHomotopic_of_homotopic⟧.

*Where the formal proof departs from the retelling.* The retelling uses the approximation of $H$ directly as a homotopy. Formally a homotopy must be smooth on all of $M \times \mathbb R$, while $Q$ is controlled only on $M \times [0,1]$; composing with $\sigma$ settles both points.

### V8.5 Problem 5: maps into a higher sphere miss a point

> **Theorem.** Let $X$ be a second countable smooth manifold without boundary, modelled on a real vector space of finite dimension $m < p$ lying in the lowest universe. Every smooth $f : X \to S^p$ misses some point, and is smoothly homotopic to a constant map. If $M \subseteq \mathbb R^{K+1}$ is a compact submanifold modelled on $\mathbb R^m$, $m < p$, every continuous map $M \to S^p$ is homotopic to a constant. ⟦Chapter8/Smoothing · exists_notMem_range_of_lt⟧ ⟦Chapter8/Smoothing · exists_smoothHomotopic_const_of_lt⟧ ⟦Chapter8/Smoothing · exists_homotopic_const_of_lt⟧

*The idea.* A regular value of a map from a lower-dimensional manifold cannot be attained. Once a point is missed, stereographic projection from it contracts the map.

*The proof as formalized.*

1. *A point is missed.* Brown's theorem gives a regular value $y$ of $f$. If $y = f(x)$, then $df_x$ would map an $m$-dimensional space onto $\mathbb R^p$, impossible for $m < p$ ⟦Chapter8/Smoothing · exists_notMem_range_of_lt⟧. Brown's theorem is stated for model spaces in a common universe, whence the universe condition.
2. *Contraction.* Let $\pi_y$ be stereographic projection from $y$ onto the hyperplane $y^\perp$, and $\pi_y^{-1}$ its inverse ⟦Chapter7/Stereo · stereo⟧ ⟦Chapter7/Stereo · stereoInv⟧. The homotopy is
$$H(x, t) = \pi_y^{-1}\big((1 - \sigma(t))\,\pi_y(f(x))\big).$$
It is smooth because $\pi_y$ is smooth away from $y$ and $\pi_y^{-1}$ is smooth everywhere; it lies in $S^p$ because its argument lies in $y^\perp$; $H(\cdot, 0) = f$ because $\pi_y^{-1}\pi_y = \mathrm{id}$ off $y$; and $H(\cdot, 1)$ is the constant $\pi_y^{-1}(0) = -y$ ⟦Chapter8/Smoothing · exists_smoothHomotopic_const_of_lt⟧.
3. *Continuous maps.* Approximate a continuous $f$ within $2$ by a smooth $f'$ (Problem 4 (a)). Problem 3 makes $f$ homotopic to $f'$, and step 2 gives a smooth, hence continuous, homotopy from $f'$ to a constant ⟦Chapter8/Smoothing · exists_homotopic_const_of_lt⟧.

### V8.6 and V8.7 Problems 6 and 7: fixed points and antipodal pairs

Both problems rest on two facts. Points of the sphere that are not antipodal are at distance $< 2$, by the parallelogram law $\|a - b\|^2 + \|a + b\|^2 = 4$ ⟦Chapter8/SphereMaps · norm_sub_lt_two_of_ne_neg⟧. And for $n \ge 1$ smoothly homotopic self-maps of $S^n$ have the same degree, by the homotopy invariance of §5, since $S^n$ is connected ⟦Chapter8/SphereMaps · deg_eq_of_smoothHomotopic⟧. The degree theory is built for smooth maps, so both problems are stated for smooth maps.

> **Theorem (Problem 6).** For $n \ge 1$, a smooth map $f : S^n \to S^n$ with $\deg f \ne (-1)^{n+1}$ has a fixed point. ⟦Chapter8/SphereMaps · exists_fixedPoint_of_deg_ne⟧

*Proof.* If $f(x) \ne x$ for all $x$, then $f(x)$ is never antipodal to $-x$, so $\|f(x) - (-x)\| < 2$. Problem 3 makes $f$ smoothly homotopic to the antipodal map, whose degree is $(-1)^{n+1}$ ⟦Chapter5/HairyBall · deg_antip⟧.

> **Lemma.** For $n \ge 1$, a smooth map $h : S^n \to S^n$ with $h(-x) = h(x)$ for all $x$ has even degree. ⟦Chapter8/SphereMaps · even_deg_of_even_map⟧

*Proof as formalized.* Take a regular value $y$ of $h$. The degree is the sum of the signs over the finite set $h^{-1}(y)$; reduce it modulo $2$. Each term is $\pm 1 \equiv 1$, since the sign at a regular point is nonzero. As $h$ is even, $x \mapsto -x$ is an involution of $h^{-1}(y)$, and it has no fixed points ⟦Chapter8/SphereMaps · antip_ne⟧. So the terms cancel in pairs, $1 + 1 = 0$ in $\mathbb Z/2$.

*A simpler route than the retelling's.* The retelling compares the signs at $x$ and $-x$ through the chain rule for $h = h \circ (-\mathrm{id})$. Parity does not need the signs, and the formal proof never compares them.

> **Theorem (Problem 7).** For $n \ge 1$, a smooth map $f : S^n \to S^n$ of odd degree satisfies $f(-x) = -f(x)$ for some $x$. ⟦Chapter8/SphereMaps · exists_antipodal_of_odd_deg⟧

*Proof as formalized.* Suppose not. Then $w(x) = f(x) + f(-x)$ never vanishes, and $h = \nu \circ w$ is smooth and even. It is never antipodal to $f$: if $f(x) = -w(x)/\|w(x)\|$, then $\langle f(x), w(x) \rangle = -\|w(x)\| < 0$, whereas $\langle f(x), w(x) \rangle = 1 + \langle f(x), f(-x) \rangle \ge 0$ by Cauchy–Schwarz. So $f$ and $h$ are smoothly homotopic by Problem 3, and $\deg f = \deg h$ is even by the lemma, a contradiction ⟦Chapter8/SphereMaps · exists_antipodal_of_odd_deg⟧.

### V8.0 (i) Local zero sets of submersions are submanifolds

Lemma 1 of §2 makes a global level set $f^{-1}(y)$ into a manifold. In Problems 8 to 11 one knows less: near each of its points the set is cut out by a function defined only near that point.

> **Theorem.** Let $M$ be a smooth manifold without boundary modelled on a finite-dimensional space $E$, and let $F$, $Z$ be finite-dimensional with $\dim Z + \dim F = \dim E$. Suppose that each point $x$ of $S \subseteq M$ has an open neighbourhood $U$ with a map $g : M \to F$, smooth on $U$, such that $S \cap U = g^{-1}(0) \cap U$ and $dg_y$ is onto for every $y \in S \cap U$. Then $S$ is a submanifold, given by slice charts modelled on $Z$ with complement $F$. ⟦Chapter8/LocalSlice · IsSliceSubmanifold.of_locally_preimage⟧

*The idea.* Apply Lemma 1 to the restriction of $g$ to $U$, and carry the resulting slice chart back to $M$.

*The proof as formalized.* The restriction of $g$ to the open submanifold $U$ is smooth, and $0$ is a regular value of it, since restriction does not change derivatives ⟦Chapter6/Opens · mfd_comp_subtype_val⟧. Lemma 1 of §2 gives a slice chart of $S \cap U = (g|_U)^{-1}(0)$ around $x$ inside the manifold $U$ ⟦Chapter2/LevelSet · exists_sliceChart_preimage⟧. What remains is formal but must be done: a partial diffeomorphism of $U$ is transported to one of $M$, with the same target, source the image of the old source, and an arbitrary value outside $U$ ⟦Chapter8/LocalSlice · PartialDiffeomorph.ofOpens⟧. It is a slice chart for $S$ because $S \cap U$ is exactly the zero set of $g$ in $U$.

> **Theorem (tangent space).** Let $S \subseteq M$ carry any slice structure modelled on $Z$, where $\dim Z + \dim F = \dim E$. If $x \in S$, $g : M \to F$ is smooth on an open set $U \ni x$, $g = 0$ on $S \cap U$, and $dg_x$ is onto, then $TS_x = \ker dg_x$, where $TS_x$ is the image of the derivative of the inclusion. ⟦Chapter8/LocalSlice · IsSliceSubmanifold.range_mfderiv_val_eq_ker⟧

*Proof.* This is Lemma 2 of §2 in local form. The composite $g \circ \iota$ vanishes near $x$, so $dg_x \circ d\iota_x = 0$ and $TS_x \subseteq \ker dg_x$. As $d\iota_x$ is injective ⟦Chapter2/LevelSet · injective_mfderiv_val⟧, both spaces have dimension $\dim Z = \dim E - \dim F$. Only the vanishing on $S$ and surjectivity at $x$ are used; an elementwise form ($v$ is tangent iff $dg_x v = 0$) is also recorded ⟦Chapter8/LocalSlice · IsSliceSubmanifold.mem_range_mfderiv_val_iff_of_local⟧.

Every slice chart $\varphi$ of a submanifold $M$ of a vector space $E$ supplies such a $g$, its normal part $a \mapsto (\varphi a)_2$: the derivative $\mathrm{pr}_2 \circ d\varphi_a$ is onto since $d\varphi_a$ is an isomorphism onto $Z \times W$ ⟦Chapter8/ProdGraph · surjective_fderiv_sliceDef⟧. The same isomorphism gives $\dim Z + \dim W = \dim E$ as soon as $M$ is nonempty ⟦Chapter8/ProdGraph · IsSliceSubmanifold.finrank_add⟧, so the tangent-space theorem applies: $TM_x = \ker(\mathrm{pr}_2 \circ d\varphi_x)$ for every slice chart $\varphi$ at $x$ ⟦Chapter8/ProdGraph · range_mfd_val_eq_ker_sliceChart⟧.

### V8.8 and V8.9 Problems 8 and 9: products and graphs

In Problems 8 to 10, $M \subseteq E_1$ and $N \subseteq E_2$ are submanifolds of finite-dimensional real normed spaces, given by slice charts modelled on $Z_1$, $Z_2$ with complements $W_1$, $W_2$, all finite-dimensional (a few lemmas need less). Tangent spaces are the images of the derivatives of the inclusions.

> **Theorem (Problem 8).** $M \times N \subseteq E_1 \times E_2$ is a submanifold modelled on $Z_1 \times Z_2$ with complement $W_1 \times W_2$, and $T(M \times N)_{(x,y)} = TM_x \times TN_y$. ⟦Chapter8/ProdGraph · isSliceSubmanifold_prod⟧ ⟦Chapter8/ProdGraph · range_mfd_val_prod⟧

*Proof as formalized.* Near $(x, y)$, for slice charts $\varphi_1$ at $x$ and $\varphi_2$ at $y$, the set $M \times N$ is the zero set of $(a, b) \mapsto ((\varphi_1 a)_2, (\varphi_2 b)_2)$ on the product of the chart domains. The derivative of this map is $D_1 \times D_2$, with $D_i = \mathrm{pr}_2 \circ d\varphi_i$, and it is onto ⟦Chapter8/ProdGraph · prodDef_eq_zero_iff⟧ ⟦Chapter8/ProdGraph · surjective_mfderiv_prodDef⟧. The criterion gives the manifold structure, and the tangent space is $\ker(D_1 \times D_2) = \ker D_1 \times \ker D_2 = TM_x \times TN_y$. No parametrization of $M \times N$ is ever built.

> **Theorem (Problem 9).** For a smooth map $f : M \to N$, the graph $\Gamma = \{(x, f(x))\} \subseteq E_1 \times E_2$ is a submanifold modelled on $Z_1$ with complement $W_1 \times E_2$, and $T\Gamma_{(x, f(x))}$ is the image of $u \mapsto (d\iota_x u,\ d\iota_{f(x)}\, df_x u)$, that is, the graph of $df_x$. ⟦Chapter8/ProdGraph · isSliceSubmanifold_graph⟧ ⟦Chapter8/ProdGraph · range_mfd_val_graph⟧

*Proof as formalized.*

1. *Extending $f$.* For a slice chart $\varphi$ of $M$ at $x$, with induced chart $\psi$ of $M$, put $\tilde f(a) = f(\psi^{-1}((\varphi a)_1))$ on the open set of those $a \in \operatorname{dom}\varphi$ for which $(\varphi a)_1$ lies in the image of $\psi$. It is smooth and extends $f$ ⟦Chapter8/ProdGraph · graphExt⟧ ⟦Chapter8/ProdGraph · contDiffOn_graphExt⟧ ⟦Chapter8/ProdGraph · graphExt_val⟧.
2. *Defining function.* Near $(x, f(x))$, $\Gamma$ is the zero set of $(a, b) \mapsto ((\varphi a)_2,\ b - \tilde f(a))$, whose derivative $(v, w) \mapsto ((d\varphi\, v)_2,\ w - d\tilde f\, v)$ is onto ⟦Chapter8/ProdGraph · graphDef_eq_zero_iff⟧ ⟦Chapter8/ProdGraph · surjective_mfderiv_graphDef⟧.
3. *Tangent space.* The kernel is $\{(v, w) : v \in TM_x,\ w = d\tilde f_x v\}$, and differentiating $\tilde f \circ \iota_M = \iota_N \circ f$ near $x$ gives $d\tilde f_x \circ d\iota_x = d\iota_{f(x)} \circ df_x$ ⟦Chapter8/ProdGraph · range_mfd_val_graph⟧.

Where the retelling shows that $x \mapsto (x, f(x))$ is a diffeomorphism onto $\Gamma$, the formal proof reads structure and tangent space off one defining function.

### V8.10 Problem 10: the tangent bundle and $df$

Let $M \subseteq E$ be modelled on $Z$ with complement $W$, and $TM = \{(x, v) \in E \times E : x \in M,\ v \in TM_x\}$ ⟦Chapter8/TangentBundle · tangentBundleSet⟧.

A definitional point comes first. $TM_x$ is a subspace of $E$, while $df_x$ acts on the model space $Z$. So the formal $df$ first writes $v \in TM_x$ in chart coordinates, as the vector $u$ with $d\iota_x u = v$ (unique, since $d\iota_x$ is injective, and chosen), and then sets $df(x, v) = (f(x),\ d\iota_{f(x)}\, df_x u)$ ⟦Chapter8/TangentBundle · tangentCoord⟧ ⟦Chapter8/TangentBundle · tangentMap⟧.

> **Theorem.** (a) $TM$ is a submanifold of $E \times E$ modelled on $Z \times Z$ with complement $W \times W$, of dimension $2 \dim M$ ⟦Chapter8/TangentBundle · isSliceSubmanifold_tangentBundle⟧. (b) For smooth $f : M \to N$, the map $df : TM \to TN$ is smooth ⟦Chapter8/TangentBundle · contMDiff_tangentMap⟧. (c) $d(\mathrm{id}) = \mathrm{id}$, a statement without hypotheses, and $d(g \circ f) = dg \circ df$ for smooth $f : M \to N$ and $g : N \to P$ ⟦Chapter8/TangentBundle · tangentMap_id⟧ ⟦Chapter8/TangentBundle · tangentMap_comp⟧.

*The idea.* Locally, $TM$ is cut out by the normal parts of $a$ and of $d\varphi_a v$; and $df$ is locally the restriction of the differential of a smooth extension of $f$.

*Proof of (a).* For a slice chart $\varphi$, put $g(a, v) = ((\varphi a)_2, (d\varphi_a v)_2)$ on $\operatorname{dom}\varphi \times E$. For $a \in M$, $TM_a = \ker(\mathrm{pr}_2 \circ d\varphi_a)$, so $TM$ is the zero set of $g$ there ⟦Chapter8/TangentBundle · sliceChart_mem_tangentSpace_iff⟧. The derivative is
$$dg_{(a,v)}(u, w) = \big((d\varphi_a u)_2,\ (d\varphi_a w)_2 + (d^2\varphi_a(u, v))_2\big),$$
and it is onto: choose $u$ for the first component, then $w$ to correct the second, since $\mathrm{pr}_2 \circ d\varphi_a$ is onto ⟦Chapter8/TangentBundle · sliceChart_surjective_snd⟧. The criterion applies.

*Proof of (b).* Near $(x_0, v_0)$, use the slice chart $\varphi$ that defines the chart $\psi$ of $M$ at $x_0$, and the smooth extension $\rho(a) = f(\psi^{-1}((\varphi a)_1))$ of $f$ to an open subset of $E$. For $b \in M$ near $x_0$ and $w = d\iota_b u \in TM_b$, differentiating $\rho \circ \iota_M = \iota_N \circ f$ gives $d\rho_b w = d\iota_{f(b)}\, df_b u$. So near $(x_0, v_0)$, $df$ is the restriction to $TM$ of the smooth map $(a, w) \mapsto (\rho(a), d\rho_a w)$, and it is smooth as a map into the manifold $TN$ ⟦Chapter8/TangentBundle · contMDiff_tangentMap⟧.

*Proof of (c).* The identity rule is $d\iota_x u = v$. The composition rule is the chain rule $d(g \circ f)_x = dg_{f(x)} \circ df_x$, together with the fact that the chart coordinates of $d\iota_{f(x)}(df_x u)$ are $df_x u$ ⟦Chapter8/TangentBundle · tangentCoord_mfd_val⟧.

### V8.11 Problem 11: the normal bundle and the ε-neighbourhood

Let $M \subseteq \mathbb R^k$ be a submanifold given by slice charts modelled on $\mathbb R^m$ with complement $\mathbb R^w$, and
$$E = \{(x, v) \in \mathbb R^k \times \mathbb R^k : x \in M,\ v \perp TM_x\}$$
⟦Chapter8/NormalBundle · normalBundleSet⟧. For compact nonempty $M \subseteq \mathbb R^{K+1}$, Part IV provides a radius $\varepsilon_0 > 0$ and a map $r : \mathbb R^{K+1} \to M$ with $\|y - r(y)\| = \operatorname{dist}(y, M)$ for all $y$ and $r = \mathrm{id}$ on $M$; on $N_{\varepsilon_0} = \{y : \operatorname{dist}(y, M) < \varepsilon_0\}$ the nearest point is unique, $r$ is smooth, and $y - r(y) \perp TM_{r(y)}$ ⟦Chapter6/Tubular4 · tubr_spec⟧.

> **Theorem.** (a) If $m + w = k$, then $E$ is a submanifold of $\mathbb R^k \times \mathbb R^k$ modelled on $\mathbb R^k$, with complement $\mathbb R^w \times \mathbb R^m$. (b) If $M \subseteq \mathbb R^{K+1}$ is compact and nonempty and $m + w = K + 1$, there is $\varepsilon > 0$ such that $(x, v) \mapsto x + v$ is a diffeomorphism from the open subset $\{(x, v) \in E : \|v\| < \varepsilon\}$ of $E$ onto $N_\varepsilon = \{y : \operatorname{dist}(y, M) < \varepsilon\}$. ⟦Chapter8/NormalBundle · isSliceSubmanifold_normalBundle⟧ ⟦Chapter8/NormalBundle · exists_normalTube_diffeomorph⟧

*The idea.* Locally, $E$ is cut out by the normal coordinates of $x$ and the tangential components of $v$. The sum map has invertible derivative along the zero section, compactness makes it injective on a uniformly thin tube, and the nearest-point map inverts it.

*Proof of (a).* Near $p \in M$ let $\varphi$ be the chosen slice chart at $p$, $\phi(z) = \varphi^{-1}(z, 0)$ the local parametrization, and $B(a) = (d\phi_{(\varphi a)_1})^*$ the adjoint of its derivative, a map $\mathbb R^k \to \mathbb R^m$ ⟦Chapter8/NormalBundle · B⟧. Then $E$ is locally the zero set of $g(a, v) = ((\varphi a)_2,\ B(a)v)$: the first component cuts out $M$, and since $TM_a$ is the image of $d\phi$, $v \perp TM_a$ if and only if $B(a) v = 0$ ⟦Chapter8/NormalBundle · g⟧ ⟦Chapter8/NormalBundle · mem_normalBundleSet_iff⟧. The adjoint $B(a)$ is onto: $\langle B(a)\, d\phi\, y, y \rangle = \|d\phi\, y\|^2$ and $d\phi$ is injective, so $B(a) \circ d\phi$ is an injective, hence bijective, endomorphism of $\mathbb R^m$ ⟦Chapter8/NormalBundle · surjective_B⟧. So $dg(u, h) = ((d\varphi_a u)_2,\ B(a)h + (dB_a u)v)$ is onto, and the criterion applies ⟦Chapter8/NormalBundle · surjective_fderiv_g⟧.

*Proof of (b), as formalized.*

1. *Invertible derivative on the zero section.* By the kernel theorem, $TE_{(x,0)} = \ker dg_{(x,0)}$, the pairs $(u, h)$ with $u \in TM_x$ and $h \perp TM_x$ (the term $(dB_a u)v$ vanishes at $v = 0$). The sum map $S(x, v) = x + v$ has derivative $(u, h) \mapsto u + h$, and $u + h = 0$ forces $\|u\|^2 = -\langle h, u \rangle = 0$ ⟦Chapter8/NormalBundle · injective_mfd_normalSum⟧. So $dS_{(x,0)}$ is invertible.
2. *Local injectivity.* The inverse function theorem on the $k$-manifold $E$ gives $r_x > 0$ such that $S$ is injective on $\{(a, v) \in E : \|a - x\| < r_x,\ \|v\| < r_x\}$ ⟦Chapter8/NormalBundle · exists_radius_normalSum_injective⟧.
3. *Uniform injectivity.* Cover $M$ by finitely many balls $B(x_i, r_{x_i}/2)$, a nonempty family since $M \ne \emptyset$, and let $\varepsilon_1 = \min_i r_{x_i}/4$. If $a + v = b + w$ with $\|v\|, \|w\| < \varepsilon_1$ and $\|a - x_i\| < r_{x_i}/2$, then $\|b - x_i\| \le \|a - x_i\| + \|v\| + \|w\| < r_{x_i}$: both points lie in the injectivity neighbourhood of $(x_i, 0)$ and coincide ⟦Chapter8/NormalBundle · exists_eps_normalSum_injective⟧.
4. *The radius* is $\varepsilon = \min(\varepsilon_1, \varepsilon_0)$ ⟦Chapter8/NormalBundle · normalε⟧.
5. *$r(x + v) = x$.* Let $(x, v) \in E$, $\|v\| < \varepsilon$, $y = x + v$. Then $\operatorname{dist}(y, M) \le \|v\| < \varepsilon_0$, so $(r(y), y - r(y)) \in E$ with $\|y - r(y)\| = \operatorname{dist}(y, M) < \varepsilon$. This point and $(x, v)$ have the same sum, so they coincide by step 3 ⟦Chapter8/NormalBundle · normalRetraction_eq⟧.
6. *The diffeomorphism.* $S$ maps the tube into $N_\varepsilon$, since $\operatorname{dist}(x + v, M) \le \|v\|$. The inverse is $y \mapsto (r(y), y - r(y))$, a smooth map into $E$ because $r$ is smooth; one composite is the identity trivially, the other by step 5 ⟦Chapter8/NormalBundle · exists_diffeomorph_normalε⟧.

*What the book leaves implicit.* The injectivity radius must be made uniform (step 3). The formal statement also assumes $M \ne \emptyset$, because the radius of Part IV and the minimum over the finite cover need it; for empty $M$ the claim is trivial, but that case is not treated. Note the logical order: $r(x + v) = x$ is not an input from Part IV, which gives it only for small multiples $sv$, $s$ near $0$ ⟦Chapter6/Tubular4 · tubr_spec⟧; it is a consequence of injectivity ⟦Chapter8/NormalBundle · normalRetraction_eq⟧.

### V8.12 Problem 12: the retraction, and maps into $M$

Let $M \subseteq \mathbb R^{K+1}$ be compact and nonempty, with $r$, $\varepsilon_0$ and $\varepsilon$ as in Problem 11.

> **Theorem (the nearest point).** If $m + w = K + 1$ and $(x, v) \in E$ with $\|v\| < \varepsilon$, then $r(x + v) = x$, and $\|(x + v) - x\| < \|(x + v) - z\|$ for every $z \in M$ other than $x$. ⟦Chapter8/Nearest · normalRetraction_nearest⟧

*Proof.* The first half is step 5 above. For the second, put $y = x + v \in N_{\varepsilon_0}$: a point $z \ne r(y) = x$ of $M$ as close to $y$ as $x$ would be a second nearest point, which Part IV excludes on $N_{\varepsilon_0}$ ⟦Chapter8/Retraction · tubr_dist_lt⟧.

To use $r$ as a map into $M$, the formal proof checks that it is smooth into the manifold $M$: smoothness into $\mathbb R^{K+1}$ on the open set $N_{\varepsilon_0}$ passes to $M$ by corestriction ⟦Chapter8/Retraction · contMDiffAt_tubr⟧.

> **Theorem (Problem 12, approximation).** Let $X \subseteq \mathbb R^{L+1}$ and $M \subseteq \mathbb R^{K+1}$ be compact submanifolds given by slice charts, with $M$ nonempty. Every continuous $G : X \to M$ is a uniform limit of smooth maps, and two smooth maps $X \to M$ that are homotopic are smoothly homotopic. ⟦Chapter8/Retraction · exists_smooth_approx_mfld⟧ ⟦Chapter8/Retraction · smoothHomotopic_of_homotopic_mfld⟧

*The idea.* Repeat Problem 4 with $r$ in place of $\nu$; the nearest-point property replaces the normalization estimate.

*The proof as formalized.*

1. *Approximation.* With $\delta = \min(\varepsilon/2, \varepsilon_0)$ take a smooth $Q$ within $\delta$ of $G$ on $X$. Then $Q(X) \subseteq N_{\varepsilon_0}$, so $f = r \circ Q$ is smooth. As $G(x) \in M$, the nearest-point property gives $\|r(Q) - Q\| \le \|G - Q\|$, so $\|f - G\| \le 2\|Q - G\| < \varepsilon$ ⟦Chapter8/Retraction · norm_sub_tubr_le⟧.
2. *Nearby maps.* If smooth $f, g : X \to M$ satisfy $\|f - g\| < \varepsilon_0$, the path $c(x, t) = (1 - \sigma(t)) f(x) + \sigma(t) g(x)$ stays within $\|f(x) - g(x)\|$ of $f(x) \in M$, hence in $N_{\varepsilon_0}$, and $r \circ c$ is a smooth homotopy from $r \circ f = f$ to $r \circ g = g$. This step does not need $X$ compact ⟦Chapter8/Retraction · smoothHomotopic_of_dist_lt_mfld⟧.
3. *Homotopies.* Approximate a homotopy on $X \times [0,1]$ within $\varepsilon_0/4$ by a smooth $Q$, and put $\tilde H(x, t) = r(Q(x, \sigma(t)))$. Its ends are within $\varepsilon_0/2$ of $f$ and $g$; step 2 and transitivity finish, as in Problem 4 ⟦Chapter8/Retraction · smoothHomotopic_of_homotopic_mfld⟧.

### What the formalization taught us

- **Hidden hypotheses.** Problem 1 needs $N$ compact, so that $\deg g$ is defined; the formal statement also asks $P$ to be Hausdorff ⟦Chapter8/DegComp · deg_comp⟧. The formal statements of Problem 11 (b) and of Problem 12 assume $M$ nonempty, as the tubular radius of Part IV requires; the trivial empty case is left out ⟦Chapter8/NormalBundle · exists_eps_normalSum_injective⟧ ⟦Chapter8/Retraction · exists_smooth_approx_mfld⟧.
- **Deviations.** Problems 6 and 7 are stated for smooth maps, for which the degree is built ⟦Chapter8/SphereMaps · exists_fixedPoint_of_deg_ne⟧. Problem 2 is stated for $\deg P \ge 1$, where the extension by $\hat P(\infty) = \infty$ is continuous ⟦Chapter8/PolyDeg · deg_polyMap⟧.
- **Universes.** The degree and Brown's theorem are stated for model spaces in a common universe, a harmless side condition in Problems 1 and 5 ⟦Chapter8/Smoothing · exists_notMem_range_of_lt⟧.
- **One criterion, four constructions.** Products, graphs, tangent and normal bundles are all local zero sets of submersions. One criterion yields their manifold structures, and its companion, the kernel theorem, the tangent spaces that are needed: those of products and graphs, and that of the normal bundle along the zero section. Beyond Lemma 1 of §2, the criterion costs only the transport of charts from an open subset to the ambient manifold ⟦Chapter8/LocalSlice · PartialDiffeomorph.ofOpens⟧ ⟦Chapter8/LocalSlice · IsSliceSubmanifold.range_mfderiv_val_eq_ker⟧.
- **Taming time.** Homotopies are smooth maps on $X \times \mathbb R$, so every straight-line homotopy is reparametrized by a smooth step, which keeps the approximations where they are controlled ⟦Chapter8/Smoothing · smoothHomotopic_of_homotopic⟧.
- **Parity without signs.** Even maps have even degree by a count modulo $2$, with no comparison of signs ⟦Chapter8/SphereMaps · even_deg_of_even_map⟧.
- **A different logical order in Problem 11.** Uniform injectivity of $x + v$ on a thin tube is proved by compactness, and $r(x + v) = x$ is derived from it ⟦Chapter8/NormalBundle · normalRetraction_eq⟧.
- **One approximation theorem.** Stone–Weierstrass for restrictions of smooth functions, on any compact subset of a finite-dimensional space, serves Problems 4, 5 and 12 alike ⟦Chapter8/Approx · exists_contDiff_approx_of_isCompact⟧.


## Part IX. Orientation tools and linking numbers (Milnor §8, Problem 13)

Problem 13 asks three things about the linking number $l(M,N)$ of disjoint compact oriented manifolds in $\mathbb R^{k+1}$. It asks for the symmetry law $l(N,M) = (-1)^{(m+1)(n+1)}\,l(M,N)$, for the vanishing of $l(M,N)$ when $M$ bounds away from $N$, and for a definition when the manifolds lie in the sphere $S^{m+n+1}$. The problem leaves its conventions implicit: how $M\times N$ is oriented (the book uses product orientations without fixing one), which orientation $S^k$ carries (elsewhere the book orients spheres as boundaries of disks), and what "bounds" means. The last request also hides a theorem with an unstated hypothesis. The formal proof first builds four tools, V8.0 (ii)–(v) of the verified edition: product orientations, orientations given by a complementary frame, local degrees for maps whose relevant preimages are compact, and some genericity facts. Problem 13 uses the first two and the last. The third serves the Hopf invariant of Part X.

**Map.**

- `Chapter8/OrientProd`: product orientations, block maps, the swap sign $(-1)^{mn}$, relabelling along equal dimensions.
- `Chapter8/OrientFrame`: "frame first" orientations; two orientations of a connected manifold agree or are opposite; Milnor's orientation of $S^n$.
- `Chapter8/ProperDegree`: finiteness, local constancy and homotopy invariance of the signed count when only preimages are compact.
- `Chapter8/Generic`: small images are meagre; the off-diagonal of $S^p\times S^p$ is connected; local constancy on a dense set.
- `Chapter8/Linking`: the linking number, its symmetry, its vanishing when the first manifold bounds.
- `Chapter8/LinkingDefs`: stereographic projection, rotations, the linking number after a rotation.
- `Chapter8/LinkingSphere`: admissible rotations exist, and for positive dimensions the choice does not matter.

### V8.0 (ii) Product orientations and the sign of the swap

> **Proposition.** Let $E, F$ be real vector spaces of dimensions $m, n$, oriented by $a, b$.
>
> 1. There is an orientation $a\times b$ of $E\times F$ for which $(e_1,0),\dots,(e_m,0),(0,f_1),\dots,(0,f_n)$ is positive whenever $e$ is a positive basis of $E$ and $f$ one of $F$.
> 2. Let $E', F'$ have dimensions $m, n$ and orientations $a', b'$. If $T(v,w) = (Av,\ Cv + Bw)$ for linear maps $A : E\to E'$, $B : F\to F'$, $C: E\to F'$, then $\operatorname{sign} T = \operatorname{sign} A\cdot\operatorname{sign} B$, relative to $a\times b$ and $a'\times b'$.
> 3. The swap $(v,w)\mapsto(w,v)$ has sign $(-1)^{mn}$ from $a\times b$ to $b\times a$.
>
> Let $M, N$ be smooth manifolds modelled on $E, F$ (boundary allowed), with orientations $o_M, o_N$. Then $(x,y)\mapsto o_M(x)\times o_N(y)$ is an orientation of $M\times N$. Let $\varphi: M\to M'$ and $\psi: N\to N'$ be maps into oriented smooth manifolds of dimensions $m, n$, differentiable at $x$ and at $y$. Then the sign of $\varphi\times\psi$ at $(x,y)$ is the product of their signs. The swap $M\times N\to N\times M$ has sign $(-1)^{mn}$ everywhere.

*The idea.* Evaluate every form on a concatenated basis. Everything then reduces to the determinant of a block-triangular matrix, and for the swap to the sign of one permutation.

*The proof as formalized.* Write $(e,f)$ for the concatenated basis of $E\times F$ ⟦Chapter8/OrientProd · prodBasis⟧, and let $\varepsilon_e(a)$ be $+1$ if $e$ is $a$-positive and $-1$ otherwise. The product orientation is *defined* as the class of $\varepsilon_{e_0}(a)\,\varepsilon_{f_0}(b)\,\det_{(e_0,f_0)}$ for fixed reference bases $e_0, f_0$ ⟦Chapter8/OrientProd · orProdGen⟧. Other bases $e,f$ give the same class. A family whose first $m$ vectors are $(\alpha_j,\gamma_j)$ and whose last $n$ are $(0,\beta_j)$ has $\det_{(e,f)} = \det_e\alpha\cdot\det_f\beta$. Hence $\det_{(e_0,f_0)} = \det_{e_0}(e)\det_{f_0}(f)\det_{(e,f)}$, while $\varepsilon_{e_0}(a)\det_{e_0}(e)\,\varepsilon_e(a) > 0$ ⟦Chapter8/OrientProd · prodBasis_det_apply⟧ ⟦Chapter8/OrientProd · orEpsB_mul_det_mul_pos⟧ ⟦Chapter8/OrientProd · rayOfNeZero_prodBasis⟧. For positive $e, f$ the representative is $\det_{(e,f)}$ itself, which is statement 1 ⟦Chapter8/OrientProd · orProdGen_eq⟧. For statement 2, $T$ maps the concatenated reference basis to a block-triangular family, so the quantity whose sign is $\operatorname{sign}T$ factors into those for $A$ and $B$ ⟦Chapter8/OrientProd · orSign_prod_triangular⟧ ⟦Chapter8/OrientProd · orSign_prodMap⟧.

The swap sends $(e,f)$ to $(f,e)$ composed with the block permutation of $m+n$ letters that moves the first $m$ letters behind the last $n$. The formal proof identifies this permutation with the $n$-th power of the cyclic shift of $m+n$ letters, whose sign is $(-1)^{m+n-1}$. Its sign is therefore $(-1)^{n(m+n-1)} = (-1)^{mn}$, since $n(n-1)$ is even ⟦Chapter8/OrientProd · finCongr_trans_finAddFlip⟧ ⟦Chapter8/OrientProd · sign_finCongr_trans_finAddFlip⟧ ⟦Chapter8/OrientProd · orSign_swap⟧.

On manifolds, the chart of $M\times N$ at $(x,y)$ is the product of the charts, so its derivative is a product map. By statement 2, the continuity condition for $o_M\times o_N$ is then the product of the conditions for $o_M$ and $o_N$ ⟦Chapter8/OrientProd · Orient.prod⟧. The derivative of $\varphi\times\psi$ is $d\varphi\times d\psi$, and that of the swap is the linear swap ⟦Chapter8/OrientProd · signAt_prodMap⟧ ⟦Chapter8/OrientProd · signAt_swap⟧.

*What the formal proof has to make explicit.* An orientation is indexed by its dimension. One of $E\times F$ has index $m+n$, one of $F\times E$ has index $n+m$, and these are the same number written differently. So $b\times a$ is relabelled along $n+m = m+n$ before the two are compared ⟦Chapter8/OrientProd · Orient.cast⟧. Relabelling both orientations never changes a sign ⟦Chapter8/OrientProd · orSign_reindex_finCongr⟧ ⟦Chapter8/OrientProd · signAt_cast⟧.

### V8.0 (iii) Frame orientations and Milnor's orientation of the sphere

Milnor orients a boundary by putting the outward normal first. The formal text makes this one construction, used here for the sphere and in Part X for preimages of regular values.

> **Construction.** Let $S$ be a smooth manifold without boundary modelled on a space $Z$ of dimension $d$. Let $E$ be a space of dimension $d+k$, oriented by $o$, and let $\Omega$ be a fixed volume form representing $o$. Let $\iota: S\to E$ be smooth and $\nu = (\nu_1,\dots,\nu_k) : S\to E^k$ continuous, such that for every $q$ the $d$-form $z\mapsto\Omega(\nu_1(q),\dots,\nu_k(q),\,d\iota_q z_1,\dots,d\iota_q z_d)$ on $Z$ is nonzero. Calling $z$ positive when this number is positive defines an orientation of $S$.
>
> **Sign formula.** Let $(S,\iota,\nu,\Omega)$ and $(S',\kappa,\mu,\Omega')$ be two such data of dimension $d$, and let $f: S\to S'$. Then the sign of $f$ at $q$ is $\operatorname{sgn}\bigl(\Omega'(\mu(f(q)),\,d\kappa\,df_q e)\cdot\Omega(\nu(q),\,d\iota_q e)\bigr)$ for every $d$-tuple $e$ in $Z$ with $\Omega(\nu(q), d\iota_q e)\neq 0$. The statement also assumes $f$ differentiable at $q$, but does not use it.
>
> **Theorem.** On a preconnected manifold, two orientations either agree at every point or are opposite at every point.
>
> **The sphere.** Let $O_n$ be the frame orientation of $S^n$ given by the inclusion into $\mathbb R^{n+1}$, the standard orientation of $\mathbb R^{n+1}$ and the frame $\nu(q) = q$. Let $O^5_n$ be the orientation of $S^n$ built in Chapter 5. If $n > 0$, then $O_n = \pm O^5_n$, and the antipodal map has degree $(-1)^{n+1}$ for $O_n$.

*The idea.* Read in one chart, the frame form is a continuous, nowhere vanishing family of $d$-forms on the fixed space $Z$. These forms make up a line, so the family keeps its sign. On the sphere, $T_qS^n = q^\perp$, so $q$ is a complementary frame.

*The proof as formalized.*

1. *Forms.* The tuple $(\nu_1,\dots,\nu_k,w_1,\dots,w_d)$ and the form $w\mapsto\Omega(\nu,w)$ are built by inserting one frame vector at a time ⟦Chapter8/OrientFrame · frameTuple⟧ ⟦Chapter8/OrientFrame · frameCurry⟧. Along a linear map $T: Z\to E$, the frame orientation of $Z$ is the one represented by the pulled-back form, or an arbitrary default when that form vanishes ⟦Chapter8/OrientFrame · frameForm⟧ ⟦Chapter8/OrientFrame · frameOr⟧. All positive volume forms of $E$ give the same orientation ⟦Chapter8/OrientFrame · frameOr_eq⟧. The form is nonzero on $z$ whenever $(\nu, Tz)$ is linearly independent ⟦Chapter8/OrientFrame · frameForm_apply_ne_zero_of_linearIndependent⟧.
2. *Continuity.* Fix $q_0$, the chart $c_0$ at $q_0$, and $\psi = \iota\circ c_0^{-1}$. By the chain rule, the frame form at $q$ is the pull-back along $(dc_0)_q$ of $\Phi(q) = \Omega\bigl(\nu(q),\,d\psi_{c_0(q)}\,\cdot\,\bigr)$, a $d$-form on $Z$. On a fixed basis $u_0$ of $Z$, the value $\Phi(q)(u_0)$ is continuous in $q$, because top-degree forms, $\nu$ and $d\psi$ are all continuous ⟦Chapter8/OrientFrame · continuous_alternatingMap_of_finrank⟧. Near $q_0$ it keeps the sign of $\Phi(q_0)(u_0)\neq 0$, so $\Phi(q) = c\,\Phi(q_0)$ with $c>0$. The chart has derivative the identity at $q_0$. So $(dc_0)_q$ carries the orientation at $q$ to the one at $q_0$ with sign $\operatorname{sgn}(c^{-1}) = 1$ ⟦Chapter8/OrientFrame · Orient.ofFrame_cont⟧ ⟦Chapter8/OrientFrame · Orient.ofFrame⟧. The sign formula is the definition of the sign, unwound ⟦Chapter8/OrientFrame · signAt_ofFrame⟧.
3. *Two orientations.* At each point, two orientations agree or are opposite. By the continuity condition for both, each of these two sets is open, so on a preconnected space one of them is everything ⟦Chapter8/OrientFrame · Orient.eq_or_eq_neg⟧.
4. *The sphere.* With one frame vector, the frame form is Chapter 5's contraction ⟦Chapter8/OrientFrame · frameForm_one⟧. Let $G(x) = |x|^2-1$. Then $d\iota_q$ is injective with image in $\ker dG_q$, and $dG_q(q) = 2\neq 0$. So by Chapter 5's contraction lemma the frame $(q)$ is complementary everywhere ⟦Chapter5/LevelOrient · contractForm_basis_ne_zero⟧ ⟦Chapter8/OrientFrame · sph_frameForm_ne_zero⟧. This defines $O_n$ ⟦Chapter8/OrientFrame · stdOrE⟧ ⟦Chapter8/OrientFrame · sphOrStd⟧. For $n>0$ the sphere is connected, and step 3 gives $O_n = \pm O^5_n$ ⟦Chapter8/OrientFrame · sphOrStd_eq_or_neg⟧. In the $+$ case the antipodal degree is Chapter 5's value. In the $-$ case source and target are both reversed, and no sign changes ⟦Chapter5/HairyBall · deg_antip⟧ ⟦Chapter8/OrientFrame · deg_antip_std⟧.

*Why a second orientation of the sphere.* Chapter 5 oriented $S^n$ as the level set $\{G = 0\}$. It contracted the orientation of an unspecified reference basis $e$ of $\mathbb R^{n+1}$ with $-\sum_i dG(e_i)\,e_i$, a vector on which $dG$ is negative ⟦Chapter5/HairyBall · sphOr⟧ ⟦Chapter5/LevelOrient · outward⟧. That vector points into the ball. So $O^5_n$ is the boundary orientation of the exterior $\{|x|\ge 1\}$, relative to an orientation of $\mathbb R^{n+1}$ that the formal text never identifies. The degree of a map of the sphere to itself does not notice this. Linking numbers do: reversing the orientation of $S^k$ reverses the sign at every point ⟦Chapter6/LevelZero · signAt_neg_right⟧, hence every linking number, and with it the Hopf invariant of Part X. So linking numbers use $O_k$, and the two orientations are related only up to sign.

### V8.0 (iv) Local degrees when only preimages are compact

Chapter 5 studied the signed count $\deg_y f = \sum_{x\in f^{-1}(y)}\operatorname{sign} df_x$ for compact $M$. The Hopf invariant of Part X is a signed count for a map defined only on an open subset of $S\times S$. The old proofs used compactness of $M$ only through certain preimages, and the results below assume only that.

> **Theorem.** Let $M, N$ be smooth manifolds without boundary, modelled on spaces of the same finite dimension $n$ that lie in a common universe, Hausdorff and oriented. Let $f: M\to N$ be smooth and $y$ a regular value of $f$.
>
> (a) If $f^{-1}(y)$ is compact, it is finite. For this, $M$ Hausdorff and $N$ with closed points suffice, and no orientation is needed.
>
> (b) Suppose $f^{-1}(V)$ is compact for some neighbourhood $V$ of $y$, not necessarily closed. Then every $y'$ near $y$ is a regular value, and $\deg_{y'} f = \deg_y f$.
>
> (c) Let $M$ also be second countable and $F: M\times\mathbb R\to N$ smooth, with $y$ a regular value of $f_0 = F(\cdot,0)$ and of $f_1 = F(\cdot,1)$. Suppose $\{(x,t): F(x,t)\in V,\ 0\le t\le 1\}$ is compact for some neighbourhood $V$ of $y$. Then $\deg_y f_0 = \deg_y f_1$.

*The idea.* Replace $M$ by $f^{-1}(V)$ in the old proofs. For (c), first find a value that is regular for the homotopy itself.

*The proof as formalized.*

1. *Finiteness.* By the inverse function theorem, $f$ is injective near each point of the fibre. Finitely many such neighbourhoods cover the compact fibre, and each contains no point of the fibre except its centre ⟦Chapter8/ProperDegree · IsRegularValue.finite_preimage_of_isCompact⟧.
2. *Local constancy.* This is Chapter 1's argument with one change ⟦Chapter1/RegularValue · IsRegularValue.eventually_finsum_preimage_eq⟧. Around each point $x$ of the finite fibre, take a local inverse $L_x$ and an open $U_x\ni x$ in its image. The $U_x$ are pairwise disjoint, and a given weight $\varphi$, locally constant near the fibre, is constant on each. Chapter 1 removed the closed set $f(M\setminus\bigcup_x U_x)$. Here $C = f(f^{-1}(V)\setminus\bigcup_x U_x)$ is compact, hence closed, and it misses $y$. Take $y'\in\operatorname{int}V\cap\bigcap_x L_x^{-1}(U_x)$ outside $C$. Then every preimage of $y'$ lies in some $U_x$ and is regular, and $x\mapsto L_x(y')$ is a bijection $f^{-1}(y)\to f^{-1}(y')$ preserving $\varphi$ ⟦Chapter8/ProperDegree · IsRegularValue.eventually_isRegularValue_and_finsum_preimage_eq_of_isCompact⟧. The sign of $df$ is such a weight ⟦Chapter5/Orient · eventually_signAt_eq⟧ ⟦Chapter8/ProperDegree · IsRegularValue.eventually_degAt_eq_of_isCompact⟧.
3. *A regular value of the homotopy.* If $y$ is also a regular value of $F$, the cylinder argument of Chapter 5 ⟦Chapter5/HomotopyInv · degAt_eq_of_homotopy_of_isRegularValue⟧ is repeated, not invoked, with the compactness hypothesis in place of compactness of $M$. Lemma 1 of §5 is applied to the region $\{g\ge 0\}$ for $g(x,t) = t(1-t)$, and $\{F = y,\ g\ge0\}$, which is $\{F = y,\ 0 \le t \le 1\}$, is compact by hypothesis ⟦Chapter5/LemmaOne · lemmaOne_ambient⟧. Since $dg = (1-2t)\,dt$, the boundary signs are $\operatorname{sign}(df_0)_x$ at $t=0$ and $-\operatorname{sign}(df_1)_x$ at $t=1$. The end fibres are finite by step 1, because the slices at $t = 0, 1$ are compact ⟦Chapter8/ProperDegree · isCompact_preimage_slice_of_isCompact⟧ ⟦Chapter8/ProperDegree · degAt_eq_of_homotopy_of_isRegularValue_of_isCompact'⟧.
4. *Regularity only over $[0,1]$.* Suppose $F$ is regular only at points of $F^{-1}(y)$ with $0\le t\le 1$. Reparametrize time by $\tau(t) = (1-\cos\pi t)/2$, which takes values in $[0,1]$, with $\tau(0) = 0$, $\tau(1) = 1$ and $\tau'(t) = \tfrac\pi2\sin\pi t$. Then $y$ is a regular value of $\Phi(x,t) = F(x,\tau(t))$ everywhere. Where $\sin\pi t\neq 0$, $d\Phi$ has the image of $dF$. Where $\sin\pi t = 0$, $\tau(t)\in\{0,1\}$, and horizontal vectors already reach everything because the end maps are regular. Compactness for $\Phi$ follows from that for $F$ ⟦Chapter8/ProperDegree · degAt_eq_of_homotopy_of_isRegularValue_of_isCompact⟧.
5. *The general case.* Step 2 for $f_0$ and $f_1$ gives an open $U\ni y$ inside $V$ on which both end maps are regular with constant signed counts. Since $M\times\mathbb R$ is second countable, Brown's theorem gives $y'\in U$ regular for $F$ ⟦Chapter2/Brown · dense_regularValues⟧. The set $\{F = y',\ 0\le t\le 1\}$ is closed in the compact set of the hypothesis, and step 4 at $y'$ finishes ⟦Chapter8/ProperDegree · degAt_eq_of_homotopy_of_isCompact⟧.

The value $y'$ of step 5 is regular for the whole homotopy, so step 3 would already suffice there. The reparametrization proves more than this chain uses.

### V8.0 (v) Genericity: small images, the off-diagonal, local constancy

> **Proposition.** Let $P, N$ be manifolds modelled on real normed spaces $E, F$, with $E$ finite-dimensional and $\dim P<\dim N$.
>
> (a) For any map $g: P\to N$, no point of $g(P)$ is a regular value. Here boundary is allowed.
>
> (b) Let now $P$ and $N$ be smooth and without boundary, $F$ finite-dimensional, $E$ and $F$ in a common universe, and $P$ second countable. If $g$ is smooth, $N\setminus g(P)$ is dense. If $g$ is only smooth on an open set $U\subseteq P$, then $N\setminus g(U)$ is dense; if moreover $N$ is Hausdorff, then $g(K)$ is closed and nowhere dense for every compact $K\subseteq U$, and $g(U)$ is meagre.
>
> (c) For $p\ge 1$, the set $\{(a,b)\in S^p\times S^p : a\neq b\}$ is connected.
>
> (d) Let $S$ be a preconnected subset of a topological space, and $R$ a set with $S\subseteq\overline{R\cap S}$. Suppose every $x\in S$ has a neighbourhood $V$ such that $\varphi$ is constant on $V\cap R\cap S$. Then $\varphi$ is constant on $R\cap S$.
>
> (e) In a Baire space, every nonempty open set contains points outside any given meagre set.

*The proof as formalized.* For (a), $dg_x$ maps a space of smaller dimension and cannot be onto ⟦Chapter8/Generic · not_isRegularValue_of_finrank_lt⟧. For (b), the regular values are dense by Brown's theorem, and by (a) they avoid the image ⟦Chapter8/Generic · dense_compl_range_of_finrank_lt⟧. For $g$ smooth on $U$, apply this to the open submanifold $U$ ⟦Chapter8/Generic · Generic.dense_compl_image_of_finrank_lt⟧. The image of a compact $K\subseteq U$ is compact, hence closed, with empty interior ⟦Chapter8/Generic · isNowhereDense_image_of_finrank_lt⟧. Being locally compact and second countable, $U$ is a countable union of compact sets, so $g(U)$ is a countable union of closed nowhere dense sets ⟦Chapter8/Generic · isMeagre_image_of_finrank_lt⟧.

For (c), the antipodal pairs $(c,-c)$ form a connected set off the diagonal, the image of the connected sphere. A pair $(a,b)$ with $a\neq b$ is joined to $(a,-a)$ by
$$t\mapsto\Bigl(a,\ \frac{(1-t)\,b - t\,a}{|(1-t)\,b - t\,a|}\Bigr),\qquad 0\le t\le 1.$$
The vector $(1-t)b-ta$ vanishes only if $|1-t| = |t|$, which forces $t = \tfrac12$ and $b = a$. If its normalization were $a$, comparing norms in $(1-t)\,b = (t + |(1-t)b-ta|)\,a$ would again force $b = a$ ⟦Chapter8/Generic · isConnected_offDiag_sph⟧.

For (d), let $\psi(x)$ be the common value of $\varphi$ on $V_x\cap R\cap S$, which is nonempty by density. Then $\psi = \varphi$ on $R\cap S$, and $\psi$ is locally constant on $S$: for $x'$ near $x$, a point of $V_{x'}\cap\operatorname{int}V_x\cap R\cap S$ shows $\psi(x') = \psi(x)$. The formal proof gives the set of values the discrete topology, so that local constancy becomes continuity ⟦Chapter8/Generic · eq_of_locallyConst_on_dense⟧. Part (e) is Baire's theorem ⟦Chapter8/Generic · exists_mem_open_not_mem_of_isMeagre⟧. Parts (c) and (d) serve the Hopf invariant in Part X, and (b) and (e) are used below.

### V8.13 Problem 13: the linking number

#### The definition

Let $A, B$ be smooth manifolds without boundary modelled on $\mathbb R^a$ and $\mathbb R^b$, oriented by $o_A, o_B$. Let $k = a+b$ and $\alpha: A\to\mathbb R^{k+1}$, $\beta: B\to\mathbb R^{k+1}$. The linking map is
$$\lambda_{\alpha,\beta}(x,y) = \frac{\alpha(x)-\beta(y)}{|\alpha(x)-\beta(y)|}\in S^k.$$
Normalization sends $0$ to a fixed base point, so $\lambda_{\alpha,\beta}$ is defined everywhere ⟦Chapter6/Region · nv0⟧ ⟦Chapter8/Linking · linkMap⟧ ⟦Chapter8/Linking · linkMap_val⟧. It is smooth when $\alpha, \beta$ are smooth with $\alpha(x)\neq\beta(y)$ for all $x, y$ ⟦Chapter8/Linking · contMDiff_linkMap⟧. The linking number $l(\alpha,\beta)$ is the degree of $\lambda_{\alpha,\beta}$. Here $A\times B$ carries the product orientation, relabelled from index $a+b$ to index $k$, and $S^k$ carries $O_k$, its orientation as the boundary of the disk ⟦Chapter8/Linking · linkingNumber⟧. Milnor's disjoint $M, N\subseteq\mathbb R^{k+1}$ are the case of inclusions. Allowing maps costs nothing, and the sphere part needs it.

#### Symmetry

> **Theorem.** Let $A, B$ be as above, and in addition compact, Hausdorff and second countable. Let $k = a+b>0$, and let $\alpha,\beta$ be smooth with $\alpha(x)\neq\beta(y)$ for all $x, y$. Then
> $$l(\beta,\alpha) = (-1)^{(a+1)(b+1)}\,l(\alpha,\beta).$$

*The idea.* $\lambda_{\beta,\alpha}$ is the swap, followed by $\lambda_{\alpha,\beta}$, followed by the antipodal map. The swap has sign $(-1)^{ab}$, the antipodal map has sign $(-1)^{k+1}$, and $ab + k + 1 = (a+1)(b+1)$. This is the expected proof.

*The proof as formalized.* The identity $\lambda_{\beta,\alpha}(y,x) = -\lambda_{\alpha,\beta}(x,y)$ is immediate ⟦Chapter8/Linking · linkMap_swap⟧. The swap $B\times A\to A\times B$ has sign $(-1)^{ab}$ for the relabelled product orientations. The relabelling $a+b\to k$ of $A\times B$ is split as $a+b\to b+a\to k$; the common step $b+a\to k$ is then removed from both sides, and what remains is the swap sign of V8.0 (ii) ⟦Chapter8/Linking · orient_cast_cast⟧ ⟦Chapter8/Linking · signAt_swap_cast⟧. The antipodal map has sign $(-1)^{k+1}$ at every point for $O_k$. This is Chapter 5's value for $O^5_k$, carried over by $O_k = \pm O^5_k$, which needs $k>0$ ⟦Chapter5/HairyBall · signAt_antip⟧ ⟦Chapter8/Linking · signAt_antip_std⟧. Brown's theorem gives a regular value $z$ of $\lambda_{\alpha,\beta}$. Then $-z$ is a regular value of $\lambda_{\beta,\alpha}$, since by the chain rule the sign at each of its preimages is a product of three nonzero signs. Composing on either side with a bijection of constant sign $\sigma$ multiplies the signed count by $\sigma$ ⟦Chapter6/Compose · degAt_comp_bij'⟧ ⟦Chapter6/Compose · degAt_comp_bij_left⟧. Hence $\deg\lambda_{\beta,\alpha} = (-1)^{ab}(-1)^{k+1}\deg\lambda_{\alpha,\beta}$ for any orientations of $A\times B$ and $B\times A$ related by a swap of sign $(-1)^{ab}$ ⟦Chapter8/Linking · deg_linkMap_swap⟧ ⟦Chapter8/Linking · linkingNumber_symm⟧.

*Hidden hypothesis.* The condition $k>0$ is used twice. The degree may be computed at any regular value only when the target is connected, and $S^0$ is not. The comparison of $O_k$ with $O^5_k$ also runs through connectedness.

#### Bounding

Milnor's hypothesis "$M$ bounds an oriented manifold $X$ disjoint from $N$" is taken in the ambient form that the formal text uses for manifolds with boundary throughout.

> **Theorem.** Let $B$ be a smooth manifold without boundary modelled on $\mathbb R^b$, compact, Hausdorff, second countable and oriented. Let $W$ be a smooth manifold without boundary modelled on $\mathbb R^{a+1}$, Hausdorff, second countable and oriented. Let $g: W\to\mathbb R$ be smooth, with $0$ a regular value and $X = \{g\ge 0\}$ compact. Let $k = a+b>0$, and let $\bar\alpha: W\to\mathbb R^{k+1}$ and $\beta: B\to\mathbb R^{k+1}$ be smooth with $\bar\alpha(w)\neq\beta(y)$ whenever $g(w)\ge 0$. Give $A = g^{-1}(0)$ its submanifold structure and the boundary orientation, outward vector first. Then $l(\bar\alpha|_A,\beta) = 0$.

*The idea.* The linking map extends over $X\times B$, a compact region in $W\times B$ with boundary $A\times B = \{G = 0\}$, where $G(w,y) = g(w)$. A map that extends over a compact region has degree $0$ on its boundary. What must be checked is that the boundary orientation of $A\times B$ inside $W\times B$ is the product orientation.

*The linear algebra.* Let $E_1, F, Z_1, Z$ have dimensions $m+1, n, m, m+n$, with orientations $o_E$ of $E_1$ and $o_F$ of $F$. Let $l$ be a linear form on $E_1$, let $T : Z_1\to E_1$ be injective with image in $\ker l$, and let $l(\nu)<0$. Let $S: Z\to E_1\times F$ have image $\{v : l(v_1) = 0\}$, let $l(\nu^P_1) <0$, and let $S\circ D = T\times\mathrm{id}_F$. Then $D$ carries (the contraction of $o_E$ by $\nu$ along $T$) $\times\,o_F$ to the contraction of the relabelled $o_E\times o_F$ by $\nu^P$ along $S$, with sign $+1$. Indeed $\nu^P = c\,(\nu,0) + St$ with $c = l(\nu^P_1)/l(\nu)>0$, and $St$, lying in the image of $S$, contributes nothing ⟦Chapter6/SignLemmas · contractForm_eq_smul⟧. On the concatenated basis, the target form is evaluated on the block-triangular family $((\nu,0), (Tu_i,0), (0,f_j))$. The two forms then differ by $c$ times squares of signs ⟦Chapter8/Linking · mul_orEpsB_pos⟧ ⟦Chapter8/Linking · orSign_contractOr_prod⟧.

*The proof as formalized.*

1. $A$ is compact, being closed in $X$, and $S^{a+b}$ is connected ⟦Chapter8/Linking · linkingNumber_eq_zero_of_bounds⟧.
2. $P = W\times B$ carries the product orientation, relabelled to index $a+b+1$. It is also transferred to the model $\mathbb R^{a+1}\times\mathbb R^b$. Mathlib's product of two models equals the model of the product space without being identical to it, and the level-set results are stated for the latter ⟦Chapter8/Linking · Orient.ofEqModel⟧. The function $G = g\circ\mathrm{pr}_1$ has $0$ as a regular value, and $L = G^{-1}(0)$ gets the boundary orientation ⟦Chapter6/LevelOrientM · levelOrientM⟧.
3. The bijection $\varphi: A\times B\to L$, $\varphi(w,y) = (w,y)$, is smooth, and $d\iota_L\circ d\varphi = d\iota_A\times\mathrm{id}$. The linear algebra with $l = dg_w$ gives $\operatorname{sign}\varphi = +1$ everywhere ⟦Chapter8/Linking · orSign_contractOr_prod⟧.
4. The map $\lambda(w,y) = (\bar\alpha(w)-\beta(y))/|\bar\alpha(w)-\beta(y)|$ is smooth on the open set $U = \{\bar\alpha(w)\neq\beta(y)\}$, which contains $X\times B$. The regular values of $\lambda|_U$ are dense by Brown's theorem. Those of the linking map of $A\times B$ are open and dense, since $A\times B$ is compact. The sphere is a Baire space, so the two sets share a point $e$ ⟦Chapter6/RegularOpen · dense_isOpen_regularValues⟧ ⟦Chapter6/RegularOpen · exists_mem_of_dense_of_isOpen⟧.
5. At $x\in L$ with $\lambda(x) = e$, both $\lambda$ and $\lambda|_L$ are regular: the former because $x\in U$, the latter by the chain rule through $\varphi$. So the kernel line of $d\lambda_x$ is transverse to $L$ ⟦Chapter6/LevelZero · exists_mfd_eq_zero_of_isRegularPoint_level⟧. The set $\{\lambda = e\}\cap(X\times B)$ is compact.
6. Lemma 1 of §5, in its boundary form for a map smooth on an open set containing the level set, gives $\deg_e(\lambda|_L) = 0$ ⟦Chapter6/LevelZero · degAt_level_eq_zero_of_opens⟧. Transported along $\varphi$, which has sign $+1$, this is $\deg_e$ of the linking map of $A\times B$, that is, $l(\bar\alpha|_A,\beta)$ ⟦Chapter6/LevelMap · degAt_comp_bij⟧ ⟦Chapter8/Linking · orient_cast_self⟧.

### V8.13′ Problem 13: linking numbers in the sphere

Milnor's last sentence, "Define the linking number for disjoint manifolds in the sphere $S^{m+n+1}$", asks for a definition. The natural one projects stereographically from a point off both manifolds. This defines something only if the result does not depend on the point, and that is a theorem.

#### The definition

Stereographic projection from the north pole $N = e_{k+1}$ of $S^{k+1}\subseteq\mathbb R^{k+2}$ is
$$\operatorname{st}(x) = \frac{(x_0,\dots,x_k)}{1-x_{k+1}}\in\mathbb R^{k+1},$$
Chapter 7's projection onto the equatorial hyperplane, read in coordinates ⟦Chapter8/LinkingDefs · stN⟧ ⟦Chapter8/LinkingDefs · ι_stN⟧. It is injective on $S^{k+1}\setminus\{N\}$ and smooth where $x_{k+1}\neq 1$ ⟦Chapter8/LinkingDefs · stN_injOn⟧ ⟦Chapter8/LinkingDefs · contDiffAt_stN⟧. A *rotation* is a linear isometry of $\mathbb R^{k+2}$ with positive determinant ⟦Chapter8/LinkingDefs · IsRotation⟧. For $\alpha: A\to S^{k+1}$, $\beta: B\to S^{k+1}$ and a linear isometry $R$, set $l_R(\alpha,\beta) = l(\operatorname{st}\circ R\circ\alpha,\ \operatorname{st}\circ R\circ\beta)$ ⟦Chapter8/LinkingDefs · linkingNumberRot⟧. Whenever $R\alpha$ and $R\beta$ avoid $N$, the projected maps are smooth, and disjoint when $\alpha,\beta$ are ⟦Chapter8/LinkingDefs · contMDiff_stN_comp⟧ ⟦Chapter8/LinkingDefs · stN_comp_disjoint⟧. Call a rotation $R$ *admissible* if $R\alpha$ and $R\beta$ avoid $N$. Finally, $l_{\mathrm{sph}}(\alpha,\beta)$ is $l_R$ for a chosen rotation $R$ with $R\alpha(x)\neq N$ and $R\beta(y)\neq N$ for all pairs $(x,y)$, and $0$ if there is none ⟦Chapter8/LinkingSphere · linkingNumberSph⟧.

> **Theorem.** Let $A, B$ be smooth manifolds without boundary modelled on $\mathbb R^a$ and $\mathbb R^b$, second countable, with $a,b\ge 1$ and $k = a+b$. Let $\alpha: A\to S^{k+1}$ and $\beta: B\to S^{k+1}$ be smooth.
>
> (a) There is a rotation $R$ with $R\alpha(x)\neq N$ and $R\beta(y)\neq N$ for every pair $(x,y)\in A\times B$.
>
> (b) Suppose moreover that $A, B$ are compact, Hausdorff and oriented, and that $\alpha(x)\neq\beta(y)$ for all $x, y$. Then $l_{\mathrm{sph}}(\alpha,\beta) = l_R(\alpha,\beta)$ for every rotation $R$ with $R\alpha(x)\neq N$ and $R\beta(y)\neq N$ for every pair $(x,y)\in A\times B$.
>
> When $A$ and $B$ are nonempty, the condition on $R$ in (a) and (b) says that $R$ is admissible.

*The idea.* An admissible rotation carries a point $q$ off both images to the north pole. Which rotation does so is irrelevant, by linear algebra. Moving $q$ continuously while keeping it off both images changes $l_R$ only by a homotopy. Two admissible points can be joined through a common point $w$ by two great-circle arcs that avoid both images, provided the bad choices of $w$ form a meagre set. This is where $a,b\ge 1$ enters.

*The proof as formalized.*

1. *Existence.* By V8.0 (v), $\alpha(A)\cup\beta(B)$ is meagre, since $a, b<k+1$. So some $q$ avoids it, and a planar rotation carries $q$ to $N$ ⟦Chapter7/Rotation · exists_rotation_path⟧ ⟦Chapter8/LinkingSphere · exists_admissible_rotation⟧. The hypotheses $a, b\ge 1$ appear in this statement but are not needed: $a, b<k+1$ already follows from $a+b = k$.
2. *Linear maps of positive determinant.* Let $\det T>0$. Then $\lambda_{T\alpha,T\beta} = h\circ\lambda_{\alpha,\beta}$ with $h(u) = Tu/|Tu|$, a bijection of $S^k$ ⟦Chapter8/LinkingSphere · bijective_nv0_linear⟧. Its sign is $\operatorname{sgn}\det T = +1$ at every point. Chapter 6 proved this for $O^5_k$, and it carries over to $O_k$ ⟦Chapter6/Radial · signAt_nv0_linear⟧ ⟦Chapter8/LinkingSphere · signAt_nv0_linear_std⟧. Hence $l(T\alpha,T\beta) = l(\alpha,\beta)$ for maps $\alpha,\beta$ into $\mathbb R^{k+1}$ as in V8.13, when $k>0$ ⟦Chapter8/LinkingSphere · linkingNumber_comp_linear⟧.
3. *Rotations fixing the north pole.* Let $Q$ be a rotation with $QN = N$. It preserves the last coordinate, since $\langle Qx,N\rangle = \langle Qx,QN\rangle = \langle x,N\rangle$. So $\operatorname{st}(Qx) = T_Q(\operatorname{st}x)$, where $T_Q$ is the block of $Q$ on the first $k+1$ coordinates ⟦Chapter8/LinkingSphere · stN_map_of_fix⟧. The last column of $Q$ is $e_{k+1}$, and Laplace expansion along it gives $\det T_Q = \det Q>0$ ⟦Chapter8/LinkingSphere · det_restrictN⟧. By step 2, $l_{Q\circ R} = l_R$ for every linear isometry $R$, rotation or not, with $R\alpha$ and $R\beta$ avoiding $N$ ⟦Chapter8/LinkingSphere · linkingNumberRot_trans_of_fix⟧.
4. *Families of rotations.* Let $S_t$ be linear isometries depending smoothly on $t$, with $S_t\alpha$ and $S_t\beta$ avoiding $N$ for $0\le t\le 1$. A formal homotopy is defined for all $t\in\mathbb R$, so time is reparametrized by a smooth transition function $\rho$ with values in $[0,1]$, $\rho(0) = 0$ and $\rho(1) = 1$. The linking maps of $\operatorname{st}\circ S_{\rho(t)}\circ\alpha$ and $\operatorname{st}\circ S_{\rho(t)}\circ\beta$ then form a smooth homotopy on $A\times B\times\mathbb R$. Homotopy invariance of the degree (Milnor's Theorem B of §5) gives $l_{S_0} = l_{S_1}$ ⟦Chapter5/Degree · deg_eq_of_homotopy⟧ ⟦Chapter8/LinkingSphere · linkingNumberRot_eq_of_family⟧.
5. *Arcs and bad midpoints.* For unit vectors $q$ and $w\neq -q$, one has $w = \cos\theta\,q + \sin\theta\,v$ with $v$ a unit vector orthogonal to $q$ and $0\le\theta<\pi$ ⟦Chapter8/LinkingSphere · exists_arc⟧. Suppose a point $c\neq q$ lies on the arc $s\mapsto\cos s\,q+\sin s\,v$, $0\le s\le\theta$. Then $c - rq = \mu w$ for $\mu = \sin s/\sin\theta>0$ and $r = \cos s-\mu\cos\theta$, so $w = (c-rq)/|c-rq|$ ⟦Chapter8/LinkingSphere · arc_avoid⟧. Geometrically, and this picture is not formalized, a point $c\neq\pm q$ thus spoils only the open half great circle from $q$ through $c$ to $-q$. For a smooth $\gamma: X\to S^{k+1}$, the spoiled points form the "cone", the image of the open set $\{\gamma(x)\neq rq\}\subseteq X\times\mathbb R$ under $(x,r)\mapsto(\gamma(x)-rq)/|\gamma(x)-rq|$. If $\dim X+1<k+1$, the cone is meagre ⟦Chapter8/LinkingSphere · isMeagre_cone⟧. For $\alpha$ and $\beta$ this condition reads $a<k$ and $b<k$, that is, $b\ge 1$ and $a\ge 1$. Given $q, q'$ on the sphere, Baire's theorem gives $w\neq -q, -q'$ outside the four cones of $\alpha$ and $\beta$ seen from $q$ and from $q'$ ⟦Chapter8/LinkingSphere · isMeagre_singleton_sph⟧ ⟦Chapter8/LinkingSphere · exists_good_point⟧.
6. *One leg.* Let $R$ be admissible and $q = R^{-1}N$, and choose $w$ as in step 5. Put $S_t = R\circ\operatorname{rot}_{q,v}(-t\theta)$, where $\operatorname{rot}_{q,v}$ rotates the plane of $q$ and $v$ ⟦Chapter7/Rotation · rotCLM⟧ ⟦Chapter8/LinkingSphere · rotLIE⟧. Then $S_t(c) = N$ exactly when $c = \cos(t\theta)\,q+\sin(t\theta)\,v$, a point of the arc. No point of $\alpha(A)\cup\beta(B)$ lies there: such a point differs from $q$ because $R$ is admissible, and step 5 excludes the rest of the arc. So step 4 applies. The rotation $S_1$ is admissible, sends $w$ to $N$, and has $l_{S_1} = l_R$ ⟦Chapter8/LinkingSphere · isRotation_rotLIE⟧ ⟦Chapter8/LinkingSphere · exists_leg⟧.
7. *Independence.* Let $R, R'$ be admissible, and take $w$ good for $q = R^{-1}N$ and $q' = R'^{-1}N$. The two legs give admissible rotations $S, S'$ with $Sw = S'w = N$, $l_R = l_S$ and $l_{R'} = l_{S'}$. Then $Q = S\circ S'^{-1}$ is a rotation fixing $N$ with $S = Q\circ S'$, so step 3 gives $l_S = l_{S'}$ ⟦Chapter8/LinkingSphere · isRotation_trans⟧ ⟦Chapter8/LinkingSphere · isRotation_symm⟧ ⟦Chapter8/LinkingSphere · linkingNumberRot_eq_of_admissible⟧.
8. *The chosen rotation.* The condition in the definition of $l_{\mathrm{sph}}$ quantifies over pairs $(x,y)$, so it says nothing when $A$ or $B$ is empty. That case is treated separately: both sides are degrees of a map from the empty manifold, hence $0$. Otherwise the chosen rotation is admissible, and step 7 applies ⟦Chapter8/LinkingSphere · linkingNumber_of_isEmpty⟧ ⟦Chapter8/LinkingSphere · linkingNumberSph_eq⟧.

#### Why both dimensions must be positive

The formal text states the following example as a remark and does not formalize it. Let $a = 0$ and $b = k\ge 1$. Let $A$ be a point mapped to $p$, and let $\beta$ be the inclusion of a great $k$-sphere $\Sigma\subseteq S^{k+1}$ not through $p$. Projection from $q\notin\Sigma\cup\{p\}$ carries $\Sigma$ to a round sphere $\Sigma'\subseteq\mathbb R^{k+1}$. It sends the hemisphere containing $q$ to the unbounded side of $\Sigma'$ and the other hemisphere to the ball. A point inside $\Sigma'$ has linking number $\pm1$ with it, and a point outside has linking number $0$. So $l_R = 0$ when $R^{-1}N$ lies on the same side of $\Sigma$ as $p$, and $l_R = \pm1$ otherwise. In the proof, the cone of $\Sigma$ has dimension $b+1 = k+1$ and is not meagre: a projection point cannot pass from one side of $\Sigma$ to the other without crossing it.

### What the formalization taught us

- *Dimensions are indices.* Orientations carry their dimension as an index, so $m+n$, $n+m$ and $k$ are matched by explicit relabelling, as are the product of two models and the model of a product. No sign changes, but every statement about products has to say so ⟦Chapter8/OrientProd · signAt_cast⟧ ⟦Chapter8/Linking · Orient.ofEqModel⟧.
- *Milnor's orientation of the sphere had to be built.* Chapter 5's orientation is the boundary orientation of the exterior of the ball, relative to an unspecified basis. Degrees of maps of the sphere to itself cannot see this, but linking numbers can. They use the frame orientation, related to the old one only up to sign ⟦Chapter8/OrientFrame · sphOrStd⟧ ⟦Chapter8/OrientFrame · sphOrStd_eq_or_neg⟧.
- *Compact preimages suffice.* Local constancy and homotopy invariance of the signed count need compactness only of $f^{-1}(V)$, or of the part of $F^{-1}(V)$ over $[0,1]$ ⟦Chapter8/ProperDegree · IsRegularValue.eventually_degAt_eq_of_isCompact⟧ ⟦Chapter8/ProperDegree · degAt_eq_of_homotopy_of_isCompact⟧.
- *$k>0$ for linking numbers.* For $k = 0$ the target $S^0$ of the linking map is disconnected ⟦Chapter8/Linking · deg_linkMap_swap⟧.
- *The boundary orientation of a product is the product orientation*, when the normal and the bounding factor both come first. No sign appears, but the check is a genuine computation ⟦Chapter8/Linking · orSign_contractOr_prod⟧.
- *Positive dimensions in the sphere.* Independence of the rotation fails for a point and a great sphere, by an example that is not formalized. The proof uses $a,b\ge 1$ exactly to make the cones meagre, and existence of admissible rotations does not need it ⟦Chapter8/LinkingSphere · isMeagre_cone⟧ ⟦Chapter8/LinkingSphere · exists_admissible_rotation⟧.
- *Conventions of the formal definitions.* Homotopies are maps on $X\times\mathbb R$, so a family that is admissible only for $t\in[0,1]$ must be reparametrized. The linking number in the sphere is $0$ when no rotation satisfies its admissibility clause, and that clause is vacuous when one manifold is empty ⟦Chapter8/LinkingSphere · linkingNumberRot_eq_of_family⟧ ⟦Chapter8/LinkingSphere · linkingNumberSph_eq⟧.


## Part X. The Hopf invariant (Milnor §8, Problems 14–15)

Problem 14 asks for three properties of the linking number of two fibres of a map $f : S^{2p-1} \to S^p$; Problem 15 asks for three consequences. The formal proof organizes all six around one observation. For maps $g, f$ into $S^p$, the linking number of $g^{-1}(y)$ and $f^{-1}(z)$ is a *local degree*: the local degree at $((y,z),e)$ of the map $\Phi(x,x') = ((g(x), f(x')), \lambda(x,x'))$, defined on pairs of distinct points of $S^{2p-1}$ away from a projection point, where $\lambda$ is the direction between the stereographic images of $x$ and $x'$ ⟦Chapter8/LinkDegree · degAt_phiR_eq_linkingNumberRot⟧. Local degrees survive homotopies whose preimages stay in a compact region, and they behave well under composition. Everything else is a matter of choosing the right homotopies. On the way the formalization has to fix how a fibre is oriented, compare two signs through a block determinant, supply a compactness argument the book leaves unsaid, and add a hypothesis to the natural two-map version of a). And when everything is computed with the book's conventions, the Hopf fibration turns out to have Hopf invariant $-1$, not $+1$.

**Conventions.** Throughout, $p = d+1$ with $d \ge 1$ (so $p \ge 2$), and $S$ denotes $S^{2d+1} = S^{2p-1}$. Spheres $S^n \subset \mathbb R^{n+1}$ carry Milnor's orientation as boundaries of disks, *outward normal first*: a basis $\zeta$ of $T_qS^n$ is positive iff $\det(q, \zeta_1, \dots, \zeta_n) > 0$ ⟦Chapter8/OrientFrame · sphOrStd⟧ ⟦Chapter8/HopfSign · orientation_eq_sphOrStd_iff⟧. For compact oriented $A^a$, $B^b$ and maps $\alpha, \beta$ into $\mathbb R^{k+1}$ with disjoint images, $k = a+b$, the linking number is the degree of $\lambda(x,y) = (\alpha(x)-\beta(y))/\|\alpha(x)-\beta(y)\|$ on $A \times B$ with the product orientation ⟦Chapter8/Linking · linkMap⟧ ⟦Chapter8/Linking · linkingNumber⟧. In a sphere $S^{k+1}$ one first applies a rotation $R$ (a linear isometry of positive determinant) that keeps the north pole $\mathbf n = e_{k+1}$ off both images, then projects by $\mathrm{st}(x) = (x_0, \dots, x_k)/(1-x_{k+1})$; call the result $l_R$ ⟦Chapter8/LinkingDefs · stN⟧ ⟦Chapter8/LinkingDefs · linkingNumberRot⟧. The linking number in the sphere is $l_R$ for a chosen admissible $R$, and $0$ if none exists; by V8.13′ the choice does not matter when $a, b \ge 1$ and the images are disjoint ⟦Chapter8/LinkingSphere · linkingNumberSph⟧ ⟦Chapter8/LinkingSphere · linkingNumberSph_eq⟧. For a map $\Phi$ between oriented manifolds of equal dimension, $\operatorname{sign}_x\Phi$ is the sign of $d\Phi_x$ ($0$ if singular) and $\deg_w\Phi = \sum_{x \in \Phi^{-1}(w)} \operatorname{sign}_x\Phi$.

**Map of the part.**

1. `PreimOrient`: the orientation of the fibre $f^{-1}(y)$ of a map between spheres, frame first, with its chart-level description.
2. `LinkAlg`: the block-determinant lemma comparing the sign of $(x,x') \mapsto ((Dx, D'x'), L(x,x'))$ with the sign of $L$ on the kernels.
3. `LinkDegree`: the domain $D_R$ and the map $\Phi$; linking number $=$ local degree; homotopy invariance (the engine).
4. `HopfInvariant`: the linking number of two fibres, transport, moves, Problem 14 a), b), c), and the definition of $H$.
5. `HopfMap`: the Hopf fibration as a quadratic map, Milnor's formula, regularity, two fibres and the pair realizing a direction.
6. `HopfSign`: the fibres over $(\pm1,0,0)$ have linking number $-1$.
7. `HopfComp`: the local composition formula and its consequence for fibres of $g \circ f$.
8. `HopfProps`: Problem 15 (odd $p$, compositions, $H(\pi) = -1$).

### V8.0 (iii) Orienting the fibre of a regular value

Milnor says the fibres "can be oriented as in §5". In §5 the fibre $A = F^{-1}(y)$ was a curve. A tangent vector $v_1$ of $A$ is positive when, completed by $v_2, \dots$ to a positive basis of the ambient tangent space, the vectors $v_2, \dots$ are carried by $dF$ to a positive basis of the target. So the tangent vector comes first and lifts of a positive basis come after. For a $d$-dimensional fibre of a map with $p$-dimensional target, the natural generalization lists the $d$ tangent vectors first. The formalization lists them last.

**Definition (fibre orientation).** Let $f : S^{d+p} \to S^p$ be smooth, $y$ a regular value, and $e = (e_1, \dots, e_p)$ a positive basis of $T_yS^p$, read in the chart $c_y$ of $S^p$ at $y$. The fibre $N = f^{-1}(y)$ is a $d$-dimensional submanifold given by slice charts ⟦Chapter8/PreimOrient · isSliceSubmanifold_preim⟧. Let $\tilde F(z) = c_y(f(z/|z|))$ be the radial extension of the chart expression of $f$, let $A = d\tilde F_x$, and let $v_i(x) = A^*(AA^*)^{-1}e_i$. A basis $w$ of $T_xN$ is positive iff $(x, v_1(x), \dots, v_p(x), w_1, \dots, w_d)$, with the $w_j$ read in $\mathbb R^{d+p+1}$, is a positive basis of $\mathbb R^{d+p+1}$ ⟦Chapter8/PreimOrient · sphExt⟧ ⟦Chapter8/PreimOrient · sphPullFrame⟧ ⟦Chapter8/PreimOrient · preimOr⟧.

**Proposition.** (i) For any vectors $u_1, \dots, u_p$ tangent to $S^{d+p}$ at $x$ with $df_x(u_i) = e_i$: $w$ is positive iff $(u_1, \dots, u_p, w_1, \dots, w_d)$ is positive for the orientation of $S^{d+p}$ ⟦Chapter8/PreimOrient · preimOr_or_eq⟧. (ii) Two positive bases $e, e'$ of $T_yS^p$ give the same orientation ⟦Chapter8/PreimOrient · preimOr_eq_of_orientation_eq⟧.

So the formal convention is "lifts first, tangent vectors last" ⟦Chapter8/PreimOrient · preimOr_or_eq⟧. The comparison with §5 is not a formal lemma but a count: the §5-style convention differs by moving $p$ vectors past $d$ vectors, a factor $(-1)^{dp}$. In the Hopf setting $d = p-1$, so $dp = (p-1)p$ is even and the two conventions agree; there the fibres are oriented "as in §5" literally.

*The idea: an ambient frame.* An orientation of a manifold in the formal library is an orientation of each chart space, varying continuously. The general device that produces one takes a smooth map $\iota$ into a vector space $E$ and a continuous family of frames $\nu(q)$ such that the form $z \mapsto \Omega(\nu(q), d\iota\,z)$ never vanishes (so $\iota$ is an immersion and the frames are complementary), and declares $z$ positive iff $\Omega(\nu(q), d\iota\,z) > 0$ for a positive volume form $\Omega$ of $E$. Continuity is proved once, by a chart argument ⟦Chapter8/OrientFrame · Orient.ofFrame⟧. The sphere itself is oriented this way, with the one-vector frame $(q)$; the fibre uses the frame $(x, v_1(x), \dots, v_p(x))$ ⟦Chapter8/PreimOrient · preimFrame⟧. Chapter 7's Pontryagin framing would have been the obvious candidate, but it is set up for ambient manifolds presented with a different normal model than the formal sphere, a mismatch of presentation rather than of mathematics. The explicit extension $\tilde F$ takes the place of its tubular retraction.

*The proof as formalized.*

1. *The extension.* $\tilde F$ is smooth near every point of $N$. By the chain rule, $A \circ d\iota_x = df_x$, where $\iota$ is the inclusion of the sphere ⟦Chapter8/PreimOrient · sphExtDer_comp_mfd_val⟧. Since $\tilde F$ is constant along rays, $Ax = 0$ ⟦Chapter8/PreimOrient · sphExtDer_self⟧, and $A$ is onto because $df_x$ is ⟦Chapter8/PreimOrient · surjective_sphExtDer⟧.
2. *The frame.* The vector $v_i = A^*(AA^*)^{-1}e_i$ satisfies $Av_i = e_i$ and lies in $\operatorname{im}A^* = (\ker A)^\perp$, so it is orthogonal to $x$, hence tangent to the sphere ⟦Chapter8/PreimOrient · sphExtDer_sphPullFrame⟧ ⟦Chapter8/PreimOrient · inner_sphPullFrame⟧. It is continuous along $N$ (indeed smooth near it), since inversion is smooth on invertible operators ⟦Chapter8/PreimOrient · continuous_sphPullFrame⟧.
3. *Reduction to the sphere.* Write $v_i = d\iota(c_i)$. For any lifts $u$ we have $df_x(c_i - u_i) = 0$, so $c_i - u_i$ is tangent to $N$. An alternating form in $d+p$ arguments vanishes when $d+1$ of them lie in the $d$-dimensional space $T_xN$. Hence the $d$-form $w \mapsto \Omega(x, c, w)$ on $T_xN$ does not change when $c$ is replaced by $u$. This is (i) ⟦Chapter8/PreimOrient · apply_vecCons_frameTuple_eq_zero⟧ ⟦Chapter8/PreimOrient · frameForm_congr_frame⟧ ⟦Chapter8/PreimOrient · frameForm_preimFrame⟧.
4. *Nondegeneracy.* The family $(u, w)$ is linearly independent when $df_x u$ is independent and $w$ is a basis of $\ker df_x$. So the form never vanishes, which is what the frame device needs ⟦Chapter8/PreimOrient · linearIndependent_frameTuple⟧ ⟦Chapter8/PreimOrient · frameForm_lift_ne_zero⟧.
5. *Independence of $e$.* Two bases with the same orientation are joined by a path of bases (Chapter 7's path-connectedness of the positive-determinant group). Along the lifted path, the form evaluated on a fixed basis of $T_xN$ is continuous and never zero, so by the intermediate value theorem it keeps its sign. The two forms are therefore positive multiples of each other ⟦Chapter8/PreimOrient · exists_pos_frameForm_lift⟧.

### Linear algebra for V8.14: the block determinant

The sign of $\Phi$ at a pair of fibre points must be compared with the sign of the linking map there. This is pure linear algebra.

**Lemma (two fibres).** Let $V$ have dimension $d+p$ with orientations $o_V, o_V'$, let $F$ have dimension $p$ with orientations $o_F, o_F'$, let $G$ be oriented of dimension $k = 2d$, and let $Z, Z'$ have dimension $d$. Let $D, D' : V \to F$ be linear, let $\iota : Z \to V$ and $\iota' : Z' \to V$ be injective with $\operatorname{im}\iota = \ker D$ and $\operatorname{im}\iota' = \ker D'$, and let $u, u' \in V^p$ be such that $Du$ is a positive basis for $o_F$ and $D'u'$ one for $o_F'$. Orient $Z$ frame first ($z$ positive iff $(u, \iota z)$ is positive for $o_V$), and $Z'$ likewise with $u'$ and $o'_V$. Then for every linear $L : V \times V \to G$,
$$\operatorname{sign}\bigl[(x,x') \mapsto ((Dx, D'x'), L(x,x'))\bigr] = (-1)^{dp}\,\operatorname{sign}\bigl[L \circ (\iota \times \iota')\bigr],$$
the left side relative to $o_V \times o_V'$ and $(o_F \times o_F') \times o_G$, the right side relative to the product of the two frame orientations and $o_G$ ⟦Chapter8/LinkDegree · orSign_pair_preimage₂⟧. The special case $o_V = o_V'$, $o_F = o_F'$ is also proved on its own ⟦Chapter8/LinkAlg · orSign_pair_preimage⟧.

*The idea.* In the bases $(u, \iota z)$ and $(u', \iota' z')$ the matrix is block triangular with identity blocks on the frames. The only sign comes from reordering $(u, \iota z, u', \iota' z')$ into $(u, u', \iota z, \iota' z')$, which moves $p$ vectors past $d$. So the number $(-1)^{dp}$ turns up again, for a different reason than in the fibre convention, and again it is $+1$ when $p = d+1$.

*The proof as formalized.*

1. *Frame orientation and positive bases.* $(u, \iota z)$ is a basis, and it is positive for $o_V$ iff $z$ is positive for the frame orientation ⟦Chapter8/LinkAlg · linearIndependent_frameTuple⟧ ⟦Chapter8/LinkAlg · frameOr_basis_iff⟧. Signs are computed in arbitrary bases as the sign of (orientation sign of source basis) $\times$ (orientation sign of target basis) $\times$ (determinant) ⟦Chapter8/LinkAlg · orSign_eq_sgn_det⟧.
2. *One fibre, no sign.* Let $W$ be oriented of dimension $b$ with $d+b = k$, and let $L : V \times W \to G$. Then $(x,w) \mapsto (Dx, L(x,w))$ has the sign of $L \circ (\iota \times \mathrm{id})$. In the bases $(u, \iota z, w)$ and $(Du, g)$, the vector $u_j$ goes to $(Du_j, \ast)$, while $\iota z_i$ and $w_l$ go to $(0, L(\cdot))$. The matrix is block lower triangular with identity upper block, and the orientation signs of the chosen bases match ⟦Chapter8/LinkAlg · orSign_single_preimage⟧.
3. *The mirror case.* With the fibre in the second factor, $(w,x) \mapsto (Dx, L(w,x))$ has $(-1)^{bp}$ times the sign of $L \circ (\mathrm{id} \times \iota)$. Compose with the swaps $W \times V \to V \times W$ (sign $(-1)^{b(d+p)}$) and $Z \times W \to W \times Z$ (sign $(-1)^{db}$) ⟦Chapter8/LinkAlg · orSign_single_preimage_right⟧ ⟦Chapter8/OrientProd · orSign_swap⟧.
4. *Two fibres.* Rebracket $(F \times F) \times G \to F \times (F \times G)$, which has sign $+1$ ⟦Chapter8/LinkAlg · orSign_prodAssoc⟧. Then apply step 2 to the first factor with $W = V$, and step 3 to the second factor with $W = Z$ and $b = d$.

### V8.14, the engine: linking numbers of fibres are local degrees

For a linear isometry $R$ of $\mathbb R^{2d+2}$, let
$$D_R = \{(x,x') \in S \times S : Rx \ne \mathbf n,\ Rx' \ne \mathbf n,\ x \ne x'\},$$
an open set ⟦Chapter8/LinkDegree · domR⟧. For smooth $g, f : S \to S^{d+1}$ define on $D_R$
$$\Phi(x,x') = \bigl((g(x), f(x')),\ \lambda_R(x,x')\bigr), \qquad \lambda_R(x,x') = \frac{\mathrm{st}(Rx)-\mathrm{st}(Rx')}{\|\mathrm{st}(Rx)-\mathrm{st}(Rx')\|} \in S^{2d}.$$
It is smooth on $D_R$: $\mathrm{st}$ is smooth off $\mathbf n$ and injective there, so the difference never vanishes ⟦Chapter8/LinkDegree · phiR⟧ ⟦Chapter8/LinkDegree · lamR⟧ ⟦Chapter8/LinkDegree · contMDiffAt_phiR⟧. Source and target both have dimension $4d+2$. $D_R$ carries the product orientation of $S \times S$, and the target $(S^{d+1} \times S^{d+1}) \times S^{2d}$ carries the product of the sphere orientations ⟦Chapter8/LinkDegree · orDomR⟧ ⟦Chapter8/LinkDegree · orTarget⟧.

**Theorem (linking number $=$ local degree).** Let $d \ge 1$ and let $f, g : S \to S^{d+1}$ be smooth. Let $y$ be a regular value of $g$ and $z$ one of $f$, with positive bases $e_y, e_z$ orienting $g^{-1}(y)$ and $f^{-1}(z)$, and suppose the two fibres are disjoint. Let $R$ be a rotation with $Rx \ne \mathbf n$ for all $x \in g^{-1}(y) \cup f^{-1}(z)$, and let $e \in S^{2d}$ be a regular value of the linking map of $\mathrm{st}\circ R$ on $g^{-1}(y) \times f^{-1}(z)$. Then $((y,z),e)$ is a regular value of $\Phi$ on $D_R$, and
$$\deg_{((y,z),e)}\Phi = l_R\bigl(g^{-1}(y), f^{-1}(z)\bigr)$$
⟦Chapter8/LinkDegree · isRegularValue_phiR⟧ ⟦Chapter8/LinkDegree · degAt_phiR_eq_linkingNumberRot⟧.

The hypothesis that $R$ has positive determinant is carried along but not used. It matters only for independence of $R$ (V8.13′).

*The idea.* The fibre of $\Phi$ over $((y,z),e)$ is the fibre of the linking map over $e$. At corresponding points the two signs agree, by the lemma above with $p = d+1$, where $(-1)^{d(d+1)} = 1$.

*The proof as formalized.*

1. *Signs at corresponding points.* At $(x,x')$ with $g(x) = y$ and $f(x') = z$, the derivative is $d\Phi = ((dg_x, df_{x'}), d\lambda_R)$, and the derivative of the linking map is $d\lambda_R \circ (d\iota \times d\iota')$. The tangent spaces of the fibres are the kernels ⟦Chapter8/LinkDegree · range_mfd_val_eq_ker⟧. By the chart description, the fibre orientations are frame orientations for lifts of $e_y$ and $e_z$. The block lemma applies with $V = \mathbb R^{2d+1}$ (the chart spaces at $x$ and $x'$, carrying the sphere's orientation at each point), $F = \mathbb R^{d+1}$ and $G = \mathbb R^{2d}$ ⟦Chapter8/LinkDegree · signAt_phiR_eq⟧.
2. *Regularity.* At a fibre point, the sign of the linking map is nonzero because $e$ is regular. So the sign of $\Phi$ is nonzero, and $d\Phi$ is invertible ⟦Chapter8/LinkDegree · isRegularValue_phiR⟧.
3. *Fibres.* The map $(x,x') \mapsto (x,x')$ carries the fibre of the linking map bijectively onto the fibre of $\Phi$. It lands in $D_R$ by disjointness and avoidance of $\mathbf n$, and it is onto because $\Phi(q) = ((y,z),e)$ forces $g(q_1) = y$ and $f(q_2) = z$. The linking number is the degree of the linking map, computed at the regular value $e$; here $d \ge 1$ makes $S^{2d}$ connected. Corresponding terms of the two sums are equal ⟦Chapter8/LinkDegree · degAt_phiR_eq_linkingNumberRot⟧.

**Theorem (homotopy invariance, the engine).** Let $d \ge 1$ and let $G, F : S \times \mathbb R \to S^{d+1}$ be smooth, with $G_t = G(\cdot,t)$ and $F_t = F(\cdot,t)$. (The smoothness of the four end maps is listed separately, though it follows.) Let $y$ be a regular value of $G_0$ and of $G_1$, $z$ one of $F_0$ and of $F_1$, and $e_y, e_z$ positive bases. Let $R$ be a rotation. Suppose that for every $t \in [0,1]$ the sets $G_t^{-1}(y)$ and $F_t^{-1}(z)$ are disjoint and do not meet $R^{-1}(\mathbf n)$. Then
$$l_R\bigl(G_0^{-1}(y), F_0^{-1}(z)\bigr) = l_R\bigl(G_1^{-1}(y), F_1^{-1}(z)\bigr)$$
⟦Chapter8/LinkDegree · linkingNumberRot_eq_of_homotopy⟧.

No regularity is assumed at intermediate times: $G_t^{-1}(y)$ need not be a manifold for $0 < t < 1$, and only disjointness and avoidance of $R^{-1}(\mathbf n)$ are required there. This is what makes the engine flexible, and everything below uses it.

*The proof as formalized.*

1. *A common direction.* The regular values of each end's linking map form an open dense set, since its domain is compact. So there is a common regular value $e$, and $((y,z),e)$ is regular for $\Phi_0$ and $\Phi_1$ ⟦Chapter6/RegularOpen · dense_isOpen_regularValues⟧ ⟦Chapter8/LinkDegree · contMDiff_linkMap_preim⟧.
2. *The homotopy.* $\Psi(q,t) = ((G_t(q_1), F_t(q_2)), \lambda_R(q))$ is smooth on $D_R \times \mathbb R$, with ends $\Phi_0$ and $\Phi_1$ ⟦Chapter8/LinkDegree · linkingNumberRot_eq_of_homotopy⟧.
3. *Compactness.* There are closed neighbourhoods $V_1 \ni y$ and $V_2 \ni z$ such that, for $t \in [0,1]$, $G_t(x) \in V_1$ and $F_t(x') \in V_2$ imply $(x,x') \in D_R$ ⟦Chapter8/LinkDegree · exists_isClosed_nhds_domR⟧. To see this, let $K = R^{-1}(\mathbf n) \times [0,1]$. The compact sets $G(K)$ and $F(K)$ miss $y$ and $z$. The compact set $\{(G(w), F(w)) : w \in S \times [0,1]\}$ misses $(y,z)$, by disjointness. One shrinks a product neighbourhood accordingly. The part of $\Psi^{-1}(V_1 \times V_2 \times S^{2d})$ over $[0,1]$ is then closed in the compact space $S \times S \times [0,1]$ and contained in $D_R \times [0,1]$, hence compact, although $D_R$ is not.
4. *Proper homotopy invariance.* A local degree does not change along a homotopy on a non-compact manifold, provided the value is regular for both end maps and the part over $[0,1]$ of the preimage of some neighbourhood of the value is compact ⟦Chapter8/ProperDegree · degAt_eq_of_homotopy_of_isCompact⟧. That result passes to a nearby value that is regular for the whole homotopy (Sard) and has the same local degrees at the ends, and then argues as in §5, with time reparametrized by $(1-\cos\pi t)/2$ so that regularity at the ends suffices. By the previous theorem, the local degrees at the two ends are the two linking numbers.

*What the book leaves implicit.* Milnor's arguments move fibres around. The formal statement says exactly what must not happen along the way. The moving fibres must not meet, or $\lambda$ is undefined. They must not cross the point from which one projects. And the relevant preimages must stay in a compact part of the non-compact domain $D_R$ ⟦Chapter8/LinkDegree · exists_isClosed_nhds_domR⟧.

### V8.14 Problem 14: the Hopf invariant

#### The linking number of two fibres

For smooth $g, f : S \to S^{d+1}$, a regular value $y$ of $g$ and a regular value $z$ of $f$, the symbol $l(g^{-1}(y), f^{-1}(z))$ denotes the linking number in the sphere $S^{2d+1}$ of the two fibres, oriented by chosen positive bases of $T_yS^{d+1}$ and $T_zS^{d+1}$ ⟦Chapter8/HopfInvariant · posB⟧ ⟦Chapter8/HopfInvariant · linkPre⟧. By V8.0 (iii) the chosen bases do not matter. If the fibres are disjoint and a rotation $R$ keeps $\mathbf n$ off both, then $l = l_R$ ⟦Chapter8/HopfInvariant · linkPre_eq_linkingNumberRot⟧. This is V8.13′ with $a = b = d$, which asks for $d \ge 1$; it is one place where the hypothesis $p \ge 2$ enters (for $p = 1$ the fibres would be finite sets in $S^1$).

Every point $q$ is carried to $\mathbf n$ by a rotation $R_q$ ⟦Chapter8/HopfInvariant · exists_rotation_to_north⟧. Avoiding $R_q^{-1}(\mathbf n)$ then simply means avoiding $q$. Fibres of regular values are meagre, so a point outside any two of them exists ⟦Chapter8/HopfInvariant · isMeagre_preim⟧ ⟦Chapter8/HopfInvariant · exists_ne_ne⟧. In this form the engine reads:

**Proposition (engine with a base point).** Let $d \ge 1$, let $G, F : S \times \mathbb R \to S^{d+1}$ be smooth (the smoothness of the four end maps is again listed separately), let $y$ be a regular value of $G_0$ and of $G_1$, and let $z$ be one of $F_0$ and of $F_1$. Suppose that for $t \in [0,1]$, $G_t(x) = y$ implies $F_t(x) \ne z$, and that some $q \in S$ satisfies $G_t(q) \ne y$ and $F_t(q) \ne z$ for all $t \in [0,1]$. Then $l(G_0^{-1}(y), F_0^{-1}(z)) = l(G_1^{-1}(y), F_1^{-1}(z))$ ⟦Chapter8/HopfInvariant · linkPre_eq_of_homotopy⟧.

#### Transport and moves

**Proposition (transport).** Let $d \ge 1$, let $g, f$ be smooth, let $y$ be regular for $g$ and $z$ for $f$, and suppose $g^{-1}(y) \cap f^{-1}(z) = \emptyset$. Let $\rho_1, \rho_2$ be orientation-preserving diffeomorphisms of $S^{d+1}$ (smooth bijections of sign $+1$ everywhere). Suppose also that $\rho_1 \circ g$ and $\rho_2 \circ f$ are smooth and that $\rho_1(y)$, $\rho_2(z)$ are regular values of them; these hypotheses are listed although they follow from the others. Then
$$l\bigl((\rho_1 g)^{-1}(\rho_1 y), (\rho_2 f)^{-1}(\rho_2 z)\bigr) = l\bigl(g^{-1}(y), f^{-1}(z)\bigr)$$
⟦Chapter8/HopfInvariant · IsPosDiffeo⟧ ⟦Chapter8/HopfInvariant · linkPre_comp_posDiffeo⟧.

The two sides concern the same sets, but their orientations are built from different positive bases and different maps. The formal proof never compares these orientations. It chooses $q$ outside both fibres, the rotation $R_q$, and a common regular value $e$ of the two linking maps. Then both sides are local degrees, of $\Phi$ at $((y,z),e)$ and of $\Phi' = ((\rho_1 \times \rho_2) \times \mathrm{id}) \circ \Phi$ at $((\rho_1 y, \rho_2 z), e)$. Composing with a bijection of constant sign $+1$ does not change local degrees ⟦Chapter6/Compose · degAt_comp_bij_left⟧. Planar rotations of the sphere are such diffeomorphisms ⟦Chapter8/HopfInvariant · isPosDiffeo_rotS⟧.

**Proposition (moves).** Let $\rho_i(\theta)$ be the rotation by $\theta$ in the plane of an orthonormal pair $u_i, v_i$ ⟦Chapter7/Rotation · rotCLM⟧. Let $d \ge 1$, let $g, f$ be smooth, and let $y$ be regular for $g$ and $z$ for $f$. Let $y' = \rho_1(\theta_1)y$ be regular for $g$ and $z' = \rho_2(\theta_2)z$ regular for $f$. Suppose that for $t \in [0,1]$ the equalities $g(x) = \rho_1(t\theta_1)y$ and $f(x) = \rho_2(t\theta_2)z$ never hold together, and that a fixed $q$ has $g(q) \ne \rho_1(t\theta_1)y$ and $f(q) \ne \rho_2(t\theta_2)z$. Then $l(g^{-1}(y), f^{-1}(z)) = l(g^{-1}(y'), f^{-1}(z'))$ ⟦Chapter8/HopfInvariant · linkPre_move⟧.

*Proof.* Apply the engine to $G_t = \rho_1(-t\theta_1) \circ g$ and $F_t = \rho_2(-t\theta_2) \circ f$ with the fixed values $y, z$. Then $G_t^{-1}(y) = g^{-1}(\rho_1(t\theta_1)y)$, and $y$ is regular for $G_1$ because $y'$ is regular for $g$ ⟦Chapter8/HopfInvariant · rotHom⟧ ⟦Chapter8/HopfInvariant · isRegularValue_rotS_comp⟧. Transport by $\rho_1(\theta_1) \times \rho_2(\theta_2)$ then turns $G_1$ back into $g$ and $y$ into $y'$. The values passed on the way need not be regular.

#### a) Local constancy

**Theorem (V8.14 a).** Let $d \ge 1$, let $f : S \to S^{d+1}$ be smooth, and let $y \ne z$ be regular values of $f$. There is a neighbourhood $U$ of $y$ such that every regular value $y' \in U$ of $f$ satisfies $l(f^{-1}(y'), f^{-1}(z)) = l(f^{-1}(y), f^{-1}(z))$. The same holds in $z$ ⟦Chapter8/HopfInvariant · linkPre_self_eventually_eq⟧ ⟦Chapter8/HopfInvariant · linkPre_self_eventually_eq_right⟧.

Both are the case $g = f$ of a two-map statement: for smooth $g, f$, a regular value $y$ of $g$ and $z$ of $f$ with $g^{-1}(y) \cap f^{-1}(z) = \emptyset$, the same conclusion holds for regular values $y'$ of $g$ near $y$ ⟦Chapter8/HopfInvariant · linkPre_eventually_eq⟧. When $g = f$, disjointness is just $y \ne z$.

*Proof.* Take $q$ outside both fibres. The set $K = g(f^{-1}(z))$ is compact and does not contain $y$; choose $\varepsilon$ with $B(y,\varepsilon) \cap K = \emptyset$. For $y'$ within $\min(\varepsilon, |g(q)-y|)$ of $y$, the great-circle arc from $y$ to $y'$ stays within $|y'-y|$ of $y$ ⟦Chapter7/Rotation · exists_rotation_path⟧. So the arc misses $g(q)$ and every $g(x)$ with $f(x) = z$, and the move with $z$ fixed applies ⟦Chapter8/HopfInvariant · linkPre_move_left⟧.

*A correction to a natural generalization.* For two maps, the formal statement does not settle for $y \ne z$: it assumes that the fibres are disjoint at $y$, and this is exactly the form b) needs ⟦Chapter8/HopfInvariant · linkPre_eventually_eq⟧. The reason is geometric, and it is not formalized (no counterexample is checked by machine). At values $y$ where $g^{-1}(y)$ meets $f^{-1}(z)$ the symbol $l(g^{-1}(y), f^{-1}(z))$ is still defined but no longer a linking number of disjoint manifolds, and moving $y$ past such a value pushes one fibre through the other, as when two circles in $\mathbb R^3$ pass through each other; the linking number can jump there.

#### b) Nearby maps

**Theorem (V8.14 b).** Let $d \ge 1$ and let $f, g : S \to S^{d+1}$ be smooth. Let $y \ne z$ be regular values of both $f$ and $g$, and suppose $\|f(x)-g(x)\| < \|y-z\|$ for all $x$. Then
$$l\bigl(f^{-1}(y), f^{-1}(z)\bigr) = l\bigl(g^{-1}(y), f^{-1}(z)\bigr) = l\bigl(g^{-1}(y), g^{-1}(z)\bigr)$$
⟦Chapter8/HopfInvariant · linkPre_eq_of_norm_lt⟧.

*The idea.* Deform $f$ into $g$ in one slot along the normalized chord and keep the other slot fixed. A chord point is never farther from $f(x)$ than $g(x)$ is, so the moving fibre of $y$ never meets $f^{-1}(z)$.

*The proof as formalized (first equality; the second is symmetric).*

1. *The chord.* Let $m = \max_x\|f(x)-g(x)\|$, attained by compactness; then $m < \|y-z\| \le 2$. Let $C_t = (1-\sigma(t))f + \sigma(t)g$, normalized, where $\sigma$ is a smooth transition function equal to $0$ for $t \le 0$ and $1$ for $t \ge 1$. It is a smooth homotopy from $f$ to $g$ ⟦Chapter8/HopfInvariant · chord⟧. For unit vectors $a, b$ with $|a-b| < 2$ and $s \in [0,1]$, the point $w = (1-s)a + sb$ has $|w| \le 1$, and normalizing moves it by $1-|w| \le |w-b|$. Hence $|w/|w| - a| \le (1-s)|a-b| + s|a-b| = |a-b|$, and likewise for $b$ ⟦Chapter8/HopfInvariant · norm_nv0_chord_sub⟧.
2. *Disjointness at the start.* $g^{-1}(y) \cap f^{-1}(z) = \emptyset$, since otherwise $\|f(x)-g(x)\| = \|z-y\|$.
3. *A good value.* Take $q$ with $f(q) \ne z$. Choose $y'$ near $y$ with the following properties: it is regular for $f$ and for $g$; it lies in the neighbourhoods given by a) for $f$ and by the two-map form of a) for $(g,f)$, the latter available by step 2; it satisfies $m < \|y'-z\|$; and it avoids the curve $t \mapsto C_t(q)$, $t \in [0,1]$ ⟦Chapter8/HopfInvariant · exists_regular_off⟧. Such a $y'$ exists because regular values are open (proved here for compact domains in arbitrary dimensions; Chapter 6 had only equal dimensions) and dense, and a smooth curve in a sphere of dimension $\ge 2$ is nowhere dense ⟦Chapter8/HopfInvariant · isOpen_setOf_isRegularValue⟧ ⟦Chapter8/Generic · isNowhereDense_image_of_finrank_lt⟧.
4. *The engine* with $G = C$ and $F_t = f$. If $C_t(x) = y'$ and $f(x) = z$, then $\|y'-z\| \le \|f(x)-g(x)\| \le m < \|y'-z\|$, which is impossible ⟦Chapter8/HopfInvariant · norm_chord_sub_left⟧ ⟦Chapter8/HopfInvariant · linkPre_eq_of_homotopy⟧. The base point stays off both fibres: $f(q) \ne z$ by the choice of $q$, and $C_t(q) \ne y'$ by the choice of $y'$.
5. *The chain.* $l(f^{-1}y, f^{-1}z) = l(f^{-1}y', f^{-1}z)$ by a); $= l(g^{-1}y', f^{-1}z)$ by the engine, since $C_0 = f$ and $C_1 = g$; $= l(g^{-1}y, f^{-1}z)$ by the two-map form of a).

The detour through $y'$ is forced by the base point: $y$ itself may lie on the trajectory of $q$.

#### c) Independence and homotopy invariance

**Definition.** If $f$ is smooth and has two distinct regular values, $H(f) = l(f^{-1}(y_0), f^{-1}(z_0))$ for a chosen pair $y_0 \ne z_0$ of regular values; otherwise $H(f) = 0$ ⟦Chapter8/HopfInvariant · hopfInvariant⟧. For $d \ge 1$ every smooth $f$ has such a pair ⟦Chapter8/HopfInvariant · exists_regular_pair⟧, so only non-smooth maps get the value $0$ by default.

**Theorem (V8.14 c).** Let $d \ge 1$. (i) If $f : S \to S^{d+1}$ is smooth, then $l(f^{-1}(y), f^{-1}(z)) = H(f)$ for all regular values $y \ne z$ of $f$ ⟦Chapter8/HopfInvariant · linkPre_eq_hopfInvariant⟧. (ii) If $f, g$ are smooth and smoothly homotopic, then $H(f) = H(g)$ ⟦Chapter8/HopfInvariant · hopfInvariant_eq_of_smoothHomotopic⟧.

*Proof of (i).* Let $X = \{(y,z) \in S^{d+1} \times S^{d+1} : y \ne z\}$. It is connected, and pairs of regular values are dense in it. If every point of $X$ has a neighbourhood on which the linking number is constant over the regular pairs, then it is constant over all regular pairs in $X$ ⟦Chapter8/Generic · isConnected_offDiag_sph⟧ ⟦Chapter8/Generic · eq_of_locallyConst_on_dense⟧. Local constancy near $(p_1,p_2) \in X$ is proved directly with simultaneous moves ⟦Chapter8/HopfInvariant · linkPre_eq_linkPre_of_ne⟧:

1. If $f$ is constant, a constant map has no regular value in its image, so every fibre of a regular value is empty and every linking number is $0$ ⟦Chapter8/HopfInvariant · not_isRegularValue_const⟧ ⟦Chapter8/HopfInvariant · linkPre_eq_zero_of_forall_ne⟧.
2. Otherwise some $q$ has $f(q) \notin \{p_1, p_2\}$. If not, $f^{-1}(p_1)$ would be both open and closed in the connected $S$. Let $r = \min(|p_1-p_2|, |f(q)-p_1|, |f(q)-p_2|)/8$.
3. Two regular pairs $(a_1,a_2)$ and $(b_1,b_2)$ in $B(p_1,r) \times B(p_2,r)$ are joined by great-circle arcs $a_i \to b_i$, each staying within $3r$ of $p_i$. The arcs miss $f(q)$, which is at distance $\ge 8r$. They cannot pass through a common value $f(x)$ at the same time, since that would give $|p_1-p_2| < 6r$. The move lemma applies ⟦Chapter7/Rotation · exists_rotation_path⟧ ⟦Chapter8/HopfInvariant · linkPre_move⟧.

*Proof of (ii).* A smooth homotopy is a smooth $H : S \times \mathbb R \to S^{d+1}$ with $H(\cdot,0) = f$ and $H(\cdot,1) = g$. Fix any $q$. Choose $y$, a common regular value of $f$ and $g$ off the curve $t \mapsto H(q,t)$, $t \in [0,1]$, and then $z \ne y$ with the same properties. Such values exist by the genericity argument of b) ⟦Chapter8/HopfInvariant · exists_regular_off⟧. The engine with $G = F = H$ applies: disjointness is automatic because $y \ne z$, and $q$ avoids both fibres by choice ⟦Chapter8/HopfInvariant · linkPre_eq_of_homotopy⟧. It gives $l(f^{-1}y, f^{-1}z) = l(g^{-1}y, g^{-1}z)$, and both sides are Hopf invariants by (i).

*Where the formal proof departs from Milnor.* The book's order suggests deducing c) from b) by cutting a homotopy into steps shorter than $\|y-z\|$. The formal proof does not use b) for c). It applies the engine to the homotopy itself, once the two values avoid the trajectory of a single base point, and b) stands as a separate result ⟦Chapter8/HopfInvariant · hopfInvariant_eq_of_smoothHomotopic⟧. The dependence on $y$ and $z$ is settled by connectedness of $X$ and simultaneous moves of both values; a) itself is not used ⟦Chapter8/HopfInvariant · linkPre_eq_linkPre_of_ne⟧. *Deviation:* homotopies are smooth.

### V8.15 Problem 15: odd $p$ and compositions

**Theorem (odd $p$).** Let $d \ge 1$ with $d+1$ odd, and let $f : S \to S^{d+1}$ be smooth. Then $H(f) = 0$ ⟦Chapter8/HopfProps · hopfInvariant_eq_zero_of_odd⟧.

*Proof.* Take distinct regular values $y, z$, a point $q$ outside $f^{-1}\{y,z\}$, and $R$ with $Rq = \mathbf n$. Both $l(f^{-1}y, f^{-1}z)$ and $l(f^{-1}z, f^{-1}y)$ are Euclidean linking numbers after $R$ ⟦Chapter8/HopfInvariant · linkPre_eq_linkingNumberRot⟧. The symmetry of Problem 13 relates them by the factor $(-1)^{(d+1)(d+1)} = -1$ ⟦Chapter8/Linking · linkingNumber_symm⟧. Both are $H(f)$ by c), so $H(f) = -H(f)$.

**Theorem (compositions).** Let $d \ge 1$, and let $f : S \to S^{d+1}$ and $g : S^{d+1} \to S^{d+1}$ be smooth. Then $H(g\circ f) = (\deg g)^2 H(f)$, with the degree taken for Milnor's orientation on both sides ⟦Chapter8/HopfProps · hopfInvariant_comp⟧.

*The idea.* Write $\Phi_h$ for the map $\Phi$ built from $g = f = h$. Then $\Phi_{g\circ f} = ((g \times g) \times \mathrm{id}) \circ \Phi_f$, and the local degree of a composition is a sum over the fibre of the outer map.

*The proof as formalized.*

1. *Local composition formula.* Let $\Phi : M \to N$ and $\Gamma : N \to P$ be smooth, where $M$ and $N$ are oriented manifolds of dimension $n$ and $P$ carries an orientation in degree $n$ (the statement does not fix the dimension of $P$; in the application all three have dimension $4d+2$). Let $w \in P$ be such that $\Gamma^{-1}(w)$ and $(\Gamma\circ\Phi)^{-1}(w)$ are finite. Then $\deg_w(\Gamma \circ \Phi) = \sum_{w' \in \Gamma^{-1}(w)} \operatorname{sign}_{w'}\Gamma \cdot \deg_{w'}\Phi$. No regularity is needed, since signs multiply at every point ⟦Chapter8/HopfComp · degAt_comp_eq_finsum⟧ ⟦Chapter6/SignLemmas · signAt_comp'⟧.
2. *Fibres downstairs.* If $y$ is a regular value of $g \circ f$ and $g(y_i) = y$, then $y_i$ is a regular value of $f$: $dg \circ df$ is onto, so $dg$ is onto, hence injective in equal dimensions, so $df$ is onto ⟦Chapter8/HopfComp · isRegularValue_of_comp⟧.
3. *Linking numbers under composition.* Let $y \ne z$ be regular for $g$ and $g \circ f$, let $R$ be admissible for $(g \circ f)^{-1}\{y,z\}$, and let $e$ be a regular value of all the linking maps involved. Then
$$l_R\bigl((g f)^{-1}y, (g f)^{-1}z\bigr) = \sum_{y_i \in g^{-1}(y)}\ \sum_{z_j \in g^{-1}(z)} \operatorname{sign}_{y_i}g\,\operatorname{sign}_{z_j}g\ l_R\bigl(f^{-1}y_i, f^{-1}z_j\bigr).$$
The fibre of $\Gamma = (g\times g)\times\mathrm{id}$ over $((y,z),e)$ is $(g^{-1}y \times g^{-1}z) \times \{e\}$, and the sign of $\Gamma$ there is $\operatorname{sign}_{y_i}g\,\operatorname{sign}_{z_j}g$. The fibre of $\Phi_{gf}$ is finite, being the image of a fibre of a linking map ⟦Chapter8/OrientProd · signAt_prodMap⟧ ⟦Chapter8/HopfComp · finite_preimage_phiR⟧ ⟦Chapter8/HopfComp · linkingNumberRot_comp_eq_finsum⟧. A common $e$ exists: a dense set meets finitely many open dense sets ⟦Chapter6/RegularOpen · exists_mem_of_dense_of_isOpen⟧ ⟦Chapter8/HopfComp · linkingNumberRot_comp_eq_finsum'⟧.
4. *Assembly.* Distinct common regular values of $g$ and $g \circ f$ exist ⟦Chapter8/HopfProps · exists_regular_pair_comp⟧. Each $l_R(f^{-1}y_i, f^{-1}z_j)$ equals $H(f)$ by c), since $y_i \ne z_j$. Each sum of signs is $\deg g$ ⟦Chapter8/HopfComp · finsum_signAt_eq_deg⟧.

*Where the formal proof departs from Milnor.* The usual argument decomposes $(g\circ f)^{-1}(y)$ as $\bigsqcup f^{-1}(y_i)$, with orientations changed by $\operatorname{sign} dg_{y_i}$, and uses bilinearity of linking numbers. The formal proof proves neither the orientation comparison nor bilinearity over disjoint unions. Both are absorbed in the local composition formula ⟦Chapter8/HopfComp · degAt_comp_eq_finsum⟧.

### V8.15 The Hopf fibration

**Definition.** With $z_1 = x_0 + ix_1$ and $z_2 = x_2 + ix_3$ (Milnor's $x_1, \dots, x_4$ shifted to start at $0$),
$$\pi(x) = \bigl(2(x_0x_2 + x_1x_3),\ 2(x_1x_2 - x_0x_3),\ x_0^2 + x_1^2 - x_2^2 - x_3^2\bigr) = \bigl(2z_1\bar z_2,\ |z_1|^2 - |z_2|^2\bigr).$$
One has $\|\pi(x)\| = \|x\|^2$, so $\pi$ maps $S^3$ smoothly to $S^2$ ⟦Chapter8/HopfMap · hopfPoly⟧ ⟦Chapter8/HopfMap · norm_hopfPoly⟧ ⟦Chapter8/HopfMap · contMDiff_hopfMap⟧.

**Proposition.**

(i) *Milnor's formula.* If $z_2 \ne 0$ then $\pi(x) = h^{-1}(z_1/z_2)$, where $h^{-1}(w) = (2\operatorname{Re}w, 2\operatorname{Im}w, |w|^2-1)/(|w|^2+1)$ is the inverse of stereographic projection from $(0,0,1)$. If $z_2 = 0$ then $\pi(x) = (0,0,1)$ ⟦Chapter8/HopfMap · invStereoC⟧ ⟦Chapter8/HopfMap · hopfMap_eq_milnor⟧ ⟦Chapter8/HopfMap · hopfMap_eq_top⟧.

(ii) *Every point of $S^2$ is a regular value.* Let $D$ be the derivative of the polynomial map at $x$. Then $DD^{\mathsf T} = 4\|x\|^2$ and $\langle x, D^{\mathsf T}u\rangle = 2\langle\pi(x), u\rangle$ ⟦Chapter8/HopfMap · hopfPoly_fderiv_apply⟧ ⟦Chapter8/HopfMap · inner_hopfAdj⟧ ⟦Chapter8/HopfMap · fderiv_hopfAdj⟧. So for $u$ tangent at $\pi(x)$, the vector $v = \tfrac14 D^{\mathsf T}u$ is tangent at $x$ and $Dv = u$ ⟦Chapter8/HopfMap · isRegularValue_hopfMap⟧.

(iii) *Two fibres.* $\pi(x) = (1,0,0)$ iff $z_1 = z_2$, and $\pi(x) = (-1,0,0)$ iff $z_1 = -z_2$. These are great circles, the intersections of $S^3$ with two planes. For the first, $2(x_0x_2 + x_1x_3) = 1$ and $|x| = 1$ give $(x_0-x_2)^2 + (x_1-x_3)^2 = 0$ ⟦Chapter8/HopfMap · hopfMap_eq_e0_iff⟧ ⟦Chapter8/HopfMap · hopfMap_eq_neg_e0_iff⟧.

(iv) *The pair realizing a direction.* Let $\mathrm{st}(x) = (x_0,x_1,x_2)/(1-x_3)$ ⟦Chapter8/HopfMap · stereoTop⟧ ⟦Chapter8/HopfSign · stN_eq_stereoTop⟧. For $x$ in the fibre over $(1,0,0)$ and $x'$ in the fibre over $(-1,0,0)$, the vector $\mathrm{st}(x) - \mathrm{st}(x')$ is a positive multiple of $(0,-1,0)$ iff
$$x = a = \tfrac{1}{\sqrt2}(0,-1,0,-1), \qquad x' = a' = \tfrac{1}{\sqrt2}(0,1,0,-1)$$
⟦Chapter8/HopfMap · hopf_link_pair_iff⟧. The first and third coordinates of the difference give $x_0 = x'_0 = 0$. Then $x_1^2 = x_1'^2 = \tfrac12$. After clearing positive denominators, the sign condition on the second coordinate reads $x_1 - x'_1 + 2x_1x'_1 < 0$, and of the four sign choices only $x_1 = -\tfrac1{\sqrt2}$, $x'_1 = \tfrac1{\sqrt2}$ satisfies it.

### V8.15 The sign: $H(\pi) = -1$

**Theorem.** $H(\pi) = -1$ ⟦Chapter8/HopfProps · hopfInvariant_hopfMap⟧. More precisely, with $y = (1,0,0)$, $z = (-1,0,0)$, fibres oriented as above, and the identity rotation, $l_{\mathrm{id}}(\pi^{-1}(y), \pi^{-1}(z)) = -1$ ⟦Chapter8/HopfSign · linkingNumberRot_hopfMap⟧.

*The idea.* By the theorem "linking number $=$ local degree", this linking number is the local degree of $\Phi(x,x') = ((\pi x, \pi x'), \lambda(x,x'))$ at $((y,z),e)$, with $e = (0,-1,0)$. The fibre is the single point $(a,a')$, so everything reduces to one sign. That sign is a product of three explicit determinants.

*The proof as formalized.*

1. *Admissibility.* The fibres are disjoint. Neither contains $\mathbf n = (0,0,0,1)$: on them $x_3 = \pm x_1$, which would give $1 = 0$. So the identity rotation is admissible ⟦Chapter8/HopfSign · hopf_disj⟧ ⟦Chapter8/HopfSign · hopf_north_y⟧ ⟦Chapter8/HopfSign · hopf_north_z⟧.
2. *The fibre of $\Phi$.* $\lambda(x,x') = e$ means $\mathrm{st}(x)-\mathrm{st}(x')$ is a positive multiple of $e$. By (iv), the fibre of $\Phi$ over $((y,z),e)$ is $\{(a,a')\}$ ⟦Chapter8/HopfSign · eq_q₀_of_phiR⟧ ⟦Chapter8/HopfSign · preimage_phiR⟧.
3. *Reduction.* The block lemma with $d = 1$, $p = 2$ (factor $(-1)^2 = 1$) reduces the sign of $\Phi$ at $(a,a')$ to the sign of $d\lambda \circ (\iota \times \iota') : \mathbb R \times \mathbb R \to T_eS^2$. Here $\iota, \iota'$ are the inclusions of the lines spanned by the fibre directions $t = \tfrac1{\sqrt2}(1,0,1,0)$ at $a$ and $t' = \tfrac1{\sqrt2}(-1,0,1,0)$ at $a'$; these lines are the kernels of $d\pi$ ⟦Chapter8/HopfSign · D_vt⟧ ⟦Chapter8/HopfSign · range_toSpanSingleton_eq_ker⟧. (As one checks by hand, outside the formal proof, they are the velocities of the circle action $(z_1,z_2) \mapsto (e^{i\phi}z_1, e^{i\phi}z_2)$.)
4. *Lifts.* At $a$ take $u_1 = (1,0,-1,0)$ and $u_2 = (0,-1,0,1)$, with $d\pi\,u_1 = 2\sqrt2\,(0,1,0)$ and $d\pi\,u_2 = 2\sqrt2\,(0,0,1)$. They lift a positive basis at $y$, because $\det(y, d\pi u_1, d\pi u_2) = 8$. At $a'$ take $w_1 = (0,1,0,1)$ and $w_2 = (1,0,1,0)$, with $d\pi\,w_1 = 2\sqrt2\,(0,0,1)$ and $d\pi\,w_2 = 2\sqrt2\,(0,1,0)$, and $\det(z, d\pi w_1, d\pi w_2) = 8$ ⟦Chapter8/HopfSign · det_D_uA⟧ ⟦Chapter8/HopfSign · det_D_uA'⟧.
5. *The fibres are oriented against $t$ and $t'$.* $\det(a, u_1, u_2, t) = \det(a', w_1, w_2, t') = -2$ ⟦Chapter8/HopfSign · det_eVA⟧ ⟦Chapter8/HopfSign · det_eVA'⟧. By the chart description of the fibre orientation and the determinant test for the sphere, $t$ and $t'$ are negative ⟦Chapter8/HopfSign · orEpsB_frameOr_A⟧ ⟦Chapter8/HopfSign · orEpsB_frameOr_A'⟧.
6. *The direction map.* $w_0 := \mathrm{st}(a) - \mathrm{st}(a') = 2(\sqrt2-1)(0,-1,0)$. The derivative of $v \mapsto v/|v|$ at $w_0$ is $|w_0|^{-1}$ times the identity on $w_0^\perp$ ⟦Chapter8/HopfSign · exists_hasFDerivAt_normalize⟧ ⟦Chapter8/HopfSign · exists_mfd_lamR⟧. Also $d\,\mathrm{st}_a(t) = (\sqrt2-1)(1,0,1)$ and $d\,\mathrm{st}_{a'}(t') = (\sqrt2-1)(-1,0,1)$. Hence $d\lambda(t,0) = c(1,0,1)$ and $d\lambda(0,t') = c(1,0,-1)$ with $c = (\sqrt2-1)/|w_0|$ ⟦Chapter8/HopfSign · mfd_lamR_t⟧ ⟦Chapter8/HopfSign · mfd_lamR_t'⟧. By the formula for $w_0$, $c = \tfrac12$; the formal proof only uses $c > 0$ ⟦Chapter8/HopfSign · cl_pos⟧. Since $\det(e, c(1,0,1), c(1,0,-1)) = -2c^2 < 0$, these two vectors form a negative basis of $T_eS^2$ ⟦Chapter8/HopfSign · det_βl⟧ ⟦Chapter8/HopfSign · orEpsB_ξe⟧.
7. *The sign.* $\operatorname{sign}\bigl((-1)(-1)\cdot(-1)\bigr) = -1$ ⟦Chapter8/HopfSign · orSign_lam⟧ ⟦Chapter8/HopfSign · signAt_q₀⟧. So the local degree is $-1$ ⟦Chapter8/HopfSign · degAt_hopf⟧. Because the only fibre point has nonzero sign, $e$ is a regular value of the linking map ⟦Chapter8/HopfSign · isRegularValue_linkMap_hopfE⟧, and the linking number is $-1$. Since $y \ne z$ are regular values, this linking number is $H(\pi)$.

*Which conventions give $+1$.* This analysis is not formalized; it combines the formal lemmas cited in it with the multiplicativity of signs. Among the natural variations of the conventions, only changes to the linking number itself move the value. Three changes flip it. (a) The direction $(x'-x)/\|x'-x\|$ instead of $(x-x')/\|x-x'\|$ composes $\lambda$ with the antipodal map of $S^2$, of degree $(-1)^3$ ⟦Chapter8/OrientFrame · deg_antip_std⟧. (b) Orienting the domain as $\pi^{-1}(z) \times \pi^{-1}(y)$ while keeping the direction composes with the swap of two circles, of sign $(-1)^{1\cdot1}$ ⟦Chapter8/OrientProd · signAt_swap⟧. (c) The opposite orientation on the target $S^2$ of $\lambda$. Several changes leave $-1$ unchanged:

- Listing tangent vectors first in the fibre convention: $(-1)^{dp} = +1$.
- Exchanging the two fibres, which does (a) and (b) together: $(-1)^{(1+1)(1+1)} = +1$ ⟦Chapter8/Linking · linkingNumber_symm⟧.
- Reversing the orientation of the source $S^3$ or of the target of $\pi$: this reverses both fibres, and the product orientation survives.
- Another pole or a complex conjugation in Milnor's $h$: this replaces $\pi$ by $\rho\circ\pi$ for an isometry $\rho$ of $S^2$, and $H(\rho\circ\pi) = (\deg\rho)^2H(\pi)$ by the composition theorem ⟦Chapter8/HopfProps · hopfInvariant_comp⟧.

So a value $+1$ comes from redefining the linking number itself, by an odd number of the changes (a)–(c). The choices listed that concern only the fibres or the map leave $-1$, and the book's conventions, taken literally, give $-1$; the last statement is the formal theorem. Either way the invariant is nonzero. A constant map has $H = 0$, since it has no regular value in its image and so its fibres over regular values are empty ⟦Chapter8/HopfInvariant · not_isRegularValue_const⟧ ⟦Chapter8/HopfInvariant · linkPre_eq_zero_of_forall_ne⟧. With c), the Hopf fibration is therefore not smoothly null-homotopic, a one-line consequence that the formal text does not state separately.

### What the formalization taught us

- **$p \ge 2$ is a hypothesis.** Linking numbers of fibres go through V8.13′ with $a = b = p-1$, which needs $a, b \ge 1$ ⟦Chapter8/HopfInvariant · linkPre_eq_linkingNumberRot⟧.
- **The fibre convention is a choice.** The formal fibre orientation puts the frame first; by an informal count it differs from the §5-style convention by $(-1)^{dp}$, which is $+1$ for $d = p-1$ ⟦Chapter8/PreimOrient · preimOr⟧.
- **The two-map form of a) assumes disjoint fibres.** Without disjointness the linking number can jump (a geometric observation, not machine-checked); Milnor's one-map statement is safe because $y \ne z$ ⟦Chapter8/HopfInvariant · linkPre_eventually_eq⟧.
- **Values regular only at the ends.** The engine asks for regularity of $y$ and $z$ at $t = 0, 1$ only. In return it requires the moving fibres to stay disjoint and away from the projection point, and it needs a compactness argument on the non-compact domain $D_R$ ⟦Chapter8/LinkDegree · linkingNumberRot_eq_of_homotopy⟧ ⟦Chapter8/LinkDegree · exists_isClosed_nhds_domR⟧.
- **A base point replaces "a point outside".** Projecting from a point $q$, and keeping $q$ off every moving fibre, is what the choice of values in b) and c) is arranged around ⟦Chapter8/HopfInvariant · linkPre_eq_of_homotopy⟧ ⟦Chapter8/HopfInvariant · exists_regular_off⟧.
- **Regular values of maps between different dimensions form an open set** when the domain is compact. This had to be proved afresh; Chapter 6's version was for equal dimensions ⟦Chapter8/HopfInvariant · isOpen_setOf_isRegularValue⟧.
- **Orientations are compared through local degrees.** Transport and the composition formula never compare two fibre orientations directly ⟦Chapter8/HopfInvariant · linkPre_comp_posDiffeo⟧ ⟦Chapter8/HopfComp · linkingNumberRot_comp_eq_finsum⟧.
- **c) does not go through b).** Homotopy invariance applies the engine to the homotopy itself; independence of the values uses connectedness of the off-diagonal and treats constant maps separately ⟦Chapter8/HopfInvariant · hopfInvariant_eq_of_smoothHomotopic⟧ ⟦Chapter8/HopfInvariant · linkPre_eq_linkPre_of_ne⟧.
- **$H(\pi) = -1$.** With outward-normal-first spheres, the fibre orientation of V8.0 (iii) (which is §5's in this dimension) and $\lambda = (x-x')/\|x-x'\|$ on the product, the Hopf fibration has Hopf invariant $-1$, not the book's $1$ ⟦Chapter8/HopfProps · hopfInvariant_hopfMap⟧.


## Part XI. Transversality and the cohomotopy group (Milnor §8, Problems 16–17)

Milnor's last two problems ask for three things. A framed submanifold can be moved slightly to meet a given submanifold transversally, and the transverse intersection is a manifold (Problem 16). Transverse intersection induces a product $\Pi^p(M) \times \Pi^q(M) \to \Pi^{p+q}(M)$ of framed cobordism classes, and for $p \ge \frac12 m + 1$ disjoint union makes $\Pi^p(M)$ an abelian group (Problem 17). The formal solution, about 4,800 lines, is assembled from the machinery of §7 but has to open it up. "Keep the cobordism away from the other piece" is a statement about the underlying set of a cobordism, which the existence theorems of §7 hide, so several are re-proved with the set recorded. Two ideas carry the part. A framed submanifold is moved within its class not by deforming it but by changing the regular value of a map that realizes it. And the product and the inverse are both computed as Pontryagin manifolds of explicit maps, then identified *exactly*, framings included, with the intersection and with a pair of parallel copies.

**Map.**
- `Chapter8/Transversality`: transversality, the intersection of transverse submanifolds, the transverse translate inside a product neighbourhood.
- `Chapter8/FramedOps`: reflexivity, the set of classes, disjoint unions of framed submanifolds and of cobordisms, Lemma 1 and the homotopy construction with the underlying set exposed.
- `Chapter8/CohomotopyProduct`: dual forms, the framed intersection, a map $\mu : S^p \times S^q \to S^{p+q}$, transverse representatives, the intersection product.
- `Chapter8/CohomotopyGroup`: disjoint representatives, independence of the sum, the monoid laws, the cancelling pair, the group.

### Conventions

$M \subseteq \mathbb R^{K+1}$ is a submanifold of dimension $m$ given by slice charts (normal model $\mathbb R^w$), with the structure they induce; as a subspace of Euclidean space it is Hausdorff and second countable. Wherever Pontryagin manifolds or classes appear, $M$ is also compact and nonempty. Tangent spaces $T_xM$, $T_xN$ are subspaces of $\mathbb R^{K+1}$, images of the derivatives of the inclusions ⟦Chapter7/Framed · tangentM⟧ ⟦Chapter7/Framed · tangentN⟧.

A framed submanifold $F = (N, v)$ of dimension $n$ and codimension $p$ is a compact $N \subseteq M$ given by slice charts (model $\mathbb R^n$, normal model $\mathbb R^p$, $n + p = m$) with smooth $v_1, \dots, v_p : N \to \mathbb R^{K+1}$, tangent to $M$, orthogonal to $T_xN$ and linearly independent ⟦Chapter7/Framed · FramedSub⟧. A framed cobordism from $F_0$ to $F_1$ is an $(n+1)$-dimensional submanifold $S \subseteq M \times \mathbb R$ given by slice charts, equal to $N_0 \times \mathbb R$ over $t < \varepsilon$ and to $N_1 \times \mathbb R$ over $t > 1 - \varepsilon$ (some $0 < \varepsilon < \frac12$), compact over $[0,1]$, framed in $M \times \mathbb R$ by vectors equal to $(v^0_i, 0)$ and $(v^1_i, 0)$ at the ends; $F_0 \sim F_1$ means one exists ⟦Chapter7/Framed · FramedCob⟧ ⟦Chapter7/Framed · FramedCobordant⟧.

For $f : M \to S^p$ smooth with regular value $y$, a basis $b$ of the model space $\mathbb R^p$ at $y$, and $n + p = m$, $\mathrm{Pont}(f, y, b)$ is $f^{-1}(y)$ with the framing
$$(f^*b)_i(x) = A^*(AA^*)^{-1}b_i, \qquad A = A_f(x) = d\tilde f_x : \mathbb R^{K+1} \to \mathbb R^p,$$
where $\tilde f$ is $f$ precomposed with the nearest-point retraction onto $M$ and read in the chart at $y$ ⟦Chapter7/Pontryagin · At⟧ ⟦Chapter7/Pontryagin · pontV⟧ ⟦Chapter7/Pontryagin · pontryagin⟧. As $\ker A = T_xf^{-1}(y) \oplus (T_xM)^\perp$, $(f^*b)_i(x)$ is the unique vector tangent to $M$, normal to $f^{-1}(y)$, with $A$-image $b_i$ ⟦Chapter7/PontFrame · ker_At_eq⟧ ⟦Chapter7/PontFrame · pontV_eq_of⟧. Positive bases are positive for the orientation of $S^p$ fixed in Chapter 5 and used throughout §7 ⟦Chapter7/Lemma2 · exists_posBasis⟧; it need not be the outward-normal-first orientation of Part X, and the statements of this part do not involve it. $e_k$ is a standard basis vector.

Results of §7 carry Milnor's names: Lemma 1 (the positive basis does not matter), Theorem A (nor does the regular value), Theorem B (homotopic if and only if framed cobordant), Theorem C (every framed submanifold is a Pontryagin manifold), and the *homotopy construction* in the proofs of Lemmas 2 and 3 (the preimage of a regular value of a homotopy constant near the ends). Theorem C is used in the form: for every framed $F$ and basis $b$ there are $f$ with regular value north and $c > 0$ with $\mathrm{Pont}(f, \mathrm{north}, cb) = F$ ⟦Chapter7/ThmB · exists_map_of_framedSub⟧. The scalar $c$ recurs as a nuisance, removed by Lemma 1 for a positive diagonal matrix.

### V8.16 Problem 16: transverse intersections and the transverse translate

Submanifolds $N$ (model $\mathbb R^n$, normal model $\mathbb R^p$) and $N'$ (model $\mathbb R^{n'}$, normal model $\mathbb R^{p'}$) of $M$, given by slice charts, meet transversally if $T_xN + T_xN' = T_xM$ for all $x \in N \cap N'$ ⟦Chapter8/Transversality · Transverse⟧. Since the derivative of $M \hookrightarrow \mathbb R^{K+1}$ is injective, this is equivalent to the images of the derivatives of $N \hookrightarrow M$ and $N' \hookrightarrow M$ spanning $\mathbb R^m$, and all proofs work at this chart level ⟦Chapter8/Transversality · Transversality.transverse_iff⟧.

**Milnor's parenthesis.** *If $n + p = m$, $n' + p' = m$, $N$ and $N'$ meet transversally and $n + n' < m$, then $N \cap N' = \varnothing$*: at a common point, $m = \dim(T_xN + T_xN') \le n + n'$ ⟦Chapter8/Transversality · inter_eq_empty_of_transverse⟧. The two equations are hypotheses, but this dimension count does not need them.

#### The intersection

> **Theorem.** Let $N, N' \subseteq M$ be given by slice charts, with models $\mathbb R^n, \mathbb R^{n'}$ and normal models $\mathbb R^p, \mathbb R^{p'}$, where $n + p = m$ and $n' + p' = m$; suppose they meet transversally, and let $r + (p + p') = m$. Then $N \cap N'$ is a submanifold of $M$ given by slice charts, with model $\mathbb R^r$ and normal model $\mathbb R^{p+p'}$, and $T_x(N \cap N') = T_xN \cap T_xN'$ for every $x \in N \cap N'$. ⟦Chapter8/Transversality · isSliceSubmanifold_inter⟧ ⟦Chapter8/Transversality · tangentN_inter⟧

No compactness is needed. Since $r$ must be supplied, the case covered is $p + p' \le m$; otherwise the parenthesis applies.

*The idea.* Near a common point, $N$ and $N'$ are the zero sets of the normal coordinates of slice charts. The pair of normal coordinates cuts out $N \cap N'$, and transversality is exactly what makes it a submersion.

*The proof as formalized.*
1. For a slice chart $\varphi$ of $N$, the normal coordinate $\mathrm{pr}_2 \circ \varphi$ is smooth with surjective derivative $D$, and at points of $N$, $\ker D$ is the chart-level tangent space of $N$ ⟦Chapter8/Transversality · surjective_sliceSnd⟧ ⟦Chapter8/Transversality · ker_sliceSnd_eq_range⟧. The last fact is an instance of a principle proved for Chapter 8: the tangent space of a local zero set of a map with surjective derivative is the kernel of that derivative ⟦Chapter8/LocalSlice · IsSliceSubmanifold.range_mfderiv_val_eq_ker⟧.
2. Near $x \in N \cap N'$, with slice charts $\varphi, \varphi'$ on $U, U'$, the map $g = (\mathrm{pr}_2\varphi, \mathrm{pr}_2\varphi')$, read in $\mathbb R^{p+p'}$, is smooth on $U \cap U'$, vanishes there exactly on $N \cap N'$, and has derivative $(D, D')$ ⟦Chapter8/Transversality · exists_local_inter⟧.
3. If $D, D'$ are onto and $\ker D + \ker D'$ is everything, then $(D, D')$ is onto: given $(a, a')$, pick $Du = a$, $D'u' = a'$ and split $u - u' = k + k'$ along the kernels; then $u - k = u' + k'$ solves both. Transversality says the kernels span, so $g$ has surjective derivative along $N \cap N'$, with kernel $\ker D \cap \ker D'$ ⟦Chapter8/Transversality · surjective_prod_of_ker_sup⟧.
4. Local zero sets of such maps are submanifolds given by slice charts ⟦Chapter8/LocalSlice · IsSliceSubmanifold.of_locally_preimage⟧. By step 1's principle their chart-level tangent space is $\ker D \cap \ker D'$, and the injective map $d(M \hookrightarrow \mathbb R^{K+1})$ preserves intersections ⟦Chapter8/Transversality · Transversality.tangentN_inter_of⟧.

#### The transverse translate

Product-neighbourhood data for $F = (N, v)$ (the Product Neighborhood Theorem) consist of $G(x, u) = r\big(x + \sum_i \lambda(u)_i v_i(x)\big)$, with $r$ the nearest-point retraction and $\lambda$ a smooth clamp equal to the identity for $|u| \le a_0$, and a radius $\varepsilon \le a_0$ such that $G$ is injective with bijective derivative on $N \times B_\varepsilon$ ⟦Chapter7/TubeData · TubeData⟧; such data exist for every $F$ ⟦Chapter7/TubeData · exists_tubeData⟧. The image $V = G(N \times B_\varepsilon)$ is open, $G$ has a smooth inverse on it, and $\pi = \mathrm{pr}_2 \circ G^{-1} : V \to \mathbb R^p$ is the fibre coordinate.

> **Theorem.** Let $M$ be compact and nonempty, $F = (N, v)$ a framed submanifold of dimension $n$ and codimension $p$, $(G, \varepsilon)$ product-neighbourhood data for $F$, $N' \subseteq M$ a submanifold given by slice charts (model $\mathbb R^{n'}$, normal model $\mathbb R^{p'}$), and $\delta > 0$. Then there is $u \in \mathbb R^p$ with $|u| < \delta$ and $|u| < \varepsilon$ such that $N_u = G(N \times \{u\})$ is a submanifold of $M$ given by slice charts (model $\mathbb R^n$, normal model $\mathbb R^p$) meeting $N'$ transversally, $x \mapsto G(x, u)$ is injective on $N$, and $|G(x,u) - x| < \delta$ for all $x \in N$. ⟦Chapter8/Transversality · exists_transverse_deformation⟧

*The idea.* $N_u = \pi^{-1}(u)$ has tangent space $\ker d\pi$, so it is transverse to $N'$ at $z$ exactly when $d\pi_z(T_zN') = \mathbb R^p$, that is, when $z$ is a regular point of $\pi|_{N'}$. Sard's theorem in Brown's form supplies such regular values $u$ arbitrarily near $0$.

*The proof as formalized.*
1. For $|u| < \varepsilon$, $z \in N_u$ if and only if $z \in V$ and $\pi(z) = u$ ⟦Chapter8/Transversality · mem_range_tube_iff⟧. From $\pi \circ G = \mathrm{pr}_2$ near the tube, $d\pi \circ dG = \mathrm{pr}_2$, so $\pi$ is a submersion on $V$ ⟦Chapter8/Transversality · mfd_fib_comp_G⟧ ⟦Chapter8/Transversality · surjective_mfd_fib⟧. Hence $N_u$, the zero set of $\pi - u$ on $V$, is a submanifold with chart-level tangent space $\ker d\pi_z$ ⟦Chapter8/Transversality · isSliceSubmanifold_range⟧ ⟦Chapter8/Transversality · range_mfd_val_range_eq_ker⟧.
2. As $G(x, 0) = x$ and $N$ is compact, some $\rho_1 > 0$ gives $|G(x,t) - x| < \delta$ for all $x \in N$, $|t| < \rho_1$.
3. Brown's theorem for $\pi$ on the open subset $N' \cap V$ of $N'$ gives a regular value $u$ with $|u| < \min(\delta, \varepsilon, \rho_1)$ ⟦Chapter2/Brown · dense_regularValues⟧.
4. At $z \in N_u \cap N'$, $d\pi_z \circ d(N' \hookrightarrow M)_z$ is onto, and a second small lemma (*if $A \circ B$ is onto, then $\ker A + \operatorname{range} B$ is everything*) gives $\ker d\pi_z + T_zN' = \mathbb R^m$ at chart level ⟦Chapter8/Transversality · ker_sup_range_eq_top_of_surjective_comp⟧.
5. Injectivity is that of $G$ on the tube; if $N = \varnothing$, $u = 0$ will do.

*What the book leaves implicit.* "Deformed slightly" becomes a translate in the product neighbourhood with three quantitative properties. No framing of $N_u$ is produced, and Problem 17 does not use this theorem.

### Framed cobordism classes and disjoint unions

**Reflexivity and the set of classes.** Chapter 7 proved symmetry and transitivity, but reflexivity only for framed points ⟦Chapter7/Reach · FramedCobordant.refl'⟧. Rather than build $N \times \mathbb R$ as a cobordism by hand, the formal proof writes $F = \mathrm{Pont}(k, \mathrm{north}, ce)$ by Theorem C and applies the homotopy construction to the constant homotopy $(x, t) \mapsto k(x)$, in every dimension and codimension ⟦Chapter8/FramedOps · framedCobordant_refl⟧. For $M$ compact and nonempty, $\Pi_{n,p}(M)$ is the quotient of the framed submanifolds of dimension $n$ and codimension $p$ by framed cobordism ⟦Chapter8/FramedOps · framedSetoid⟧ ⟦Chapter8/FramedOps · FramedClass⟧. It is Milnor's $\Pi^p(M)$ when $n + p = m$, and empty otherwise.

> **Proposition.** If $F = (N, v)$ and $G = (N', v')$ are framed submanifolds of dimension $n$ and codimension $p$ with $N \cap N' = \varnothing$, then $F \sqcup G = (N \cup N', v \cup v')$ is a framed submanifold of dimension $n$ and codimension $p$. ⟦Chapter8/FramedOps · FramedSub.union⟧

Near a point of $N$ the union agrees with $N$ on the open set $M \setminus N'$ ($N'$ is compact), where slice charts of $N$ serve for the union ⟦Chapter8/FramedOps · isSliceSubmanifold_of_locally_eq⟧ ⟦Chapter8/FramedOps · isSliceSubmanifold_union_of_isClosed⟧. There the two inclusions factor through each other, so the union has tangent space $T_xN$; smoothness of $v \cup v'$ is checked piecewise ⟦Chapter8/FramedOps · tangentN_eq_of_inter_eq⟧ ⟦Chapter8/FramedOps · contMDiff_unionFun⟧.

> **Proposition.** Let $X$ be a framed cobordism from $F_0$ to $F_1$ and $Y$ one from $G_0$ to $G_1$, all of dimension $n$ and codimension $p$, with disjoint underlying sets, $F_0 \cap G_0 = \varnothing$ and $F_1 \cap G_1 = \varnothing$. Then $X \cup Y$, with collar width $\min(\varepsilon_X, \varepsilon_Y)$, is a framed cobordism from $F_0 \sqcup G_0$ to $F_1 \sqcup G_1$ with underlying set $S_X \cup S_Y$. ⟦Chapter8/FramedOps · FramedCob.union⟧ ⟦Chapter8/FramedOps · framedCobordant_union⟧

The argument is the same once underlying sets are known to be closed. They are not compact, but $S = \{(x,t) \in S : 0 \le t \le 1\} \cup N_0 \times (-\infty, 0] \cup N_1 \times [1, \infty)$ is a union of three closed sets ⟦Chapter8/FramedOps · FramedCob.isClosed_S⟧.

**The set exposed.** Chapter 7 asserts only that Pontryagin manifolds are cobordant; the following versions record the cobordism.

> **Homotopy construction, with its set.** Let $M$ be compact and nonempty, $n + p = m$, $0 < \varepsilon < \frac12$, and $H : M \times \mathbb R \to S^p$ smooth with regular value $z$, with $H(x,t) = f(x)$ for $t \le \varepsilon$ and $H(x,t) = g(x)$ for $t \ge 1 - \varepsilon$, where $f, g$ are smooth with regular value $z$; let $b$ be linearly independent. Then there is a framed cobordism from $\mathrm{Pont}(f, z, b)$ to $\mathrm{Pont}(g, z, b)$ with underlying set exactly $H^{-1}(z)$. ⟦Chapter8/FramedOps · exists_framedCob_of_homotopy⟧
>
> **Lemma 1, with its set.** Let $M$ be compact and nonempty, $n + p = m$, $f$ smooth with regular value $y$, $b, b'$ linearly independent, and $A$ a matrix with $\det A > 0$ and $b'_j = \sum_i A_{ij}b_i$. Then there is a framed cobordism from $\mathrm{Pont}(f, y, b')$ to $\mathrm{Pont}(f, y, b)$ with underlying set $f^{-1}(y) \times \mathbb R$. ⟦Chapter8/FramedOps · exists_framedCob_of_det_pos⟧

The proofs reassemble the §7 constructions and record the set; Lemma 1 comes from a form allowing two maps with the same level set ⟦Chapter8/FramedOps · exists_framedCob_of_det_pos'⟧.

### V8.17 Problem 17: the intersection product

#### The dual forms and the framed intersection

For a framing $v(x) = (v_1, \dots, v_p)$ let $Uc = \sum_j c_jv_j$. The *dual forms* are
$$\alpha_F(x) = (U^*U)^{-1}U^* : \mathbb R^{K+1} \to \mathbb R^p, \qquad \alpha_F(x)\,y = \mathrm{Gram}(v)^{-1}\big(\langle v_i, y\rangle\big)_i$$
⟦Chapter8/CohomotopyProduct · dualOf⟧ ⟦Chapter8/CohomotopyProduct · FramedSub.dual⟧. They satisfy $\alpha_Fv_i = e_i$, vanish on $\mathrm{span}(v)^\perp$ (hence on $T_xN$ and $(T_xM)^\perp$), are onto, and vary smoothly with $x$ ⟦Chapter8/CohomotopyProduct · dual_v⟧ ⟦Chapter8/CohomotopyProduct · dual_eq_zero_of_mem_tangentN⟧ ⟦Chapter8/CohomotopyProduct · contMDiff_dual⟧.

Let $F = (N, v)$ have dimension $n$ and codimension $p$, $G = (N', v')$ dimension $n'$ and codimension $q$, and for $x \in N \cap N'$ put $A(x) = (\alpha_F(x), \alpha_G(x)) : \mathbb R^{K+1} \to \mathbb R^p \times \mathbb R^q \cong \mathbb R^{p+q}$. The key observation: transversality makes $A(x)$ onto, since $\ker\alpha_F + \ker\alpha_G \supseteq T_xN + T_xN' + (T_xM)^\perp = \mathbb R^{K+1}$ and step 3 above applies ⟦Chapter8/CohomotopyProduct · surjective_pairA_of_transverse⟧. Put $w_k(x) = A^*(AA^*)^{-1}e_k$ ⟦Chapter8/CohomotopyProduct · interV⟧ ⟦Chapter8/CohomotopyProduct · interFrame⟧.

> **Definition–Proposition.** Let $F, G$ be as above, meeting transversally, and $r + (p + q) = m$. Then $F \cap G = (N \cap N', w)$ is a framed submanifold of dimension $r$ and codimension $p + q$, and its framing vectors satisfy
> $$\big(\alpha_F(x)w_k(x),\ \alpha_G(x)w_k(x)\big) = k\text{-th standard basis vector of } \mathbb R^p \times \mathbb R^q.$$
> ⟦Chapter8/CohomotopyProduct · FramedSub.inter⟧ ⟦Chapter8/CohomotopyProduct · dual_inter_v⟧

Each axiom takes a line: $w_k \perp \ker A \supseteq (T_xM)^\perp$, so $w_k$ is tangent to $M$; $T_x(N \cap N') = T_xN \cap T_xN' \subseteq \ker A$ by V8.16, so it is normal; $Aw_k = e_k$ gives independence; the pseudo-inverse is smooth where $A$ is onto ⟦Chapter8/CohomotopyProduct · contMDiff_interFrame⟧. What matters below is that $w$ comes from the same pseudo-inverse formula as a Pontryagin framing.

#### Transverse representatives

> **Theorem.** Let $M$ be compact and nonempty and $p \ge 1$. For all $c \in \Pi_{n,p}(M)$ and $c' \in \Pi_{n',q}(M)$ there are $F \in c$ and $G \in c'$ meeting transversally. ⟦Chapter8/CohomotopyProduct · exists_transverse_rep⟧

*The idea.* Keep $G$, and replace $F$ by the Pontryagin manifold of its Theorem-C map $f$ at a value $z$ regular both for $f$ and for $f|_{N'}$. The regular values of $f$ form an open set containing north ($M$ is compact) and those of $f|_{N'}$ a dense set (Brown), so such $z$ exist ⟦Chapter7/RegOpen · isOpen_regularValues_sph⟧.

*The proof as formalized.* With a positive basis $b$ at north, $F_0 = \mathrm{Pont}(f, \mathrm{north}, cb)$; take $z$ as above, a positive basis $e'$ at $z$, and $F = \mathrm{Pont}(f, z, e')$. Theorem A gives $F \sim \mathrm{Pont}(f, \mathrm{north}, b)$, and Lemma 1 for $cI$ gives $F_0 \sim \mathrm{Pont}(f, \mathrm{north}, b)$ ⟦Chapter7/Lemma2 · framedCobordant_of_regularValues⟧ ⟦Chapter8/CohomotopyProduct · framedCobordant_diag⟧. At $x \in f^{-1}(z) \cap N'$ the chart-level tangent space of $f^{-1}(z)$ is $\ker df_x$ ⟦Chapter8/CohomotopyProduct · range_mfd_val_level⟧ and $df_x \circ d(N' \hookrightarrow M)$ is onto, so the "$A \circ B$" lemma gives transversality ⟦Chapter8/CohomotopyProduct · exists_transverse_cobordant⟧.

*Where the formal proof departs from Milnor.* The translate of V8.16 is not used: it carries no framing, and relating it to $F$ would need a cobordism of its own. Moving the regular value gets the cobordism free from Theorem A.

#### A smooth map $\mu : S^p \times S^q \to S^{p+q}$

Informally, $\mu$ plays the role of the collapse $S^p \times S^q \to S^p \wedge S^q \cong S^{p+q}$; the formal proofs use only the three properties in the proposition below. Let $\sigma(a) = (1 + a_{p+1})^{-1}(a_1, \dots, a_p)$ be stereographic projection from the south pole, $\pi_{\rm std} : \mathbb R^k \to S^k$ the standard collapse map of §7 (north only at $0$, south outside the ball of radius $\frac12$), and $\Gamma : \mathbb R^p \times \mathbb R^q \to \mathbb R^{p+q}$ a linear isomorphism. Define
$$\mu_\Gamma(a, b) = \pi_{\rm std}\big(E_\Gamma(\sigma(a), \sigma(b))\big) \ \text{ if } a, b \ne \text{south}, \qquad \mu_\Gamma(a,b) = \text{south otherwise},$$
with $E_\Gamma = (d\pi_{\rm std,0})^{-1} \circ \Gamma \circ (d\sigma_{\rm north} \times d\sigma_{\rm north})^{-1}$ ⟦Chapter8/CohomotopyProduct · sig⟧ ⟦Chapter8/CohomotopyProduct · muE⟧ ⟦Chapter8/CohomotopyProduct · mu⟧; $d\sigma_{\rm north}$ is invertible because inverse stereographic projection is a right inverse of $\sigma$ ⟦Chapter8/CohomotopyProduct · mfd_sig_comp_mfd_tau⟧.

> **Proposition.** $\mu_\Gamma$ is smooth, $\mu_\Gamma^{-1}(\text{north}) = \{(\text{north}, \text{north})\}$, and its derivative at $(\text{north}, \text{north})$, read in the charts at the north poles, is $\Gamma$. ⟦Chapter8/CohomotopyProduct · contMDiff_mu⟧ ⟦Chapter8/CohomotopyProduct · mu_eq_north_iff⟧ ⟦Chapter8/CohomotopyProduct · hasMFDerivAt_mu⟧

The delicate point is smoothness where a coordinate is the south pole, and the formal proof makes it quantitative. If $C$ is an antilipschitz constant of $E_\Gamma$ and the last coordinate of $a$ is below $-1 + 1/(C^2+1)$, then $|\sigma(a)| > C$, so $|E_\Gamma(\sigma(a), \sigma(b))| \ge \frac12$ and $\pi_{\rm std}$ already returns the south pole: $\mu_\Gamma$ is locally constant there ⟦Chapter8/CohomotopyProduct · lt_norm_sig⟧ ⟦Chapter8/CohomotopyProduct · eventually_mu_eq_south⟧.

#### The Pontryagin manifold of $\mu \circ (f, g)$ is the framed intersection

> **Theorem.** Let $M$ be compact and nonempty; $f : M \to S^p$ and $g : M \to S^q$ smooth with north a regular value of both; $b, b'$ linearly independent families in $\mathbb R^p, \mathbb R^q$; $n + p = m$, $n' + q = m$, $r + (p+q) = m$; and suppose $\mathrm{Pont}(f, \mathrm{north}, b)$ and $\mathrm{Pont}(g, \mathrm{north}, b')$ meet transversally. Then for every linear isomorphism $\Gamma$, $h = \mu_\Gamma \circ (f, g)$ is smooth, north is a regular value of $h$, and
> $$\mathrm{Pont}(h, \mathrm{north}, \beta) = \mathrm{Pont}(f, \mathrm{north}, b) \cap \mathrm{Pont}(g, \mathrm{north}, b'), \qquad \beta = \big(\Gamma(b_1, 0), \dots, \Gamma(b_p, 0), \Gamma(0, b'_1), \dots, \Gamma(0, b'_q)\big).$$
> ⟦Chapter8/CohomotopyProduct · pontryagin_mu_eq⟧ ⟦Chapter8/CohomotopyProduct · muBasis⟧

The equality is of framed submanifolds: same set, same vector fields.

*The idea.* The ambient derivative of $h$ is $\Gamma$ applied to those of $f$ and $g$, and the ambient derivative of a Pontryagin map factors through the dual forms of its own framing. So $A_h$ is an invertible matrix times $(\alpha_F, \alpha_G)$, and uniqueness of Pontryagin framing vectors does the rest.

*The proof as formalized.*
1. $h^{-1}(\text{north}) = f^{-1}(\text{north}) \cap g^{-1}(\text{north})$, since $\mu_\Gamma^{-1}(\text{north}) = \{(\text{north}, \text{north})\}$.
2. Along $F = \mathrm{Pont}(f, \mathrm{north}, b)$, $A_f(x) = B_b \circ \alpha_F(x)$ with $B_bc = \sum_i c_ib_i$ ⟦Chapter8/CohomotopyProduct · At_eq_basisCLM_dual⟧: $A_f$ kills vectors orthogonal to all $(f^*b)_i$, which span the range of $A_f^*$ ⟦Chapter8/CohomotopyProduct · At_eq_zero_of_forall_inner⟧, and $A_f(f^*b)_i = b_i$.
3. Near $h^{-1}(\text{north})$, $\tilde h$ is $\mu_\Gamma$ in the product chart composed with $(\tilde f, \tilde g)$, so $A_h(x) = \Gamma \circ (A_f(x), A_g(x)) = B \circ A(x)$ with $B = \Gamma \circ (B_b \times B_{b'})$ invertible ⟦Chapter8/CohomotopyProduct · At_mu⟧ ⟦Chapter8/CohomotopyProduct · At_mu_eq⟧.
4. $A(x)$ is onto by transversality, so north is a regular value of $h$.
5. $w_k(x)$ is tangent to $M$, normal to $h^{-1}(\text{north})$, and $A_h(x)w_k = Be_k = \beta_k$; the Pontryagin vector $(h^*\beta)_k(x)$ is the unique such vector ⟦Chapter7/PontFrame · pontV_eq_of⟧.

#### Invariance and the product

> **Theorem.** Let $M$ be compact and nonempty, $p, q \ge 1$, $r + (p+q) = m$. If $F \sim F_1$ (dimension $n$, codimension $p$) and $G \sim G_1$ (dimension $n'$, codimension $q$), with $F$ meeting $G$ and $F_1$ meeting $G_1$ transversally, then $F \cap G \sim F_1 \cap G_1$. ⟦Chapter8/CohomotopyProduct · framedCobordant_inter⟧

*The idea.* Turn the cobordisms into homotopies (Theorem B, "if"), compose with $\mu$, and turn back (Theorem B, "only if"). The friction is in the bases: Theorem B wants positive bases, while $\beta$ is built from Theorem C's rescaled bases. The formal proof chooses $\Gamma$ to make $\beta$ a positive diagonal rescaling of a positive basis.

*The proof as formalized.*
1. Take positive bases $b, b', \gamma$ at the north poles of $S^p, S^q, S^{p+q}$ ⟦Chapter7/Lemma2 · exists_posBasis⟧. Theorem C gives $F = \mathrm{Pont}(f, \mathrm{north}, cb)$, $F_1 = \mathrm{Pont}(f_1, \mathrm{north}, c_1b)$, $G = \mathrm{Pont}(g, \mathrm{north}, db')$, $G_1 = \mathrm{Pont}(g_1, \mathrm{north}, d_1b')$, with $c, c_1, d, d_1 > 0$.
2. $\mathrm{Pont}(f, \mathrm{north}, b) \sim F \sim F_1 \sim \mathrm{Pont}(f_1, \mathrm{north}, b)$ by Lemma 1 at the ends, so $f \simeq f_1$; likewise $g \simeq g_1$ ⟦Chapter7/ThmAconv · smoothHomotopic_of_framedCobordant⟧.
3. Let $\Gamma(b_i, 0) = \gamma_i$ and $\Gamma(0, b'_j) = \gamma_{p+j}$ ⟦Chapter8/CohomotopyProduct · gammaOf⟧. Composing the homotopies with $\mu_\Gamma$ joins $h = \mu_\Gamma \circ (f, g)$ to $h_1 = \mu_\Gamma \circ (f_1, g_1)$.
4. By the previous theorem, $F \cap G = \mathrm{Pont}(h, \mathrm{north}, \beta)$ with $\beta = (c\gamma_1, \dots, c\gamma_p, d\gamma_{p+1}, \dots, d\gamma_{p+q})$, and likewise $F_1 \cap G_1$ with $c_1, d_1$ ⟦Chapter8/CohomotopyProduct · muBasis_gammaOf⟧.
5. Lemma 1 for positive diagonal matrices replaces $\beta$ by $\gamma$ at both ends, and Theorem B with basis $\gamma$ joins them ⟦Chapter7/ThmA · framedCobordant_of_homotopic⟧: $F \cap G \sim \mathrm{Pont}(h, \mathrm{north}, \gamma) \sim \mathrm{Pont}(h_1, \mathrm{north}, \gamma) \sim F_1 \cap G_1$.

> **Theorem (V8.17).** Let $M$ be compact and nonempty, $r + (p+q) = m$, $p \ge 1$ and $q \ge 1$. There is a map $\Pi_{n,p}(M) \times \Pi_{n',q}(M) \to \Pi_{r,p+q}(M)$ sending $([F], [G])$ to $[F \cap G]$ whenever $F$ and $G$ meet transversally. Any two maps with this property coincide (for this, $p \ge 1$ suffices). ⟦Chapter8/CohomotopyProduct · exists_intersection_product⟧ ⟦Chapter8/CohomotopyProduct · intersection_product_unique⟧

The map is defined by choosing transverse representatives of each pair of classes; invariance makes the value independent of the choice, and uniqueness holds because such representatives always exist. Neither $\Gamma$ nor $\mu$ enters the product, only its proof; the ordering, with the $p$ vectors from $F$ first, is built into $w$.

*Hidden hypotheses.* $p, q \ge 1$ (positive bases, Theorems A and B), and $p + q \le m$ through $r$. The case $p + q > m$ is not stated, since no natural number $r$ has $r + p + q = m$. Informally it is trivial: then $n + n' < m$, the parenthesis of V8.16 makes transverse representatives disjoint, and Milnor's product is the class of $\varnothing$.

### V8.17′ Problem 17: the group $\Pi^p(M)$ for $2p \ge m + 2$

Assume $m + 2 \le 2p$. With $n + p = m$ this gives $p \ge 1$ and $n + 1 < p$, so even an $(n+1)$-manifold has image of dense complement in $S^p$. That is the only way Milnor's hypothesis $p \ge \frac12 m + 1$ enters.

#### Room in the sphere

> **Lemma.** If $G$ is framed of dimension $n$ and codimension $p$ with $n + 1 < p$, and $H : M \times \mathbb R \to S^p$ is smooth, then $S^p \setminus H(N_G \times \mathbb R)$ is dense. ⟦Chapter8/CohomotopyGroup · dense_compl_range⟧

By Brown's theorem, the regular values of $H$ on the $(n+1)$-manifold $N_G \times \mathbb R$ are dense, and none lies in the image, since no linear map out of $\mathbb R^{n+1}$ is onto $\mathbb R^p$. For a single image $f(N_G)$ the lemma is applied to $H = f \circ \mathrm{pr}_1$ ⟦Chapter8/CohomotopyGroup · dense_compl_image⟧, so that case too carries $n + 1 < p$, though $n < p$ would do.

> **Lemma.** Let $p \ge 1$, $U \subseteq S^p$ open with $\text{north} \in U$, and $D \subseteq S^p$ dense. There are an orthonormal pair, with rotations $r_\tau$ by angle $\tau$ in its plane, and $\theta_0 \ge 0$ with $r_{\theta_0}(\text{north}) \in D$ and $r_\tau(\text{north}) \in U$ for all $\tau \in [0, \theta_0]$. ⟦Chapter8/CohomotopyGroup · exists_arc⟧

Take $z \in D$ in a ball about north inside $U$; the rotation path from north to $z$ never gets farther from north than $z$.

> **Lemma (rotation arc).** Let $M$ be compact and nonempty, $n + p = m$, $f$ smooth with regular value north, $r_\tau$ as above with $\theta_0 \ge 0$ and every $r_\tau(\text{north})$, $\tau \in [0, \theta_0]$, a regular value of $f$, and $b$ linearly independent. Then $r_{\theta_0}(\text{north})$ is a regular value, $dr_{\theta_0}b$ is independent, and there is a framed cobordism from $\mathrm{Pont}(f, r_{\theta_0}(\text{north}), dr_{\theta_0}b)$ to $\mathrm{Pont}(f, \text{north}, b)$ all of whose points $(x, t)$ have $f(x) = r_\tau(\text{north})$ for some $\tau \in [0, \theta_0]$. ⟦Chapter8/CohomotopyGroup · exists_rotCob⟧

The homotopy $(x,t) \mapsto r_{\theta_0\rho(t)}(f(x))$, with $\rho$ a smooth transition from $0$ ($t \le \frac14$) to $1$ ($t \ge \frac34$), hits $r_{\theta_0}(\text{north})$ exactly when $f(x) = r_{\theta_0(1-\rho(t))}(\text{north})$, a point of the arc. There $f$ is regular and the rotation is a diffeomorphism, so the $x$-derivative alone is onto ⟦Chapter8/CohomotopyGroup · isRegularValue_rotHom⟧, and the homotopy construction gives a cobordism with that preimage as its set. Its far end, $\mathrm{Pont}(r_{\theta_0} \circ f, r_{\theta_0}(\text{north}), dr_{\theta_0}b)$, *equals* $\mathrm{Pont}(f, \text{north}, b)$, the framing pulling back through $dr_{\theta_0}^{-1}$ ⟦Chapter7/Compose · pontV_comp⟧. This is Milnor's rotation proof of Lemma 2, with the set recorded and no orientation bookkeeping: the rotated basis is used as it is.

#### Disjoint representatives

> **Theorem.** Let $M$ be compact and nonempty and $m + 2 \le 2p$. For framed $F, G_1, G_2$ of dimension $n$ and codimension $p$ there is $F'$ with $F \sim F'$ and $F'$ disjoint from $G_1$ and $G_2$. Hence any two classes in $\Pi_{n,p}(M)$ have disjoint representatives. ⟦Chapter8/CohomotopyGroup · exists_cobordant_disjoint⟧ ⟦Chapter8/CohomotopyGroup · exists_disjoint_rep⟧

Write $F = \mathrm{Pont}(f, \mathrm{north}, ce)$. The complement of the compact set $f(N_{G_1}) \cup f(N_{G_2})$ is dense, so an arc of regular values of $f$ runs from north to some $z$ outside it, and the rotation arc gives $F \sim \mathrm{Pont}(f, z, dr(ce))$, whose set $f^{-1}(z)$ misses both. Two submanifolds are avoided at once because associativity and independence each need it.

#### Independence of the sum

> **Theorem (V8.17′).** Let $M$ be compact and nonempty and $m + 2 \le 2p$. If $F \sim F_1$ and $G \sim G_1$, all of dimension $n$ and codimension $p$, with $F \cap G = \varnothing$ and $F_1 \cap G_1 = \varnothing$, then $F \sqcup G \sim F_1 \sqcup G_1$. ⟦Chapter8/CohomotopyGroup · framedCobordant_union_of_framedCobordant⟧

*The idea.* Never move both pieces at once. Choose $G' \sim G$ disjoint from $F$ and $F_1$; move $G$ to $G'$ with $F$ fixed, $F$ to $F_1$ with $G'$ fixed, and $G'$ to $G_1$ with $F_1$ fixed ⟦Chapter8/CohomotopyGroup · framedCobordant_union_of_framedCobordant'⟧. Each move is an instance of the following lemma.

> **Lemma (one component).** Let $M$ be compact and nonempty, $m + 2 \le 2p$, $F \sim F_1$, and $G$ disjoint from $F$ and from $F_1$, all of dimension $n$ and codimension $p$. Then $F \sqcup G \sim F_1 \sqcup G$. ⟦Chapter8/CohomotopyGroup · union_left_of_framedCobordant⟧

*The proof as formalized.*
1. With a positive basis $b$ at north, Theorem C gives $F = \mathrm{Pont}(f, \mathrm{north}, cb)$ and $F_1 = \mathrm{Pont}(f_1, \mathrm{north}, c_1b)$. Lemma 1 and Theorem B give $f \simeq f_1$, via a homotopy $H$ constant for $t \le \frac14$ and $t \ge \frac34$ ⟦Chapter7/Homotopy · SmoothHomotopic.exists_const_near_ends⟧.
2. The common regular values of $f$ and $f_1$ outside $f(N_G) \cup f_1(N_G)$ form an open set $U$ containing north, since $f^{-1}(\text{north}) = N_F$ and $f_1^{-1}(\text{north}) = N_{F_1}$ miss $N_G$. The regular values of $H$ outside $H(N_G \times \mathbb R)$ form a dense set $D$, as $H(N_G \times \mathbb R) = H(N_G \times [0,1])$ is compact with dense complement. Take an arc from north to $z \in D$ inside $U$.
3. Four cobordisms follow, each with set disjoint from $N_G \times \mathbb R$. $X_1$, from $\mathrm{Pont}(f, z, dr(cb))$ to $F$, is the rotation arc for $f$, lying over $f^{-1}(\text{arc})$, which misses $N_G$. $X_2$, to $\mathrm{Pont}(f_1, z, dr(cb))$, is the homotopy construction for $H$, with set $H^{-1}(z)$. $X_3$, to $\mathrm{Pont}(f_1, z, dr(c_1b))$, is Lemma 1 for $(c/c_1)I$, with set $f_1^{-1}(z) \times \mathbb R$. $X_4$, to $F_1$, is the rotation arc for $f_1$.
4. The product cobordism $Y$ from $G$ to itself has set exactly $N_G \times \mathbb R$, by Theorem C and the homotopy construction for a constant homotopy ⟦Chapter8/CohomotopyGroup · exists_framedCob_prod⟧. Uniting each $X_i$ with $Y$ and chaining gives $F \sqcup G \sim F_1 \sqcup G$ ⟦Chapter8/FramedOps · framedCobordant_union⟧.

*What the book leaves implicit.* The hint "use the disjoint union operation" hides that a cobordism from $F$ to $F_1$ may run through $G$. The formal proof rules this out by rebuilding the cobordism from a homotopy and a well-chosen regular value, recording where each piece lies; the dimension hypothesis pays for the sweep $H(N_G \times \mathbb R)$.

#### The monoid laws

The empty framed submanifold $\varnothing_{n,p}$ exists only when $n + p = m$ ⟦Chapter8/CohomotopyGroup · emptyFramedSub⟧. The sum of two classes is defined through chosen disjoint representatives, and by independence $[F] + [G] = [F \sqcup G]$ for *any* disjoint representatives ⟦Chapter8/CohomotopyGroup · cohomotopyAdd⟧ ⟦Chapter8/CohomotopyGroup · cohomotopyAdd_mk⟧. Commutativity, associativity and $F \sqcup \varnothing = F$ are equalities of framed submanifolds ⟦Chapter8/CohomotopyGroup · union_comm'⟧ ⟦Chapter8/CohomotopyGroup · union_assoc'⟧ ⟦Chapter8/CohomotopyGroup · union_empty'⟧. For associativity the third class is represented by some $H' \sim H$ avoiding both $F$ and $G$, which is where the two-set form of the disjointness theorem is needed ⟦Chapter8/CohomotopyGroup · cohomotopyAdd_assoc⟧.

#### The inverse

Let $F^- = (N, (-v_1, v_2, \dots, v_p))$ ⟦Chapter8/CohomotopyGroup · FramedSub.negFirst⟧.

> **Theorem (V8.17′).** Let $M$ be compact and nonempty, $m + 2 \le 2p$ and $p \ge 1$. For every framed $F$ of dimension $n$ and codimension $p$, $[F] + [F^-] = [\varnothing_{n,p}]$. ⟦Chapter8/CohomotopyGroup · cohomotopyAdd_negFirst⟧

If $N = \varnothing$, $F \sqcup F^-$ is itself empty. Otherwise the proof rests on a lemma with no dimension hypothesis.

> **Lemma (cancelling pair).** Let $M$ be compact and nonempty, $p \ge 1$, $N \ne \varnothing$, and $(G, \varepsilon)$ product-neighbourhood data for $F$. There are disjoint framed $P, Q$ with $F \sim P$, $F^- \sim Q$ and $P \sqcup Q \sim \varnothing_{n,p}$. ⟦Chapter8/CohomotopyGroup · exists_cancel_pair⟧

Then $[F] + [F^-] = [P] + [Q] = [P \sqcup Q] = [\varnothing_{n,p}]$. Apart from making the sum defined, $2p \ge m + 2$ is used only in the middle equality.

*Tube maps.* For $\Phi : \mathbb R^p \to S^p$, the tube map is $\Phi \circ \pi$ on $V$ and the south pole elsewhere. It is smooth when $\Phi(s) = \text{south}$ for $|s| \ge r_0$, $r_0 < \varepsilon$, being then constant off the compact set $G(N \times \bar B_{r_0})$; likewise for families ⟦Chapter8/CohomotopyGroup · tubeMap⟧ ⟦Chapter8/CohomotopyGroup · contMDiff_tubeHom⟧. North is a regular value once $d\Phi$ is onto at the points of $B_\varepsilon$ that $\Phi$ sends to north, which we call the zeros of $\Phi$ ⟦Chapter8/CohomotopyGroup · isRegularValue_tubeMap⟧.

*Constants and model maps.* The formal proof takes $a = \min(\varepsilon/8, \frac14)$, $r_0 = \varepsilon/2$, $\varepsilon_0 = \min(r_0, r_0^2/2, ar_0)$, and $c > 0$ so large that §7's collapse map $\mathrm{col}_c$ (north only at $0$, derivative $c\cdot\mathrm{id}$ there) is the south pole for $|z| \ge \varepsilon_0/2$. Let $T_l = 2l\,\mathrm{proj}_{e_1} + (\mathrm{id} - \mathrm{proj}_{e_1})$, multiplying the $e_1$-component by $2l$. The model maps, all south for $|s| \ge r_0$, are:
- the *cancelling map* $\kappa(s) = \mathrm{col}_c\big((s_1^2 - a^2)e_1 + (s - s_1e_1)\big)$, with zeros $\pm ae_1$ and derivative $c\,T_{\sigma a}$ at $\sigma ae_1$, $\sigma = \pm 1$ ⟦Chapter8/CohomotopyGroup · can0⟧ ⟦Chapter8/CohomotopyGroup · can0_eq_north_iff⟧ ⟦Chapter8/CohomotopyGroup · hasMFDerivAt_can0⟧;
- the *folded maps* $\phi_\sigma(s) = \mathrm{col}_c\big(T_{\sigma a}(s - \sigma ae_1)\big)$, with the single zero $\sigma ae_1$ and the same derivative $c\,T_{\sigma a}$ there ⟦Chapter8/CohomotopyGroup · foldΦ_eq_north_iff⟧ ⟦Chapter8/CohomotopyGroup · hasMFDerivAt_foldΦ⟧.

*The proof as formalized.*
1. $P, Q$ are the Pontryagin manifolds, at north with basis $ce$, of the tube maps of $\phi_+, \phi_-$: the parallel copies $G(N \times \{\pm ae_1\})$, disjoint as $ae_1 \ne -ae_1$.
2. $P \sqcup Q$ *equals* the Pontryagin manifold of the tube map of $\kappa$ ⟦Chapter8/CohomotopyGroup · pontryagin_can0_eq_union⟧. The sets agree. Where $\pi(z) = \sigma ae_1$, the tube maps of $\kappa$ and $\phi_\sigma$ have the same derivative, since a tube map composed with $G$ is $\Phi \circ \mathrm{pr}_2$ and $dG$ is invertible ⟦Chapter8/CohomotopyGroup · mfd_tubeMap_eq⟧. And a Pontryagin framing depends only on the value and derivative at the point, for $A_f(x)$ kills $(T_xM)^\perp$ and agrees with $df_x$ on $T_xM$ ⟦Chapter8/CohomotopyGroup · At_eq_of_mfd_eq⟧ ⟦Chapter8/CohomotopyGroup · pontryagin_v_eq_of_mfd_eq⟧.
3. $P \sqcup Q \sim \varnothing$. §7's cancellation family $\mathrm{col}_c\big((s_1^2 - a^2\rho(t))e_1 + (s - s_1e_1)\big)$, with $\rho = 1$ for $t \le \frac14$, $\rho = -1$ for $t \ge \frac34$, $|\rho| \le 1$ and $\rho' \ne 0$ at zeros of $\rho$ ⟦Chapter7/CancelMap · exists_rho⟧, gives a tube family with north regular: where $\rho(t) = 0$ the zero is $s = 0$, $T_0$ kills $e_1$, and the $t$-derivative supplies that direction. At $t = 1$ north is not attained ($s_1^2 = -a^2$), and the homotopy construction gives the cobordism to $\varnothing$ ⟦Chapter8/CohomotopyGroup · framedCobordant_can0⟧.
4. $F \sim P$ and $F^- \sim Q$ via the moving family $\Phi_t(s) = \mathrm{col}_c\big(T_{l(t)}(s - \gamma(t))\big)$, with $l(t) = \sigma\big(\frac12 + (a - \frac12)\rho_0(t)\big)$, $\gamma(t) = \rho_0(t)\,\sigma ae_1$ and $\rho_0$ a transition from $0$ to $1$ ⟦Chapter8/CohomotopyGroup · lPath⟧ ⟦Chapter8/CohomotopyGroup · γPath⟧. At $t = 1$ this is $\phi_\sigma$; at $t = 0$ it is $\mathrm{col}_c(T_{\sigma/2}s)$, the plain collapse for $\sigma = 1$ and the collapse after reversing $s_1$ for $\sigma = -1$. As $G(x, se_i) = r(x + sv_i(x))$, the time-$0$ tube map equals $\mathrm{col}_c(se_i)$ along $s \mapsto r(x + s\sigma_iv_i(x))$, where $\sigma_1 = \sigma$ and $\sigma_i = 1$ otherwise ⟦Chapter8/CohomotopyGroup · Tcan_half_line⟧. §7's identification lemma then makes its Pontryagin manifold $(N, (\sigma v_1, v_2, \dots, v_p))$, which is $F$ or $F^-$ ⟦Chapter8/CohomotopyGroup · pontryagin_tubeMap_eq⟧ ⟦Chapter7/Identify · pontryagin_eq_of_collapse⟧. Since $|T_{l(t)}z| \ge 2a|z|$ and $|\gamma(t)| \le a$, the family is south for $|s| \ge r_0$ ⟦Chapter8/CohomotopyGroup · norm_Tcan_ge⟧ ⟦Chapter8/CohomotopyGroup · moveΦ_south⟧; each slice has derivative $c\,T_{l(t)}$ at its only zero $\gamma(t)$, so the homotopy construction applies ⟦Chapter8/CohomotopyGroup · framedCobordant_fold⟧.

The moving family translates the zero from $0$ to $\sigma ae_1$ while rescaling the $e_1$-direction from $\sigma$ to $2\sigma a$, exactly the derivative of $\kappa$ there. That match makes step 2 an equality rather than one more cobordism.

#### The group as stated

Negation is defined through a chosen representative, $-[F] = [F_c^-]$ for some $F_c \sim F$ ⟦Chapter8/CohomotopyGroup · cohomotopyNeg⟧. That $[F^-]$ depends only on $[F]$ is never proved by a cobordism. It follows from uniqueness of inverses: if $[F_0] = [F]$, then $[F_0^-] = [F_0^-] + [F] + [F^-] = [F_0^-] + [F_0] + [F^-] = [F^-]$ ⟦Chapter8/CohomotopyGroup · cohomotopyNeg_mk⟧.

> **Theorem (V8.17′, the group).** Let $M \subseteq \mathbb R^{K+1}$ be a compact, nonempty submanifold of dimension $m$ given by slice charts, and let $n + p = m$, $m + 2 \le 2p$ and $p \ge 1$. Then $\Pi_{n,p}(M)$ is an abelian group in which $[F] + [G] = [F \sqcup G]$ for disjoint representatives, the zero is $[\varnothing_{n,p}]$, and $-[F] = [F^-]$. ⟦Chapter8/CohomotopyGroup · cohomotopyGroup⟧ ⟦Chapter8/CohomotopyGroup · cohomotopyGroup_add⟧ ⟦Chapter8/CohomotopyGroup · cohomotopyGroup_neg⟧

The structure is a definition depending on the three hypotheses, not a global instance; three lemmas identify its addition, zero and negation ⟦Chapter8/CohomotopyGroup · cohomotopyGroup_zero⟧. The hypothesis $p \ge 1$ follows from $m + 2 \le 2p$ and only names the first framing vector. The hypothesis $n + p = m$ is genuine: without it there is no empty framed submanifold, indeed no class at all.

### What the formalization taught us

- **Reflexivity is not free.** Chapter 7 had it only for framed points; in every codimension the formal proof obtains it from Theorem C and the homotopy construction ⟦Chapter8/FramedOps · framedCobordant_refl⟧.
- **Cobordisms are closed, not compact.** They extend over all of $M \times \mathbb R$, so disjoint unions need a proof that underlying sets are closed ⟦Chapter8/FramedOps · FramedCob.isClosed_S⟧.
- **The hints hide sets.** Disjointness of cobordisms concerns sets, so Lemma 1, the homotopy construction and the rotation argument of Lemma 2 were re-proved with the set recorded ⟦Chapter8/FramedOps · exists_framedCob_of_homotopy⟧ ⟦Chapter8/CohomotopyGroup · exists_rotCob⟧.
- **Move the regular value, not the submanifold.** Transverse and disjoint representatives both come from a new regular value of a Theorem-C map; the translate of Problem 16 goes unused ⟦Chapter8/CohomotopyProduct · exists_transverse_cobordant⟧.
- **Identifications are exact.** The Pontryagin manifolds of $\mu \circ (f, g)$ and of the cancelling map are the framed intersection and the union of the folded copies on the nose, because Pontryagin framings are determined by the derivative ⟦Chapter8/CohomotopyProduct · pontryagin_mu_eq⟧ ⟦Chapter8/CohomotopyGroup · At_eq_of_mfd_eq⟧.
- **A choice of $\Gamma$ absorbs orientations,** reducing them to positive diagonal rescalings ⟦Chapter8/CohomotopyProduct · muBasis_gammaOf⟧.
- **Hidden hypotheses and scope.** The product assumes $p, q \ge 1$ (transverse representatives and uniqueness only $p \ge 1$) and is stated only for $p + q \le m$ ⟦Chapter8/CohomotopyProduct · exists_intersection_product⟧. The group needs $n + p = m$; its $p \ge 1$ is redundant ⟦Chapter8/CohomotopyGroup · cohomotopyGroup⟧. Milnor's parenthesis carries two equations that its proof does not need ⟦Chapter8/Transversality · inter_eq_empty_of_transverse⟧.
- **Where $2p \ge m + 2$ is spent.** Only on disjoint representatives and independence of the sum; the cancelling pair works for every $p \ge 1$ ⟦Chapter8/CohomotopyGroup · union_left_of_framedCobordant⟧ ⟦Chapter8/CohomotopyGroup · exists_cancel_pair⟧.
- **Negation comes free.** That reversing the first framing vector respects framed cobordism follows from uniqueness of inverses ⟦Chapter8/CohomotopyGroup · cohomotopyNeg_mk⟧.


## Part XII. The Appendix: one-manifolds (Milnor pp. 54–56)

Milnor's Appendix proves one theorem, that every smooth connected one-manifold is diffeomorphic to the circle or to an interval, and draws from it the one corollary the book uses: the boundary points of a compact 1-manifold come in pairs, the two ends of an arc (§§2, 4, 5). This part has two halves, written in that order and set out in that order.

The first half (V.A, V.A′) is the corollary alone, proved *without* the classification and for a merely **topological** 1-manifold with boundary, which is stronger than the book in the hypothesis and weaker in the conclusion. It keeps Milnor's idea, to parametrize as far as possible, and changes the three tools that carry it: arc-length parametrizations become arbitrary homeomorphisms onto intervals; Milnor's lemma on overlapping parametrizations becomes a lemma about arcs starting at a boundary point, the only kind ever extended, so no circle appears; and the maximal parametrization is reached by a finite induction over a cover by chart arcs. A short second file connects the result to the manifolds with boundary produced by Lemma 4 of §2. This is the half that Parts I to III depend on, and nothing else in the book does.

The second half (V.B to V.J) is Milnor's theorem itself, in nine stages, this time with his arc-length parametrizations and in a sharper form than he states: a connected Hausdorff σ-compact smooth one-manifold is diffeomorphic to **exactly one** of the circle, $[0,1]$, $[0,\infty)$ and $\mathbb R$, the case being read off from whether it is compact and whether its boundary is empty. It ends by proving the corollary a second time, as Milnor does, *from* the classification, with the two boundary points of a component identified as the two ends of one parametrization rather than counted modulo two. The first half is left in place untouched, because Chapters 2 and 4 cite it; the second is used by nothing in the book, and is here because the book states it — and by one thing outside the book, the dimension of a non-orientable manifold in Part VII.

**Map.**
- `Appendix/OneManifold`: V.A; arcs, the end lemma for two arcs, the overlap of an arc from a boundary point with any arc, gluing, the finite induction to a closed arc, the pairing of boundary points.
- `Appendix/HalfSpace`: V.A′; the half-space over a zero space is a half-line, and the half-slice submanifolds of Chapter 2 satisfy the hypotheses of V.A.
- `Appendix/TwoComponents`: V.B; Milnor's Appendix Lemma 1, the topological half, with the circle case counted.
- `Appendix/Smooth/Setup`, `Appendix/Smooth/SmoothArc`: V.C, V.D; the one-dimensional model and smooth arcs.
- `Appendix/Smooth/LengthElement`, `Appendix/Smooth/ArcLength`: V.E; a Riemannian metric in dimension one, and unit-speed arcs.
- `Appendix/Smooth/Affine`: V.F; Lemma 1 in full, and the extension theorem that preserves the coordinate.
- `Appendix/Smooth/Compact`, `Appendix/Smooth/Circle`, `Appendix/Smooth/NonCompact`: V.G, V.H, V.I; Milnor's four cases.
- `Appendix/Smooth/Main`: V.J; the theorem, its six exclusions, and the boundary count drawn from it.

### V.A The boundary count for compact topological 1-manifolds

> **Theorem (V.A).** Let $H$ be a topological space and $\varphi : H \to [0,\infty)$ a homeomorphism. Let $M$ be a compact Hausdorff space with a charted-space structure modelled on $H$: an atlas of homeomorphisms from open subsets of $M$ onto open subsets of $H$, and for each point a chosen chart of the atlas whose domain contains it. Let $B \subseteq M$ be such that, for every chart $e$ of the atlas and every $x$ in the domain of $e$,
> $$x \in B \iff \varphi(e(x)) = 0 .$$
> Then $B$ is finite and has an even number of points. ⟦Appendix/OneManifold · even_ncard_boundary⟧

The condition on $B$ is called boundary compatibility, and $\varphi(e(x))$ is the coordinate of $x$ in the chart $e$ ⟦Appendix/OneManifold · BoundaryCompatible⟧ ⟦Appendix/OneManifold · coord⟧.

*Stronger than the book.* Milnor's manifolds are smooth subsets of $\mathbb R^k$. Here $M$ is abstract, and a Mathlib charted space imposes no compatibility between its charts, so $M$ is any compact Hausdorff topological 1-manifold with boundary: no smooth structure, no embedding, no second countability, and no derivative anywhere in the proof. The model is any space homeomorphic to $[0,\infty)$, so that the half-space models of Chapter 2 fit without re-charting ⟦Appendix/HalfSpace · halfSpaceHomeomorph⟧.

*Weaker than the book.* This theorem does not state the classification. On the way, its proof shows that the component of a boundary point is the homeomorphic image of a closed interval whose two ends are its only boundary points ⟦Appendix/OneManifold · exists_closed_arc⟧ ⟦Appendix/OneManifold · IsFrom.source_eq_of_mem⟧. Components without boundary points are never examined, since they contribute nothing to the count, and the circle case therefore never arises. The classification itself is V.J, in the second half of this part, and V.J draws the boundary count from it a second time; but that is a statement about *smooth* one-manifolds, so it neither subsumes V.A nor is subsumed by it.

*What the book leaves implicit.* Milnor's boundary, the points that charts send to $\partial H^m$, is tacitly independent of the chart. The formal statement takes a set $B$ and assumes that every chart sends exactly $B$ to $0$; the proof uses this only for the chosen chart at each point ⟦Appendix/OneManifold · exists_arc_of_mem_boundary⟧ ⟦Appendix/OneManifold · exists_arc_of_notMem_boundary⟧. Hausdorffness, automatic in $\mathbb R^k$, is a genuine hypothesis, as an example outside the formal text shows: two copies of $[0,1]$ glued along $[0,1)$ form a compact space, locally homeomorphic to open subsets of $[0,\infty)$, whose evident charts send exactly $0$ and the two copies of $1$ to $0$. It has three boundary points.

*The idea.* Start at a boundary point $p$ with a chart arc $[0,\varepsilon) \to M$ and extend it. While its interval is half-open, its domain is not the whole component of $p$, so some chart arc contains a frontier point of the domain, and the two glue to an arc from $p$ containing both. Finitely many chart arcs cover $M$ and each gluing swallows a new one, so eventually the interval is closed, $[0,c]$; the domain is then the component, and its far end is the only other boundary point there. So "the other end of my component" is a fixed-point-free involution of $B$. The one hard lemma: the overlap of an arc from a boundary point with any arc is connected ⟦Appendix/OneManifold · overlap_ordConnected⟧.

*The proof as formalized.*

#### 1. Arcs, and the finiteness of $B$

An *arc* of $(M,B)$ is a homeomorphism $A$ from an open set $U_A \subseteq M$ onto a bounded interval $T_A \subseteq \mathbb R$ with more than one point, such that for $x \in U_A$
$$x \in B \iff A(x) \notin \operatorname{int} T_A$$
⟦Appendix/OneManifold · Arc⟧. As $\operatorname{int} T_A = (\inf T_A, \sup T_A)$ ⟦Appendix/OneManifold · interior_target⟧, the points of $B$ in $U_A$ are those whose coordinate is an endpoint of $T_A$ lying in $T_A$. Boundedness makes $\inf T_A$ and $\sup T_A$ real numbers, and every limit argument below is about them. An arc can be reversed, $x \mapsto -A(x)$ onto $-T_A$ ⟦Appendix/OneManifold · neg⟧. An arc *from* $p$ has $p \in U_A$, $A(p) = 0$ and $0 \in T_A \subseteq [0,\infty)$ ⟦Appendix/OneManifold · IsFrom⟧; its interval is $[0,c)$ or $[0,c]$, with $c = \sup T_A > 0$ ⟦Appendix/OneManifold · IsFrom.target_eq⟧.

Arcs come from charts. Restrict a chart to the points whose coordinate lies in a bounded interval $J \subseteq [0,\infty)$ with more than one point. If the model points with coordinate in $J$ form an open subset of $H$ inside the chart's image, and no point of $J$ other than $0$ is an endpoint of $J$, the result is an arc with interval $J$, by boundary compatibility of the chart ⟦Appendix/OneManifold · arcOfChart⟧. The chart at $y$ contains all model points whose coordinate is within some $\varepsilon > 0$ of that of $y$ ⟦Appendix/OneManifold · exists_radius⟧. At $p \in B$ the coordinate is $0$, and $J = [0,\varepsilon)$ gives an arc from $p$; at $y \notin B$ the coordinate $t_0$ is positive, and $J = (t_0 - \delta, t_0 + \delta)$ with $\delta = \min(\varepsilon, t_0)$ gives an arc around $y$ with open interval, whose domain misses $B$ ⟦Appendix/OneManifold · exists_arc_of_mem_boundary⟧ ⟦Appendix/OneManifold · exists_arc_of_notMem_boundary⟧.

So $B$ is closed ⟦Appendix/OneManifold · isClosed_boundary⟧, and an arc from $p$ with interval $[0,\varepsilon)$ meets $B$ only in $p$ ⟦Appendix/OneManifold · boundary_inter_source_eq⟧. As $B$ is compact, finitely many such arcs cover it, and $B$ is finite ⟦Appendix/OneManifold · finite_boundary⟧. This half of the conclusion uses neither Hausdorffness nor gluing.

#### 2. Two arcs: monotone transitions and the end lemma

Fix arcs $A$ and $A'$. The overlap in $A$'s coordinate, $S = A(U_A \cap U_{A'})$, is relatively open in $T_A$, and the transition $\tau = A' \circ A^{-1} : S \to T_{A'}$ is continuous and injective ⟦Appendix/OneManifold · overlap⟧ ⟦Appendix/OneManifold · trans⟧ ⟦Appendix/OneManifold · overlap_relOpen⟧. *Where the formal proof departs from Milnor.* Milnor differentiates: arc length forces $\tau' = \pm 1$, so the graph of $\tau$ consists of segments of slope $\pm 1$. The formal proof uses only that a continuous injection on an interval is strictly monotone ⟦Appendix/OneManifold · strictMonoOn_or_strictAntiOn_of_ordConnected⟧, and it names the components of $S$ without topology, through the *hull*
$$\operatorname{hull}_S(t_0) = \{\, t : [t, t_0] \subseteq S \,\},$$
the largest interval in $S$ through $t_0$, with $[t,t_0]$ the segment between the two points in either order ⟦Appendix/OneManifold · hull⟧. Two hulls are equal or disjoint, and the hulls of a relatively open subset of an interval are relatively open ⟦Appendix/OneManifold · hull_eq_or_disjoint⟧ ⟦Appendix/OneManifold · hull_relOpen⟧. Call an endpoint of a hull *free* (our term) if it lies in $T_A$ but not in $S$.

**The end lemma.** Let $\beta = \sup K$ be a free endpoint of a hull $K$. As $s \uparrow \beta$ in $K$, $\tau(s)$ converges monotonically to $L = \sup \tau(K)$ or $L = \inf \tau(K)$, as $\tau$ increases or decreases on $K$ ⟦Appendix/OneManifold · tendsto_sSup_of_monotoneOn⟧ ⟦Appendix/OneManifold · tendsto_sInf_of_antitoneOn⟧, and $L \notin T_{A'}$ ⟦Appendix/OneManifold · end_lemma⟧. Indeed $y = A^{-1}(\beta)$ lies in $U_A \setminus U_{A'}$. If $L \in T_{A'}$, then $A^{-1}(s) \to y$ by continuity of $A^{-1}$ at $\beta$, while $A^{-1}(s) = A'^{-1}(\tau(s)) \to A'^{-1}(L)$ by continuity of $A'^{-1}$ at $L$; limits in $M$ are unique, so $y = A'^{-1}(L) \in U_{A'}$, a contradiction. The interval $T_{A'}$ contains the values $\tau(s)$, all on one side of $L$, but not $L$, so it lies entirely on that side ⟦Appendix/OneManifold · lt_of_end_lemma_upper⟧. Say the free end *reaches the upper edge* of $T_{A'}$ if $L$ is a strict upper bound of $T_{A'}$ (so $L = \sup T_{A'} \notin T_{A'}$), and the lower edge likewise; every free end, left or right, reaches an edge ⟦Appendix/OneManifold · end_right⟧ ⟦Appendix/OneManifold · end_left⟧. This is Milnor's remark that the segments of the graph cannot end inside the rectangle $I \times J$, and it is the first use of Hausdorffness.

**Clash.** Free ends of two distinct hulls cannot reach the same edge ⟦Appendix/OneManifold · clash_upper⟧ ⟦Appendix/OneManifold · clash_lower⟧: the images of the hulls would be intervals with the same unattained supremum (or infimum), such intervals meet ⟦Appendix/OneManifold · inter_nonempty_of_sSup_eq⟧, and injectivity of $\tau$ turns a common value into a common point. Nor can a free end reach an edge that belongs to $T_{A'}$ ⟦Appendix/OneManifold · not_upper_of_sSup_mem⟧ ⟦Appendix/OneManifold · not_lower_of_sInf_mem⟧. Together these give Milnor's count of at most one segment ending on each edge of the rectangle.

#### 3. The overlap with an arc from a boundary point is an interval

> **Lemma.** Let $M$ be Hausdorff, $A$ an arc with $p \in U_A$, $A(p) = 0$ and $T_A = [0,c)$ for some $c > 0$, and $A'$ any arc. Then $A(U_A \cap U_{A'})$ is an interval. ⟦Appendix/OneManifold · overlap_ordConnected⟧

First, each hull of $S$ has at least two points, and an endpoint of a hull other than $0$ and $c$ is free: if it lay in $S$ it would lie in the hull, which, being relatively open, would extend past it ⟦Appendix/OneManifold · hull_nontrivial⟧ ⟦Appendix/OneManifold · sSup_hull_notMem⟧ ⟦Appendix/OneManifold · sInf_hull_notMem⟧. Second, $p \in B$ ⟦Appendix/OneManifold · p_mem_boundary⟧, so if $0 \in S$ then $\tau(0) = A'(p)$ is an endpoint of $T_{A'}$ belonging to $T_{A'}$: $p$ *occupies* an edge, which no free end can reach ⟦Appendix/OneManifold · trans_zero_eq_sInf_or_sSup⟧.

Now suppose $t_1 < u < t_2$ with $t_1, t_2 \in S$ and $u \notin S$, and let $K_1, K_2$ be the hulls of $t_1, t_2$, so that $K_1 < u < K_2$. The right end of $K_1$ is at most $u < c$ and the left end of $K_2$ at least $u > 0$, so both are free. The left end of $K_1$ is free, or else it is $0$ and $0 \in S$. In the first case $K_1$ has two free ends, which reach opposite edges since $\tau$ is monotone on $K_1$, and the free left end of $K_2$ must share an edge with one of them: a clash. In the second case $p$ occupies one edge, so the free right end of $K_1$ and the free left end of $K_2$ both reach the other: again a clash ⟦Appendix/OneManifold · overlap_ordConnected⟧. In Milnor's picture the graph of $\tau$ lies in the rectangle $T_A \times T_{A'}$, with four edges. The formal count needs only the two edges of $T_{A'}$: the right edge of $T_A$ is never examined, and the left one enters only through the corner $(0, \tau(0))$, which the boundary point $p$ pins to an edge of $T_{A'}$. Milnor's two-component case, the circle, cannot occur.

#### 4. Gluing two arcs

> **Lemma.** Let $M$ be Hausdorff, $A$ an arc from $p$ with $T_A = [0,c)$, $c > 0$, $A'$ an arc, and $x \in U_{A'} \setminus U_A$ a point of the closure of $U_A$. Then there is an arc $\tilde A$ from $p$ with $U_A \cup U_{A'} \subseteq U_{\tilde A}$. ⟦Appendix/OneManifold · exists_extension⟧

*Normalization.* Put $d = A'(x)$ and $S' = A'(U_A \cap U_{A'}) = \tau(S)$, an interval. By injectivity $d \notin S'$, and $d \in \overline{S'}$ because $x$ is a limit of points of $U_A \cap U_{A'}$ and $A'$ is continuous at $x$. So $S'$ lies on one side of $d$; after reversing $A'$ if necessary ⟦Appendix/OneManifold · overlap_neg_left⟧, $S' < d = \sup S'$. The normalized case ⟦Appendix/OneManifold · exists_extension_aux⟧ runs as follows, with $\sigma = A \circ A'^{-1} : S' \to S$ the inverse of $\tau$.

1. *The overlap sits at the far end of $T_A$.* The end $d$ of $S'$ is free for the pair $(A', A)$, so $\sigma(t)$ reaches an edge of $T_A = [0,c)$ as $t \uparrow d$. The lower edge is excluded because $0 \in T_A$; hence $\sigma$ is increasing, $\sup S = c$, and $\tau$ is increasing ⟦Appendix/OneManifold · end_right⟧.
2. *Below $d$, everything is overlap.* If $\inf S \notin S$, it is a free end, and $\inf S'$ is a strict lower bound of $T_{A'}$ ⟦Appendix/OneManifold · end_left⟧. If $\inf S \in S$, then $\inf S = 0$ (a positive one would be free), and $\tau(0)$ is an endpoint of $T_{A'}$ lying in $T_{A'}$, the lower one since $\tau(0) < \tau(s) < d$ for $s > 0$ in $S$ ⟦Appendix/OneManifold · trans_zero_eq_sInf_or_sSup⟧. Either way every $t \in T_{A'}$ below $d$ lies in $S'$, so a point $y \in U_{A'}$ lies in $U_A$ exactly when $A'(y) < d$.
3. *The new arc.* With $c'' = c + \sup T_{A'} - d$, define on $U_A \cup U_{A'}$ and on $T = \{\, t \ge 0 : t < c \text{ or } d + t - c \in T_{A'} \,\}$
$$\tilde A(y) = \begin{cases} A(y), & y \in U_A,\\ c + A'(y) - d, & y \notin U_A,\end{cases} \qquad \tilde A^{-1}(t) = \begin{cases} A^{-1}(t), & t < c,\\ A'^{-1}(d + t - c), & t \ge c;\end{cases}$$
$T$ is an interval with $(0,c'') \subseteq T \subseteq [0,c'']$ ⟦Appendix/OneManifold · exists_extension_aux⟧. Milnor extends $\tau$ to an affine map $L$ and pieces $f$ together with $g \circ L$. Here $\tau$ is only monotone, so beyond $c$ the formal proof uses $A'^{-1}$ composed with the translation $t \mapsto d + t - c$, which agrees with $\tau$ only in the limit at the seam.
4. *Continuity at the seam.* On $U_{A'}$, $\tilde A = G \circ A'$ with $G = \sigma$ below $d$ and $G(t) = c + t - d$ from $d$ on. $G$ is continuous on $T_{A'}$: below $d$ it is $\sigma$ on the neighbourhood $S'$ (step 2), $\sigma(t) \to c = G(d)$ as $t \uparrow d$ (step 1), and above $d$ it is affine ⟦Appendix/OneManifold · tendsto_sSup_of_monotoneOn⟧. As $U_A$ and $U_{A'}$ are open, $\tilde A$ is continuous on their union. Dually, at $c$: $S$ contains $(\inf S, c)$, and there $\tilde A^{-1}(s) = A'^{-1}(\tau(s)) \to A'^{-1}(d) = x = \tilde A^{-1}(c)$ ⟦Appendix/OneManifold · exists_extension_aux⟧.
5. *The rest.* Step 2 decides the branches, and the inverse identities follow. A point of $U_A$ is in $B$ iff $A(y) = 0$ iff $\tilde A(y) \notin (0,c'')$; a point of $U_{A'} \setminus U_A$ has $A'(y) \ge d > \inf T_{A'}$, so it is in $B$ iff $A'(y) = \sup T_{A'}$ iff $\tilde A(y) = c''$ ⟦Appendix/OneManifold · exists_extension_aux⟧.

At some 370 lines this is the longest proof of the part: the formal cost of Milnor's "$f$ and $g \circ L$ piece together to yield the required extension" once the pieces are merely monotone.

#### 5. The closed arc

> **Proposition.** Under the hypotheses of V.A, for every $p \in B$ there is an arc from $p$ whose interval contains its supremum, that is, equals $[0,c]$. ⟦Appendix/OneManifold · exists_closed_arc⟧

Choose for each $y \in M$ a chart arc containing $y$; by compactness finitely many of them, indexed by a finite set $s$, cover $M$. Start from the arc from $p$ with interval $[0,\varepsilon)$ and induct on the number of $z \in s$ whose arc's domain is not contained in the current domain $U_A$. If $\sup T_A \in T_A$ we are done. Otherwise $T_A = [0,c)$, and $U_A$ is not the whole component of $p$: the component is closed, hence compact, so if it were $U_A$ then $T_A = A(U_A)$ would be compact and contain $c$. As $U_A$ is an open proper subset of this connected component and contains $p$, some $x \notin U_A$ lies in its closure ⟦Appendix/OneManifold · exists_mem_closure_of_ne⟧. This $x$ lies in the domain of the cover arc of some $y \in s$, and gluing gives an arc from $p$ whose domain contains both domains. The count drops: $y$ was not absorbed before (its domain contains $x$) and is now. Milnor extends to a maximal parametrization instead; no maximality principle is needed here.

A closed arc fills its component ⟦Appendix/OneManifold · IsFrom.source_eq_of_mem⟧: its domain $A^{-1}([0,c])$ is compact, hence closed because $M$ is Hausdorff (the second use), and it is open, connected and contains $p$ ⟦Appendix/OneManifold · isPreconnected_source⟧. By the boundary condition,
$$B \cap \operatorname{comp}(p) = \{\, p,\ A^{-1}(c) \,\}$$
⟦Appendix/OneManifold · IsFrom.boundary_inter_component⟧.

#### 6. Pairing and parity

Each $p \in B$ thus has a partner $q = A^{-1}(c) \in B$, distinct from $p$ as $A(q) = c > 0 = A(p)$, with $B \cap \operatorname{comp}(p) = \{p, q\}$ ⟦Appendix/OneManifold · exists_partner⟧. Choosing a partner $\iota(p)$ for each $p$ gives an involution: $\iota(p)$ lies in the component of $p$, so $\iota(\iota(p)) \in \{p, \iota(p)\}$, and it is not $\iota(p)$. The count is a line of algebra ⟦Appendix/OneManifold · even_ncard_of_involution⟧: over a finite set with a fixed-point-free involution, $\prod(-1) = 1$ because the factors cancel in pairs, so $(-1)^{\#B} = 1$ and $\#B$ is even. With step 1 this is V.A ⟦Appendix/OneManifold · even_ncard_boundary⟧.

### V.A′ The count for the manifolds with boundary of Lemma 4

> **Theorem (V.A′).** Let $M$ be a Hausdorff smooth manifold modelled, through a model with corners, on a real normed space $E$ (finite dimension and empty boundary are not required), and let $Z$ be a real normed space with at most one point, that is, $Z = 0$. Let $B \subseteq X \subseteq M$, and suppose that $X$ is a half-slice submanifold of $M$ with boundary $B$ over $Z$: every point of $X$ lies in the domain of a half-slice chart, a diffeomorphism $\Phi$ from an open subset of $M$ onto an open subset of $\mathbb R \times Z$ such that, for $q$ in its domain, $q \in X \iff \Phi(q)_1 \ge 0$ and $q \in B \iff \Phi(q)_1 = 0$ (the chart also carries a base point of $X$ in its domain). If $X$ is compact, then $B$ is finite and has an even number of points. ⟦Appendix/HalfSpace · IsHalfSliceSubmanifold.even_ncard_boundary⟧

Half-slice charts and the half-space model $\{(t,z) \in \mathbb R \times Z : t \ge 0\}$ are those of V2.4 ⟦Chapter2/Boundary · HalfSliceChart⟧ ⟦Chapter2/Boundary · IsHalfSliceSubmanifold⟧. The atlas of $X$ consists of the restrictions to $X$ of all half-slice charts, with a chosen one at each point ⟦Chapter2/Boundary · toChart⟧ ⟦Chapter2/Boundary · chartedSpace⟧. For this structure the boundary of $X$ in Mathlib's sense consists exactly of the points of $X$ that lie in $B$, which under the hypothesis $B \subseteq X$ is all of $B$ ⟦Chapter2/Boundary · boundary_eq⟧: V.A′ counts the genuine boundary.

*The idea.* For $Z = 0$ the half-space is a half-line, the boundary hypothesis of V.A is built into the definition of a half-slice chart, and V.A applies to $X$ itself.

*The proof as formalized.* For $Z = 0$, $(t,z) \mapsto t$ is a homeomorphism of the half-space onto $[0,\infty)$, with inverse $t \mapsto (t,0)$ ⟦Appendix/HalfSpace · halfSpaceHomeomorph⟧. Each chart of $X$ is induced by a half-slice chart $\Phi$, its coordinate at $q$ is the first component of $\Phi(q)$, and by definition this vanishes exactly on $B$; so $X$ is boundary compatible for $\{q \in X : q \in B\}$, for every chart of the atlas ⟦Appendix/HalfSpace · IsHalfSliceSubmanifold.boundaryCompatible⟧. Finally $X$ is a compact space, Hausdorff as a subspace of $M$; V.A applies, and the inclusion $X \to M$, injective and carrying $\{q \in X : q \in B\}$ onto $B$ because $B \subseteq X$, transports finiteness and the count ⟦Appendix/HalfSpace · IsHalfSliceSubmanifold.even_ncard_boundary⟧. Only the continuity of $\Phi$ and $\Phi^{-1}$ is used. A lemma that a zero-dimensional space has at most one point is included ⟦Appendix/HalfSpace · subsingleton_of_finrank_eq_zero⟧, though the applications take $Z$ to be a zero subspace and check this directly.

*From Lemma 4 to V.A′.* Lemma 4 (V2.6) makes these manifolds ⟦Chapter2/WithBoundary · isHalfSliceSubmanifold_levelSet⟧. For $f : M \to N$ smooth between boundaryless manifolds modelled on finite-dimensional spaces, $y$ a regular value, and $g : M \to \mathbb R$ smooth such that at each point of $f^{-1}(y) \cap g^{-1}(0)$ some tangent vector is killed by $df$ but not by $dg$, it makes $\{g \ge 0\}$ a half-slice submanifold of the level set $f^{-1}(y)$ with boundary $\{g = 0\}$, over a space $Z'$ of dimension $\dim M - \dim N - 1$. When $\dim M = \dim N + 1$, $Z' = 0$: the ambient manifold of V.A′ is the level set, a 1-manifold, and $X = f^{-1}(y) \cap \{g \ge 0\}$. The two applications of V.A′ supply Hausdorffness from the ambient space and compactness by exhibiting $X$ as closed in a compact set.

- *Brouwer (V2.10).* With $g(x) = 1 - \|x\|^2$ and $f$ the retraction onto the sphere, extended by a cutoff, $X$ is compact inside the unit ball, and V.A′ makes $\#B$ even although $B = \{y\}$ ⟦Chapter2/Brouwer · exists_fixedPoint_of_contDiff⟧.
- *The homotopy lemma, case 1 (V4.3).* Lemma 4 with the two functions $t$ and $1 - t$ (V4.1) ⟦Chapter4/Cylinder · isHalfSliceSubmanifold_levelSet_two⟧ makes $F^{-1}(y) \cap (M \times [0,1])$ a half-slice submanifold, compact because $M$ is; V.A′ gives the parity of $\#f^{-1}(y) + \#g^{-1}(y)$ ⟦Chapter4/Homotopy · homotopy_lemma_of_isRegularValue⟧.
- *Lemma 1 of §5 (V5.3)* needs the arcs themselves. Through the same identification it applies the closed-arc proposition of step 5 to $f^{-1}(y) \cap \{g \ge 0\}$, whose compactness is a hypothesis there, pairs each boundary point with the far end of its arc, and shows that the two ends carry opposite signs ⟦Chapter5/LemmaOne · lemmaOne_ambient'⟧.

### The classification: what it says, and why arc length

> **Theorem (V.J).** Let $M$ be a connected, Hausdorff, σ-compact, nonempty smooth one-manifold. Then $M$ is diffeomorphic to **exactly one** of four models, and which one is settled by two questions. If $M$ is compact, it is the circle when its boundary is empty (V.H) and $[0,1]$ when it is not (V.G). If $M$ is not compact, it is $\mathbb R$ when its boundary is empty and $[0,\infty)$ when it is not (V.I). ⟦Appendix/Smooth/Main · nonempty_diffeomorph_or⟧ ⟦Appendix/Smooth/Main · models_pairwise_not_diffeomorph⟧

That is Milnor's Appendix theorem, with the four models named instead of "some interval of real numbers" and with the mutual exclusions proved. This section says what the setting is, why the proof has to use arc length, and where the hypotheses go; the seven that follow set out its nine stages, V.B to V.J, in the order in which they are used rather than the order in which they were written.

*The setting.* $M$ is charted, through a model with corners $I$, on a real normed space $E$ of dimension one, and "boundary" means Mathlib's boundary of $M$ relative to $I$ — which V.C shows to be the set of points whose coordinate in *any* chart lies on the frontier of the model's range, so that it is the boundary in the naive sense and needs no compatibility hypothesis of the kind V.A has to assume. The model itself is **not** assumed boundaryless: V.C sorts its range into three shapes, the line, a closed half-line and a nondegenerate compact interval, and all three stay alive to the end, the third making $M$ a one-manifold *with corners*. Smooth means $C^\infty$ except where $C^1$ is noted. Where the boundary is assumed empty, that is a statement about $M$ and not about the model.

*Why arc length, and not arbitrary charts.* Milnor parametrizes by arc length and observes that the transition between two such parametrizations has derivative $\pm 1$, hence is $s \mapsto \pm s + k$. It is tempting to read this as a convenience, since a transition between one-dimensional charts is in any case a monotone diffeomorphism, and monotonicity is all that V.A needs. It is not a convenience, and V.F says exactly why. The engine of the whole proof is an *extension* step: an arc that does not yet fill its component is glued to a chart arc reaching past its end. With merely monotone transitions the glued arc contains a reparametrization of the old one, and the strongest conclusion one can state is an existential that forgets the witness's coordinate — from the statement alone the transition from the old parameter to the new could be $s \mapsto s^2$. With arc length the transition is $s \mapsto s$, the sign and the constant both being pinned by the normalization, so the old parameter *is* the new parameter on the old domain. That is what makes a chain of extensions mean anything, and it is what fixes the period in the circle case. Milnor states his lemma for arc-length parametrizations because it has to be stated for them.

*What arc length presupposes.* A Riemannian metric. Milnor's manifolds sit in $\mathbb R^k$ and he restricts the Euclidean metric without comment. In dimension one a Riemannian metric is a *length element*: a positive smooth density transforming by the absolute value of the derivative of a transition. It is the one piece of general theory the classification needs and Mathlib does not have, so it is built here (V.E), and it is the single place where σ-compactness enters the whole nine stages. There the hypothesis is not a technicality but a necessity: a manifold carrying a Riemannian metric is metrizable, the long line carries none, and the long line is a connected smooth one-manifold which is neither the circle nor an interval. Everything after the length element — the arcs, the curves, the propagation lemma, all four cases — uses only Hausdorffness, connectedness, and whether or not $M$ is compact.

*The shape of the proof.* Milnor's Lemma 1 and its two-component picture come first (V.B, V.F), then unit-speed arcs (V.C to V.E), then the four cases in two pairs. With a boundary point there is an honest exhaustion, because an arc issuing from a boundary point has a half-open interval and can therefore be extended: finitely many chart arcs cover a compact manifold, each gluing swallows one more, and the arc that results *is* the diffeomorphism (V.G). Without a boundary point there is no such exhaustion, because every arc then has an open interval and the extension theorem needs a half-open one; so injectivity is dropped, arcs are replaced by *curves* — maps of the line agreeing near each time with an arc-length parametrization — a propagation lemma makes them unique, and compactness makes them close up into Milnor's periodic parametrization (V.H). The two non-compact cases run the same curve machinery without the closing up (V.I). The assembly (V.J) needs two invariants to tell the four models apart: compactness, and the number of boundary points.

### V.B and V.C Lemma 1's topological half, and the one-dimensional model

> **Lemma (V.B).** Let $A$ and $A'$ be arcs of a Hausdorff $(M, B)$ in the sense of V.A, and let $S = A(U_A \cap U_{A'})$ be the overlap read in $A$'s coordinate, whose components are its hulls. Call a hull *inner* when both of its ends are interior to $T_A$. Then an inner hull is carried by the transition onto the whole of $T_{A'}$ and is the *only* hull, so that $S$ is a single interval; every hull that is not inner reaches an end of $T_A$; hence $S$ has at most **two** components; and two distinct components reach *opposite* ends of $T_A$. ⟦Appendix/TwoComponents · IsInnerHull⟧ ⟦Appendix/TwoComponents · image_trans_hull_eq_of_isInnerHull⟧ ⟦Appendix/TwoComponents · ordConnected_overlap_of_isInnerHull⟧ ⟦Appendix/TwoComponents · encard_hulls_le_two⟧ ⟦Appendix/TwoComponents · sInf_eq_and_sSup_eq_of_hull_ne⟧

This is Milnor's Appendix Lemma 1 with its affine clause removed, and it is his picture: the graph of the transition lies in the rectangle $T_A \times T_{A'}$ in at most two segments, neither of which can end inside it, and when there are two they end on *opposite* edges of $T_A$ — which is the circle case, the one V.A excludes by fiat by always starting an arc at a boundary point. Here it is counted rather than excluded.

*The idea the earlier file lacked* is to single out the inner hull. Both of its ends are free, so by the end lemma of V.A the transition runs off both ends of $T_{A'}$ at once; being monotone, its image is all of $T_{A'}$; and injectivity then leaves no room for a second hull ⟦Appendix/TwoComponents · hull_eq_of_isInnerHull⟧. The two clash lemmas of V.A are therefore not needed here at all, and V.A's normalization turns out to have been doing nothing essential ⟦Appendix/TwoComponents · sInf_eq_or_sSup_eq_of_not_isInnerHull⟧. Two byproducts: an inner hull occurs exactly when $A'$ sits inside $A$ ⟦Appendix/TwoComponents · source_subset_of_isInnerHull⟧, and an inner hull forces $A'$ to contain no boundary point at all ⟦Appendix/TwoComponents · not_isInnerHull_of_mem_boundary⟧ — which is why V.A, extending only arcs from boundary points, never met one. *Hypotheses:* $M$ Hausdorff, where V.A's end lemma already needs it, and the two arcs' own data. No charts, no smoothness, no compactness, no dimension.

*The one-dimensional model (V.C).* A closed convex subset of the line with nonempty interior is the line, a closed half-line, or a nondegenerate compact interval ⟦Appendix/Smooth/Setup · closed_convex_cases⟧, so the model range, read through a linear identification of $E$ with $\mathbb R$ normalized once and for all ⟦Appendix/Smooth/Setup · modelCoord⟧, is $\mathbb R$, a half-line $[a,\infty)$, or a nondegenerate $[a,b]$ — never $(-\infty, a]$ ⟦Appendix/Smooth/Setup · modelRange_cases⟧. Every chart then carries a real coordinate, whose image is an open set cut by the model range ⟦Appendix/Smooth/Setup · chartCoord⟧; derivatives along the model range are unique, so the derivative within it is unambiguous even at an endpoint ⟦Appendix/Smooth/Setup · uniqueDiffOn_modelRange⟧; and the boundary is chart-independent, a point in the source of **any** chart being a boundary point exactly when its real coordinate lies on the frontier of the model range, by Mathlib's $C^1$ theorem ⟦Appendix/Smooth/Setup · mem_boundary_iff_chartCoord_mem_frontier⟧. **What this does to V.A:** the boundary compatibility that the topological theorem has to assume is a *theorem* for a $C^1$ one-manifold with a half-line model, with no side condition at all ⟦Appendix/Smooth/Setup · boundaryCompatible⟧, so the count of the first half applies to smooth one-manifolds unconditionally. Two normalized local models close the stage: every boundary point has a chart-derived coordinate onto $[0,\varepsilon)$, every interior point one onto $(-\varepsilon,\varepsilon)$ ⟦Appendix/Smooth/Setup · exists_boundaryModel⟧ ⟦Appendix/Smooth/Setup · exists_interiorModel⟧.

*Three things that looked dangerous were handled rather than avoided.* The compact-interval case stays live, and no statement of this half excludes it; charts at interior points are shrunk away from the model's own endpoints before $\varepsilon$ is chosen; and the sign of the identification with $\mathbb R$ is normalized twice, globally and again at an endpoint, the local sign mattering because it is what keeps the far endpoint out of a normalized chart. $C^1$ suffices throughout, and neither Hausdorffness nor compactness nor boundarylessness occurs.

### V.D and V.E Smooth arcs, the length element, and unit speed

*Smooth arcs (V.D).* A *smooth arc* is an arc of V.A whose coordinate is smooth as a map of manifolds into $\mathbb R$ and whose parametrization is smooth as a map of $\mathbb R$ into $M$, so that the whole apparatus of V.A is inherited ⟦Appendix/Smooth/SmoothArc · SmoothArc⟧. The interval of an arc is convex with nonempty interior, so derivatives within it are unambiguous at its endpoints ⟦Appendix/Smooth/SmoothArc · uniqueDiffOn_target⟧; the transition between two smooth arcs is smooth on the relatively open piece of the interval where it is defined, which is V.A's overlap ⟦Appendix/Smooth/SmoothArc · SmoothArc.contDiffOn_trans⟧ ⟦Appendix/Smooth/SmoothArc · transSource⟧; the two transition derivatives multiply to $1$, so **neither vanishes** ⟦Appendix/Smooth/SmoothArc · SmoothArc.derivWithin_trans_mul_derivWithin_trans⟧ ⟦Appendix/Smooth/SmoothArc · SmoothArc.derivWithin_trans_ne_zero⟧ — this is where Milnor's "the derivative is $\pm 1$" first appears, in a form that does not yet presuppose arc length; a smooth arc is an immersion, endpoints included ⟦Appendix/Smooth/SmoothArc · SmoothArc.derivWithin_ne_zero⟧; and every point lies on a smooth arc, with interval $[0,\varepsilon)$ at a boundary point and $(-\varepsilon,\varepsilon)$ elsewhere ⟦Appendix/Smooth/SmoothArc · exists_smoothArc_of_mem_boundary⟧ ⟦Appendix/Smooth/SmoothArc · exists_smoothArc_of_notMem_boundary⟧. The one-sided smoothness that looked like the technical heart of the stage cost nothing: smoothness on a set is already relative to that set, so at an endpoint it *is* the one-sided condition. The one real wrinkle was that a transition is defined only on a relatively open piece of the interval, so a derivative is computed there and then transported to the whole of it.

*The length element (V.E).* A density in dimension one, indexed not by charts but by *local real parameters* — a partial homeomorphism of an open subset of $M$ onto a subset of $\mathbb R$ with unique derivatives, smooth both ways ⟦Appendix/Smooth/LengthElement · RealChart⟧ — of which both a chart read in V.C's coordinate and a smooth arc are instances ⟦Appendix/Smooth/LengthElement · SmoothArc.toRealChart⟧, which is what lets a length element be evaluated along an arc with no intermediate layer. A *length element* assigns to each local parameter $c$ a positive smooth $\rho_c$ with
$$\rho_c(u) = \rho_\kappa(\tau(u))\,|\tau'(u)|$$
for the transition $\tau$ from $c$ to $\kappa$ ⟦Appendix/Smooth/LengthElement · LengthElement⟧. Its engine is the transition-derivative calculus on possibly half-open sets: the chain rule at an endpoint, the cocycle rule, non-vanishing, and smoothness one degree down ⟦Appendix/Smooth/LengthElement · transDeriv⟧ ⟦Appendix/Smooth/LengthElement · transDeriv_comp⟧ ⟦Appendix/Smooth/LengthElement · transDeriv_ne_zero⟧ ⟦Appendix/Smooth/LengthElement · contDiffOn_transDeriv⟧. **Existence** is a partition of unity, $\rho_c(u) = \sum_i \lambda_i(c^{-1}u)\,|\tau'_{c \to \kappa_i}(u)|$ with $\lambda$ subordinate to the chart sources and $\kappa_i$ the real coordinate of the chart at $i$ ⟦Appendix/Smooth/LengthElement · nonempty_lengthElement⟧, and it needs exactly four things: dimension one, smoothness of class $C^\infty$ (partitions of unity are built from smooth bumps, and a transition derivative loses a degree, so a $C^n$ manifold would give only a $C^{n-1}$ element), $M$ Hausdorff, and $M$ σ-compact, these last two being the hypotheses of Mathlib's subordinate partition of unity. **Those two are used nowhere else in the whole classification**, and all three shapes of V.C stay alive.

*Unit-speed arcs, Milnor's "by a straightforward change of variables".* Call an arc *unit-speed* when the length element read in its own parameter is identically $1$ ⟦Appendix/Smooth/ArcLength · UnitSpeed⟧. Then every point lies on a unit-speed arc sending it to $0$, with interval $[0,\varepsilon)$ at a boundary point and $(-\varepsilon,\varepsilon)$ elsewhere ⟦Appendix/Smooth/ArcLength · exists_reparam⟧ ⟦Appendix/Smooth/ArcLength · exists_unitSpeed⟧. The new parameter of the point at old parameter $u$ is $\sigma(u) = \int_0^u \rho$ ⟦Appendix/Smooth/ArcLength · arcLength⟧ ⟦Appendix/Smooth/ArcLength · arcParam⟧, and all the work is at the endpoint of a half-open interval, where Mathlib's two-sided inverse function rule says nothing at all. So the **one-sided rule** is proved rather than dodged: if $g$ inverts $f$ on a set, is continuous there, and $f$ has nonzero derivative *within* its own set at $g(v)$, then $g$ has derivative $1/f'$ within that set at $v$, both derivatives allowed to be one-sided ⟦Appendix/Smooth/ArcLength · hasDerivWithinAt_of_leftInvOn⟧; smoothness of the inverse then follows by bootstrapping on the order ⟦Appendix/Smooth/ArcLength · contDiffOn_arcParamInv⟧. Two devices made the endpoints painless: all the analysis happens on a *compact* interval inside the arc's interval, where the fundamental theorem of calculus holds at the endpoints and compactness gives continuity of the inverse for nothing ⟦Appendix/Smooth/ArcLength · continuousOn_leftInvOn_of_isCompact⟧; and the window is chosen in the *new* parameter, since arc length need not be symmetric about the base point.

### V.F Milnor's Appendix Lemma 1 in full, and the extension theorem

> **Lemma (V.F, Milnor's Appendix Lemma 1, p. 54).** Let $A$ and $A'$ be unit-speed smooth arcs for a common length element. Then on each component of the overlap the transition is $s \mapsto \pm s + k$, with a sign and a constant belonging to that component; the overlap has at most two components; and if it has two they reach opposite ends of $T_A$. ⟦Appendix/Smooth/Affine · milnor_appendix_lemma_one⟧

The affine half is one line from the cocycle rule. In a unit-speed parameter the density is $1$, so the rule reads $1 = 1 \cdot |\tau'(u)|$ and $|\tau'| = 1$ at every parameter of the overlap, endpoints of a half-open interval included ⟦Appendix/Smooth/Affine · abs_transDeriv_eq_one⟧. Being continuous and omitting $0$, $\tau'$ is *constantly* $+1$ or constantly $-1$ on each component ⟦Appendix/Smooth/Affine · exists_sign_transDeriv⟧ — if it took both values the intermediate value theorem would produce a parameter at which it vanished — and a function with constant derivative within an order-connected set is affine there ⟦Appendix/Smooth/Affine · exists_affine_trans⟧. The other two clauses are V.B, which uses no smoothness whatever. Unit speed survives reversal of the parameter, the transition being $s \mapsto -s$ ⟦Appendix/Smooth/Affine · UnitSpeed.neg⟧, and that is what lets the extension theorem drop a normalization by negating a coordinate.

> **Theorem (the extension theorem, V.F).** Let $A$ be a unit-speed arc from a boundary point $p$ with $A(p) = 0$ and interval $[0,c)$, let $A'$ be any unit-speed arc, and let $x \in U_{A'} \setminus U_A$ lie in the closure of $U_A$. Then there is a unit-speed smooth arc $\tilde A$ from $p$ whose domain is the **union** $U_A \cup U_{A'}$ and whose coordinate **equals** $A$ at every point of $U_A$. ⟦Appendix/Smooth/Affine · exists_extension_unitSpeed⟧ ⟦Appendix/Smooth/Affine · exists_extension_aux_unitSpeed⟧

*Where the expected route was wrong, and it governs everything after.* V.A's topological extension theorem **cannot be reused with smoothness added**. Its conclusion is an existential that forgets the witness's coordinate, and from the statement alone one recovers only that the transition from old to new is an increasing homeomorphism fixing $0$; it could be $s \mapsto s^2$. So the theorem is restated for smooth arcs, reusing the apparatus beneath it verbatim and transcribing the parts of its proof that carry over. About 75 lines of the original then *disappear*: both one-sided limit computations at the junction, and the trichotomy proofs of continuity there. They disappear because with unit-speed arcs the two branches are the same affine function on the *whole* overlap and not merely near the seam, so there is no junction to be continuous at. The strong form is not a bonus but forced: the transition being $s \mapsto \pm s + k$, and the normalization pinning down both the sign and the constant, the old parameter *is* the new parameter on the old domain. This is the sharp reason Milnor states his lemma for arc-length parametrizations and not for arbitrary charts.

*Hypotheses.* The affine half needs a length element and unit speed and nothing else: no dimension, no Hausdorffness, no compactness, no boundarylessness. Lemma 1 and the extension theorem add Hausdorffness, because V.B and V.A's overlap apparatus are stated for Hausdorff spaces, and the extension theorem inherits V.A's normalization, that the first arc starts at a boundary point with coordinate $0$.

### V.G Milnor's first case: a compact one-manifold with boundary is $[0,1]$

> **Theorem (V.G).** Let $M$ be a compact Hausdorff smooth one-manifold with a boundary point $p$. Then there are a unit-speed smooth arc $A$ and a length $\ell > 0$ with $A(p) = 0$, interval exactly $[0,\ell]$ and domain exactly **the connected component of $p$**, and the boundary inside that component is $\{p, A^{-1}(\ell)\}$ ⟦Appendix/Smooth/Compact · exists_unitSpeedArc_component⟧. If $M$ is moreover connected, the domain is all of $M$ ⟦Appendix/Smooth/Compact · exists_unitSpeedArc_of_preconnected⟧, the arc rescaled by $1/\ell$ is a **diffeomorphism $M \to [0,1]$** ⟦Appendix/Smooth/Compact · SmoothArc.diffeomorphIcc⟧ ⟦Appendix/Smooth/Compact · nonempty_diffeomorphIcc⟧, and the boundary of $M$ is exactly the two points $p$ and $A^{-1}(\ell)$ ⟦Appendix/Smooth/Compact · boundary_eq_pair⟧ ⟦Appendix/Smooth/Compact · ncard_boundary_eq_two⟧.

The last clause is **Milnor's own corollary**, and where V.A counts the boundary points modulo two it *identifies* them.

*The proof is Milnor's Step 2, run with unit-speed arcs* ⟦Appendix/Smooth/Compact · exists_closed_unitSpeedArc⟧. Cover $M$ by the domains of unit-speed arcs, one arc per point by V.E, and take a *finite* subcover. Start from a unit-speed arc at $p$ with interval $[0,\varepsilon)$, and induct on the number of members of the subcover not yet swallowed. If the interval attains its supremum we are done. Otherwise it is $[0,c)$, and the domain is not yet the whole component of $p$: the component is closed, hence compact, so if the domain were all of it then the interval, being its continuous image, would be compact and would contain $c$. Being an open proper subset of that component and containing $p$, the domain then has a point of its closure outside itself; the subcover arc containing that point extends the arc by V.F, and it does so swallowing at least one more member, since its own domain was not contained in the old one and is contained in the new. When the interval closes up to $[0,\ell]$ the domain is compact, hence closed, hence — being also open, connected and nonempty — the whole component; and the boundary condition of an arc then names its two ends. The diffeomorphism is the arc itself, rescaled by $1/\ell$ ⟦Appendix/Smooth/Compact · SmoothArc.equivIcc⟧.

*Three things worth recording.* **Compactness is used three times, and σ-compactness would not do for two of them:** to extract a *finite* subcover, which is what makes the induction terminate, and to know that the component of $p$ is compact, which is what forbids a proper open subarc from exhausting it. Only the third use, feeding the length element of V.E, is σ-compactness in disguise, which is why the compact cases need no countability hypothesis of their own. **Connectedness is needed nowhere in the exhaustion:** the honest conclusion is about the component of $p$, which is the form V.J wants and which makes the disconnected case there cheap. And the conversion of the rescaled arc into a diffeomorphism, through Mathlib's two bridges for $[0,1]$, cost about twenty lines — the cheapest part of the stage rather than the dearest.

*Deviation.* V.A's finite-cover induction is restated rather than reused, for three independent reasons. Its conclusion is a topological arc, and the induction feeds its own output back in, so the object it carries must be the object the next step consumes. Its extension step is V.A's, which does not record that the coordinate is preserved, so V.F's is the theorem the loop calls. And its hypothesis of boundary compatibility demands a homeomorphism of the model space with a half-line, which does not exist when the model range is a compact interval — a shape V.C deliberately admits. Nothing in V.A's file is edited.

### V.H Milnor's second case: a compact boundaryless one-manifold is the circle

> **Theorem (V.H).** Let $M$ be a nonempty compact Hausdorff connected smooth one-manifold with **empty boundary**. Then there are a length element, a period $T > 0$ and a map $\gamma : \mathbb R \to M$ which is an arc-length parametrization near every time, is $T$-periodic and onto, is injective on $[0,T)$, has $T$ as its *least* period, and satisfies $\gamma(s) = \gamma(t)$ exactly when $s - t$ is an integer multiple of $T$ ⟦Appendix/Smooth/Circle · exists_periodic_parametrisation⟧. In words, such an $M$ **is a closed geodesic of length $T$**, which is Milnor's Step 5. And $M$ is diffeomorphic to the circle ⟦Appendix/Smooth/Circle · nonempty_diffeomorphCircle⟧.

*Where the whole programme had to be corrected.* **The exhaustion of V.G does not exist here.** Every arc of a manifold with empty boundary has an *open* interval ⟦Appendix/Smooth/Circle · Arc.isOpen_target_of_boundary_eq_empty⟧ ⟦Appendix/Smooth/Circle · SmoothArc.isOpen_target⟧, whereas V.F's extension theorem needs the first arc's interval to be half-open, that is, to start at a boundary point. So V.G's induction has no boundaryless analogue in the shape one expects, and the obstruction is not technical: there is nothing to start the induction with.

*The replacement is to drop injectivity.* A *unit-speed curve* on a set $U$ of times is a map $\gamma : \mathbb R \to M$ which near every time of $U$ agrees with the arc-length parametrization $s \mapsto A^{-1}(s - k)$ of a unit-speed arc ⟦Appendix/Smooth/Circle · IsUnitSpeedCurveOn⟧. Unlike an arc it is not injective — which is the whole point, since the curve that wraps round a circle is not — and unlike an arc it is a genuine function on the line, so two of them can be compared time by time. Every unit-speed arc of a boundaryless manifold is one ⟦Appendix/Smooth/Circle · isUnitSpeedCurveOn_arc⟧.

> **The propagation lemma.** Two unit-speed curves on the same *interval* of times which agree near one time agree at every time. ⟦Appendix/Smooth/Circle · eqOn_of_eventuallyEq⟧

This is the engine of the stage, and it replaces the uniqueness theorem for integral curves, which Mathlib proves only for manifolds without boundary and only for genuine flows. Its proof is a connectedness argument run **in the parameter of one arc rather than in the time**, and the reason is exactly the two-component picture of V.B: the set of times at which the two curves agree *on a neighbourhood* is open but not obviously closed, because an overlap can have two components. Pushed into a single component — a hull — the transition is affine by V.F and is pinned down by two coincidences ⟦Appendix/Smooth/Circle · trans_eq_add_of_two_points⟧, so in the arc's parameter the set of agreement is closed, and the set of parameters having a whole neighbourhood of agreement is closed there too; being open, nonempty and closed in an interval, it is everything. Hausdorffness enters here, for uniqueness of limits, and nothing else does: no compactness, no dimension, no boundarylessness, no connectedness of $M$. With curves, continuation needs no gluing of injective arcs and no two-component bookkeeping at all.

*The maximal curve.* Say that $x$ is *reached* at time $t$ from a fixed unit-speed arc $A_0$ when some unit-speed curve that agrees with $A_0$ near time $0$ sends $t$ to $x$ ⟦Appendix/Smooth/Circle · Reach⟧. Propagation makes that single-valued ⟦Appendix/Smooth/Circle · Reach.unique⟧ ⟦Appendix/Smooth/Circle · subset_dom_and_eqOn⟧, so a function can be extracted from it: the set $\mathrm{Dom}$ of reached times ⟦Appendix/Smooth/Circle · Dom⟧ and the curve on it ⟦Appendix/Smooth/Circle · globalCurve⟧ ⟦Appendix/Smooth/Circle · isUnitSpeedCurveOn_globalCurve⟧. That set is an open interval containing $0$ ⟦Appendix/Smooth/Circle · isOpen_dom⟧ ⟦Appendix/Smooth/Circle · ordConnected_dom⟧ ⟦Appendix/Smooth/Circle · zero_mem_dom⟧, and none of this uses compactness. Compactness is what makes it the whole line: as the time approaches an end of the interval the curve accumulates somewhere, a unit-speed arc about the accumulation point receives it, and a five-line gluing continues it past the end ⟦Appendix/Smooth/Circle · not_bddAbove_dom⟧ ⟦Appendix/Smooth/Circle · dom_eq_univ⟧.

*The period, and Milnor's matching directions.* Compactness again: as the time tends to $+\infty$ the curve accumulates at some $q$, and the propagation lemma — not a germ argument — shows that it passes exactly *through* $q$, at two distinct times, the two visits being far enough apart in the accumulation for the times they produce to differ ⟦Appendix/Smooth/Circle · exists_cluster⟧ ⟦Appendix/Smooth/Circle · IsUnitSpeedCurveOn.exists_shift⟧. Two times with the same value then give a period ⟦Appendix/Smooth/Circle · exists_period⟧, and that step is the geometric heart: it is the one part of Milnor's Step 5 with no counterpart in V.A's file ⟦Appendix/Smooth/Circle · periodic_of_eq⟧. Read in a unit-speed arc $B$ centred at the common value, the curve has slope $\sigma_1 = \pm 1$ near $t_1$ and $\sigma_2 = \pm 1$ near $t_2$ ⟦Appendix/Smooth/Circle · exists_unitSpeed_centred⟧ ⟦Appendix/Smooth/Circle · IsUnitSpeedCurveOn.exists_sign⟧. If the two signs agree then $\gamma$ and $\gamma(\cdot + (t_2 - t_1))$ agree near $t_1$, hence everywhere by propagation, and $t_2 - t_1$ is a period. If they disagree the curve would have to *reflect*: $\gamma$ and $\gamma(t_1 + t_2 - \cdot)$ would agree near $t_1$, hence everywhere, so that $\gamma(m + w) = \gamma(m - w)$ about the midpoint $m$ — which contradicts the injectivity of a unit-speed curve near a time ⟦Appendix/Smooth/Circle · IsUnitSpeedCurveOn.exists_injOn⟧. **So the two directions must match**, and that is Milnor's observation, proved by excluding the reflection.

*The minimal period.* The set of periods is a subgroup of the line, closed because the curve is continuous, and *discrete*, because a unit-speed curve is injective near every time and so no period can be smaller than the radius of an interval of injectivity. The positive periods are therefore the elements of a closed set bounded below, whose infimum belongs to it, and every period is an integer multiple of that least one ⟦Appendix/Smooth/Circle · exists_minimal_period⟧. Surjectivity finishes the geometry: the image of the curve is the image of $[0,T]$, hence compact, hence closed, and it is open because the curve is locally a parametrization, so it is a nonempty clopen subset of a preconnected $M$ ⟦Appendix/Smooth/Circle · IsUnitSpeedCurveOn.isOpen_range⟧ ⟦Appendix/Smooth/Circle · surjective_of_periodic⟧.

*The descent, and why it cannot go through a quotient.* Mathlib has no quotient-manifold theory, so $\mathbb R / T\mathbb Z$ is not available as a smooth manifold and the descent goes through *local inverses of the exponential*. The map $t \mapsto \exp(2\pi i t/T)$ is smooth, is onto by an explicit section built from the principal argument, and identifies exactly the times differing by a multiple of $T$ ⟦Appendix/Smooth/Circle · circleParam⟧ ⟦Appendix/Smooth/Circle · contMDiff_circleParam⟧ ⟦Appendix/Smooth/Circle · circleSection⟧ ⟦Appendix/Smooth/Circle · circleParam_eq_iff⟧; and it is a local diffeomorphism, obtained **without computing a chart of the circle** — the two coordinate functions $z \mapsto \operatorname{re} z$ and $z \mapsto \operatorname{im} z$ pull back to $\cos$ and $\sin$, whose derivatives cannot both vanish, and rescaling whichever does not gives a smooth left inverse of the derivative ⟦Appendix/Smooth/Circle · isLocalDiffeomorph_circleParam⟧. Since $\gamma$ and the exponential identify *the same* pairs of times, the descended map is a bijection, and it is a local diffeomorphism because near each point it agrees with $\gamma$ composed with a local inverse of the exponential ⟦Appendix/Smooth/Circle · IsUnitSpeedCurveOn.isLocalDiffeomorphAt⟧. One friction is worth recording: Mathlib's tangent spaces carry no norm, so "a nonzero linear map between one-dimensional spaces is invertible" had to be stated for topological modules with the inverse supplied as data, which that left inverse provides ⟦Appendix/Smooth/Circle · isInvertible_of_finrank_one⟧.

*Hypotheses.* Hausdorff three times: the length element, V.F's apparatus, and — essentially — the propagation lemma. Compact twice, and **σ-compactness would not do for either**: to make the curve accumulate as its time approaches the end of its interval, which is what lets it be continued, and to make it accumulate at $+\infty$, which is what forces it to return. Preconnected only for surjectivity, and nonempty only to choose a base point. No second countability, no orientability. And **V.B turns out not to be used here**: what this stage needs from V.A's file is the relative openness of hulls and V.F's affine half, not the counting of components. V.B remains the right statement of Milnor's lemma; the expectation that V.H would depend on it was wrong.

### V.I Milnor's third and fourth cases: $[0,\infty)$ and $\mathbb R$

> **Theorem (V.I).** Let $M$ be a connected Hausdorff σ-compact smooth one-manifold which is **not compact**. If its boundary is empty, $M$ is diffeomorphic to $\mathbb R$ ⟦Appendix/Smooth/NonCompact · nonempty_diffeomorphReal⟧. If it has a boundary point $p$, then $M$ is diffeomorphic to $[0,\infty)$ and $p$ is its **only** boundary point ⟦Appendix/Smooth/NonCompact · nonempty_diffeomorphIci⟧ ⟦Appendix/Smooth/NonCompact · boundary_eq_singleton⟧.

*One fact organises the whole stage:* **no value of a unit-speed curve is a boundary point** ⟦Appendix/Smooth/NonCompact · IsUnitSpeedCurveOn.notMem_boundary⟧. It is why the boundary point has to be adjoined by hand, why the curve stops exactly at it, and why a repeated value is impossible.

*The boundaryless case.* Start from a unit-speed arc centred at an arbitrary point and take the maximal curve of V.H, whose construction uses no compactness at all. Its image is **open**, because the curve is locally a parametrization ⟦Appendix/Smooth/NonCompact · IsUnitSpeedCurveOn.isOpen_image⟧, and **closed**, because every point of the closure which is not a boundary point already lies in it — and here emptiness of the boundary makes every such point eligible ⟦Appendix/Smooth/NonCompact · mem_image_dom_of_mem_closure⟧. Being a nonempty clopen subset of a preconnected space it is everything. Injectivity is where non-compactness enters, and it enters only there: a repeated value makes the curve satisfy a shift identity ⟦Appendix/Smooth/NonCompact · eqOn_add_of_eq⟧, and then the image of one compact interval of times is both compact and open, hence all of $M$, hence $M$ compact ⟦Appendix/Smooth/NonCompact · isCompact_isOpen_image_Icc_of_eq⟧. What comes out is a parametrization of $M$ by an *open interval* of times ⟦Appendix/Smooth/NonCompact · exists_parametrisation_of_boundary_eq_empty⟧ — the honest form, since without compactness the interval need not be the whole line, as $(0,1)$ shows — and every nonempty open interval of the line is diffeomorphic to the line ⟦Appendix/Smooth/NonCompact · exists_param_of_isOpen_ordConnected⟧.

*The case with a boundary point.* The arc issuing from $p$ has interval $[0,\varepsilon_0)$, so it is not a legitimate starting arc for a curve. Restricting it to $(0,\varepsilon_0)$ and recentring gives one that is ⟦Appendix/Smooth/NonCompact · SmoothArc.shrink⟧ ⟦Appendix/Smooth/NonCompact · SmoothArc.unitSpeed_shrink⟧, and the maximal curve from it has $-\varepsilon_0/2$ as the *unattained* left end of its interval of times, because it tends to $p$ there ⟦Appendix/Smooth/NonCompact · tendsto_left_halfline⟧ and cannot take that value ⟦Appendix/Smooth/NonCompact · left_notMem_dom⟧. Shift the time and adjoin the single time $0$ with value $p$: the result is a ray, a parametrization of $M$ by $[0,\infty)$ or by some $[0,b)$ ⟦Appendix/Smooth/NonCompact · shape_of_halfline⟧ ⟦Appendix/Smooth/NonCompact · exists_ray_of_mem_boundary⟧, and each of those is diffeomorphic to $[0,\infty)$ ⟦Appendix/Smooth/NonCompact · exists_param_halfline⟧. Injectivity needs no compactness here: a repeated value would make the image everything, and the image cannot contain $p$ ⟦Appendix/Smooth/NonCompact · injOn_dom_halfline⟧. **Surjectivity is the long step**, and it is the only place non-compactness is used in this case. A *second* boundary point in the closure has to be excluded, and reading the curve in an arc issuing from such a point shows that the curve arrives exactly there at an end of its interval of times; if that is the far end then $M$ is covered by three compact pieces and so is compact, which is V.G ⟦Appendix/Smooth/NonCompact · insert_image_dom_eq_univ⟧.

*No inverse function theorem is used anywhere in this stage*, and in particular none at a boundary endpoint, where there would be none to use. The four shapes of open interval and the two of half-line are reparametrized by explicit elementary formulas — built from the exponential, the logistic curve and a Möbius map — with their logarithmic or rational inverses written down beside them, so both halves of every diffeomorphism are exhibited ⟦Appendix/Smooth/NonCompact · exists_param_of_isOpen_ordConnected⟧ ⟦Appendix/Smooth/NonCompact · exists_param_halfline⟧. The inverse coordinate of the curve itself, the map $M \to \mathbb R$ that reads off a point's time, is likewise assembled from the local parametrizations rather than obtained by inverting anything ⟦Appendix/Smooth/NonCompact · exists_inverse_coord⟧ ⟦Appendix/Smooth/NonCompact · exists_inverse_coord'⟧.

*What had to be built.* $[0,\infty)$ as a manifold with boundary. Mathlib has $[a,b]$ only, and there through two charts; here a single chart is a homeomorphism onto the whole model half-space ⟦Appendix/Smooth/NonCompact · iciHomeomorph⟧ ⟦Appendix/Smooth/NonCompact · instIciChartedSpace⟧ ⟦Appendix/Smooth/NonCompact · instIciIsManifold⟧, with the two bridges — inclusion into $\mathbb R$, projection from it — that make a map into or out of it smooth exactly when its real expression is ⟦Appendix/Smooth/NonCompact · contMDiff_subtypeVal_Ici⟧ ⟦Appendix/Smooth/NonCompact · contMDiffOn_iciProj⟧.

*Where σ-compactness is.* **It is used once and only once, to build the length element of V.E.** Everything after that — the arcs, the curves, the propagation lemma, the maximality of the interval of reached times, the continuation step and both classifications — uses only Hausdorffness, connectedness and the failure of compactness. And that one use is exactly where the hypothesis is *necessary*; see the end of V.J. Milnor gets it free by sitting in Euclidean space, and uses it silently, the metric he restricts to $M$ being a Riemannian metric.

*Two corrections to the expected route, both instructive.* A repeated value gives a *period* only once the curve is known to run on the whole line, which here it need not, so injectivity is proved instead from the compact-and-open image above. And a unit-speed curve cannot take a boundary value at all, so it cannot run on a closed half-line of times; the boundary point has to be adjoined by hand, and showing that no *second* boundary point appears in the closure is the long step rather than a formality.

### V.J The theorem, its six exclusions, and the count again

The four cases are assembled by splitting on compactness and on emptiness of the boundary ⟦Appendix/Smooth/Main · nonempty_diffeomorph_cases⟧ ⟦Appendix/Smooth/Main · nonempty_diffeomorph_or⟧, each model carrying its own model with corners. Nothing is assumed about the boundary, about orientability or about second countability, and no compatibility hypothesis is assumed anywhere, V.C having proved chart-independence of the boundary.

*Exclusivity* is a statement about the four models alone, and all six exclusions are proved ⟦Appendix/Smooth/Main · models_pairwise_not_diffeomorph⟧. Two invariants suffice. **Compactness** separates the circle and $[0,1]$ from $[0,\infty)$ and $\mathbb R$, which settles four of the six, a diffeomorphism being in particular a homeomorphism ⟦Appendix/Smooth/Main · compactSpace_of_diffeomorph⟧ ⟦Appendix/Smooth/Main · not_compactSpace_Ici⟧. **The number of boundary points** settles the remaining one in each compactness class: a diffeomorphism carries boundary onto boundary — a theorem of Mathlib, here wanted for two *different* models with corners at once — so that number is a diffeomorphism invariant ⟦Appendix/Smooth/Main · ncard_boundary_eq_of_diffeomorph⟧, and its values on the four models are $0$, $2$, $1$ and $0$ ⟦Appendix/Smooth/Main · ncard_boundary_Icc⟧ ⟦Appendix/Smooth/Main · ncard_boundary_Ici⟧ ⟦Appendix/Smooth/Main · isEmpty_diffeomorph_Icc_Ici⟧.

*The slice form, and Milnor's corollary a second time.* In Chapter 2's language, let $X$ be a compact half-slice submanifold with boundary $B$ of a Hausdorff ambient manifold, over a one-point $Z$ — that is, a compact one-manifold with boundary in the sense of V.A′. Then every connected component of $X$ is diffeomorphic to the circle or to $[0,1]$ ⟦Appendix/Smooth/Main · IsHalfSliceSubmanifold.component_diffeomorph⟧; the components carrying a boundary point are exactly those of the second kind ⟦Appendix/Smooth/Main · IsHalfSliceSubmanifold.nonempty_diffeomorphIcc_component_iff⟧ ⟦Appendix/Smooth/Main · IsHalfSliceSubmanifold.nonempty_diffeomorphCircle_component_iff⟧; each of those meets $B$ in exactly two points ⟦Appendix/Smooth/Main · IsHalfSliceSubmanifold.ncard_boundary_inter_component⟧; every boundary point has exactly one partner ⟦Appendix/Smooth/Main · IsHalfSliceSubmanifold.exists_boundary_partner⟧; and $B$ is finite of even cardinality ⟦Appendix/Smooth/Main · IsHalfSliceSubmanifold.even_ncard_boundary_of_classification⟧. That last is V.A′ again, and the point of the stage is that it now follows **from the classification**, as in the book: the pairing is "the other end of my own component", and it is realised by the two ends of a single arc-length parametrization rather than by an abstract parity argument ⟦Appendix/Smooth/Main · boundary_inter_component_eq_pair⟧ ⟦Appendix/Smooth/Main · even_ncard_boundary_of_compact⟧. V.A′ is not cited and is left untouched; what is reused from V.A's file is only the pure combinatorics, that a fixed-point-free involution of a finite set has even cardinality ⟦Appendix/OneManifold · even_ncard_of_involution⟧.

*Three bridges had to be built, and the project will want all three.* **The connected components of a one-manifold are open** ⟦Appendix/Smooth/Main · isOpen_connectedComponent_of_oneManifold⟧, hence are manifolds in their own right ⟦Appendix/Smooth/Main · componentOpens⟧ ⟦Appendix/Smooth/Main · boundary_componentOpens⟧, which is what lets a theorem needing connectedness be applied to a *disconnected* manifold; it needs nothing but dimension one and smoothness, since V.D gives every point a neighbourhood which is the domain of an arc, and the domain of an arc is preconnected. **The boundary of the model half-line is a single point** ⟦Appendix/Smooth/Main · boundary_Ici⟧, which Mathlib could not supply, having no half-line manifold. And **the boundary count for a possibly disconnected compact one-manifold**, whose *finiteness* is the harder half and could not reuse V.A, because V.A wants a compatibility hypothesis available only when the model range is a half-line ⟦Appendix/Smooth/Main · finite_boundary_of_compact⟧.

*σ-compactness is necessary, and the long line says why.* The classification is **false** without a countability hypothesis. The long line — two copies of the closed long ray $\omega_1 \times [0,1)$ with the lexicographic order topology, glued along their least elements — is a connected Hausdorff smooth one-manifold without boundary which is neither compact nor σ-compact, and it is not even homeomorphic, let alone diffeomorphic, to any of the four models, since it is not second countable and all four are. So the two non-compact cases must assume σ-compactness, and they do. In the compact cases nothing extra is needed: compact plus Hausdorff plus a finite-dimensional model gives second countability by Mathlib's own theorem. And the failure is located exactly: it is **the length element** that does not exist, since a manifold carrying a Riemannian metric is metrizable, so the long line carries none, and Milnor's arc-length reparametrization has nothing to start from. Milnor's manifolds sit in $\mathbb R^k$, hence are second countable, and he uses this silently.

*Size.* 9,276 lines for the nine stages: 463 for V.B, and 8,813 in the nine files of the smooth Appendix — 820 for V.C, 630 for V.D, 1,315 for V.E, 929 for V.F, 421 for V.G, 1,712 for V.H, 2,202 for V.I and 784 for V.J. With V.A and V.A′ the Appendix is 11,054 lines in twelve files. Those 9,276 lines are the largest single addition the project has had, exceeding the mod 2 remark of Part VII, which held the record before; and the two largest files are the two whose route had to be invented rather than transcribed, V.H and V.I. A design pass estimated the whole at about 4,000 lines in nine stages; the nine stage boundaries held, which no previous estimate in this project managed, and the lines came to more than twice the estimate.

### What the formalization taught us

- *No smoothness, for the count.* It holds for compact Hausdorff topological 1-manifolds; slopes $\pm 1$ become strict monotonicity ⟦Appendix/OneManifold · strictMonoOn_or_strictAntiOn_of_ordConnected⟧, and in V.A′ the smooth structure is carried but unused ⟦Appendix/HalfSpace · IsHalfSliceSubmanifold.even_ncard_boundary⟧. The classification, by contrast, cannot do without it: a topological one-manifold has no arc length.
- *The boundary is an input.* That every chart sends exactly $B$ to $0$ is assumed, though the proof uses it only for the chosen charts ⟦Appendix/OneManifold · BoundaryCompatible⟧; in Chapter 2 it holds by construction ⟦Appendix/HalfSpace · IsHalfSliceSubmanifold.boundaryCompatible⟧. The topological fact that would make it automatic (a homeomorphism between open subsets of the half-line preserves the point $0$) is never proved; in the *smooth* setting the hypothesis is now discharged instead, by the chart-independence of the boundary for a $C^1$ manifold ⟦Appendix/Smooth/Setup · boundaryCompatible⟧.
- *Hausdorff, twice:* to identify two limits in the end lemma ⟦Appendix/OneManifold · end_lemma⟧, and to know that the compact domain of a closed arc is closed ⟦Appendix/OneManifold · IsFrom.source_eq_of_mem⟧. In the doubled-endpoint example both fail: the arc from $0$ to one copy of $1$ is compact but not closed, and its points converge to both copies.
- *Compactness, three times:* for the finiteness of $B$ ⟦Appendix/OneManifold · finite_boundary⟧, for the finite cover by chart arcs, and to see that an arc with interval $[0,c)$ cannot fill a component ⟦Appendix/OneManifold · exists_closed_arc⟧.
- *No circle, no maximality, in the first half.* Only arcs from boundary points are extended, so overlaps are intervals ⟦Appendix/OneManifold · overlap_ordConnected⟧, and a finite induction replaces the maximal parametrization ⟦Appendix/OneManifold · exists_closed_arc⟧; the price is that the count, and not the classification, is what comes out. In the second half the circle case is counted instead of excluded ⟦Appendix/TwoComponents · encard_hulls_le_two⟧, and the normalization that excluded it turns out to have been doing nothing essential.
- *A Riemannian metric is the only general theory the classification needs*, and in dimension one it is a positive smooth density on local real parameters. Mathlib has no metric-existence theorem, so it was built; smooth bumps are why it is $C^\infty$ and not merely $C^1$ ⟦Appendix/Smooth/LengthElement · nonempty_lengthElement⟧.
- *Arc length is not a convenience.* Monotone transitions suffice for the count, but an extension theorem stated with them forgets the witness's coordinate, and then a chain of extensions says nothing. Unit speed makes the transition $s \mapsto s$, so the extended arc genuinely *extends* the old one ⟦Appendix/Smooth/Affine · exists_extension_unitSpeed⟧. That is why Milnor's lemma is about arc-length parametrizations and not about charts.
- *The exhaustion does not exist without boundary.* Every arc of a boundaryless manifold has an open interval, and the extension theorem needs a half-open one ⟦Appendix/Smooth/Circle · Arc.isOpen_target_of_boundary_eq_empty⟧. Dropping injectivity repairs it: unit-speed *curves*, made unique by a propagation lemma proved in the parameter of an arc rather than in the time, because the overlap can have two components ⟦Appendix/Smooth/Circle · eqOn_of_eventuallyEq⟧.
- *σ-compactness enters once*, to build the length element, and there it is necessary: the long line carries no Riemannian metric, so arc length has nothing to start from, and the long line is a connected smooth one-manifold which is none of the four models ⟦Appendix/Smooth/NonCompact · nonempty_diffeomorphReal⟧.
- *Two invariants separate the four models*, compactness and the number of boundary points, and the second needs a diffeomorphism to carry boundary onto boundary across two *different* models with corners ⟦Appendix/Smooth/Main · ncard_boundary_eq_of_diffeomorph⟧ ⟦Appendix/Smooth/Main · models_pairwise_not_diffeomorph⟧.
- *Components of a one-manifold are open*, hence manifolds, which is the whole bridge from a theorem about connected manifolds to a statement about a disconnected one ⟦Appendix/Smooth/Main · isOpen_connectedComponent_of_oneManifold⟧.
- *The seam.* Gluing arcs with a merely monotone transition is the longest proof of the first half; continuity at the seam comes down to two monotone limits ⟦Appendix/OneManifold · exists_extension_aux⟧. With unit speed there is no seam, and those seventy-five lines simply vanish ⟦Appendix/Smooth/Affine · exists_extension_aux_unitSpeed⟧.
- *Parity by involution:* the product of $-1$ over $B$, paired off by "the other end of my component" ⟦Appendix/OneManifold · exists_partner⟧ ⟦Appendix/OneManifold · even_ncard_of_involution⟧. Proved twice with the same combinatorics and two different pairings: an abstract one in V.A, and in V.J the two ends of one arc-length parametrization ⟦Appendix/Smooth/Main · IsHalfSliceSubmanifold.exists_boundary_partner⟧.
- *The arcs are reused.* Chapter 5 needs the pairing by arcs, not only the parity ⟦Chapter5/LemmaOne · lemmaOne_ambient'⟧. And the classification is reused too, outside the book's own dependencies: Part VII takes from it that a connected one-manifold is orientable ⟦Chapter7/OneManifoldOrientable · isOrientable_of_finrank_eq_one⟧.
