# Appendix. Why a piece of string has zero or two ends: classifying 1-manifolds

*Milnor, "Topology from the Differentiable Viewpoint", Appendix, rewritten for a first-year student.
Every proof is complete. This is the one result quoted without proof in Chapters 2, 4, 5 and 6; it
is proved here, and with it the whole book is closed.*

---

## 0. The fact that carried the book

A piece of string, however it is bent or tangled, is either a closed loop or has exactly two ends.
Never one, never three. Four times in this book that was the whole point:

* Brouwer's fixed point theorem (Chapter 2): the curve $f^{-1}(y)$ would have had one end.
* The homotopy lemma (Chapter 4): solutions appear and disappear in pairs because the arcs of
  $F^{-1}(y)$ have two ends.
* The degree (Chapter 5): the two ends of an arc carry opposite signs.
* Poincaré–Hopf (Chapter 6), through the degree.

Here is the theorem, with its proof.

**Theorem.** Every smooth connected 1-dimensional manifold, with or without boundary, is
diffeomorphic to the circle $S^1$ or to an interval of real numbers (open, closed, or half-open;
bounded or not). In particular a *compact* connected 1-manifold is diffeomorphic to $S^1$ or to
$[0,1]$, and a compact 1-manifold with boundary has an even number of boundary points.

The last sentence follows from the rest: a compact manifold has finitely many components (the
components are open, so they form an open cover with no proper subcover), each is a circle (no
boundary points) or a closed interval (two), and any interval is diffeomorphic to one of $[0,1]$,
$[0,1)$, $(0,1)$ (bounded ones by an affine map, unbounded ones by $t \mapsto \tanh t$ or its
restrictions), of which only $[0,1]$ is compact.

---

## 1. Parametrization by arc length

Let $M \subseteq \mathbb R^k$ be a 1-manifold, and $I \subseteq \mathbb R$ an interval.

**Definition.** A map $f : I \to M$ is a *parametrization by arc length* if it is a diffeomorphism
onto an open subset of $M$ and its velocity $df_s(1) \in TM_{f(s)} \subseteq \mathbb R^k$ has
Euclidean length $1$ for every $s \in I$. (If $I$ has an endpoint, $f$ sends it to a boundary
point of $M$, since $f(I)$ is open in $M$.)

**Lemma 1.1.** Every point of $M$ lies in the image of some parametrization by arc length.

*Proof.* Take a local parametrization $h : J \to M$ around the point, $J$ an interval (open, or
half-open at a boundary point). Since $h$ is a diffeomorphism onto its image, $h'(u) \ne 0$ for all
$u$ (a diffeomorphism has invertible derivative). Fix $u_0 \in J$ and put $\sigma(u) := \int_{u_0}^u
\|h'(t)\|\,dt$. Then $\sigma$ is smooth with $\sigma' = \|h'\| > 0$, so it is a diffeomorphism of
$J$ onto an interval $I$, and $f := h \circ \sigma^{-1} : I \to M$ is a diffeomorphism onto $h(J)$
with $\|f'(s)\| = \|h'(u)\|/\sigma'(u) = 1$. $\square$

---

## 2. Two parametrizations overlap in at most two pieces

**Lemma 2.1 (Milnor's Lemma).** Let $f : I \to M$ and $g : J \to M$ be parametrizations by arc
length. Then $f(I) \cap g(J)$ has at most two connected components. If it has one component, $f$
extends to a parametrization by arc length of $f(I) \cup g(J)$. If it has two, $M$ is diffeomorphic
to $S^1$.

*Proof.* Consider the *graph*
$$\Gamma := \{(s, t) \in I \times J : f(s) = g(t)\}.$$

*Step 1: $\Gamma$ is a closed set made of line segments of slope $\pm 1$.* Closed: $f$ and $g$ are
continuous. Now let $(s_0, t_0) \in \Gamma$. The set $f^{-1}(g(J))$ is open in $I$ (as $g(J)$ is
open in $M$), and on it $\tau := g^{-1} \circ f$ is defined and smooth, with $g(\tau(s)) = f(s)$.
Differentiating, $g'(\tau(s))\,\tau'(s) = f'(s)$; both $g'$ and $f'$ are unit vectors, so
$|\tau'(s)| = 1$, and $\tau'$, being continuous with values $\pm 1$, is constant on each component
of $f^{-1}(g(J))$. Hence on the component containing $s_0$, $\tau(s) = \pm(s - s_0) + t_0$: near
$(s_0, t_0)$, the set $\Gamma$ is the graph of $\tau$, a line segment of slope $\pm 1$ through
$(s_0, t_0)$. Symmetrically (using $f^{-1} \circ g$), $\Gamma$ near $(s_0, t_0)$ is also a graph
over the $t$-axis. So each component of $\Gamma$ is a segment of slope $\pm 1$, open in the sense
that it is the graph of $\tau$ over a component of the open set $f^{-1}(g(J))$.

*Step 2: the segments run from edge to edge of the rectangle $I \times J$.* Let $L$ be a component
of $\Gamma$, the graph of $\tau$ over an open subinterval $(a, b) \subseteq I$ (or a half-open one
if it reaches an endpoint of $I$). Suppose $b$ is an interior point of $I$. As $s \uparrow b$,
$\tau(s) = \pm s + \text{const}$ converges to some $t_1$; if $t_1$ were an interior point of $J$
then $g(t_1) = \lim g(\tau(s)) = \lim f(s) = f(b)$, so $(b, t_1) \in \Gamma$, and by Step 1 $\Gamma$
near $(b, t_1)$ is a segment through it, which would extend $L$ past $b$, contradicting that $(a,b)$
is a whole component of $f^{-1}(g(J))$. So either $b$ is an endpoint of $I$ or $t_1$ is an endpoint
(or limit) of $J$: each segment of $\Gamma$ extends until it hits the boundary of the rectangle at
both ends.

*Step 3: at most one segment ends on each edge, so at most two components.* Suppose two segments
$L_1, L_2$ both reach the edge $s = b$ (the right edge of $I \times J$, with $b$ an endpoint of $I$
or $b = \sup I$). Their $t$-limits $t_1 \ne t_2$ as $s \to b$ would, if $b \in I$, give
$g(t_1) = f(b) = g(t_2)$ with $t_1, t_2 \in J$, contradicting injectivity of $g$; and if $t_1, t_2$
are endpoints of $J$ with $b \notin I$, then $f(s) \to g(t_1)$ and $f(s) \to g(t_2)$ as $s \to b$
along the two segments, so $g(t_1) = g(t_2)$ again. The same for the other three edges, using
injectivity of $f$ for the edges $t = \text{const}$. Since each segment has two ends on distinct
edges (a segment of slope $\pm 1$ cannot have both ends on the same edge), and there are four edges,
there are at most two segments. Moreover, if there are two, they have the same slope: two segments
of opposite slopes inside a rectangle, each running edge to edge, would cross, but $\Gamma$ is a
disjoint union of its components.

*Step 4: one component.* If $\Gamma$ is a single segment, $\tau(s) = \pm s + c$ on its domain, and
this formula defines an affine bijection $L : \mathbb R \to \mathbb R$ extending $\tau$. Define
$$F : I \cup L^{-1}(J) \to f(I) \cup g(J), \qquad F := f \text{ on } I, \quad F := g \circ L
\text{ on } L^{-1}(J).$$
The domain is a union of two intervals that overlap (in $f^{-1}(g(J))$, where $F$ is well defined
because $g \circ L = g \circ \tau = f$ there), hence an interval. $F$ is smooth, has unit speed, is
injective (if $F(s) = F(s')$ with $s \in I$, $s' \in L^{-1}(J)$, then $f(s) = g(L(s'))$ so $s \in
f^{-1}(g(J))$ and $L(s) = \tau(s) = L(s')$, whence $s = s'$), and is a local diffeomorphism onto
the open set $f(I) \cup g(J)$; an injective local diffeomorphism is a diffeomorphism onto its image.
So $F$ is a parametrization by arc length extending $f$ over $f(I) \cup g(J)$.

*Step 5: two components.* Say both segments have slope $+1$ (if $-1$, replace $g$ by
$t \mapsto g(-t)$, which is again a parametrization by arc length). Two disjoint segments of slope
$+1$, each running from edge to edge of the rectangle, must be arranged as follows: one runs from
the bottom edge to the right edge, the other from the left edge to the top edge (any other
arrangement makes them cross or puts two ends on one edge). Translating $J$, we may assume the
first one lies on the diagonal $t = s$. Then, writing $I = (a, d)$ and $J = (c, \beta)$,

* the first segment is $\{(s, s) : c < s < d\}$, so $f = g$ on $(c, d)$;
* the second is $\{(s, s + \ell) : a < s < b\}$ for some $\ell > 0$ and $b \le c$, running from the
  left edge $s = a$ to the top edge $t = \beta = b + \ell$; so $f(s) = g(s + \ell)$ for $a < s < b$.

(Here $b \le c$ because the two segments have disjoint $s$-ranges, by injectivity of $g$; and
$d \le a + \ell$ because they have disjoint $t$-ranges, by injectivity of $f$. This is Milnor's
$a < b \le c < d \le \alpha < \beta$ with $\alpha = a + \ell$.) Thus the beginning of $f$ coincides
with the end of $g$, shifted by $\ell$, and the end of $f$ coincides with the beginning of $g$: the
two arcs close up into a loop of length $\ell$.

Define $H : (a, \beta) \to M$ by $H := f$ on $(a, d)$ and $H := g$ on $(c, \beta)$; consistent on
the overlap $(c, d)$. The interval $(a, \beta)$ has length $\beta - a = (b - a) + \ell > \ell$, and
$H(s) = f(s) = g(s + \ell) = H(s + \ell)$ for $a < s < b$, i.e. $H$ agrees with its own shift by
$\ell$ wherever both are defined. So $H$ descends to a smooth map
$$h : S^1 = \mathbb R / \ell\mathbb Z \to M, \qquad h(s \bmod \ell) := H(s),$$
of unit speed. It is injective: if $H(s) = H(s')$ with $s < s'$ in $(a, \beta)$, then either both
lie in $(a, d)$ or both in $(c, \beta)$, contradicting injectivity of $f$ or $g$, or $s \le c$ and
$s' \ge d$, in which case $f(s) = g(s')$ puts $(s, s')$ on $\Gamma$, hence on one of the two
segments; the diagonal is excluded by $s < s'$, so $s' = s + \ell$, which is the identification.
Hence $h$ is a smooth injective local diffeomorphism, i.e. a diffeomorphism of $S^1$ onto its image.
That image is open in $M$ (it is $f(I) \cup g(J)$) and compact (image of $S^1$), hence closed; since
$M$ is connected, $h(S^1) = M$. $\square$

---

## 3. Proof of the classification theorem

*Step 1: a maximal parametrization.* Assume $M$ is not diffeomorphic to $S^1$. Fix a
parametrization by arc length $f_0 : I_0 \to M$ (Lemma 1.1; $M$ is nonempty). Consider all
parametrizations by arc length $F : I \to M$ that extend $f_0$ ($I \supseteq I_0$, $F|_{I_0} = f_0$).
Any two of them, $F_1 : I_1 \to M$ and $F_2 : I_2 \to M$, have a common extension: their images
intersect (both contain $f_0(I_0)$), so by Lemma 2.1 and the assumption on $M$ the intersection has
one component and $F_1$ extends to a parametrization $F_3$ of $F_1(I_1) \cup F_2(I_2)$; the affine
map $L$ in that construction extends $F_2^{-1} \circ F_1$, which is the identity on $I_0$, so $L =
\mathrm{id}$ and $F_3 = F_2$ on $I_2$. In particular $F_1 = F_2$ on $I_1 \cap I_2$, and $F_1(s) =
F_2(s')$ implies $s = s'$ (injectivity of $F_3$). Therefore the union $I^\ast$ of the domains of all
extensions is an interval, the extensions patch together to a single map $F^\ast : I^\ast \to M$,
and $F^\ast$ has unit speed, is a local diffeomorphism, and is injective. An injective local
diffeomorphism is a diffeomorphism onto its image, which is the open set $\bigcup F(I)$. So
$F^\ast$ is a parametrization by arc length extending $f_0$, and by construction it cannot be
extended to any larger interval: it is *maximal*.

*Step 2: a maximal parametrization is onto.* Suppose $F^\ast(I^\ast) \ne M$. The set $F^\ast(I^\ast)$ is open and nonempty; since $M$ is connected it is
not closed, so it has a limit point $x \in M \setminus F^\ast(I^\ast)$. By Lemma 1.1 there is a
parametrization by arc length $g : J \to M$ with $x \in g(J)$. Since $g(J)$ is an open
neighbourhood of a limit point of $F^\ast(I^\ast)$, the two images intersect. By Lemma 2.1, either
$M \cong S^1$, excluded, or $F^\ast$ extends to a parametrization by arc length of
$F^\ast(I^\ast) \cup g(J)$, a strictly larger open set (it contains $x$), over a strictly larger
interval. This contradicts maximality.

*Step 3: conclusion.* If $M \cong S^1$ we are done. Otherwise $F^\ast : I^\ast \to M$ is a
diffeomorphism from an interval onto $M$. $\blacksquare$

---

## 4. What the theorem does not say

Milnor closes with a warning that we repeat, because a beginner who has just seen dimension one
fall in two pages may expect the same elsewhere. In dimension two the classification of compact
surfaces is a classical theorem, longer but complete. In dimension three it was the subject of a
century of work, ending with Perelman's proof of Thurston's geometrization conjecture in 2003. In
dimension four and above, compact manifolds *cannot* be classified: Markov showed in 1958 that there
is no algorithm that decides whether two given compact 4-manifolds are diffeomorphic, because such
an algorithm would solve the word problem for groups, which is unsolvable. The two ends of a
string are a special gift of dimension one.

---

## 5. Summary of what was silently assumed, now made explicit

| Where | Milnor says | What is actually needed |
|---|---|---|
| p. 54 | "any given local parametrization can be transformed into a parametrization by arc-length by straightforward change of variables" | $\sigma(u) = \int\|h'\|$ is a diffeomorphism because $h' \ne 0$ (Lemma 1.1) |
| p. 55 | "these line segments cannot end in the interior of $I \times J$" | a segment ending at an interior point would extend through it by the local description (Step 2 of Lemma 2.1) |
| p. 55 | "there can be at most one of the segments ending on each of the four edges" | injectivity of $f$ and $g$, also in the limit at open ends (Step 3) |
| p. 55 | "$f$ and $g \circ L$ piece together to yield the required extension" | the union of two overlapping intervals is an interval; an injective local diffeomorphism is a diffeomorphism onto its image (Step 4) |
| p. 55 | "the image $h(S^1)$, being compact and open in $M$, must be the entire manifold" | connectedness of $M$ (Step 5) |
| p. 56 | "any parametrization by arc-length can be extended to one which is maximal" | uniqueness of extensions via the closed-and-open set $A$, so the union of all extensions is an extension (Step 1 of §3) |

**Checked by machine.** The consequence the book uses, that a compact 1-manifold with boundary has
an even number of boundary points, has been verified in the Lean proof assistant as part of this
project, in a stronger form: for *topological* 1-manifolds with boundary (a compact Hausdorff
space with charts to the half-line), with no smooth structure and no arc length. The formal proof
replaces parametrizations by arc length with arcs, homeomorphisms onto intervals, and the maximal
parametrization of §3 by a finite induction over a cover by charts. The classification theorem
itself is not stated formally; what is proved on the way is that a component containing a
boundary point is homeomorphic to a closed interval. With this piece in place, Brouwer's theorem
and the degree theory of Chapters 4 and 5 are machine-checked as well; the machine-checked edition,
§10, has the details. The text does not depend on this.
