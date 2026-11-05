# Chapter 1. How many ways can you reach a point? Smooth maps and regular values

*Milnor, "Topology from the Differentiable Viewpoint", §1, rewritten for a first-year student who
wants to know what the definitions are for. Every proof is complete. Where Milnor writes "clearly"
or "it follows", we stop and do the work.*

---

## 0. A question you can ask with a desk lamp

An articulated desk lamp has two rigid arms joined by hinges: one hinge at the base, one at the
elbow. Put the lamp head at some point of the table. How many ways are there to set the two hinges
so that the head lands exactly there?

Try it. For a point comfortably within reach there are exactly two: elbow up and elbow down. Move
the target a little and there are still two; the two settings move a little too. Push the target
outward. When it reaches the edge of what the lamp can reach, the two settings merge into one, with
the arm stretched straight. Push a little further and there are none. Something similar happens
close to the base, where the arm has to fold back on itself.

So the count of solutions is *stuck at two* over a whole region, and it changes only when the
target crosses one of two special circles. This chapter is about why that is a theorem and not a
coincidence. The set of hinge settings is a compact surface (a torus: two angles). The position of
the head is a smooth map from that surface to the plane of the table. The two special circles are
the images of the settings where the map "folds", the *critical points*. Everywhere else, the
theorem of this chapter says, the number of solutions of $f(x) = y$ is locally constant in $y$.

That one theorem, about counting solutions, is the engine of the whole book. At the end of this
chapter it proves that every polynomial equation has a complex root, and it returns as the arm
in §7 with a complete computation. In later chapters it counts the images a gravitational lens
makes, and the fixed points a flow must have.

---

## 1. What you need to know before starting

This chapter uses two courses' worth of background, and nothing else.

**Multivariable calculus.** For a map $f : U \to \mathbb R^l$ defined on an open set
$U \subseteq \mathbb R^k$, the *derivative* of $f$ at a point $x$ is a linear map
$df_x : \mathbb R^k \to \mathbb R^l$, the one that best approximates $f$ near $x$:

$$f(x+h) = f(x) + df_x(h) + (\text{something much smaller than } h).$$

Its matrix is the matrix of partial derivatives. The map $f$ is *smooth* if all partial
derivatives of all orders exist and are continuous. You need three facts.

1. *Chain rule.* $d(g\circ f)_x = dg_{f(x)} \circ df_x$.
2. *The derivative of the identity is the identity,* and the derivative of a linear map $L$ is $L$.
3. *Inverse function theorem in $\mathbb R^k$.* If $f : U \to \mathbb R^k$ is smooth and $df_x$
   is an invertible linear map, then there is an open set $U' \ni x$ such that $f$ maps $U'$
   bijectively onto an open set $f(U')$, and the inverse map $f(U') \to U'$ is smooth.

   Milnor cites Apostol or Dieudonné for this. We take it as known.

**Point-set topology.** Open and closed sets, continuity, and these three notions.

* A space is *compact* if every open cover has a finite subcover. A closed subset of a compact
  space is compact. The image of a compact set under a continuous map is compact.
* A space is *Hausdorff* if any two distinct points have disjoint open neighbourhoods. In a
  Hausdorff space, compact sets are closed, and single points are closed.
* A set is *connected* if it cannot be written as a disjoint union of two nonempty sets that are
  each open in it. The image of a connected set under a continuous map is connected.

Every subset of $\mathbb R^k$ is Hausdorff. This matters below: Milnor's manifolds live inside
$\mathbb R^k$, so he never has to say "Hausdorff", but the arguments use it, and we will say
where.

---

## 2. Smooth manifolds (Milnor pp. 1–2)

A manifold is a space that looks, close up, like a piece of $\mathbb R^m$. The lamp's set of
hinge settings looks, close up, like a piece of the plane: two angles, each free to vary a little.
The surface of the Earth looks, close up, like a piece of the plane, which is why maps work.

**Definition.** Let $M \subseteq \mathbb R^k$. A map $f : M \to \mathbb R^l$ is *smooth* if for
every $x \in M$ there is an open set $W \subseteq \mathbb R^k$ containing $x$ and a smooth map
$F : W \to \mathbb R^l$ that agrees with $f$ on $W \cap M$.

So smoothness on an arbitrary subset means "locally extends to a smooth map on an open set".
A map $f : M \to N$ between subsets of Euclidean spaces is smooth if it is smooth as a map into
$\mathbb R^l \supseteq N$. It is a *diffeomorphism* if it is a smooth bijection whose inverse is
also smooth.

**Definition.** A subset $M \subseteq \mathbb R^k$ is a *smooth manifold of dimension $m$* if
every $x \in M$ has a neighbourhood $W \cap M$ (with $W$ open in $\mathbb R^k$) that is
diffeomorphic to an open subset $U$ of $\mathbb R^m$. A diffeomorphism $g : U \to W \cap M$ is
called a *parametrization*; its inverse $W \cap M \to U$ is a *coordinate system* or *chart*.

**Example: the sphere.** The unit sphere $S^2 = \{(x,y,z) : x^2+y^2+z^2 = 1\}$ is a smooth
manifold of dimension 2. The map $(x,y) \mapsto (x, y, \sqrt{1-x^2-y^2})$, defined for
$x^2+y^2<1$, parametrizes the open upper hemisphere $z > 0$; it is smooth, and its inverse is the
projection $(x,y,z) \mapsto (x,y)$, which is the restriction of a linear map and hence smooth.
Six such maps (one per hemisphere $x>0$, $x<0$, $y>0$, $y<0$, $z>0$, $z<0$) cover the sphere.

**Example: the torus of hinge settings.** A hinge angle is a point of the circle
$S^1 = \{(\cos\theta, \sin\theta)\} \subseteq \mathbb R^2$. Two hinges give a point of
$S^1 \times S^1 \subseteq \mathbb R^4$, the *torus*. Near any point, the map
$(\theta_1, \theta_2) \mapsto (\cos\theta_1, \sin\theta_1, \cos\theta_2, \sin\theta_2)$,
restricted to a small open square of angles, is a parametrization: it is smooth, injective on a
square of side less than $2\pi$, and its inverse is given near the point by inverse trigonometric
functions, which are smooth where the relevant cosine or sine is nonzero. So the torus is a
compact smooth manifold of dimension 2. (Compact: it is closed and bounded in $\mathbb R^4$.)

> **A note on abstract manifolds.** Modern treatments do not require a manifold to sit inside
> $\mathbb R^k$. They define a manifold as a space equipped with charts (homeomorphisms from open
> pieces of the space to open subsets of $\mathbb R^m$) whose changes of coordinates are smooth.
> Every manifold in Milnor's sense is one in this sense: the charts are the inverses of Milnor's
> parametrizations, and the change of coordinates $h^{-1}\circ g$ is smooth because $h^{-1}$ and
> $g$ are. The converse is the Whitney embedding theorem. Everything in this chapter holds for
> abstract manifolds, with one consequence: an abstract manifold need not be Hausdorff, so we
> add "Hausdorff" as a hypothesis when we use it.

---

## 3. Tangent spaces and derivatives (Milnor pp. 2–7)

We want to differentiate a smooth map $f : M \to N$ between manifolds. The derivative at $x$
should be a linear map from a "tangent space" at $x$ to a tangent space at $f(x)$. For the lamp,
the tangent space at a setting is the plane of small changes of the two angles, and the
derivative tells how the head moves for a small change of the hinges.

**Definition of the tangent space.** Let $M \subseteq \mathbb R^k$ be an $m$-manifold, $x\in M$,
and choose a parametrization $g : U \to M$ with $g(u) = x$. Think of $g$ as a map
$U \to \mathbb R^k$, so its derivative $dg_u : \mathbb R^m \to \mathbb R^k$ makes sense. Define

$$TM_x := \operatorname{image}(dg_u) \subseteq \mathbb R^k.$$

**Claim 3.1. This does not depend on the choice of $g$.** Let $h : V \to M$ be another
parametrization with $h(v) = x$. Then $h^{-1}\circ g$ is defined on the open set
$U_1 := g^{-1}(h(V))$, which contains $u$, and it is a diffeomorphism onto its image $V_1$
(a composition of diffeomorphisms). On $U_1$ we have $g = h \circ (h^{-1}\circ g)$, so by the
chain rule

$$dg_u = dh_v \circ d(h^{-1}\circ g)_u.$$

The right-hand factor $d(h^{-1}\circ g)_u : \mathbb R^m \to \mathbb R^m$ is invertible (it is the
derivative of a diffeomorphism; see Claim 3.3), so it is onto $\mathbb R^m$, and therefore
$\operatorname{image}(dg_u) = \operatorname{image}(dh_v)$.

**Claim 3.2. $TM_x$ has dimension $m$.** Since $g^{-1} : g(U) \to U$ is smooth, there is an open
$W \ni x$ in $\mathbb R^k$ and a smooth $F : W \to \mathbb R^m$ agreeing with $g^{-1}$ on
$W \cap g(U)$. On the open set $U_0 := g^{-1}(W \cap g(U)) \ni u$ we have $F \circ g = \mathrm{id}$,
so by the chain rule $dF_x \circ dg_u = \mathrm{id}_{\mathbb R^m}$. A linear map with a left
inverse is injective, so $dg_u$ is injective and its image has dimension $m$.

**Claim 3.3 (Milnor's "Assertion", p. 4).** If $f : U \to V$ is a diffeomorphism between open
subsets of $\mathbb R^k$ and $\mathbb R^l$, then $k = l$ and $df_x$ is invertible. *Proof.*
$f^{-1}\circ f = \mathrm{id}_U$ and $f \circ f^{-1} = \mathrm{id}_V$; differentiating with the
chain rule, $d(f^{-1})_{f(x)}\circ df_x = \mathrm{id}_{\mathbb R^k}$ and
$df_x\circ d(f^{-1})_{f(x)} = \mathrm{id}_{\mathbb R^l}$. So $df_x$ has a two-sided inverse.
A linear map $\mathbb R^k\to\mathbb R^l$ with a two-sided inverse forces $k=l$ (compare
dimensions of domain and image).

**Definition of the derivative.** Let $f : M \to N$ be smooth, $x \in M$, $y = f(x)$. Choose an
open $W \ni x$ in $\mathbb R^k$ and a smooth $F : W \to \mathbb R^l$ agreeing with $f$ on
$W \cap M$. Define $df_x(v) := dF_x(v)$ for $v \in TM_x$.

**Claim 3.4. $df_x$ maps $TM_x$ into $TN_y$, and does not depend on $F$.** Choose parametrizations
$g : U \to M$ around $x$ and $h : V \to N$ around $y$, shrinking $U$ so that $g(U) \subseteq W$
and $f(g(U)) \subseteq h(V)$ (possible because $f$ is continuous, being locally the restriction
of the continuous map $F$). Then $h^{-1}\circ f \circ g : U \to V$ is a well-defined smooth map,
and on $U$ we have $F \circ g = h \circ (h^{-1}\circ f\circ g)$. Chain rule:

$$dF_x \circ dg_u = dh_v \circ d(h^{-1}\circ f\circ g)_u .$$

The left side, applied to $\mathbb R^m$, is $dF_x(TM_x)$. The right side lands in
$\operatorname{image}(dh_v) = TN_y$. So $dF_x(TM_x) \subseteq TN_y$. And the formula shows
$df_x = dh_v \circ d(h^{-1}\circ f\circ g)_u \circ (dg_u)^{-1}$ on $TM_x$ (using that $dg_u$ is a
bijection $\mathbb R^m \to TM_x$ by Claim 3.2), which involves only $f$, $g$, $h$, not $F$.

**Properties.** The chain rule $d(g\circ f)_x = dg_{f(x)}\circ df_x$ and $d(\mathrm{id})_x =
\mathrm{id}$ hold for manifolds, by applying the Euclidean versions to local extensions.
Consequently, exactly as in Claim 3.3: *if $f : M \to N$ is a diffeomorphism then $df_x : TM_x \to
TN_{f(x)}$ is an isomorphism, so $\dim M = \dim N$.*

**In practice.** The formula in Claim 3.4 says: to compute $df_x$, write $f$ in coordinates as
$h^{-1}\circ f\circ g$ and take the ordinary Jacobian matrix. For the lamp, $f$ is already a map
from angles to the plane, and $df$ is its $2 \times 2$ Jacobian; we compute it in §7.

---

## 4. The inverse function theorem on manifolds (Milnor pp. 4 and 7)

Milnor states the inverse function theorem for open subsets of $\mathbb R^k$ (p. 4) and then uses
it for manifolds without comment (p. 7). Here is the manifold statement and its proof from the
Euclidean one.

**Theorem 4.1.** Let $f : M \to N$ be a smooth map between manifolds of the same dimension, and
$x \in M$. If $df_x : TM_x \to TN_{f(x)}$ is an invertible linear map, then there are open sets
$U' \ni x$ in $M$ and $V' \ni f(x)$ in $N$ such that $f$ restricts to a diffeomorphism $U' \to V'$.

*Proof.* Choose charts: a parametrization $g : U \to M$ with $g(u) = x$, and $h : V \to N$ with
$h(v) = f(x)$; shrink $U$ so that $f(g(U)) \subseteq h(V)$. Let
$\varphi := h^{-1}\circ f\circ g : U \to V$, the map "$f$ written in charts". It is smooth, and by
the formula in Claim 3.4, $df_x = dh_v \circ d\varphi_u\circ (dg_u)^{-1}$, with $dg_u$ and $dh_v$
bijections onto the tangent spaces. Hence $df_x$ invertible implies $d\varphi_u$ invertible.

Apply the Euclidean inverse function theorem to $\varphi$ at $u$: there is an open $U_1 \ni u$
such that $\varphi$ maps $U_1$ diffeomorphically onto an open set $V_1 = \varphi(U_1)$. Put
$U' := g(U_1)$ and $V' := h(V_1)$. These are open in $M$ and $N$ (images of open sets under
the homeomorphisms $g$, $h$ onto open subsets of $M$, $N$). On $U'$ we have
$f = h\circ\varphi\circ g^{-1}$, a composition of diffeomorphisms $U' \to U_1 \to V_1 \to V'$.
$\square$

**What the theorem says physically.** If the Jacobian of "hinges $\mapsto$ head position" is
invertible at a setting, then near that setting the head position determines the hinges, and does
so smoothly: a small, smooth motion of the head is produced by a small, smooth motion of the
hinges. Where the Jacobian is not invertible, no such smooth inverse exists. Robot controllers
call these *singular configurations* and steer around them, because near one, the inverse
derivative $(df_x)^{-1}$ is enormous: a small motion of the hand demands a violent motion of the
joints. §7 makes this quantitative.

---

## 5. Regular values, and why the count is locally constant (Milnor pp. 7–8)

From now on $f : M \to N$ is smooth and $\dim M = \dim N$.

**Definition.** A point $x \in M$ is a *regular point* of $f$ if $df_x$ is invertible; otherwise
$x$ is a *critical point*. A point $y \in N$ is a *regular value* if every point of $f^{-1}(y)$ is
regular; otherwise (that is, if $y = f(x)$ for some critical point $x$) $y$ is a *critical
value*. Note that a point $y$ *not in the image of $f$* is a regular value, because the condition
on $f^{-1}(y) = \varnothing$ is vacuous. For the lamp: a target out of reach is a regular value,
with zero solutions.

By Theorem 4.1, near a regular point $f$ is a diffeomorphism onto an open set.

**Theorem 5.1.** Suppose $M$ is compact, $N$ is Hausdorff (points are closed suffices), and $y$
is a regular value. Then $f^{-1}(y)$ is finite.

*Proof.* Write $S := f^{-1}(y)$.

*Step 1: $S$ is compact.* The set $\{y\}$ is closed in $N$, and $f$ is continuous, so $S$ is
closed in $M$. A closed subset of a compact space is compact.

*Step 2: each point of $S$ is isolated in $S$.* Let $x \in S$. Since $y$ is a regular value,
$x$ is a regular point, so by Theorem 4.1 there is an open $U_x \ni x$ on which $f$ is injective.
If $x' \in U_x \cap S$ then $f(x') = y = f(x)$, so $x' = x$. Thus $U_x \cap S = \{x\}$.

*Step 3: finiteness.* The sets $U_x$, $x \in S$, form an open cover of the compact set $S$.
Choose a finite subcover $U_{x_1},\dots,U_{x_k}$. Every $z \in S$ lies in some $U_{x_i}$, and
then $z = x_i$ by Step 2. So $S \subseteq \{x_1,\dots,x_k\}$. $\square$

Milnor's text for this: "$f^{-1}(y)$ is in any case compact, being a closed subset of the compact
space $M$; and $f^{-1}(y)$ is discrete, since $f$ is one-one in a neighborhood of each
$x \in f^{-1}(y)$." Step 3, that compact and discrete implies finite, is left to the reader.

**Definition.** For $M$ compact and $y$ a regular value, $\#f^{-1}(y)$ denotes the number of
points of $f^{-1}(y)$, a natural number by Theorem 5.1.

**Theorem 5.2 (the count is locally constant).** Suppose $M$ is compact and $M$, $N$ are
Hausdorff. Let $y$ be a regular value. Then there is an open set $V \ni y$ such that
$\#f^{-1}(y') = \#f^{-1}(y)$ for every $y' \in V$.

Milnor gives the proof in a bracket of four lines. It is the most compressed argument in the
chapter, so here it is in full. Keep the lamp in mind: the $x_i$ are the elbow-up and elbow-down
settings, and the $L_i$ below are the two inverse-kinematics formulas.

*Proof.* Let $x_1,\dots,x_k$ be the points of $f^{-1}(y)$ (finite by Theorem 5.1; $k$ may be $0$).

*Step 1: separate the $x_i$.* Since $M$ is Hausdorff and the $x_i$ are finitely many distinct
points, we can choose open sets $W_1,\dots,W_k$ with $x_i \in W_i$ and $W_i \cap W_j = \varnothing$
for $i \ne j$. (For each pair $i \ne j$ pick disjoint open neighbourhoods $A_{ij} \ni x_i$,
$B_{ij}\ni x_j$, and let $W_i$ be the intersection of all $A_{ij}$ and $B_{ji}$ over $j \ne i$;
finitely many intersections, so still open.)

*Step 2: local inverses.* Each $x_i$ is a regular point. By Theorem 4.1, choose an open
$U_i' \ni x_i$ mapped by $f$ diffeomorphically onto an open set of $N$. Put $U_i := U_i'\cap W_i$,
still open, still containing $x_i$, still mapped diffeomorphically onto an open set
$V_i := f(U_i)$ of $N$, with the $U_i$ pairwise disjoint. Write $L_i : V_i \to U_i$ for the
inverse of $f|_{U_i}$.

*Step 3: the bad set.* Let $C := f(M \setminus (U_1\cup\dots\cup U_k))$. The set
$M\setminus\bigcup U_i$ is closed in the compact space $M$, hence compact; its image $C$ under
the continuous $f$ is compact; and since $N$ is Hausdorff, $C$ is closed. Moreover $y \notin C$:
if $y = f(z)$ then $z$ is one of the $x_i$, which lies in $U_i$.

*Step 4: the neighbourhood.* Set $V := (V_1\cap\dots\cap V_k)\setminus C$. This is open (a finite
intersection of open sets minus a closed set) and contains $y$ (as $y = f(x_i) \in V_i$ for
each $i$, and $y \notin C$).

*Step 5: counting.* Let $y' \in V$. We claim the map $i \mapsto L_i(y')$ is a bijection from
$\{1,\dots,k\}$ onto $f^{-1}(y')$.

* It lands in $f^{-1}(y')$: $f(L_i(y')) = y'$ because $y' \in V_i$.
* It is injective: $L_i(y') \in U_i$ and $L_j(y') \in U_j$; if these are equal then
  $U_i\cap U_j \ne \varnothing$, so $i = j$.
* It is surjective: let $f(z) = y'$. Since $y' \notin C$, $z \notin M\setminus\bigcup U_i$, so
  $z \in U_i$ for some $i$. Then $f(z) = y'$ and $f|_{U_i}$ is injective with inverse $L_i$, so
  $z = L_i(y')$.

Hence $\#f^{-1}(y') = k = \#f^{-1}(y)$. $\square$

> **Two remarks.** (a) Milnor writes "where $y$ ranges only through regular values", but the
> proof does not use that $y'$ is regular: the count equals $k$ for *every* $y' \in V$. (b) The
> two uses of "Hausdorff", Steps 1 and 3, are invisible in Milnor because his manifolds sit in
> $\mathbb R^k$. For abstract manifolds they must be hypotheses.

> **Why compactness cannot be dropped.** Take $M = (0, 3)$, an open interval, $N = \mathbb R$,
> and $f(x) = x$. Every point is regular, but $\#f^{-1}(y)$ is $1$ for $0 < y < 3$ and $0$
> otherwise, and it jumps at $y = 0$ and $y = 3$. Solutions escaped through the open ends. The
> bad set $C$ in Step 3 is exactly what stops this: with $M$ compact, the solutions have nowhere
> to escape to.

### An interactive look at the theorem

The figure shows the lamp as a two-link arm with link lengths $\ell_1 = 1$ and $\ell_2 = 0.6$.
On the right is the table: the plane $N$, with the two critical circles of radii
$\ell_1 - \ell_2$ and $\ell_1 + \ell_2$. On the left is the torus $M$ of hinge settings, drawn as
a square with opposite edges identified, with the critical points (arm straight, $\theta_2 = 0$;
arm folded, $\theta_2 = \pi$) as two horizontal lines. Drag the target point $y$ on the table.
The two solutions appear on the torus and as the two arm postures on the table. Between the
circles the count is $2$; cross a circle and the two solutions meet on a critical line and
vanish together.

<div id="arm-figure"></div>

*(In the printed version this figure is a still image; the interactive version is in the web
edition.)*

---

## 6. The counting principle (Milnor p. 9)

The last paragraph of Milnor's proof of the fundamental theorem of algebra uses nothing about
polynomials. We isolate it.

**Theorem 6.1.** Let $M$ be compact, $M$ and $N$ Hausdorff, $f : M \to N$ smooth with
$\dim M=\dim N$. Let $R \subseteq N$ be a connected set consisting of regular values, and suppose
some point of $R$ is in the image of $f$. Then every point of $R$ is in the image of $f$.

*Proof.* Consider the function $c : R \to \mathbb N$, $c(y) := \#f^{-1}(y)$. By Theorem 5.2,
each $y \in R$ has a neighbourhood on which $c$ is constant. A function into $\mathbb N$ that is
locally constant is continuous when $\mathbb N$ has the discrete topology, and a continuous map
from a connected set to a discrete space is constant (its image is connected, and connected
subsets of a discrete space are single points). So $c$ is constant on $R$. By hypothesis
$c(y_0) \ge 1$ for some $y_0 \in R$, so $c(y) \ge 1$ for all $y \in R$, i.e. $f^{-1}(y) \ne
\varnothing$. $\square$

**Corollary 6.2.** If moreover the set of *all* regular values is connected and contains a point
of the image, then $f$ is onto. *Proof.* A point of $N$ is either a regular value, covered by
Theorem 6.1, or a critical value, which is by definition $f$ of something. $\square$

For the lamp, the regular values form three connected regions (inside the small circle, between
the circles, outside the big circle), and on each the count is constant: $0$, $2$, $0$.

---

## 7. Application: the two-link arm, completely

Here is the desk lamp as a theorem. The same computation, with six joints instead of two, is done
inside every industrial robot controller many times a second.

**The map.** Links of lengths $\ell_1 > \ell_2 > 0$, hinge angles $\theta_1$ (at the base,
measured from the $x$-axis) and $\theta_2$ (at the elbow, measured from the first link). The head
is at

$$f(\theta_1, \theta_2) = \bigl(\ell_1\cos\theta_1 + \ell_2\cos(\theta_1+\theta_2),\;
\ell_1\sin\theta_1 + \ell_2\sin(\theta_1+\theta_2)\bigr).$$

This is a smooth map $f : M \to N$ from the torus $M = S^1 \times S^1$ (compact, Hausdorff,
dimension 2) to the plane $N = \mathbb R^2$ (Hausdorff, dimension 2).

**The derivative.** In the angle coordinates, $df$ is the Jacobian matrix with columns
$\partial f/\partial\theta_1$ and $\partial f/\partial\theta_2$. Writing $s_1 = \sin\theta_1$,
$c_{12} = \cos(\theta_1 + \theta_2)$ and so on,

$$df = \begin{pmatrix} -\ell_1 s_1 - \ell_2 s_{12} & -\ell_2 s_{12} \\
\ell_1 c_1 + \ell_2 c_{12} & \ell_2 c_{12}\end{pmatrix},
\qquad
\det df = \ell_1\ell_2\,(c_1 s_{12} - s_1 c_{12}) = \ell_1\ell_2\sin\theta_2 .$$

(The $\ell_2^2$ terms cancel, and $c_1 s_{12} - s_1 c_{12} = \sin(\theta_1+\theta_2-\theta_1)$.)

**Critical points and critical values.** $df$ is invertible exactly when $\sin\theta_2 \ne 0$.
The critical points are the two circles $\theta_2 = 0$ (arm straight) and $\theta_2 = \pi$ (arm
folded back). Their images are the circles $|y| = \ell_1 + \ell_2$ and $|y| = \ell_1 - \ell_2$.
So the regular values are the three connected open regions

$$R_{\text{in}} = \{|y| < \ell_1 - \ell_2\}, \qquad
R_{\text{mid}} = \{\ell_1 - \ell_2 < |y| < \ell_1 + \ell_2\}, \qquad
R_{\text{out}} = \{|y| > \ell_1 + \ell_2\}.$$

**What the theorems say.** By Theorem 5.1, over each regular value there are finitely many
settings. By Theorem 6.1, the count is constant on each of the three regions. It remains to find
it at one point of each. Since $|f| \le \ell_1 + \ell_2$ and $|f| \ge \ell_1 - \ell_2$ (triangle
inequality), the count is $0$ on $R_{\text{out}}$ and on $R_{\text{in}}$: those regular values are
not in the image, in agreement with the definition. On $R_{\text{mid}}$, take any target $y$ with
$r = |y|$. The law of cosines gives

$$\cos\theta_2 = \frac{r^2 - \ell_1^2 - \ell_2^2}{2\ell_1\ell_2},$$

and for $\ell_1 - \ell_2 < r < \ell_1 + \ell_2$ the right side lies strictly between $-1$ and $1$,
so there are exactly two values $\theta_2 = \pm\arccos(\cdots)$, and for each of them $\theta_1$
is determined: $\theta_1 = \operatorname{atan2}(y) - \operatorname{atan2}(\ell_2\sin\theta_2,\;
\ell_1 + \ell_2\cos\theta_2)$. So the count is exactly $2$. Elbow up, elbow down.

The theorem predicted "constant on the region"; the formula confirms "two". A beginner should
notice which is the stronger statement. The formula needed the law of cosines, which exists
because the arm is so simple. The theorem needed only that $f$ is smooth and $M$ compact, and
will apply to a six-joint arm, a polynomial, or a gravitational lens, where no formula is
available.

**The two local inverses.** The maps $L_1, L_2$ of Theorem 5.2 are here the two branches
$y \mapsto (\theta_1, \theta_2)$ with $\theta_2 > 0$ and $\theta_2 < 0$. They are defined and
smooth on all of $R_{\text{mid}}$, not just on a neighbourhood of one $y$, because $R_{\text{mid}}$
happens to be simple; in general the $L_i$ are only local.

**The singularities.** Differentiate the law of cosines: $-\sin\theta_2\, d\theta_2 = (r/\ell_1\ell_2)\, dr$,
so $|d\theta_2/dr| = r/(\ell_1\ell_2|\sin\theta_2|)$, which tends to infinity as the arm
straightens. This is the inverse function theorem read backwards: $(df)^{-1}$ has norm at least
$1/|\det df|$ times something bounded, so as $\det df = \ell_1\ell_2\sin\theta_2 \to 0$ the joints
must move ever faster to produce a given motion of the hand. That is why a robot arm slows down,
or refuses, when asked to reach the edge of its workspace. In robotics the quantity
$1/|\det df|$ (or the ratio of singular values of $df$) is called the *manipulability* or
*dexterity* index; near a critical point it is bad, and the controller knows it because it is
watching the same determinant we just computed.

> **The same theorem in another costume.** A GPS receiver solves $f(x) = y$ where $x$ is its
> position and $y$ the vector of measured distances to the satellites. The satellites' geometry
> determines $df_x$; when the satellites are nearly coplanar as seen from the receiver, $df_x$ is
> nearly singular, $(df_x)^{-1}$ is large, and small measurement errors become large position
> errors. Receivers report this as the "dilution of precision", and it is the size of
> $(df_x)^{-1}$. Same theorem, same determinant.

---

## 8. The fundamental theorem of algebra (Milnor pp. 8–9)

The counting principle proves a theorem of algebra that has nothing visibly to do with arms or
manifolds. Milnor put it here to show what the machinery can do; so do we.

**Theorem 8.1.** Every nonconstant polynomial
$P(z) = a_0 z^n + a_1 z^{n-1}+\dots+a_n$ with complex coefficients, $a_0 \ne 0$, $n \ge 1$, has
a zero.

The idea: a polynomial is a smooth map $\mathbb C \to \mathbb C$, but $\mathbb C$ is not
compact, so Theorem 6.1 does not apply, and indeed the count can leak to infinity as in the open
interval example. We add one point at infinity to make it compact.

### 8.1 The compact surface

Milnor takes the unit sphere $S^2 \subset \mathbb R^3$ and identifies $S^2$ minus the north
pole with $\mathbb C$ by stereographic projection. We take the more direct route.

**Definition.** The *Riemann sphere* is the set $\widehat{\mathbb C} := \mathbb C \cup \{\infty\}$,
with the topology in which a set is open if either it is an open subset of $\mathbb C$, or it
contains $\infty$ and its complement is a compact subset of $\mathbb C$. (Neighbourhoods of
$\infty$ are "everything outside a big disc".) This is a compact Hausdorff space.

We make it a smooth 2-manifold with two charts:

* $\chi_0 : \mathbb C \to \mathbb C$, $\chi_0(z) = z$, defined on $\widehat{\mathbb C}\setminus\{\infty\}$;
* $\chi_\infty : \widehat{\mathbb C}\setminus\{0\}\to \mathbb C$, $\chi_\infty(z) = 1/z$ for
  $z \ne 0,\infty$, and $\chi_\infty(\infty) = 0$.

Both are homeomorphisms onto $\mathbb C$ (for $\chi_\infty$ one checks that $1/z \to 0$ as
$z \to \infty$ and $1/z \to \infty$ as $z \to 0$). The change of coordinates
$\chi_\infty\circ\chi_0^{-1}$ is $z \mapsto 1/z$ on $\mathbb C\setminus\{0\}$, which is smooth.
So $\widehat{\mathbb C}$ is a smooth manifold, and it is compact and Hausdorff.

> **Why not $S^2$?** Stereographic projection is a diffeomorphism $S^2 \to \widehat{\mathbb C}$,
> so the two are the same manifold and Milnor's argument transfers word for word. Working on
> $\widehat{\mathbb C}$ directly saves the coordinate computation "$h_+h_-^{-1}(z) = 1/\bar z$"
> and removes the complex conjugates from Milnor's formula for $Q$ below.

### 8.2 The map

Define $f : \widehat{\mathbb C}\to\widehat{\mathbb C}$ by $f(z) = P(z)$ for $z \in \mathbb C$
and $f(\infty) = \infty$.

**Claim 8.2. $f$ is continuous.** On $\mathbb C$ it is a polynomial. At $\infty$: we need
$P(z)\to\infty$ as $z\to\infty$, i.e. $|P(z)|\to\infty$ as $|z|\to\infty$, which holds for any
nonconstant polynomial (the leading term dominates).

**Claim 8.3. $f$ is smooth.** Smoothness is checked in charts.

*At a point $z \in \mathbb C$:* use the chart $\chi_0$ at both ends. Then $f$ reads as
$\chi_0\circ f\circ\chi_0^{-1} = P$, a polynomial, hence smooth.

*At $\infty$:* use the chart $\chi_\infty$ at both ends. For $w \ne 0$ with $P(1/w)\neq 0$,

$$\chi_\infty\circ f\circ\chi_\infty^{-1}(w) = \chi_\infty(P(1/w)) = \frac{1}{P(1/w)},$$

and $\chi_\infty f\chi_\infty^{-1}(0) = \chi_\infty(f(\infty)) = 0$. Now compute: with
$\widetilde P(w) := a_0 + a_1 w + \dots + a_n w^n$ (the *reversed* polynomial),

$$P(1/w) = a_0 w^{-n} + a_1 w^{-(n-1)} + \dots + a_n = w^{-n}\,\widetilde P(w), \qquad\text{so}\qquad
\frac{1}{P(1/w)} = \frac{w^n}{\widetilde P(w)} =: Q(w).$$

Since $\widetilde P(0) = a_0 \ne 0$, there is an open disc around $0$ on which $\widetilde P$ has
no zero. On that disc, $Q$ is a quotient of polynomials with nonvanishing denominator, hence
smooth; and on that disc, for $w \ne 0$, $P(1/w) = w^{-n}\widetilde P(w) \ne 0$, so the formula
$\chi_\infty f\chi_\infty^{-1}(w) = Q(w)$ is valid, while at $w = 0$ both sides are $0$ (because
$n \ge 1$). A function that agrees with a smooth function on a neighbourhood of a point is smooth
at that point. $\square$

### 8.3 The critical values

**Claim 8.4.** For $z \in \mathbb C$ with $P'(z)\ne 0$, the point $z$ is a regular point of $f$.

*Proof.* In the chart $\chi_0$ at both ends, $f$ is $P$, so $df_z$ is the derivative of $P$ at
$z$ viewed as a real-linear map $\mathbb C\to\mathbb C$: it is $h \mapsto P'(z)\,h$. If
$P'(z)\ne 0$ this is invertible (inverse $h\mapsto h/P'(z)$). $\square$

Define the *bad set*

$$B := \{\infty\}\cup\{P(z) : P'(z) = 0\}\subseteq\widehat{\mathbb C}.$$

**Claim 8.5.** $B$ is finite, every point of $B$ is in the image of $f$, and every point outside
$B$ is a regular value of $f$.

*Proof.* $P'$ is a nonzero polynomial (its degree is $n-1\ge 0$ and its leading coefficient
$n a_0 \ne 0$), so it has finitely many zeros; $B$ is the image of a finite set plus one point.
$\infty = f(\infty)$ and $P(z) = f(z)$, so $B\subseteq f(\widehat{\mathbb C})$. Finally let
$y\notin B$ and $f(x) = y$. Then $x\ne\infty$ (else $y = \infty\in B$), so $x = z\in\mathbb C$,
and $P'(z)\ne 0$ (else $y = P(z)\in B$), so $z$ is a regular point by Claim 8.4. $\square$

> Milnor does not mention that $\infty$ might be a critical point of $f$. It usually is: in the
> chart $\chi_\infty$, $f$ is $Q(w) = w^n/\widetilde P(w)$, whose derivative at $0$ vanishes when
> $n\ge 2$. It does no harm, because we simply put $\infty$ into the bad set.

### 8.4 The complement of a finite set is connected

**Claim 8.6.** $\widehat{\mathbb C}\setminus B$ is connected.

*Proof.* Since $\infty\in B$, the set $\widehat{\mathbb C}\setminus B$ equals
$\mathbb C\setminus B_0$ where $B_0 := \{P(z): P'(z)=0\}$ is finite. The complement of a finite
set in $\mathbb C = \mathbb R^2$ is path-connected: given two points $a, b$ outside $B_0$, among
the infinitely many paths $a \to p \to b$ made of two segments through a third point $p$, at most
finitely many meet $B_0$ (each point of $B_0$ rules out the $p$ on at most two lines), so some
avoid it. Path-connected implies connected. $\square$

### 8.5 Some good value is hit

**Claim 8.7.** There is a point $y_0\notin B$ in the image of $f$.

*Proof.* The image $P(\mathbb C)$ is infinite: otherwise $\mathbb C$ would be the union, over the
finitely many values $c\in P(\mathbb C)$, of the sets $\{z : P(z) = c\}$, each of which is finite
(the zeros of the nonzero polynomial $P - c$), so $\mathbb C$ would be finite. Since $B_0$ is
finite, some $y_0 = P(z_0)\in P(\mathbb C)$ lies outside $B_0$; then $y_0\notin B$ and $y_0 =
f(z_0)$. $\square$

### 8.6 Conclusion

Apply Theorem 6.1 with $M = N = \widehat{\mathbb C}$ (compact, Hausdorff, dimension 2), the
smooth map $f$, and $R := \widehat{\mathbb C}\setminus B$: by Claim 8.5 it consists of regular
values, by Claim 8.6 it is connected, and by Claim 8.7 it meets the image. Hence
$R\subseteq f(\widehat{\mathbb C})$. Together with $B\subseteq f(\widehat{\mathbb C})$ from
Claim 8.5, $f$ is onto.

In particular $0 = f(x)$ for some $x\in\widehat{\mathbb C}$. Since $f(\infty) = \infty\ne 0$,
$x$ is a complex number $z$, and $f(z) = P(z) = 0$. $\blacksquare$

In the language of the lamp: the polynomial is an arm with $n$ ways to reach every regular value
(the count is $n$ on the connected set $R$, since $P(z) = y_0$ has $n$ distinct roots when
$y_0$ is not a critical value), and there are no unreachable regular values because the sphere
has no outside.

---

## 9. Summary of what was silently assumed, now made explicit

| Where | Milnor says | What is actually needed |
|---|---|---|
| p. 7 | "it follows from the inverse function theorem" | the manifold version, Theorem 4.1, proved from the Euclidean one |
| p. 8 | "$f^{-1}(y)$ is compact and discrete" hence finite | $N$ has closed points; compact + discrete $\Rightarrow$ finite (Step 3 of 5.1) |
| p. 8 | "choose pairwise disjoint neighbourhoods" | $M$ Hausdorff (Step 1 of 5.2) |
| p. 8 | $V = \bigcap V_i \setminus f(M\setminus\bigcup U_i)$ is a neighbourhood | $N$ Hausdorff, so the compact set $f(M\setminus\bigcup U_i)$ is closed (Step 3 of 5.2) |
| p. 8 | "#$f^{-1}(y)$ is locally constant" | the count is constant on a whole neighbourhood, regular or not (Theorem 5.2) |
| p. 9 | "the regular values form a sphere minus finitely many points" | $\infty$ may be critical; the bad set includes it (Claim 8.5) |
| p. 9 | "#$f^{-1}(y)$ can't be zero everywhere" | the image of a nonconstant polynomial is infinite (Claim 8.7) |

**Checked by machine.** Theorems 4.1, 5.1, 5.2, 6.1, 6.2 and 8.1, with the Riemann sphere and
the polynomial map, have been verified in the Lean proof assistant as part of this project, for
abstract manifolds with the Hausdorff hypotheses stated above. The text does not depend on this;
it is a silent check that no step above was skipped. The two-link arm computation in §7 is
elementary and was not formalized.
