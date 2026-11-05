# Chapter 2. The crumpled map: level sets, boundaries, and Brouwer's fixed point

*Milnor, "Topology from the Differentiable Viewpoint", §2, rewritten for a first-year student who
wants to know what the theorem is for. Every proof is complete, except that one fact about
one-dimensional manifolds is quoted from Milnor's Appendix and proved in the chapter devoted to
it.*

---

## 0. A crumpled map

Take a street map of the town you are standing in. Crumple it up, without tearing it, and drop it
on the ground anywhere inside the region it depicts. Then some point of the paper is lying
directly above the place in town that it represents.

Or: stir a cup of coffee gently, so that the surface moves continuously and stays a disk. When it
comes to rest, at least one point of the surface is exactly where it started.

Both are the same theorem. Each place in town is a point of a disk $D$; the crumpled map sends it
to the point of the ground under its picture, another point of $D$; the claim is that this
continuous map $D \to D$ has a *fixed point*, a point $x$ with $g(x) = x$. That is Brouwer's fixed
point theorem, in dimension 2. In dimension 3 it says a continuous rearrangement of the contents of
a ball leaves some point in place. In dimension $n$ it is the foundation of the existence theorems
of economics (equilibrium prices exist; every finite game has a Nash equilibrium) and of the
theory of Markov chains (every finite chain has a stationary distribution; see §7).

Why should it be true? Here is the whole argument in one picture. Suppose $g$ has no fixed point.
Then from every point $x$ you can draw the ray that starts at $g(x)$, passes through $x$, and
leaves the disk at a boundary point $f(x)$. This $f$ is a smooth map from the disk onto its
boundary circle that leaves boundary points where they are. Now pick a boundary point $y$ and look
at the set of all $x$ with $f(x) = y$: it is a curve that starts at $y$ and wanders into the disk.
Where can it end? It cannot end at an interior point, because near a regular point the equation
$f(x) = y$ has solutions along a curve through it, not a dead end. It cannot end at another
boundary point, since $f$ is the identity there. So it cannot end at all, and a compact curve
with exactly one endpoint does not exist. The interactive figure in §6 shows the curve ending, as
it must, at a fixed point of $g$.

Making that argument rigorous takes this whole chapter. We need to know that a solution set
$f^{-1}(y)$ is a manifold (Lemmas 1 and 2), what a manifold with boundary is and that solution
sets in it are again manifolds with boundary (Lemmas 3 and 4), and that a compact 1-manifold has
an even number of endpoints (the Appendix).

---

## 1. Regular values when the dimensions differ (Milnor p. 10)

In Chapter 1 the domain and target had the same dimension, so "$df_x$ invertible" made sense.
Now let $f : M \to N$ be smooth with $\dim M = m \ge n = \dim N$.

**Definition.** A point $x \in M$ is a *regular point* if $df_x : TM_x \to TN_{f(x)}$ is
surjective, and a *critical point* otherwise. A point $y \in N$ is a *regular value* if every
point of $f^{-1}(y)$ is regular, and a *critical value* otherwise. When $m = n$, surjective and
invertible are the same for a linear map between spaces of equal finite dimension, so this agrees
with Chapter 1. When $m < n$, every point is critical.

**Theorem 1.1 (Sard, Brown).** Let $M$ and $N$ be smooth manifolds without boundary, $M$ covered
by countably many charts (for instance any subset of $\mathbb R^k$), and $f : M \to N$ smooth.
Then the regular values of $f$ are dense in $N$: every nonempty open subset of $N$ contains one.

This is the theorem that guarantees the regular values we need below actually exist. Its proof is
the whole of Chapter 3. Nothing in the present chapter depends on how it is proved.

---

## 2. Level sets are manifolds (Milnor pp. 11–12)

**Lemma 2.1 (Milnor's Lemma 1).** Let $f : M \to N$ be smooth, $m \ge n$, and $y$ a regular
value. Then $f^{-1}(y) \subseteq M$ is a smooth manifold of dimension $m - n$.

*Proof.* Let $x \in f^{-1}(y)$. Since $df_x : TM_x \to TN_y$ is onto, its kernel $\mathcal N$ has
dimension $m - n$ (rank–nullity). Regard $M \subseteq \mathbb R^k$ and choose a linear map
$L : \mathbb R^k \to \mathbb R^{m-n}$ whose restriction to $\mathcal N$ is an isomorphism (extend a
basis of $\mathcal N$ to a basis of $\mathbb R^k$, send the basis of $\mathcal N$ to the standard
basis of $\mathbb R^{m-n}$ and the other basis vectors to $0$). Define

$$F : M \to N \times \mathbb R^{m-n}, \qquad F(\xi) = (f(\xi), L(\xi)).$$

The target is a manifold of dimension $n + (m - n) = m$, and $dF_x(v) = (df_x(v), L(v))$. This is
injective: if $df_x(v) = 0$ then $v \in \mathcal N$, and then $L(v) = 0$ forces $v = 0$. An
injective linear map between spaces of the same dimension $m$ is an isomorphism, so by the inverse
function theorem (Chapter 1, Theorem 4.1) $F$ maps a neighbourhood $U$ of $x$ in $M$
diffeomorphically onto a neighbourhood $V$ of $(y, L(x))$.

Under $F$, the set $f^{-1}(y) \cap U$ corresponds exactly to $(\{y\} \times \mathbb R^{m-n}) \cap V$:
a point $\xi \in U$ has $f(\xi) = y$ if and only if the first component of $F(\xi)$ is $y$. The
set $\{z \in \mathbb R^{m-n} : (y, z) \in V\}$ is open in $\mathbb R^{m-n}$, and
$z \mapsto F^{-1}(y, z)$ is a diffeomorphism from it onto $f^{-1}(y) \cap U$ (it is the
restriction of the diffeomorphism $F^{-1}$ to a subset, and its inverse is $\xi \mapsto L(\xi)$,
the restriction of a linear map). That is a parametrization of $f^{-1}(y)$ near $x$. $\square$

Charts of this kind, in which the level set becomes a coordinate slice $\{y\} \times \mathbb R^{m-n}$,
are called *slice charts*. The lemma says a level set at a regular value is covered by slice
charts, and that is what makes it a manifold.

**Example.** $f(x) = x_1^2 + \dots + x_m^2$ on $\mathbb R^m$ has $df_x(v) = 2\langle x, v\rangle$,
which is onto $\mathbb R$ whenever $x \ne 0$. So every $y \ne 0$ is a regular value, and
$f^{-1}(1) = S^{m-1}$ is a manifold of dimension $m - 1$. This is a shorter proof than the six
hemispheres of Chapter 1, and it works in every dimension at once.

**Lemma 2.2 (Milnor's Lemma 2).** In the situation of Lemma 2.1, the tangent space of
$M' = f^{-1}(y)$ at $x$ is the kernel of $df_x$.

*Proof.* Let $i : M' \to M$ be the inclusion, which is smooth (it is the restriction of the
identity of $\mathbb R^k$). The composition $f \circ i$ is the constant map with value $y$, so its
derivative is zero: $df_x \circ di_x = 0$. Hence $di_x(TM'_x) \subseteq \ker df_x$. Now
$di_x$ is injective (in the parametrization $z \mapsto F^{-1}(y,z)$ of the proof above,
$L \circ i$ is the coordinate map, so $L \circ di_x$ is the identity of $\mathbb R^{m-n}$ in
coordinates), so $di_x(TM'_x)$ has dimension $m - n$, the same as $\ker df_x$. A subspace of the
same dimension is the whole space. $\square$

---

## 3. Manifolds with boundary (Milnor pp. 12–13)

The disk has an edge; the ball has a skin. To talk about them we need manifolds that look, close
up, like a half-space near some points.

Let $H^m = \{x \in \mathbb R^m : x_m \ge 0\}$ be the closed half-space, with boundary
$\partial H^m = \{x : x_m = 0\}$.

**Definition.** A subset $X \subseteq \mathbb R^k$ is a *smooth $m$-manifold with boundary* if
every $x \in X$ has a neighbourhood $W \cap X$ ($W$ open in $\mathbb R^k$) diffeomorphic to a
relatively open subset $V \cap H^m$ of $H^m$ ($V$ open in $\mathbb R^m$). The *boundary*
$\partial X$ is the set of points of $X$ that correspond to points of $\partial H^m$ under such a
diffeomorphism; the *interior* is $X \setminus \partial X$.

(Smoothness of a map on $V \cap H^m$ means, as always, local extendability to a smooth map on an
open subset of $\mathbb R^m$.)

Milnor writes: "It is not hard to show that $\partial X$ is a well-defined smooth manifold of
dimension $m - 1$." Well-defined means that whether $x$ is a boundary point cannot depend on
which chart we look through. Here is the argument he had in mind.

**Claim 3.1.** No point of $X$ corresponds to a boundary point of $H^m$ under one chart and to an
interior point under another.

*Proof.* Suppose $\varphi : W_1 \cap X \to V_1 \cap H^m$ and $\psi : W_2 \cap X \to V_2 \cap H^m$
are two charts around $x$ with $\varphi(x)_m > 0$ and $\psi(x)_m = 0$. Choose an open ball $B$
around $\varphi(x)$ in $\mathbb R^m$ so small that $B \subseteq \{x_m > 0\}$ and
$B \subseteq \varphi(W_1 \cap W_2 \cap X)$. The change of coordinates
$\tau := \psi \circ \varphi^{-1} : B \to H^m$ is smooth in the ordinary sense, since $B$ is open
in $\mathbb R^m$. Its inverse $\varphi \circ \psi^{-1}$ is smooth on $\tau(B) \ni \psi(x)$, so it
extends to a smooth map $\sigma$ on an open neighbourhood of $\psi(x)$ in $\mathbb R^m$ agreeing
with $\varphi \circ \psi^{-1}$ on the part inside $H^m$. Then $\sigma \circ \tau$ is the identity
on a neighbourhood of $\varphi(x)$ in $B$, so by the chain rule $d\sigma \circ d\tau = \mathrm{id}$,
and $d\tau_{\varphi(x)}$ is injective, hence invertible. By the inverse function theorem, $\tau$
maps a small ball $B' \subseteq B$ onto an open subset of $\mathbb R^m$. That open set contains
$\psi(x)$, whose last coordinate is $0$, and is contained in $\tau(B) \subseteq H^m$. But no open
subset of $\mathbb R^m$ containing a point with $x_m = 0$ lies inside $\{x_m \ge 0\}$: it
contains points with $x_m < 0$. Contradiction. $\square$

So the boundary is well defined. That it is an $(m-1)$-manifold is immediate: a chart
$\varphi : W \cap X \to V \cap H^m$ restricts to a bijection $W \cap \partial X \to V \cap \partial H^m$
(by Claim 3.1, boundary points go exactly to boundary points), and $V \cap \partial H^m$ is an open
subset of $\partial H^m = \mathbb R^{m-1}$; the restriction and its inverse are smooth as
restrictions of smooth maps. Similarly, the interior of $X$ is an $m$-manifold without boundary.

**Lemma 3.2 (Milnor's Lemma 3).** Let $M$ be a manifold without boundary and $g : M \to \mathbb R$
smooth with $0$ a regular value. Then $\{x \in M : g(x) \ge 0\}$ is a manifold with boundary, and
its boundary is $g^{-1}(0)$.

*Proof.* Write $X = \{g \ge 0\}$. At a point with $g(x) > 0$: by continuity a neighbourhood of
$x$ in $M$ lies inside $X$, and a chart of $M$ there, composed with a translation to move the
image into $\{x_m > 0\}$, is a chart of $X$ of the required kind, sending $x$ to an interior
point of $H^m$. At a point with $g(x) = 0$: run the proof of Lemma 2.1 with $f = g$, $n = 1$,
target $\mathbb R$. The map $F = (g, L) : M \to \mathbb R \times \mathbb R^{m-1}$ is a
diffeomorphism from a neighbourhood $U$ of $x$ onto a neighbourhood $V$ of $(0, L(x))$, and it
carries $X \cap U = \{g \ge 0\} \cap U$ onto $V \cap \{t \ge 0\}$, which, after the coordinate
swap putting $t$ last, is a relatively open subset of $H^m$. Under this chart, points with
$g = 0$ are exactly the points with $t = 0$, that is, the boundary points. So $X$ is a manifold
with boundary and $\partial X = g^{-1}(0)$. $\square$

**Example: the disk.** $D^m = \{x \in \mathbb R^m : \|x\| \le 1\} = \{g \ge 0\}$ with
$g(x) = 1 - \|x\|^2$. We have $dg_x(v) = -2\langle x, v\rangle$, which is onto $\mathbb R$ whenever
$x \ne 0$, in particular whenever $g(x) = 0$. So $0$ is a regular value, $D^m$ is an
$m$-manifold with boundary, and $\partial D^m = g^{-1}(0) = S^{m-1}$.

---

## 4. Level sets in a manifold with boundary (Milnor p. 13)

**Lemma 4.1 (Milnor's Lemma 4).** Let $X$ be an $m$-manifold with boundary, $N$ an $n$-manifold
without boundary, $m > n$, and $f : X \to N$ smooth. Suppose $y \in N$ is a regular value both
of $f$ and of the restriction $f|_{\partial X} : \partial X \to N$. Then $f^{-1}(y)$ is an
$(m-n)$-manifold with boundary, and its boundary is $f^{-1}(y) \cap \partial X$.

*Proof.* The statement is local: it says every point of $f^{-1}(y)$ has a neighbourhood of a
certain kind. Through charts of $X$ and $N$ we may therefore assume $X$ is a relatively open
subset of $H^m$ and $N = \mathbb R^n$.

*Interior points.* At a point $\bar x$ of $f^{-1}(y)$ with $\bar x_m > 0$, a neighbourhood of
$\bar x$ in $X$ is open in $\mathbb R^m$, and Lemma 2.1 gives a slice chart there: near $\bar x$,
$f^{-1}(y)$ is an $(m-n)$-manifold without boundary.

*Boundary points.* Let $\bar x \in f^{-1}(y)$ with $\bar x_m = 0$. Since $f$ is smooth on $X$,
there is an open neighbourhood $U$ of $\bar x$ in $\mathbb R^m$ and a smooth
$g : U \to \mathbb R^n$ agreeing with $f$ on $U \cap X$. At $\bar x$, $dg_{\bar x} = df_{\bar x}$ is
surjective. Surjectivity of a linear map is an open condition (it is the nonvanishing of some
$n \times n$ minor of the matrix, a continuous function of the entries), so after shrinking $U$
we may assume $dg_u$ is surjective for every $u \in U$: then $y$ is a regular value of $g$, and
by Lemma 2.1, $g^{-1}(y) \subseteq U$ is a smooth manifold of dimension $m - n$ without boundary.

Let $\pi : g^{-1}(y) \to \mathbb R$ be the restriction of the last coordinate, $\pi(u) = u_m$.
It is smooth. We claim that **$0$ is a regular value of $\pi$**. Let $u \in g^{-1}(y)$ with
$u_m = 0$; we must show $d\pi_u$ is nonzero on the tangent space $T(g^{-1}(y))_u$, which by
Lemma 2.2 is $\ker dg_u$. Suppose instead $d\pi_u$ vanished on $\ker dg_u$. Since $d\pi_u$ is
the restriction of the linear functional $v \mapsto v_m$, this says
$\ker dg_u \subseteq \{v : v_m = 0\} = T(\partial H^m)_u$. Now $u \in X \cap \partial H^m =
\partial X$ near $\bar x$, and $g = f$ on $X$, so $d(f|_{\partial X})_u$ is the restriction of
$dg_u$ to $T(\partial H^m)_u$. Its kernel is $\ker dg_u \cap T(\partial H^m)_u = \ker dg_u$,
which has dimension $m - n$. By rank–nullity applied to the restriction, whose domain has
dimension $m - 1$, its rank is $(m - 1) - (m - n) = n - 1 < n$. So $d(f|_{\partial X})_u$ is not
surjective, contradicting the hypothesis that $y$ is a regular value of $f|_{\partial X}$.

Now apply Lemma 3.2 to the manifold $g^{-1}(y)$ (without boundary, dimension $m - n$) and the
function $\pi$: the set $\{u \in g^{-1}(y) : \pi(u) \ge 0\} = g^{-1}(y) \cap H^m = f^{-1}(y) \cap U$
is an $(m-n)$-manifold with boundary $\pi^{-1}(0) = f^{-1}(y) \cap U \cap \partial H^m =
f^{-1}(y) \cap \partial X \cap U$. This is the required local statement at $\bar x$. $\square$

> **Where the boundary hypothesis is used.** Without regularity of $y$ for $f|_{\partial X}$ the
> lemma is false: take $X = H^2$, $N = \mathbb R$, $f(x_1, x_2) = x_2 - x_1^2$. Then $0$ is a regular
> value of $f$, and $f^{-1}(0)$ is the parabola $x_2 = x_1^2$, which touches $\partial X$ at the
> origin without crossing it. The parabola is a fine 1-manifold, but its intersection with
> $\partial X$ is a single point, not its boundary (it has none). The restriction $f|_{\partial X}
> (x_1, 0) = -x_1^2$ has $0$ as a critical value, so the lemma does not apply, and indeed its
> conclusion fails.

---

## 5. The Brouwer fixed point theorem (Milnor pp. 13–15)

One more input, about the simplest manifolds of all.

**Theorem 5.1 (classification of compact 1-manifolds; Milnor's Appendix).** Every compact
connected smooth 1-manifold with boundary is diffeomorphic either to the circle $S^1$ or to the
closed interval $[0,1]$. Consequently a compact smooth 1-manifold with boundary has finitely many
components, and its boundary consists of an *even* number of points.

(A compact manifold has finitely many components because components are open, so they form an
open cover with no proper subcover. A circle has no boundary points and an interval has two.) The
proof is a page of careful analysis of arc-length parametrizations; it is given in full in the
chapter on the Appendix. Everything in this section rests on it.

**Lemma 5.2 (Milnor's Lemma 5).** Let $X$ be a compact manifold with boundary. There is no smooth
map $f : X \to \partial X$ with $f(x) = x$ for all $x \in \partial X$.

*Proof.* Suppose $f$ is such a map, and let $m = \dim X$, so that $\dim \partial X = m - 1$.

*Step 1: a regular value.* Apply Theorem 1.1 to the restriction of $f$ to the interior of $X$,
which is an $m$-manifold without boundary covered by countably many charts (as a subset of
$\mathbb R^k$), with target the $(m-1)$-manifold $\partial X$. Its regular values are dense, so
there is $y \in \partial X$ regular for $f|_{\text{int} X}$. This $y$ is regular for $f$ itself:
the points of $f^{-1}(y)$ are either interior, where regularity is given, or boundary points $x$,
where $x = f(x) = y$; and at $x = y$ the derivative $df_y$ restricted to $T(\partial X)_y$ is the
derivative of the identity, so $df_y$ is onto $T(\partial X)_y$. Moreover every point is a regular
value of $f|_{\partial X} = \mathrm{id}$.

*Step 2: the level set.* By Lemma 4.1 with $n = m - 1 < m$, $f^{-1}(y)$ is a smooth manifold of
dimension $1$ with boundary $f^{-1}(y) \cap \partial X$. Since $f$ is the identity on $\partial X$,
a boundary point $x$ has $f(x) = y$ only if $x = y$; so the boundary of $f^{-1}(y)$ is the single
point $\{y\}$. And $f^{-1}(y)$ is compact: it is closed in the compact space $X$, being the
preimage of the closed set $\{y\}$.

*Step 3: contradiction.* A compact 1-manifold with boundary has an even number of boundary points
(Theorem 5.1). One is not even. $\square$

This is the rigorous form of the picture in §0: the curve $f^{-1}(y)$ that "cannot end".

**Lemma 5.3 (Milnor's Lemma 6).** Every smooth map $g : D^n \to D^n$ has a fixed point.

*Proof.* Suppose $g(x) \ne x$ for all $x \in D^n$. We build a smooth retraction $f : D^n \to S^{n-1}$
and contradict Lemma 5.2. For $x \in D^n$ let

$$u = u(x) := \frac{x - g(x)}{\|x - g(x)\|},$$

the unit vector pointing from $g(x)$ toward $x$; it is smooth since the denominator never
vanishes. We want $f(x) = x + t\,u$ with $t \ge 0$ chosen so that $\|f(x)\| = 1$: the point where
the ray from $g(x)$ through $x$ leaves the disk. The condition $\|x + tu\|^2 = 1$ reads
$t^2 + 2t\,(x \cdot u) + (\|x\|^2 - 1) = 0$, a quadratic in $t$ with roots
$-x\cdot u \pm \sqrt{(x\cdot u)^2 + 1 - \|x\|^2}$. Take the root with the plus sign:

$$t(x) := -x\cdot u + \sqrt{1 - \|x\|^2 + (x\cdot u)^2}, \qquad f(x) := x + t(x)\,u(x).$$

Milnor writes that it is "easy to verify" that this works. Here is the verification.

*The square root is of a positive quantity, so $t$ and $f$ are smooth.* The radicand
$1 - \|x\|^2 + (x\cdot u)^2$ is a sum of two nonnegative terms, and it vanishes only if
$\|x\| = 1$ and $x \cdot u = 0$. Suppose $\|x\| = 1$. Then
$x \cdot u = (1 - x\cdot g(x))/\|x - g(x)\|$, and $x \cdot g(x) \le \|x\|\,\|g(x)\| \le 1$ by
Cauchy–Schwarz, with equality only if $g(x) = \lambda x$ with $\lambda \ge 0$ and $\|g(x)\| = 1$,
that is, $g(x) = x$, which is excluded. So $x \cdot u > 0$ on the sphere, and the radicand is
positive everywhere on $D^n$. Positive radicand, smooth radicand, so smooth square root; and
$g$ is smooth on $D^n$ in the sense of local extension, so all of this extends smoothly to a
neighbourhood of each point.

*$f$ takes values in $S^{n-1}$.* By construction $t$ solves the quadratic, so $\|f(x)\| = 1$.

*$f$ fixes the sphere.* If $\|x\| = 1$ then $1 - \|x\|^2 = 0$, so
$t = -x\cdot u + |x \cdot u| = 0$ because $x \cdot u > 0$. Hence $f(x) = x$.

So $f : D^n \to S^{n-1} = \partial D^n$ is a smooth retraction, which Lemma 5.2 forbids. $\square$

(The geometric meaning of $t \ge 0$ everywhere: in the interior, $t > -x\cdot u + |x\cdot u| \ge 0$,
so $f(x)$ really is the exit point of the ray in the forward direction $u$.)

**Theorem 5.4 (Brouwer).** Every continuous map $G : D^n \to D^n$ has a fixed point.

*Proof.* Suppose not. The function $x \mapsto \|G(x) - x\|$ is continuous and positive on the
compact set $D^n$, so it attains a minimum $\mu > 0$. By the Weierstrass approximation theorem
(polynomials are dense in the continuous functions on a compact subset of $\mathbb R^n$; apply it
to each of the $n$ components), there is a polynomial map $P_1 : \mathbb R^n \to \mathbb R^n$ with
$\|P_1(x) - G(x)\| < \mu/2$ for all $x \in D^n$. This $P_1$ may leave the disk, but not by much:
$\|P_1(x)\| < 1 + \mu/2$. So set

$$P(x) := \frac{P_1(x)}{1 + \mu/2}.$$

Then $\|P(x)\| < 1$, so $P$ maps $D^n$ into itself, and $P$ is smooth (a polynomial). Also

$$\|P(x) - P_1(x)\| = \frac{\mu/2}{1 + \mu/2}\,\|P_1(x)\| < \mu/2,
\qquad\text{so}\qquad
\|P(x) - G(x)\| < \mu/2 + \mu/2 = \mu.$$

Hence $\|P(x) - x\| \ge \|G(x) - x\| - \|P(x) - G(x)\| > \mu - \mu = 0$ for every $x$: the smooth
map $P : D^n \to D^n$ has no fixed point. This contradicts Lemma 5.3. $\square$

So the crumpled map has a point over its own location, however it fell. Notice what the proof did
*not* need: it never found the fixed point, and it never needed the map to be injective, or to
preserve anything. It needed only continuity, compactness, and the parity of endpoints of a curve.

---

## 6. An interactive look at the proof

The figure shows a disk and a smooth map $g$ of the disk to itself: a contraction by the factor
$0.55$, followed by a rotation and a shift, so $g(x) = c + 0.55\,R_\varphi x$. The faint arrows
show $x \mapsto g(x)$ at a grid of points. The one fixed point of $g$ is marked.

Choose a boundary point $y$ with the slider. The thick curve is $f^{-1}(y)$: the set of points
$x$ for which the ray from $g(x)$ through $x$ exits the disk at $y$. It starts at $y$ (where
$f(y) = y$), runs into the disk, and ends at the fixed point of $g$, where the construction of $f$
breaks down because the ray has no direction. The faint curves are $f^{-1}(y')$ for other
boundary points $y'$; all of them end at the same place. If $g$ had no fixed point, none of these
curves could end anywhere, and each would be a compact 1-manifold with exactly one boundary point.
Change the rotation and the shift and watch the fixed point move; the curves follow it.

<div id="brouwer-figure"></div>

*(In the printed version this figure is a still image; the interactive version is in the web
edition.)*

---

## 7. Application: every finite Markov chain has a stationary distribution

Brouwer's theorem is an existence theorem: it says an equilibrium exists without saying where. That
is exactly what the theory of random processes, and of economics, needs from it.

**Convex bodies are disks.** Brouwer's theorem was proved for the round disk, but the sets that
occur in applications are simplices and other convex bodies. The transfer is a lemma.

**Lemma 7.1.** Let $K \subseteq \mathbb R^d$ be compact, convex, and contain a ball around $0$.
Then there is a homeomorphism $h : K \to D^d$. Consequently every continuous map $K \to K$ has a
fixed point.

*Proof.* Choose $r, R > 0$ with $B(0, r) \subseteq K \subseteq B(0, R)$. Define the *gauge*
$\rho(v) := \inf\{t > 0 : v/t \in K\}$ for $v \in \mathbb R^d$. Three properties. (i) $\rho(\lambda v) =
\lambda\rho(v)$ for $\lambda \ge 0$, directly from the definition. (ii) $\|v\|/R \le \rho(v) \le
\|v\|/r$, because $v/t \in B(0,R)$ forces $t \ge \|v\|/R$, and $v/t \in B(0,r) \subseteq K$ as
soon as $t > \|v\|/r$. (iii) $\rho(v + w) \le \rho(v) + \rho(w)$: if $v/s, w/t \in K$ then
$(v+w)/(s+t) = \frac{s}{s+t}\,\frac{v}{s} + \frac{t}{s+t}\,\frac{w}{t} \in K$ by convexity. From
(ii) and (iii), $|\rho(v) - \rho(w)| \le \rho(v - w)$ or $\rho(w - v)$, each at most
$\|v - w\|/r$, so $\rho$ is continuous. Finally $K = \{\rho \le 1\}$: if $v \in K$ then $\rho(v)
\le 1$. Conversely let $\rho(v) \le 1$. If $v = 0$ then $v \in K$. Otherwise $\rho(v) > 0$ by
(ii), and there are $t_k \downarrow \rho(v)$ with $v/t_k \in K$; since $K$ is closed,
$v/\rho(v) \in K$, and then $v = \rho(v)\,(v/\rho(v)) + (1 - \rho(v))\,0 \in K$ by
convexity.

Now define $h(v) := \rho(v)\,v/\|v\|$ for $v \ne 0$ and $h(0) := 0$. It is continuous away from
$0$, and near $0$ we have $\|h(v)\| = \rho(v) \le \|v\|/r \to 0$. It maps $K$ into $D^d$ since
$\|h(v)\| = \rho(v) \le 1$, and its inverse is $w \mapsto \|w\|\,w/\rho(w)$ (for $w \ne 0$; $0
\mapsto 0$), which is continuous by the same estimates and maps $D^d$ into $K$ because
$\rho(\|w\| w/\rho(w)) = \|w\| \le 1$. So $h$ is a homeomorphism. If $T : K \to K$ is continuous,
then $h \circ T \circ h^{-1} : D^d \to D^d$ has a fixed point $w$ by Theorem 5.4, and
$h^{-1}(w)$ is a fixed point of $T$. $\square$

**The theorem.** A *stochastic matrix* is an $n \times n$ matrix $A$ with entries $a_{ij} \ge 0$
and each column summing to $1$: $a_{ij}$ is the probability of moving to state $i$ from state $j$.
If $v$ is a probability vector (entries $\ge 0$, summing to $1$) describing where the system is now,
then $Av$ describes where it is one step later. A *stationary distribution* is a probability vector
$v$ with $Av = v$: a distribution the chain leaves unchanged.

**Theorem 7.2.** Every stochastic matrix has a stationary distribution.

*Proof.* Let $\Delta = \{v \in \mathbb R^n : v_i \ge 0,\ \sum v_i = 1\}$, the set of probability
vectors. It is compact (closed and bounded) and convex (a convex combination of probability
vectors is one). Inside the hyperplane $E = \{\sum v_i = 1\} \cong \mathbb R^{n-1}$ it contains a
ball around the point $p = (1/n, \dots, 1/n)$: all points of $E$ within distance $1/n$ of $p$ have
positive entries. Translating $p$ to the origin, Lemma 7.1 applies with $d = n - 1$.

The map $v \mapsto Av$ is continuous and carries $\Delta$ into $\Delta$: the entries of $Av$ are
nonnegative, and $\sum_i (Av)_i = \sum_j \bigl(\sum_i a_{ij}\bigr) v_j = \sum_j v_j = 1$. By
Lemma 7.1 it has a fixed point. $\square$

**Perron–Frobenius, weak form.** The same argument with $T(v) := Av / \sum_i (Av)_i$ shows: any
matrix with nonnegative entries, such that $Av \ne 0$ for every nonzero $v \ge 0$ (for instance,
no zero column), has an eigenvector with nonnegative entries and a positive eigenvalue
$\lambda = \sum_i (Av)_i$. Here $T$ is continuous on $\Delta$ because the denominator is a
positive continuous function there.

**What it is used for.**

* *Web search.* Google's original PageRank is the stationary distribution of a random surfer who
  follows links at random; the matrix is stochastic by construction (with a small "teleportation"
  term added so that it is strictly positive, which also makes the stationary distribution unique,
  a fact this argument does not give). Theorem 7.2 says the ranking exists for every web graph.
* *Population biology.* A Leslie matrix records survival and fertility rates by age class. Its
  Perron eigenvector is the stable age distribution a population converges to, and the eigenvalue
  is the long-run growth rate. Existence is Theorem 7.2's argument; uniqueness and convergence
  need the full Perron–Frobenius theorem.
* *Economics.* Nash's 1950 proof that every finite game has an equilibrium in mixed strategies is
  a page long, and its content is a fixed point theorem applied to the product of the players'
  simplices, a convex body. The existence of equilibrium prices in a market economy (Arrow and
  Debreu, 1954) is proved the same way. In each case the theorem promises that an equilibrium
  exists; finding it is a separate and often hard problem, exactly as the proof of Lemma 5.3
  never located the fixed point.

---

## 8. Summary of what was silently assumed, now made explicit

| Where | Milnor says | What is actually needed |
|---|---|---|
| p. 11 | "$f^{-1}(y)$ is a smooth manifold" | the slice chart $F = (f, L)$ and the inverse function theorem on manifolds (Lemma 2.1) |
| p. 12 | "$\partial X$ is a well-defined smooth manifold" | invariance of interior points under changes of chart, via the inverse function theorem (Claim 3.1) |
| p. 13 | "the hypotheses of Lemma 3 are satisfied" for $\pi$ | a dimension count using Lemma 2.2 and regularity of $y$ for $f|_{\partial X}$ (Lemma 4.1) |
| p. 13 | Sard's theorem gives a regular value $y \in \partial X$ | apply it to the interior of $X$; boundary points are automatically regular since $f = \mathrm{id}$ there (Lemma 5.2, Step 1) |
| p. 14 | "it is easy to verify" that $f$ is smooth and fixes $S^{n-1}$ | the radicand is positive, using Cauchy–Schwarz (Lemma 5.3) |
| p. 14 | "$P$ maps $D^n$ into $D^n$" | the rescaling by $1 + \mu/2$ and the triangle inequality (Theorem 5.4) |
| p. 14 | a compact 1-manifold has an even number of boundary points | the Appendix (Theorem 5.1) |

**Checked by machine.** Everything in this chapter has been verified in the Lean proof assistant as
part of this project: Lemmas 2.1, 2.2, 3.2 and 4.1, the disk example, the no-retraction lemma, the
retraction built from a map without fixed points, and Brouwer's theorem for smooth and for
continuous maps. This includes the construction of the slice charts and half-slice charts that
Milnor's "this proves that $f^{-1}(y)$ is a manifold" hides. The text does not depend on this. The
verified edition (§3) states each result as checked, and *Milnor, proof by proof* (Part I) tells
how the formal proofs go.