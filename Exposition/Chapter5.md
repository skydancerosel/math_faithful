# Chapter 5. Counting with signs: oriented manifolds and the Brouwer degree

*Milnor, "Topology from the Differentiable Viewpoint", §5, rewritten for a first-year student who
wants to know what the theorem is for. Every proof is complete.*

---

## 0. Somewhere on Earth the wind is not blowing

At any moment, the wind at the surface of the Earth assigns to each point a horizontal arrow. The
claim: somewhere the arrow has length zero. Not on average, not usually, but at every instant, at
some point of the globe, the air is perfectly still.

This is the *hairy ball theorem*: a smooth field of tangent vectors on the sphere $S^2$ must vanish
somewhere. You cannot comb a hairy ball flat without a parting or a whorl. The proof in this
chapter is Brouwer's, from 1912, and it goes like this. If the wind never stopped, you could slide
every point of the globe along its wind arrow, further and further, until each point had travelled
half way around and arrived at its antipode. That is a smooth deformation of the identity map of
the sphere into the antipodal map $x \mapsto -x$. But the antipodal map turns the sphere inside
out, and the identity does not, and no continuous deformation can change that.

"Turns inside out" is a statement about orientation, and the last chapter's invariant, the degree
modulo 2, cannot see it: both the identity and the antipodal map hit every point exactly once, so
both have degree $1 \bmod 2$. To separate them we must count the solutions of $f(x) = y$ *with
signs*, $+1$ where $f$ preserves orientation and $-1$ where it reverses it. The signed count is the
*Brouwer degree*, an integer. This chapter defines it, proves that it does not depend on $y$ and
does not change under deformation, and computes it for the antipodal map. The sphere theorem
follows. At the end, the same integer explains why the circulation of a superfluid vortex comes in
exact multiples of Planck's constant divided by the mass of the atom.

---

## 1. Orientations (Milnor pp. 26–27)

**Vector spaces.** An *orientation* of a finite-dimensional real vector space $V$ of dimension
$n \ge 1$ is an equivalence class of ordered bases, where $(b_1, \dots, b_n)$ and
$(b'_1, \dots, b'_n)$ are equivalent if $b'_i = \sum_j a_{ij} b_j$ with $\det(a_{ij}) > 0$. Since
the determinant of a change of basis is nonzero and multiplicative, this is an equivalence relation
with exactly two classes. A basis in the chosen class is *positively oriented*. The space
$\mathbb R^n$ has its standard orientation, that of $(e_1, \dots, e_n)$. For the zero-dimensional
space, an orientation is by definition a sign, $+1$ or $-1$.

An isomorphism $L : V \to W$ between oriented spaces of the same dimension *preserves* orientation
if it carries positive bases to positive bases, and *reverses* it otherwise; write $\operatorname{sign} L
= \pm 1$ accordingly. For $V = W$, $\operatorname{sign} L = \operatorname{sign}\det L$. Signs multiply
under composition.

**Manifolds.** An *oriented manifold* is a manifold $M$ with a choice of orientation of each
tangent space $TM_x$, which fit together: every point has a neighbourhood $U$ and a chart
$h : U \to \mathbb R^m$ (or $H^m$) such that each $dh_x$ carries the orientation of $TM_x$ to the
standard orientation of $\mathbb R^m$. A manifold that admits an orientation is *orientable*. A
connected orientable manifold has exactly two orientations: the set where two orientations agree is
open (by the chart condition) and so is the set where they disagree, and one of them is empty.

**Boundaries.** Let $M$ be an oriented manifold with boundary and $x \in \partial M$. In a boundary
chart $h : U \to H^m$ with $h(x) \in \partial H^m$, a tangent vector $v \in TM_x$ is *inward* if
the last coordinate of $dh_x(v)$ is positive, *outward* if it is negative, and *tangent to the
boundary* if it is zero.

**Claim 1.1.** These three classes do not depend on the chart.

*Proof.* Let $h, h'$ be two boundary charts around $x$ and $\tau = h' \circ h^{-1}$ the change of
coordinates, a diffeomorphism between relatively open subsets of $H^m$ carrying boundary points to
boundary points (Chapter 2, Claim 3.1) and interior points to interior points. Let $u = h(x)$ and
let $w$ be a vector with $w_m > 0$. For small $t \ge 0$ the point $u + tw$ lies in $H^m$, so
$\tau(u + tw)_m \ge 0$, with equality at $t = 0$; differentiating at $t = 0$ gives
$(d\tau_u w)_m \ge 0$. Since $\tau$ carries $\partial H^m$ into itself, $d\tau_u$ carries
$T(\partial H^m) = \{w_m = 0\}$ into itself, and being invertible it carries the complement to the
complement; so $(d\tau_u w)_m \ne 0$, hence $> 0$. Thus inward vectors go to inward vectors, and by
the same argument applied to $\tau^{-1}$, outward to outward. $\square$

**Definition (induced orientation of the boundary).** For $x \in \partial M$ and $m \ge 2$, choose
a positively oriented basis $(v_1, \dots, v_m)$ of $TM_x$ with $v_1$ outward and $v_2, \dots, v_m$
tangent to $\partial M$. Then $(v_2, \dots, v_m)$ is declared a positive basis of $T(\partial M)_x$.
For $m = 1$, a boundary point gets the orientation $+1$ if a positively oriented vector at it points
outward, and $-1$ if inward.

**Claim 1.2.** This is well defined, and makes $\partial M$ an oriented manifold.

*Proof.* Let $(v_1, \dots, v_m)$ and $(v'_1, \dots, v'_m)$ both be positive bases of the kind
described. Write $v'_1 = a v_1 + (\text{tangent vector})$ and $v'_i = \sum_{j \ge 2} a_{ij} v_j$
for $i \ge 2$ (possible since $v_2, \dots, v_m$ span the tangent space of the boundary). Both $v_1$
and $v'_1$ are outward, so $a > 0$: the outward vectors form a half-space bounded by
$T(\partial M)_x$. The change-of-basis matrix is block triangular with $a$ in the corner and
$(a_{ij})_{i,j \ge 2}$ as the other block, so its determinant $a \cdot \det(a_{ij})$ is positive,
hence $\det(a_{ij}) > 0$: the two boundary bases define the same orientation. The chart condition
for $\partial M$ holds because an orientation-preserving boundary chart $h$ of $M$ sends
$T(\partial M)_x$ onto $\mathbb R^{m-1} \times \{0\}$ and the outward vector $v_1$ to a vector
$(\ast, -c)$ with $c > 0$; expanding the determinant of the positive basis $(dh\,v_1, dh\,v_2,
\dots, dh\,v_m)$ along its last row, whose only nonzero entry is $-c$, shows that the
$(m-1) \times (m-1)$ matrix formed by $dh\,v_2, \dots, dh\,v_m$ has determinant of sign
$(-1)^m$, the same at every boundary point. So $h|_{\partial M}$, composed with a fixed reflection
of $\mathbb R^{m-1}$ when $m$ is odd, is an orientation-preserving chart of $\partial M$.
$\square$

**Example.** Orient $D^m$ as an open subset of $\mathbb R^m$ (standard). At $x \in S^{m-1}$ the
outward vector is $x$ itself, so $(w_2, \dots, w_m)$ tangent to the sphere is positive iff
$(x, w_2, \dots, w_m)$ is a positive basis of $\mathbb R^m$. This is the standard orientation of
$S^{m-1}$; for $S^1$ it is counterclockwise.

---

## 2. The degree (Milnor pp. 27–28)

Let $M$ and $N$ be oriented $n$-manifolds without boundary, $M$ compact, $N$ connected, and
$f : M \to N$ smooth. At a regular point $x$, $df_x : TM_x \to TN_{f(x)}$ is an isomorphism of
oriented spaces, and $\operatorname{sign} df_x = \pm 1$ is defined. For a regular value $y$ put

$$\deg(f; y) := \sum_{x \in f^{-1}(y)} \operatorname{sign} df_x \in \mathbb Z,$$

a finite sum by Chapter 1, Theorem 5.1. Reducing modulo 2 gives $\#f^{-1}(y) \bmod 2$, the
invariant of Chapter 4.

**Claim 2.1.** $\deg(f; y)$ is a locally constant function of $y$ on the set of regular values.

*Proof.* In the proof of Chapter 1, Theorem 5.2, we found a neighbourhood $V$ of $y$ and
diffeomorphisms $L_i : V \to U_i$, $i = 1, \dots, k$, inverse to $f$ on disjoint open sets $U_i$
around the points $x_i$ of $f^{-1}(y)$, such that $f^{-1}(y') = \{L_1(y'), \dots, L_k(y')\}$ for
all $y' \in V$. Shrink $V$ to be connected. On each $U_i$ the function $x \mapsto
\operatorname{sign} df_x$ is continuous with values in $\{\pm 1\}$ (in charts it is the sign of a
nonvanishing continuous determinant), and $U_i$ is connected (it is diffeomorphic to $V$), so it is
constant on $U_i$. Hence each term of the sum, and the sum, is the same at $y'$ as at $y$. $\square$

**Theorem A.** $\deg(f; y)$ does not depend on the regular value $y$. It is called the *degree*
of $f$, written $\deg f$.

**Theorem B.** If $f$ and $g$ are smoothly homotopic, then $\deg f = \deg g$.

The proofs run parallel to Chapter 4, with the orientations tracked. The key step is the following.

---

## 3. A map that extends over a filling has degree zero (Milnor pp. 28–29)

Suppose $M = \partial X$ for a compact oriented $(n+1)$-manifold $X$, with $M$ carrying the
induced orientation.

**Lemma 3.1 (Milnor's Lemma 1).** If $f : M \to N$ extends to a smooth $F : X \to N$, then
$\deg(f; y) = 0$ for every regular value $y$ of $f$.

*Proof.* **Case 1: $y$ is a regular value of $F$ too.** By Chapter 2, Lemma 4.1 (with $m = n+1$),
$F^{-1}(y)$ is a compact 1-manifold with boundary $F^{-1}(y) \cap \partial X = f^{-1}(y)$. By the
Appendix, it is a finite disjoint union of circles and arcs, and every point of $f^{-1}(y)$ is an
endpoint of exactly one arc. So it suffices to show that for each arc $A$ with endpoints $a, b$,

$$\operatorname{sign} df_a + \operatorname{sign} df_b = 0.$$

*Orienting the arc.* At $x \in A$ let $v_1 \in TA_x$ be a nonzero tangent vector to $A$. Since
$dF_x$ vanishes on $TA_x = \ker dF_x$ (Chapter 2, Lemma 2.2) and is onto $TN_y$, it induces an
isomorphism $TX_x / \mathbb R v_1 \cong TN_y$. Complete $v_1$ to a positive basis $(v_1, v_2,
\dots, v_{n+1})$ of $TX_x$; then $(dF_x v_2, \dots, dF_x v_{n+1})$ is a basis of $TN_y$, and we
declare $v_1$ *positive* for $A$ if this basis is positive for $N$. This does not depend on the
completion: if $(v_1, v'_2, \dots)$ is another positive basis, the change of basis is block
triangular with $1$ in the corner, so the $n \times n$ block relating $(v_i)_{i \ge 2}$ and
$(v'_i)_{i \ge 2}$ modulo $v_1$ has positive determinant, and it is also the matrix relating their
images under $dF_x$. Replacing $v_1$ by $-v_1$ flips the sign (then $(−v_1, v_2, \dots)$ is
negative, so use $(-v_1, -v_2, v_3, \dots)$, whose image basis differs by one sign). So exactly
one direction along $A$ is positive at each point, and it varies continuously: in a chart the
condition is the sign of a continuous nonvanishing determinant. Let $v_1(x)$ be the positive unit
tangent vector (unit with respect to the Euclidean norm of $\mathbb R^k \supseteq X$).

*The two ends.* Let $\gamma : [0,1] \to A$ be a diffeomorphism (Appendix), with $\gamma(0) = a$,
$\gamma(1) = b$. Then $\gamma'(s)$ and $v_1(\gamma(s))$ are both nonzero tangent vectors to $A$,
so $\gamma'(s) = \varepsilon(s)\,|\gamma'(s)|\,v_1(\gamma(s))$ with $\varepsilon(s) = \pm 1$
continuous, hence constant. Replacing $\gamma$ by $\gamma(1 - s)$ if necessary (which swaps the
names $a$ and $b$), we may assume $\varepsilon = +1$: $\gamma$ runs in the positive direction. Now
$\gamma'(0)$ points into $X$: in a boundary chart $\gamma(s)$ has nonnegative last coordinate for
$s \ge 0$, zero at $s = 0$, so the last coordinate of $\gamma'(0)$ is $\ge 0$, and it is nonzero
because, in the proof of Chapter 2, Lemma 4.1, the last coordinate restricted to the level set has
$0$ as a regular value. So $v_1(a)$ is inward. By the same argument at $s = 1$, $v_1(b)$ is
outward.

*The signs.* Take $x = b$. Choose a positive basis $(v_1, v_2, \dots, v_{n+1})$ of $TX_b$ with
$v_1 = v_1(b)$ and $(dF_b v_i)_{i \ge 2}$ positive in $TN_y$. Since $v_1$ is not tangent to
$\partial X$, every vector can be written as a multiple of $v_1$ plus a vector tangent to
$\partial X$; put $v'_i := v_i - c_i v_1$ tangent to $\partial X$ for $i \ge 2$. Then
$(v_1, v'_2, \dots, v'_{n+1})$ is still positive (unipotent change of basis), $dF_b v'_i = dF_b v_i$
because $dF_b v_1 = 0$, and $dF_b v'_i = df_b v'_i$ because $v'_i$ is tangent to $M = \partial X$
where $F = f$. As $v_1$ is outward, $(v'_2, \dots, v'_{n+1})$ is a positive basis of $TM_b$ by the
definition of the boundary orientation, and $df_b$ carries it to a positive basis of $TN_y$. So
$\operatorname{sign} df_b = +1$. At $x = a$ the same construction gives a positive basis
$(v_1, v'_2, \dots)$ of $TX_a$ with $v_1 = v_1(a)$ inward and $df_a$ carrying $(v'_i)_{i\ge2}$ to a
positive basis of $TN_y$; but now $-v_1$ is outward and $(-v_1, v'_2, \dots)$ is a negative basis,
so $(v'_2, \dots, v'_{n+1})$ is a *negative* basis of $TM_a$. Hence $\operatorname{sign} df_a = -1$.
The sum over the arc is zero, and summing over all arcs, $\deg(f; y) = 0$.

**Case 2: $y$ is regular for $f$ but not for $F$.** By Claim 2.1, $\deg(f; \cdot)$ is constant on
a neighbourhood $V$ of $y$ consisting of regular values of $f$ (the critical values of $f$ form a
closed set, as in Chapter 4). By Brown's theorem (Chapter 3), $V$ contains a regular value $y'$ of
$F$, which is also regular for $f$. By Case 1, $\deg(f; y) = \deg(f; y') = 0$. $\square$

---

## 4. Homotopy invariance, and the proofs of Theorems A and B (Milnor p. 29)

**Orienting the cylinder.** For an oriented $n$-manifold $M$ without boundary, orient
$X = [0,1] \times M$ by declaring $(\partial_t, v_1, \dots, v_n)$ positive whenever $(v_i)$ is
positive for $M$, where $\partial_t$ is the unit vector in the $[0,1]$ direction. Its boundary is
$\{1\} \times M \cup \{0\} \times M$. At $(1, x)$ the outward vector is $\partial_t$, so the
induced orientation of $\{1\} \times M$ is that of $M$. At $(0, x)$ the outward vector is
$-\partial_t$, and $(-\partial_t, v_1, \dots, v_n)$ is positive iff $(v_i)$ is negative for $M$;
so the induced orientation of $\{0\} \times M$ is the *opposite* of that of $M$.

**Lemma 4.1 (Milnor's Lemma 2).** Let $F : [0,1] \times M \to N$ be a smooth homotopy from $f$ to
$g$, and $y$ a regular value of both $f$ and $g$. Then $\deg(g; y) = \deg(f; y)$.

*Proof.* Apply Lemma 3.1 to $X = [0,1] \times M$ and the restriction of $F$ to $\partial X$. On
$\{1\} \times M$ this restriction is $g$ with the orientation of $M$, contributing $\deg(g; y)$;
on $\{0\} \times M$ it is $f$ with the opposite orientation, contributing $-\deg(f; y)$ (reversing
the orientation of the domain flips every sign). The total is zero. $\square$

**Proof of Theorem A.** Let $y, z$ be regular values of $f$. By the homogeneity lemma (Chapter 4,
Lemma 3.1) there is a diffeomorphism $h : N \to N$ with $h(y) = z$, smoothly isotopic to the
identity through diffeomorphisms $h_t$. Each $h_t$ preserves orientation: for fixed $x$, the
function $t \mapsto \operatorname{sign} d(h_t)_x$ is continuous with values $\pm 1$ on the connected
interval, and equals $+1$ at $t = 0$. Now $z$ is a regular value of $h \circ f$ (the preimage is
$f^{-1}(y)$, and $d(h \circ f)_x = dh_y \circ df_x$ is an isomorphism), and
$$\deg(h \circ f; z) = \sum_{x \in f^{-1}(y)} \operatorname{sign} dh_y \cdot \operatorname{sign} df_x
= \deg(f; y).$$
On the other hand $(x, t) \mapsto h_t(f(x))$ is a smooth homotopy from $f$ to $h \circ f$, and $z$
is regular for both, so Lemma 4.1 gives $\deg(h \circ f; z) = \deg(f; z)$. Hence
$\deg(f; y) = \deg(f; z)$. $\square$

**Proof of Theorem B.** Let $F$ be a homotopy from $f$ to $g$. The regular values of $f$ and of
$g$ are each open and dense in $N$ (dense by Brown; open because critical values form a closed set
when the domain is compact), so their intersection is nonempty. Pick $y$ in it. By Lemma 4.1 and
Theorem A, $\deg f = \deg(f; y) = \deg(g; y) = \deg g$. $\square$

---

## 5. Examples, and the hairy ball (Milnor pp. 29–31)

**Diffeomorphisms.** A diffeomorphism $f : M \to N$ has $f^{-1}(y)$ a single point for every $y$,
so $\deg f = \operatorname{sign} df_x = \pm 1$ according as $f$ preserves or reverses orientation
(the sign is constant by connectedness of $M$, which we assume here). **Consequently an
orientation-reversing diffeomorphism of a compact connected oriented manifold is not smoothly
homotopic to the identity** (Theorem B).

**Constant maps** have degree $0$: a value not attained is a regular value with empty preimage.

**Powers on the circle.** $f_k(z) = z^k$ on $S^1 \subseteq \mathbb C$. For $k \ne 0$, every $y$ has
exactly $|k|$ preimages, the $|k|$-th roots of $y$. In the angle coordinate, $f_k$ is $\theta
\mapsto k\theta$, with derivative $k$, so every preimage has sign $\operatorname{sign} k$, and
$\deg f_k = k$. For $k = 0$ the map is constant. So every integer is a degree.

**Reflections.** Let $r_i : S^n \to S^n$ change the sign of the $i$-th coordinate. It is a
diffeomorphism, and it reverses orientation. To see this, take a point $x$ with $x_i = 0$. Then
$r_i$ fixes $x$, the outward normal, and maps $TS^n_x = x^\perp$ to itself. If $(x, w_2, \dots,
w_{n+1})$ is a positive basis of $\mathbb R^{n+1}$ with the $w_j$ tangent, then $(x, r_i w_2, \dots,
r_i w_{n+1})$ is its image under $r_i$, a negative basis since $\det r_i = -1$. By the definition
of the boundary orientation, $(w_j)$ is a positive basis of $TS^n_x$ and $(r_i w_j)$ a negative
one: $r_i$ reverses orientation at $x$, hence everywhere, the sign being constant on the connected
sphere. So $\deg r_i = -1$.

**The antipodal map** $\alpha(x) = -x$ is $r_1 \circ r_2 \circ \dots \circ r_{n+1}$. The degree of
a composition of diffeomorphisms is the product of the degrees (the sign of a composition of
isomorphisms is the product of the signs), so

$$\deg \alpha = (-1)^{n+1}.$$

For $n$ even this is $-1$: **the antipodal map of an even-dimensional sphere is not smoothly
homotopic to the identity.** The degree modulo 2 could not see this; both maps have $\deg_2 = 1$.

**Theorem 5.1 (Brouwer's hairy ball theorem).** The sphere $S^n$ admits a smooth field of nowhere
vanishing tangent vectors if and only if $n$ is odd.

*Proof.* A tangent vector field on $S^n \subseteq \mathbb R^{n+1}$ is a smooth $v : S^n \to
\mathbb R^{n+1}$ with $v(x) \cdot x = 0$ for all $x$. Suppose $v(x) \ne 0$ everywhere. Replacing
$v$ by $v/\|v\|$ we may assume $\|v(x)\| = 1$. Define
$$F : S^n \times [0, \pi] \to \mathbb R^{n+1}, \qquad F(x, \theta) = x\cos\theta + v(x)\sin\theta.$$
Then $\|F(x,\theta)\|^2 = \cos^2\theta\,\|x\|^2 + 2\sin\theta\cos\theta\,(x\cdot v(x)) +
\sin^2\theta\,\|v(x)\|^2 = \cos^2\theta + \sin^2\theta = 1$, so $F$ maps into $S^n$; it is smooth;
$F(x, 0) = x$ and $F(x, \pi) = -x$. Rescaling $\theta$ to $[0,1]$, this is a smooth homotopy from
the identity to the antipodal map. By Theorem B, $(-1)^{n+1} = \deg\alpha = \deg \mathrm{id} = 1$,
so $n$ is odd.

Conversely, for $n = 2k - 1$ the formula
$$v(x_1, x_2, \dots, x_{2k-1}, x_{2k}) = (x_2, -x_1, x_4, -x_3, \dots, x_{2k}, -x_{2k-1})$$
is smooth, satisfies $v(x) \cdot x = \sum (x_{2j-1}x_{2j} - x_{2j}x_{2j-1}) = 0$, and has
$\|v(x)\| = \|x\| = 1$. $\square$

So the wind on Earth ($n = 2$) is calm somewhere. Incidentally, the proof shows the antipodal map
*is* homotopic to the identity for $n$ odd: slide along the field $v$.

> **Where the argument needs each ingredient.** Compactness of $S^n$: without it the count could
> leak to infinity. Orientability: without it there is no sign to count, and indeed the analogous
> statement for the real projective plane is different. Smoothness of the homotopy: Theorem B is
> about smooth homotopies, but Chapter 8, Problem 4, shows continuous homotopies can be smoothed,
> so nothing is lost.

### An interactive look at the signed count

The figure shows a map $f : S^1 \to S^1$ as a graph on the unrolled torus: the input angle $\theta$
runs horizontally, the output $f(\theta)$ vertically, and the graph wraps around when it leaves
the top or bottom. The map is
$$f(\theta) = k\theta + a\sin 3\theta,$$
which is well defined on the circle for any integer $k$. The horizontal line is the target $y$.
Each crossing of the graph with the line is a solution of $f(\theta) = y$; where the graph crosses
upward, $f' > 0$ and the sign is $+1$ (blue); where it crosses downward, $-1$ (orange). The signed
total is displayed. Change $y$ and $a$ freely: individual crossings appear and disappear in
$\pm$ pairs and the total never moves. Change $k$ and the total changes to $k$, because $k$ cannot
be changed continuously.

<div id="degree-figure"></div>

*(In the printed version this figure is a still image; the interactive version is in the web
edition.)*

---

## 6. Application: why superfluid vortices are quantized

Liquid helium below $2.17\,\mathrm K$, and the ultracold atomic gases made since 1995, are
*superfluids*. The whole fluid is described by a single complex-valued function $\psi(x) =
\sqrt{\rho(x)}\,e^{i\varphi(x)}$, where $\rho$ is the density of the fluid and $\varphi$ is a phase
angle, a point of the circle $S^1$. The velocity of the fluid is the gradient of the phase:

$$\mathbf v = \frac{\hbar}{m}\,\nabla\varphi,$$

where $m$ is the mass of one atom and $\hbar$ is Planck's constant divided by $2\pi$. (This is the
one line of physics we need; it comes from the Schrödinger equation.)

**The circulation.** Take a closed loop $\gamma : S^1 \to \{\text{fluid}\}$ that avoids the places
where $\rho = 0$, so that $\varphi$ is defined along it. The *circulation* around the loop is
$\Gamma = \oint_\gamma \mathbf v \cdot d\mathbf l = \frac{\hbar}{m}\oint_\gamma \nabla\varphi \cdot
d\mathbf l$. The integral of the gradient of an angle around a closed loop is not zero in general,
because the angle is only defined modulo $2\pi$: it equals $2\pi$ times the number of times the
phase winds around the circle as one goes around the loop. Precisely: the composite
$$e^{i\varphi}\circ\gamma : S^1 \to S^1$$
is a smooth map from the circle to itself, and $\oint_\gamma \nabla\varphi\cdot d\mathbf l =
2\pi \deg(e^{i\varphi} \circ \gamma)$. (Proof: lift $\varphi\circ\gamma$ to a real function
$\tilde\varphi$ on $[0, 2\pi]$; then $\oint\nabla\varphi\cdot d\mathbf l = \tilde\varphi(2\pi) -
\tilde\varphi(0) = 2\pi n$ for an integer $n$; and $n$ is the degree, because a regular value $y$ of
the map $\theta \mapsto \tilde\varphi(\theta) \bmod 2\pi$ is crossed upward $n$ more times than
downward, exactly as in the figure above.) Hence

> **Quantization of circulation (Onsager 1949, Feynman 1955).**
> $$\Gamma = \frac{h}{m}\cdot\deg(e^{i\varphi}\circ\gamma), \qquad h = 2\pi\hbar,$$
> an integer multiple of $h/m$.

For helium, $h/m \approx 9.97 \times 10^{-8}\ \mathrm{m^2/s}$. Vinen measured the circulation
around a wire in rotating helium in 1961 and found this unit. In rotating atomic condensates the
vortices are photographed directly, and they form a lattice of identical unit vortices (Abo-Shaeer,
Raman, Vogels and Ketterle, 2001) rather than one big whirl, because the energy of a vortex grows
like the square of its integer and two unit vortices are cheaper than one double one.

**Why the integer cannot change.** Deform the flow smoothly in time, keeping $\rho \ne 0$ along the
loop. Then $e^{i\varphi}\circ\gamma$ changes by a smooth homotopy, and by Theorem B its degree does
not change. So the circulation around the loop is frozen. The only way to change it is to let a zero
of $\psi$, a *vortex core*, cross the loop: there the phase is undefined, the map to $S^1$ is not
defined, and the theorem does not apply. This is exactly how a vortex enters a rotating condensate:
from the edge, where the density vanishes.

**The vortex itself.** Around a straight vortex line the phase is $\varphi = n\vartheta$ in
cylindrical coordinates, the map $e^{i\varphi}$ on a small loop around the core is $z \mapsto z^n$,
of degree $n$, and the velocity $\|\mathbf v\| = n\hbar/(mr)$ blows up at the core, which is why the
density must vanish there. The integer $n$ is a degree in the sense of this chapter, and that is
the whole reason it is an integer.

> **A remark on the lensing theorem.** Chapter 4 proved that a transparent gravitational lens
> produces an odd number of images. The degree refines this: the lens map is homotopic to the
> identity, so its degree is $1$, and therefore (number of images with $\det d\beta > 0$) minus
> (number with $\det d\beta < 0$) $= 1$. Images of the two kinds have opposite *parity*: one is a
> mirror image of the source and the other is not. Astronomers can sometimes tell which is which,
> and the count checks.

---

## 7. Summary of what was silently assumed, now made explicit

| Where | Milnor says | What is actually needed |
|---|---|---|
| p. 26 | "outward vectors" at a boundary point | independence of the chart, from the derivative of a change of coordinates preserving the half-space (Claim 1.1) |
| p. 26 | the boundary orientation is well defined | block-triangular change of basis with positive corner entry (Claim 1.2) |
| p. 27 | "$\deg(f;y)$ is a locally constant function of $y$" | the local inverses $L_i$ of Chapter 1 have connected domains, on which the sign is constant (Claim 2.1) |
| p. 28 | "$v_1$ determines the orientation of $TA_x$ iff…" | independence of the completion $(v_2,\dots)$, via a block-triangular determinant (Lemma 3.1) |
| p. 28 | "$v_1$ points outward at one boundary point and inward at the other" | the arc is diffeomorphic to $[0,1]$ (Appendix); its velocity is transverse to $\partial X$ by the regularity in Chapter 2, Lemma 4.1 |
| p. 29 | "$h$ will preserve orientation" | continuity in $t$ of $\operatorname{sign} d(h_t)_x$ along the isotopy |
| p. 29 | "$f$ is homotopic to $h \circ f$" | the homotopy $h_t \circ f$, and the common regular value $z$ (Theorem A) |
| p. 30 | "the antipodal map is the composition of $n+1$ reflections" | degree of a composition of diffeomorphisms is the product; a reflection reverses the boundary orientation of the sphere |

**Checked by machine.** Everything in this chapter has been verified in the Lean proof assistant:
orientations and the sign of a derivative, Lemma 1 (in an ambient form, with the boundary presented
by a function), Lemma 2, Theorems A and B, the Brouwer degree, the degree of the antipodal map, and
the hairy ball theorem. See the verified edition, §6, and *Milnor, proof by proof*, Part III.