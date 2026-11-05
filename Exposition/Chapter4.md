# Chapter 4. Counting solutions: the degree modulo 2

*Milnor, "Topology from the Differentiable Viewpoint", §4, rewritten for a first-year student who
wants to know what the theorem is for. Every proof is complete.*

---

## 0. A question you can ask with a piece of rope

Lay a closed loop of rope on a table. Hammer a nail into the table somewhere the rope does not
pass, and hold a ruler against the nail so that it points in some direction. Count how many times
the ruler crosses the rope.

Now move the rope around on the table any way you like, stretching and folding it, but never
lifting it over the nail. The count changes: fold a piece of the rope across the ruler and you
gain two crossings, fold it back and you lose two. But the count never changes by one. Its
*parity*, odd or even, is stuck for as long as the rope stays away from the nail. Rotate the
ruler to a different direction and the parity is the same. Look at a completely different
region of the rope and it is the same.

This chapter is about why. The rope is a smooth map from a circle to a circle: each point of the
rope is sent to the direction in which it is seen from the nail. The crossings with the ruler are
the solutions $x$ of the equation $f(x) = y$, where $y$ is the direction of the ruler. The theorem
says: for a smooth map between compact manifolds of the same dimension, the number of solutions of
$f(x) = y$, counted at a regular value $y$, has a parity that does not depend on $y$ and does not
change when $f$ is deformed. That parity is the *degree modulo 2* of $f$.

Two things about this are surprising to a beginner. First, that a count of solutions of an
equation can carry information stable under any continuous change of the equation. Second, that
only the parity survives, not the number itself. Both are visible in the interactive figure below,
and both are exactly what the proof explains: solutions can only be created or destroyed in
pairs, at a fold.

At the end of the chapter the same theorem, applied to the bending of light by a galaxy, says that
a transparent gravitational lens always produces an *odd* number of images of a distant source.
That is an observed fact about the sky, and it is a theorem in this chapter.

---

## 1. Smooth homotopy and isotopy (Milnor p. 20)

Throughout, $M$ and $N$ are smooth manifolds. We write $M \times [0,1]$ for the cylinder over $M$;
when $M$ has no boundary, this is a manifold with boundary $M \times \{0\} \cup M \times \{1\}$
(Lemma 3 of Chapter 2 applied to the coordinate $t$ and to $1 - t$).

**Definition.** Two smooth maps $f, g : X \to Y$ are *smoothly homotopic*, written $f \sim g$, if
there is a smooth map $F : X \times [0,1] \to Y$ with $F(x, 0) = f(x)$ and $F(x, 1) = g(x)$ for
all $x$. The map $F$ is a *smooth homotopy* from $f$ to $g$. If $f$ and $g$ are diffeomorphisms
and each intermediate map $x \mapsto F(x,t)$ is also a diffeomorphism, $F$ is a *smooth isotopy*.

**Claim 1.1.** Smooth homotopy is an equivalence relation.

*Proof.* Reflexive: $F(x,t) = f(x)$. Symmetric: $F(x, 1-t)$. Transitive: this is the one step
that needs care. Given homotopies $F$ from $f$ to $g$ and $G$ from $g$ to $h$, the obvious
"run $F$ on $[0, \tfrac12]$ and $G$ on $[\tfrac12, 1]$" is continuous but may fail to be smooth at
$t = \tfrac12$. The repair is to slow both homotopies to a stop before joining them. Let
$\varphi : [0,1] \to [0,1]$ be smooth with $\varphi(t) = 0$ for $t \le \tfrac13$ and
$\varphi(t) = 1$ for $t \ge \tfrac23$; for instance

$$\varphi(t) = \frac{\lambda(t - \tfrac13)}{\lambda(t - \tfrac13) + \lambda(\tfrac23 - t)},
\qquad \lambda(\tau) = \begin{cases} 0 & \tau \le 0 \\ e^{-1/\tau} & \tau > 0.\end{cases}$$

(The denominator is never zero, because at least one of $\tau_1 = t - \tfrac13$, $\tau_2 =
\tfrac23 - t$ is positive; and $\lambda$ is smooth, the standard fact that $e^{-1/\tau}$ and all
its derivatives tend to $0$ as $\tau \to 0^+$.) Then $F'(x,t) = F(x, \varphi(t))$ is a smooth
homotopy from $f$ to $g$ that is *constant* equal to $f$ for $t \le \tfrac13$ and constant equal
to $g$ for $t \ge \tfrac23$; likewise $G'$. Now define $H(x,t) = F'(x, 2t)$ for $t \le \tfrac12$
and $H(x,t) = G'(x, 2t-1)$ for $t \ge \tfrac12$. Near $t = \tfrac12$ both formulas equal $g(x)$
identically, so $H$ is smooth. $\square$

The same argument shows smooth isotopy is an equivalence relation on diffeomorphisms.

---

## 2. The homotopy lemma (Milnor pp. 21–22)

Recall from Chapter 1: if $M$ is compact, $\dim M = \dim N$, and $y$ is a regular value of a smooth
$f : M \to N$, then $f^{-1}(y)$ is finite and we write $\#f^{-1}(y)$ for its size.

**Homotopy Lemma 2.1.** Let $f, g : M \to N$ be smoothly homotopic maps between manifolds of the
same dimension, with $M$ compact and without boundary. If $y$ is a regular value of both $f$ and
$g$, then
$$\#f^{-1}(y) \equiv \#g^{-1}(y) \pmod 2.$$

The idea is the whole chapter, so here it is before the proof. Let $F : M \times [0,1] \to N$ be
the homotopy. Consider the set $F^{-1}(y)$ inside the cylinder. Its points on the bottom face
$M \times \{0\}$ are the solutions of $f(x) = y$; its points on the top face are the solutions of
$g(x) = y$. If $y$ is a regular value of $F$ as well, then $F^{-1}(y)$ is a smooth curve, a compact
1-manifold whose boundary consists exactly of those top and bottom points (Chapter 2, Lemma 4).
A compact 1-manifold is a finite union of circles and arcs. Circles have no ends. Each arc has two
ends. An arc that runs from the bottom to the top contributes one solution to each of $f$ and
$g$; an arc that starts and ends on the bottom contributes two solutions to $f$ and none to $g$;
similarly for the top. So the two counts differ by an even number. The picture is Milnor's
Figure 6, reproduced interactively below.

*Proof.* Let $F$ be a smooth homotopy from $f$ to $g$.

*Case 1: $y$ is a regular value of $F$.* By Lemma 4 of Chapter 2, applied to the manifold with
boundary $X = M \times [0,1]$ and the map $F$, the set $F^{-1}(y)$ is a compact 1-manifold with
boundary
$$\partial F^{-1}(y) = F^{-1}(y) \cap \partial X = f^{-1}(y) \times \{0\} \;\cup\; g^{-1}(y) \times \{1\}.$$
(The hypothesis of Lemma 4, that $y$ is regular for $F$ restricted to $\partial X$, is exactly
the hypothesis that $y$ is regular for $f$ and for $g$. Compactness: $F^{-1}(y)$ is closed in the
compact space $M \times [0,1]$.) The number of boundary points is therefore
$\#f^{-1}(y) + \#g^{-1}(y)$. By the classification of compact 1-manifolds (the Appendix), a compact
1-manifold with boundary is a finite disjoint union of circles and closed intervals, so it has an
even number of boundary points. Hence $\#f^{-1}(y) + \#g^{-1}(y)$ is even, which is the claim.

*Case 2: $y$ is not a regular value of $F$.* We cannot use $y$ itself, so we move to a nearby
point that works for everything, using two results already proved. By the local constancy lemma
of Chapter 1 (Theorem 4.2 there), there is a neighbourhood $V_1$ of $y$ such that
$\#f^{-1}(y') = \#f^{-1}(y)$ for all $y' \in V_1$, and a neighbourhood $V_2$ with
$\#g^{-1}(y') = \#g^{-1}(y)$ for all $y' \in V_2$. By Brown's theorem (Chapter 2, Theorem 2.1)
the regular values of $F$ are dense in $N$, so there is a regular value $z$ of $F$ inside the
open set $V_1 \cap V_2$. Note that $z$ is then also a regular value of $f$ and of $g$: a regular
value of $F$ is regular for $F|_{\partial X}$, because at a boundary point the derivative of the
restriction is the derivative of $F$ restricted to the tangent space of the boundary, and if
$dF_{(x,0)}$ is onto then... this step needs care, so let us do it properly. At $(x, 0)$ the
derivative of $F$ is $dF_{(x,0)}(v, s) = df_x(v) + s\,w$ for some vector $w$ (the $t$-derivative
of $F$). We are *not* claiming $df_x$ is onto merely because $dF_{(x,0)}$ is; that is false in
general. What we know instead is that $z \in V_1$, and $V_1$ was chosen inside the set of regular
values of $f$ (Chapter 1, Theorem 4.2 produces a neighbourhood consisting of regular values).
The same for $g$ and $V_2$. So $z$ is regular for $f$, $g$, and $F$, and Case 1 applies to $z$:
$$\#f^{-1}(y) = \#f^{-1}(z) \equiv \#g^{-1}(z) = \#g^{-1}(y) \pmod 2. \qquad\square$$

> **Where Milnor was quicker than the argument.** In Case 2 Milnor writes "there is a neighborhood
> $V_1$ of $y$, consisting of regular values of $f$, so that $\#f^{-1}(y') = \#f^{-1}(y)$". The
> phrase "consisting of regular values" is essential and easy to miss: the neighbourhood from the
> local constancy lemma must be shrunk to lie inside the (open) set of regular values of $f$, which
> is possible because the critical values of $f$ form a closed set ($f$ is continuous, the critical
> points form a closed subset of the compact $M$, so the critical values are compact). Without
> it, Case 1 could not be applied to $z$.

---

### An interactive look at the proof

The figure shows the cylinder $S^1 \times [0,1]$, unrolled as a rectangle: the angle $\theta$
runs horizontally, the time $t$ vertically, with $f = F(\cdot, 0)$ at the bottom and
$g = F(\cdot, 1)$ at the top. The homotopy is
$$F(\theta, t) = \theta + a(t)\,\sin 3\theta, \qquad a(t) = a_0 + t\,(a_1 - a_0),$$
a map of the circle to itself that is a small wobble of the identity for small $a$ and develops
three folds once $3a > 1$. The curves drawn are $F^{-1}(y)$ for the target direction $y$. Their
endpoints on the bottom edge are the solutions of $f(\theta) = y$; on the top edge, of
$g(\theta) = y$.

Drag $a_1$ past $1/3$ and watch a fold cross the target: a new arc appears whose both ends are on
the top edge, and the top count jumps from $1$ to $3$. Drag $y$ around: the counts change, the
parity never does. Every arc either connects bottom to top (one solution each) or returns to the
edge it started from (two solutions on one side). That is the entire proof.

<div id="homotopy-figure"></div>

*(In the printed version this figure is a still image; the interactive version is in the web
edition.)*

---

## 3. The homogeneity lemma (Milnor pp. 22–24)

The homotopy lemma compares two maps at one target point. To compare one map at two target
points we need to move the points around by a deformation of $N$.

**Homogeneity Lemma 3.1.** Let $y$ and $z$ be interior points of a smooth connected manifold
$N$. Then there is a diffeomorphism $h : N \to N$, smoothly isotopic to the identity, with
$h(y) = z$.

For the sphere this is a one-line proof: rotate. In general the proof constructs, inside a single
chart, a flow that slides one point to another while leaving everything outside a ball fixed, and
then uses connectedness to chain such slides together.

**Step 1: sliding the origin inside the unit ball of $\mathbb R^n$.** Let $\varphi : \mathbb R^n
\to \mathbb R$ be smooth, positive on the open unit ball, and zero outside it, for instance
$\varphi(x) = \lambda(1 - \|x\|^2)$ with $\lambda$ as in §1. Fix a unit vector $c$ and consider
the differential equation
$$\frac{dx}{dt} = c\,\varphi(x).$$
The right-hand side is smooth and bounded (by $\max\varphi$), and it is Lipschitz on all of
$\mathbb R^n$ (a smooth function that is constant outside a compact set has bounded derivative).
By the existence and uniqueness theorem for ordinary differential equations with a globally
Lipschitz right-hand side, for every $\bar x$ there is a unique solution $x(t)$ defined for
*all* $t \in \mathbb R$ with $x(0) = \bar x$; write $F_t(\bar x)$ for it. The three standard
properties are:

1. $F_t(\bar x)$ depends smoothly on $(t, \bar x)$ (smooth dependence on initial conditions);
2. $F_0 = \mathrm{id}$;
3. $F_{s+t} = F_s \circ F_t$ (uniqueness: both sides solve the equation with the same value at
   $t = 0$).

From 2 and 3, $F_t \circ F_{-t} = \mathrm{id}$, so each $F_t$ is a diffeomorphism of
$\mathbb R^n$, and $(x, t) \mapsto F_t(x)$ is a smooth isotopy from the identity to $F_t$. Where
$\varphi = 0$, that is outside the unit ball, the equation says $dx/dt = 0$, so those points do
not move: $F_t$ is the identity outside the ball. Finally, the origin moves along the straight
line $\{sc : s \in \mathbb R\}$ in the direction $c$: along that line the equation becomes the
scalar equation $ds/dt = \varphi(sc)$ with $\varphi(sc) > 0$ for $|s| < 1$, so $s(t)$ increases
strictly and, since the solution exists for all time and cannot leave the ball (it would have to
stop first), tends to the boundary. Hence $t \mapsto F_t(0)$ sweeps out the whole open segment
from $0$ to $c$. Choosing $c$ and $t$, we can send $0$ to any point of the open unit ball.

**Step 2: connectedness.** Call two points of $N$ *isotopic* if some diffeomorphism smoothly
isotopic to the identity carries one to the other. Composing isotopies (Claim 1.1 for isotopies)
this is an equivalence relation. Let $y$ be an interior point and let $\psi$ be a chart mapping a
neighbourhood $U$ of $y$ diffeomorphically onto $\mathbb R^n$ with $\psi(y) = 0$ (take any chart,
translate, and rescale so that its image contains the closed unit ball; then restrict). Transport
the isotopy of Step 1 to $U$ by $\psi$ and extend it by the identity outside $U$; since the Step 1
maps are the identity outside the unit ball, the extended map is smooth on all of $N$. This shows
every point of $\psi^{-1}(\text{open unit ball})$, a neighbourhood of $y$, is isotopic to $y$.
So each isotopy class of interior points is open. The interior of $N$ is connected (it is $N$
when $N$ has no boundary; in general it is the complement of the boundary, which is connected
whenever $N$ is, a fact we only need for boundaryless $N$ in this book). A connected set cannot be
partitioned into two or more disjoint nonempty open sets, so there is exactly one isotopy class.
$\square$

---

## 4. The theorem (Milnor p. 24)

From here on, $M$ is compact without boundary, $N$ is connected, $\dim M = \dim N$, and
$f : M \to N$ is smooth.

**Theorem 4.1.** If $y$ and $z$ are regular values of $f$, then
$$\#f^{-1}(y) \equiv \#f^{-1}(z) \pmod 2.$$
This common residue class, the *degree modulo 2* of $f$, written $\deg_2 f$, depends only on the
smooth homotopy class of $f$.

*Proof.* By the homogeneity lemma there is a diffeomorphism $h : N \to N$, isotopic to the
identity, with $h(y) = z$. Then $z$ is a regular value of $h \circ f$: if $h(f(x)) = z$ then
$f(x) = y$ (as $h$ is injective), $x$ is a regular point of $f$, and $d(h\circ f)_x = dh_{f(x)}
\circ df_x$ is a composition of isomorphisms. The isotopy from the identity to $h$ gives a smooth
homotopy from $f$ to $h \circ f$ (compose the isotopy with $f$), so by the homotopy lemma
$$\#(h \circ f)^{-1}(z) \equiv \#f^{-1}(z) \pmod 2.$$
But $(h\circ f)^{-1}(z) = f^{-1}(h^{-1}(z)) = f^{-1}(y)$, so the left side is $\#f^{-1}(y)$.

For homotopy invariance: let $g \sim f$. By Brown's theorem the regular values of $f$ and of $g$
are each dense, and the set of regular values of a smooth map from a compact manifold is open
(its complement, the set of critical values, is the image of the closed set of critical points
and so is compact). A dense open set meets any other dense set, so there is a $y$ regular for
both $f$ and $g$. By the homotopy lemma, $\deg_2 f \equiv \#f^{-1}(y) \equiv \#g^{-1}(y) \equiv
\deg_2 g$. $\square$

> **Where Milnor was quicker than the argument.** He writes "By Sard's theorem, there exists an
> element $y \in N$ which is a regular value for both $f$ and $g$." Sard gives that each set of
> regular values is dense; to intersect two dense sets one needs one of them to be open as well.
> That is where compactness of $M$ enters a second time.

**Examples.**

* A constant map $c : M \to N$ has $\deg_2 c = 0$: any $y \ne c$ is a regular value with empty
  preimage.
* The identity of $M$ has $\deg_2 = 1$: every $y$ is a regular value with exactly one preimage.
* Therefore the identity of a compact boundaryless manifold is not smoothly homotopic to a
  constant map. For the rope this says: you cannot shrink a loop that winds once around the nail
  down to a point without passing over the nail.
* Consequently there is no smooth map $f : D^{n+1} \to S^n$ that fixes the sphere pointwise, for
  $F(x,t) = f(tx)$ would be a smooth homotopy on $S^n$ from the constant map $f(0)$ to the
  identity. This recovers Lemma 5 of Chapter 2 for the disk, and with it the smooth Brouwer fixed
  point theorem, this time with the parity count doing the work that the 1-manifold classification
  did there. (The classification is still used, inside the homotopy lemma.)

---

## 5. Application: a transparent gravitational lens makes an odd number of images

Light from a distant quasar passing near a galaxy is bent by the galaxy's gravity, and an observer
can see several images of the same quasar. Here is what the theorem of this chapter says about how
many.

**The model.** In the thin-lens approximation, positions in the sky are points of a plane. A ray
that would have arrived from position $x$ in the *image plane* (as seen by the observer) actually
originates from position
$$\beta(x) = x - \alpha(x)$$
in the *source plane*, where the deflection $\alpha(x)$ is determined by the mass distribution of
the lens: $\alpha$ is the gradient of a potential $\psi$ solving $\Delta\psi = 2\kappa$, with
$\kappa \ge 0$ the (dimensionless) surface mass density. A source at position $s$ is seen at every
$x$ with $\beta(x) = s$: the images of the source are the solutions of the equation $\beta(x) = s$.

**Two physical facts.** (i) For a lens of finite total mass, $\alpha(x) \to 0$ as $|x| \to
\infty$: far from the galaxy, light is not deflected. (ii) If the mass density is smooth and
bounded, the map $\beta$ is smooth. A lens satisfying these is called *transparent* (the model
breaks down for a point mass, where $\alpha$ blows up at the origin; a black hole is not
transparent in this sense).

**The theorem.** Compactify the plane by adding a point at infinity, making it a sphere $S^2$
(Chapter 1, §6, where we did exactly this for polynomials). Because of (i), $\beta$ extends to a
smooth map $\bar\beta : S^2 \to S^2$ fixing the point at infinity, in the same way and for the
same reason as the polynomial map did. Now turn the lens down: for $\lambda \in [0,1]$ let
$\beta_\lambda(x) = x - \lambda\,\alpha(x)$. Each $\beta_\lambda$ is a transparent lens map (mass
density $\lambda\kappa$), $\beta_1 = \beta$, and $\beta_0$ is the identity. So $(x, \lambda)
\mapsto \bar\beta_\lambda(x)$ is a smooth homotopy on $S^2$ from the identity to $\bar\beta$. By
Theorem 4.1,
$$\deg_2 \bar\beta = \deg_2(\mathrm{id}) = 1.$$
Therefore, for every regular value $s$, the number of solutions of $\beta(x) = s$ is odd:

> **Odd-number theorem.** A transparent gravitational lens produces an odd number of images of
> any source not on a caustic.

The exceptional sources are those on *caustics*, the critical values of $\beta$; by Sard's
theorem they form a set of measure zero in the source plane. When a source crosses a caustic, two
images appear or disappear together, which is the fold of §2 seen in the sky.

Astronomers mostly observe an even number of images (two or four), which was for a time called
the "missing image problem". The theorem says the missing image must exist; it is the one near
the centre of the lens, strongly demagnified by the dense core, and it has since been detected in
several systems. A theorem about counting solutions of $f(x) = y$ modulo 2 predicted the
existence of a faint image before it was seen.

---

## 6. Summary of what was silently assumed, now made explicit

| Where | Milnor says | What is actually needed |
|---|---|---|
| p. 20 | homotopy is transitive | reparametrize both homotopies to be constant near the ends before joining (§1) |
| p. 21 | "$F^{-1}(y)$ is a compact 1-manifold with boundary …" | Chapter 2, Lemma 4, applied to $M \times [0,1]$; regularity for $F|_{\partial X}$ is regularity for $f$ and $g$ |
| p. 22 | "a neighborhood $V_1$ consisting of regular values" | the critical values of $f$ form a compact, hence closed, set, so the local-constancy neighbourhood can be shrunk into the regular values |
| p. 23 | the ODE has solutions "defined for all real numbers" | the vector field is bounded and globally Lipschitz |
| p. 23 | "$F_t$ will carry the origin to any desired point" | the origin moves monotonically along a ray and cannot stop inside the ball |
| p. 24 | "By Sard's theorem, there exists $y$ regular for both" | the regular values of $f$ are dense *and open*, since $M$ is compact |

**Checked by machine.** Everything in this chapter has been verified in the Lean proof assistant:
Lemma 4 for the cylinder, the homotopy lemma, the homogeneity lemma, the theorem that the degree
modulo 2 does not depend on the regular value and is a homotopy invariant, and the surjectivity of
maps of nonzero degree. The homogeneity lemma is proved with explicit bump-function
diffeomorphisms rather than flows. See the verified edition, §5, and *Milnor, proof by proof*,
Part II.