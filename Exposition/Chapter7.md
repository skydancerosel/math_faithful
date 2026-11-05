# Chapter 7. Follow the needles that point north: framed cobordism and the Pontryagin construction

*Milnor, "Topology from the Differentiable Viewpoint", §7, rewritten for a first-year student who
wants to know what the theorem is for. Every proof is complete; one geometric step (the product
neighbourhood of a cobordism near its ends) is spelled out where Milnor writes "completely
analogous".*

---

## 0. A magnet full of compass needles

Inside a magnet, every point carries a little arrow: the direction of the local magnetization, a
unit vector $n(x) \in S^2$. Far from any defects the arrows vary smoothly. Now mark the points where
the arrow points *exactly north*. In a three-dimensional sample this is a curve (three equations
in three unknowns minus... no: two equations, since a direction has two degrees of freedom, so a
one-dimensional set). Along that curve, also record which way the arrow tilts as you step off the
curve: eastward in one direction, upward in another. This decorated curve is the *Pontryagin
manifold* of the texture.

The theorem of this chapter says that the decorated curve knows everything about the texture that
survives continuous deformation. Two magnetization patterns can be deformed into one another if and
only if their decorated "north curves" can be deformed into one another, through decorated surfaces
in space-time. And every decorated curve arises from some texture. A question about maps to the
sphere, which are hard to draw, becomes a question about curves in space, which are easy to draw.
When the north curve is a knot or a link, the texture is a *hopfion*, and the linking of the north
curve with the south curve is an integer the texture cannot lose. Such textures were photographed
in a magnet in 2023.

Mathematically: the degree of Chapter 5 was defined for maps between manifolds of the *same*
dimension. Pontryagin's construction handles maps $f : M \to S^p$ from a compact manifold of any
dimension $m \ge p$ to a sphere, by replacing the finite set $f^{-1}(y)$ and its signs with the
$(m-p)$-manifold $f^{-1}(y)$ and a *framing* of its normal directions. When $m = p$ we recover the
degree, and as a corollary we get Hopf's theorem: maps $M^m \to S^m$ are classified up to homotopy
by their degree alone.

---

## 1. Cobordism and framings (Milnor pp. 41–42)

Throughout, $M$ is a compact smooth manifold of dimension $m$ without boundary, $M \subseteq \mathbb R^k$.

**Definition.** Let $N, N' \subseteq M$ be compact submanifolds of dimension $n$ without boundary.
Their *codimension* is $m - n$. $N$ is *cobordant to $N'$ within $M$* if there is a compact
manifold with boundary $X \subseteq M \times [0,1]$ such that
$$X \cap \bigl(M \times [0,\varepsilon)\bigr) = N \times [0,\varepsilon), \qquad
X \cap \bigl(M \times (1-\varepsilon, 1]\bigr) = N' \times (1-\varepsilon, 1]$$
for some $\varepsilon > 0$, $\partial X = N \times \{0\} \cup N' \times \{1\}$, and $X$ meets
$M \times \{0, 1\}$ only in $\partial X$. Cobordism is an equivalence relation: reflexive via
$N \times [0,1]$, symmetric via $t \mapsto 1 - t$, transitive by stacking two cobordisms end to
end (the product structure near the ends makes the union smooth).

**Definition.** A *framing* of a submanifold $N \subseteq M$ of codimension $p$ is a smooth
function $v$ assigning to each $x \in N$ a basis $v(x) = (v^1(x), \dots, v^p(x))$ of the normal
space $TN_x^\perp \subseteq TM_x$. The pair $(N, v)$ is a *framed submanifold*. Two framed
submanifolds $(N, v)$, $(N', w)$ are *framed cobordant* if there is a cobordism $X$ between them
with a framing $u$ of $X$ in $M \times [0,1]$ such that
$$u^i(x, t) = (v^i(x), 0) \text{ for } (x,t) \in N \times [0,\varepsilon), \qquad
u^i(x, t) = (w^i(x), 0) \text{ for } (x,t) \in N' \times (1-\varepsilon, 1].$$
This too is an equivalence relation, for the same reasons.

Not every submanifold admits a framing: a normal bundle can be twisted (the centre circle of a
Möbius band inside the band). A framed submanifold is in particular one whose normal bundle is
trivial.

---

## 2. The Pontryagin manifold of a map (Milnor pp. 42–45)

Let $f : M \to S^p$ be smooth and $y \in S^p$ a regular value. By Chapter 2, Lemma 2.1,
$N := f^{-1}(y)$ is a compact submanifold of codimension $p$, and by Lemma 2.2 its tangent space at
$x$ is $\ker df_x$. Hence $df_x$ restricted to the normal space $TN_x^\perp$ is injective, and,
both spaces having dimension $p$, an isomorphism onto $T(S^p)_y$. Choose a positively oriented basis
$v = (v_1, \dots, v_p)$ of $T(S^p)_y$. For each $x \in N$ let $w^i(x) \in TN_x^\perp$ be the unique
normal vector with $df_x(w^i(x)) = v_i$. The $w^i$ are smooth in $x$ (they solve a linear system
whose coefficients depend smoothly on $x$ and whose matrix is invertible), and form a framing
$w = f^*v$ of $N$.

**Definition.** $(f^{-1}(y), f^*v)$ is the *Pontryagin manifold* of $f$ (at $y$, with respect to
$v$).

**Theorem A.** The framed cobordism class of the Pontryagin manifold does not depend on the choice
of regular value $y$ or of positive basis $v$.

**Theorem B.** Two smooth maps $M \to S^p$ are smoothly homotopic if and only if their Pontryagin
manifolds are framed cobordant.

**Theorem C.** Every compact framed submanifold of codimension $p$ in $M$ is the Pontryagin manifold
of some smooth map $M \to S^p$.

Together: **homotopy classes of maps $M \to S^p$ correspond bijectively to framed cobordism classes
of codimension-$p$ framed submanifolds of $M$.**

**Lemma 2.1 (Milnor's Lemma 1).** If $v, v'$ are two positive bases of $T(S^p)_y$, then
$(f^{-1}(y), f^*v)$ and $(f^{-1}(y), f^*v')$ are framed cobordant.

*Proof.* The positive bases of $T(S^p)_y$ correspond to matrices in $GL^+(p)$, which is path
connected (Chapter 6, Lemma 1.1). Choose a smooth path $v_t$ of positive bases from $v$ to $v'$,
constant near $t = 0$ and $t = 1$. Then $X := f^{-1}(y) \times [0,1]$ with framing
$u^i(x, t) := ((f^*v_t)^i(x), 0)$ is a framed cobordism. (The normal space of $X$ in
$M \times [0,1]$ at $(x, t)$ is $TN_x^\perp \times \{0\}$.) $\square$

We now often write "the framed manifold $f^{-1}(y)$" for the Pontryagin manifold with any positive
basis.

**Lemma 2.2 (Milnor's Lemma 2).** If $y$ is a regular value of $f$ and $z$ is sufficiently close
to $y$, then $f^{-1}(z)$ is framed cobordant to $f^{-1}(y)$.

*Proof.* The critical values of $f$ form a compact set (image of the closed set of critical points
of the compact $M$), so there is $\varepsilon > 0$ such that every point within distance
$\varepsilon$ of $y$ is a regular value. Let $\|z - y\| < \varepsilon$, $z \ne y$. Let $\theta \in
(0, \pi)$ be the angle between $y$ and $z$ and $R_\alpha$ the rotation by angle $\alpha$ in the
plane spanned by $y, z$, fixing its orthogonal complement. Let $\beta : [0,1] \to [0,1]$ be smooth,
$0$ near $0$ and $1$ near $1$, and $r_t := R_{\beta(t)\theta}$. Then $r_t$ is a smooth family of
rotations of $S^p$ with $r_t = \mathrm{id}$ near $t = 0$, $r_t = r_1$ near $t = 1$, $r_1(y) = z$,
and each $r_t^{-1}(z) = R_{-\beta(t)\theta}(z)$ lies on the short great-circle arc from $z$ to $y$,
all of whose points are within distance $\|z - y\| < \varepsilon$ of $y$ (chord length increases
with angle), hence are regular values of $f$.

Define $F : M \times [0,1] \to S^p$, $F(x, t) := r_t(f(x))$. For each $t$, $z$ is a regular value of
$r_t \circ f$: its preimage is $f^{-1}(r_t^{-1} z)$, a set of regular points of $f$, and $d(r_t
\circ f) = dr_t \circ df$ is onto. A fortiori $z$ is a regular value of $F$, and of $F$ restricted to
$M \times \{0, 1\}$. By Chapter 2, Lemma 4.1, $X := F^{-1}(z)$ is a compact manifold with boundary
$f^{-1}(z) \times \{0\} \cup f^{-1}(y) \times \{1\}$. Near $t = 0$, $F(x,t) = f(x)$, so $X$ is
$f^{-1}(z) \times [0, \varepsilon_0)$ there and the framing $F^*v$ is $(f^*v, 0)$; near $t = 1$,
$F(x,t) = r_1 f(x)$, so $X$ is $f^{-1}(y) \times (1 - \varepsilon_0, 1]$ with framing
$((r_1 f)^*v, 0) = (f^*(dr_1^{-1} v), 0)$, where $dr_1^{-1}v$ is a positive basis at $y$
(rotations preserve orientation). So $(X, F^*v)$ is a framed cobordism from $f^{-1}(z)$ to
$f^{-1}(y)$ with the framing $f^*(dr_1^{-1}v)$, which is framed cobordant to $f^{-1}(y)$ with any
positive framing by Lemma 2.1. $\square$

**Lemma 2.3 (Milnor's Lemma 3).** If $f$ and $g$ are smoothly homotopic and $y$ is a regular value
of both, then $f^{-1}(y)$ and $g^{-1}(y)$ are framed cobordant.

*Proof.* Reparametrizing the homotopy (Chapter 4, §1), choose $F : M \times [0,1] \to S^p$ with
$F(x, t) = f(x)$ for $t \le \varepsilon$ and $F(x,t) = g(x)$ for $t \ge 1 - \varepsilon$. By Brown's
theorem choose a regular value $z$ of $F$ so close to $y$ that, by Lemma 2.2, $f^{-1}(z)$ is framed
cobordant to $f^{-1}(y)$ and $g^{-1}(z)$ to $g^{-1}(y)$. Because $F$ is constant in $t$ near the
ends, $dF_{(x, t)} = (df_x, 0)$ for $t \le \varepsilon$, so $z$ regular for $F$ makes $z$ regular
for $f$, and likewise for $g$. Then $F^{-1}(z)$ with the framing $F^*v$ is a framed cobordism from
$f^{-1}(z)$ to $g^{-1}(z)$, exactly as in the previous proof. Chain the three cobordisms. $\square$

**Proof of Theorem A.** Independence of $v$ is Lemma 2.1. For two regular values $y, z$: choose
rotations $r_t$ as above with $r_0 = \mathrm{id}$, $r_1(y) = z$ (any two points of the sphere are
joined by a rotation path). Then $F(x, t) = r_t f(x)$ is a homotopy from $f$ to $r_1 \circ f$, and
$z$ is a regular value of both ($(r_1 f)^{-1}(z) = f^{-1}(y)$). By Lemma 2.3, $f^{-1}(z)$ is
framed cobordant to $(r_1 f)^{-1}(z) = f^{-1}(y)$ (with the framing $f^*(dr_1^{-1}v)$, positive,
hence by Lemma 2.1 equivalent to any). $\square$

---

## 3. The product neighbourhood theorem (Milnor pp. 45–46)

**Theorem 3.1.** Let $(N, v)$ be a compact framed submanifold of codimension $p$ in $M$ (both
without boundary). Then there is a diffeomorphism $g : N \times \mathbb R^p \to V$ onto an open
neighbourhood $V$ of $N$ in $M$, with $g(x, 0) = x$ and $dg_{(x,0)}(0, e_i) = v^i(x)$.

Milnor proves this for $M = \mathbb R^{n+p}$ by straight lines and says the general case uses
geodesics. We can avoid geodesics with the tubular neighbourhood of Chapter 6.

*Proof.* Let $r : N_\varepsilon \to M$ be the smooth closest-point retraction of Chapter 6,
Proposition 4.1, defined on the $\varepsilon$-neighbourhood of $M$ in $\mathbb R^k$. Since $N$ is
compact, $C := \max_{x, i} \|v^i(x)\| < \infty$; let $\delta := \varepsilon/(pC)$ and
$U_\delta$ the open $\delta$-ball in $\mathbb R^p$. Define
$$g_0 : N \times U_\delta \to M, \qquad g_0(x; t) := r\Bigl(x + \sum_i t_i v^i(x)\Bigr),$$
well defined since the argument is within $\varepsilon$ of $x \in M$. It is smooth. Its derivative
at $(x, 0)$: on $TN_x$ it is $dr_x = \mathrm{id}$ (as $r$ is the identity on $M$); on $\mathbb R^p$
it is $t \mapsto dr_x(\sum t_i v^i(x)) = \sum t_i v^i(x)$, because $v^i(x) \in TM_x$ and $dr_x$ is
the identity on $TM_x$. So $dg_{0,(x,0)} : TN_x \oplus \mathbb R^p \to TM_x = TN_x \oplus TN_x^\perp$
is an isomorphism. By the inverse function theorem $g_0$ is a diffeomorphism near each $(x, 0)$.
It is injective on $N \times U_{\delta'}$ for some $\delta' \le \delta$: otherwise there are pairs
$(x_j, t_j) \ne (x'_j, t'_j)$ with $t_j, t'_j \to 0$ and equal images; passing to subsequences
$x_j \to x_0$, $x'_j \to x'_0$ by compactness of $N$, continuity gives $x_0 = g_0(x_0, 0) =
g_0(x'_0, 0) = x'_0$, and for large $j$ both pairs lie in a neighbourhood of $(x_0, 0)$ on which
$g_0$ is injective, a contradiction. Thus $g_0$ maps $N \times U_{\delta'}$ diffeomorphically onto
an open set $V \supseteq N$. Finally compose with the diffeomorphism $\mathbb R^p \to U_{\delta'}$
inverse to $u \mapsto u/(1 - \|u\|^2/\delta'^2)$ (a radial map with positive radial derivative,
tending to infinity at the boundary), whose derivative at $0$ is the identity. The resulting $g$
has $g(x,0) = x$ and $dg_{(x,0)}(0, e_i) = v^i(x)$. $\square$

---

## 4. Every framed submanifold is a Pontryagin manifold (Milnor pp. 46–47)

**Proof of Theorem C.** Let $(N, v)$ be given, and $g : N \times \mathbb R^p \to V$ a product
neighbourhood. Define the projection $\pi : V \to \mathbb R^p$, $\pi(g(x, u)) = u$. It is smooth,
$0$ is a regular value (in the coordinates $g$, $\pi$ is the projection), $\pi^{-1}(0) = N$, and
the framing $\pi^* (e_1, \dots, e_p)$ is $v$: the normal vector $w^i(x)$ with $d\pi_x(w^i) = e_i$
is $dg_{(x,0)}(0, e_i) = v^i(x)$, which is normal to $N$ by hypothesis.

*A map from $\mathbb R^p$ to the sphere.* Fix a point $s_0 \in S^p$, let $h : S^p \setminus \{s_0\}
\to \mathbb R^p$ be stereographic projection from $s_0$, and let $\lambda : \mathbb R \to [0, \infty)$
be smooth with $\lambda(t) > 0$ for $t < 1$, $\lambda(t) = 0$ for $t \ge 1$, and $\lambda$
decreasing on $[0,1)$; for instance $\lambda(t) = e^{-1/(1-t)}$ for $t < 1$. Define
$$\varphi(u) := h^{-1}\bigl(u/\lambda(\|u\|^2)\bigr) \ \text{ for } \|u\| < 1, \qquad
\varphi(u) := s_0 \ \text{ for } \|u\| \ge 1.$$
On the open unit ball, $\varphi$ is a diffeomorphism onto $S^p \setminus \{s_0\}$: the map
$u \mapsto u/\lambda(\|u\|^2)$ is radial, with radial function $s \mapsto s/\lambda(s^2)$ strictly
increasing from $0$ to $\infty$ on $[0,1)$ with positive derivative, so it is a diffeomorphism of
the ball onto $\mathbb R^p$. Smoothness of $\varphi$ across $\|u\| = 1$: in the stereographic chart
$h'$ from the antipode of $s_0$, which sends $s_0$ to $0$ and is related to $h$ by the inversion
$h' = h/\|h\|^2$, we have $h'(\varphi(u)) = \lambda(\|u\|^2)\,u/\|u\|^2$ for $0 < \|u\| < 1$, and
this extends by $0$ to a smooth function on $\{u \ne 0\}$, because $\lambda$ and all its derivatives
vanish as $\|u\| \to 1$. So $\varphi$ is smooth, and $\varphi(0)$ is a regular value with
$\varphi^{-1}(\varphi(0)) = \{0\}$.

*The map.* Define $f : M \to S^p$ by $f := \varphi \circ \pi$ on $V$ and $f := s_0$ on
$M \setminus V$. The set $K := g(N \times \bar B_1) = \{x \in V : \|\pi(x)\| \le 1\}$ is compact,
hence closed in $M$, and $f \equiv s_0$ on the open set $M \setminus K$; on the open set $V$, $f$
is smooth. So $f$ is smooth on $M$. Its Pontryagin manifold at $\varphi(0)$, with the basis
$(d\varphi_0 e_i)$ (positive for a suitable orientation of $S^p$; otherwise replace $e_1$ by
$-e_1$ and $v^1$ by $-v^1$ throughout), is $\pi^{-1}(0) = N$ with framing $\pi^*(e_i) = v$.
$\square$

---

## 5. The Pontryagin manifold determines the homotopy class (Milnor pp. 47–49)

**Lemma 5.1 (Milnor's Lemma 4).** Let $f, g : M \to S^p$ have a common regular value $y$ and
*identical* Pontryagin manifolds there: $f^{-1}(y) = g^{-1}(y) =: N$ and $f^*v = g^*v$. Then $f$
and $g$ are smoothly homotopic.

*Proof.* **Step 1: the case $f = g$ on a neighbourhood $V$ of $N$.** Let $h : S^p \setminus \{y\}
\to \mathbb R^p$ be stereographic projection from $y$. For $x \notin N$, $f(x) \ne y$ and $g(x) \ne
y$, so
$$H(x, t) := \begin{cases} f(x), & x \in V, \\ h^{-1}\bigl(t\,h(f(x)) + (1-t)\,h(g(x))\bigr), & x \in M \setminus N \end{cases}$$
is well defined (the two formulas agree on $V \setminus N$, where $f = g$), smooth, and is a
homotopy from $g$ to $f$.

**Step 2: making $f$ agree with $g$ near $N$.** Since $f^*v = g^*v$ means $df_x = dg_x$ on the
normal spaces, and both vanish on $TN_x$, we have $df_x = dg_x$ for $x \in N$. Choose a product
neighbourhood $g_N : N \times \mathbb R^p \to V$ (Theorem 3.1) so small that $f(V)$ and $g(V)$
avoid the antipode $\bar y$ of $y$ (possible: $f^{-1}(\bar y)$ is a compact set disjoint from $N$).
Let $\bar h : S^p \setminus \{\bar y\} \to \mathbb R^p$ be stereographic projection from $\bar y$,
normalized so that $\bar h(y) = 0$ and $d\bar h_y(v_i) = e_i$ (compose with a linear map). Put
$$F := \bar h \circ f \circ g_N, \qquad G := \bar h \circ g \circ g_N : N \times \mathbb R^p \to \mathbb R^p.$$
Then $F^{-1}(0) = G^{-1}(0) = N \times \{0\}$, and at $(x, 0)$ both $dF$ and $dG$ vanish on $TN_x$
and send $(0, e_i) \mapsto d\bar h_y(df_x(w^i(x))) = d\bar h_y(v_i) = e_i$: both derivatives are the
projection to $\mathbb R^p$.

*A lower bound.* By Taylor's theorem on the compact set $N \times \bar B_1$ (second derivatives
bounded), there is $c_1$ with $\|F(x, u) - u\| \le c_1\|u\|^2$ for $\|u\| \le 1$, hence
$$F(x,u)\cdot u \ \ge\ \|u\|^2 - c_1\|u\|^3 \ >\ 0 \qquad \text{for } 0 < \|u\| < c := \min(1/c_1, 1),$$
and similarly for $G$ (take the worse constant). So for $0 < \|u\| < c$, $F(x,u)$ and $G(x,u)$ lie in
the same open half-space $\{w : w \cdot u > 0\}$, and no convex combination of them is $0$.

*The deformation.* Let $\lambda : \mathbb R^p \to [0,1]$ be smooth, $1$ for $\|u\| \le c/2$ and $0$
for $\|u\| \ge c$. Put
$$F_t(x, u) := \bigl(1 - \lambda(u)\,t\bigr)F(x,u) + \lambda(u)\,t\,G(x,u).$$
Then $F_0 = F$; $F_t = F$ wherever $\|u\| \ge c$; $F_1 = G$ wherever $\|u\| \le c/2$; and $F_t$ has
no zeros with $u \ne 0$: for $\|u\| \ge c$ because $F$ has none, for $0 < \|u\| < c$ because
$F_t(x,u)\cdot u > 0$. Transport back: define $f_t := \bar h^{-1} \circ F_t \circ g_N^{-1}$ on $V$
and $f_t := f$ outside $g_N(N \times \bar B_c)$. The two definitions agree on the overlap (where
$F_t = F$), and $g_N(N \times \bar B_c)$ is compact, so $f_t$ is a smooth homotopy from $f$ to a
map $f_1$ with $f_1^{-1}(y) = N$ and $f_1 = g$ on the neighbourhood $g_N(N \times B_{c/2})$ of
$N$. By Step 1, $f_1 \simeq g$. Hence $f \simeq g$. $\square$

**Proof of Theorem B.** If $f \simeq g$, their Pontryagin manifolds are framed cobordant by
Lemma 2.3 (choose a common regular value, which exists as in Chapter 5). Conversely let
$(X, u)$ be a framed cobordism in $M \times [0,1]$ from $(f^{-1}(y), f^*v)$ to $(g^{-1}(y), g^*v)$.
We build a homotopy $F : M \times [0,1] \to S^p$ whose Pontryagin manifold at $y$ is exactly
$(X, u)$, by the construction of Theorem C applied to $X$:

*Product neighbourhood of $X$.* Run the proof of Theorem 3.1 with $M \times [0,1] \subseteq
\mathbb R^{k+1}$ in place of $M$ and $X$ in place of $N$: the retraction is $r \times \mathrm{id}$,
and $g_0(\xi; t) = (r \times \mathrm{id})(\xi + \sum t_i u^i(\xi))$ for $\xi \in X$. For $\xi$ in the
end regions $N \times [0, \varepsilon)$ and $N' \times (1 - \varepsilon, 1]$ the framing vectors are
horizontal, $u^i = (v^i, 0)$, so $g_0$ preserves the $[0,1]$-coordinate there and maps into
$M \times [0,1]$; for $\xi$ with $[0,1]$-coordinate in $[\varepsilon, 1-\varepsilon]$, a displacement
of size less than $\varepsilon/2$ stays inside $M \times (0, 1)$. So for small $\delta$, $g_0$ is
defined on $X \times U_\delta$ with values in $M \times [0,1]$; the derivative and injectivity
arguments are unchanged ($X$ is compact), giving a diffeomorphism $g_X : X \times \mathbb R^p \to
W$ onto an open neighbourhood $W$ of $X$ in $M \times [0,1]$, which restricts over $N \times
\{0\}$ to a product neighbourhood of $N$ in $M \times \{0\}$ with the framing $v = f^*v$, and
similarly at $t = 1$.

*The homotopy.* Define $\Pi : W \to \mathbb R^p$ by $\Pi(g_X(\xi, u)) = u$ and $F := \varphi \circ
\Pi$ on $W$, $F := s_0$ elsewhere, with $\varphi$ as in Theorem C and $s_0$ chosen so that
$\varphi(0) = y$ and $d\varphi_0(e_i) = v_i$ (compose $\varphi$ with a rotation and, if needed, a
reflection of $\mathbb R^p$). As in Theorem C, $F$ is smooth, and its Pontryagin manifold at $y$ is
$(X, u)$. The map $F_0 := F(\cdot, 0)$ has $F_0^{-1}(y) = N$ with framing $F_0^*v = v = f^*v$: the
Pontryagin manifolds of $F_0$ and $f$ at $y$ are *identical*. By Lemma 5.1, $F_0 \simeq f$; likewise
$F_1 \simeq g$; and $F$ is a homotopy from $F_0$ to $F_1$. Therefore $f \simeq g$. $\square$

---

## 6. The Hopf theorem (Milnor p. 50)

Now take $p = m$: maps $f : M \to S^m$ from a compact connected oriented $m$-manifold. A framed
submanifold of codimension $m$ is a finite set of points $x$ with a basis $w(x)$ of $TM_x$. Define
$\operatorname{sgn}(x) = +1$ if $w(x)$ is a positive basis of $TM_x$ and $-1$ otherwise.

**Claim 6.1.** For the Pontryagin manifold of $f$ at $y$, $\sum_x \operatorname{sgn}(x) = \deg f$.

*Proof.* $w(x) = f^*v$ is the basis with $df_x(w^i) = v_i$, $v$ positive at $y$. It is positive
iff $df_x$ preserves orientation, i.e. iff $\operatorname{sign} df_x = +1$. Sum over $f^{-1}(y)$.
$\square$

**Claim 6.2.** Two framed $0$-manifolds in $M$ with the same $\sum \operatorname{sgn}$ are framed
cobordant.

*Proof.* Three moves. *(a) Changing the frame at a point.* Two bases of $TM_x$ of the same sign
are joined by a path in $GL^+$; the cobordism $\{x\} \times [0,1]$ with the moving frame realizes
this (as in Lemma 2.1). *(b) Moving a point.* Given $x, x'$, choose a smooth path $\gamma$ in $M$
from $x$ to $x'$, constant near its ends ($M$ is connected). The arc $X = \{(\gamma(t), t)\}$ with a
frame obtained by continuously extending $w(x)$ along the arc (the normal bundle of an arc is
trivial: extend a frame step by step and orthonormalize) is a framed cobordism from $(x, w(x))$
to $(x', w')$ for some frame $w'$ at $x'$, and $\operatorname{sgn}$ is preserved: along the arc,
the basis (positive tangent of $X$, $w^1, \dots, w^m$) of $T(M \times [0,1])$ has constant
orientation, the tangent points in the $+t$ direction at both ends here, and $(\partial_t, w)$ is
positive iff $w$ is positive for $M$. *(c) Cancelling a pair of opposite signs.* Given $x \ne x'$
with $\operatorname{sgn}(x) = -\operatorname{sgn}(x')$, choose an embedded arc $X$ in $M \times [0,1)$
from $(x, 0)$ to $(x', 0)$, vertical near its ends (for $m \ge 2$ join $x$ to $x'$ by an embedded
path $\gamma$ in $M$ and take $(\gamma(s), \varepsilon\sin\pi s)$ suitably reparametrized; for
$m = 1$, $M = S^1$ and an arc of the circle serves). Extend $w(x)$ to a frame along $X$ normal to
$X$. At the far end the tangent of $X$ points in the $-t$ direction (the arc returns to $M \times
\{0\}$), so by the constancy of orientation of (tangent, frame) along $X$, the transported frame
at $x'$ has sign $-\operatorname{sgn}(x) = \operatorname{sgn}(x')$; by (a), adjust it near the end
to equal $w(x')$. Then $X$ is a framed cobordism from $\{x, x'\}$ to the empty set. Reading it
backwards creates a pair.

Given two framed $0$-manifolds with the same sum $d$: cancel opposite pairs in each until each
consists of $|d|$ points of the same sign $\operatorname{sgn} d$ (if $d = 0$, until empty); then
move the points of one onto the points of the other by (b), and fix the frames by (a). $\square$

**Theorem 6.3 (Hopf).** Let $M$ be compact, connected, oriented, without boundary, of dimension
$m$. Two smooth maps $M \to S^m$ are smoothly homotopic if and only if they have the same degree.

*Proof.* Homotopic maps have equal degrees (Chapter 5, Theorem B). Conversely, if $\deg f = \deg g$,
their Pontryagin manifolds have the same $\sum\operatorname{sgn}$ (Claim 6.1), hence are framed
cobordant (Claim 6.2), hence $f \simeq g$ (Theorem B). $\square$

Together with Chapter 5, §5 (every integer is a degree: compose $S^m \to S^m$ of degree $k$ from a
degree-$k$ map of $S^1$ by suspension, or use Theorem C on $|k|$ framed points), this says that the
homotopy classes of maps $S^m \to S^m$ are in bijection with $\mathbb Z$ via the degree: in the
notation of homotopy theory, $\pi_m(S^m) \cong \mathbb Z$. Problem 4 of Chapter 8 removes the word
"smooth".

> **Two remarks without proof (Milnor p. 50).** If $M$ is connected but non-orientable, two maps
> $M \to S^m$ are homotopic iff they have the same degree modulo 2: sliding a point around a loop
> that reverses orientation changes the sign of its frame, so only the parity of the number of
> points survives. And Pontryagin used framed 1- and 2-manifolds in $S^m$ to show that there are
> exactly two homotopy classes of maps $S^{p+1} \to S^p$ and $S^{p+2} \to S^p$ for $p \ge 3$; beyond
> that the method becomes unwieldy, and homotopy theory took over. But the construction runs both
> ways, and it is the seed of Thom's cobordism theory.

### An interactive look at the construction

The figure shows a map from the torus $T^2 = S^1 \times S^1$ (drawn as a square with opposite
edges identified) to the circle $S^1$: a direction field on the torus,
$$\theta(x, y) = 2\pi(n x + m y) + (\text{a smooth periodic wobble}),$$
where $n, m$ are integers. Choose a target direction $y_0$ with the slider. The curves are the
Pontryagin manifold $\theta^{-1}(y_0)$, and the little arrows along them are the framing: the
normal direction in which $\theta$ increases. Change the target and the wobble: the curves move,
split and rejoin, but always by a framed cobordism, and the pair of winding numbers of the family
never changes. Change $n$ or $m$ and it does, because integers cannot be changed continuously.
Theorem B says these winding numbers, with the framing, are all a map $T^2 \to S^1$ remembers up
to homotopy.

<div id="pontryagin-figure"></div>

*(In the printed version this figure is a still image; the interactive version is in the web
edition.)*

---

## 7. Application: skyrmions and hopfions

**Skyrmions.** In a thin magnetic film the magnetization is a unit vector field $n : \mathbb R^2 \to
S^2$ that tends to a fixed direction $n_\infty$ (say "up") far away. Adding a point at infinity to
the plane, as in Chapter 1, makes $n$ a smooth map $\bar n : S^2 \to S^2$, and it has a degree
$Q = \deg\bar n \in \mathbb Z$, the *skyrmion number*. In the physics literature it is written
$$Q = \frac{1}{4\pi}\int_{\mathbb R^2} n \cdot \Bigl(\frac{\partial n}{\partial x}\times\frac{\partial n}{\partial y}\Bigr)\,dx\,dy,$$
the integral of the Jacobian determinant of $n$ (with respect to the area form of $S^2$); that the
integral of the Jacobian of a map between compact oriented surfaces equals the degree times the
target's area follows from the change of variables formula, applied over the regular values (which
have full measure by Sard) using the local inverses of Chapter 1. A skyrmion is a texture with
$Q = \pm 1$: a region where the magnetization points *down* at one point and sweeps around all
directions as one moves outward. By Hopf's theorem, textures with different $Q$ cannot be deformed
into each other; by Theorem B, the Pontryagin manifold, which for $p = m = 2$ is the finite set of
points where $n$ points down, counted with signs, is all that matters. The topological protection
of $Q$ is why skyrmions are pursued as bits for magnetic memory: a skyrmion cannot fade away by a
small perturbation. They were first seen as a lattice in manganese silicide by neutron scattering
in 2009 and imaged directly the year after.

**Hopfions.** In a three-dimensional sample, $n : \mathbb R^3 \to S^2$ with $n \to n_\infty$ at
infinity is a map $\bar n : S^3 \to S^2$. Now $m = 3 > p = 2$: no degree, but a Pontryagin manifold,
which is a framed *link* in $S^3$, the set of points where $n$ points north, with a normal frame.
The framed cobordism class of a link in $S^3$ carries an integer, the *Hopf invariant* (Chapter 8,
Problem 14): the linking number of the preimages of two distinct regular values, equivalently the
linking number of the north curve with the south curve, or the self-linking of the framed north
curve. For the Hopf map $S^3 \to S^2$ the preimages are two circles linked once. A texture with
nonzero Hopf invariant is a *hopfion*; it cannot be deformed to the uniform state, because the
linking of two closed curves cannot change without the curves crossing, which would mean two
different directions at the same point. Hopfions were predicted in field theory (Faddeev 1975),
found numerically as knotted solitons (Battye and Sutcliffe 1998), and observed as "hopfion rings"
in the chiral magnet FeGe by electron holography in 2023. The photograph in that paper is, quite
literally, a Pontryagin manifold: a closed loop of points where the magnetization points one way,
threading a skyrmion string.

**Why the construction, and not just the degree.** The degree answers "how many times does the map
wrap?" and only makes sense when domain and target have the same dimension. The Pontryagin manifold
answers "where does the map hit a chosen value, and how does it approach it?" and makes sense
whenever $m \ge p$. For a texture in a three-dimensional magnet the second question is the one you
can photograph.

---

## 8. Summary of what was silently assumed, now made explicit

| Where | Milnor says | What is actually needed |
|---|---|---|
| p. 42 | "there is a unique vector $w^i(x) \in Tf^{-1}(y)_x^\perp$ that maps to $v_i$" | $df_x$ restricted to the normal space is an isomorphism, by Chapter 2, Lemma 2.2, and dimension count |
| p. 43 | "the space of positive bases is connected" | $GL^+(p)$ path connected, Chapter 6, Lemma 1.1 |
| p. 44 | "each $r_t^{-1}(z)$ lies on the great circle from $y$ to $z$, and hence is a regular value" | the short arc stays within the chord distance of $y$; critical values form a compact set (Lemma 2.2) |
| p. 44 | $F^{-1}(z)$ "provides a framed cobordism" | $F$ is constant in $t$ near the ends, so the framing is horizontal there and $z$ regular for $F$ implies regular for $f$, $g$ (Lemmas 2.2, 2.3) |
| p. 46 | "replace straight lines by geodesics in $M$" | the closest-point retraction of Chapter 6 does the job without geodesics (Theorem 3.1) |
| p. 47 | "choose a smooth map $\varphi : \mathbb R^p \to S^p$…"; "clearly $f$ is smooth" | explicit $\varphi$ with a flat cutoff, checked in the chart at $s_0$; $f \equiv s_0$ on the complement of a compact set (Theorem C) |
| p. 48 | "by Taylor's theorem $\|F(x,u) - u\| \le c_1\|u\|^2$" | $dF_{(x,0)}$ is the projection because $f^*v = g^*v$; compactness of $N \times \bar B_1$ (Lemma 5.1) |
| p. 49 | "an argument completely analogous to the proof of Theorem C constructs a homotopy" | the product neighbourhood of $X$ in $M \times [0,1]$ stays inside $M \times [0,1]$ because the framing is horizontal near the ends (Theorem B) |
| p. 50 | "it is not difficult to see that the framed cobordism class of the 0-manifold is determined by $\sum\operatorname{sgn}$" | the three moves of Claim 6.2, with the orientation bookkeeping along an arc |

**Checked by machine.** Everything in this chapter has been verified in the Lean proof assistant:
framed cobordism, the Pontryagin construction, Lemmas 1–4, Theorems A, B and C, the Product
Neighborhood Theorem and the Hopf theorem. Not formalized: the closing remark that maps from a
non-orientable manifold are classified by the degree modulo 2. See the verified edition, §8, and
*Milnor, proof by proof*, Parts V–VII.