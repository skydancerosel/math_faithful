# Chapter 8. Milnor's seventeen problems, with solutions

*Milnor, "Topology from the Differentiable Viewpoint", §8, consists of seventeen problems "for the
reader". Here they are, each with a complete solution in the style of the preceding chapters. A
reader who has followed the book should try each one before reading on; the solutions are
arranged so that the statement comes first and the argument after a rule.*

---

## Problem 1. The degree of a composition

*Show that $\deg(g \circ f) = \deg g \cdot \deg f$.*

Let $f : M \to N$, $g : N \to P$ be smooth maps between compact connected oriented manifolds of the
same dimension. The regular values of $g$ form an open dense subset of $P$ (Chapter 5, proof of
Theorem B), and so do those of $g \circ f$; pick $z$ in both. For $y \in g^{-1}(z)$ and $x \in
f^{-1}(y)$, $d(g \circ f)_x = dg_y \circ df_x$ is invertible and $dg_y$ is invertible, so $df_x$ is
invertible: every $y \in g^{-1}(z)$ is a regular value of $f$. Since $(g \circ f)^{-1}(z)$ is the
disjoint union of the $f^{-1}(y)$ over $y \in g^{-1}(z)$, and signs multiply,
$$\deg(g \circ f) = \sum_{y \in g^{-1}(z)} \sum_{x \in f^{-1}(y)} \operatorname{sign} dg_y\,
\operatorname{sign} df_x = \sum_{y \in g^{-1}(z)} \operatorname{sign} dg_y \cdot \deg(f; y)
= \deg f \sum_{y \in g^{-1}(z)} \operatorname{sign} dg_y = \deg f \cdot \deg g. \qquad\square$$

## Problem 2. Polynomials have degree $n$

*Show that a complex polynomial of degree $n$ gives a smooth map of the Gauss sphere $S^2$ to
itself of degree $n$.*

Chapter 1, §8, made $P$ into a smooth map $f$ of the Riemann sphere $\widehat{\mathbb C}$. Orient
$\widehat{\mathbb C}$ by the chart $\chi_0$ (the standard orientation of $\mathbb C = \mathbb R^2$);
the change of coordinates to $\chi_\infty$ is $z \mapsto 1/z$, holomorphic with nonzero derivative,
and multiplication by a nonzero complex number $w = a + bi$ is the real matrix $\begin{pmatrix} a &
-b \\ b & a\end{pmatrix}$ with determinant $|w|^2 > 0$, so holomorphic maps preserve orientation and
the two charts orient $\widehat{\mathbb C}$ consistently. For a regular value $y \notin B$ (Chapter
1, Claim 8.5), the equation $P(z) = y$ has $n$ roots counted with multiplicity, all simple because
$P'(z) \ne 0$ at each root ($y$ is not a critical value), so $n$ distinct preimages, each with
$df_z = $ multiplication by $P'(z) \ne 0$, of sign $+1$. Hence $\deg f = n$. $\square$

## Problem 3. Maps that are never antipodal are homotopic

*If $f, g : X \to S^p$ satisfy $\|f(x) - g(x)\| < 2$ for all $x$, then $f \simeq g$, smoothly if $f,
g$ are smooth.*

The hypothesis says $g(x) \ne -f(x)$. Then $(1-t)f(x) + t\,g(x) \ne 0$ for $t \in [0,1]$: if it
vanished, taking norms would give $(1-t) = t$, so $t = \tfrac12$ and $f(x) = -g(x)$. Hence
$$F(x, t) := \frac{(1-t)f(x) + t\,g(x)}{\|(1-t)f(x) + t\,g(x)\|}$$
is a well-defined homotopy $X \times [0,1] \to S^p$ from $f$ to $g$, smooth when $f, g$ are. $\square$

## Problem 4. Smoothing maps and homotopies

*If $X$ is compact, every continuous map $X \to S^p$ is uniformly approximable by smooth maps, and
continuously homotopic smooth maps are smoothly homotopic.*

Let $X \subseteq \mathbb R^k$ be compact and $G : X \to S^p \subseteq \mathbb R^{p+1}$ continuous.
By the Weierstrass approximation theorem applied to each component, there is a polynomial map
$Q : \mathbb R^k \to \mathbb R^{p+1}$ with $\|Q(x) - G(x)\| < \varepsilon$ on $X$, for any given
$\varepsilon < 1$. Then $\|Q(x)\| > 1 - \varepsilon > 0$, so $\tilde G := Q/\|Q\|$ is smooth on a
neighbourhood of $X$, maps into $S^p$, and
$\|\tilde G(x) - G(x)\| \le \|\tilde G(x) - Q(x)\| + \|Q(x) - G(x)\| < \varepsilon + \varepsilon$.
For the second statement, let $H : X \times [0,1] \to S^p$ be a continuous homotopy between smooth
$f$ and $g$. Apply the first part to $H$ on the compact set $X \times [0,1] \subseteq \mathbb R^{k+1}$
with $\varepsilon = \tfrac14$: a smooth $\tilde H$ with $\|\tilde H - H\| < \tfrac12$. Then
$\tilde H(\cdot, 0)$ is smooth and within $\tfrac12 < 2$ of $f$, so smoothly homotopic to $f$ by
Problem 3; likewise $\tilde H(\cdot, 1) \simeq g$; and $\tilde H$ is a smooth homotopy between them.
Concatenate (Chapter 4, Claim 1.1). $\square$

## Problem 5. Maps into a higher-dimensional sphere are null-homotopic

*If $m < p$, every map $M^m \to S^p$ is homotopic to a constant.*

By Problem 4 we may assume $f$ smooth. Since $m < p$, every point of $M$ is a critical point, so
$f(M)$ is the set of critical values, which has measure zero by Sard's theorem (via charts, as in
Brown's theorem); in particular $f$ is not onto. Choose $y \notin f(M)$ and let $h : S^p \setminus
\{y\} \to \mathbb R^p$ be stereographic projection. Then $F(x, t) := h^{-1}\bigl((1-t)\,h(f(x))\bigr)$
is a smooth homotopy from $f$ to the constant map $h^{-1}(0)$. $\square$

## Problem 6. Brouwer's fixed point theorem for spheres

*A map $f : S^n \to S^n$ with $\deg f \ne (-1)^{n+1}$ has a fixed point.*

If $f(x) \ne x$ for all $x$, then $f(x) \ne -\alpha(x)$ where $\alpha(x) = -x$, so $\|f(x) -
\alpha(x)\| < 2$ and $f \simeq \alpha$ by Problem 3. Hence $\deg f = \deg\alpha = (-1)^{n+1}$
(Chapter 5, §5), contrary to hypothesis. $\square$

## Problem 7. Maps of odd degree carry some antipodal pair to an antipodal pair

*A map $f : S^n \to S^n$ of odd degree carries some pair $\{x, -x\}$ to a pair $\{y, -y\}$.*

Suppose $f(-x) \ne -f(x)$ for all $x$. Then $f(x) + f(-x) \ne 0$, and
$$h(x) := \frac{f(x) + f(-x)}{\|f(x) + f(-x)\|}$$
is a smooth map $S^n \to S^n$ with $h(-x) = h(x)$. It is homotopic to $f$ by Problem 3: $h(x) =
-f(x)$ would mean $f(x) + f(-x) = -\lambda f(x)$ with $\lambda > 0$, so $f(-x) = -(1+\lambda) f(x)$,
impossible for unit vectors. So $\deg h = \deg f$. But an even map has even degree: let $y$ be a
regular value of $h$; the preimage $h^{-1}(y)$ is invariant under $\alpha$ and contains no fixed
point of $\alpha$, so it splits into pairs $\{x, -x\}$. Differentiating $h = h \circ \alpha$ gives
$dh_x = dh_{-x} \circ d\alpha_x$, so $\operatorname{sign} dh_x = \operatorname{sign} dh_{-x} \cdot
(-1)^{n+1}$: each pair contributes $\pm 2$ or $0$ to the degree. Hence $\deg h$ is even, and so is
$\deg f$. $\square$

## Problem 8. Tangent spaces of products

*For $M \subseteq \mathbb R^k$, $N \subseteq \mathbb R^l$, show $T(M \times N)_{(x,y)} = TM_x \times TN_y$.*

If $g : U \to M$ and $h : V \to N$ are parametrizations around $x$ and $y$, then $g \times h : U
\times V \to M \times N$ is a parametrization around $(x, y)$ (smooth, injective, with inverse
$(g^{-1}, h^{-1})$ locally extended), so $M \times N$ is a manifold of dimension $m + n$, and
$d(g \times h)_{(u,v)} = dg_u \times dh_v$ has image $\operatorname{im} dg_u \times \operatorname{im}
dh_v = TM_x \times TN_y$. $\square$

## Problem 9. The graph of a smooth map

*The graph $\Gamma = \{(x, f(x))\}$ of $f : M \to N$ is a smooth manifold with $T\Gamma_{(x,y)} =$
the graph of $df_x$.*

The map $\gamma(x) := (x, f(x))$ is smooth $M \to M \times N$, injective, with inverse the
projection $\Gamma \to M$, which is the restriction of a linear map and hence smooth. So $\gamma$ is
a diffeomorphism $M \to \Gamma$, and composing it with parametrizations of $M$ gives parametrizations
of $\Gamma$: $\Gamma$ is an $m$-manifold. Its tangent space is the image of $d\gamma_x = (\mathrm{id},
df_x)$, namely $\{(v, df_x v) : v \in TM_x\}$, the graph of $df_x$ inside $TM_x \times TN_y$. $\square$

## Problem 10. The tangent bundle

*$TM = \{(x, v) \in M \times \mathbb R^k : v \in TM_x\}$ is a smooth manifold, and $f \mapsto df$ is
functorial.*

For a parametrization $g : U \to M$, define $\tilde g : U \times \mathbb R^m \to TM$, $\tilde g(u,
w) := (g(u), dg_u(w))$. It is smooth, injective ($g$ is, and $dg_u$ is injective by Chapter 1, Claim
3.2), and its image is $\{(x, v) : x \in g(U)\}$, open in $TM$. Its inverse is smooth: $x \mapsto
g^{-1}(x)$ is smooth (locally the restriction of a smooth $F$ with $F \circ g = \mathrm{id}$), and
$w = dF_x(v)$ because $dF_x \circ dg_u = \mathrm{id}$. So the $\tilde g$ are parametrizations and
$TM$ is a $2m$-manifold. For smooth $f : M \to N$, the map $df : TM \to TN$, $(x, v) \mapsto (f(x),
df_x v)$, reads in these parametrizations as $(u, w) \mapsto (\varphi(u), d\varphi_u w)$ with
$\varphi = h^{-1} \circ f \circ g$, which is smooth. The identities $d(\mathrm{id}) = \mathrm{id}$
and $d(g \circ f) = dg \circ df$ are the chain rule, pointwise. $\square$

## Problem 11. The normal bundle and the $\varepsilon$-neighbourhood

*$E = \{(x, v) : v \perp TM_x\}$ is a smooth manifold; for compact $M$, $(x, v) \mapsto x + v$ maps
the $\varepsilon$-neighbourhood of $M \times 0$ in $E$ diffeomorphically onto $N_\varepsilon$.*

This is Chapter 6, Proposition 4.1, where it was proved in full for use in the Poincaré–Hopf
theorem. $\square$

## Problem 12. The closest-point retraction, and smoothing maps into a manifold

*$r(x + v) = x$ is the closest point of $M$; using $r$, prove Problem 4 with $S^p$ replaced by a
compact manifold $M$.*

The first statement is Chapter 6, Proposition 4.1 (i). For the second: let $X$ be compact and
$G : X \to M \subseteq \mathbb R^k$ continuous. Choose $\varepsilon$ as in Proposition 4.1 and a
polynomial $Q$ with $\|Q - G\| < \varepsilon$ on $X$ (Weierstrass). Then $Q(X) \subseteq
N_\varepsilon$, and $\tilde G := r \circ Q$ is smooth with values in $M$ and $\|\tilde G(x) - G(x)\|
\le \|r(Q(x)) - Q(x)\| + \|Q(x) - G(x)\| < 2\varepsilon$, because $r(Q(x))$ is the closest point of
$M$ to $Q(x)$ and $G(x) \in M$ is within $\varepsilon$. For homotopies: approximate a continuous
homotopy $H$ by a smooth $\tilde H = r \circ Q$ within $\varepsilon$; for smooth $f$ within
$\varepsilon$ of $\tilde H(\cdot, 0)$, the segment $(1-t)f(x) + t\tilde H(x, 0)$ stays within
$\varepsilon$ of $f(x) \in M$, so $r$ of it is a smooth homotopy in $M$. Concatenate. $\square$

## Problem 13. Linking numbers

*For disjoint compact oriented boundaryless $M^m, N^n \subseteq \mathbb R^{k+1}$ with $m + n = k$,
$\lambda(x, y) = (x - y)/\|x - y\|$ has degree $l(M, N)$. Prove $l(N, M) = (-1)^{(m+1)(n+1)}
l(M, N)$; prove $l(M, N) = 0$ if $M$ bounds an oriented $X$ disjoint from $N$; define linking in
$S^{m+n+1}$.*

*Symmetry.* Let $\sigma : N \times M \to M \times N$ swap the factors and $\alpha$ the antipodal
map of $S^k$. Then $\lambda_{N,M} = \alpha \circ \lambda_{M,N} \circ \sigma$. With product
orientations, $\sigma$ has degree $(-1)^{mn}$ (moving $n$ vectors past $m$ vectors in an ordered
basis is $mn$ transpositions), and $\deg\alpha = (-1)^{k+1} = (-1)^{m+n+1}$ (Chapter 5). By
Problem 1, $l(N, M) = (-1)^{mn + m + n + 1} l(M, N) = (-1)^{(m+1)(n+1)} l(M, N)$.

*Bounding.* If $M = \partial X$ with $X$ compact oriented and $X \cap N = \varnothing$, then
$\lambda$ extends to $X \times N \to S^k$ by the same formula, and $\partial(X \times N) = M \times N$
with the product orientation (the outward normal lies in the $X$ factor, which comes first). By
Chapter 5, Lemma 3.1, $\deg\lambda = 0$.

*In the sphere.* For disjoint $M, N \subseteq S^{m+n+1}$, the union $M \cup N$ has measure zero,
so there is a point $q$ outside it; stereographic projection $h_q$ from $q$ carries $M, N$ to
disjoint submanifolds of $\mathbb R^{m+n+1}$, and one defines $l(M, N) := l(h_q(M), h_q(N))$. It
does not depend on $q$: two admissible points $q, q'$ can be joined by a path $q_t$ in the
complement of $M \cup N$ (the complement of a compact set of dimension $\le \max(m,n) \le m+n-1$,
codimension at least $2$, is connected: a path between $q$ and $q'$ can be perturbed off it by
Sard's theorem applied to the map (parameter, perturbation) $\mapsto$ sphere), and then
$(x, y, t) \mapsto \lambda(h_{q_t}(x), h_{q_t}(y))$ is a homotopy, so the degree is constant by
Chapter 5, Theorem B. $\square$

## Problem 14. The Hopf invariant

*For $f : S^{2p-1} \to S^p$ and regular values $y \ne z$, the manifolds $f^{-1}(y)$, $f^{-1}(z)$
are oriented as in Chapter 5 and $l(f^{-1}(y), f^{-1}(z))$ is defined. Prove: (a) it is locally
constant in $y$; (b) if $\|f - g\| < \|y - z\|$ pointwise and $y, z$ are regular for $g$ too, then
$l(f^{-1}(y), f^{-1}(z)) = l(g^{-1}(y), f^{-1}(z)) = l(g^{-1}(y), g^{-1}(z))$; (c) it depends only
on the homotopy class of $f$, not on $y, z$. This integer $H(f)$ is the Hopf invariant.*

*Orientation.* $f^{-1}(y)$ has dimension $2p - 1 - p = p - 1$, and $(p-1) + (p-1) + 1 = 2p - 1$, so
linking numbers in $S^{2p-1}$ make sense. Orient $f^{-1}(y)$ so that a basis of its tangent space
followed by the framing $f^*v$ is a positive basis of $T(S^{2p-1})$; this is the orientation Chapter
5, Lemma 3.1, used for the arcs of $F^{-1}(y)$.

*(a)* Let $y'$ be close to $y$, with the short arc from $y$ to $y'$ consisting of regular values
and avoiding $z$. Chapter 7, Lemma 2.2, gives rotations $r_t$ and the manifold $X = F^{-1}(y')
\subseteq S^{2p-1} \times [0,1]$, $F(x, t) = r_t f(x)$, whose slice at height $t$ is $N_t :=
f^{-1}(r_t^{-1} y')$, with $N_0 = f^{-1}(y')$ and $N_1 = f^{-1}(y)$; the framing $F^*v$ orients
$X$ compatibly with the orientations of $N_0$ and $N_1$ (up to the boundary sign of Chapter 5,
which is the same at both ends of the comparison below). Every $N_t$ is disjoint from $f^{-1}(z)$
because $r_t^{-1}y' \ne z$. Choose $q \in S^{2p-1}$ outside the measure-zero set $\bigcup_t N_t
\cup f^{-1}(z)$ and project stereographically. The map $\Lambda : X \times f^{-1}(z) \to S^{2p-2}$,
$((x,t), x') \mapsto \lambda(h_q x, h_q x')$, is smooth and defined everywhere, and $\partial(X
\times f^{-1}(z)) = (N_1 - N_0) \times f^{-1}(z)$ as oriented manifolds. By Chapter 5, Lemma 3.1,
$\deg\Lambda|_{\partial} = 0$, i.e. $l(f^{-1}(y), f^{-1}(z)) = l(f^{-1}(y'), f^{-1}(z))$.

*(b)* Measure distances along the sphere by angle; the hypothesis $\|f - g\| < \|y - z\|$ becomes
$d(f(x), g(x)) \le d(y, z) - \delta$ for some $\delta > 0$ (compactness). Let $F_t(x)$ be the point
at fraction $t$ along the short great-circle arc from $f(x)$ to $g(x)$; $F$ is a smooth homotopy
with $d(F_t(x), f(x)) \le d(y,z) - \delta$ (reparametrize to be constant near $t = 0, 1$). Choose a
regular value $y'$ of $F$ with $d(y', y) < \delta/2$; then $y'$ is regular for $f$ and $g$ (Chapter
7, Lemma 2.3), and $X := F^{-1}(y')$ is disjoint from $f^{-1}(z) \times [0,1]$: if $f(x) = z$ then
$d(F_t(x), z) \le d(y,z) - \delta < d(y', z)$, so $F_t(x) \ne y'$. Now the argument of (a), with this
$X$, gives $l(f^{-1}(y'), f^{-1}(z)) = l(g^{-1}(y'), f^{-1}(z))$; combined with (a) for $f$ and for
$g$ (moving $y'$ back to $y$), $l(f^{-1}(y), f^{-1}(z)) = l(g^{-1}(y), f^{-1}(z))$. The second
equality is the same argument with the roles of the two manifolds exchanged (Problem 13's symmetry
shows nothing is lost by exchanging them).

*(c)* *Independence of $y, z$.* For a rotation $r$ of $S^p$ close to the identity, $\|r \circ f - f\|
< \|y - z\|$, so by (b), $l(f^{-1}(y), f^{-1}(z)) = l((rf)^{-1}(y), (rf)^{-1}(z)) = l(f^{-1}(r^{-1}y),
f^{-1}(r^{-1}z))$: the pair $(y, z)$ can be moved by small rotations without changing the linking
number, and by (a) $y$ (and, symmetrically, $z$) can be moved alone within regular values. Since
the regular values are open and dense and rotations act transitively on pairs at a given angle, any
two admissible pairs are connected by such moves. *Homotopy invariance.* Given a smooth homotopy
$F_t$ from $f$ to $g$, uniform continuity gives $0 = t_0 < \dots < t_r = 1$ with $\|F_{t_i} -
F_{t_{i+1}}\| < 1$; for each $i$ choose common regular values $y_i, z_i$ of $F_{t_i}$ and
$F_{t_{i+1}}$ with $\|y_i - z_i\| > 1$ (possible: regular values are open dense, and nearly antipodal
pairs exist), and apply (b). $\square$

## Problem 15. Properties of the Hopf invariant, and the Hopf fibration

*If $p$ is odd, $H(f) = 0$. For $S^{2p-1} \xrightarrow{f} S^p \xrightarrow{g} S^p$, $H(g \circ f) =
(\deg g)^2 H(f)$. The Hopf fibration $\pi(z_1, z_2) = h^{-1}(z_1/z_2)$ has $H(\pi) = 1$.*

*Odd $p$.* By Problem 13 with $m = n = p - 1$, $l(f^{-1}(z), f^{-1}(y)) = (-1)^{p^2} l(f^{-1}(y),
f^{-1}(z)) = -H(f)$ for $p$ odd; by (c) the left side is also $H(f)$. So $H(f) = 0$.

*Composition.* Choose $y, z$ regular for $g$ and for $g \circ f$. Then $(g\circ f)^{-1}(y) =
\bigsqcup_{y_i \in g^{-1}(y)} f^{-1}(y_i)$, each piece carrying its orientation multiplied by
$\operatorname{sign} dg_{y_i}$ (the framing $(g \circ f)^* v = f^*(dg^{-1}v)$ is positive or negative
at $y_i$ accordingly), and similarly for $z$. The linking number is additive in each variable
over disjoint unions and changes sign with orientation, so
$$H(g \circ f) = \sum_{i,j} \operatorname{sign} dg_{y_i}\,\operatorname{sign} dg_{z_j}\;
l\bigl(f^{-1}(y_i), f^{-1}(z_j)\bigr) = \Bigl(\sum_i \operatorname{sign} dg_{y_i}\Bigr)\Bigl(\sum_j
\operatorname{sign} dg_{z_j}\Bigr) H(f) = (\deg g)^2 H(f),$$
using (c) for each pair $(y_i, z_j)$.

*The Hopf fibration.* Write points of $S^3 \subseteq \mathbb C^2$ as $(z_1, z_2)$ with $|z_1|^2 +
|z_2|^2 = 1$, and $\pi(z_1, z_2) = h^{-1}(z_1/z_2) \in S^2$, with $\pi = h^{-1}(\infty)$ when $z_2 =
0$. The fibre over $h^{-1}(c)$ is the great circle $\{z_1 = c z_2\} \cap S^3$, and every value is
regular ($\pi$ is a submersion: in the chart $c = z_1/z_2$ its derivative has rank $2$). Take
$y = h^{-1}(1)$ and $z = h^{-1}(-1)$: the fibres are $C_+ = \{(w, w)/\sqrt2 : |w| = 1\}$ and
$C_- = \{(w, -w)/\sqrt2\}$. Project stereographically from $q = (0, i) \in S^3$, which lies on
neither: $(x_1, x_2, x_3, x_4) \mapsto (x_1, x_2, x_3)/(1 - x_4)$. With $w = e^{i\varphi}$,
$$C_+ \mapsto \frac{(\cos\varphi, \sin\varphi, \cos\varphi)}{\sqrt2 - \sin\varphi}, \qquad
C_- \mapsto \frac{(\cos\varphi, \sin\varphi, -\cos\varphi)}{\sqrt2 + \sin\varphi},$$
circles in the planes $\{x_1 = x_3\}$ and $\{x_1 = -x_3\}$ respectively. Compute the degree of the
linking map $\lambda(a, b) = (a - b)/\|a - b\|$ at the value $-e_2$: $a - b \parallel e_2$ forces
$a, b$ on the common line $x_1 = x_3 = 0$ of the two planes, where $\cos\varphi = 0$; $C_+$ meets it
at $x_2 = \sqrt2 + 1$ and $x_2 = -(\sqrt2 - 1)$, $C_-$ at $x_2 = \sqrt2 - 1$ and $x_2 = -(\sqrt2+1)$.
Of the four pairs, exactly one has $a - b$ pointing in the direction $-e_2$: $a = (0, -(\sqrt2-1),
0)$, $b = (0, \sqrt2 - 1, 0)$. At this pair the tangent to $C_+$ is parallel to $(1, 0, 1)$ and the
tangent to $C_-$ to $(-1, 0, 1)$ (differentiate the parametrizations at $\varphi = -\pi/2$ and
$\varphi = \pi/2$; the denominators have zero derivative there), so $d(a - b)$ maps onto the plane
spanned by $(1,0,1)$ and $(-1,0,1)$, the tangent plane of $S^2$ at $-e_2$: the value $-e_2$ is
regular with a single preimage, and $H(\pi) = \deg\lambda = \pm 1$. The sign needs care. With
the book's own conventions (spheres oriented as boundaries of balls, the fibres oriented as
preimages as in Chapter 5, $C_+ \times C_-$ oriented as a product, and $\lambda$ as above) it is
$-1$, not the $+1$ of the problem statement: the machine-checked edition carries out the
determinant computation at the pair $(a, b)$ and records this value (V8.15 there). The sign flips
under any one of three equally natural changes of convention: $\lambda(a, b) = (b - a)/\|b - a\|$,
the product taken in the order $C_- \times C_+$, or the target sphere of $\lambda$ oriented the
other way; the book's $+1$ corresponds to one of these. Reversing the orientation of $S^3$, or of
the target $S^2$ of $\pi$, reverses both fibres at once and leaves $H(\pi)$ unchanged, and the
order of the vectors in the preimage orientation (Milnor's ordering of the framing) makes no
difference here. The important fact is $|H(\pi)| = 1$: the Hopf map is not null-homotopic,
although $\pi_3(S^2)$ is invisible to the degree. $\square$

## Problem 16. Transversality

*Submanifolds $N, N' \subseteq M$ intersect transversally if $TN_x + TN'_x = TM_x$ at every
$x \in N \cap N'$. If $N$ is framed, it can be deformed slightly to meet a given $N'$ transversally,
and the intersection is then a manifold.*

Let $g : N \times \mathbb R^p \to V$ be a product neighbourhood (Chapter 7, Theorem 3.1) and $\pi :
V \to \mathbb R^p$ the projection. For $u \in \mathbb R^p$ let $N_u := g(N \times \{u\}) = \pi^{-1}(u)$,
a framed submanifold isotopic to $N = N_0$ through $N_{su}$, $s \in [0,1]$; for small $u$ it is a
small deformation of $N$. Consider the smooth map $\pi|_{N' \cap V} : N' \cap V \to \mathbb R^p$.
**Claim:** $N_u$ meets $N'$ transversally iff $u$ is a regular value of $\pi|_{N' \cap V}$. Indeed,
at $x \in N_u \cap N'$, $d\pi_x : TM_x \to \mathbb R^p$ is onto with kernel $T(N_u)_x$, so
$TN_u + TN'_x = TM_x$ iff $d\pi_x(TN'_x) = \mathbb R^p$, which is regularity of $x$ for
$\pi|_{N'}$. By Sard's theorem, regular values of $\pi|_{N' \cap V}$ are dense, so there are
arbitrarily small $u$ for which $N_u$ is transverse to $N'$, and then $N_u \cap N' = (\pi|_{N' \cap
V})^{-1}(u)$ is a manifold of dimension $\dim N' - p = n + n' - m$ by Chapter 2, Lemma 2.1 (empty if
$n + n' < m$). $\square$

## Problem 17. Products and the cohomotopy group

*Let $\Pi^p(M)$ be the set of framed cobordism classes of codimension $p$ in $M$. Define
$\Pi^p(M) \times \Pi^q(M) \to \Pi^{p+q}(M)$ by transverse intersection, and for $p \ge \tfrac12 m +
1$ make $\Pi^p(M)$ an abelian group by disjoint union.*

*Product.* Given framed $(N, v)$ of codimension $p$ and $(N', w)$ of codimension $q$, deform $N$ by
Problem 16 to meet $N'$ transversally. At $x \in N \cap N'$, transversality gives $T(N \cap N')_x =
TN_x \cap TN'_x$ and $TM_x = TN_x + TN'_x$, so the normal space of $N \cap N'$, of dimension $p + q$,
is spanned by the normal spaces of $N$ and $N'$ (the projection $TM_x \to TN_x^\perp$ restricted to
$TN'_x$ is onto, since $TN_x + TN'_x = TM_x$; project $v$ and $w$ onto the normal space of $N \cap
N'$ and concatenate). This gives a framed submanifold of codimension $p + q$. Well defined on
classes: a framed cobordism of $N$ inside $M \times [0,1]$, made transverse to $N' \times [0,1]$
by the same argument, intersects it in a framed cobordism of the intersections; and two transverse
deformations of $N$ are joined by a framed cobordism (the isotopy $N_{(1-s)u + su'}$), which after
a further transverse perturbation gives a cobordism between the two intersections.

*Group structure for $p \ge \tfrac12 m + 1$.* Then $n = m - p \le \tfrac12 m - 1$, so $2n < m - 1$:
two framed $n$-submanifolds can be made disjoint by a small isotopy (Problem 16 with $N' = $ the
other one: transverse intersection has negative dimension, so is empty), and likewise two
$(n+1)$-dimensional cobordisms inside $M \times [0,1]$, since $2(n+1) < m + 1$. Define $[N] + [N']
:= [N \sqcup N']$ after making them disjoint; well defined because disjoint cobordisms can be taken
disjoint, and any two ways of making $N$, $N'$ disjoint are connected through disjoint isotopies.
Associativity and commutativity are clear (disjoint union is), the empty manifold is the identity,
and the inverse of $(N, v)$ is $(N, \bar v)$ with the first framing vector negated: $N \sqcup N$
with framings $v$ and $\bar v$ is the boundary of the framed cobordism obtained by pushing a copy of
$N$ into $M \times [0,1]$ along a half-turn in the plane of $v^1$ and $\partial_t$, exactly as in
Chapter 7, Claim 6.2(c). The result is the *cohomotopy group* $\pi^p(M)$; by Chapter 7 it is the
set of homotopy classes of maps $M \to S^p$ with a group structure, and for $M = S^m$ it is the
homotopy group $\pi_m(S^p)$. $\square$

---

**Checked by machine.** All seventeen problems have been verified in the Lean proof assistant. One
value differs from the statement of Problem 15, as explained above: with the book's conventions the
Hopf fibration has Hopf invariant $-1$. See the verified edition, §9, and *Milnor, proof by proof*,
Parts VIII–XI.