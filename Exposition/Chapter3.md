# Chapter 3. Why caustics are thin: the theorem of Sard and Brown

*Milnor, "Topology from the Differentiable Viewpoint", §2 (statement) and §3 (proof), rewritten
for a first-year student who wants to know what the theorem is for. Every proof is complete.*

---

## 0. The bright lines on the bottom of a swimming pool

Sunlight falls on a swimming pool whose surface is rippled by a breeze. On the floor of the pool
you see a moving network of bright lines. They are never bright *patches*: the light gathers into
curves, sharp and thin, with ordinary illumination between them. Why lines?

Here is the geometry. Each point $x$ of the water surface receives a vertical ray, bends it at the
surface by refraction, and sends it to a point $f(x)$ on the floor. For a surface of height
$\eta(x)$ with gentle slopes, Snell's law gives

$$f(x) = x - \kappa\,\nabla\eta(x), \qquad \kappa = h\Bigl(1 - \frac1n\Bigr),$$

where $h$ is the depth and $n \approx 4/3$ the refractive index of water (the ray bends toward
the surface normal, which tilts against the slope). So $f$ is a smooth map from the plane of the
surface to the plane of the floor. A small patch of surface of area $dA$ around $x$ sends its
light to a patch of area $|\det df_x|\,dA$ around $f(x)$. The brightness at a floor point $y$ is
therefore

$$I(y) = \sum_{x \,:\, f(x) = y} \frac{1}{|\det df_x|},$$

one term for each ray that arrives. Where $\det df_x = 0$, the light from a patch of surface is
squeezed into a set of smaller dimension, and the brightness is infinite: these floor points are
the *caustics*. In the language of Chapter 1, the points where $\det df_x = 0$ are the critical
points of $f$, and the caustics are the *critical values*.

Now the question has a precise form. The caustics are the image under a smooth map of the set
where a smooth function ($\det df$) vanishes. Why does that image have no area? The set
$\{\det df = 0\}$ is typically a curve on the surface, so its image is a curve on the floor, which
is the everyday answer. But $\det df$ could vanish on a fat set, an entire region of the surface
could be flat, and then the critical set has positive area. The theorem of this chapter says it
does not matter: **the critical values of a smooth map always form a set of measure zero.** A flat
region of surface is sent to a single point; a region where $f$ folds is sent to a curve; there
is no way to arrange the folding so that infinitely bright light covers an area. That is Sard's
theorem, and the picture on the floor of the pool is a picture of it.

The consequences run through the rest of the book. At almost every floor point $y$ finitely many
rays arrive, and by Chapter 1 the number of rays is constant on each region between the caustics;
every construction in Chapters 4 to 7 begins by choosing a regular value, and it is this theorem
that says one exists. At the end of the chapter the same theorem, in one dimension, explains why a
rainbow is a thin arc at $42°$ from the point opposite the sun, and why red is on the outside.

---

## 1. Statement of the theorem (Milnor p. 10)

**Definition.** Let $f : U \to \mathbb R^p$ be smooth, $U \subseteq \mathbb R^n$ open. A point
$x \in U$ is a *critical point* if $df_x : \mathbb R^n \to \mathbb R^p$ is not surjective. Write
$C$ for the set of critical points. A point of $\mathbb R^p$ is a *critical value* if it is
$f(x)$ for some critical point $x$, and a *regular value* otherwise.

When $n = p$, "not surjective" is the same as "not invertible", so this agrees with Chapter 1.
When $n < p$ every point is critical, and the theorem says that $f(U)$ has measure zero: a
smooth curve in the plane has no area, and a smooth surface in space has no volume.

**Theorem 1.1 (Sard).** Let $E$, $F$ be finite-dimensional real vector spaces, $U \subseteq E$
open, $f : U \to F$ smooth. Then $f(C)$ has measure zero in $F$.

**Corollary 1.2.** The regular values of $f$ are dense in $F$.

*Proof of the corollary from the theorem.* A set of measure zero cannot contain a ball, so its
complement meets every ball. $\square$

We state the theorem for abstract finite-dimensional spaces rather than for $\mathbb R^n$ and
$\mathbb R^p$ because the proof is an induction on $n$ that passes from $E$ to a hyperplane
$K \subseteq E$, and from $F$ to a hyperplane $F_1 \subseteq F$. Hyperplanes are not literally
$\mathbb R^{n-1}$, and choosing coordinates on them every time would only add noise.

**Background needed beyond Chapters 1 and 2.**

* *Lebesgue measure* on $\mathbb R^p$: a way of assigning a "volume" $\mu(A) \in [0,\infty]$ to
  sets $A \subseteq \mathbb R^p$ so that boxes get their usual volume, $\mu$ is unchanged by
  translation, and $\mu(\bigcup A_i) \le \sum \mu(A_i)$ for countably many sets. A set of
  measure zero contains no ball, so its complement is dense. Any two such "volumes" on a
  finite-dimensional space differ by a constant factor (uniqueness of Haar measure); in
  particular they have the same null sets, which is all we use.
* *Fubini's theorem*, in the following form. Let $A \subseteq \mathbb R \times \mathbb R^{p-1}$ be
  measurable (for us: compact). If every slice $A_t = \{v : (t, v) \in A\}$ has measure zero in
  $\mathbb R^{p-1}$, then $A$ has measure zero in $\mathbb R^p$.
* *Hausdorff dimension* (only for one step): a set of Hausdorff dimension less than $p$ has
  measure zero in $\mathbb R^p$, and a map that is Hölder continuous with exponent $\alpha$
  divides Hausdorff dimension by at most $\alpha$. Milnor avoids this language and counts cubes
  instead; the cube count *is* the proof of these two facts, so either route may be taken.

### An interactive look at the theorem

The figure is the floor of the pool. The surface height $\eta$ is a fixed sum of a few sine
waves; each of $250{,}000$ surface points $x$ sends its ray to $f(x) = x - \kappa\nabla\eta(x)$,
and the picture shows how many rays land in each small cell of the floor. The first slider is
$\kappa$, which grows with the depth of the pool; the second is the height of the waves.

For small $\kappa$ the map is close to the identity, every floor point receives exactly one ray,
and the floor is evenly lit. Increase $\kappa$ until $\det df$ first vanishes somewhere: the
caustics appear, as curves, and the floor divides into regions receiving $1$ or $3$ rays. Increase
it further and the network becomes intricate, but it never thickens into a patch. The theorem
says it cannot, at any value of the sliders.

<div id="caustic-figure"></div>

*(In the printed version this figure is a still image; the interactive version is in the web
edition.)*

---

## 2. Brown's theorem on manifolds (Milnor pp. 10–11)

**Definition.** For a smooth map $f : M \to N$ between manifolds (of any dimensions), $x$ is a
*critical point* if $df_x : TM_x \to TN_{f(x)}$ is not surjective. Critical and regular values are
defined as before.

**Theorem 2.1 (Brown).** Let $M$ be a manifold covered by countably many charts (for instance a
subset of $\mathbb R^k$), $N$ a manifold, both without boundary, and $f : M \to N$ smooth. Then
the regular values of $f$ are dense in $N$.

Milnor's whole proof is the phrase "since $M$ can be covered by a countable collection of
neighborhoods each diffeomorphic to an open subset of $\mathbb R^m$". Here is what that phrase
contains.

*Proof.* Let $W \subseteq N$ be open and nonempty; we must find a regular value in $W$. Suppose
not, so every point of $W$ is a critical value.

*Step 1: pass to a chart of $N$.* Pick $y_1 \in W$ and a chart $\psi$ of $N$ around $y_1$, a
diffeomorphism from an open neighbourhood of $y_1$ onto an open subset of $F = \mathbb R^n$. The
set $\psi(W \cap \operatorname{dom}\psi)$ is a neighbourhood of $\psi(y_1)$ in $F$, so it has
positive measure.

*Step 2: countably many charts of $M$.* Every point of $M$ lies in the domain of a chart. By
hypothesis, countably many of these domains, say those of charts $\varphi_1, \varphi_2, \dots$,
already cover $M$. (For a subset of $\mathbb R^k$ this follows from the Lindelöf property: every
open cover of a subset of $\mathbb R^k$ has a countable subcover, because $\mathbb R^k$ has a
countable base of open balls with rational centres and radii.)

*Step 3: read $f$ in charts.* For each $i$ let $U_i \subseteq E = \mathbb R^m$ be the open set of
points $u$ in the image of $\varphi_i$ with $f(\varphi_i^{-1}(u)) \in \operatorname{dom}\psi$, and
let $F_i := \psi \circ f \circ \varphi_i^{-1} : U_i \to F$. This is a smooth map between open
subsets of Euclidean spaces.

*Step 4: critical points correspond.* Let $x \in M$ be a critical point of $f$ with
$x \in \operatorname{dom}\varphi_i$ and $f(x) \in \operatorname{dom}\psi$, and put $u = \varphi_i(x)$.
By the chain rule,
$$d(F_i)_u = d\psi_{f(x)} \circ df_x \circ d(\varphi_i^{-1})_u .$$
The derivative $d\psi_{f(x)}$ is injective: it has $d(\psi^{-1})$ as a left inverse, because
$\psi^{-1} \circ \psi$ is the identity near $f(x)$ and the derivative of the identity is the
identity. Hence if $d(F_i)_u$ were surjective, then $df_x \circ d(\varphi_i^{-1})_u$ would be
surjective, so $df_x$ would be surjective, contradicting that $x$ is critical. So $u$ is a
critical point of $F_i$.

*Step 5: conclude.* Every $y \in W \cap \operatorname{dom}\psi$ is $f(x)$ for a critical point
$x$, which lies in some $\operatorname{dom}\varphi_i$; by Step 4, $\psi(y) = F_i(u)$ with $u$ a
critical point of $F_i$. So
$$\psi(W \cap \operatorname{dom}\psi) \subseteq \bigcup_i F_i(\text{critical points of } F_i).$$
Each set on the right has measure zero by Sard's theorem, and there are countably many, so the
union has measure zero. This contradicts Step 1. $\square$

> **Where the hypotheses come from.** Countably many charts are needed in Step 2. Both manifolds
> are assumed to have no boundary, since Sard's theorem is applied to open subsets of Euclidean
> space; Chapter 2 showed how to handle a boundary by passing to the interior. The target $N$
> carries no measure of its own: Step 1 uses a measure on the model space $F$, and the proof
> works for any choice of Haar measure there.

---

## 3. Proof of Sard's theorem (Milnor §3, pp. 16–19)

Throughout, $f : U \to F$ is smooth, $U \subseteq E$ open, $n = \dim E$, $p = \dim F$. For
$k \ge 1$ let
$$C_k := \{x \in U : \text{all derivatives of } f \text{ of order } 1, 2, \dots, k \text{ vanish at } x\}.$$
So $C_1$ is the set where $df_x = 0$, and $C \supseteq C_1 \supseteq C_2 \supseteq \cdots$ (the
first inclusion needs $p \ge 1$: a zero map onto a nonzero space is not surjective).

In the pool, $C \setminus C_1$ is where the surface folds the light (the generic caustic), $C_1$
is where the surface is momentarily flat to first order, $C_2$ flat to second order, and so on.
The proof treats these separately, because the mechanism that kills the area is different: folds
are handled by slicing (Steps 1 and 2), extreme flatness by a Taylor estimate (Step 3).

The proof is by induction on $n$, for all $F$ at once. For any $k$,
$$C \subseteq (C \setminus C_1) \cup (C_1 \setminus C_2) \cup \dots \cup (C_{k-1} \setminus C_k) \cup C_k,$$
so it suffices to prove that the images of these $k+1$ sets are null. This is Milnor's three
steps: Step 1 handles $C \setminus C_1$, Step 2 handles $C_i \setminus C_{i+1}$ for $i \ge 1$,
Step 3 handles $C_k$ for $k$ large. Steps 1 and 2 use the induction hypothesis in dimension
$n - 1$; Step 3 does not.

**Two degenerate cases first.** If $p = 0$, every linear map to $F$ is surjective, $C = \varnothing$,
and there is nothing to prove; this case must be set aside because the "Haar measure" on a
one-point space is a point mass, so the statement "images of $C_k$ are null" would be false for
$k \ge 1$. If $n = 0$ and $p \ge 1$, then $U$ has at most one point, $f(C)$ is at most one point,
and points have measure zero.

### 3.1 The coordinate change $h(x) = (w(x), x_2, \dots, x_n)$

Steps 1 and 2 use the same device, which we set up once.

**Lemma 3.1.** Let $w : U \to \mathbb R$ be smooth and $\bar x \in U$ with $dw_{\bar x} \ne 0$. Let
$\ell = dw_{\bar x}$, choose $v \in E$ with $\ell(v) = 1$, let $K = \ker \ell$ (a subspace of
dimension $n - 1$), and define
$$H : E \to \mathbb R \times K, \qquad H(x) = \bigl(w(x),\; x - \ell(x)\,v\bigr).$$
Then there are open sets $V \ni \bar x$ in $U$ and $V' \subseteq \mathbb R \times K$ such that $H$
maps $V$ bijectively onto $V'$, with smooth inverse $G : V' \to V$.

(In coordinates where $v = e_1$ and $K = \{x_1 = 0\}$, this is exactly Milnor's
$h(x) = (w(x), x_2, \dots, x_n)$.)

*Proof.* The second component $P(x) = x - \ell(x) v$ lies in $K$ because $\ell(P(x)) = \ell(x) -
\ell(x)\ell(v) = 0$. $H$ is smooth, with derivative $dH_{\bar x} = (\ell, P)$. This linear map is
invertible: its inverse is $(t, z) \mapsto z + t v$, as one checks directly:
$P(x) + \ell(x) v = x$, and $\ell(z + tv) = t$, $P(z + tv) = z$ for $z \in K$. Now apply the
inverse function theorem (Chapter 1, Theorem 4.1). $\square$

The point of the construction: **$H$ carries the level set $\{w = 0\}$ into the hyperplane
$\{0\} \times K$**, because the first component of $H(x)$ is $w(x)$.

### 3.2 Step 3: $f(C_k)$ is null for $(k+1)p > n$

**Lemma 3.2 (Taylor-type bound).** Let $B \subseteq U$ be convex, and suppose
$\|D^{k+1} f(z)\| \le c$ for all $z \in B$. If $x \in B$ and all derivatives of $f$ of orders
$1, \dots, k$ vanish at $x$, then
$$\|f(y) - f(x)\| \le c\,\|y - x\|^{k+1} \qquad\text{for all } y \in B.$$

*Proof, by induction on $k$.* For $k = 0$ this is the mean value inequality: along the segment
from $x$ to $y$ (which lies in $B$ by convexity), $\|df_z\| \le c$, so
$\|f(y) - f(x)\| \le c\|y - x\|$.

For $k + 1$: apply the case $k$ to the map $df : U \to \operatorname{Hom}(E, F)$. Its
derivatives of orders $1, \dots, k$ at $x$ are the derivatives of $f$ of orders $2, \dots, k+1$,
which vanish; and $\|D^{k+1}(df)\| = \|D^{k+2} f\| \le c$ on $B$. So $\|df_z - df_x\| \le
c\|z - x\|^{k+1}$ for $z \in B$, and $df_x = 0$, so $\|df_z\| \le c\|z - x\|^{k+1}$. For $z$ on
the segment from $x$ to $y$, $\|z - x\| \le \|y - x\|$, hence $\|df_z\| \le c\|y - x\|^{k+1}$
there, and the mean value inequality along the segment gives
$\|f(y) - f(x)\| \le c\|y - x\|^{k+1} \cdot \|y - x\|$. $\square$

Milnor states this as "From Taylor's theorem, the compactness of $I^n$, and the definition of
$C_k$" and writes the constant $c$ without comment. The induction above is the honest content
of that sentence: it needs only the mean value inequality, not Taylor's theorem with remainder.

**Proposition 3.3 (Step 3).** Let $B \subseteq U$ be compact and convex, and $(k+1)p > n$. Then
$f(C_k \cap B)$ has measure zero.

*Proof.* $D^{k+1} f$ is continuous, so it is bounded by some $c$ on the compact set $B$. By
Lemma 3.2, for any two points $x, x'$ of $C_k \cap B$ (apply the lemma with $y = x'$),
$$\|f(x') - f(x)\| \le c\,\|x' - x\|^{k+1}.$$
That is, $f$ restricted to $C_k \cap B$ is Hölder continuous with exponent $k + 1$. A Hölder map
with exponent $\alpha$ maps a set of Hausdorff dimension $d$ to a set of Hausdorff dimension at
most $d/\alpha$; $C_k \cap B \subseteq E$ has dimension at most $n$; so $f(C_k \cap B)$ has
Hausdorff dimension at most $n/(k+1) < p$, hence measure zero in $F$. $\square$

> **Milnor's version.** He subdivides a cube $I^n$ of edge $\delta$ into $r^n$ cubes of edge
> $\delta/r$. Each small cube meeting $C_k$ is mapped, by the Hölder bound, into a cube of edge
> $a / r^{k+1}$; the total volume is at most $r^n (a/r^{k+1})^p = a^p r^{n - (k+1)p} \to 0$. That
> computation is precisely the proof that a Hölder map of exponent $k+1$ sends a set of dimension
> $n$ to a set of dimension $\le n/(k+1)$, which is why we can quote it.

To cover all of $C_k$, note that every point of $U$ has a closed ball around it inside $U$, and
countably many such balls cover $C_k$ (Lindelöf again). So $f(C_k)$ is a countable union of null
sets.

### 3.3 Step 2: $f(C_k \setminus C_{k+1})$ is null for $k \ge 1$

**Proposition 3.4 (Step 2).** Assume Sard's theorem holds in dimension $n - 1$, and $p \ge 1$.
Let $k \ge 1$ and $\bar x \in C_k \setminus C_{k+1}$. Then $\bar x$ has a neighbourhood $V$ such
that $f(C_k \cap V)$ has measure zero.

*Proof.* Since $\bar x \in C_k \setminus C_{k+1}$, some derivative of order $k+1$ is nonzero at
$\bar x$: there are vectors $m_0, m_1, \dots, m_k$ with $D^{k+1} f(\bar x)(m_0, \dots, m_k) \ne 0$,
and then a linear functional $\ell_0 : F \to \mathbb R$ with
$\ell_0\bigl(D^{k+1} f(\bar x)(m_0, \dots, m_k)\bigr) \ne 0$. Define
$$w(x) := \ell_0\bigl(D^k f(x)(m_1, \dots, m_k)\bigr).$$
This is a smooth real function (Milnor's $\partial^k f_r / \partial x_{s_2} \cdots \partial x_{s_{k+1}}$).
Two properties:

* $w = 0$ on $C_k$, because $D^k f = 0$ there.
* $dw_{\bar x}(m_0) = \ell_0\bigl(D^{k+1} f(\bar x)(m_0, m_1, \dots, m_k)\bigr) \ne 0$, because the
  derivative of $x \mapsto D^k f(x)$ in direction $m_0$ is $D^{k+1} f(x)(m_0, \cdot)$.

So Lemma 3.1 applies to $w$ at $\bar x$: we get $H : V \to V'$ with inverse $G$, and $H$ carries
$C_k \cap V$ into $\{0\} \times K$. Let $V_0 := \{z \in K : (0, z) \in V'\}$, open in $K$, and
$$\bar g : V_0 \to F, \qquad \bar g(z) := f(G(0, z)).$$
This is Milnor's "restriction of $g = f \circ h^{-1}$ to the hyperplane". It is smooth, and $K$ has
dimension $n - 1$, so by the induction hypothesis $\bar g(\text{critical points of } \bar g)$ is
null. We show $f(C_k \cap V)$ is contained in it. Let $x \in C_k \cap V$ and write $H(x) = (0, z)$
(the first coordinate is $w(x) = 0$). Then $z \in V_0$, and $\bar g(z) = f(G(H(x))) = f(x)$. It
remains to see that $z$ is a critical point of $\bar g$. By the chain rule,
$d\bar g_z = df_x \circ d(G(0,\cdot))_z$, and $df_x = 0$ since $x \in C_k$ with $k \ge 1$. So
$d\bar g_z = 0$, which is not surjective because $p \ge 1$. $\square$

### 3.4 Step 1: $f(C \setminus C_1)$ is null

This is, as Milnor says, "perhaps the hardest" step, and the only one that uses Fubini.

**Proposition 3.5 (Step 1).** Assume Sard's theorem holds in dimension $n - 1$, and $p \ge 1$.
Let $\bar x \in C \setminus C_1$. Then $\bar x$ has a neighbourhood $B$ such that $f(C \cap B)$
has measure zero.

*Proof.*

*(a) The coordinate change.* Since $\bar x \notin C_1$, $df_{\bar x} \ne 0$: there is $u$ with
$df_{\bar x}(u) \ne 0$, and a functional $\ell_0 : F \to \mathbb R$ with
$\ell_0(df_{\bar x}(u)) \ne 0$. Put $w := \ell_0 \circ f$ (Milnor's $f_1$). Then
$dw_{\bar x} = \ell_0 \circ df_{\bar x} \ne 0$, and Lemma 3.1 gives $H : V \to V' \subseteq \mathbb R
\times K$ with inverse $G$. Let $g := f \circ G : V' \to F$ (Milnor's $g = f \circ h^{-1}$).

The key identity: **for $(t, z) \in V'$, $\ell_0(g(t, z)) = t$.** Indeed
$\ell_0(g(t,z)) = w(G(t,z))$ is the first component of $H(G(t,z)) = (t, z)$. This is Milnor's
"$g$ carries hyperplanes into hyperplanes".

*(b) Splitting the target.* Choose $y_0 \in F$ with $\ell_0(y_0) = 1$, let $F_1 := \ker \ell_0$
(dimension $p - 1$), and $Q : F \to F_1$, $Q(y) = y - \ell_0(y) y_0$. Then
$e(y) := (\ell_0(y), Q(y))$ is a linear isomorphism $F \cong \mathbb R \times F_1$ with inverse
$(s, y_1) \mapsto y_1 + s y_0$. Note that $Q(y) = y$ whenever $\ell_0(y) = 0$.

For each $t$ define the slice map
$$g_t : V'_t \to F_1, \qquad g_t(z) := Q(g(t, z)), \qquad V'_t := \{z \in K : (t, z) \in V'\}.$$
This is Milnor's $g^t$. By (a), $g(t, z) = g_t(z) + t\,y_0$, so $g$ is determined by its slices.

*(c) Milnor's block-matrix remark.* **Claim: if $(t, z) \in V'$ is a critical point of $g$, then
$z$ is a critical point of $g_t$.** Write $D = dg_{(t,z)} : \mathbb R \times K \to F$. From the key
identity, $\ell_0 \circ D$ is the projection to the first factor. From the definition of $g_t$ and the
chain rule, $d(g_t)_z(u) = Q(D(0, u))$. Now suppose $d(g_t)_z$ is surjective; we show $D$ is
surjective. Given $y \in F$, let $s = \ell_0(y)$ and $c = D(s, 0)$. The vector $y - c$ satisfies
$\ell_0(y - c) = s - s = 0$, so it lies in $F_1$ and $Q(y - c) = y - c$. By surjectivity of
$d(g_t)_z$ there is $u$ with $Q(D(0,u)) = y - c$; since $\ell_0(D(0,u)) = 0$ we have
$Q(D(0,u)) = D(0,u)$, so $D(0, u) = y - c$ and $D(s, u) = c + (y - c) = y$. $\square_{\text{claim}}$

*(d) Fubini.* Choose a closed ball $B$ around $\bar x$ inside $V$, and let
$T := f(C \cap B)$. The set $C$ is closed in $U$ (surjectivity of a linear map is an open
condition), so $C \cap B$ is compact, and $T$ is compact, hence measurable; so is $e(T)$.

Consider a slice: let $(t, y_1) \in e(T)$, so $(t, y_1) = e(f(x))$ with $x \in C \cap B$. Put
$q = H(x) \in V'$. Then $g(q) = f(x)$, and by the key identity the first coordinate of $q$ is
$\ell_0(f(x)) = t$; write $q = (t, z)$. The point $q$ is a critical point of $g$: by the chain rule
$dg_q = df_x \circ dG_q$, and $df_x$ is not surjective, so neither is $dg_q$. By the claim in (c),
$z$ is a critical point of $g_t$, and $g_t(z) = Q(g(q)) = Q(f(x)) = y_1$. Hence
$$\{y_1 : (t, y_1) \in e(T)\} \subseteq g_t(\text{critical points of } g_t) \qquad \text{for every } t.$$
The right side is null in $F_1$ by the induction hypothesis (applied to $g_t : V'_t \to F_1$, with
$\dim K = n - 1$; any Haar measure on $F_1$ will do). So every slice of $e(T)$ is null, and by
Fubini $e(T)$ is null in $\mathbb R \times F_1$. Transporting back along the isomorphism $e$,
$T$ is null in $F$. $\square$

### 3.5 Assembling the induction

**Theorem 3.6.** For every $n$, Sard's theorem holds for all $E$ of dimension $n$, all $F$, all
Haar measures on $F$, all open $U$, and all smooth $f$.

*Proof.* Induction on $n$. The case $n = 0$ and the case $p = 0$ were done at the start of §3.
Let $n = m + 1$, $p \ge 1$, and assume the theorem in dimension $m$. Take $k := m + 1$; then
$(k+1)p \ge k + 1 > n$. Decompose $C$ as at the start of §3. The image of $C \setminus C_1$ is
null by Proposition 3.5 (each point has a good neighbourhood; countably many cover). The image
of each $C_i \setminus C_{i+1}$, $1 \le i < k$, is null by Proposition 3.4 in the same way. The
image of $C_k$ is null by Proposition 3.3. A finite union of null sets is null. $\square$

> **How much smoothness is really needed?** The proof used derivatives up to order $k + 1$ with
> $k = n$, so $f$ of class $C^{n+1}$ suffices in this argument, and Sard's own theorem needs
> $C^{\max(n-p+1,\,1)}$. Below that the theorem is false: Whitney (1935) built a $C^1$ function
> on $\mathbb R^2$ whose critical set contains an arc on which the function is not constant, so its
> critical values fill an interval. The smoothness is not decoration.

---

## 4. Application: the rainbow is a critical value

Descartes computed the angle of the rainbow in 1637, and his computation is Sard's theorem in one
dimension, together with the observation that the intensity blows up at a critical value.

**The map.** Sunlight enters a spherical raindrop of unit radius and refractive index $n$. A ray
is labelled by its *impact parameter* $b \in [0, 1]$, its distance from the axis through the
centre of the drop. It meets the surface at incidence angle $i$ with $\sin i = b$, refracts to the
angle $r$ with $\sin r = b/n$ (Snell), reflects once off the back of the drop, and refracts out.
Each refraction turns the ray by $i - r$ and the reflection turns it by $\pi - 2r$, so the total
deflection is

$$D(b) = 2(i - r) + (\pi - 2r) = \pi + 2\arcsin b - 4\arcsin\frac{b}{n}.$$

This is a smooth map $D : (0, 1) \to \mathbb R$ from the one-dimensional manifold of impact
parameters to the one-dimensional manifold of angles. Light arriving at the observer at the
deflection angle $\theta$ has come from every $b$ with $D(b) = \theta$: the solutions of an
equation $f(x) = y$, once more.

**Brightness.** Rays with impact parameter in $[b, b + db]$ form a ring of area $2\pi b\,db$ on
the drop's cross-section. They leave in the cone of angles $[D(b), D(b) + D'(b)\,db]$, whose solid
angle is $2\pi\sin\theta\,|D'(b)|\,db$. So the brightness at deflection angle $\theta$ is

$$I(\theta) \propto \sum_{b \,:\, D(b) = \theta} \frac{b}{\sin\theta\,|D'(b)|},$$

the one-dimensional version of the pool formula in §0, and it is infinite exactly at the critical
values of $D$.

**The critical point.** Differentiating, with $di/db = 1/\sqrt{1 - b^2}$ and
$dr/db = 1/\sqrt{n^2 - b^2}$,

$$D'(b) = \frac{2}{\sqrt{1 - b^2}} - \frac{4}{\sqrt{n^2 - b^2}} = 0
\iff n^2 - b^2 = 4(1 - b^2) \iff b^2 = \frac{4 - n^2}{3}.$$

For $1 < n < 2$ this has exactly one solution $b_* \in (0,1)$. So the critical set is a single
point, the critical value $D(b_*)$ is a single angle, and the set of critical values has measure
zero, as Sard demands, in the most literal way possible. On either side of $b_*$ the map $D$ is
monotone, so every regular value in the range of $D$ near $D(b_*)$ is hit twice (a fold: two rays
arrive at each angle) and values beyond $D(b_*)$ are not hit at all. The brightness has an
integrable singularity of the form $|\theta - D(b_*)|^{-1/2}$ at the fold, which is a *bright
edge* with darkness on one side: the rainbow.

For water, $n$ depends slightly on colour, and the computation gives:

| colour | $n$ | $b_*$ | $D(b_*)$ | angle from the antisolar point, $180° - D(b_*)$ |
|---|---|---|---|---|
| red | 1.331 | 0.862 | 137.6° | 42.4° |
| yellow | 1.333 | 0.861 | 137.9° | 42.1° |
| violet | 1.343 | 0.856 | 139.4° | 40.6° |

The rainbow is a circle of angular radius about $42°$ around the point opposite the sun, red on
the outside and violet inside, with the sky darker just outside it (the angles beyond the fold are
not reached by any ray). All three facts are read off the table.

**The secondary bow.** Rays reflected twice inside the drop have deflection
$D_2(b) = 2\pi + 2\arcsin b - 6\arcsin(b/n)$, with critical point $b^2 = (9 - n^2)/8$ and critical
value corresponding to about $51°$ from the antisolar point, colours reversed (red at $50.4°$,
violet at $53.5°$). Between $42°$ and $51°$ neither map has values: that is Alexander's dark band,
visible whenever both bows are.

**What Sard adds.** In this one-dimensional example one can find the critical point by hand, and
the theorem seems like overkill. But the point of view is what matters, and it scales. The
caustic network on the pool floor, the bright curves a wine glass throws on a tablecloth, the
folds of a gravitational lens (Chapter 4): all are images of critical sets of smooth maps between
manifolds of the same dimension, all are sets of measure zero by Sard's theorem, and all have the
same local structure at a generic fold, a $|\theta - \theta_*|^{-1/2}$ edge with light on one side.
Geometric optics is the study of a smooth map $f$ and the count $\#f^{-1}(y)$; its caustics are
the critical values; and the theorem of this chapter is the statement that they are always thin.

> **Beyond geometric optics.** The infinity at the fold is an artefact of treating light as rays.
> Airy (1838) computed the wave-optical brightness near the rainbow angle: the singularity is
> smoothed into a peak of width proportional to $\lambda^{2/3}$ (with $\lambda$ the wavelength), followed
> by fainter oscillations on the bright side, the *supernumerary bows*. But the location of the
> peak is still the critical value, and the fold is still the reason there is a peak at all.

---

## 5. Summary of what was silently assumed, now made explicit

| Where | Milnor says | What is actually needed |
|---|---|---|
| p. 10 | "regular values are dense" | uniqueness of Haar measure up to scale, so null sets do not depend on the choice of volume |
| p. 11 | "$M$ can be covered by a countable collection of neighborhoods" | the Lindelöf property; automatic for subsets of $\mathbb R^k$ |
| p. 11 | critical points of $f$ are critical points in charts | chain rule plus injectivity of chart derivatives (Step 4 of Theorem 2.1) |
| p. 16 | induction "for $n \ge 0$, $p \ge 1$" | $p = 0$ and $n = 0$ treated separately, for different reasons |
| p. 17 | $h$ is a local diffeomorphism | Lemma 3.1, via the inverse function theorem on manifolds from Chapter 1 |
| p. 18 | "$g(C')$ is measurable, since it can be expressed as a countable union of compact subsets" | $C$ is closed in $U$ because surjectivity of a linear map is an open condition |
| p. 18 | "a point is critical for $g^t$ iff it is critical for $g$" | only "if" is needed; the block-matrix computation is Claim (c) of Proposition 3.5 |
| p. 19 | "From Taylor's theorem … we see that $\|R(x,h)\| \le c\|h\|^{k+1}$" | Lemma 3.2, by induction on $k$ from the mean value inequality |
| p. 19 | the cube count | equivalently, Hölder maps divide Hausdorff dimension (Proposition 3.3) |

**Checked by machine.** Sard's theorem (Theorem 1.1, in the form of Theorem 3.6, for arbitrary
finite-dimensional spaces and Haar measures), its corollary, and Brown's theorem (Theorem 2.1)
have been verified in the Lean proof assistant as part of this project, following the proof above
step for step. The text does not depend on this. The optics in §0 and §4 is elementary and was not
formalized.
