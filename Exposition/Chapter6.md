# Chapter 6. Highs, lows and cols: vector fields and the Euler number

*Milnor, "Topology from the Differentiable Viewpoint", §6, rewritten for a first-year student who
wants to know what the theorem is for. Every proof is complete except where stated: the
identification of the index sum with the Euler characteristic from homology is quoted, as Milnor
quotes it.*

---

## 0. A law of the weather map

On a weather map the wind circulates around the centres of high and low pressure, and there are
also *cols* (saddle points of the pressure), where two highs and two lows meet in a cross, and the
air flows in along one axis and out along the other. Count them over the whole globe at one
instant: highs $H$, lows $L$, cols $C$. The claim:

$$H + L - C = 2 .$$

Always. Whatever the weather, and on any planet with an atmosphere. The number $2$ belongs to the
sphere, not to the weather. This is the Poincaré–Hopf theorem, and this chapter proves it, in the
form: for any smooth tangent vector field on a compact manifold $M$ with finitely many zeros, the
sum of the *indices* of the zeros is a number $\chi(M)$ that depends only on $M$. A centre of
circulation has index $+1$, a col has index $-1$, and $\chi(S^2) = 2$.

The tool is the degree of Chapter 5. The index of a zero is the degree of the direction field
$v/\|v\|$ on a small sphere around it. Everything then comes down to Chapter 5, Lemma 3.1: a map
that extends over a filling has degree zero. At the end of the chapter the same theorem is applied
to a drop of liquid crystal, where it forces defects to exist and fixes their total charge.

---

## 1. The index of a zero (Milnor pp. 32–35)

Let $v : U \to \mathbb R^m$ be a smooth vector field on an open set $U \subseteq \mathbb R^m$ with an
*isolated* zero at $z$: $v(z) = 0$ and $v \ne 0$ on some punctured ball around $z$. On a small
sphere $S_\varepsilon(z)$ inside that ball, the map
$$\bar v(x) := \frac{v(x)}{\|v(x)\|} : S_\varepsilon(z) \to S^{m-1}$$
is smooth, and both spheres are oriented as boundaries of their disks. The *index* $\iota(v, z)$ is
the degree of $\bar v$. It does not depend on $\varepsilon$: for $\varepsilon' < \varepsilon$ the
maps on the two spheres are homotopic through $\bar v$ on the intermediate spheres (a homotopy of
$S^{m-1} \times [0,1] \to S^{m-1}$ via $x \mapsto \bar v(z + (\varepsilon' + t(\varepsilon -
\varepsilon'))x)$), so Chapter 5, Theorem B applies.

**Examples in the plane.** For $v(x) = x$ (a source), $\bar v$ is the identity of the circle,
index $+1$. For $v(x) = -x$ (a sink), $\bar v$ is the antipodal map, index $(-1)^2 = +1$. For
$v(x_1, x_2) = (x_1, -x_2)$ (a saddle), $\bar v$ is a reflection, index $-1$. For $v(x_1, x_2) =
(-x_2, x_1)$ (a rotation, the centre of a cyclone), $\bar v$ is a rotation of the circle by a
quarter turn, a diffeomorphism preserving orientation, index $+1$. In complex notation, $v(z) =
z^k$ has index $k$ and $v(z) = \bar z^{\,k}$ has index $-k$ (Chapter 5, §5).

To define the index on a manifold we need that it is invariant under diffeomorphisms of the
domain. The proof passes through a lemma of independent interest.

**Lemma 1.1 (Milnor's Lemma 2).** Every orientation-preserving diffeomorphism $f$ of $\mathbb R^m$
is smoothly isotopic to the identity.

*Proof.* Composing with a translation, assume $f(0) = 0$. *Hadamard's lemma:* there are smooth
$g_1, \dots, g_m : \mathbb R^m \to \mathbb R^m$ with $f(x) = \sum_i x_i\, g_i(x)$ and
$g_i(0) = \partial f/\partial x_i(0)$. Indeed
$$f(x) = f(x) - f(0) = \int_0^1 \frac{d}{dt} f(tx)\,dt = \sum_i x_i \int_0^1 \frac{\partial f}
{\partial x_i}(tx)\,dt,$$
and $g_i(x) := \int_0^1 \partial_i f(tx)\,dt$ is smooth (differentiate under the integral sign).
Define
$$F(x, t) := \sum_i x_i\, g_i(tx), \qquad\text{so that}\qquad F(x, t) = \frac{f(tx)}{t}\ (t > 0),
\quad F(x, 0) = df_0(x).$$
$F$ is smooth on $\mathbb R^m \times [0,1]$ by the first formula. For $t > 0$, $F(\cdot, t)$ is the
diffeomorphism $x \mapsto f(tx)/t$; for $t = 0$ it is the linear isomorphism $df_0$, which has
positive determinant since $f$ preserves orientation. So $F$ is an isotopy from $df_0$ to $f$.

It remains to connect $df_0$ to the identity through linear isomorphisms, i.e. to show that
$GL^+(m)$, the matrices with positive determinant, is path connected. Let $A \in GL^+(m)$. Polar
decomposition: $A = QP$ with $P = (A^{\mathsf T}A)^{1/2}$ symmetric positive definite and
$Q = AP^{-1}$ orthogonal, $\det Q = \det A/\det P > 0$, so $\det Q = 1$. The path
$P_t = (1-t)P + tI$ consists of positive definite matrices (a convex combination of positive
definite matrices is positive definite), joining $P$ to $I$. For $Q \in SO(m)$: by the normal form
theorem for orthogonal matrices, $Q$ is conjugate by an orthogonal matrix to a block-diagonal
matrix of $2 \times 2$ rotations $R(\alpha_j)$ and diagonal entries $\pm 1$; since $\det Q = 1$
there is an even number of $-1$'s, which we group in pairs as rotations $R(\pi)$. Shrinking every
angle $\alpha_j$ to $0$ gives a path in $SO(m)$ from $Q$ to $I$. Concatenating, $A = QP$ is joined
to $I$ through $Q_tP_t \in GL^+(m)$. A path in $GL^+(m)$ from $df_0$ to $I$, followed by $F$, is
the required isotopy (smooth the joint by the reparametrization trick of Chapter 4, §1). $\square$

**Lemma 1.2 (Milnor's Lemma 1).** Let $f : U \to U'$ be a diffeomorphism between open subsets of
$\mathbb R^m$, $v$ a vector field on $U$ with an isolated zero at $z$, and $v' := df \circ v \circ
f^{-1}$ the corresponding field on $U'$. Then $\iota(v', f(z)) = \iota(v, z)$.

*Proof.* Translating, assume $z = f(z) = 0$, and shrink $U$ to a ball, so it is convex and
star-shaped about $0$.

*Orientation-preserving case.* As in Lemma 1.1, $f_t(x) := f(tx)/t$ for $0 < t \le 1$ and
$f_0 := df_0$ define a smooth family of maps $f_t : U \to \mathbb R^m$, each an embedding
(injective with invertible derivative) with $f_t(0) = 0$; and $\Phi(x, t) := (f_t(x), t)$ is a
smooth injective map $U \times [0,1] \to \mathbb R^m \times [0,1]$ with invertible derivative, hence
a diffeomorphism onto an open set $W$ containing $\{0\} \times [0,1]$. By compactness of $[0,1]$,
$W \supseteq \bar B_\varepsilon(0) \times [0,1]$ for some $\varepsilon > 0$, and shrinking
$\varepsilon$ we may also assume $v$ has no zero in $f_t^{-1}(\bar B_\varepsilon) \setminus \{0\}$
for all $t$ (the set $\{(x,t) : x \in f_t^{-1}(\bar B_\varepsilon)\}$ is compact and shrinks to
$\{0\} \times [0,1]$). On $W$ define $v_t := df_t \circ v \circ f_t^{-1}$, smooth in $(x, t)$
since $f_t^{-1}(x)$ is the first component of $\Phi^{-1}(x, t)$. Each $v_t$ vanishes on
$B_\varepsilon$ only at $0$. So $(x, t) \mapsto v_t(x)/\|v_t(x)\|$ is a smooth homotopy
$S_\varepsilon \times [0,1] \to S^{m-1}$ from $\bar v_0$ to $\bar v_1 = \bar v'$, where $v_0 =
df_0 \circ v \circ df_0^{-1}$. By Chapter 5, Theorem B, $\iota(v', 0) = \iota(v_0, 0)$. Finally
connect $df_0$ to $I$ in $GL^+(m)$ (Lemma 1.1) and repeat the argument with the linear maps
$L_t$: $\iota(v_0, 0) = \iota(v, 0)$.

*Orientation-reversing case.* Every orientation-reversing diffeomorphism is $\rho \circ f_1$ with
$\rho$ the reflection $x_1 \mapsto -x_1$ and $f_1 = \rho \circ f$ orientation preserving, so it
suffices to treat $\rho$. Then $v' = \rho \circ v \circ \rho$ (as $\rho^{-1} = \rho$ and $d\rho =
\rho$), and $\bar v' = \rho \circ \bar v \circ \rho$ on $S_\varepsilon$, since $\rho$ preserves
norms. The degree of a composition of diffeomorphisms multiplies, and $\rho|_{S^{m-1}}$ has degree
$-1$ (Chapter 5, §5), so $\deg \bar v' = (-1)\cdot\deg\bar v\cdot(-1) = \deg \bar v$. $\square$

**Definition.** For a vector field $w$ on a manifold $M$ with an isolated zero $z$, and a
parametrization $g : U \to M$ of a neighbourhood of $z$, the index $\iota(w, z)$ is the index at
$g^{-1}(z)$ of the field $dg^{-1} \circ w \circ g$ on $U$. By Lemma 1.2 this does not depend on
$g$.

---

## 2. Hopf's lemma: the index sum equals the degree of the Gauss map (Milnor pp. 35–36)

Let $X \subseteq \mathbb R^m$ be a compact $m$-manifold with boundary, and let
$g : \partial X \to S^{m-1}$ be the *Gauss map*, assigning to each boundary point its outward unit
normal vector. (It is smooth: in a boundary chart, the outward normal is the unit vector
orthogonal to the tangent space of $\partial X$ on the outward side, a smooth function of the
chart's derivative.)

**Lemma 2.1 (Hopf).** Let $v : X \to \mathbb R^m$ be a smooth vector field with finitely many
zeros, all in the interior, pointing outward along $\partial X$: $v(x)\cdot g(x) > 0$ for
$x \in \partial X$. Then
$$\sum_{\text{zeros } z} \iota(v, z) = \deg g .$$

*Proof.* Remove from $X$ a small open ball $B_\varepsilon(z_i)$ around each zero $z_i$, with the
balls disjoint and inside the interior of $X$. The result $X'$ is a compact manifold with boundary
$\partial X' = \partial X \cup \bigcup_i S_\varepsilon(z_i)$, and $v$ has no zero on $X'$, so
$\bar v = v/\|v\| : X' \to S^{m-1}$ is smooth. By Chapter 5, Lemma 3.1, applied to $\bar v$ on
$\partial X'$ with the orientation induced from $X'$, $\deg(\bar v|_{\partial X'}) = 0$.

The degree over a disconnected boundary is the sum over the components. On $\partial X$ the
induced orientation from $X'$ is the same as from $X$, and $\bar v|_{\partial X}$ is homotopic to
$g$: since $v(x)\cdot g(x) > 0$, the segment $(1-t)\bar v(x) + t\,g(x)$ never passes through $0$
(both endpoints lie in the open half-space $\{u : u\cdot g(x) > 0\}$), so normalizing it gives a
smooth homotopy in $S^{m-1}$. Hence this component contributes $\deg g$.

On the small sphere $S_\varepsilon(z_i)$, the outward normal of $X'$ points *into* the ball, so
the orientation induced from $X'$ is the opposite of the orientation as boundary of the ball; the
contribution is $-\iota(v, z_i)$. Adding up, $\deg g - \sum_i \iota(v, z_i) = 0$. $\square$

*Example.* For a field on the disk $D^m$ pointing outward along $S^{m-1}$, the Gauss map is the
identity, and the index sum is $+1$. Any field on the disk pointing outward has a zero.

---

## 3. Nondegenerate zeros (Milnor pp. 36–38)

**Definition.** A zero $z$ of $v : U \to \mathbb R^m$ is *nondegenerate* if the linear map
$dv_z : \mathbb R^m \to \mathbb R^m$ is invertible. Then $z$ is isolated: by the inverse function
theorem $v$ is injective near $z$, so has no other zero nearby.

**Lemma 3.1 (Milnor's Lemma 4).** The index of a nondegenerate zero is $\operatorname{sign}\det dv_z$.

*Proof.* Translate $z$ to $0$ and shrink $U$ to a ball on which $v$ is a diffeomorphism onto an
open set (inverse function theorem). If $\det dv_0 > 0$, then Lemma 1.2's construction applied to
the diffeomorphism $v$ itself gives a family $v_t(x) = v(tx)/t$, $v_0 = dv_0$, of vector fields
on the ball, each vanishing only at $0$; the argument there shows $\iota(v, 0) = \iota(dv_0, 0)$,
and then, connecting $dv_0$ to $I$ in $GL^+(m)$, $\iota(dv_0, 0) = \iota(I, 0) = \deg(\mathrm{id}_{S^{m-1}}) = 1$.
If $\det dv_0 < 0$, then $\rho \circ v$ has positive determinant, so $\iota(\rho\circ v, 0) = 1$,
and $\overline{v} = \rho \circ \overline{\rho\circ v}$ has degree $(-1)\cdot 1 = -1$. $\square$

Now a zero $z$ of a field $w$ on a manifold $M \subseteq \mathbb R^k$. Regard $w$ as a map
$M \to \mathbb R^k$, so $dw_z : TM_z \to \mathbb R^k$ is defined.

**Lemma 3.2 (Milnor's Lemma 5).** At a zero $z$, $dw_z$ maps $TM_z$ into $TM_z$. If this linear
map $TM_z \to TM_z$ has determinant $D \ne 0$, then $z$ is an isolated zero of index
$\operatorname{sign} D$.

*Proof.* Let $h : U \to M$ be a parametrization with $h(u_0) = z$, and $t_i := \partial h/\partial
u_i$, a basis of $TM_{h(u)}$ at each $u$. Let $v = \sum_j v_j e_j$ be the field on $U$
corresponding to $w$, so that $w(h(u)) = dh_u(v(u)) = \sum_j v_j(u)\, t_j(u)$. Differentiate this
identity in $u_i$:
$$dw_{h(u)}(t_i) = \frac{\partial\, w(h(u))}{\partial u_i} = \sum_j \frac{\partial v_j}{\partial u_i}\, t_j
+ \sum_j v_j\,\frac{\partial t_j}{\partial u_i}.$$
At $u = u_0$ all $v_j$ vanish, so $dw_z(t_i) = \sum_j (\partial v_j/\partial u_i)(u_0)\, t_j \in TM_z$.
Thus $dw_z$ maps $TM_z$ into itself, and its matrix in the basis $(t_i)$ is the Jacobian matrix of
$v$ at $u_0$. So $D = \det dv_{u_0}$, and Lemma 3.1 (with the definition of the index on a manifold)
gives the claim. $\square$

---

## 4. The index sum is independent of the field (Milnor pp. 38–39)

Let $M \subseteq \mathbb R^k$ be a compact manifold without boundary. For $\varepsilon > 0$ let
$N_\varepsilon := \{x \in \mathbb R^k : \operatorname{dist}(x, M) \le \varepsilon\}$.

**Proposition 4.1 (the tubular neighbourhood).** For $\varepsilon$ small enough: (i) every
$x \in N_\varepsilon$ has a unique closest point $r(x) \in M$, and $r : N_\varepsilon \to M$ is
smooth; (ii) $x - r(x)$ is orthogonal to $TM_{r(x)}$; (iii) $N_\varepsilon$ is a smooth manifold
with boundary $\partial N_\varepsilon = \{x : \|x - r(x)\| = \varepsilon\}$, whose outward unit
normal at $x$ is $(x - r(x))/\varepsilon$.

Milnor refers to Problems 11 and 12 of §8 for this; here is the proof.

*Proof.* Let $E := \{(p, n) \in M \times \mathbb R^k : n \perp TM_p\}$, the *normal bundle*. It is
a smooth manifold of dimension $k$: near a point of $M$ with parametrization $h : U \to M$, the
vectors $t_i(u) = \partial h/\partial u_i$ span $TM_{h(u)}$; Gram–Schmidt applied to
$(t_1, \dots, t_m, e_1, \dots, e_k)$ (dropping dependent vectors, which for $u$ near a fixed $u_0$
can be done with a fixed choice of $k - m$ of the $e_j$) produces smooth orthonormal vectors
$n_1(u), \dots, n_{k-m}(u)$ spanning $TM_{h(u)}^\perp$; then $(u, s) \mapsto (h(u), \sum s_a n_a(u))$
is a parametrization of $E$ over $h(U) \times \mathbb R^{k-m}$.

Define $\Psi : E \to \mathbb R^k$, $\Psi(p, n) = p + n$. At $(p, 0)$ its derivative sends
$(\dot p, 0) \mapsto \dot p \in TM_p$ and $(0, \dot n) \mapsto \dot n \in TM_p^\perp$, so it is an
isomorphism $TE_{(p,0)} = TM_p \oplus TM_p^\perp \to \mathbb R^k$. By the inverse function theorem
$\Psi$ is a local diffeomorphism near each $(p, 0)$. It is injective on $E_\varepsilon := \{(p,n) \in
E : \|n\| \le \varepsilon\}$ for $\varepsilon$ small: otherwise there are $(p_j, n_j) \ne (p'_j, n'_j)$
with $\|n_j\|, \|n'_j\| \to 0$ and $p_j + n_j = p'_j + n'_j$; by compactness of $M$ pass to
subsequences with $p_j \to p$, $p'_j \to p'$; then $p = p'$, and for large $j$ both pairs lie in a
neighbourhood of $(p, 0)$ on which $\Psi$ is injective, a contradiction. So $\Psi$ maps
$E_\varepsilon$ diffeomorphically onto its image, which is open in $\mathbb R^k$ near $M$ and, by
compactness, contains $N_{\varepsilon'}$ for some $\varepsilon' \le \varepsilon$ (the image of the
open set $\{\|n\| < \varepsilon\}$ is an open set containing $M$).

Now (i) and (ii): let $x \in N_{\varepsilon'}$ and let $p \in M$ be a closest point (exists by
compactness). Then $p$ minimizes $\|x - h(u)\|^2$ over $u$, so $(x - p) \cdot t_i = 0$ for all $i$:
$x - p \perp TM_p$, and $\|x - p\| \le \varepsilon'$. Hence $(p, x - p) \in E_\varepsilon$ with
$\Psi(p, x-p) = x$; by injectivity $p$ is the unique closest point, and $r(x) = $ (first component
of $\Psi^{-1}(x)$) is smooth. (iii): under the diffeomorphism $\Psi^{-1}$, $N_{\varepsilon'}$
corresponds to $\{(p, n) \in E : \varepsilon'^2 - \|n\|^2 \ge 0\}$, and the function $(p, n) \mapsto
\|n\|^2$ on $E$ has derivative $2 n\cdot\dot n$ in the normal direction, nonzero when $n \ne 0$; so
by Chapter 2, Lemma 3.2, this is a manifold with boundary $\{\|n\| = \varepsilon'\}$. Finally
the function $\varphi(x) := \|x - r(x)\|^2$ has $d\varphi_x(\eta) = 2(x - r(x))\cdot(\eta - dr_x\eta)
= 2(x - r(x))\cdot\eta$, because $dr_x\eta \in TM_{r(x)} \perp (x - r(x))$. So $\nabla\varphi =
2(x - r(x))$, and the outward normal to the level set $\partial N_{\varepsilon'} = \varphi^{-1}(\varepsilon'^2)$
is $\nabla\varphi/\|\nabla\varphi\| = (x - r(x))/\varepsilon'$. Rename $\varepsilon'$ as $\varepsilon$. $\square$

**Theorem 4.2 (Milnor's Theorem 1).** For any smooth tangent vector field $v$ on $M$ with only
nondegenerate zeros, the index sum $\sum_z \iota(v, z)$ equals the degree of the Gauss map
$g : \partial N_\varepsilon \to S^{k-1}$. In particular it does not depend on $v$.

*Proof.* Extend $v$ to $N_\varepsilon$ by
$$w(x) := (x - r(x)) + v(r(x)).$$
The two summands are orthogonal ($x - r(x) \perp TM_{r(x)} \ni v(r(x))$), so $w(x) = 0$ iff
$x = r(x) \in M$ and $v(x) = 0$: the zeros of $w$ are exactly the zeros of $v$. On the boundary,
$w(x)\cdot g(x) = \|x - r(x)\|^2/\varepsilon = \varepsilon > 0$, so $w$ points outward. At a zero
$z \in M$: for $\eta \in TM_z$, $dr_z\eta = \eta$ (as $r$ is the identity on $M$), so
$dw_z(\eta) = \eta - \eta + dv_z(\eta) = dv_z(\eta)$; for $\eta \in TM_z^\perp$, differentiating
$r$ along the normal line $z + s\eta$, on which $r$ is constant equal to $z$, gives $dr_z\eta = 0$,
so $dw_z(\eta) = \eta$. In a basis adapted to $\mathbb R^k = TM_z \oplus TM_z^\perp$, $dw_z$ is
block diagonal with blocks $dv_z|_{TM_z}$ and the identity, so $\det dw_z = \det(dv_z : TM_z \to
TM_z)$, and by Lemmas 3.1 and 3.2, $\iota(w, z) = \iota(v, z)$. Now Lemma 2.1 applied to $w$ on
$X = N_\varepsilon$ gives $\sum_z \iota(v, z) = \sum_z \iota(w, z) = \deg g$. $\square$

**Definition.** The common value is the *Euler number* $\chi(M)$ of $M$.

**Examples.** (a) *Spheres.* On $S^m$ the field $v(x) = p - (p\cdot x)\,x$, with $p$ the north
pole, is tangent ($v\cdot x = p\cdot x - p\cdot x = 0$) and vanishes only at $x = \pm p$. Near the
south pole $-p$, in the chart given by projection to $p^\perp$, $v \approx$ (identity) so the index
is $+1$; near the north pole $v \approx -$(identity) on $p^\perp \cong \mathbb R^m$, index
$\operatorname{sign}\det(-I_m) = (-1)^m$. So
$$\chi(S^m) = 1 + (-1)^m = \begin{cases} 2 & m \text{ even},\\ 0 & m \text{ odd}.\end{cases}$$
This reproves the hairy ball theorem: a field without zeros has index sum $0 \ne 2$.
(b) *Odd dimensions.* Replacing $v$ by $-v$ multiplies each index by $\deg(\text{antipodal map of }
S^{m-1}) = (-1)^m$; for $m$ odd, $\chi(M) = -\chi(M)$, so $\chi(M) = 0$ for every compact
odd-dimensional manifold. (c) *The torus* $S^1 \times S^1$ carries the nowhere-zero field
$(x, y) \mapsto (ix, 0)$, so $\chi = 0$. (d) *Surfaces of genus $g$* (a sphere with $g$ handles):
the gradient of the height function, for the surface standing upright, has one minimum, $2g$
saddles and one maximum, giving $\chi = 2 - 2g$.

> **The identification with topology (Milnor's Step 1).** The number $\chi(M)$ defined here equals
> the Euler characteristic of $M$ computed from any triangulation ($V - E + F$ for a surface), or
> from homology as $\sum (-1)^i \operatorname{rank} H_i(M)$. Milnor's route: by Morse theory there
> is a function on $M$ whose gradient has only nondegenerate zeros, and the number of zeros of index
> $(-1)^\lambda$ is the number of critical points of Morse index $\lambda$, whose alternating sum is
> the Euler characteristic (Milnor, *Morse Theory*, §5). We quote this; nothing below depends on it.

> **Degenerate zeros (Milnor's Step 2).** If $v$ has an isolated but degenerate zero at $z$,
> choose a bump function $\lambda$ equal to $1$ near $z$ and $0$ outside a small ball $B$ around
> $z$ containing no other zero, and a regular value $y$ of $v$ (Sard) so small that $v - y$ has no
> zero on the annulus where $0 < \lambda < 1$. Then $v' := v - \lambda y$ agrees with $v$ outside
> $B$, its zeros inside $B$ are those of $v - y$ near $z$, all nondegenerate (regular value), and
> by Lemma 2.1 on the ball $B$ the sum of their indices is $\deg(\bar v|_{\partial B}) = \iota(v,z)$.
> Doing this at each degenerate zero replaces $v$ by a nondegenerate field with the same index
> sum, so Theorem 4.2 holds for all fields with isolated zeros.

> **Manifolds with boundary (Milnor's Step 3).** For $M$ with boundary and $v$ pointing outward
> along $\partial M$, the same construction works, but $N_\varepsilon$ has corners where
> $\partial M$ meets the tube, and the extension $w$ is only continuous there. Milnor notes the
> difficulty and does not resolve it in the text; one way through is to first double the
> collar of the boundary so that $v$ becomes a field on a slightly larger manifold with the same
> zeros, and we leave it there.

### An interactive look at the theorem

The figure is a globe with a randomly generated smooth pressure field, shaded from low (dark) to
high (light), and the wind drawn as the field that circulates along the isobars (in the Northern
hemisphere the wind goes clockwise around a high). The zeros of the wind are the critical points of
the pressure. The program finds them numerically and classifies each by the sign of the
determinant of the Hessian: highs and lows (index $+1$) are marked $H$ and $L$, cols (index $-1$)
are marked with a cross. The count $H + L - C$ is shown. Change the weather with the slider and
watch highs and lows appear, always together with a col, so that the total stays $2$. Rotate the
globe to check the far side.

<div id="weather-figure"></div>

*(In the printed version this figure is a still image; the interactive version is in the web
edition.)*

---

## 5. Application: the weather, and defects in liquid crystals

**The weather map, proved.** Idealize the atmosphere as a thin layer: the horizontal wind is a
tangent vector field $v$ on $S^2$. Where the pressure $p$ has a nondegenerate extremum, the wind
circulates around it and $v$ has an isolated zero of index $+1$ (a rotation, or a source or sink,
all of index $+1$ by §1). Where $p$ has a nondegenerate saddle, the wind has a saddle zero of
index $-1$ (the hyperbolic flow of §1). On a real weather map there are no other calm points,
and the zeros are nondegenerate. Theorem 4.2 with $\chi(S^2) = 2$:
$$H + L - C = 2.$$
So there are always at least two centres of circulation somewhere on Earth, and every additional
pair of centres comes with a col between them. The meteorologists' rule of thumb is a theorem
about the sphere.

**Liquid crystals.** A nematic liquid crystal is a fluid of rod-like molecules that locally align:
at each point there is a preferred axis, the *director*, a unit vector $n(x)$ *up to sign* (the
rods have no head or tail). Coat a small sphere with a thin nematic layer whose director is tangent
to the surface, as happens on a droplet suspended in the fluid. If $n$ could be chosen as a
continuous vector field, Theorem 4.2 would force zeros; but the director must have unit length,
so instead it must be *undefined* somewhere: these are the *defects*, visible under a polarizing
microscope as points where the texture becomes singular. The Poincaré–Hopf theorem for line fields
(the same proof, with the index of a defect defined as half the degree of the map $n^2 : S^1 \to
S^1$ that ignores the sign, so that indices are in $\frac12\mathbb Z$) says:

> The indices of the defects of a tangent director field on a sphere add up to $2$.

The cheapest defects have index $+\tfrac12$: the director turns by a half-turn around them. Four
of them make $2$, and to minimize the elastic energy they sit as far apart as possible, at the
vertices of a tetrahedron. This was predicted by Nelson (2002) and seen in nematic shells by
Lopez-Leon, Koning, Devaiah, Vitelli and Fernandez-Nieves (2011). Nelson's proposal: attach
molecular linkers at the four defects, and the coated droplet becomes a colloidal "atom" with
tetrahedral valence, a building block for self-assembling a diamond-like lattice. The number four
is $2 \div \tfrac12$, and the $2$ is the Euler number of the sphere.

The same theorem governs the whorls in a fingerprint (a line field on a disk with prescribed
boundary behaviour), the singular points of the fibre directions in a heart wall, and the defects
in the cosmic microwave background polarization pattern. Wherever a direction field lives on a
surface, the sum of its singularities is fixed by the surface.

---

## 6. Summary of what was silently assumed, now made explicit

| Where | Milnor says | What is actually needed |
|---|---|---|
| p. 32 | the index "is the degree of this mapping" | independence of the radius $\varepsilon$, via a homotopy between the small spheres |
| p. 34 | "$f(x) = x_1 g_1(x) + \dots + x_m g_m(x)$ … suitable smooth functions" | Hadamard's lemma with $g_i(x) = \int_0^1 \partial_i f(tx)\,dt$ (Lemma 1.1) |
| p. 34 | "$df_0$ is clearly isotopic to the identity" | $GL^+(m)$ is connected: polar decomposition and the normal form of rotations (Lemma 1.1) |
| p. 34 | "these vector fields are all defined and nonzero on a sufficiently small sphere" | the map $(x,t) \mapsto (f_t(x), t)$ is a diffeomorphism onto an open set containing $\{0\}\times[0,1]$; compactness of $[0,1]$ (Lemma 1.2) |
| p. 36 | "$\bar v|_{\partial X}$ is homotopic to $g$" | both lie in the same open half-space, so the straight-line homotopy avoids $0$ (Lemma 2.1) |
| p. 38 | "for $\varepsilon$ sufficiently small $N_\varepsilon$ is a smooth manifold with boundary" | the normal bundle, the map $(p,n) \mapsto p+n$, injectivity by compactness (Proposition 4.1) |
| p. 38 | "an easy computation shows that $\operatorname{grad}\varphi = 2(x - r(x))$" | $dr_x\eta \perp x - r(x)$ (Proposition 4.1) |
| p. 39 | "$dw_z(h) = h$ for $h \in TM_z^\perp$" | $r$ is constant along normal lines, so $dr_z$ kills normal vectors (Theorem 4.2) |
| p. 40 | Steps 1–3 | Step 1 quoted (Morse theory); Step 2 proved above; Step 3 left as Milnor leaves it |

**Checked by machine.** The index of a zero, the region lemma, Hopf's lemma, the invariance of the
index under diffeomorphisms (Lemma 1, proved by a direct computation of signs instead of Lemma 2),
the $\varepsilon$-neighbourhood theorem and the Poincaré–Hopf theorem for compact submanifolds of
Euclidean space have been verified in the Lean proof assistant. Not formalized: Milnor's Lemma 2
itself, the chart definition of the index, and the identification of the index sum with the Euler
characteristic. See the verified edition, §7, and *Milnor, proof by proof*, Part IV.