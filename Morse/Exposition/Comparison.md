# Morse Theory beside Lean

*Every result of the book beside the statement the machine actually checked. The left column is Milnor, in his own terms. The right column is the formal statement, with the hypotheses he leaves to the reader written out. Click a declaration to see the Lean it names.*

Left: the statement as the book states it. Right: the statement proved in Lean, with the hypotheses written out. Each declaration is given with its file and line.

## Chapter 1

*Milnor §§1–2, pp. 1–12: critical points, the Hessian and the index, the Morse lemma, flows*

### V1.1. The torus of §1

*narrower* · (2)–(4) not identified · no cell attachments · a torus of revolution, $0 < \rho < R$ · (1) read as $a < 0 = f(p)$

**Milnor (§1, pp. 1–3).** A torus $M$ stands on a plane $V$ to which it is tangent (Diagram 1), $f : M \to \mathbb R$ is the height above $V$, and $M^a = \{x \in M : f(x) \le a\}$. Milnor lists five stages as $a$ increases: $M^a$ is vacuous below $f(p)$, homeomorphic to a 2-cell for $f(p) < a < f(q)$, to a cylinder for $f(q) < a < f(r)$, to a compact genus-one surface bounded by a circle for $f(r) < a < f(s)$, and is the full torus above $f(s)$. Up to homotopy type, passing $f(p)$, $f(q)$, $f(r)$, $f(s)$ attaches a 0-cell, a 1-cell, a 1-cell and a 2-cell. The four points are the critical points of $f$, and in suitable coordinates $f = x^2 + y^2$ at $p$, $f = \text{const} + x^2 - y^2$ at $q$ and $r$, and $f = \text{const} - x^2 - y^2$ at $s$: the number of minus signs is the dimension of the cell attached.

*No equations are given and nothing is checked: the example is offered as an illustration of the theorems to come.*

**Proved in Lean.** For $0 < \rho < R$ let $T \subseteq \mathbb R^3$ be the torus $(\sqrt{x_1^2 + x_2^2} - R)^2 + x_3^2 = \rho^2$, a compact surface (V3.22), and $f(x) = x_1 + R + \rho$ its height above the plane $x_1 = -(R + \rho)$, which touches $T$ at $p = (-(R + \rho), 0, 0)$. Then $f|T$ has exactly four critical points, $p$, $q = (-(R - \rho), 0, 0)$, $r = (R - \rho, 0, 0)$ and $s = (R + \rho, 0, 0)$, at the heights $0$, $2\rho$, $2R$ and $2R + 2\rho$; all four are non-degenerate, of indices $0, 1, 1, 2$. $T^a = \emptyset$ for $a < 0$ and $T^a = T$ for $a \ge 2R + 2\rho$. If $a \le b$ and $[a, b]$ contains none of the four heights, a $C^\infty$ diffeomorphism of $T$ carries $T^a$ onto $T^b$, $T^a$ is a strong deformation retract of $T^b$, and the inclusion $T^a \to T^b$ is a homotopy equivalence.

- `Morse.torus` — Morse/Chapter3/TorusSurface.lean, line 75
- `Morse.Torus.isCriticalPointM_height_iff` — Morse/Chapter3/Torus.lean, line 311
- `Morse.Torus.pointP_spec` — Morse/Chapter3/Torus.lean, line 468
- `Morse.Torus.pointQ_spec` — Morse/Chapter3/Torus.lean, line 480
- `Morse.Torus.pointR_spec` — Morse/Chapter3/Torus.lean, line 492
- `Morse.Torus.pointS_spec` — Morse/Chapter3/Torus.lean, line 505
- `Morse.Torus.sublevel_height_eq_empty` — Morse/Chapter3/Torus.lean, line 278
- `Morse.Torus.sublevel_height_eq_univ` — Morse/Chapter3/Torus.lean, line 285
- `Morse.theorem_3_1_torus` — Morse/Chapter3/Torus.lean, line 686

*What differs.*
- Of the five stages only (1) and (5) are proved. That the intermediate sublevel sets are a disk, a cylinder and a torus with a disk removed is not, and neither are the cell attachments of p. 2; between critical heights only Theorem 3.1 is applied.
- The torus is fixed: the torus of revolution with $0 < \rho < R$, standing upright on its tangent plane. Lying flat, its height function would have two circles of degenerate critical points.
- The critical points, their indices and the four critical values are proved, where Milnor asserts them; the normal forms are not restated, but follow from the lemma of Morse (V1.8) and the indices.
- Case (1) is printed $a < 0 < f(p)$ in the scan, whereas $f(p) = 0$; the hypothesis is $a < 0$. The details, whose Lean files sit with Chapter 3, are V3.22–V3.25.

### V1.2. Attaching a cell

*as in the book*

**Milnor (§1, pp. 2–3).** With $e^k$ the $k$-cell of vectors of length at most $1$ in $\mathbb R^k$, $\dot e^k$ its boundary sphere $S^{k-1}$, and $g : S^{k-1} \to Y$ continuous, the space $Y \cup_g e^k$, $Y$ with a $k$-cell attached by $g$, is obtained from the topological sum of $Y$ and $e^k$ by identifying each $x \in S^{k-1}$ with $g(x) \in Y$. For $k = 0$, $e^0$ is a point and $\dot e^0 = S^{-1}$ is empty, so that attaching a 0-cell adds a disjoint point.

**Proved in Lean.** For a topological space $X$, an integer $n \ge 0$ and a continuous map $\varphi : S^{n-1} \to X$, the space $X \cup_\varphi e^n$ is the pushout, in the category of topological spaces, of $\varphi$ and the inclusion of the unit sphere $S^{n-1}$ in the closed unit ball $D^n$ of $\mathbb R^n$: the quotient of $X \sqcup D^n$ by the identification of each $u \in S^{n-1}$ with $\varphi(u)$, so that a map out of it is a pair of maps on $X$ and on $D^n$ which agree along $\varphi$. For $n = 0$ the sphere is empty and $D^0$ is a point. The disk and the sphere are Mathlib's, those of its CW complexes.

- `Morse.AttachCell` — Morse/Chapter2/Attaching.lean, line 81
- `Morse.cellDesc` — Morse/Chapter2/Attaching.lean, line 108

### V1.3. Critical points, the Hessian, index and nullity in coordinates

*restated* · index: the negative index of inertia · non-degenerate: null space $0$ · Milnor's definitions become theorems

**Milnor (§2, pp. 4–5).** A point $p$ is a critical point of a smooth $f : M \to \mathbb R$ when the induced map $f_* : TM_p \to T\mathbb R_{f(p)}$ is zero, which in local coordinates means that the first partial derivatives vanish at $p$; $f(p)$ is then a critical value. A critical point is non-degenerate when the matrix $(\partial^2 f/\partial x^i \partial x^j(p))$ is non-singular, a condition which can be checked directly not to depend on the coordinates. The index of a bilinear functional $H$ on a vector space is the maximal dimension of a subspace on which $H$ is negative definite, and its nullity is the dimension of the null space $\{v : H(v, w) = 0 \text{ for all } w\}$; a critical point is non-degenerate exactly when $f_{**}$ has nullity $0$.

*The coordinate condition for a critical point is displayed in the book, but the display is lost in the scan.*

**Proved in Lean.** Let $E$ be a real normed space and $f : E \to \mathbb R$. A point $p$ is a critical point of $f$ if $f$ is differentiable at $p$ with derivative $0$. The Hessian of $f$ at $p$ is the second derivative $d^2 f_p$, a continuous bilinear form on $E$, symmetric when $f$ is $C^2$ at $p$; it is defined at every point but only used at critical points. For a continuous bilinear form $H$ on $E$ the null space is $\{v : H(v, w) = 0 \text{ for all } w\}$, the nullity is its dimension, $H$ is non-degenerate if its null space is $0$, and the index of $H$ is the negative index of inertia of $v \mapsto H(v, v)$. For finite-dimensional $E$ the index is the largest dimension of a subspace on which $H(v, v) < 0$ for all $v \ne 0$, and non-degenerate means nullity $0$; for $E = \mathbb R^n$ and $f$ of class $C^2$ at $p$, it means that the matrix $(\partial^2 f/\partial x^i\partial x^j(p))$ is non-singular.

- `Morse.IsCriticalPoint` — Morse/Chapter1/Nondegenerate.lean, line 91
- `Morse.hessian` — Morse/Chapter1/Nondegenerate.lean, line 113
- `Morse.hessian_symm` — Morse/Chapter1/Nondegenerate.lean, line 117
- `Morse.nullSpace` — Morse/Chapter1/Nondegenerate.lean, line 152
- `Morse.nullity` — Morse/Chapter1/Nondegenerate.lean, line 159
- `Morse.index` — Morse/Chapter1/Nondegenerate.lean, line 165
- `Morse.index_isGreatest` — Morse/Chapter1/Nondegenerate.lean, line 196
- `Morse.IsNondegenerate` — Morse/Chapter1/Nondegenerate.lean, line 169
- `Morse.isNondegenerate_iff_nullity_eq_zero` — Morse/Chapter1/Nondegenerate.lean, line 176
- `Morse.isNondegenerate_hessian_iff_det_ne_zero` — Morse/Chapter1/Nondegenerate.lean, line 335

*What differs.*
- The index is defined as Mathlib's negative index of inertia, and Milnor's definition, the maximal dimension of a negative definite subspace, is a theorem.
- Non-degeneracy is defined by a zero null space; Milnor's definition by a non-singular matrix of second partial derivatives is a theorem, for $f$ of class $C^2$ at $p$.
- The nullity is a dimension in Mathlib's sense, which is $0$ for an infinite-dimensional null space; the counts are meaningful in finite dimension, where they are used.

### V1.4. The same notions on a manifold; Morse functions

*restated* · the Hessian read in the preferred chart · no vector-field extensions · no Hausdorff hypothesis

**Milnor (§2, pp. 4–5).** At a critical point $p$ of $f$ on a manifold $M$, the Hessian is the symmetric bilinear functional $f_{**}$ on $TM_p$ given by $f_{**}(v, w) = \tilde v_p(\tilde w(f))$, where $\tilde v$ and $\tilde w$ are vector fields extending $v$ and $w$; it is symmetric because the Poisson bracket term $[\tilde v, \tilde w]_p(f)$ vanishes at a critical point, and hence independent of both extensions. In local coordinates its matrix in the basis $\partial/\partial x^i|_p$ is $(\partial^2 f/\partial x^i\partial x^j(p))$. The index of $f$ at $p$ is the index of $f_{**}$. Differentiable functions with no degenerate critical points are the subject of Theorem 3.5 (p. 20).

**Proved in Lean.** Let $M$ be a smooth manifold without boundary modelled on a real normed space $E$, with no Hausdorff or countability hypothesis, $f : M \to \mathbb R$ and $p \in M$. The point $p$ is a critical point of $f$ if $df_p : T_pM \to \mathbb R$ is $0$; equivalently, $df_p$ is not surjective, which is the companion project's definition. The Hessian $f_{**}$ at $p$ is the second derivative at $\kappa(p)$ of $f \circ \kappa^{-1}$, $\kappa$ the preferred chart at $p$: a bilinear form on $E$, which Mathlib identifies with $T_pM$ through the same chart. The index and the nullity of $f$ at $p$ are those of $f_{**}$, and $p$ is a non-degenerate critical point if it is critical and $f_{**}$ is non-degenerate. A Morse function is a $C^\infty$ function on $M$ all of whose critical points are non-degenerate.

- `Morse.IsCriticalPointM` — Morse/Chapter1/Manifold.lean, line 232
- `Morse.hessianM` — Morse/Chapter1/Manifold.lean, line 239
- `Morse.indexM` — Morse/Chapter1/Manifold.lean, line 247
- `Morse.nullityM` — Morse/Chapter1/Manifold.lean, line 251
- `Morse.IsNondegenerateCriticalPointM` — Morse/Chapter1/Manifold.lean, line 243
- `Morse.IsMorseFunction` — Morse/Chapter1/Manifold.lean, line 256
- `Morse.isCriticalPointM_iff_milnor` — Morse/Chapter1/Manifold.lean, line 388

*What differs.*
- Milnor's intrinsic formula $\tilde v_p(\tilde w(f))$, and its independence of the extensions, are not formalized. The formal Hessian is his coordinate expression, the matrix of second partial derivatives (his formula for extensions with constant coefficients), read in the preferred chart; its independence of the chart is proved instead (V1.5).
- Mathlib's derivative is $0$ at a point where $f$ is not differentiable, so such a point counts as critical; for smooth $f$ this never matters.

### V1.5. Independence of the coordinate system

*stronger* · $f$ only $C^2$ at $p$ · coordinates in any normed space · criticality used exactly once

**Milnor (§2, pp. 4–5).** Milnor remarks that non-degeneracy does not depend on the coordinate system, which can be checked directly and will also follow from the intrinsic definition of the Hessian; on p. 5 he computes that the matrix $(\partial^2 f/\partial x^i\partial x^j(p))$ represents $f_{**}$ with respect to the basis $\partial/\partial x^1|_p, \dots, \partial/\partial x^n|_p$.

**Proved in Lean.** On normed spaces: if $\psi$ is $C^2$ at $q$, $f$ is $C^2$ at $\psi(q)$ and $df_{\psi(q)} = 0$, then $d^2(f\circ\psi)_q(v, w) = d^2 f_{\psi(q)}(d\psi_q v, d\psi_q w)$. On a manifold $M$ as in V1.4, a smooth coordinate system is a homeomorphism $y$ of an open subset of $M$ onto an open subset of a real normed space $E'$, $C^\infty$ with $C^\infty$ inverse (for $E' = E$ these are exactly the charts of the maximal atlas); let $p$ lie in its domain. If $f$ is differentiable at $p$, then $p$ is critical iff $y(p)$ is a critical point of $f \circ y^{-1}$, that is, for $E' = \mathbb R^n$, iff all the $\partial f/\partial y^i(p)$ vanish. If $f$ is $C^2$ at $p$ and $p$ is critical, the Hessian of $f \circ y^{-1}$ at $y(p)$ is $f_{**}$ composed in both arguments with the derivative of $y^{-1}$ at $y(p)$; hence non-degeneracy, index and nullity are those of $f \circ y^{-1}$ at $y(p)$, and for $E' = \mathbb R^n$, $p$ is non-degenerate iff $\det(\partial^2 f/\partial y^i\partial y^j(p)) \ne 0$.

- `Morse.hessian_comp` — Morse/Chapter1/Nondegenerate.lean, line 264
- `Morse.IsSmoothCoord` — Morse/Chapter1/Manifold.lean, line 454
- `Morse.isSmoothCoord_iff_mem_maximalAtlas` — Morse/Chapter1/Manifold.lean, line 484
- `Morse.IsSmoothCoord.isCriticalPointM_iff_forall_partial` — Morse/Chapter1/Manifold.lean, line 814
- `Morse.IsSmoothCoord.hessian_comp_symm` — Morse/Chapter1/Manifold.lean, line 744
- `Morse.IsSmoothCoord.isNondegenerate_iff` — Morse/Chapter1/Manifold.lean, line 756
- `Morse.IsSmoothCoord.index_eq` — Morse/Chapter1/Manifold.lean, line 764
- `Morse.IsSmoothCoord.nullity_eq` — Morse/Chapter1/Manifold.lean, line 772
- `Morse.IsSmoothCoord.isNondegenerate_iff_det_ne_zero` — Morse/Chapter1/Manifold.lean, line 830

*What differs.*
- Milnor works with smooth functions and coordinates in $\mathbb R^n$; the formal statements need $f$ only $C^2$ at $p$ and allow coordinates with values in any real normed space.
- Criticality enters exactly once, to kill the first-order term $df(d^2\psi)$ of the chain rule: away from a critical point the matrix of second partial derivatives is not a tensor.

### V1.6. Functions on a slice submanifold

*not in the book* · the setting of Chapters 2–4 · Hessian of $F \circ x$, not of $F$ · Milnor's formulas of pp. 35–36 proved

**Milnor (§6, pp. 35–36).** The book has no separate setting for functions on a submanifold. §2 is written for an abstract manifold, and from §6 on Milnor computes on $M \subset \mathbb R^n$ in local coordinates $u \mapsto \vec x(u)$ without comment. For $L_{\vec p}(\vec q) = \|\vec q - \vec p\|^2$ he notes that $\vec q$ is critical iff $\vec q - \vec p$ is normal to $M$ at $\vec q$ (p. 35), and that at a critical point the second partial derivatives are $2(\partial\vec x/\partial u^i \cdot \partial\vec x/\partial u^j + \partial^2\vec x/\partial u^i\partial u^j \cdot (\vec x - \vec p))$ (p. 36).

**Proved in Lean.** Let $V$ be a real normed space and $N \subseteq V$ a slice submanifold modelled on $Z$ in the sense of the companion project: every point of $N$ lies in the domain of a slice chart $\sigma$, a $C^\infty$ diffeomorphism of an open subset of $V$ onto an open subset of $Z \times W$ carrying the points of $N$ in its domain exactly onto $Z \times \{0\}$. $N$ need not be closed; it is a smooth manifold modelled on $Z$, with the parametrizations $x(z) = \sigma^{-1}(z, 0)$. Let $T_qN \subseteq V$ be the range of the derivative of the inclusion, $F : V \to \mathbb R$, and $q \in N$ in the domain of $\sigma$. If $F$ is differentiable at $q$, then $q$ is a critical point of $F|N$ iff $\sigma(q)_1$ is a critical point of $F \circ x$, iff $dF_q$ vanishes on $T_qN$, and, for a complete inner product space $V$, iff $\nabla F(q) \perp T_qN$. If $F$ is $C^2$ at a critical point $q$ of $f = F|N$, the Hessian of $F \circ x$ at $\sigma(q)_1$ is the Hessian $f_{**}$ of V1.4 composed with the derivative of the parametrization, so non-degeneracy, index and nullity of $F|N$ at $q$ are those of $F \circ x$. For $V$ an inner product space and $L_p(y) = \|y - p\|^2$: $q$ is a critical point of $L_p|N$ iff $q - p \perp T_qN$; for any $x$ of class $C^2$ at $u$, the second derivative of $L_p \circ x$ at $u$ is $2(\langle \partial x/\partial v, \partial x/\partial w\rangle + \langle \partial^2 x/\partial v\,\partial w, x(u) - p\rangle)$; and at a critical point the index and the nullity of $L_p|N$ are those of this form.

- `Milnor.IsSliceSubmanifold` — ../Milnor/Chapter2/Submanifold.lean, line 116
- `Morse.sliceParam` — Morse/Chapter1/ManifoldSubmanifold.lean, line 98
- `Morse.tangentSubspace` — Morse/Chapter1/ManifoldSubmanifold.lean, line 294
- `Morse.isCriticalPointM_comp_val_iff_forall_tangent` — Morse/Chapter1/ManifoldSubmanifold.lean, line 332
- `Morse.isCriticalPointM_comp_val_iff_gradient_mem_orthogonal` — Morse/Chapter1/ManifoldSubmanifold.lean, line 364
- `Morse.hessian_comp_sliceParam` — Morse/Chapter1/ManifoldSubmanifold.lean, line 211
- `Morse.isNondegenerateCriticalPointM_comp_val_iff_sliceParam` — Morse/Chapter1/ManifoldSubmanifold.lean, line 267
- `Morse.isCriticalPointM_normSq_sub_iff` — Morse/Chapter1/ManifoldSubmanifold.lean, line 423
- `Morse.hessian_normSq_sub_comp` — Morse/Chapter1/ManifoldSubmanifold.lean, line 441
- `Morse.indexM_normSq_sub_eq` — Morse/Chapter1/ManifoldSubmanifold.lean, line 455

*What differs.*
- No counterpart as a statement: these identifications are what Milnor uses silently whenever he computes on a submanifold in a parametrization, and every later statement about a submanifold of Euclidean space rests on them.
- The Hessian of $F \circ x$ is not the restriction of the ambient Hessian of $F$: the chain rule adds $dF_q(\partial^2 x/\partial v\,\partial w)$, which does not vanish at a critical point of $F|N$ and which, for $L_p$, is the second-fundamental-form term of Milnor's formula.

### V1.7. Lemma 2.1 (Hadamard)

*stronger* · star-shaped, not convex · any normed source, complete target · $B(0) = \frac12 d^2f_0$ proved · $V$ open

**Milnor (§2, Lemma 2.1, p. 5).** A $C^\infty$ function $f$ on a convex neighbourhood $V$ of $0$ in $\mathbb R^n$ with $f(0) = 0$ can be written $f(x) = \sum_i x_i g_i(x)$, the $g_i$ being $C^\infty$ on $V$ with $g_i(0) = \partial f/\partial x_i(0)$. The proof writes $f(x)$ as $\int_0^1 \frac{d}{dt} f(tx)\,dt$ and takes $g_i(x) = \int_0^1 \partial f/\partial x_i(tx)\,dt$.

**Proved in Lean.** Let $V \subseteq \mathbb R^n$ be open and convex with $0 \in V$, and $f$ smooth on $V$ with $f(0) = 0$. Then $f(x) = \sum_i x_i g_i(x)$ on $V$ for functions $g_i$ smooth on $V$ with $g_i(0) = \partial f/\partial x_i(0)$. More generally, let $V$ be open and star-shaped about $0$ in a real normed space $E$ and $f$ smooth on $V$, with values in a complete normed space and $f(0) = 0$. Then $f(x) = L(x)\,x$ on $V$ for a family of linear maps $L$ smooth on $V$ with $L(0) = df_0$; and if moreover $df_0 = 0$, then $f(x) = B(x)(x, x)$ on $V$ for a family of bilinear maps $B$ smooth on $V$, with $B(x)$ symmetric for each $x \in V$ and $B(0) = \frac12 d^2 f_0$. Along the way: if $h$ is $C^n$ on an open $U \subseteq E \times \mathbb R$ containing $V \times [0, 1]$, $V$ open, then $x \mapsto \int_0^1 h(x, t)\,dt$ is $C^n$ on $V$.

- `Morse.exists_hadamard_coord` — Morse/Chapter1/Hadamard.lean, line 253
- `Morse.exists_hadamard_on` — Morse/Chapter1/Hadamard.lean, line 224
- `Morse.exists_hadamard_two_on` — Morse/Chapter1/Hadamard.lean, line 280
- `Morse.contDiffOn_intervalIntegral` — Morse/Chapter1/Hadamard.lean, line 178

*What differs.*
- Convexity is weakened to star-shapedness, $\mathbb R^n$ to any real normed space, and the values may lie in any complete normed space; $V$ must be open, which the book leaves implicit.
- The smoothness of the $g_i$, which Milnor does not argue, is differentiation under the integral sign on an open set, proved here.
- On p. 7 Milnor applies the lemma twice, symmetrizes, and asserts without proof that the coefficients at $0$ are $\frac12\,\partial^2 f/\partial x^i\partial x^j(0)$. That second-order form is proved directly, by Taylor's formula with integral remainder, with $B(x) = \int_0^1 (1 - t)\,d^2 f_{tx}\,dt$.

### V1.8. Lemma 2.2 (the lemma of Morse)

*stronger* · $f$ smooth only near $p$ · any manifold, no Hausdorff hypothesis · one inverse-function step

**Milnor (§2, Lemma 2.2, p. 6).** Near a non-degenerate critical point $p$ of $f$ there are local coordinates $(y^1, \dots, y^n)$, all vanishing at $p$, on a neighbourhood $U$ of $p$, in which $f = f(p) - (y^1)^2 - \dots - (y^\lambda)^2 + (y^{\lambda+1})^2 + \dots + (y^n)^2$ on all of $U$, $\lambda$ being the index of $f$ at $p$. The proof writes $f = \sum x_ix_jh_{ij}$ by Lemma 2.1 and completes one square at a time by induction, after a linear change of the last $n - r + 1$ coordinates making $H_{rr}(0) \ne 0$.

**Proved in Lean.** Let $E$ be a finite-dimensional real normed space, $n = \dim E$, $f$ smooth on an open set $U \ni p$, and $p$ a critical point at which $d^2 f_p$ is non-degenerate, of index $\lambda$. Then there is a homeomorphism $y$ of an open neighbourhood $U' \subseteq U$ of $p$ onto an open subset of $\mathbb R^n$, $C^\infty$ with $C^\infty$ inverse, such that $y(p) = 0$ and $f = f(p) - (y^1)^2 - \dots - (y^\lambda)^2 + (y^{\lambda+1})^2 + \dots + (y^n)^2$ throughout $U'$. In coordinate-free form, there is such a $\varphi$ onto an open subset of $E$ with $\varphi(p) = 0$, $d\varphi_p = \mathrm{id}$ and $f = f(p) + \frac12 d^2 f_p(\varphi, \varphi)$ on its domain. On a smooth manifold without boundary modelled on $E$, with no Hausdorff hypothesis, for $f$ smooth on an open $U \ni p$ and $p$ a non-degenerate critical point of index $\lambda$: there is a smooth coordinate system $y$ with values in $\mathbb R^n$, domain an open neighbourhood of $p$ inside $U$, $y(p) = 0$ and the same normal form on its domain; and there is a chart $\varphi$ of the maximal atlas with domain inside $U$, $\varphi(p) = 0$ and $f = f(p) + \frac12 f_{**}(\varphi, \varphi)$.

- `Morse.morse_lemma` — Morse/Chapter1/MorseLemma.lean, line 306
- `Morse.exists_morse_chart` — Morse/Chapter1/MorseLemma.lean, line 227
- `Morse.morse_lemmaM` — Morse/Chapter1/ManifoldMorse.lean, line 268
- `Morse.exists_morse_chartM` — Morse/Chapter1/ManifoldMorse.lean, line 236
- `Morse.exists_sqrt_family` — Morse/Chapter1/SquareRoot.lean, line 227
- `Morse.exists_linearEquiv_diagForm` — Morse/Chapter1/MorseLemma.lean, line 168

*What differs.*
- Milnor's $f$ is smooth on $M$; the formal $f$ need only be smooth on an open set containing $p$, and on a manifold no Hausdorff or countability hypothesis enters.
- The proof is not Milnor's induction, which completes one square at a time and does not justify the linear change making $H_{rr}(0) \ne 0$. One application of the inverse function theorem, to a map on linear operators whose derivative at the identity is $H \mapsto 2B_0(H\cdot, \cdot)$, gives linear maps $C(x)$, smooth in $x$, with $C(0) = \mathrm{id}$ and $f(p + x) = f(p) + \frac12 d^2 f_p(C(x)x, C(x)x)$.
- Sylvester's law of inertia, from Mathlib, then diagonalizes $\frac12 d^2 f_p$ with the negative squares first.

### V1.9. The index is forced by the normal form

*stronger* · criticality concluded, not assumed · non-degeneracy concluded

**Milnor (§2, proof of Lemma 2.2, p. 6).** The proof of Lemma 2.2 begins by showing that if $f(q) = f(p) - (z^1(q))^2 - \dots - (z^\lambda(q))^2 + (z^{\lambda+1}(q))^2 + \dots + (z^n(q))^2$ in some coordinate system $z$ around $p$, then $\lambda$ must be the index of $f$ at $p$: the matrix of $f_{**}$ in the basis $\partial/\partial z^i|_p$ is diagonal with $\lambda$ entries $-2$ and $n - \lambda$ entries $2$, so $f_{**}$ is negative definite on a subspace of dimension $\lambda$ and positive definite on one of dimension $n - \lambda$, and no larger negative definite subspace exists.

**Proved in Lean.** On a real normed space $E$ with $n = \dim E$: if $f$ is $C^2$ at a critical point $p$ and $z$ is a homeomorphism of an open neighbourhood of $p$ onto an open subset of $\mathbb R^n$, $C^\infty$ with $C^\infty$ inverse, with $z(p) = 0$ and $f = f(p) - \sum_{i \le k}(z^i)^2 + \sum_{i > k}(z^i)^2$ on its domain, $k \le n$, then $k$ is the index of $f$ at $p$. On a manifold as in V1.4, with no hypothesis on $f$: if $z$ is a smooth coordinate system around $p$ with values in $\mathbb R^n$, $z(p) = 0$, $k \le n$, and $f$ has this form on its domain, then $p$ is a non-degenerate critical point of $f$ of index $k$.

- `Morse.index_eq_of_morse_chart` — Morse/Chapter1/MorseLemma.lean, line 358
- `Morse.isNondegenerateCriticalPointM_of_morse_chart` — Morse/Chapter1/ManifoldMorse.lean, line 369
- `Morse.indexM_eq_of_morse_chart` — Morse/Chapter1/ManifoldMorse.lean, line 407

*What differs.*
- On a manifold the formal statement assumes nothing about $f$ beyond the normal form, and concludes that $p$ is a non-degenerate critical point, of index $k$.
- The proof is Milnor's, with the independence of coordinates (V1.5) that he uses without comment.

### V1.10. Corollary 2.3: non-degenerate critical points are isolated

*stronger* · $f$ only $C^2$ at $p$ · not through the lemma of Morse

**Milnor (§2, Corollary 2.3, p. 8).** A non-degenerate critical point is isolated: no other critical point comes arbitrarily close to it. The corollary is stated directly after the proof of Lemma 2.2, with no proof of its own.

**Proved in Lean.** Let $E$ be finite-dimensional. If $f : E \to \mathbb R$ is $C^2$ at $p$ and $p$ is a non-degenerate critical point, then $p$ has a neighbourhood in which it is the only critical point of $f$. The same holds on a manifold without boundary modelled on $E$, for $f$ of class $C^2$ at $p$.

- `Morse.IsNondegenerateCriticalPoint.exists_nhds_isCriticalPoint_eq` — Morse/Chapter1/Nondegenerate.lean, line 359
- `Morse.IsNondegenerateCriticalPointM.exists_nhds_isCriticalPointM_eq` — Morse/Chapter1/ManifoldMorse.lean, line 120

*What differs.*
- Milnor's functions are smooth; the formal statement needs only $C^2$ at the point, where the lemma of Morse is not available.
- The proof does not use the normal form: $x \mapsto df_x$ has the injective derivative $d^2 f_p$ at $p$, so it does not vanish at the points $x \ne p$ near $p$.

### V1.11. Finitely many critical points in a compact set

*not in the book* · used silently on p. 23 · no Hausdorff hypothesis

**Milnor (§3, proof of Theorem 3.5, p. 23).** The book does not state this. In the proof of Theorem 3.5 Milnor lists the critical values $c_1 < c_2 < c_3 < \dots$ and says that the sequence has no cluster point since each $M^a$ is compact, which needs each compact set to contain only finitely many critical points, a consequence of Corollary 2.3 left to the reader.

**Proved in Lean.** Let $M$ be as in V1.4. The critical set of a $C^1$ function on $M$ is closed. If $E$ is finite-dimensional and $f$ is $C^2$ with all its critical points non-degenerate, the critical points of $f$ form a discrete set and every compact set contains only finitely many of them; in particular a Morse function on a compact $M$ has finitely many critical points. Hausdorffness is not needed.

- `Morse.isClosed_setOf_isCriticalPointM` — Morse/Chapter1/ManifoldMorse.lean, line 135
- `Morse.isDiscrete_inter_setOf_isCriticalPointM` — Morse/Chapter1/ManifoldMorse.lean, line 158
- `Morse.finite_inter_setOf_isCriticalPointM` — Morse/Chapter1/ManifoldMorse.lean, line 177
- `Morse.IsMorseFunction.finite_setOf_isCriticalPointM` — Morse/Chapter1/ManifoldMorse.lean, line 188

*What differs.*
- A consequence of Corollary 2.3 that the book uses without stating. Theorem 3.5, the Morse inequalities and the Euler characteristic formula all count critical points, and this is what makes the counts finite.

### V1.12. Examples of degenerate critical points

*value differs* · (d): the $y$ axis, not the $x$ axis · (a), (c): the only critical point · (b) not formalized

**Milnor (§2, pp. 8–9).** Milnor pictures five degenerate critical points: (a) $f(x) = x^3$ at the origin; (b) $e^{-1/x^2}\sin^2(1/x)$, whose origin is a degenerate and non-isolated critical point; (c) the monkey saddle $x^3 - 3xy^2$, the real part of $(x + iy)^3$, at $(0, 0)$; (d) $f(x, y) = x^2$, whose critical points, all degenerate, form the $x$ axis, a submanifold of $\mathbb R^2$; (e) $x^2y^2$, whose degenerate critical points fill the union of the $x$ and $y$ axes, not even a submanifold of $\mathbb R^2$.

**Proved in Lean.** (a) The only critical point of $x^3$ on $\mathbb R$ is $0$, where the Hessian is $0$, so it is degenerate. (c) The only critical point of $x^3 - 3xy^2$ on $\mathbb R^2$ is the origin, where the Hessian is $0$. (d) The critical points of $x^2$ on $\mathbb R^2$ are the points of the line $x = 0$, and all are degenerate. (e) The critical points of $x^2y^2$ are the points of the two coordinate axes, and all are degenerate. In (d) and (e) degeneracy is the contrapositive of Corollary 2.3: a critical point that is a limit of other critical points, of a function $C^2$ there, is degenerate.

- `Morse.Examples.cube_degenerate` — Morse/Chapter1/Examples.lean, line 100
- `Morse.Examples.isCriticalPoint_cube_iff` — Morse/Chapter1/Examples.lean, line 80
- `Morse.Examples.hessian_cube` — Morse/Chapter1/Examples.lean, line 88
- `Morse.Examples.monkey_degenerate` — Morse/Chapter1/Examples.lean, line 155
- `Morse.Examples.isCriticalPoint_monkey_iff` — Morse/Chapter1/Examples.lean, line 120
- `Morse.Examples.isCriticalPoint_sqFst_iff` — Morse/Chapter1/Examples.lean, line 172
- `Morse.Examples.not_isNondegenerate_sqFst` — Morse/Chapter1/Examples.lean, line 181
- `Morse.Examples.isCriticalPoint_sqMul_iff` — Morse/Chapter1/Examples.lean, line 202
- `Morse.Examples.not_isNondegenerate_sqMul` — Morse/Chapter1/Examples.lean, line 220
- `Morse.not_isNondegenerate_of_frequently` — Morse/Chapter1/Examples.lean, line 46

*What differs.*
- In (d) the book says the critical set is the $x$ axis; since $\partial f/\partial x = 2x$ and $\partial f/\partial y = 0$, it is the $y$ axis. The formalization noticed this.
- In (a) and (c) the formal statements add that the origin is the only critical point.
- Example (b) is not formalized: its smoothness at $0$ needs the flatness of $e^{-1/x^2}$ against the growth of the derivatives of $\sin^2(1/x)$. Nor are the submanifold claims of (d) and (e).

### V1.13. One-parameter groups of diffeomorphisms

*narrower* · $M$ a vector space $E$ · $\varphi_0 = \mathrm{id}$ proved

**Milnor (§2, pp. 9–10).** Milnor's 1-parameter group of diffeomorphisms of $M$ is a $C^\infty$ map $\varphi : \mathbb R \times M \to M$ whose maps $\varphi_t$ are diffeomorphisms of $M$ with $\varphi_{t+s} = \varphi_t \circ \varphi_s$. It determines the vector field $X_q(f) = \lim_{h \to 0} (f(\varphi_h(q)) - f(q))/h$, which is said to generate $\varphi$, and each orbit $t \mapsto \varphi_t(q)$ solves $d\varphi_t(q)/dt = X_{\varphi_t(q)}$ with $\varphi_0(q) = q$.

**Proved in Lean.** On a real normed space $E$, a one-parameter group of diffeomorphisms is a map $\varphi : \mathbb R \times E \to E$, $C^\infty$ in $(t, x)$, such that each $\varphi_t$ is a $C^\infty$ diffeomorphism of $E$ and $\varphi_{t+s} = \varphi_t\circ\varphi_s$ for all $t$, $s$. A vector field $X : E \to E$ generates $\varphi$ if for every $x$ the curve $h \mapsto \varphi_h(x)$ has derivative $X(x)$ at $h = 0$. Then $\varphi_0 = \mathrm{id}$, and if $X$ generates $\varphi$, every orbit $t \mapsto \varphi_t(x)$ is an integral curve of $X$.

- `Morse.IsOneParameterGroup` — Morse/Flow/Smooth.lean, line 259
- `Morse.Generates` — Morse/Flow/Smooth.lean, line 267
- `Morse.IsOneParameterGroup.zero` — Morse/Flow/Smooth.lean, line 272
- `Morse.IsOneParameterGroup.isIntegralCurve` — Morse/Flow/Smooth.lean, line 286

*What differs.*
- Only for $M = E$, where a tangent vector is a vector and Milnor's limit defining $X_q(f)$ becomes the derivative of $h \mapsto \varphi_h(q)$.
- That $\varphi_0 = \mathrm{id}$, used on p. 10 as the initial condition, follows from the group law because $\varphi_0$ is injective.

### V1.14. Global flows, and smooth dependence on the initial point

*restated* · global, not local and iterated · smooth dependence proved, not quoted · vector spaces only

**Milnor (§2, pp. 10–11).** In the proof of Lemma 2.4 Milnor quotes as well known, citing Graves, that the equation $d\varphi_t(q)/dt = X_{\varphi_t(q)}$, $\varphi_0(q) = q$, has locally a unique solution which depends smoothly on the initial conditions. Covering the compact support $K$ by finitely many such neighbourhoods gives $\epsilon_0 > 0$ and solutions for $|t| < \epsilon_0$, smooth in both variables; for larger $t$ he iterates $\varphi_{\epsilon_0/2}$, and says it is not difficult to verify that the result is well defined, smooth, and satisfies $\varphi_{t+s} = \varphi_t\circ\varphi_s$.

**Proved in Lean.** Let $E$ be a complete real normed space and $X : E \to E$ bounded and globally Lipschitz, for instance $C^1$ with compact support. Through every point there is an integral curve of $X$ defined on all of $\mathbb R$, every integral curve is a flow line, and the flow satisfies $\varphi_0 = \mathrm{id}$ and $\varphi_{s+t} = \varphi_s\circ\varphi_t$, is jointly continuous in $(t, x)$, and each $\varphi_t$ is a homeomorphism with inverse $\varphi_{-t}$. If $X$ is $C^n$, $1 \le n \le \infty$, with compact support, then $(t, x) \mapsto \varphi_t(x)$ is $C^n$ on $\mathbb R \times E$ and each $\varphi_t$ is a $C^n$ diffeomorphism.

- `Morse.IsBddLipschitz` — Morse/Flow/Global.lean, line 77
- `Morse.flow` — Morse/Flow/Global.lean, line 171
- `Morse.IsBddLipschitz.isIntegralCurve_flow` — Morse/Flow/Global.lean, line 190
- `Morse.IsBddLipschitz.eq_flow` — Morse/Flow/Global.lean, line 199
- `Morse.IsBddLipschitz.flow_add` — Morse/Flow/Global.lean, line 206
- `Morse.IsBddLipschitz.flowHomeomorph` — Morse/Flow/Global.lean, line 336
- `Morse.contDiff_flow_uncurry` — Morse/Flow/Smooth.lean, line 185
- `Morse.flowDiffeomorph` — Morse/Flow/Smooth.lean, line 237

*What differs.*
- Milnor quotes the local theory and iterates it; the formal statements are global, for bounded Lipschitz or compactly supported fields on a Banach space, so no consistency of the splitting of $t$ into multiples of $\epsilon_0/2$ has to be checked.
- Smooth dependence on the initial point, which Mathlib lacks, is proved rather than quoted: on $[0, 1]$ the flow line through $x$ solves $\Psi(\gamma) = x$ in the Banach space $C([0, 1], E)$, with $\Psi(\gamma) = \gamma - \int_0^{\cdot} X(\gamma)$ a homeomorphism with everywhere invertible derivative for a small Lipschitz constant, so the time-one map is as smooth as $X$.
- Only vector spaces are treated; on submanifolds of $\mathbb R^K$ Chapter 2 uses the ambient flow of a field tangent to the submanifold instead.

### V1.15. Lemma 2.4: compactly supported fields generate flows

*narrower* · $M$ a vector space $E$ · uniqueness among all generated groups

**Milnor (§2, Lemma 2.4, p. 10).** If a smooth vector field on $M$ vanishes outside some compact set $K \subset M$, then it generates exactly one 1-parameter group of diffeomorphisms of $M$.

*The Remark on p. 11 shows that compact support cannot be omitted: $d/dt$ on the open interval $(0, 1)$ generates no 1-parameter group.*

**Proved in Lean.** Let $E$ be a complete real normed space and $X : E \to E$ a $C^\infty$ vector field which vanishes outside a compact set. Then there is exactly one one-parameter group of diffeomorphisms of $E$ (V1.13) generated by $X$, namely its flow (V1.14).

- `Morse.lemma_2_4` — Morse/Flow/Smooth.lean, line 300

*What differs.*
- Only for $M = E$. If $E$ is infinite-dimensional the hypothesis forces $X = 0$, so the content is the case $E = \mathbb R^n$; on a manifold that is not a vector space the lemma is not formalized.
- The uniqueness, implicit in the book, holds among all one-parameter groups generated by $X$, because uniqueness of integral curves is global in time; on a manifold it would need $M$ Hausdorff.

## Chapter 2

*Milnor §3, pp. 12–24: the homotopy type of sublevel sets, attaching cells*

### V2.1. Sublevel sets and strong deformation retracts

*stronger* · the strong form, fixing $A$ throughout · Milnor gives no definition

**Milnor (§3, pp. 12–13).** Throughout §3, $M^a = f^{-1}(-\infty, a] = \{p \in M : f(p) \le a\}$. Milnor uses “deformation retract” without a definition: in the proof of Theorem 3.1 he builds a 1-parameter family of maps $r_t : M^b \to M^b$ with $r_0$ the identity and $r_1$ a retraction onto $M^a$, concludes that $M^a$ is a deformation retract of $M^b$, and so that the inclusion is a homotopy equivalence.

**Proved in Lean.** For a real function $f$ on a set and $c \in \mathbb R$, $M^c = \{x : f(x) \le c\}$. A subset $A$ of a topological space $X$ is a strong deformation retract of $X$ if there are a continuous map $r : X \to X$ with values in $A$ and a homotopy $r_t$, $0 \le t \le 1$, from $r_0 = \mathrm{id}_X$ to $r_1 = r$ with $r_t(a) = a$ for all $t$ and all $a \in A$. If $A \subseteq B$ are subsets of a space and $A$ is a strong deformation retract of $B$, the inclusion $A \to B$ is a homotopy equivalence, with $r_1$ as homotopy inverse.

- `Morse.sublevel` — Morse/Chapter2/Crossing.lean, line 73
- `Morse.IsStrongDeformationRetract` — Morse/Chapter2/Crossing.lean, line 90
- `Morse.IsStrongDeformationRetract.exists_homotopyEquiv` — Morse/Chapter2/Crossing.lean, line 97

*What differs.*
- Every deformation Milnor constructs fixes the smaller set at all times, and every formal statement asserts this strong form, which implies the weaker ones; the strong form is also what the homology of pairs needs in Chapter 3 (V3.33).

### V2.2. Theorem 3.1 on a Euclidean space

*narrower* · $M = \mathbb R^n$ with an inner product · a diffeomorphism of $E$ onto itself · $a = b$ allowed

**Milnor (§3, Theorem 3.1, p. 12).** For a smooth real function $f$ on a manifold $M$ and $a < b$, if the set $f^{-1}[a, b]$ of points where $a \le f \le b$ is compact and free of critical points of $f$, then $M^a$ and $M^b$ are diffeomorphic; moreover $M^a$ is a deformation retract of $M^b$, so the inclusion $M^a \to M^b$ is a homotopy equivalence. The proof chooses a Riemannian metric, takes $\rho$ equal to $1/\langle \mathrm{grad} f, \mathrm{grad} f\rangle$ on $f^{-1}[a, b]$ and vanishing outside a compact neighbourhood of it, and pushes $M^b$ down to $M^a$ along the flow $\varphi_t$ of $\rho\,\mathrm{grad} f$; then $\varphi_{b-a}$ carries $M^a$ diffeomorphically onto $M^b$.

**Proved in Lean.** Let $E$ be a finite-dimensional real inner product space, $f : E \to \mathbb R$ of class $C^\infty$, $a \le b$, and suppose that $f^{-1}[a, b]$ is compact and contains no critical point of $f$. Then there is a $C^\infty$ diffeomorphism $\Phi$ of $E$ with $\Phi(M^a) = M^b$; $M^a$ is a strong deformation retract of $M^b$; the inclusion $M^a \to M^b$ is a homotopy equivalence; and $M^a$ and $M^b$ are homeomorphic.

- `Morse.theorem_3_1` — Morse/Chapter2/Regular.lean, line 253
- `Morse.exists_diffeomorph_image_sublevel_eq` — Morse/Chapter2/Regular.lean, line 273
- `Morse.exists_cutoff` — Morse/Chapter2/Regular.lean, line 158
- `Morse.IsSlabFlow.image_sublevel` — Morse/Chapter2/Crossing.lean, line 326
- `Morse.IsSlabFlow.isStrongDeformationRetract` — Morse/Chapter2/Crossing.lean, line 384

*What differs.*
- Only on $\mathbb R^n$, whose inner product plays the part of Milnor's Riemannian metric; submanifolds of Euclidean space are V2.3, compact manifolds V2.4, and non-compact abstract manifolds are not covered.
- “$M^a$ is diffeomorphic to $M^b$” is formalized as what the proof gives, a diffeomorphism of the whole space carrying $M^a$ onto $M^b$, Milnor's $\varphi_{b-a}$.
- The cut-off $\rho$ is constructed. Milnor's “clearly” needs that each trajectory crosses the slab $f^{-1}[a, b]$ once, at unit speed, which is proved for any continuous flow along which $f$ has derivative $1$ in the slab; his two-case $r_t$ becomes the single continuous formula $r_t(q) = \varphi_{t\min(0,\, a - f(q))}(q)$.

### V2.3. Theorem 3.1 on a submanifold of Euclidean space

*narrower* · $N \subseteq V$, closed or not · $f$ the restriction of a smooth $F$ · no Riemannian metric

**Milnor (§3, Theorem 3.1, p. 12).** For a smooth real function $f$ on a manifold $M$ and $a < b$, if $f^{-1}[a, b]$ is compact and contains no critical points of $f$, then $M^a$ is diffeomorphic to $M^b$, and $M^a$ is a deformation retract of $M^b$, so that the inclusion is a homotopy equivalence.

**Proved in Lean.** Let $V$ be a finite-dimensional real normed space, $N \subseteq V$ a slice submanifold modelled on a finite-dimensional $Z$ (V1.6; $N$ need not be closed), $F : V \to \mathbb R$ of class $C^\infty$ and $f = F|N$. Let $a \le b$, and suppose that $f^{-1}[a, b] \subseteq N$ is compact and contains no critical point of $f$, as a function on the manifold $N$. Then there is a $C^\infty$ diffeomorphism $\Phi$ of $N$ with $\Phi(N^a) = N^b$, $N^a$ is a strong deformation retract of $N^b$, and the inclusion $N^a \to N^b$ is a homotopy equivalence. When $N$ is compact, the compactness of $f^{-1}[a, b]$ need not be assumed.

- `Morse.theorem_3_1_submanifold` — Morse/Chapter2/Submanifold.lean, line 372
- `Morse.theorem_3_1_submanifold_of_isCompact` — Morse/Chapter2/Submanifold.lean, line 442
- `Morse.flow_mem_of_tangent` — Morse/Chapter2/Submanifold.lean, line 336

*What differs.*
- $M$ is a submanifold of a Euclidean space, Hausdorff and second countable as a subset, and $f$ must be the restriction of a smooth function on the ambient space.
- No metric is used. Slice charts and bump functions give a smooth field $Y$ on $V$, tangent to $N$ along $N$, with $dF(Y) > 0$ on $f^{-1}[a, b]$; the field $\rho Y$, with $\rho\,dF(Y) = 1$ there, replaces $\rho\,\mathrm{grad} f$, and its flow on $V$ preserves $N$.

### V2.4. Theorem 3.1 on a compact manifold

*narrower* · $M$ compact · Hausdorff assumed · through a Whitney embedding

**Milnor (§3, Theorem 3.1, p. 12).** For a smooth real function $f$ on a manifold $M$ and $a < b$, if $f^{-1}[a, b]$ is compact and contains no critical points of $f$, then $M^a$ is diffeomorphic to $M^b$, and $M^a$ is a deformation retract of $M^b$, so that the inclusion is a homotopy equivalence.

**Proved in Lean.** Let $M$ be a compact Hausdorff smooth manifold without boundary modelled on a finite-dimensional real normed space, $f : M \to \mathbb R$ of class $C^\infty$, $a \le b$, and suppose that $f^{-1}[a, b]$ contains no critical point of $f$. Then a $C^\infty$ diffeomorphism of $M$ carries $M^a$ onto $M^b$, $M^a$ is a strong deformation retract of $M^b$, and the inclusion $M^a \to M^b$ is a homotopy equivalence.

- `Morse.theorem_3_1_of_compactSpace` — Morse/Chapter4/Whitney.lean, line 536
- `Morse.exists_diffeomorph_sliceSubmanifold` — Morse/Chapter4/Whitney.lean, line 180
- `Morse.exists_contDiff_comp_val_eq` — Morse/Chapter3/EulerChar.lean, line 203

*What differs.*
- Only compact $M$, Hausdorff as Milnor's manifolds tacitly are. Mathlib's Whitney embedding for compact manifolds makes $M$ diffeomorphic to a compact slice submanifold $N \subseteq \mathbb R^{K+1}$, on which $f$ is the restriction of a smooth function on $\mathbb R^{K+1}$, so V2.3 applies, and its conclusions are carried back to $M$.
- For a non-compact $M$ with $f^{-1}[a, b]$ compact the transfer would need a closed embedding into Euclidean space, which Mathlib does not have.

### V2.5. Compactness cannot be omitted

*restated* · the punctured plane, not Diagram 3 · not even homotopy equivalent

**Milnor (§3, Remark after Theorem 3.1, p. 13).** The compactness of $f^{-1}[a, b]$ is essential. Diagram 3 pictures a surface with a point $p$ between the levels $a$ and $b$ removed, where, Milnor says, $M^a$ is clearly not a deformation retract of $M^b$.

*The Remark is unnumbered; Remark 3.3 is the statement of p. 19.*

**Proved in Lean.** Let $M = \mathbb C \setminus \{i\}$, $f(z) = |z|^2$ on $M$, $a = \frac14$ and $b = 4$. No $z \in \mathbb C$ with $\frac14 \le |z|^2 \le 4$ is a critical point of $|z|^2$, but $f^{-1}[\frac14, 4] \subseteq M$ is not compact; $M^{1/4}$, the closed disc of radius $\frac12$, and $M^4$, the closed disc of radius $2$ without $i$, are not homotopy equivalent, so $M^{1/4}$ is not a strong deformation retract of $M^4$, and the two are not homeomorphic. With $i$ put back, Theorem 3.1 applies: in $\mathbb C$ the disc of radius $\frac12$ is a strong deformation retract of the disc of radius $2$.

- `Morse.RemarkP13.remark_p13` — Morse/Chapter2/Remark.lean, line 254
- `Morse.RemarkP13.remark_p13_not_isStrongDeformationRetract` — Morse/Chapter2/Remark.lean, line 260
- `Morse.RemarkP13.remark_p13_not_homeomorph` — Morse/Chapter2/Remark.lean, line 265
- `Morse.RemarkP13.remark_p13_not_isCompact` — Morse/Chapter2/Remark.lean, line 220
- `Morse.RemarkP13.remark_p13_not_isCriticalPoint` — Morse/Chapter2/Remark.lean, line 208
- `Morse.RemarkP13.remark_p13_plane` — Morse/Chapter2/Remark.lean, line 271

*What differs.*
- The pictured surface is replaced by the punctured plane, and the conclusion is the stronger one that the two sublevel sets are not even homotopy equivalent. $M$ is open in $\mathbb C$, so the critical points of $f$ are those of $|z|^2$.
- The “clearly” is the non-contractibility of the punctured disc, proved by lifting a null-homotopy of $z \mapsto z - i$ through the covering $\exp : \mathbb C \to \mathbb C \setminus \{0\}$.

### V2.6. Theorem 3.2 on a Euclidean space

*narrower* · $M = \mathbb R^n$ with an inner product · retraction onto an embedded cell · Milnor's $\mu$ constructed · $\partial F/\partial\eta \ge 1$, not $> 1$

**Milnor (§3, Theorem 3.2, p. 14).** Take a smooth $f : M \to \mathbb R$ and a non-degenerate critical point $p$ of index $\lambda$, with $c = f(p)$, and assume that for some $\epsilon > 0$ the set $f^{-1}[c - \epsilon, c + \epsilon]$ is compact with $p$ its only critical point. Then, once $\epsilon$ is small enough, $M^{c+\epsilon}$ is homotopy equivalent to $M^{c-\epsilon}$ with a $\lambda$-cell attached. In the proof a function $\mu$ modifies $f$ near $p$ to a smooth $F$ with $F^{-1}(-\infty, c - \epsilon] = M^{c-\epsilon} \cup H$, and four Assertions show that $M^{c-\epsilon} \cup e^\lambda$ is a deformation retract of $M^{c+\epsilon}$.

*The scan prints “a k-cell” and renders the index as “A”; both are read as $\lambda$, as the proof requires.*

**Proved in Lean.** Let $E$ be a finite-dimensional real inner product space, $f : E \to \mathbb R$ of class $C^\infty$, $p$ a critical point at which $d^2 f_p$ is non-degenerate, $\lambda$ its index and $c = f(p)$, and suppose that for some $\epsilon_0 > 0$ the set $f^{-1}[c - \epsilon_0, c + \epsilon_0]$ is compact and contains no critical point other than $p$. Then there is $\epsilon_1 > 0$ such that for every $\epsilon$ with $0 < \epsilon \le \epsilon_1$ there is a map $\chi$ from the closed unit ball $D^\lambda$ of $\mathbb R^\lambda$ to $E$, continuous and injective on $D^\lambda$, with $\chi(z) \in M^{c-\epsilon}$ exactly when $|z| = 1$ and $\chi(D^\lambda) \subseteq M^{c+\epsilon}$, such that $M^{c-\epsilon} \cup \chi(D^\lambda)$ is a strong deformation retract of $M^{c+\epsilon}$. Hence the inclusion of $M^{c-\epsilon} \cup \chi(D^\lambda)$ in $M^{c+\epsilon}$ is a homotopy equivalence, and there is an injective continuous $\varphi : S^{\lambda-1} \to M^{c-\epsilon}$ such that $M^{c+\epsilon}$ is homotopy equivalent to $M^{c-\epsilon} \cup_\varphi e^\lambda$.

- `Morse.theorem_3_2` — Morse/Chapter2/CellAttach.lean, line 812
- `Morse.theorem_3_2_homotopyEquiv` — Morse/Chapter2/CellAttach.lean, line 853
- `Morse.theorem_3_2_attach` — Morse/Chapter2/CellAdjunction.lean, line 212
- `Morse.milnorMu` — Morse/Chapter2/CellModel.lean, line 195
- `Morse.isMilnorMu_milnorMu` — Morse/Chapter2/CellModel.lean, line 239
- `Morse.isStrongDeformationRetract_handle` — Morse/Chapter2/CellAttach.lean, line 624
- `Morse.CellModel.retractModel` — Morse/Chapter2/CellModel.lean, line 479

*What differs.*
- Only on $\mathbb R^n$ with an inner product; on submanifolds of Euclidean space it is V2.8, and on abstract manifolds it is not formalized.
- The conclusion is stronger than a homotopy type: a strong deformation retraction of $M^{c+\epsilon}$ onto $M^{c-\epsilon}$ together with an embedded cell meeting it exactly in its boundary sphere, which is what the proof produces. “For all sufficiently small $\epsilon$” is read as “for every $\epsilon$ in some $(0, \epsilon_1]$”.
- Milnor's $\mu$ ($C^\infty$, $\mu(0) > \epsilon$, $\mu = 0$ on $[2\epsilon, \infty)$, $-1 < \mu' \le 0$), whose existence he does not show, is $\mu(r) = \frac34\int_r^{2\epsilon}\beta$ for a smooth plateau $\beta$. Assertion 2 uses $\partial F/\partial\eta \ge 1$; the scan shows $> 1$, which fails where $\mu' = 0$.
- The three cases of $r_t$ in Assertion 4 are one formula, $(x, y) \mapsto (x, \sigma_t(x, y)\,y)$, continuous on the whole patch; it pastes with the identity because it moves only points of the compact ellipsoid $\xi + 2\eta \le 2\epsilon$ and keeps them there.

### V2.7. A cell meeting a closed set in its boundary is attached to it

*hypotheses explicit* · $M$ Hausdorff, $A$ closed · the subspace is the adjunction space

**Milnor (§3, proof of Theorem 3.2, p. 16).** With $e^\lambda$ the set of points of the coordinate patch with $(u^1)^2 + \dots + (u^\lambda)^2 \le \epsilon$ and $u^{\lambda+1} = \dots = u^n = 0$, Milnor notes that $e^\lambda \cap M^{c-\epsilon}$ is precisely the boundary $\dot e^\lambda$, so that $e^\lambda$ is attached to $M^{c-\epsilon}$ as required. That the subspace $M^{c-\epsilon} \cup e^\lambda$ is then the space $M^{c-\epsilon} \cup_\varphi e^\lambda$ defined in §1 is not argued.

**Proved in Lean.** Let $A$ be a closed subset of a Hausdorff space $M$ and $\chi : \mathbb R^n \to M$ continuous and injective on $D^n$, with $\chi(z) \in A$ exactly when $|z| = 1$, for $z \in D^n$. Then the subspace $A \cup \chi(D^n)$ of $M$ is the pushout of $\varphi = \chi|S^{n-1} : S^{n-1} \to A$ and the inclusion $S^{n-1} \to D^n$, that is, $A \cup_\varphi e^n$ (V1.2), and $\varphi$ is injective. Consequently, if $f : M \to \mathbb R$ is continuous, $a \le b$, $\chi$ is as above for $A = M^a$, $\chi(D^n) \subseteq M^b$, and $M^a \cup \chi(D^n)$ is a strong deformation retract of $M^b$, then $M^b$ is homotopy equivalent to $M^a \cup_\varphi e^n$.

- `Morse.isPushout_of_cell` — Morse/Chapter2/CellAdjunction.lean, line 65
- `Morse.exists_isPushout_union_cell` — Morse/Chapter2/CellAdjunction.lean, line 148
- `Morse.exists_isPushout_union_cell_of_t2` — Morse/Chapter2/CellPatch.lean, line 465
- `Morse.exists_homotopyEquiv_pushout_of_cell` — Morse/Chapter2/CellPatch.lean, line 521

*What differs.*
- The identification of the subspace with the adjunction space is a lemma that Milnor does not state (Lemma D of the exposition). It needs $M$ Hausdorff and $A$ closed, so that the cell is closed and $\chi$ is a homeomorphism onto it.
- The proof checks the universal property of the pushout directly, by the pasting lemma for the closed cover of $A \cup \chi(D^n)$ by $A$ and $\chi(D^n)$.

### V2.8. Theorem 3.2 in a Morse patch, and on a submanifold

*narrower* · $N \subseteq V$, $f = F|N$ · Hausdorff used · the patch half in any Hausdorff space

**Milnor (§3, Theorem 3.2, p. 14).** For a non-degenerate critical point $p$ of index $\lambda$, $c = f(p)$, with $f^{-1}[c - \epsilon, c + \epsilon]$ compact and free of other critical points, $M^{c+\epsilon}$ has the homotopy type of $M^{c-\epsilon}$ with a $\lambda$-cell attached, for all sufficiently small $\epsilon$. The proof works in a coordinate neighbourhood $U$ of $p$ in which $f = c - \xi + \eta$; Assertion 3, that $F^{-1}(-\infty, c - \epsilon]$ is a deformation retract of $M^{c+\epsilon}$, is Theorem 3.1 applied to $F$, and the rest of the argument takes place in the patch.

**Proved in Lean.** (i) The topological half, in any Hausdorff space $M$. Let $X$, $Y$ be finite-dimensional real inner product spaces with $\dim X = \lambda$, $f : M \to \mathbb R$, $p \in M$, and $\varphi$ a homeomorphism of an open neighbourhood of $p$ onto an open subset of $X \times Y$ with $\varphi(p) = 0$, $f = f(p) - |x|^2 + |y|^2$ on its domain, and image containing the ball $|x|^2 + |y|^2 \le 2\epsilon$, $\epsilon > 0$. Let $\mu$ satisfy Milnor's four conditions, and let $F = f - \mu(|x|^2 + 2|y|^2)$ on the domain of $\varphi$ and $F = f$ elsewhere. If $F^{-1}(-\infty, f(p) - \epsilon]$ is a strong deformation retract of $M^{f(p)+\epsilon}$, the conclusion of V2.6 about the cell holds in $M$ for this $\epsilon$. (ii) Let $V$, $Z$ be finite-dimensional, $N \subseteq V$ a slice submanifold modelled on $Z$, $F : V \to \mathbb R$ of class $C^\infty$, $f = F|N$, $p \in N$ a non-degenerate critical point of $f$ of index $\lambda$, $c = f(p)$, and suppose that for some $\epsilon_0 > 0$ the set $f^{-1}[c - \epsilon_0, c + \epsilon_0]$ is compact and contains no critical point of $f$ other than $p$. Then there is $\epsilon_1 > 0$ such that for every $\epsilon \in (0, \epsilon_1]$ there is a cell $\chi(D^\lambda) \subseteq N^{c+\epsilon}$, $\chi$ continuous and injective on $D^\lambda$, meeting $N^{c-\epsilon}$ exactly in $\chi(S^{\lambda-1})$, with $N^{c-\epsilon} \cup \chi(D^\lambda)$ a strong deformation retract of $N^{c+\epsilon}$; and $N^{c+\epsilon}$ is homotopy equivalent to $N^{c-\epsilon} \cup_\varphi e^\lambda$ for an injective $\varphi$.

- `Morse.IsMorsePatch` — Morse/Chapter2/CellPatch.lean, line 68
- `Morse.IsMilnorMu` — Morse/Chapter2/CellModel.lean, line 127
- `Morse.patch_theorem_3_2` — Morse/Chapter2/CellPatch.lean, line 412
- `Morse.theorem_3_2_submanifold` — Morse/Chapter2/CellAttachSubmanifold.lean, line 236
- `Morse.theorem_3_2_attach_submanifold` — Morse/Chapter2/CellAttachSubmanifold.lean, line 318
- `Morse.exists_contDiff_comp_val_eq_of_chart` — Morse/Chapter2/CellAttachSubmanifold.lean, line 95

*What differs.*
- On a manifold, Theorem 3.2 is proved for $f = F|N$ on a slice submanifold of a Euclidean space; abstract manifolds, compact or not, are not covered.
- Hausdorffness, used silently by Milnor, is needed for the ellipsoid $\xi + 2\eta \le 2\epsilon$ to be closed in $M$, for the smoothness of $F$ and the continuity of $r_t$, and for the cell to be attached (V2.7); it is automatic for $N \subseteq V$.
- The Morse coordinates are the lemma of Morse on the manifold $N$, taken inside one slice chart. Assertion 3 is V2.3 applied to $F$, which first requires extending $F$ to a smooth function on $V$, a step that Milnor's intrinsic Theorem 3.1 does not need.

### V2.9. Remark 3.3: several critical points on one level

*narrower* · submanifolds of $V$ only · disjoint Morse charts · cells attached one at a time

**Milnor (§3, Remark 3.3, p. 19).** When the level $f^{-1}(c)$ contains $k$ non-degenerate critical points $p_1, \dots, p_k$, of indices $\lambda_1, \dots, \lambda_k$, the same kind of proof gives that $M^{c+\epsilon}$ is homotopy equivalent to $M^{c-\epsilon} \cup e^{\lambda_1} \cup \dots \cup e^{\lambda_k}$.

**Proved in Lean.** Let $N \subseteq V$, $F$ and $f = F|N$ be as in V2.8 (ii), $S$ a finite set of non-degenerate critical points of $f$, all with value $c$, and suppose that for some $\epsilon_0 > 0$ the set $f^{-1}[c - \epsilon_0, c + \epsilon_0]$ is compact and all its critical points lie in $S$. Then there is $\epsilon_1 > 0$ such that for every $\epsilon \in (0, \epsilon_1]$ there are cells $e_p = \chi_p(D^{\lambda_p})$, $p \in S$, $\lambda_p$ the index of $p$, each $\chi_p$ continuous and injective on $D^{\lambda_p}$, meeting $N^{c-\epsilon}$ exactly in $\chi_p(S^{\lambda_p - 1})$, contained in $N^{c+\epsilon}$ and pairwise disjoint, such that $N^{c-\epsilon} \cup \bigcup_{p \in S} e_p$ is a strong deformation retract of $N^{c+\epsilon}$.

- `Morse.remark_3_3_submanifold` — Morse/Chapter2/SeveralCritical.lean, line 366
- `Morse.isFiniteCellComplexType_union_cells` — Morse/Chapter2/CWType.lean, line 414

*What differs.*
- Only on slice submanifolds, for $f$ the restriction of an ambient smooth function.
- The hypotheses left to “a similar proof” are written out: a compact $f^{-1}[c - \epsilon_0, c + \epsilon_0]$ whose critical points all lie on the level, and Morse charts with pairwise disjoint domains, which needs Hausdorffness.
- That the union is $N^{c-\epsilon}$ with the cells attached one at a time is part of the proof of Theorem 3.5 (V2.12).

### V2.10. Remark 3.4: the critical level

*narrower* · $M = \mathbb R^n$ only · a lemma on nested retracts

**Milnor (§3, Remark 3.4, p. 20).** With a small change in the proof of 3.2, $M^c$ too is a deformation retract of $M^{c+\epsilon}$, being one of $F^{-1}(-\infty, c]$, which is one of $M^{c+\epsilon}$ (Diagram 8). Together with 3.2, Milnor says, one sees easily that $M^{c-\epsilon} \cup e^\lambda$ is a deformation retract of $M^c$.

*The scan prints it as “Remark 2.4”; p. 24 cites it as Remark 3.4.*

**Proved in Lean.** Under the hypotheses of V2.6, $E$ a finite-dimensional real inner product space, there is $\epsilon_1 > 0$ such that for every $\epsilon \in (0, \epsilon_1]$: $M^c$ is a strong deformation retract of $M^{c+\epsilon}$; and there is a map $\chi$ from $D^\lambda$ to $E$, continuous and injective on $D^\lambda$, with $\chi(z) \in M^{c-\epsilon}$ exactly when $|z| = 1$, such that the part of $M^{c-\epsilon} \cup \chi(D^\lambda)$ lying in $M^c$ is a strong deformation retract of $M^c$.

- `Morse.remark_3_4` — Morse/Chapter2/CriticalLevel.lean, line 187
- `Morse.IsStrongDeformationRetract.of_retract` — Morse/Chapter2/CriticalLevel.lean, line 59

*What differs.*
- Only on $\mathbb R^n$ with an inner product, not on submanifolds; so the Remark of p. 24 at a critical value is not reached there (V2.15).
- The “easily” uses a lemma Milnor does not state: if $A \subseteq B \subseteq C$ and both $A$ and $B$ are strong deformation retracts of $C$, then $A$ is a strong deformation retract of $B$; only the retraction of $C$ onto $B$ is used.
- The whole cell lies in $M^c$, since $f = c - \epsilon|z|^2$ on it; the proof uses this, but the formal statement does not record it.

### V2.11. Iterated adjunction spaces in place of CW-complexes

*narrower* · attaching maps not cellular · cells in the listed order · no cellular approximation

**Milnor (§3, Theorem 3.5, p. 20).** Theorem 3.5 asserts the homotopy type of a CW-complex, for whose definition Milnor refers to J. H. C. Whitehead. In the proof (p. 23) each attaching map is replaced, by cellular approximation, by a map into the $(\lambda_j - 1)$-skeleton, so that attaching the new cells to a CW-complex gives a CW-complex again.

**Proved in Lean.** A space $K$ is an iterated adjunction space with cells $(\lambda_1, \dots, \lambda_k)$ if it is obtained from the empty space by attaching a $\lambda_1$-cell, then a $\lambda_2$-cell, and so on, each along an arbitrary continuous map of its boundary sphere into the space built so far (V1.2). A space $X$ has the homotopy type of a finite cell complex with cells $(\lambda_1, \dots, \lambda_k)$ if it is homotopy equivalent to such a $K$.

- `Morse.IsCellAttachment` — Morse/Chapter2/CWType.lean, line 110
- `Morse.IsFiniteCellComplexType` — Morse/Chapter2/CWType.lean, line 119

*What differs.*
- Weaker than a CW-complex with these cells: the attaching maps need not be cellular, and the cells are attached in the listed order rather than by dimension.
- Milnor makes the attaching maps cellular by the cellular approximation theorem, which Mathlib does not have; with it and Lemma 3.6 such a space would be homotopy equivalent to a CW-complex with the same number of cells in each dimension, a step that is not formalized.

### V2.12. Theorem 3.5 for a compact submanifold of Euclidean space

*narrower* · compact $N \subseteq V$, $f = F|N$ · iterated adjunction space, not CW · non-compact case not done

**Milnor (§3, Theorem 3.5, p. 20).** A manifold $M$ carrying a differentiable function without degenerate critical points, all of whose sublevel sets $M^a$ are compact, is homotopy equivalent to a CW-complex with one cell of dimension $\lambda$ for each critical point of index $\lambda$. The proof (pp. 23–24) lists the critical values $c_1 < c_2 < \dots$, notes that $M^a$ is vacuous for $a < c_1$, passes each critical level by Theorems 3.1 and 3.2 and Remark 3.3, and carries the cells along homotopy equivalences by Lemmas 3.6 and 3.7; the non-compact case uses a direct limit and Whitehead's theorem.

**Proved in Lean.** Let $V$ be a finite-dimensional real normed space, $N \subseteq V$ a compact slice submanifold modelled on a finite-dimensional $Z$, $F : V \to \mathbb R$ of class $C^\infty$, and suppose that every critical point of $f = F|N$ is non-degenerate. Then the critical points of $f$ can be listed without repetition as $p_1, \dots, p_k$, with $f(p_1) \le \dots \le f(p_k)$, so that $N$ has the homotopy type of a finite cell complex with cells $(\lambda(p_1), \dots, \lambda(p_k))$ in the sense of V2.11, $\lambda(p)$ the index of $p$. In particular $N$ has the homotopy type of such a complex whose number of cells of dimension $\lambda$ is, for every $\lambda$, the number $C_\lambda$ of critical points of index $\lambda$. If the critical values are distinct, the list is strictly increasing.

- `Morse.theorem_3_5'` — Morse/Chapter2/CWType.lean, line 684
- `Morse.theorem_3_5_count'` — Morse/Chapter2/CWType.lean, line 712
- `Morse.theorem_3_5` — Morse/Chapter2/CWType.lean, line 351
- `Morse.theorem_3_5_count` — Morse/Chapter2/CWType.lean, line 381
- `Morse.isCriticalPointM_of_forall_le` — Morse/Chapter2/CWType.lean, line 151

*What differs.*
- $N$ is a compact submanifold of a Euclidean space and $f$ the restriction of an ambient smooth function; the non-compact case, with its direct limit and Whitehead's theorem, is not formalized.
- The conclusion is an iterated adjunction space (V2.11), not a CW-complex; Lemma 3.6 is not needed, since the attaching maps are not made cellular.
- Hidden steps made explicit: that $M^a$ is empty below the first critical value needs the global minimum to be a critical point, and that the critical values do not accumulate is V1.11.

### V2.13. Lemma 3.6 (Whitehead)

*as in the book*

**Milnor (§3, Lemma 3.6, p. 20).** If two maps $\varphi_0$, $\varphi_1$ of the sphere $\dot e^\lambda$ into $X$ are homotopic, the identity of $X$ extends to a homotopy equivalence $k$ from $X \cup_{\varphi_0} e^\lambda$ to $X \cup_{\varphi_1} e^\lambda$. The proof gives explicit formulas for $k$ and for a map $\ell$ the other way, and says it is not difficult to verify that $k\ell$ and $\ell k$ are homotopic to the identities.

**Proved in Lean.** Let $X$ be a topological space, $n \ge 0$, and $\varphi_0, \varphi_1 : S^{n-1} \to X$ homotopic maps. Then there is a homotopy equivalence $k : X \cup_{\varphi_0} e^n \to X \cup_{\varphi_1} e^n$ which is the identity on $X$. The proof uses Milnor's formulas for $k$ and $\ell$; the homotopies he leaves to the reader are written down, built through the exponential law for the locally compact $[0, 1]$, which is the fact, used silently, that $[0, 1] \times$ (a quotient map) is a quotient map.

- `Morse.lemma_3_6` — Morse/Chapter2/Attaching.lean, line 536
- `Morse.lemma36Homotopy` — Morse/Chapter2/Attaching.lean, line 513
- `Morse.cellHomotopy` — Morse/Chapter2/Attaching.lean, line 128

### V2.14. Lemma 3.7, and the Assertion of p. 22

*stronger* · the extension is named · uses the formula for $k$ of Lemma 3.6

**Milnor (§3, Lemma 3.7, p. 21).** For an attaching map $\varphi : \dot e^\lambda \to X$, every homotopy equivalence $f : X \to Y$ extends to a homotopy equivalence $F$ from $X \cup_\varphi e^\lambda$ to $Y \cup_{f\varphi} e^\lambda$. The proof, after an unpublished paper of Hilton, takes $F = f$ on $X$ and the identity on the cell, and rests on an Assertion (p. 22): if a map $F$ has a left homotopy inverse $L$ and a right homotopy inverse $R$, then $F$ is a homotopy equivalence, and $R$ (or $L$) is a two-sided homotopy inverse.

**Proved in Lean.** Let $X$, $Y$ be topological spaces, $\varphi : S^{n-1} \to X$ continuous and $f : X \to Y$ a homotopy equivalence. Then the map $F : X \cup_\varphi e^n \to Y \cup_{f\varphi} e^n$ equal to $f$ on $X$ and to the identity on the cell is a homotopy equivalence. And for maps $F$, $L$, $R$: if $LF \simeq \mathrm{id}$ and $FR \simeq \mathrm{id}$, then $RF \simeq \mathrm{id}$.

- `Morse.lemma_3_7` — Morse/Chapter2/Attaching.lean, line 671
- `Morse.homotopic_of_leftInv_rightInv` — Morse/Chapter2/Attaching.lean, line 650

*What differs.*
- Milnor's statement says only that $f$ extends to some homotopy equivalence; the formal statement names the extension, $f$ on $X$ and the identity on the cell, as his proof does.
- The proof is Milnor's, and it uses the formula for $k$ from the proof of Lemma 3.6, not only its statement.

### V2.15. The Remark of p. 24: sublevel sets at regular values

*narrower* · $a$ not a critical value · compact $N \subseteq V$, $f = F|N$ · iterated adjunction space

**Milnor (§3, Remark after Theorem 3.5, p. 24).** The proof of Theorem 3.5 also gives, for every $a$, that $M^a$ is homotopy equivalent to a finite CW-complex with one $\lambda$-cell for each critical point of index $\lambda$ in $M^a$, and this holds even when $a$ is a critical value (compare Remark 3.4).

**Proved in Lean.** Let $N \subseteq V$, $F$ and $f = F|N$ be as in V2.12, and let $a$ be a real number which is not a critical value of $f$. Then the critical points $p$ with $f(p) < a$ can be listed without repetition as $p_1, \dots, p_j$, with $f(p_1) \le \dots \le f(p_j)$, so that $N^a$ has the homotopy type of a finite cell complex with cells $(\lambda(p_1), \dots, \lambda(p_j))$ (V2.11).

- `Morse.isFiniteCellComplexType_sublevel'` — Morse/Chapter2/CWType.lean, line 551
- `Morse.isFiniteCellComplexType_sublevel` — Morse/Chapter2/CWType.lean, line 226

*What differs.*
- Only for $a$ not a critical value: at a critical value Remark 3.4 would be needed on submanifolds, where it is not formalized.
- As in V2.12, the setting is a compact submanifold of a Euclidean space and the conclusion an iterated adjunction space rather than a CW-complex.

## Chapter 3

*Milnor §§4–5, pp. 25–32: Reeb, the torus, the Morse inequalities, the Euler characteristic*

### V3.2. Small sublevel sets at the extrema are closed cells

*restated* · a ball, its sphere onto the level set · compactness and a strict minimum · index $0$ at a minimum, $n$ at a maximum

**Milnor (§4, proof of Theorem 4.1, p. 25).** In the proof of Reeb's theorem, with $f(p) = 0$ the minimum and $f(q) = 1$ the maximum, Milnor says that if $\epsilon$ is small enough the sets $M^\epsilon = f^{-1}[0, \epsilon]$ and $f^{-1}[1 - \epsilon, 1]$ are closed $n$-cells, by the lemma of Morse (2.2).

**Proved in Lean.** (i) On a manifold $M$ modelled on a real normed space $E$, a local minimum or local maximum of any $f : M \to \mathbb R$ is a critical point. If moreover $M$ is a smooth manifold without boundary, $E$ has finite dimension $n$, $f$ is smooth on an open $U \ni p$ and $p$ is a non-degenerate local minimum (maximum), then the index of $f$ at $p$ is $0$ (resp. $n$), and there are smooth coordinates $y$ on an open subset of $U$ containing $p$, with values in $\mathbb R^n$ with its Euclidean norm, such that $y(p) = 0$ and $f = f(p) + \|y\|^2$ (resp. $f = f(p) - \|y\|^2$) on the domain of $y$. (ii) Let $X$ be a compact topological space, $f : X \to \mathbb R$ continuous with a strict global minimum at $p$ ($f(p) < f(x)$ for all $x \ne p$), and $y$ a homeomorphism from an open neighbourhood of $p$ onto an open subset of a real normed space $F$, with $y(p) = 0$ and $f = f(p) + \|y\|^2$ on its domain. Then there is $\delta > 0$ such that for every $0 < \varepsilon < \delta$ the map $v \mapsto y^{-1}(\sqrt\varepsilon\, v)$ is continuous and injective on the closed unit ball of $F$, maps it onto $\{f \le f(p) + \varepsilon\}$, and maps the unit sphere onto the level set $\{f = f(p) + \varepsilon\}$. Applied to $-f$, the same holds at a strict maximum.

- `Morse.isCriticalPointM_of_isLocalMin` — Morse/Chapter3/ReebMorse.lean, line 95
- `Morse.indexM_eq_zero_of_isLocalMin` — Morse/Chapter3/ReebMorse.lean, line 170
- `Morse.indexM_eq_finrank_of_isLocalMax` — Morse/Chapter3/ReebMorse.lean, line 197
- `Morse.exists_morse_chart_of_isLocalMin` — Morse/Chapter3/ReebMorse.lean, line 226
- `Morse.exists_morse_chart_of_isLocalMax` — Morse/Chapter3/ReebMorse.lean, line 242
- `Morse.exists_image_closedBall_eq_sublevel` — Morse/Chapter3/ReebMorse.lean, line 274

*What differs.*
- The closed cell is produced as the image of the closed unit ball under a continuous injective map, with its boundary sphere going onto the level set, which the gluing at the end of the proof needs and “closed $n$-cell” does not say.
- The lemma of Morse describes $f$ only near $p$. That the whole sublevel set lies in the Morse chart needs compactness and the uniqueness of the minimum: off a small coordinate ball, $f \ge f(p) + \eta$ for some $\eta > 0$.
- That the minimum has index $0$ and the maximum index $n$, used without comment, is proved first: in a Morse chart $f$ decreases along an axis carrying a minus sign, so a minimum has none.

### V3.3. The two critical points are the minimum and the maximum

*hypotheses explicit* · $n \ge 1$ · strict extrema · non-degeneracy rules out a constant $f$

**Milnor (§4, proof of Theorem 4.1, p. 25).** The two critical points must be the minimum and the maximum points of $f$; Milnor normalizes $f(p) = 0$ at the minimum and $f(q) = 1$ at the maximum.

**Proved in Lean.** Let $M$ be a compact smooth manifold without boundary modelled on a finite-dimensional real normed space $E$ with $n = \dim E \ge 1$, and $f : M \to \mathbb R$ smooth with exactly two critical points, both non-degenerate. Then there are points $p$, $q$ with $f(p) < f(q)$ such that the critical points are exactly $p$ and $q$, $f(p) < f(x)$ for every $x \ne p$, $f(x) < f(q)$ for every $x \ne q$, and the index of $f$ is $0$ at $p$ and $n$ at $q$. Hausdorffness is not needed.

- `Morse.exists_min_max_of_ncard_eq_two` — Morse/Chapter3/Reeb.lean, line 230

*What differs.*
- In dimension $0$ every point is critical and $f$ may be constant, so $n \ge 1$ is needed. Non-degeneracy is what shows that $f$ is not constant: a constant $f$ would make its minimum point also a maximum, of index $n \ne 0$.
- That no other point takes an extreme value, which the cells of V3.2 need, is part of the conclusion.

### V3.4. Theorem 3.1 also carries the boundary level

*stronger* · the level $f^{-1}(a)$ goes onto $f^{-1}(b)$ · what the proof of 3.1 gives

**Milnor (§4, proof of Theorem 4.1, p. 25).** In the proof of Reeb's theorem, $M^\epsilon$ is homeomorphic to $M^{1-\epsilon}$ by Theorem 3.1, and $M$ is then the union of the two closed $n$-cells $M^{1-\epsilon}$ and $f^{-1}[1 - \epsilon, 1]$, matched along their common boundary.

**Proved in Lean.** Let $N$ be a slice submanifold of a finite-dimensional real normed space $V$, modelled on a finite-dimensional $Z$, $F : V \to \mathbb R$ smooth, $f = F|N$, and $a \le b$ with $f^{-1}[a, b]$ compact and containing no critical point of $f$. Then there is a smooth diffeomorphism $\Phi$ of $N$ with $\Phi(N^a) = N^b$ and $\Phi(f^{-1}(a)) = f^{-1}(b)$.

- `Morse.exists_diffeomorph_image_sublevel_level` — Morse/Chapter3/Reeb.lean, line 154
- `Morse.IsSlabFlow.image_level` — Morse/Chapter3/Reeb.lean, line 123

*What differs.*
- The gluing needs a homeomorphism that also carries the level $f^{-1}(\epsilon)$ onto $f^{-1}(1 - \epsilon)$. The statement of Theorem 3.1 does not give this; its proof does, since the flow moves the levels of the slab at unit speed, and $\Phi$ is the time-$(b - a)$ map of that flow.

### V3.5. Two closed balls glued along their boundary form a sphere

*hypotheses explicit* · Alexander's trick · $X$ Hausdorff · where smoothness is lost

**Milnor (§4, proof of Theorem 4.1, p. 25).** Thus $M$ is the union of two closed $n$-cells matched along their common boundary, and Milnor says that it is now easy to construct a homeomorphism between $M$ and $S^n$. None is constructed.

**Proved in Lean.** (i) Alexander's trick: if $g$ is a homeomorphism of the unit sphere of a real normed space $E$, the cone $x \mapsto \|x\|\,g(x/\|x\|)$, $0 \mapsto 0$, is a homeomorphism of $E$ that preserves norms and extends $g$. (ii) Let $X$ be a Hausdorff space, $n \ge 0$, $D^n$ and $S^{n-1}$ the closed unit ball and unit sphere of $\mathbb R^n$, and $h_1, h_2 : D^n \to X$ continuous and injective, with $h_1(D^n) \cup h_2(D^n) = X$, $h_1(D^n) \cap h_2(D^n) = h_1(S^{n-1})$ and $h_2(S^{n-1}) = h_1(S^{n-1})$. Then $X$ is homeomorphic to the unit sphere $S^n \subseteq \mathbb R^{n+1}$.

- `Morse.alexanderConeHomeomorph` — Morse/Chapter3/ReebGluing.lean, line 159
- `Morse.nonempty_homeomorph_sphere_of_union_closedBall` — Morse/Chapter3/ReebGluing.lean, line 282

*What differs.*
- The identification $h_2^{-1} \circ h_1$ of the two boundary spheres is in general not the identity and must be extended over a ball, which is Alexander's trick; the inverse is continuous because a continuous bijection from a compact space onto a Hausdorff space is a homeomorphism.
- The cone is in general not differentiable at $0$: this is where smoothness is lost, as Milnor's Remark 2 says it must be.

### V3.6. Theorem 4.1 (Reeb)

*narrower* · $N$ a submanifold of $V$ · exactly two critical points · a homeomorphism, as in Milnor

**Milnor (§4, Theorem 4.1 (Reeb), p. 25).** A compact manifold $M$ carrying a differentiable function with only two critical points, both non-degenerate, is homeomorphic to a sphere. The proof: the two critical points are the minimum and the maximum; small sublevel and superlevel sets are closed $n$-cells by Lemma 2.2; $M^\epsilon$ is homeomorphic to $M^{1-\epsilon}$ by Theorem 3.1; so $M$ is two closed $n$-cells matched along their boundary.

*Remark 1 adds that the theorem remains true for degenerate critical points, with a more difficult proof, and Remark 2 that $M$ need not be diffeomorphic to $S^n$.*

**Proved in Lean.** Let $N$ be a compact slice submanifold of a finite-dimensional real normed space $V$, modelled on a finite-dimensional space of dimension $n$, and $f = F|N$ with $F : V \to \mathbb R$ smooth. If $f$ has exactly two critical points, both non-degenerate, then $N$ is homeomorphic to the unit sphere $S^n \subseteq \mathbb R^{n+1}$. For a compact $N \subseteq \mathbb R^{K+1}$ modelled on $\mathbb R^n$, $n \ge 1$, the same holds for every smooth $f : N \to \mathbb R$, which is always the restriction of a smooth function on $\mathbb R^{K+1}$. In dimension $0$, where every point is critical, $N$ has exactly two points.

- `Morse.reeb` — Morse/Chapter3/Reeb.lean, line 426
- `Morse.reeb_of_finrank_pos` — Morse/Chapter3/Reeb.lean, line 302
- `Morse.reeb_of_finrank_eq_zero` — Morse/Chapter3/Reeb.lean, line 388
- `Morse.reeb_of_contMDiff` — Morse/Chapter3/Reeb.lean, line 442

*What differs.*
- $N$ is a compact submanifold of a vector space; the abstract compact Hausdorff case is V4.24, proved through the Whitney embedding.
- “Only two” is read as exactly two: on a non-empty compact manifold of positive dimension the extrema already give two. The sphere is $S^n$ with $n = \dim N$, and $N$ has no boundary.
- In dimension $0$ Milnor's proof does not apply, since $f$ may be constant, but every point is critical, so $N$ has two points.
- The proof is Milnor's, made complete by V3.2–V3.5; the normalization $f(p) = 0$, $f(q) = 1$ is not needed.

### V3.7. Subadditive and additive functions

*restated* · indices of a preorder for spaces · argument order reversed · every pair $a \le b$ allowed

**Milnor (§5, Definition, p. 28).** An integer-valued function $S$, defined on certain pairs of spaces, is subadditive if $S(X, Z) \le S(X, Y) + S(Y, Z)$ for every $X \supset Y \supset Z$, and additive if equality always holds.

**Proved in Lean.** Spaces are replaced by the elements of a preordered set $\iota$, $a \le b$ standing for $X_a \subseteq X_b$. A function on pairs is an integer-valued function $S(a, b)$ of two indices, used only for $a \le b$, where $S(a, b)$ stands for Milnor's $S(X_b, X_a)$, the smaller space written first. $S$ is subadditive if $S(a, c) \le S(a, b) + S(b, c)$ whenever $a \le b \le c$, and additive if equality always holds.

- `Morse.IsSubadditive` — Morse/Chapter3/Inequalities.lean, line 452
- `Morse.IsAdditive` — Morse/Chapter3/Inequalities.lean, line 456

*What differs.*
- Milnor does not say on which pairs $S$ is defined; the class must be closed under the passage from $(X, Y)$ and $(Y, Z)$ to $(X, Z)$. Here every pair $a \le b$ of the index set is allowed.

### V3.8. Lemma 5.1

*hypotheses explicit* · $n \ge 1$ · subadditivity only along the chain

**Milnor (§5, Lemma 5.1, p. 28).** For a subadditive $S$ and spaces $X_0 \subset X_1 \subset \dots \subset X_n$, $S(X_n, X_0) \le \sum_{i=1}^n S(X_i, X_{i-1})$, with equality when $S$ is additive. The proof is by induction on $n$, and taking $X_0 = \emptyset$ gives inequality (1), $S(X_n) \le \sum_i S(X_i, X_{i-1})$.

**Proved in Lean.** If $S$ is subadditive and $X_0 \le X_1 \le \dots \le X_n$ with $n \ge 1$, then $S(X_0, X_n) \le \sum_{k=0}^{n-1} S(X_k, X_{k+1})$, that is, in Milnor's notation, $S(X_n, X_0) \le \sum_{i=1}^n S(X_i, X_{i-1})$; if $S$ is additive, equality holds. One form assumes subadditivity only on the triples $X_0 \le X_m \le X_{m+1}$, which is all the induction uses.

- `Morse.IsSubadditive.le_sum` — Morse/Chapter3/Inequalities.lean, line 499
- `Morse.IsAdditive.eq_sum` — Morse/Chapter3/Inequalities.lean, line 506
- `Morse.le_sum_of_chain` — Morse/Chapter3/Inequalities.lean, line 465

*What differs.*
- For $n = 0$ the statement would be $S(X_0, X_0) \le 0$, which subadditivity does not give: it gives $S(X, X) \ge 0$. Milnor's induction starts at $n = 1$, and the hypothesis is written out.

### V3.9. The homology of a filtration, and its Morse numbers

*restated* · abstract, not singular homology · finiteness a consequence on chains

**Milnor (§5, pp. 28–30).** Milnor works with singular homology with coefficients in a field $F$: $R_\lambda(X, Y)$, the $\lambda$-th Betti number of $(X, Y)$, is the rank over $F$ of $H_\lambda(X, Y; F)$, for any pair for which this rank is finite. He uses the exact sequence of a triple $X \supset Y \supset Z$, with its final $\to 0$ (p. 29), and $C_\lambda$ counts the critical points of index $\lambda$.

**Proved in Lean.** Fix a field $F$ and a preordered set $\iota$. A homology of a filtration assigns to every degree $i \ge 0$ and indices $a$, $b$ a vector space $H_i(a, b)$ over $F$, to be read as $H_i(X_b, X_a; F)$, finite-dimensional for $a \le b$, and to every triple $a \le b \le c$ a long exact sequence of $F$-linear maps $\cdots \to H_i(a,b) \to H_i(a,c) \to H_i(b,c) \to H_{i-1}(a,b) \to \cdots \to H_0(a,b) \to H_0(a,c) \to H_0(b,c) \to 0$, exact at every term. Nothing else is assumed: no functoriality, no compatibility between the sequences of different triples, no vanishing of $H_*(a, a)$, no excision. For a chain $X_0 \le X_1 \le \dots \le X_n$ the Betti numbers are $R_i = \dim H_i(X_0, X_n)$ and the Morse numbers are $C_i = \sum_{k<n} \dim H_i(X_k, X_{k+1})$. On a chain indexed by $\mathbb N$ the structure can be built from the exact sequences and the finiteness of the steps alone, so that the finiteness of the total homology is a consequence.

- `Morse.LongExactSeq` — Morse/Chapter3/Inequalities.lean, line 320
- `Morse.FiltrationHomology` — Morse/Chapter3/Inequalities.lean, line 528
- `Morse.morseNumber` — Morse/Chapter3/Inequalities.lean, line 545
- `Morse.altSum` — Morse/Chapter3/Inequalities.lean, line 210
- `Morse.FiltrationHomology.ofSteps` — Morse/Chapter3/Inequalities.lean, line 796

*What differs.*
- Every algebraic statement of §5 (V3.10–V3.15) is proved for every such structure; singular homology over a field is an instance (V3.32), and the slab computation that applies it to a manifold is V3.33–V3.34.
- The final $\to 0$ of the sequence of a triple is the surjectivity of $H_0(X, Z) \to H_0(X, Y)$, which Milnor uses on p. 29.

### V3.10. The Betti numbers are subadditive, and the Euler characteristic additive

*restated* · $\chi$ truncated at a degree $N$ · pairs closed under triples

**Milnor (§5, p. 28).** $R_\lambda$ is subadditive, as is easily seen from the portion $H_\lambda(Y, Z) \to H_\lambda(X, Z) \to H_\lambda(X, Y)$ of the exact sequence of the triple; and the Euler characteristic $\chi(X, Y) = \sum (-1)^\lambda R_\lambda(X, Y)$ is additive, which is asserted without argument.

**Proved in Lean.** For a homology of a filtration: (i) for every $\lambda$, $(a, b) \mapsto \dim H_\lambda(a, b)$ is subadditive, and in a segment $H_\lambda(a, b) \to H_\lambda(a, c) \to H_\lambda(b, c)$ of a long exact sequence the middle term is finite-dimensional when the outer two are; (ii) the alternating sum of the dimensions in a finite exact sequence $0 \to V_n \to \dots \to V_0 \to 0$ of finite-dimensional spaces is $0$; (iii) if $H_{N+1}(a, b) = 0$ for all $a \le b$, the truncated Euler characteristic $\chi_N(a, b) = \sum_{i \le N} (-1)^i \dim H_i(a, b)$ is additive.

- `Morse.LongExactSeq.finrank_le` — Morse/Chapter3/Inequalities.lean, line 365
- `Morse.LongExactSeq.finiteDimensional_middle` — Morse/Chapter3/Inequalities.lean, line 352
- `Morse.FiltrationHomology.isSubadditive_finrank` — Morse/Chapter3/Inequalities.lean, line 558
- `Morse.altSum_finrank_eq_zero_of_exact` — Morse/Chapter3/Inequalities.lean, line 304
- `Morse.LongExactSeq.altSum_eq_of_finrank_eq_zero` — Morse/Chapter3/Inequalities.lean, line 429
- `Morse.FiltrationHomology.isAdditive_eulerChar` — Morse/Chapter3/Inequalities.lean, line 581

*What differs.*
- Additivity of $\chi$ needs the total homology to be finite; here $\chi$ is truncated at a degree $N$, with vanishing in degree $N + 1$, and is Milnor's $\chi$ when the homology vanishes above $N$.
- That the pairs with finite-dimensional homology are closed under triples, which subadditivity presupposes, is the second half of (i).

### V3.11. Theorem 5.2 (weak Morse inequalities), abstractly

*narrower* · slab homology assumed (cell hypothesis) · abstract $R_\lambda$, not Betti numbers · any number of points per slab

**Milnor (§5, Theorem 5.2, p. 29).** On a compact manifold $M$, with $C_\lambda$ the number of critical points of index $\lambda$: (2) $R_\lambda(M) \le C_\lambda$, and (3) $\sum (-1)^\lambda R_\lambda(M) = \sum (-1)^\lambda C_\lambda$. The proof chooses $a_1 < \dots < a_k$ with exactly $i$ critical points in $M^{a_i}$ and $M^{a_k} = M$, computes $H_*(M^{a_i}, M^{a_{i-1}})$ as the coefficient group in dimension $\lambda_i$ and $0$ otherwise, by excision, and applies Lemma 5.1 to $R_\lambda$ and to $\chi$.

**Proved in Lean.** For a homology of a filtration and a chain $X_0 \le \dots \le X_n$ with $n \ge 1$: (2) $R_\lambda \le C_\lambda$ for every $\lambda$; (3) if no slab $H_{N+1}(X_k, X_{k+1})$ is non-zero, then $\sum_{i \le N} (-1)^i R_i = \sum_{i \le N} (-1)^i C_i$. In terms of critical points: let $P$ be a finite set, each $p \in P$ carrying an index $\mathrm{ind}(p)$ and a step $\mathrm{step}(p) < n$, and assume the cell hypothesis $\dim H_i(X_k, X_{k+1}) = \#\{p \in P : \mathrm{step}(p) = k,\ \mathrm{ind}(p) = i\}$ for all $k < n$ and all $i$. Then $C_i$ is the number of $p \in P$ of index $i$, and (2) reads $R_\lambda \le \#\{p \in P : \mathrm{ind}(p) = \lambda\}$; with one critical point per slab this is Milnor's count.

- `Morse.FiltrationHomology.finrank_le_morseNumber` — Morse/Chapter3/Inequalities.lean, line 596
- `Morse.FiltrationHomology.sum_neg_one_pow_finrank_eq` — Morse/Chapter3/Inequalities.lean, line 616
- `Morse.morseNumber_eq_card` — Morse/Chapter3/Inequalities.lean, line 818
- `Morse.morseNumber_eq_card_of_single` — Morse/Chapter3/Inequalities.lean, line 836
- `Morse.FiltrationHomology.weak_morse_inequality` — Morse/Chapter3/Inequalities.lean, line 846

*What differs.*
- The topological input, the slab computation of p. 29 (Theorems 3.1 and 3.2, homotopy invariance, excision and the homology of a cell modulo its boundary), is the cell hypothesis here, not a theorem; and $R_\lambda$ is a dimension in the abstract structure of V3.9. Both are supplied for singular homology in V3.32–V3.35.
- Milnor's choice of the $a_i$, one critical point per slab, needs distinct critical values; the cell hypothesis allows any number of critical points per slab. His chain starts at $\emptyset = M^{a_0}$, with $a_0$ never introduced; here $X_0$ is arbitrary and $R_i$ is the homology of the pair.

### V3.12. Lemma 5.3

*restated* · in the abstract structure of V3.9 · finite dimensions for rank–nullity

**Milnor (§5, Lemma 5.3, p. 29).** The function $S_\lambda(X, Y) = R_\lambda(X, Y) - R_{\lambda-1}(X, Y) + \dots \pm R_0(X, Y)$ is subadditive. The proof computes, for an exact sequence of vector spaces $\to A \to B \to C \to \dots \to D \to 0$, that the rank of the map $h$ into $A$ is $\operatorname{rank} A - \operatorname{rank} B + \operatorname{rank} C - \dots \pm \operatorname{rank} D$, hence $\ge 0$, and applies this to the boundary $\partial : H_{\lambda+1}(X, Y) \to H_\lambda(Y, Z)$ of the sequence of the triple $X \supset Y \supset Z$.

**Proved in Lean.** (i) If $V_{n+1} \xrightarrow{h} V_n \to \dots \to V_0 \to 0$ is exact at $V_0, \dots, V_n$ and all $V_k$ are finite-dimensional, then $\operatorname{rank} h = \dim V_n - \dim V_{n-1} + \dots \pm \dim V_0$. (ii) For the sequence of a triple $a \le b \le c$ in a homology of a filtration, $\operatorname{rank}(\partial : H_{\lambda+1}(b, c) \to H_\lambda(a, b)) = S_\lambda(a, b) - S_\lambda(a, c) + S_\lambda(b, c)$, where $S_\lambda = R_\lambda - R_{\lambda-1} + \dots \pm R_0$ of the pair; hence $S_\lambda(a, c) \le S_\lambda(a, b) + S_\lambda(b, c)$. (iii) So $S_\lambda$ is subadditive.

- `Morse.finrank_range_eq_altSum` — Morse/Chapter3/Inequalities.lean, line 287
- `Morse.LongExactSeq.altSum_le` — Morse/Chapter3/Inequalities.lean, line 419
- `Morse.FiltrationHomology.isSubadditive_altSum` — Morse/Chapter3/Inequalities.lean, line 568

*What differs.*
- Milnor's rank computation is proved as he makes it, with the finite dimensions that rank–nullity needs, and the identity for the rank of $\partial$ is a lemma of its own.

### V3.13. The strong Morse inequalities, abstractly

*narrower* · slab homology assumed (cell hypothesis) · abstract $R_\lambda$, not Betti numbers

**Milnor (§5, the Morse inequalities, p. 30).** Applying Lemma 5.1 to the subadditive function $S_\lambda$ and the spaces $\emptyset \subset M^{a_1} \subset \dots \subset M^{a_k}$ gives the Morse inequalities $(4_\lambda)$: $R_\lambda(M) - R_{\lambda-1}(M) + \dots \pm R_0(M) \le C_\lambda - C_{\lambda-1} + \dots \pm C_0$.

**Proved in Lean.** For a homology of a filtration and a chain with $n \ge 1$: $R_\lambda - R_{\lambda-1} + \dots \pm R_0 \le C_\lambda - C_{\lambda-1} + \dots \pm C_0$ for every $\lambda$; under the cell hypothesis of V3.11, with $C_i$ the number of critical points of index $i$.

- `Morse.FiltrationHomology.altSum_le_morseNumber` — Morse/Chapter3/Inequalities.lean, line 606
- `Morse.FiltrationHomology.morse_inequality` — Morse/Chapter3/Inequalities.lean, line 856

*What differs.*
- As for V3.11: the slab computation is an assumption here, and $R_\lambda$ a dimension in the abstract structure. In singular homology, with every hypothesis proved, the inequalities are V3.36.

### V3.14. Consequences of the strong inequalities

*hypotheses explicit* · only $\lambda = n + 1$ matters · $R_{\lambda+1} \ge 0$ suffices

**Milnor (§5, p. 30).** The strong inequalities contain the weak ones: the sum of $(4_\lambda)$ and $(4_{\lambda-1})$ is $(2_\lambda)$, and comparing $(4_\lambda)$ with $(4_{\lambda-1})$ for $\lambda > n$ yields the equality (3). As an illustration Milnor shows that $C_{\lambda+1} = 0$ forces $R_{\lambda+1} = 0$, and then $(4_\lambda)$, compared with $(4_{\lambda+1})$, becomes an equality.

**Proved in Lean.** Let $b$, $c$ be integer sequences with $S_\lambda(b) \le S_\lambda(c)$ for every $\lambda$, where $S_\lambda(d) = d_\lambda - d_{\lambda-1} + \dots \pm d_0$. Then $b_\lambda \le c_\lambda$ for every $\lambda$; if $c_{\lambda+1} = 0$ and $b_{\lambda+1} \ge 0$, then $S_\lambda(b) = S_\lambda(c)$; if $b \ge 0$ and $c_{N+1} = 0$, then $\sum_{i \le N} (-1)^i b_i = \sum_{i \le N} (-1)^i c_i$. For a filtration with the cell hypothesis, $R_l = 0$ if no critical point has index $l$, and, if every index is at most $N$, $\sum_{i \le N} (-1)^i R_i = \sum_{p \in P} (-1)^{\mathrm{ind}(p)}$, the left side being the whole alternating sum.

- `Morse.le_of_altSum_le` — Morse/Chapter3/Inequalities.lean, line 651
- `Morse.altSum_eq_of_altSum_le` — Morse/Chapter3/Inequalities.lean, line 664
- `Morse.sum_neg_one_pow_eq_of_altSum_le` — Morse/Chapter3/Inequalities.lean, line 676
- `Morse.FiltrationHomology.finrank_eq_zero_of_forall_ne` — Morse/Chapter3/Inequalities.lean, line 866
- `Morse.FiltrationHomology.euler_characteristic_eq` — Morse/Chapter3/Inequalities.lean, line 879

*What differs.*
- Only $\lambda = n + 1$ matters in the comparison for $\lambda > n$, and it uses $C_{n+1} = 0$ and $R_{n+1} \ge 0$; that the left side of (3) is the whole alternating sum uses $R_i = 0$ for $i > n$, which is (2).
- Milnor's intermediate step $R_{\lambda+1} = 0$ is not needed: $R_{\lambda+1} \ge 0$ suffices.

### V3.15. Corollary 5.4, and the lacunary principle

*stronger* · the lacunary principle added · $\lambda = 0$ stated apart · Betti numbers, not groups

**Milnor (§5, Corollary 5.4, p. 31).** If $C_{\lambda+1} = C_{\lambda-1} = 0$ then $R_\lambda = C_\lambda$ and $R_{\lambda+1} = R_{\lambda-1} = 0$. Milnor adds that this would also follow from Theorem 3.5, and that the corollary gives the homology groups of complex projective space (§4) without Theorem 3.5.

**Proved in Lean.** For integer sequences $b \ge 0$ and $c$ satisfying every $(4_\lambda)$, and so for the Betti and Morse numbers of a chain: if $\lambda \ge 1$ and $c_{\lambda+1} = c_{\lambda-1} = 0$, then $b_\lambda = c_\lambda$ and $b_{\lambda+1} = b_{\lambda-1} = 0$; if $c_1 = 0$, then $b_0 = c_0$ and $b_1 = 0$; and if no two consecutive $c_i$ are non-zero (for instance, if every odd $c_i$ vanishes), then $b_i = c_i$ for every $i$.

- `Morse.eq_of_altSum_le_succ` — Morse/Chapter3/Inequalities.lean, line 683
- `Morse.eq_of_altSum_le_zero` — Morse/Chapter3/Inequalities.lean, line 699
- `Morse.FiltrationHomology.finrank_eq_morseNumber_of_succ` — Morse/Chapter3/Inequalities.lean, line 736
- `Morse.FiltrationHomology.finrank_eq_morseNumber_of_zero` — Morse/Chapter3/Inequalities.lean, line 747
- `Morse.eq_of_altSum_le_of_lacunary` — Morse/Chapter3/Inequalities.lean, line 707
- `Morse.lacunary_of_odd` — Morse/Chapter3/Inequalities.lean, line 719
- `Morse.FiltrationHomology.finrank_eq_morseNumber_of_lacunary` — Morse/Chapter3/Inequalities.lean, line 758

*What differs.*
- The lacunary form, $b_i = c_i$ for every $i$ when no two consecutive $c_i$ are non-zero, is added; it is what Milnor's remark about complex projective space needs.
- For $\lambda = 0$ the condition $C_{\lambda-1} = 0$ is empty, and the case is stated separately.
- The corollary yields Betti numbers over a field, not integral homology groups; for a compact manifold it is V3.37 and V3.39, and $\mathbb CP^n$ is not constructed.

### V3.16. The numbers $C_\lambda$ of a function

*restated* · $0$ for infinitely many critical points · $C_\lambda = 0$ above $\dim M$

**Milnor (§5, p. 29).** $C_\lambda$ denotes the number of critical points of index $\lambda$ of the function on the compact manifold $M$, a function with isolated, non-degenerate critical points; the alternating sums of Theorem 5.2 end with $\pm C_n$.

**Proved in Lean.** For $f : M \to \mathbb R$ on a manifold modelled on a real normed space $E$, $C_\lambda(f)$ is the number of critical points of $f$ of index $\lambda$, set to $0$ if there are infinitely many. If $E$ is finite-dimensional and $f$ has finitely many critical points, $\sum_{p \text{ critical}} (-1)^{\mathrm{index}_p f} = \sum_{\lambda=0}^{\dim E} (-1)^\lambda C_\lambda(f)$.

- `Morse.critCount` — Morse/Chapter3/EulerChar.lean, line 106
- `Morse.finsum_neg_one_pow_indexM_eq_sum_critCount` — Morse/Chapter3/EulerChar.lean, line 111

*What differs.*
- The convention for infinitely many critical points never applies in the theorems that use $C_\lambda$: a Morse function on a compact manifold has finitely many (V1.11).
- $C_\lambda = 0$ for $\lambda > \dim M$, which is why Milnor's sums stop at $\pm C_n$ with $n = \dim M$.

### V3.17. The Poincaré–Hopf integer

*restated* · defined by vector fields, not homology · $K \ge 1$, $N$ non-empty · identified with homology in V3.38

**Milnor (§5, p. 28, and §6, Application 2).** Milnor's $\chi$ is the Euler characteristic $\sum (-1)^\lambda R_\lambda$ of singular homology over a field (p. 28). In Application 2 (pp. 36–37) he uses that the sum of the indices of any vector field on a compact $M$ is a topological invariant, citing Steenrod (§39.7), so that it equals $\chi(M)$.

**Proved in Lean.** Let $N \subseteq \mathbb R^{K+1}$ be a compact non-empty slice submanifold modelled on $\mathbb R^{d+1}$. An integer $\chi$ is an Euler number of $N$ if every smooth tangent vector field on $N$ whose zeros are finitely many distinct points has index sum $\chi$, the index being that of the Milnor project: the index at a zero of the extension $x \mapsto v(r(x)) + (x - r(x))$ of $v$ to a tubular neighbourhood, $r$ the nearest-point retraction. For $K \ge 1$ an Euler number exists: this is the Poincaré–Hopf theorem of the Milnor project, where it is the degree of the Gauss map of the boundary of a tubular neighbourhood. It is unique, and is written $\chi(N)$.

- `Morse.IsEulerNumber` — Morse/Chapter3/EulerChar.lean, line 146
- `Morse.exists_isEulerNumber` — Morse/Chapter3/EulerChar.lean, line 155

*What differs.*
- $\chi(N)$ is defined through vector fields, as the Poincaré–Hopf integer; its identification with $\sum_i (-1)^i \dim H_i(N; F)$ is V3.38.
- Uniqueness comes from Morse theory: every Euler number equals the alternating count of the critical points of any Morse function (V3.20), and $N$ carries one (V4.13).
- The ambient dimension must be at least $2$, as the Milnor project's Poincaré–Hopf theorem requires.

### V3.19. The index of the gradient field is $(-1)^\lambda$

*narrower* · embedded $N$, induced metric · proved, not asserted · $\operatorname{sgn}\det = (-1)^\lambda$

**Milnor (§6, Application 2, p. 36).** In Application 2 Milnor asserts, without proof, that $(-1)^\lambda$ is the index of the vector field $\mathrm{grad} f$ at a point where $f$ has index $\lambda$.

**Proved in Lean.** Let $N \subseteq \mathbb R^{K+1}$, $K \ge 1$, be a compact non-empty slice submanifold modelled on $\mathbb R^{d+1}$, $F : \mathbb R^{K+1} \to \mathbb R$ smooth and $f = F|N$. The tangential gradient $v(q) = P_q\nabla F(q)$, $P_q$ the orthogonal projection onto $T_qN$, is the gradient of $f$ for the metric induced from $\mathbb R^{K+1}$; its zeros are exactly the critical points of $f$, and it is a smooth tangent field. If $q$ is a non-degenerate critical point of $f$ of index $\lambda$, the derivative of $v$ at $q$ is an invertible endomorphism of $T_qN$ whose determinant has sign $(-1)^\lambda$, and the index of $v$ at $q$ is $(-1)^\lambda$. Along the way: for a non-degenerate symmetric form $H(v, w) = \langle Av, w\rangle$ on a finite-dimensional inner product space, $\operatorname{sgn}\det A = (-1)^{\mathrm{index}\,H}$.

- `Morse.tangentialGradient` — Morse/Chapter3/EulerCharGradient.lean, line 94
- `Morse.inner_tangentialGradient` — Morse/Chapter3/EulerCharGradient.lean, line 104
- `Morse.tangentialGradient_eq_zero_iff` — Morse/Chapter3/EulerCharGradient.lean, line 110
- `Morse.contMDiff_tangentialGradient` — Morse/Chapter3/EulerCharGradient.lean, line 223
- `Morse.index_hessT` — Morse/Chapter3/EulerCharGradient.lean, line 368
- `Morse.bijective_dvT_tangentialGradient` — Morse/Chapter3/EulerCharGradient.lean, line 392
- `Morse.indexN_tangentialGradient` — Morse/Chapter3/EulerCharGradient.lean, line 415
- `Morse.sgn_det_eq_neg_one_pow_index` — Morse/Chapter3/EulerCharAlgebra.lean, line 173

*What differs.*
- A metric must be chosen; here it is the one induced from $\mathbb R^{K+1}$, and $M$ is a compact submanifold of a Euclidean space, since vector fields and their indices are defined in the Milnor project only there.
- The Hessian of $F|N$ is not the restriction of the Hessian of $F$, since at a critical point $\nabla F(q)$ is normal to $N$, not zero. The proof replaces $F$ by $F \circ r$, $r$ the nearest-point retraction, which agrees with $F$ on $N$ and is critical at $q$ as a function on $\mathbb R^{K+1}$; the derivative of $v$ at $q$ is an endomorphism of $T_qN$ only because $v(q) = 0$.
- The sign of the determinant is $(-1)^{\mathrm{index}}$ by the spectral theorem and Sylvester's law of inertia, and it does not depend on the inner product.

### V3.20. Formula (3) without homology

*restated* · $\chi$ the Poincaré–Hopf integer · no homology used · $\dim N \ge 1$, $K \ge 1$

**Milnor (§5, formula (3), and §6, Application 2, p. 29).** For a compact manifold $M$ and a function with isolated, non-degenerate critical points, Lemma 5.1 applied to the additive $\chi$ gives $\chi(M) = C_0 - C_1 + C_2 - \dots \pm C_n$, recorded as (3) of Theorem 5.2. In Application 2 (pp. 36–37) Milnor deduces that on a compact $M$ the vector field $\mathrm{grad} f$ has index sum $\chi(M)$, and so, the index sum being a topological invariant, every vector field does.

**Proved in Lean.** Let $N \subseteq \mathbb R^{K+1}$, $K \ge 1$, be a compact non-empty slice submanifold of dimension $d + 1 \ge 1$. There is an integer $\chi(N)$, an Euler number of $N$ in the sense of V3.17, such that every Morse function $f$ on $N$ (smooth, with only non-degenerate critical points) satisfies $\sum_{\lambda=0}^{d+1} (-1)^\lambda C_\lambda(f) = \sum_{q \text{ critical}} (-1)^{\mathrm{index}_q f} = \chi(N)$. Consequently the alternating count is the same for all Morse functions on $N$, and every Euler number of $N$ equals the alternating count of any one Morse function. Every smooth $f : N \to \mathbb R$ is the restriction of a smooth function on $\mathbb R^{K+1}$.

- `Morse.IsEulerNumber.finsum_eq_of_ambient` — Morse/Chapter3/EulerChar.lean, line 162
- `Morse.exists_contDiff_comp_val_eq` — Morse/Chapter3/EulerChar.lean, line 203
- `Morse.IsEulerNumber.finsum_eq` — Morse/Chapter3/EulerChar.lean, line 236
- `Morse.IsEulerNumber.sum_critCount_eq` — Morse/Chapter3/EulerChar.lean, line 247
- `Morse.exists_eulerNumber_eq_sum_critCount` — Morse/Chapter3/EulerChar.lean, line 263
- `Morse.sum_critCount_eq_of_isMorseFunction` — Morse/Chapter3/EulerChar.lean, line 275
- `Morse.IsEulerNumber.eq_sum_critCount` — Morse/Chapter3/EulerChar.lean, line 286

*What differs.*
- What is verified here is the topological invariance of $\sum (-1)^\lambda C_\lambda$, by running Application 2 in the direction that needs no homology: the gradient field of $f$ (V3.19) has index sum $\sum (-1)^\lambda C_\lambda(f)$, and every tangent field has the index sum $\chi(N)$.
- Its equality with $\sum (-1)^i R_i(N)$, formula (3) as Milnor states it, is V3.35; the identification of $\chi(N)$ with the homological Euler characteristic is V3.38; abstract compact manifolds are V4.19.
- “Isolated” is redundant for non-degenerate critical points, and distinct critical values are not needed. In Application 2, “any differentiable function” must be one with only non-degenerate critical points, and the critical points of a vector field are its zeros.

### V3.22. The torus of Diagram 1 is a compact surface

*restated* · a torus of revolution, $0 < \rho < R$ · the regular zero set of a quartic

**Milnor (§1, p. 1).** Milnor takes a torus $M$ tangent to a plane $V$, drawn standing upright in Diagram 1. No equations are given, and nothing is said about why $M$ is a smooth compact surface.

**Proved in Lean.** For $0 < \rho < R$ let $T = \{x \in \mathbb R^3 : (\sqrt{x_1^2 + x_2^2} - R)^2 + x_3^2 = \rho^2\}$, the torus of revolution about the $x_3$-axis with core radius $R$ and tube radius $\rho$. $T$ is the zero set of $g(x) = (\|x\|^2 + R^2 - \rho^2)^2 - 4R^2(x_1^2 + x_2^2)$, and $dg$ does not vanish on $T$; hence $T$ is a $2$-dimensional slice submanifold of $\mathbb R^3$, compact and non-empty, and its tangent plane at $q$ is $\ker dg_q$, of dimension $2$.

- `Morse.torus` — Morse/Chapter3/TorusSurface.lean, line 75
- `Morse.Torus.poly` — Morse/Chapter3/TorusSurface.lean, line 93
- `Morse.Torus.mem_torus_iff` — Morse/Chapter3/TorusSurface.lean, line 186
- `Morse.Torus.dpoly_ne_zero` — Morse/Chapter3/TorusSurface.lean, line 202
- `Morse.Torus.isRegularValue_poly1` — Morse/Chapter3/TorusSurface.lean, line 258
- `Morse.isSliceSubmanifold_torus` — Morse/Chapter3/TorusSurface.lean, line 285
- `Morse.isCompact_torus` — Morse/Chapter3/TorusSurface.lean, line 310
- `Morse.Torus.finrank_tangentSubspace_torus` — Morse/Chapter3/TorusSurface.lean, line 360

*What differs.*
- The surface is fixed as the torus of revolution. $\rho < R$ makes it a smooth ring torus, and also makes the four critical values of V3.23 distinct, which cases (3) and (4) of p. 1 presuppose.

### V3.23. The height function: four critical points, of indices 0, 1, 1, 2

*restated* · indices proved, normal forms not restated · the upright torus · exactly four critical points

**Milnor (§1, p. 3).** The points $p$, $q$, $r$, $s$ at which the homotopy type of $M^a$ changes are the critical points of $f$: in any coordinates $(x, y)$ near them both partial derivatives of $f$ vanish, and one can choose coordinates with $f = x^2 + y^2$ at $p$, $f = \text{const} - x^2 - y^2$ at $s$, and $f = \text{const} + x^2 - y^2$ at $q$ and $r$. The number of minus signs is the dimension of the cell attached in passing the point.

**Proved in Lean.** Let $f = x_1 + R + \rho$ on $T$, the height above the plane $\{x_1 = -(R + \rho)\}$, which touches $T$ at $p = (-(R + \rho), 0, 0)$; the axis of revolution is parallel to the plane, so the torus stands upright. The critical points of $f$ are exactly $p$, $q = (-(R - \rho), 0, 0)$, $r = (R - \rho, 0, 0)$ and $s = (R + \rho, 0, 0)$, with critical values $0$, $2\rho$, $2R$, $2R + 2\rho$. All four are non-degenerate, of indices $0, 1, 1, 2$; $f$ is a Morse function on $T$, with $C_0 = 1$, $C_1 = 2$, $C_2 = 1$ and $C_\lambda = 0$ for $\lambda \ge 3$.

- `Morse.Torus.height` — Morse/Chapter3/Torus.lean, line 212
- `Morse.Torus.isCriticalPointM_height_iff` — Morse/Chapter3/Torus.lean, line 311
- `Morse.Torus.criticalValues_height` — Morse/Chapter3/Torus.lean, line 528
- `Morse.Torus.pointP_spec` — Morse/Chapter3/Torus.lean, line 468
- `Morse.Torus.pointQ_spec` — Morse/Chapter3/Torus.lean, line 480
- `Morse.Torus.pointR_spec` — Morse/Chapter3/Torus.lean, line 492
- `Morse.Torus.pointS_spec` — Morse/Chapter3/Torus.lean, line 505
- `Morse.Torus.isMorseFunction_height` — Morse/Chapter3/Torus.lean, line 517
- `Morse.Torus.critCount_height` — Morse/Chapter3/Torus.lean, line 550
- `Morse.hessian_comp_sliceParam_of_fderiv_eq_zero` — Morse/Chapter3/Torus.lean, line 121

*What differs.*
- Milnor asserts the critical points and the normal forms without verification. The formal statement proves that there are exactly four critical points, non-degenerate, with the indices the normal forms imply; the normal forms follow from the lemma of Morse (V1.8) and are not restated.
- The upright position is essential: lying flat, the height function has two circles of degenerate critical points.
- The proof is Lagrange's rule. At a point $(a, 0, 0)$ of $T$, $dg = \kappa\,dx_1$ with $\kappa \ne 0$, so $G = f - \kappa^{-1}g$ agrees with $f$ on $T$ and is critical at the point as a function on $\mathbb R^3$; the Hessian of $f|T$ is then $d^2G$ on the tangent plane, a diagonal form whose entries are, up to sign, the principal curvatures.

### V3.24. Milnor's cases (1) and (5), and Theorem 3.1 on the torus

*narrower* · (2)–(4): only Theorem 3.1 · (1) read as $a < 0 = f(p)$ · (5) also for $a = f(s)$

**Milnor (§1, p. 1).** (1) If $a < 0 < f(p)$, as the scan prints it, then $M^a$ is vacuous; (5) if $f(s) < a$, then $M^a$ is the full torus; and for $a$ between consecutive critical values, cases (2)–(4), $M^a$ is homeomorphic to a 2-cell, to a cylinder, and to a compact genus-one surface bounded by a circle.

**Proved in Lean.** $T^a = \emptyset$ for $a < 0$, and $T^a = T$ for $a \ge 2R + 2\rho = f(s)$. If $a \le b$ and $[a, b]$ contains none of the critical values $0$, $2\rho$, $2R$, $2R + 2\rho$, then a smooth diffeomorphism of $T$ carries $T^a$ onto $T^b$, $T^a$ is a strong deformation retract of $T^b$, and the inclusion $T^a \to T^b$ is a homotopy equivalence; in particular the $T^a$ with $a$ in any one of $(0, 2\rho)$, $(2\rho, 2R)$, $(2R, 2R + 2\rho)$ are diffeomorphic to one another.

- `Morse.Torus.sublevel_height_eq_empty` — Morse/Chapter3/Torus.lean, line 278
- `Morse.Torus.sublevel_height_eq_univ` — Morse/Chapter3/Torus.lean, line 285
- `Morse.theorem_3_1_torus` — Morse/Chapter3/Torus.lean, line 686

*What differs.*
- Of cases (2)–(4) only what Theorem 3.1 gives is verified; the homeomorphism types, a disk, a cylinder and a torus with a disk removed, are not, and would need explicit homeomorphisms.
- $f(p) = 0$ because the plane touches $M$ at $p$, so the hypothesis of (1) must be read as $a < 0 = f(p)$; and (5) holds for $a = f(s)$ as well.

### V3.25. The Euler number of the torus is 0

*not in the book* · two independent proofs · every Morse function on $T$

**Milnor (§1, p. 2).** The book computes no Euler characteristic for the torus. On p. 2 Milnor describes the passage from (1) to (5) as attaching a 0-cell, a 1-cell, another 1-cell and a 2-cell, which gives the count $1 - 2 + 1$.

**Proved in Lean.** $0$ is an Euler number of $T$ in the sense of V3.17, and every Euler number of $T$ is $0$: by V3.20 from $C_0 - C_1 + C_2 = 1 - 2 + 1$, and independently of Morse theory, because the rotation field $(-x_2, x_1, 0)$ is a smooth tangent field on $T$ without zeros. Hence every Morse function on $T$ has $C_0 - C_1 + C_2 = 0$.

- `Morse.isEulerNumber_torus` — Morse/Chapter3/Torus.lean, line 618
- `Morse.IsEulerNumber.eq_torus` — Morse/Chapter3/Torus.lean, line 629
- `Morse.sum_critCount_torus` — Morse/Chapter3/Torus.lean, line 637
- `Morse.IsEulerNumber.eq_torus_of_rotation` — Morse/Chapter3/Torus.lean, line 652

*What differs.*
- A check of V3.20 on the book's own example: the count from the height function agrees with the index sum of a nowhere-vanishing rotation field. By V3.38 the value is also the homological Euler characteristic of $T$; the Betti numbers $1, 2, 1$ themselves are not derived.

### V3.26. Relative singular homology and the exact sequence of a pair

*not in the book* · quoted by Milnor, built here · Mathlib had no relative homology · homotopy invariance for pairs

**Milnor (§5, pp. 28–29).** Milnor quotes the homology of pairs with coefficients in a field, and its exact sequences, as standard (p. 28); on p. 29 he replaces a pair by a homotopy equivalent one without comment.

**Proved in Lean.** Coefficients are an object $R$ of an abelian category with coproducts, for instance a field or any commutative ring; pairs $(X, A)$ are embeddings $A \hookrightarrow X$. The relative chain complex $C(X, A)$ is the cokernel of the chain map $C(A) \to C(X)$ of singular chains, which is injective, so that $0 \to C(A) \to C(X) \to C(X, A) \to 0$ is exact; $H_n(X, A)$ is its homology, and both are functorial in maps of pairs. The sequence $\cdots \to H_{n+1}(X, A) \to H_n(A) \to H_n(X) \to H_n(X, A) \to H_{n-1}(A) \to \cdots \to H_0(X) \to H_0(X, A) \to 0$ is exact at every place, and its boundary is natural. $H_n(X, \emptyset) \cong H_n(X)$ naturally, and $H_n(X, X) = 0$. A map of pairs inducing isomorphisms in the homology of both spaces induces isomorphisms in relative homology; maps of pairs homotopic through maps of pairs induce the same maps. If $A \subseteq B \subseteq X$ and $B$ is a strong deformation retract of $X$, then $H_n(B, A) \to H_n(X, A)$ is an isomorphism and $H_n(X, B) = 0$. With these data singular homology is a homotopy-invariant homology pretheory in the sense of Mathlib's formulation of the Eilenberg–Steenrod axioms.

- `Morse.Homology.relChains` — Morse/Homology/Relative.lean, line 165
- `Morse.Homology.relHomology` — Morse/Homology/Relative.lean, line 207
- `Morse.Homology.relδ` — Morse/Homology/Relative.lean, line 224
- `Morse.Homology.relHomology_exact₂` — Morse/Homology/Relative.lean, line 247
- `Morse.Homology.epi_homologyMap_relπ_zero` — Morse/Homology/Relative.lean, line 265
- `Morse.Homology.relδ_naturality` — Morse/Homology/Relative.lean, line 271
- `Morse.Homology.relHomologyInclIso` — Morse/Homology/Relative.lean, line 355
- `Morse.Homology.isZero_relHomology_diag` — Morse/Homology/Relative.lean, line 381
- `Morse.Homology.relHomology_map_eq_of_homotopy` — Morse/Homology/RelativeHomotopy.lean, line 227
- `Morse.Homology.isIso_relHomology_map_of_isStrongDeformationRetract` — Morse/Homology/RelativeRetract.lean, line 49
- `Morse.Homology.singularHomologyPretheory` — Morse/Homology/Pretheory.lean, line 42

*What differs.*
- Mathlib has the singular chain complex, absolute singular homology and its homotopy invariance, but no relative homology; everything Milnor quotes about pairs is built here.
- The first equality of p. 29 needs homotopy equivalences of pairs; what is proved and used is the version for strong deformation retracts. Homotopy invariance for pairs comes from the absolute one, through the cylinder $(X \times I, A \times I)$ and the five lemma.

### V3.27. The exact sequence of a triple

*not in the book* · quoted by Milnor, built here · the third isomorphism theorem

**Milnor (§5, pp. 28–30).** Milnor quotes the homology exact sequence of a triple $X \supset Y \supset Z$: its portion $H_\lambda(Y, Z) \to H_\lambda(X, Z) \to H_\lambda(X, Y)$ for subadditivity (p. 28), its final $\to 0$ (p. 29), and its boundary $H_{\lambda+1}(X, Y) \to H_\lambda(Y, Z)$ in Lemma 5.3 (p. 30).

**Proved in Lean.** For a triple $Z \subseteq Y \subseteq X$ (two composable embeddings, for instance subsets $A \subseteq B \subseteq D$ of a space), the inclusions of pairs give a short exact sequence $0 \to C(Y, Z) \to C(X, Z) \to C(X, Y) \to 0$, hence the sequence $\cdots \to H_{n+1}(X, Y) \to H_n(Y, Z) \to H_n(X, Z) \to H_n(X, Y) \to H_{n-1}(Y, Z) \to \cdots \to H_0(X, Z) \to H_0(X, Y) \to 0$, exact at every place, whose boundary is the boundary of the pair $(X, Y)$ followed by $H_n(Y) \to H_n(Y, Z)$.

- `Morse.Homology.TopTriple` — Morse/Homology/Triple.lean, line 83
- `Morse.Homology.TopTriple.ofSubsets` — Morse/Homology/Triple.lean, line 143
- `Morse.Homology.cokernel_comp_shortExact` — Morse/Homology/Triple.lean, line 69
- `Morse.Homology.TopTriple.δ` — Morse/Homology/Triple.lean, line 215
- `Morse.Homology.TopTriple.exact₂` — Morse/Homology/Triple.lean, line 237
- `Morse.Homology.TopTriple.epi_map₂_zero` — Morse/Homology/Triple.lean, line 245
- `Morse.Homology.TopTriple.δ_eq` — Morse/Homology/Triple.lean, line 266

*What differs.*
- The short exact sequence of relative chains is the third isomorphism theorem $(C(X)/C(Z))/(C(Y)/C(Z)) \cong C(X)/C(Y)$, proved in any abelian category; the sequence of the triple is the long exact sequence of that short exact sequence of complexes.

### V3.28. Excision

*not in the book* · quoted by Milnor, proved here · barycentric subdivision · not literally the step of p. 29

**Milnor (§5, p. 29).** In the computation of $H_*(M^{a_i}, M^{a_{i-1}})$ one equality is justified simply by excision, which Milnor quotes.

**Proved in Lean.** (i) If the interiors of a family of subsets of a space $X$ cover $X$, the inclusion of the chains made of simplices each lying in one member of the family into all singular chains is a chain homotopy equivalence, for any coefficients. With coefficients in a commutative ring: (ii) if $A, B \subseteq X$ have interiors covering $X$, then $(B, A \cap B) \to (X, A)$ induces isomorphisms $H_n(B, A \cap B) \cong H_n(X, A)$ for all $n$; (iii) if $Z \subseteq A \subseteq X$ and the closure of $Z$ lies in the interior of $A$, then $(X \setminus Z, A \setminus Z) \to (X, A)$ induces isomorphisms in all degrees.

- `Morse.Homology.smallChainsHomotopyEquiv` — Morse/Homology/SmallChains.lean, line 470
- `Morse.Homology.excision_of_union` — Morse/Homology/Excision.lean, line 405
- `Morse.Homology.excision` — Morse/Homology/Excision.lean, line 415
- `Morse.Homology.excision_of_closure_subset_interior` — Morse/Homology/Excision.lean, line 436

*What differs.*
- Proved as in Hatcher (Proposition 2.21 and Theorem 2.20), by barycentric subdivision with the diameter bound $(n/(n+1))^k$.
- The step Milnor calls excision is not literally an instance of (iii): the closure of the set to be excised does not lie in the interior of $M^{a_{i-1}}$. How the step is made is V3.31.

### V3.30. The homology of disks, spheres and cells

*not in the book* · quoted by Milnor, computed here · embedded cells and spheres too

**Milnor (§5, p. 29).** Milnor quotes that $H_*(e^\lambda, \dot e^\lambda)$ is the coefficient group in dimension $\lambda$ and $0$ otherwise.

**Proved in Lean.** Coefficients in a commutative ring $R$; $D^n$ and $S^{n-1}$ are the closed unit ball and unit sphere of $\mathbb R^n$, with $S^{-1} = \emptyset$. $H_i(D^n, S^{n-1}) \cong R$ for $i = n$ and $H_i(D^n, S^{n-1}) = 0$ for $i \ne n$. For $n \ge 1$, $H_0(S^n) \cong R$, $H_n(S^n) \cong R$ and $H_i(S^n) = 0$ for $i \ne 0, n$; $H_0(S^0) \cong R \oplus R$. Over a field, $\dim H_i(D^n, S^{n-1}) = [i = n]$ and $\dim H_i(S^n) = [i = 0] + [i = n]$. More generally, if $E$ is Hausdorff and $\chi : \mathbb R^k \to E$ is continuous and injective on $D^k$, the pair $(\chi(D^k), \chi(S^{k-1}))$ has the homology of $(D^k, S^{k-1})$, and an image of $S^n$ under a map continuous and injective on it has the homology of $S^n$.

- `Morse.Homology.relHomologyDiskPairIso` — Morse/Homology/Spheres.lean, line 599
- `Morse.Homology.isZero_relHomology_diskPair` — Morse/Homology/Spheres.lean, line 605
- `Morse.Homology.finrank_relHomology_diskPair` — Morse/Homology/Spheres.lean, line 611
- `Morse.Homology.sphereHomologyTopIso` — Morse/Homology/Spheres.lean, line 629
- `Morse.Homology.isZero_sphereHomology` — Morse/Homology/Spheres.lean, line 639
- `Morse.Homology.finrank_sphereHomology` — Morse/Homology/Spheres.lean, line 645
- `Morse.Homology.cellPairIso` — Morse/Homology/Spheres.lean, line 466
- `Morse.Homology.finrank_homology_imageSphere` — Morse/Homology/Spheres.lean, line 555

*What differs.*
- Computed by induction on the dimension, through the boundary of the triple $\{q\} \subseteq \chi(S^k) \subseteq \chi(D^{k+1})$, $q$ a point onto which the cell contracts, and excision for the upper hemisphere of $S^k$ attached to the lower one.

### V3.31. Attaching cells to a closed set: the step “by excision”

*stronger* · several disjoint cells at once · any commutative ring · not literally excision

**Milnor (§5, p. 29).** For $M^{a_i}$, which has the homotopy type of $M^{a_{i-1}} \cup e^{\lambda_i}$, Milnor writes $H_*(M^{a_{i-1}} \cup e^{\lambda_i}, M^{a_{i-1}}) = H_*(e^{\lambda_i}, \dot e^{\lambda_i})$, by excision, which is the coefficient group in dimension $\lambda_i$ and $0$ otherwise.

**Proved in Lean.** Let $E$ be a Hausdorff space, $Y \subseteq X \subseteq E$ with $Y$ closed, and $\chi_j : \mathbb R^{k_j} \to E$, $j = 1, \dots, m$, maps continuous and injective on the closed unit balls $D^{k_j}$, whose cells $e_j = \chi_j(D^{k_j})$ are pairwise disjoint, such that $\chi_j(z) \in Y$ exactly when $\|z\| = 1$, and $X = Y \cup e_1 \cup \dots \cup e_m$. Coefficients in a commutative ring $R$. For one cell of dimension $k$, the inclusion $(e_1, \chi_1(S^{k-1})) \to (X, Y)$ and the characteristic map $(D^k, S^{k-1}) \to (X, Y)$ induce isomorphisms in all degrees: $H_k(X, Y) \cong R$ and $H_i(X, Y) = 0$ for $i \ne k$. For several cells, $H_i(X, Y) \cong R^{c_i}$, $c_i$ the number of cells of dimension $i$; over a field $\dim H_i(X, Y) = c_i$.

- `Morse.Homology.isIso_relHomology_map_cellPair` — Morse/Homology/CellExcision.lean, line 366
- `Morse.Homology.relHomology_cellAttach_iso` — Morse/Homology/CellAttach.lean, line 126
- `Morse.Homology.relHomologyCellAttachTopIso` — Morse/Homology/CellAttach.lean, line 149
- `Morse.Homology.isZero_relHomology_cellAttach` — Morse/Homology/CellAttach.lean, line 157
- `Morse.Homology.finrank_relHomology_cellsAttach` — Morse/Homology/CellAttach.lean, line 373
- `Morse.Homology.relHomology_cellsAttach_iso` — Morse/Homology/CellAttach.lean, line 506

*What differs.*
- The step is not literally excision: the closure of the set to be excised is not inside the interior of $M^{a_{i-1}}$. One first deforms $X$ minus the centre of the cell onto $Y$, pushing the punctured cell radially onto its boundary, and then excises; $Y$ must be closed.
- Any number of disjoint cells is allowed, as Remark 3.3 needs: with several cells on one level the exact sequence of a triple gives only an inequality of dimensions, and additivity uses the disjointness of the cells. This is the exposition's Lemma E.

### V3.32. The Morse inequalities for any filtration of a space

*restated* · any filtration of any space · finiteness of the total a consequence

**Milnor (§5, pp. 28–30).** Milnor applies Lemma 5.1 to $R_\lambda$, to $\chi$ and to $S_\lambda$ on the chain $\emptyset = M^{a_0} \subset M^{a_1} \subset \dots \subset M^{a_k} = M$, which gives Theorem 5.2 and the inequalities $(4_\lambda)$.

**Proved in Lean.** Let $X_0 \subseteq X_1 \subseteq \cdots$ be subsets of a space and $\Bbbk$ a field. With $H_i(a, b) = H_i(X_b, X_a; \Bbbk)$ for $a \le b$ and the exact sequences of triples of V3.27, singular homology is a homology of a filtration in the sense of V3.9, provided every step $(X_{k+1}, X_k)$ has finite-dimensional homology. Consequently, for $n \ge 1$, if the steps $k < n$ have finite-dimensional homology, so has $(X_n, X_0)$, and with $b_i = \dim H_i(X_n, X_0; \Bbbk)$ and $C_i = \sum_{k < n} \dim H_i(X_{k+1}, X_k; \Bbbk)$: $b_l \le C_l$; $b_l - b_{l-1} + \dots \pm b_0 \le C_l - C_{l-1} + \dots \pm C_0$ for every $l$; and $\sum_{i \le N} (-1)^i b_i = \sum_{i \le N} (-1)^i C_i$ if no step has homology in degree $N + 1$. Under the cell hypothesis of V3.11, $C_i$ is the number of critical points of index $i$, and the alternating sum is $\sum_{p \in P} (-1)^{\mathrm{ind}\,p}$ when every index is at most $N$.

- `Morse.Homology.TopTriple.longExactSeq` — Morse/Homology/TripleFiltration.lean, line 73
- `Morse.Homology.subsetHomology` — Morse/Homology/TripleFiltration.lean, line 103
- `Morse.Homology.filtrationHomology` — Morse/Homology/TripleFiltration.lean, line 161
- `Morse.Homology.finiteDimensional_subsetHomology_of_steps` — Morse/Homology/TripleFiltration.lean, line 239
- `Morse.Homology.singular_weak_morse_inequality` — Morse/Homology/TripleFiltration.lean, line 247
- `Morse.Homology.singular_morse_inequality` — Morse/Homology/TripleFiltration.lean, line 257
- `Morse.Homology.singular_euler_characteristic` — Morse/Homology/TripleFiltration.lean, line 269
- `Morse.Homology.singular_morse_inequality_of_cells` — Morse/Homology/TripleFiltration.lean, line 309

*What differs.*
- This is the instance of the abstract structure of V3.9 that V3.10–V3.15 lacked. It applies to any filtration of any space whose steps have finite-dimensional homology, not only to sublevel sets, and the finiteness of the homology of $(X_n, X_0)$ is a consequence, not an assumption.

### V3.33. Betti numbers, and the homology of a slab

*restated* · pairs need strong deformation retracts · the bottom moves by a triple

**Milnor (§5, pp. 28–29).** $R_\lambda(X, Y)$ is the rank over $F$ of $H_\lambda(X, Y; F)$ (p. 28). On p. 29, $H_*(M^{a_i}, M^{a_{i-1}}) = H_*(M^{a_{i-1}} \cup e^{\lambda_i}, M^{a_{i-1}})$, the pair being replaced, by Theorems 3.1 and 3.2, by one in which $M^{a_i}$ becomes $M^{a_{i-1}}$ with a cell attached.

**Proved in Lean.** For a space $X$, $b_i(X) = \dim_\Bbbk H_i(X; \Bbbk)$, Mathlib's singular homology, is Milnor's $R_i(X)$; it is $0$ by convention if $H_i(X; \Bbbk)$ is infinite-dimensional, which never happens for the spaces below. Homeomorphic spaces have the same Betti numbers. If $A \subseteq B \subseteq D$ and $A$ is a strong deformation retract of $B$, then $H_i(D, A) \cong H_i(D, B)$, by the sequence of the triple, in which $H_*(B, A) = 0$. The slab lemma: let $A \subseteq B \subseteq X' \subseteq X$ be subsets of a Hausdorff space, $B$ closed, and $e_1, \dots, e_m$ pairwise disjoint cells attached to $B$ as in V3.31, with $B \cup e_1 \cup \dots \cup e_m \subseteq X'$; if $A$ is a strong deformation retract of $B$, $B \cup e_1 \cup \dots \cup e_m$ one of $X'$, and $X'$ one of $X$, then $H_i(X, A; \Bbbk)$ is finite-dimensional, of dimension the number of cells of dimension $i$.

- `Morse.Homology.spaceHomology` — Morse/Homology/MorseHomologyBasic.lean, line 243
- `Morse.Homology.bettiNumber` — Morse/Homology/MorseHomologyBasic.lean, line 250
- `Morse.Homology.bettiNumber_eq_of_homeomorph` — Morse/Homology/MorseHomologyBasic.lean, line 262
- `Morse.Homology.finrank_subsetHomology_eq_bettiNumber` — Morse/Homology/MorseHomologyBasic.lean, line 276
- `Morse.Homology.subsetHomologyEquivOfIsSDRBottom` — Morse/Homology/MorseHomologyBasic.lean, line 333
- `Morse.Homology.CellAttachHomology` — Morse/Homology/MorseHomologyBasic.lean, line 301
- `Morse.Homology.finrank_subsetHomology_of_cells` — Morse/Homology/MorseHomologyBasic.lean, line 346

*What differs.*
- The first equality of p. 29 is about pairs, not spaces: the top of a pair moves along deformations that fix the bottom, but the bottom moves only through the sequence of a triple. This needs strong deformation retracts, whereas Milnor states Theorem 3.2 only up to homotopy type.
- With $A = M^{a_{i-1}}$, $B = M^{c-\epsilon}$, $X' = M^{c+\epsilon}$, $X = M^{a_i}$ and $c$ the critical value, this is the slab computation; V3.34 supplies the hypotheses.

### V3.34. The Morse filtration of a compact submanifold

*narrower* · compact $N \subseteq V$, $f = F|N$ · one critical value per slab · finiteness of $H_*$ proved

**Milnor (§5, p. 29).** For a compact $M$ and a differentiable $f$ with isolated, non-degenerate critical points, Milnor takes $a_1 < \dots < a_k$ with exactly $i$ critical points in $M^{a_i}$ and $M^{a_k} = M$, and finds $H_*(M^{a_i}, M^{a_{i-1}})$ to be the coefficient group in dimension $\lambda_i$, the index of the $i$-th critical point, and $0$ in every other dimension.

**Proved in Lean.** Let $N$ be a compact slice submanifold of a finite-dimensional real normed space $V$, modelled on a finite-dimensional space, and $F : V \to \mathbb R$ smooth such that every critical point of $f = F|N$ is non-degenerate. (i) If $a' \le a$ are not critical values and all critical values in $(a', a)$ are equal, then $H_i(N^a, N^{a'}; \Bbbk)$ is finite-dimensional, of dimension the number of critical points of index $i$ in $f^{-1}(a', a)$. (ii) There are $n \ge 1$ and non-critical values $a_0 \le a_1 \le \dots$ with $N^{a_0} = \emptyset$, $N^{a_n} = N$ and at most one critical value in each $(a_k, a_{k+1})$; by (i) each step $(N^{a_{k+1}}, N^{a_k})$ has finite-dimensional homology over every field. (iii) Hence $H_i(N; \Bbbk)$ is finite-dimensional for every $i$. These statements hold for every space homeomorphic to $N$, homology being carried along the homeomorphism.

- `Morse.exists_separating_seq` — Morse/Homology/MorseHomologyBasic.lean, line 95
- `Morse.isCriticalPointM_of_forall_ge` — Morse/Homology/MorseHomologyBasic.lean, line 180
- `Morse.Homology.sublevel_step_critical` — Morse/Homology/MorseHomology.lean, line 119
- `Morse.Homology.sublevel_step` — Morse/Homology/MorseHomology.lean, line 211
- `Morse.Homology.exists_morse_filtration` — Morse/Homology/MorseHomology.lean, line 274
- `Morse.Homology.exists_cells_filtration` — Morse/Homology/MorseHomology.lean, line 342
- `Morse.Homology.critCount_eq_card` — Morse/Homology/MorseHomology.lean, line 390
- `Morse.Homology.finiteDimensional_spaceHomology` — Morse/Homology/MorseHomology.lean, line 404

*What differs.*
- Milnor's choice of the $a_i$ needs distinct critical values; here each slab contains at most one critical value, with any number of critical points on it, handled by Remark 3.3 (V2.9).
- $M^{a_0} = \emptyset$ and $M^{a_k} = M$ rest on the minimum and the maximum of $f$ being critical values; the finiteness of $R_\lambda(M)$ is a consequence, not an assumption; and “isolated” is redundant.
- The setting is a compact submanifold of a Euclidean space with $f$ the restriction of an ambient function; abstract compact manifolds are reached in V3.39.

### V3.35. Theorem 5.2 in singular homology

*narrower* · compact $N \subseteq V$, $f = F|N$ · every input of p. 29 proved · $H_i = 0$ above $\dim N$

**Milnor (§5, Theorem 5.2, p. 29).** (The weak Morse inequalities.) On a compact manifold $M$, with $C_\lambda$ the number of critical points of index $\lambda$ and Betti numbers taken over a field $F$: $R_\lambda(M) \le C_\lambda$ and $\sum (-1)^\lambda R_\lambda(M) = \sum (-1)^\lambda C_\lambda$.

**Proved in Lean.** In the setting of V3.34, with $n = \dim N$, $b_i = \dim H_i(N; \Bbbk)$ for any field $\Bbbk$, and $C_\lambda = C_\lambda(f)$: (2) $b_\lambda \le C_\lambda$ for every $\lambda$; (3) $\sum_{i=0}^n (-1)^i b_i = \sum_{\lambda=0}^n (-1)^\lambda C_\lambda$; and $H_i(N; \Bbbk) = 0$ for $i > n$, so that the left side of (3) is the whole alternating sum. The same holds for every space homeomorphic to $N$.

- `Morse.Homology.bettiNumber_le_critCount` — Morse/Homology/MorseHomology.lean, line 416
- `Morse.Homology.bettiNumber_le_critCount'` — Morse/Homology/MorseHomology.lean, line 578
- `Morse.Homology.sum_bettiNumber_eq_sum_critCount` — Morse/Homology/MorseHomology.lean, line 447
- `Morse.Homology.sum_bettiNumber_eq_sum_critCount'` — Morse/Homology/MorseHomology.lean, line 598
- `Morse.Homology.bettiNumber_eq_zero_of_finrank_lt` — Morse/Homology/MorseHomology.lean, line 473
- `Morse.Homology.subsingleton_spaceHomology_of_finrank_lt` — Morse/Homology/MorseHomology.lean, line 490

*What differs.*
- $M$ is a compact submanifold of a Euclidean space and $f$ the restriction of a smooth function on the ambient space; abstract compact manifolds are V3.39.
- Every topological input of p. 29 is proved: the homology of pairs and triples (V3.26, V3.27), the cell computation (V3.31) and the slab homology (V3.34). $R_\lambda(M) = 0$ for $\lambda > n$, which makes $\sum (-1)^\lambda R_\lambda(M)$ a finite sum, follows from (2).

### V3.36. The strong Morse inequalities in singular homology

*narrower* · compact $N \subseteq V$, $f = F|N$ · one critical value per slab

**Milnor (§5, the Morse inequalities, p. 30).** For every $\lambda$, $R_\lambda(M) - R_{\lambda-1}(M) + \dots \pm R_0(M) \le C_\lambda - C_{\lambda-1} + \dots \pm C_0$, from Lemma 5.1 applied to the subadditive $S_\lambda$ on $\emptyset \subset M^{a_1} \subset \dots \subset M^{a_k}$.

**Proved in Lean.** In the setting of V3.35, over every field: $b_\lambda - b_{\lambda-1} + \dots \pm b_0 \le C_\lambda - C_{\lambda-1} + \dots \pm C_0$ for every $\lambda$.

- `Morse.Homology.altSum_bettiNumber_le` — Morse/Homology/MorseHomology.lean, line 430
- `Morse.Homology.altSum_bettiNumber_le'` — Morse/Homology/MorseHomology.lean, line 587

*What differs.*
- As for V3.35: proved for compact submanifolds of a Euclidean space, with every topological input proved; abstract compact manifolds are V3.39.

### V3.37. Corollary 5.4 and the lacunary principle in singular homology

*narrower* · compact $N \subseteq V$, $f = F|N$ · the lacunary principle added · Betti numbers, not groups

**Milnor (§5, Corollary 5.4, p. 31).** If $C_{\lambda+1} = C_{\lambda-1} = 0$ then $R_\lambda = C_\lambda$ and $R_{\lambda+1} = R_{\lambda-1} = 0$. Milnor notes that the corollary finds the homology groups of complex projective space (§4) without Theorem 3.5.

**Proved in Lean.** In the setting of V3.35, over every field: if $\lambda \ge 1$ and $C_{\lambda+1} = C_{\lambda-1} = 0$, then $b_\lambda = C_\lambda$ and $b_{\lambda+1} = b_{\lambda-1} = 0$; if $C_1 = 0$, then $b_0 = C_0$ and $b_1 = 0$; and if no two consecutive $C_i$ are non-zero, then $b_i = C_i$ for every $i$.

- `Morse.Homology.bettiNumber_eq_critCount_of_succ` — Morse/Homology/MorseHomology.lean, line 500
- `Morse.Homology.bettiNumber_eq_critCount_of_zero` — Morse/Homology/MorseHomology.lean, line 517
- `Morse.Homology.bettiNumber_eq_critCount_of_lacunary` — Morse/Homology/MorseHomology.lean, line 532

*What differs.*
- Proved for compact submanifolds of a Euclidean space; abstract compact manifolds are V3.39.
- The lacunary form is added. Integral homology groups are not derived and $\mathbb CP^n$ is not constructed, so Milnor's application is not reached.

### V3.38. The Euler characteristic, three ways

*restated* · three descriptions of $\chi$ identified · independent of the field

**Milnor (§5, p. 28, and formula (3)).** Milnor's Euler characteristic is $\chi(X, Y) = \sum (-1)^\lambda R_\lambda(X, Y)$ (p. 28); formula (3) gives $\chi(M) = C_0 - C_1 + \dots \pm C_n$ (p. 29), and in Application 2 (pp. 36–37) $\chi(M)$ is the index sum of every vector field. That $\chi(M)$ is the same over every field is never stated.

**Proved in Lean.** (i) Let $N \subseteq \mathbb R^{K+1}$, $K \ge 1$, be a compact non-empty slice submanifold of dimension $d + 1 \ge 1$. Every Euler number $\chi$ of $N$ (V3.17, the Poincaré–Hopf integer) satisfies $\chi = \sum_{i=0}^{d+1} (-1)^i \dim H_i(N; \Bbbk)$ for every field $\Bbbk$; the same holds for every space homeomorphic to $N$. (ii) For a compact Hausdorff smooth manifold $M$ without boundary, modelled on a finite-dimensional real normed space, the integer $\chi(M)$ of V4.18 ($\sum_\lambda (-1)^\lambda C_\lambda$ for any Morse function) equals $\sum_{i=0}^{\dim M} (-1)^i \dim H_i(M; \Bbbk)$ for every field $\Bbbk$. In particular this alternating sum does not depend on the field.

- `Morse.IsEulerNumber.eq_sum_bettiNumber` — Morse/Homology/MorseHomologyManifold.lean, line 143
- `Morse.Homology.eulerNumberM_eq_sum_bettiNumber` — Morse/Homology/MorseHomologyManifold.lean, line 208

*What differs.*
- The three descriptions of $\chi$, by homology, by critical points and by index sums of vector fields, are identified, which closes the circle left open in V3.20 and V4.19.
- Passing from $M$ to an embedded copy uses the invariance of homology under homeomorphisms, which the book never states. The proof applies (3) of V3.35 to a Morse function $L_p = \|\cdot - p\|^2$ (Theorem 6.6, V4.12) and compares with V3.20, resp. V4.19, through a Whitney embedding.

### V3.39. The Morse inequalities on a compact manifold

*hypotheses explicit* · Hausdorff assumed · through a Whitney embedding · the lacunary principle added

**Milnor (§5, Theorem 5.2 and Corollary 5.4, p. 29).** §5 is stated for a compact manifold $M$ and a function with isolated, non-degenerate critical points: $R_\lambda(M) \le C_\lambda$, $\sum (-1)^\lambda R_\lambda(M) = \sum (-1)^\lambda C_\lambda$, the inequalities $(4_\lambda)$ and Corollary 5.4, for Betti numbers over a field.

**Proved in Lean.** The homology over any field of a compact $k$-dimensional slice submanifold of $\mathbb R^n$, or of a space homeomorphic to one, is finite-dimensional and vanishes above degree $k$. Let $M$ be a compact Hausdorff smooth manifold without boundary, modelled on a finite-dimensional real normed space, of dimension $n$. Then $H_i(M; \Bbbk)$ is finite-dimensional and is $0$ for $i > n$, and for every Morse function $g$ on $M$, with $b_i = \dim H_i(M; \Bbbk)$ and $C_\lambda = C_\lambda(g)$: $b_\lambda \le C_\lambda$; $(4_\lambda)$; $\sum_{i \le n} (-1)^i b_i = \sum_{\lambda \le n} (-1)^\lambda C_\lambda$; and $b_i = C_i$ for every $i$ if no two consecutive $C_i$ are non-zero.

- `Morse.Homology.finiteDimensional_spaceHomology_of_isCompact` — Morse/Homology/MorseHomologyManifold.lean, line 111
- `Morse.Homology.finiteDimensional_spaceHomology_of_compactSpace` — Morse/Homology/MorseHomologyManifold.lean, line 190
- `Morse.Homology.bettiNumber_eq_zero_of_compactSpace` — Morse/Homology/MorseHomologyManifold.lean, line 199
- `Morse.Homology.bettiNumber_le_critCount_of_compactSpace` — Morse/Homology/MorseHomologyManifold.lean, line 283
- `Morse.Homology.altSum_bettiNumber_le_of_compactSpace` — Morse/Homology/MorseHomologyManifold.lean, line 260
- `Morse.Homology.sum_bettiNumber_eq_sum_critCount_of_compactSpace` — Morse/Homology/MorseHomologyManifold.lean, line 252
- `Morse.Homology.bettiNumber_eq_critCount_of_lacunary_of_compactSpace` — Morse/Homology/MorseHomologyManifold.lean, line 291

*What differs.*
- Hausdorffness is assumed, for the embedding; Milnor's manifolds are tacitly Hausdorff.
- The proof passes through a Whitney embedding $M \cong N \subseteq \mathbb R^{K+1}$ (V4.16), on which $g$ becomes the restriction of a smooth ambient function with the same numbers $C_\lambda$ (V4.15), and homology is carried back along the homeomorphism; dimension $0$ is done directly from (3).
- Non-compact manifolds and integral homology are not covered.

### V3.41. $\mathbb CP^n$ and Milnor's coordinates

*restated* · rank-one projections $zz^*$ · slice charts from Milnor's coordinates

**Milnor (§4, p. 26).** $\mathbb CP_n$ is the set of equivalence classes of $(n + 1)$-tuples $(z_0, \dots, z_n)$ of complex numbers with $\sum|z_j|^2 = 1$. On the set $U_0$ where $z_0 \neq 0$, set $|z_0|\,z_j/z_0 = x_j + iy_j$; then $x_1, y_1, \dots, x_n, y_n$ "are the required coordinate functions, mapping $U_0$ diffeomorphically onto the open unit ball in $\mathbb R^{2n}$".

**Proved in Lean.** Here $\mathbb CP^n$ is the set of Hermitian projections of trace $1$ in the space $M_{n+1}(\mathbb C)$ of complex matrices (the Grassmannian of V14.16 with $m = 1$). Every point of it is $P = zz^*$, that is $P_{ab} = z_a\bar z_b$, for a unit vector $z \in \mathbb C^{n+1}$. For $0 \le k \le n$ let $U_k$ be the set of $P$ with $\operatorname{Re}P_{kk} > 0$; every point of $\mathbb CP^n$ lies in some $U_k$. On $\mathbb R^{2n} = \mathbb C^n$, with coordinates $z_j = x_j + iy_j$ ($j \neq k$), put $\operatorname{param}_k(z) = vv^*$, where $v_k = \sqrt{1 - |z|^2}$ and $v_j = z_j$ for $j \neq k$; and for a matrix $P$ put $\operatorname{coord}_k(P) = (P_{jk}/\sqrt{\operatorname{Re}P_{kk}})_{j \neq k}$. Then $\operatorname{coord}_k(\operatorname{param}_k(z)) = z$ for $|z| < 1$, and for $P \in \mathbb CP^n \cap U_k$, $|\operatorname{coord}_k(P)| < 1$ and $\operatorname{param}_k(\operatorname{coord}_k(P)) = P$. $\mathbb CP^n$ is a compact slice submanifold of $M_{n+1}(\mathbb C)$ of dimension $2n$, and at every $x \in \mathbb CP^n \cap U_k$ it has a slice chart whose parametrization is $z \mapsto \operatorname{param}_k(\operatorname{coord}_k(x) + z)$ near $0$.

- `Morse.CP.exists_vec_of_mem` — Morse/Chapter3/ProjectiveSpace.lean, line 203
- `Morse.CP.Model` — Morse/Chapter3/ProjectiveSpace.lean, line 127
- `Morse.CP.param` — Morse/Chapter3/ProjectiveSpace.lean, line 140
- `Morse.CP.coord` — Morse/Chapter3/ProjectiveSpace.lean, line 148
- `Morse.CP.coord_param` — Morse/Chapter3/ProjectiveSpace.lean, line 192
- `Morse.CP.nsq_coord_lt_and_param_coord` — Morse/Chapter3/ProjectiveSpace.lean, line 216
- `Morse.CP.exists_re_diag_pos` — Morse/Chapter3/ProjectiveSpace.lean, line 312
- `Morse.CP.isSliceSubmanifold` — Morse/Chapter3/ProjectiveSpace.lean, line 418
- `Morse.CP.exists_sliceChart` — Morse/Chapter3/ProjectiveSpace.lean, line 335
- `Morse.CP.isCompact` — Morse/Chapter3/ProjectiveSpace.lean, line 435

*What differs.*
- $\mathbb CP^n$ is the compact submanifold of Hermitian projections of trace $1$ in $M_{n+1}(\mathbb C)$, with the induced smooth structure; Milnor's coordinates are $P_{jk}/\sqrt{P_{kk}}$, independent of the representative, and they are the coordinates of slice charts.
- "Diffeomorphically" presupposes a smooth structure on $\mathbb CP_n$, which the book does not describe.

### V3.42. Milnor's function on $\mathbb CP^n$: critical points and indices

*as in the book* · one critical point of each even index

**Milnor (§4, pp. 26–27).** $f(z_0 : z_1 : \dots : z_n) = \sum c_j|z_j|^2$, with distinct real constants $c_j$. In the coordinates of $U_0$, $f = c_0 + \sum_{j=1}^n(c_j - c_0)(x_j^2 + y_j^2)$; so the only critical point within $U_0$ is the centre $p_0$, non-degenerate, of index twice the number of $j$ with $c_j < c_0$. Similarly at $p_1, \dots, p_n$. "Every possible even index between $0$ and $2n$ occurs exactly once."

*The scan of p. 26 prints the definition as $f = c_j|z_j|$; the display that follows it confirms $\sum c_j|z_j|^2$.*

**Proved in Lean.** For real numbers $c_0, \dots, c_n$ let $f(P) = \sum_j c_j\operatorname{Re}P_{jj}$ on $\mathbb CP^n$, so that $f(zz^*) = \sum_j c_j|z_j|^2$. In the coordinates of V3.41, $f(\operatorname{param}_k(z)) = c_k + \sum_{j \neq k}(c_j - c_k)(x_j^2 + y_j^2)$ for $|z| \le 1$. Suppose the $c_j$ are distinct. Then the critical points of $f$ are exactly the $n + 1$ points $p_k = \operatorname{param}_k(0)$ (the projections onto the coordinate axes); $p_k$ is non-degenerate, of index $2\,\#\{j : c_j < c_k\}$; so $f$ is a Morse function. The map $k \mapsto \#\{j : c_j < c_k\}$ is a bijection of $\{0, \dots, n\}$, and so the number $C_\lambda$ of critical points of index $\lambda$ is $1$ for $\lambda = 0, 2, \dots, 2n$ and $0$ for every other $\lambda$.

- `Morse.CP.height` — Morse/Chapter3/ProjectiveMorse.lean, line 74
- `Morse.CP.height_param` — Morse/Chapter3/ProjectiveMorse.lean, line 96
- `Morse.CP.isCriticalPointM_height_iff` — Morse/Chapter3/ProjectiveMorse.lean, line 282
- `Morse.CP.isNondegenerate_indexM_height` — Morse/Chapter3/ProjectiveMorse.lean, line 299
- `Morse.CP.isNondegenerate_of_isCriticalPointM` — Morse/Chapter3/ProjectiveMorse.lean, line 309
- `Morse.CP.bijective_rank` — Morse/Chapter3/ProjectiveMorse.lean, line 336
- `Morse.CP.critCount_height` — Morse/Chapter3/ProjectiveMorse.lean, line 346

*What differs.*
- The critical points, their non-degeneracy and their indices are read in the slice parametrizations of V3.41. That each even index occurs once is the bijectivity of $k \mapsto \#\{j : c_j < c_k\}$, Milnor's tacit renumbering $c_0 < \dots < c_n$.

### V3.43. The cells and the homology of $\mathbb CP^n$

*narrower* · homology over fields, not over $\mathbb Z$ · an iterated adjunction space

**Milnor (§4, p. 27).** By Theorem 3.5, $\mathbb CP_n$ has the homotopy type of a CW-complex of the form $e^0 \cup e^2 \cup e^4 \cup \dots \cup e^{2n}$. It follows that the integral homology groups of $\mathbb CP_n$ are $\mathbb Z$ for $i = 0, 2, 4, \dots, 2n$ and $0$ for other values of $i$.

**Proved in Lean.** $\mathbb CP^n$ has the homotopy type of a space built from the empty set by attaching cells one after another (V2.12), exactly one of each dimension $0, 2, \dots, 2n$. For every field $\mathbb k$, $\dim H_\lambda(\mathbb CP^n; \mathbb k) = 1$ if $\lambda$ is even and $\lambda \le 2n$, and $0$ otherwise.

- `Morse.CP.exists_cells` — Morse/Chapter3/ProjectiveMorse.lean, line 413
- `Morse.CP.bettiNumber_eq` — Morse/Chapter3/ProjectiveMorse.lean, line 402
- `Morse.bettiNumber_complexProjectiveSpace` — Morse/Chapter3/ProjectiveMorse.lean, line 426

*What differs.*
- One cell in each dimension $0, 2, \dots, 2n$, attached along arbitrary maps (V2.12). The Betti numbers over every field come from the lacunary principle (V3.37, V3.39); the integral groups are not derived.

## Chapter 4

*Milnor §6, pp. 32–38: focal points, existence and density of Morse functions*

### V4.1. The normal bundle and the endpoint map

*stronger* · $k = n$ allowed · $M$ neither closed nor compact · the twisted map $E_\Gamma$

**Milnor (§6, p. 32).** For a $k$-dimensional manifold $M$ differentiably embedded in $\mathbb R^n$, $k < n$, Milnor takes the set $N \subset M \times \mathbb R^n$ of pairs $(q, v)$ with $v$ perpendicular to $M$ at $q$, the total space of the normal vector bundle, which, he says, is not difficult to show to be an $n$-manifold differentiably embedded in $\mathbb R^{2n}$; and the endpoint map $E : N \to \mathbb R^n$, $E(q, v) = q + v$.

**Proved in Lean.** Throughout, $M \subseteq \mathbb R^n$ is a slice submanifold modelled on $\mathbb R^k$ with complement $\mathbb R^w$; if $M$ is non-empty, $k + w = n$. The normal bundle is $N = \{(q, v) \in M \times \mathbb R^n : v \perp T_qM\}$; when $k + w = n$ it is a slice submanifold of $\mathbb R^n \times \mathbb R^n$ of dimension $n$ (the Milnor project's construction). The endpoint map is $E(q, v) = q + v$; more generally, for a map $\Gamma : \mathbb R^n \to \mathbb R^n$, $E_\Gamma(q, v) = \Gamma(q) + v$, smooth over every open set on which $\Gamma$ is smooth, with $E_{\mathrm{id}} = E$.

- `Milnor.Problems.normalBundleSet` — ../Milnor/Chapter8/NormalBundle.lean, line 75
- `Milnor.Problems.isSliceSubmanifold_normalBundle` — ../Milnor/Chapter8/NormalBundle.lean, line 218
- `Morse.mem_normalBundleSet_iff` — Morse/Chapter4/NormalBundle.lean, line 93
- `Morse.slice_dim_add_eq_of_nonempty` — Morse/Chapter4/Focal.lean, line 107
- `Morse.normalEnd` — Morse/Chapter4/NormalBundle.lean, line 334
- `Morse.normalEnd_id` — Morse/Chapter4/NormalBundle.lean, line 336

*What differs.*
- “Differentiably embedded” must mean a submanifold, which a slice submanifold is: an injectively immersed manifold need not be one (V4.14).
- $k = n$ is allowed and $M$ need not be closed or compact. That $N$ is an $n$-manifold, which Milnor calls not difficult, is the Milnor project's construction of the normal bundle as a slice submanifold; for slice charts, $k + w = n$ needs $M \ne \emptyset$.
- The twisted endpoint map $E_\Gamma$ is not in the book; it serves the perturbation argument of V4.20.

### V4.2. Focal points and their multiplicity

*hypotheses explicit* · nullity read in a chart of $N$ · focal set = critical values of $E$

**Milnor (§6, Definition, p. 32).** A point $e = q + v$, $(q, v) \in N$, is a focal point of $(M, q)$, of multiplicity $\mu$, when the Jacobian of $E$ at $(q, v)$ has nullity $\mu > 0$, and a focal point of $M$ when it is one of $(M, q)$ for some $q \in M$; intuitively, focal points are where nearby normals meet. The proof of Corollary 6.2 uses that the focal points are exactly the images under $E$ of its critical points.

**Proved in Lean.** Assume $k + w = n$. The nullity of $E$ at $x \in N$ is the dimension of the kernel of $dE_x$, the tangent space of $N$ at $x$ being identified with $\mathbb R^n$ by the chart of $N$ at $x$. A point $e \in \mathbb R^n$ is a focal point of $(M, q)$ with multiplicity $\mu$ if $(q, e - q) \in N$ and the nullity of $E$ at $(q, e - q)$ is $\mu > 0$; a focal point of $(M, q)$ if this holds for some $\mu$; and a focal point of $M$ if it is a focal point of $(M, q)$ for some $q \in M$. The nullity is positive exactly at the critical points of $E$, the points where $dE$ is not onto; so the set of focal points of $M$ is the set of critical values of $E$.

- `Morse.endpointNullity` — Morse/Chapter4/Focal.lean, line 126
- `Morse.IsFocalPointMult` — Morse/Chapter4/Focal.lean, line 133
- `Morse.IsFocalPoint` — Morse/Chapter4/Focal.lean, line 137
- `Morse.focalSet` — Morse/Chapter4/Focal.lean, line 142
- `Morse.endpointNullity_pos_iff` — Morse/Chapter4/Focal.lean, line 148
- `Morse.isFocalPoint_iff` — Morse/Chapter4/Focal.lean, line 163
- `Morse.focalSet_eq_image_critPoints` — Morse/Chapter4/Focal.lean, line 174

*What differs.*
- The nullity is computed in a chart of $N$; it does not depend on the chart, two charts differing by an isomorphism of $\mathbb R^n$.
- The characterization used in the proof of Corollary 6.2 is proved as an equality of sets.

### V4.3. Theorem 6.1 (Sard)

*narrower* · $f$ smooth, not merely $C^1$ · the target a vector space · any dimensions · proved, not quoted

**Milnor (§6, Theorem 6.1 (Sard), p. 33).** For a $C^1$ map $f : M_1 \to M_2$ between differentiable manifolds of the same dimension, each with a countable basis, the critical points, where the Jacobian of $f$ is singular, have an image of measure $0$ in $M_2$. Milnor gives no proof, referring to de Rham.

**Proved in Lean.** Let $M$ be a second countable smooth manifold without boundary modelled on a finite-dimensional real normed space $E$, $F$ a finite-dimensional real normed space with a Haar measure $\mu$, $U \subseteq M$ open and $f : M \to F$ smooth on $U$. Then the image under $f$ of the points of $U$ where $df$ is not onto is $\mu$-null; in particular, for $f$ smooth on $M$, the set of critical values is null. $E$ and $F$ are required to lie in the same universe of Lean's type theory, a formality with no mathematical content.

- `Morse.measure_image_inter_critPoints_eq_zero` — Morse/Chapter4/Sard.lean, line 91
- `Morse.measure_image_critPoints_eq_zero` — Morse/Chapter4/Sard.lean, line 123

*What differs.*
- $f$ is smooth, not merely $C^1$, and the target is a vector space; on the other hand the dimensions are arbitrary. Every use in §6 is for a smooth map into $\mathbb R^n$.
- “Measure $0$” in the target needs a measure class; only $\mathbb R^n$ is used, where all Haar measures have the same null sets.
- The proof uses countably many charts and the Euclidean Sard theorem of the Milnor project, which is proved for smooth maps only.

### V4.4. Corollary 6.2: almost no point is focal

*hypotheses explicit* · $N$ second countable · any Haar measure

**Milnor (§6, Corollary 6.2, p. 33).** Almost every point of $\mathbb R^n$ is not a focal point of $M$. Proof: $N$ is an $n$-manifold and the focal points are the images of the critical points of $E : N \to \mathbb R^n$, so they form a set of measure $0$ by Sard's theorem.

**Proved in Lean.** If $k + w = n$, the set of focal points of $M$ is null for every Haar measure on $\mathbb R^n$.

- `Morse.measure_focalSet_eq_zero` — Morse/Chapter4/Focal.lean, line 201

*What differs.*
- Sard's theorem needs $N$ to have a countable basis, automatic for a subset of $\mathbb R^{2n}$; $M$ need not be closed or compact.

### V4.5. The first and second fundamental forms

*restated* · $\ell_v$ for every vector $v$ · the coordinates of a slice chart

**Milnor (§6, pp. 33–34).** In local coordinates $u^1, \dots, u^k$ on $M \subset \mathbb R^n$, with $\vec x(u)$ the inclusion, the first fundamental form is the matrix $g_{ij} = \partial\vec x/\partial u^i \cdot \partial\vec x/\partial u^j$, and the second fundamental form is the symmetric matrix $(\vec\ell_{ij})$ of vector-valued functions, $\vec\ell_{ij}$ the normal component of $\partial^2\vec x/\partial u^i\partial u^j$. For a unit vector $\vec v$ normal to $M$ at $q$, the matrix $(\vec v \cdot \vec\ell_{ij})$ is the second fundamental form of $M$ at $q$ in the direction $\vec v$. Milnor gives no invariant definition and works in a fixed coordinate system.

**Proved in Lean.** For $q \in M$, the coordinates $u \mapsto x(u)$ are the inverse of the slice chart of $M$ chosen at $q$, with $x(u_q) = q$; $dx$ and $d^2x$ are its first and second derivatives at $u_q$. The first fundamental form is the bilinear form $g(\xi, \eta) = \langle dx\,\xi, dx\,\eta\rangle$ on $\mathbb R^k$; the second fundamental form in a direction $v \in \mathbb R^n$ is $\ell_v(\xi, \eta) = \langle v, d^2x(\xi, \eta)\rangle$; and for a linear map $T$ of $\mathbb R^n$ the form $(\xi, \eta) \mapsto \langle T\,dx\,\xi, dx\,\eta\rangle - \ell_v(\xi, \eta)$ is the one attached to $E_\Gamma$ with $T = d\Gamma_q$, equal to $g - \ell_v$ for $T = \mathrm{id}$.

- `Morse.xParam` — Morse/Chapter4/NormalBundle.lean, line 116
- `Morse.uParam` — Morse/Chapter4/NormalBundle.lean, line 119
- `Morse.dParam` — Morse/Chapter4/NormalBundle.lean, line 122
- `Morse.d2Param` — Morse/Chapter4/NormalBundle.lean, line 125
- `Morse.firstFF` — Morse/Chapter4/NormalBundle.lean, line 290
- `Morse.secondFF` — Morse/Chapter4/NormalBundle.lean, line 296
- `Morse.normalForm` — Morse/Chapter4/NormalBundle.lean, line 302

*What differs.*
- $\ell_v$ is defined for every $v$ by the inner product with $d^2x$; for $v$ normal at $q$ it is Milnor's $(\vec v \cdot \vec\ell_{ij})$, the tangential part of $d^2x$ being orthogonal to $v$.
- The coordinates are those of the chosen slice chart, where Milnor allows any coordinates.

### V4.6. Principal curvatures

*restated* · no normalization of $(g_{ij})$ · $k$ curvatures, not $n$ · chart independence not proved

**Milnor (§6, p. 34).** In coordinates for which $(g_{ij})$ is the identity matrix at $q$, the principal curvatures $K_1, \dots, K_n$ of $M$ at $q$ in the normal direction $\vec v$ are the eigenvalues of $(\vec v \cdot \vec\ell_{ij})$; the reciprocals of those that are non-zero are the principal radii of curvature.

**Proved in Lean.** The shape operator $S_v$ of $M$ at $q$ in the direction $v$ is the endomorphism of the tangent space $T_qM = \operatorname{range} dx$ with $\langle S_v a, b\rangle = \ell_v(dx^{-1}a, dx^{-1}b)$; it is self-adjoint. The principal curvatures of $M$ at $q$ in the direction $v$ are its $k$ eigenvalues, with multiplicity, in decreasing order; the multiplicity of $K$ is the dimension of the eigenspace of $K$.

- `Morse.tanSpace` — Morse/Chapter4/Curvature.lean, line 89
- `Morse.shapeOp` — Morse/Chapter4/Curvature.lean, line 119
- `Morse.isSymmetric_shapeOp` — Morse/Chapter4/Curvature.lean, line 130
- `Morse.principalCurvatures` — Morse/Chapter4/Curvature.lean, line 297
- `Morse.finrank_eigenspace_shapeOp` — Morse/Chapter4/Curvature.lean, line 301

*What differs.*
- No normalization: the eigenvalues of $S_v$ are those of $g^{-1}(v \cdot \ell)$, which are Milnor's $K_i$ when $g$ is the identity. That coordinates with $g_{ij}(q) = \delta_{ij}$ exist, and that the eigenvalues do not depend on them, the book leaves implicit.
- That $S_v$ does not depend on the parametrization is not proved, and nothing uses it.
- The scan lists the curvatures as $K_1, \dots, K_n$; there are $k$ of them, and Lemma 6.3 itself uses $1 \le i \le k$.

### V4.7. Lemma 6.3: focal points along a normal line

*stronger* · any normal $v$, not only unit ones · $t = 0$ set aside · multiplicity = eigenspace dimension

**Milnor (§6, Lemma 6.3, p. 34).** Let $\vec v$ be a unit normal to $M$ at $\vec q$. On the normal line $\ell = \{\vec q + t\vec v\}$ the focal points of $(M, q)$ are exactly the points $\vec q + K_i^{-1}\vec v$ with $1 \le i \le k$ and $K_i \ne 0$; counted with their multiplicities, there are therefore at most $k$ of them on $\ell$.

**Proved in Lean.** Assume $k + w = n$, and let $\mathrm{mult}_q(e)$ be the multiplicity of $e$ as a focal point of $(M, q)$, $0$ if it is not one. For $q \in M$, $v \perp T_qM$ and $t \in \mathbb R$: $\mathrm{mult}_q(q + tv) = 0$ if $t = 0$, and otherwise it is the multiplicity of $1/t$ as an eigenvalue of $S_v$. Hence $q + tv$ is a focal point of $(M, q)$ iff $t = K^{-1}$ for a non-zero principal curvature $K$ in the direction $v$, the multiplicity of $q + K^{-1}v$ is that of $K$, and for any finitely many values of $t$ the multiplicities of the points $q + tv$ add up to at most $k$.

- `Morse.focalMult` — Morse/Chapter4/Curvature.lean, line 212
- `Morse.focalMult_add_smul` — Morse/Chapter4/Curvature.lean, line 242
- `Morse.isFocalPoint_add_smul_iff` — Morse/Chapter4/Curvature.lean, line 263
- `Morse.focalMult_add_inv_smul` — Morse/Chapter4/Curvature.lean, line 282
- `Morse.sum_focalMult_add_smul_le` — Morse/Chapter4/Curvature.lean, line 321
- `Morse.map_nullSpace_firstFF_sub_eq_eigenspace` — Morse/Chapter4/Curvature.lean, line 174

*What differs.*
- $v$ is any normal vector, not necessarily a unit vector.
- $t = 0$ must be set aside in “$1/t$ is an eigenvalue”: $q$ is never a focal point of $(M, q)$ (V4.9). The multiplicity of an eigenvalue of a symmetric matrix as a root of the characteristic polynomial equals the dimension of its eigenspace, which is what the proof produces.
- In place of Milnor's normalized coordinates, for $t \ne 0$ the map $dx$ carries the null space of $g - t\ell_v$ onto the eigenspace of $S_v$ for $1/t$.

### V4.8. The Jacobian of the endpoint map

*restated* · no normal frame · nullities agree, ranks do not

**Milnor (§6, proof of Lemma 6.3, p. 34).** Milnor chooses unit normal fields $\vec w_1, \dots, \vec w_{n-k}$, orthogonal to each other, coordinates $(u, t)$ on $N$ given by $(u, t) \mapsto (\vec x(u), \sum_\alpha t^\alpha\vec w_\alpha(u))$, and takes inner products of the partial derivatives of $E$ with $\partial\vec x/\partial u^1, \dots, \partial\vec x/\partial u^k, \vec w_1, \dots, \vec w_{n-k}$. This gives an $n \times n$ matrix whose rank equals that of the Jacobian of $E$, with an identity block below; he says its rank is the rank of the upper left block, which is $(g_{ij} - \sum_\alpha t^\alpha \vec w_\alpha \cdot \vec\ell_{ij})$.

**Proved in Lean.** Assume $k + w = n$ and let $(q, v) \in N$. A pair $(a, b) \in \mathbb R^n \times \mathbb R^n$ is tangent to $N$ at $(q, v)$ iff $a = dx\,\xi$ for some $\xi \in \mathbb R^k$ and $\langle b, dx\,\eta\rangle + \langle v, d^2x(\xi, \eta)\rangle = 0$ for every $\eta \in \mathbb R^k$. For $\Gamma$ differentiable at $q$, the derivative of $E_\Gamma$ at $(q, v)$ is $(a, b) \mapsto d\Gamma_q(a) + b$ on this tangent space, and its nullity equals the nullity of the form $(\xi, \eta) \mapsto \langle d\Gamma_q\,dx\,\xi, dx\,\eta\rangle - \langle v, d^2x(\xi, \eta)\rangle$ on $\mathbb R^k$. For $\Gamma = \mathrm{id}$: the nullity of $E$ at $(q, v)$ is the nullity of $g - \ell_v$.

- `Morse.mem_range_mfd_val_normalBundle_iff` — Morse/Chapter4/NormalBundle.lean, line 210
- `Morse.hasMFDerivAt_normalEnd` — Morse/Chapter4/NormalBundle.lean, line 342
- `Morse.finrank_ker_mfd_normalEnd` — Morse/Chapter4/NormalBundle.lean, line 379
- `Morse.endpointNullity_eq_nullity` — Morse/Chapter4/Focal.lean, line 220

*What differs.*
- No normal frame is used: the tangent space of $N$ is the kernel of the derivative of the local defining function of $N$, and its second condition is the derivative of Milnor's identity $\vec w_\alpha \cdot \partial\vec x/\partial u^j = 0$. The fields $\vec w_\alpha$ exist only locally, and the book does not say why they exist.
- The sentence that the rank of the matrix equals the rank of the upper left block does not hold as written, the two ranks differing by $n - k$; what holds, and is needed, is that the nullities agree.

### V4.9. Assertion 6.4

*stronger* · $v$ any normal vector · the case $t = 0$ treated

**Milnor (§6, Assertion 6.4, p. 35).** For a unit normal $\vec v$, $\vec q + t\vec v$ is a focal point of $(M, q)$ of multiplicity $\mu$ exactly when the matrix $(g_{ij} - t\,\vec v \cdot \vec\ell_{ij})$ is singular of nullity $\mu$.

**Proved in Lean.** Assume $k + w = n$. For $q \in M$, $v \perp T_qM$, $t \in \mathbb R$ and $\mu \in \mathbb N$: $q + tv$ is a focal point of $(M, q)$ with multiplicity $\mu$ iff the form $g - t\ell_v$ (in the coordinates of V4.5) has nullity $\mu > 0$. In particular $q$ is never a focal point of $(M, q)$, $g$ being non-degenerate.

- `Morse.isFocalPointMult_add_smul_iff` — Morse/Chapter4/Focal.lean, line 231
- `Morse.not_isFocalPoint_self` — Morse/Chapter4/Focal.lean, line 250

*What differs.*
- $v$ need not be a unit vector, and the case $t = 0$, left implicit, is part of the statement: $q$ is never a focal point of $(M, q)$.

### V4.10. The critical points and the Hessian of $L_p$

*stronger* · at every point, not only critical ones · no unit vector, no case $p = q$

**Milnor (§6, pp. 35–36).** For fixed $\vec p \in \mathbb R^n$, $f = L_{\vec p}$ satisfies $f(\vec x(u)) = \|\vec x(u) - \vec p\|^2$ and $\partial f/\partial u^i = 2\,\partial\vec x/\partial u^i \cdot (\vec x - \vec p)$, so $f$ has a critical point at $\vec q$ iff $\vec q - \vec p$ is normal to $M$ at $\vec q$. At a critical point the second partial derivatives are $2(\partial\vec x/\partial u^i \cdot \partial\vec x/\partial u^j + \partial^2\vec x/\partial u^i\partial u^j \cdot (\vec x - \vec p))$, which on setting $\vec p = \vec x + t\vec v$ becomes $2(g_{ij} - t\,\vec v \cdot \vec\ell_{ij})$.

*The second display is cut off in the scan; its value is the one used on p. 38.*

**Proved in Lean.** For $p \in \mathbb R^n$ let $L_p(q) = \|q - p\|^2$ on $M$. Then $q$ is a critical point of $L_p$ iff $p - q \perp T_qM$, that is, iff $(q, p - q) \in N$; and at every $q \in M$ the Hessian of $L_p \circ x$ at $u_q$ is $2(g - \ell_{p - q})$.

- `Morse.isCriticalPointM_normSq_sub_iff_mem_normalBundleSet` — Morse/Chapter4/Focal.lean, line 273
- `Morse.hessian_normSq_sub_xParam` — Morse/Chapter4/Focal.lean, line 290

*What differs.*
- Setting $\vec p = \vec q + t\vec v$ with $\vec v$ a unit normal presupposes that $p - q$ is normal, that is, that $q$ is critical, and that $p \ne q$. The formula is proved at every point, in the direction $p - q$ itself, so neither is needed.

### V4.11. Lemma 6.5

*hypotheses explicit* · the non-critical case treated · nullity of $L_p$ = nullity of $E$

**Milnor (§6, Lemma 6.5, p. 36).** A point $\vec q \in M$ is a degenerate critical point of $L_{\vec p}$ exactly when $\vec p$ is a focal point of $(M, \vec q)$, and the nullity of the critical point is then the multiplicity of the focal point.

**Proved in Lean.** Assume $k + w = n$, and let $p \in \mathbb R^n$, $q \in M$. If $q$ is a critical point of $L_p$, the nullity of $L_p$ at $q$ (the nullity of its Hessian) equals the nullity of $E$ at $(q, p - q)$. Hence $p$ is a focal point of $(M, q)$ with multiplicity $\mu$ iff $q$ is a critical point of $L_p$ of nullity $\mu > 0$, and $q$ is a degenerate critical point of $L_p$ iff $p$ is a focal point of $(M, q)$.

- `Morse.nullityM_normSq_sub_eq_endpointNullity` — Morse/Chapter4/Focal.lean, line 305
- `Morse.isFocalPointMult_iff` — Morse/Chapter4/Focal.lean, line 319
- `Morse.isDegenerate_normSq_sub_iff_isFocalPoint` — Morse/Chapter4/Focal.lean, line 335

*What differs.*
- The case of a non-critical $q$, left implicit, is covered: then $p - q$ is not normal at $q$ and $p$ is not a focal point of $(M, q)$.

### V4.12. Theorem 6.6

*stronger* · $M$ neither closed nor compact · $k = n$ allowed · any Haar measure

**Milnor (§6, Theorem 6.6, p. 36).** Outside a set of measure $0$ of points $\vec p \in \mathbb R^n$, the function $L_{\vec p} : M \to \mathbb R$ has no degenerate critical point; Milnor obtains this at once from Lemma 6.5 and Corollary 6.2.

**Proved in Lean.** For every slice submanifold $M \subseteq \mathbb R^n$ and every Haar measure $\mu$ on $\mathbb R^n$ (in particular Lebesgue measure), for $\mu$-almost every $p$ the function $L_p$ is a Morse function on $M$, smooth with only non-degenerate critical points. If $L_p$ is not a Morse function, $p$ is a focal point of $M$. Every non-empty open subset of $\mathbb R^n$ contains a $p$ for which $L_p$ is a Morse function.

- `Morse.mem_focalSet_of_not_isMorseFunction` — Morse/Chapter4/Focal.lean, line 358
- `Morse.ae_isMorseFunction_normSq_sub` — Morse/Chapter4/Focal.lean, line 372
- `Morse.ae_volume_isMorseFunction_normSq_sub` — Morse/Chapter4/Focal.lean, line 387
- `Morse.exists_mem_isMorseFunction_normSq_sub` — Morse/Chapter4/Focal.lean, line 395

*What differs.*
- $M$ need not be closed or compact, $k = n$ is allowed, and any Haar measure may be used. $M = \emptyset$ is trivial, and is the only case in which $k + w = n$ may fail.

### V4.13. Corollary 6.7 for closed submanifolds of $\mathbb R^n$

*narrower* · closed submanifolds of $\mathbb R^n$ · the embedding must be closed · Hausdorff, countable basis

**Milnor (§6, Corollary 6.7, p. 36).** Every manifold $M$ carries a differentiable function without degenerate critical points all of whose sublevel sets $M^a$ are compact. The proof applies Theorem 6.6 to $M$ embedded differentiably as a closed subset of $\mathbb R^{2n+1}$, which Whitney's theorem provides.

**Proved in Lean.** If the slice submanifold $M \subseteq \mathbb R^n$ is a closed subset, then for every $p$ and every $a$ the sublevel set $\{q \in M : L_p(q) \le a\}$ is compact; so for almost every $p$, $L_p$ is a Morse function on $M$ with compact sublevel sets, and $M$ carries a Morse function $f$ each of whose sublevel sets $M^a$ is compact and contains only finitely many critical points. If $M$ is compact, for almost every $p$, $L_p$ is a Morse function with finitely many critical points.

- `Morse.isCompact_sublevel_normSq_sub` — Morse/Chapter4/Existence.lean, line 74
- `Morse.ae_isMorseFunction_normSq_sub_and_isCompact_sublevel` — Morse/Chapter4/Existence.lean, line 80
- `Morse.exists_isMorseFunction_isCompact_sublevel` — Morse/Chapter4/Existence.lean, line 92
- `Morse.exists_isMorseFunction_finite_critPoints_sublevel` — Morse/Chapter4/Existence.lean, line 102
- `Morse.exists_isMorseFunction_finite_critPoints` — Morse/Chapter4/Compact.lean, line 51

*What differs.*
- Proved for closed submanifolds of $\mathbb R^n$; abstract compact manifolds are V4.17, and non-compact abstract manifolds are not covered, Mathlib's Whitney embedding being for compact manifolds only.
- The embedding must be closed: for the open interval in $\mathbb R$, every $L_p$ has a non-compact sublevel set. And “any manifold” must be read as Hausdorff with a countable basis: on the long line every continuous real function is eventually constant, so some sublevel set is not compact.

### V4.14. The image of an embedding is a submanifold

*not in the book* · a topological embedding is needed · the inverse smooth by slice charts

**Milnor (§6, proof of Corollary 6.7, p. 36).** Not stated. In the proof of Corollary 6.7 Milnor applies Theorem 6.6, a statement about manifolds in $\mathbb R^n$, to the image of Whitney's embedding, taking for granted that the image is a submanifold diffeomorphic to $M$.

**Proved in Lean.** Let $M$ be a smooth manifold without boundary modelled on a finite-dimensional real normed space $E$, $F$ a finite-dimensional real normed space, and $e : M \to F$ smooth, a topological embedding (a homeomorphism onto its image), with injective derivative at every point. For finite-dimensional $Z$, $W$ with $\dim Z = \dim E$ and $\dim Z + \dim W = \dim F$, the image $e(M)$ is a slice submanifold of $F$ modelled on $Z$ with complement $W$, and $e : M \to e(M)$ is a smooth diffeomorphism.

- `Morse.exists_continuousLinearEquiv_coprod` — Morse/Chapter4/WhitneySlice.lean, line 85
- `Morse.exists_sliceChart_range` — Morse/Chapter4/WhitneySlice.lean, line 141
- `Morse.isSliceSubmanifold_range` — Morse/Chapter4/WhitneySlice.lean, line 259
- `Morse.contMDiff_ofInjective_symm` — Morse/Chapter4/WhitneySlice.lean, line 271
- `Morse.diffeomorphRange` — Morse/Chapter4/WhitneySlice.lean, line 314
- `Morse.exists_diffeomorph_range` — Morse/Chapter4/WhitneySlice.lean, line 336

*What differs.*
- $e$ must be a homeomorphism onto its image: the figure eight, an injectively immersed line, is not a submanifold. The inverse of $e$ is smooth because of the slice charts, not merely because $e$ is a smooth bijection, as $x \mapsto x^3$ on $\mathbb R$ shows.
- The proof is the local immersion theorem, from the Milnor project's inverse function theorem on manifolds, applied to $(z, w) \mapsto e(\varphi^{-1}(Tz)) + Lw$, with $\varphi$ a chart of $M$, $T : Z \cong E$, and $L$ completing $de_x$ to an isomorphism.

### V4.15. The Morse notions are invariant under diffeomorphisms

*not in the book* · used silently on p. 36 · carries every Whitney transfer

**Milnor (§6, p. 36).** Not stated; used without comment wherever a manifold is replaced by its image under an embedding, as in the proof of Corollary 6.7.

**Proved in Lean.** Let $g : M \to M'$ be a smooth diffeomorphism of smooth manifolds without boundary modelled on real normed spaces $E$, $E'$, and $f : M \to \mathbb R$. For every $f$, $q$ is a critical point of $f \circ g^{-1}$ iff $g^{-1}(q)$ is a critical point of $f$, and the numbers of critical points agree. If $f$ is $C^2$ at a critical point $g^{-1}(q)$, the Hessian of $f \circ g^{-1}$ at $q$ is the Hessian of $f$ at $g^{-1}(q)$ pulled back by $d(g^{-1})_q$, so non-degeneracy, index and nullity agree there. $f$ is a Morse function iff $f \circ g^{-1}$ is, and for $f$ of class $C^2$ the numbers $C_\lambda$ of $f$ and $f \circ g^{-1}$ agree.

- `Morse.isCriticalPointM_comp_symm_iff` — Morse/Chapter4/WhitneyInvariance.lean, line 74
- `Morse.hessianM_comp_symm_apply` — Morse/Chapter4/WhitneyInvariance.lean, line 172
- `Morse.isNondegenerate_hessianM_comp_symm_iff` — Morse/Chapter4/WhitneyInvariance.lean, line 198
- `Morse.indexM_comp_symm` — Morse/Chapter4/WhitneyInvariance.lean, line 219
- `Morse.nullityM_comp_symm` — Morse/Chapter4/WhitneyInvariance.lean, line 227
- `Morse.isMorseFunction_comp_symm_iff` — Morse/Chapter4/WhitneyInvariance.lean, line 246
- `Morse.critCount_comp_symm` — Morse/Chapter4/WhitneyInvariance.lean, line 255

*What differs.*
- Every result of this edition about an abstract compact manifold (V2.4, V3.39, V4.17, V4.19, V4.22, V4.24) is proved on an embedded copy and carried back by these invariances.

### V4.16. Whitney's embedding, for compact manifolds

*narrower* · compact manifolds only · Hausdorff assumed · the ambient dimension not $2n + 1$

**Milnor (§6, proof of Corollary 6.7, p. 36).** An $n$-dimensional manifold can be embedded differentiably as a closed subset of $\mathbb R^{2n+1}$; Milnor quotes Whitney, Geometric Integration Theory, p. 113.

**Proved in Lean.** Let $M$ be a compact Hausdorff smooth manifold without boundary modelled on a finite-dimensional real normed space $E$, $n = \dim E$. Then $M$ has a smooth closed embedding with injective derivative into some $\mathbb R^m$ (Mathlib's Whitney embedding), whose image is a slice submanifold modelled on $E$; such an embedding exists into $\mathbb R^{K+1}$ with $K \ge 1$ and $K + 1$ as large as desired; and $M$ is diffeomorphic to a compact, closed slice submanifold $N \subseteq \mathbb R^{K+1}$, $K \ge 1$, modelled on $\mathbb R^n$.

- `Morse.exists_isSliceSubmanifold_whitney` — Morse/Chapter4/Whitney.lean, line 135
- `Morse.exists_embedding_euclidean` — Morse/Chapter4/Whitney.lean, line 156
- `Morse.exists_diffeomorph_sliceSubmanifold` — Morse/Chapter4/Whitney.lean, line 180

*What differs.*
- Compact manifolds only, Hausdorff as Milnor's tacitly are: Mathlib's Whitney embedding is for compact manifolds.
- The ambient dimension is not $2n + 1$, which plays no role; $K \ge 1$ is arranged by two extra zero coordinates, for the Poincaré–Hopf theorem.

### V4.17. Corollary 6.7 for a compact manifold

*narrower* · compact $M$ only · Hausdorff assumed · $L_p$ on an embedded copy

**Milnor (§6, Corollary 6.7, p. 36).** Every manifold $M$ carries a differentiable function without degenerate critical points all of whose sublevel sets $M^a$ are compact.

**Proved in Lean.** Every compact Hausdorff smooth manifold without boundary, modelled on a finite-dimensional real normed space, carries a Morse function, and it has finitely many critical points.

- `Morse.exists_isMorseFunction_of_compactSpace` — Morse/Chapter4/Whitney.lean, line 201

*What differs.*
- Only compact $M$, where every $M^a$ is compact anyway; the function is $L_p$ on an embedded copy (V4.16, V4.13), pulled back by the diffeomorphism (V4.15).
- A non-compact abstract manifold would need a closed embedding into Euclidean space, which Mathlib does not have.

### V4.18. The Euler number of an abstract manifold

*restated* · defined by critical points · independent of $f$ by V4.19 · equal to the homological one

**Milnor (§5, formula (3), p. 29).** $\chi(M) = C_0 - C_1 + C_2 - \dots \pm C_n$ for a function with isolated, non-degenerate critical points on a compact manifold, where $\chi$ is the Euler characteristic of p. 28, defined from the Betti numbers.

**Proved in Lean.** For a manifold $M$ modelled on $E$, $\chi(M) = \sum_{\lambda=0}^{\dim E} (-1)^\lambda C_\lambda(f)$ for one Morse function $f$ on $M$ chosen once and for all, and $\chi(M) = 0$ if $M$ has no Morse function.

- `Morse.eulerNumberM` — Morse/Chapter4/Whitney.lean, line 365

*What differs.*
- Defined through critical points, not homology. The value must not depend on the choice of $f$, which is V4.19 for compact Hausdorff $M$; there it equals $\sum_i (-1)^i \dim H_i(M; F)$ for every field $F$ (V3.38).

### V4.19. Formula (3) and Application 2 on a compact manifold

*restated* · vector fields on an embedded copy · no appeal to Steenrod · Morse functions only

**Milnor (§6, Application 2, p. 36).** On a compact $M$ some vector field has index sum $\chi(M)$ over its critical points: for a differentiable $f$, $\chi(M) = \sum (-1)^\lambda C_\lambda$, and $\mathrm{grad} f$ has index $(-1)^\lambda$ where $f$ has index $\lambda$. Since the index sum is a topological invariant (Steenrod, §39.7), every vector field on $M$ has index sum $\chi(M)$.

**Proved in Lean.** Let $M$ be a compact Hausdorff smooth manifold without boundary modelled on a finite-dimensional real normed space. (i) Every Morse function $f$ on $M$ has $\sum_{\lambda=0}^{\dim M} (-1)^\lambda C_\lambda(f) = \chi(M)$; in dimension $0$ both sides are the number of points of $M$. (ii) If $\dim M = d + 1 \ge 1$ and $N \subseteq \mathbb R^{K+1}$, $K \ge 1$, is a compact non-empty slice submanifold modelled on $\mathbb R^{d+1}$ and diffeomorphic to $M$, every Euler number of $N$ (V3.17) equals $\chi(M)$, so the Poincaré–Hopf integer does not depend on the embedding. (iii) $\chi$ is invariant under diffeomorphisms between compact Hausdorff manifolds. (iv) If $M$ is non-empty of dimension $d + 1$, it is diffeomorphic to a compact $N \subseteq \mathbb R^{K+1}$ on which every smooth tangent field with finitely many zeros has index sum $\chi(M)$.

- `Morse.sum_critCount_eq_of_isMorseFunction_of_compactSpace` — Morse/Chapter4/Whitney.lean, line 376
- `Morse.sum_critCount_eq_eulerNumberM` — Morse/Chapter4/Whitney.lean, line 402
- `Morse.exists_eulerNumber_of_compactSpace` — Morse/Chapter4/Whitney.lean, line 412
- `Morse.sum_critCount_of_finrank_eq_zero` — Morse/Chapter4/Whitney.lean, line 351
- `Morse.IsEulerNumber.eq_eulerNumberM` — Morse/Chapter4/Whitney.lean, line 422
- `Morse.eulerNumberM_eq_of_diffeomorph` — Morse/Chapter4/Whitney.lean, line 438
- `Morse.exists_isEulerNumber_eulerNumberM` — Morse/Chapter4/Whitney.lean, line 458

*What differs.*
- Vector fields and their indices are defined in the Milnor project only for submanifolds of Euclidean space, so Application 2 is stated on an embedded copy; the topological invariance that Milnor quotes from Steenrod is replaced by the Poincaré–Hopf theorem and invariance under diffeomorphisms.
- $\chi(M)$ is the integer of V4.18; it equals the Poincaré–Hopf integer of every embedded copy and, by V3.38, the homological Euler characteristic.
- “Any differentiable function” must be a Morse function, and Hausdorffness is assumed.

### V4.20. The generic linear perturbation

*not in the book* · no boundedness, compactness, closedness · replaces Milnor's construction

**Milnor (§6, proof of Corollary 6.8, p. 37).** Not in this form. Milnor's proof of Corollary 6.8 uses $L_p$ on an embedding $h : M \to \mathbb R^n$ whose first coordinate is the given function $f$, with $p$ close to $(-c, 0, \dots, 0)$ for a large $c$.

**Proved in Lean.** For every slice submanifold $M \subseteq \mathbb R^n$, every smooth $f : M \to \mathbb R$ and every Haar measure on $\mathbb R^n$: for almost every $a \in \mathbb R^n$, $f + \langle a, \cdot\rangle$ is a Morse function on $M$, and such $a$ exist in every non-empty open set. For $f = \frac12\|x\|^2$ this is Theorem 6.6, since $\frac12\|x\|^2 + \langle a, x\rangle = \frac12 L_{-a}(x) - \frac12\|a\|^2$.

- `Morse.negGrad` — Morse/Chapter4/Approximation.lean, line 114
- `Morse.exists_local_extension_of_contMDiff` — Morse/Chapter4/Approximation.lean, line 275
- `Morse.mem_image_critPoints_of_not_isNondegenerate` — Morse/Chapter4/Approximation.lean, line 186
- `Morse.ae_isMorseFunction_add_inner` — Morse/Chapter4/Approximation.lean, line 302
- `Morse.exists_mem_isMorseFunction_add_inner` — Morse/Chapter4/Approximation.lean, line 342

*What differs.*
- The standard linear perturbation, used in place of Milnor's construction. The proof is that of Theorem 6.6 with $L_p$ replaced by $f + \langle a, \cdot\rangle$ and $E$ by $E_\Gamma$, $\Gamma = -\nabla F$ for a local extension $F$ of $f$: a degenerate critical point $q$ makes $(q, a + \nabla F(q))$ a critical point of $E_\Gamma$ with value $a$ (V4.8), and Sard's theorem (V4.3) on countably many pieces of $N$ finishes.

### V4.21. Corollary 6.8 on a submanifold of $\mathbb R^n$

*stronger* · $f$ need not be bounded · $M$ need not be compact · derivatives in fixed coordinates

**Milnor (§6, Corollary 6.8, p. 37).** A bounded smooth $f : M \to \mathbb R$ is a uniform limit of smooth functions $g$ without degenerate critical points, and $g$ may be chosen so that, on a given compact set $K$, its derivatives of every order $i \le k$ are uniformly close to those of $f$.

**Proved in Lean.** Let $M \subseteq \mathbb R^n$ be any slice submanifold, $f : M \to \mathbb R$ smooth, bounded or not, $\varepsilon > 0$, $r \in \mathbb N$, and finitely many smooth coordinate systems $y_j$ on open subsets of $M$, with values in $\mathbb R^k$, with compact sets $K_j$ inside their ranges. There is a Morse function $g$ on $M$ with $|g - f| < \varepsilon$ on all of $M$ and $\|D^i((g - f) \circ y_j^{-1})(u)\| < \varepsilon$ for every $j$, every $i \le r$ and every $u \in K_j$. One can take $g = f + \langle a, \beta(\cdot)\rangle$ with $a$ small, where $\beta(y) = y/\sqrt{1 + \|y\|^2}$ is the diffeomorphism of $\mathbb R^n$ onto its open unit ball; for compact $M$ also $g = f + \langle a, \cdot\rangle$.

- `Morse.exists_isMorseFunction_approx` — Morse/Chapter4/Approximation.lean, line 383
- `Morse.ballDiffeo` — Morse/Chapter4/Uniform.lean, line 72
- `Morse.isSliceSubmanifold_ballImage` — Morse/Chapter4/Uniform.lean, line 151
- `Morse.isMorseFunction_of_ballImage` — Morse/Chapter4/Uniform.lean, line 236
- `Morse.ae_isMorseFunction_add_inner_ballDiffeo` — Morse/Chapter4/Uniform.lean, line 296
- `Morse.exists_isMorseFunction_approx_uniform` — Morse/Chapter4/Uniform.lean, line 319

*What differs.*
- No boundedness hypothesis on $f$: the perturbation $\langle a, \beta(\cdot)\rangle$ is bounded by $\|a\|$, whatever $f$ is. $M$ need not be compact; it is a submanifold of $\mathbb R^n$, and abstract compact $M$ is V4.22.
- Derivatives on a manifold exist only in coordinates, so the approximation on $K$ is read in fixed coordinate systems covering $K$; finitely many suffice.
- Milnor's embedding with bounded image and first coordinate $f$ is not constructed; the proof is V4.20 applied to the submanifold $\beta(M)$ and $f \circ \beta^{-1}$, the Morse property carried back along $\beta$.

### V4.22. Corollary 6.8 on a compact manifold

*narrower* · compact $M$ for the approximation · Hausdorff assumed · not Milnor's perturbation

**Milnor (§6, Corollary 6.8, p. 37).** Any bounded smooth function on $M$ is a uniform limit of smooth functions without degenerate critical points, which can be chosen so that their derivatives of order at most $k$ on a given compact set approximate those of $f$.

**Proved in Lean.** (i) Let $M$ be a smooth manifold without boundary modelled on a finite-dimensional real normed space, $e : M \to \mathbb R^n$ smooth, a topological embedding with injective derivative, and $f : M \to \mathbb R$ smooth. Then $f + \langle a, e(\cdot)\rangle$ is a Morse function for almost every $a$, for any Haar measure. (ii) If $M$ is compact and Hausdorff, then for every smooth $f$, $\varepsilon > 0$, $r \in \mathbb N$, and finitely many smooth coordinate systems $y_j$, with values in a real normed space, with compact sets $K_j$ inside their ranges, there is a Morse function $g$ with $|g - f| < \varepsilon$ on $M$ and every derivative of order at most $r$ of $(g - f) \circ y_j^{-1}$ of norm $< \varepsilon$ on $K_j$; one can take $g = f + \langle a, e(\cdot)\rangle$, $e$ Mathlib's Whitney embedding.

- `Morse.ae_isMorseFunction_add_inner_comp` — Morse/Chapter4/Whitney.lean, line 216
- `Morse.exists_isMorseFunction_approx_of_compactSpace` — Morse/Chapter4/Whitney.lean, line 257

*What differs.*
- (ii) is for compact Hausdorff $M$ only, where Milnor's boundedness of $f$ is automatic; non-compact abstract manifolds would need a closed embedding into Euclidean space.
- The perturbation is $\langle a, e(\cdot)\rangle$ along an embedding, not Milnor's $L_p$ on an embedding with first coordinate $f$.

### V4.23. Lemma 6.9: the index of $L_p$

*restated* · $> 1/t$, not $\ge 1/t$ · the direction $p - q$ not normalized · the case $p = q$ included

**Milnor (§6, Lemma 6.9, p. 37).** At a non-degenerate critical point $\vec q$ of $L_{\vec p}$, the index is the number of focal points of $(M, \vec q)$ on the segment from $\vec q$ to $\vec p$, counted with multiplicity. The proof (p. 38): the index of $2(g_{ij} - t\,\vec v \cdot \vec\ell_{ij})$ is its number of negative eigenvalues, which, for $(g_{ij})$ the identity, is the number of eigenvalues of $(\vec v \cdot \vec\ell_{ij})$ that are $\ge 1/t$; compare Lemma 6.3.

*Milnor adds that an analogous statement in Part III, the Morse index theorem, will be of fundamental importance.*

**Proved in Lean.** (i) The index of $g - \ell_v$ is the number of principal curvatures in the direction $v$, counted with multiplicity, that are greater than $1$. (ii) At a critical point $q$ of $L_p$, the index of $L_p$ is the number of principal curvatures of $M$ at $q$ in the direction $p - q$ that are greater than $1$. (iii) If $k + w = n$ and $q$ is a non-degenerate critical point of $L_p$, the index of $L_p$ at $q$ is $\sum_{t \in [0, 1]} \mathrm{mult}_q(q + t(p - q))$, all but finitely many terms vanishing: the number of focal points of $(M, q)$ on the segment from $q$ to $p$, each counted with its multiplicity.

- `Morse.index_firstFF_sub_secondFF` — Morse/Chapter4/Curvature.lean, line 343
- `Morse.indexM_normSq_sub_eq_card` — Morse/Chapter4/Curvature.lean, line 386
- `Morse.indexM_normSq_sub_eq_finsum_focalMult` — Morse/Chapter4/Curvature.lean, line 404

*What differs.*
- The eigenvalues to count are those $> 1/t$, not $\ge 1/t$ as printed: equality would make $p$ a focal point of $(M, q)$, that is, $q$ degenerate (V4.11), and this is where non-degeneracy enters.
- The direction $p - q$ is not normalized: if $p - q = tv$ with $\|v\| = 1$, the curvatures in the direction $p - q$ are $t$ times those in the direction $v$, so “greater than $1$” is Milnor's “greater than $1/t$”. For $p = q$ the index is $0$ and the segment holds no focal point.
- The proof is Sylvester's law of inertia in an orthonormal eigenbasis of $S_v$, in which $g - \ell_v$ is $\sum_i (1 - \kappa_i)c_i^2$.

### V4.24. Reeb's theorem on a compact manifold

*hypotheses explicit* · Hausdorff assumed · exactly two critical points · $S^n$ with $n = \dim M$

**Milnor (§4, Theorem 4.1 (Reeb), p. 25).** A compact manifold carrying a differentiable function with only two critical points, both non-degenerate, is homeomorphic to a sphere.

**Proved in Lean.** Let $M$ be a compact Hausdorff smooth manifold without boundary modelled on a real normed space of finite dimension $n$, and $f : M \to \mathbb R$ smooth with exactly two critical points, both non-degenerate. Then $M$ is homeomorphic to the unit sphere $S^n \subseteq \mathbb R^{n+1}$.

- `Morse.reeb_of_compactSpace` — Morse/Chapter4/Whitney.lean, line 481

*What differs.*
- This is Theorem 4.1 in Milnor's own setting of an abstract compact manifold. It sits in this chapter because its proof goes through the Whitney embedding (V4.16): V3.6 applies to an embedded copy, the critical points and their non-degeneracy being carried over by V4.15.
- Hausdorffness, tacit in the book, is needed for the embedding; “only two” is read as exactly two, and $M$ has no boundary.

## Chapter 5

*Milnor §7, pp. 39–42: the Lefschetz theorem on hyperplane sections*

### V5.2. Milnor's form $Q'$, and multiplication by $i$

*stronger* · the sign change for the bilinear form · coordinate-free

**Milnor (§7, p. 39).** Writing $z^h = x^h + iy^h$ in a complex quadratic form $Q(z) = \sum b_{hj}z^hz^j$ of $k$ variables and taking real parts gives a real quadratic form $Q'$ in $2k$ variables. Since $Q(iz) = -Q(z)$, an orthogonal change of variables turns $Q'$ into $-Q'$.

**Proved in Lean.** For a complex vector space $V$ and a continuous complex-bilinear $B : V \times V \to \mathbb C$, $\mathrm{Re}\,B$ is a real bilinear form; for $B(z, z') = \sum b_{hj}z^hz'^j$ on $\mathbb C^k$ its quadratic form is Milnor's $Q'$. Multiplication by $i$ is a real-linear isomorphism $J$ with $J^2 = -1$ (inverse $-J$), and $\mathrm{Re}\,B(iv, iw) = -\mathrm{Re}\,B(v, w)$ for all $v$, $w$. On a complex inner product space the real inner product $\mathrm{Re}\langle v, w\rangle$, the Euclidean inner product of $\mathbb R^{2k}$ when $V = \mathbb C^k$, satisfies $\mathrm{Re}\langle iv, iw\rangle = \mathrm{Re}\langle v, w\rangle$: $J$ is orthogonal.

- `Morse.reBilin` — Morse/Chapter5/IndexBound.lean, line 265
- `Morse.reBilin_apply` — Morse/Chapter5/IndexBound.lean, line 269
- `Morse.reBilin_I_smul` — Morse/Chapter5/IndexBound.lean, line 275
- `Morse.reInner` — Morse/Chapter5/IndexBound.lean, line 325
- `Morse.reInner_I_smul` — Morse/Chapter5/IndexBound.lean, line 343
- `Morse.realMulI` — Morse/Chapter5/IndexBound.lean, line 242
- `Morse.complexStructureEquiv` — Morse/Chapter5/IndexBound.lean, line 163

*What differs.*
- The sign change is proved for the bilinear form $\mathrm{Re}\,B$, not only for the quadratic form $Q'$.
- Mathlib's Hermitian product is conjugate-linear in the first slot, Milnor's $\sum_\alpha a_\alpha\bar b_\alpha$ in the second; their real parts agree, and only real parts occur.

### V5.3. Assertion 1

*restated* · multiplicity as eigenspace dimension · eigenvalues of $Q'$ as nullities · coordinate-free

**Milnor (§7, Assertion 1, p. 39).** The eigenvalues of $Q'$ come in opposite pairs: with $e$, of multiplicity $\mu$, $-e$ is an eigenvalue of the same multiplicity. Milnor says this clearly follows from the orthogonal change of variables carrying $Q'$ into $-Q'$.

**Proved in Lean.** Let $V$ be a complex inner product space, $B$ a continuous complex-bilinear form on $V$ and $e \in \mathbb R$. Then $\mathrm{Re}\,B - e\,\mathrm{Re}\langle\cdot,\cdot\rangle$ and $\mathrm{Re}\,B + e\,\mathrm{Re}\langle\cdot,\cdot\rangle$ have the same nullity. If $A$ is a real-linear operator on $V$ with $\mathrm{Re}\langle Au, w\rangle = \mathrm{Re}\,B(u, w)$ for all $u$, $w$ (the matrix of $Q'$ in orthonormal real coordinates), then the $e$-eigenspace of $A$ is the null space of $\mathrm{Re}\,B - e\,\mathrm{Re}\langle\cdot,\cdot\rangle$, and the $e$- and $(-e)$-eigenspaces of $A$ have the same dimension.

- `Morse.nullity_reBilin_sub_smul_reInner_eq` — Morse/Chapter5/IndexBound.lean, line 363
- `Morse.eigenspace_eq_nullSpace_sub_smul_reInner` — Morse/Chapter5/IndexBound.lean, line 371
- `Morse.finrank_eigenspace_neg_eq` — Morse/Chapter5/IndexBound.lean, line 391

*What differs.*
- The step left to “clearly” is made explicit: $J$, orthogonal with $\mathrm{Re}\,B(Ju, Jw) = -\mathrm{Re}\,B(u, w)$, carries $\mathrm{Re}\,B - e\,\mathrm{Re}\langle\cdot,\cdot\rangle$ into $-(\mathrm{Re}\,B + e\,\mathrm{Re}\langle\cdot,\cdot\rangle)$, and a linear change of variables does not change the nullity.

### V5.4. Assertion 1 relative to an invariant form

*not in the book* · the form Assertion 2 needs · relative to $(g_{ij})$, not the identity

**Milnor (§7, p. 40).** Not stated. Assertion 1 concerns the eigenvalues of $Q'$ for the coordinate inner product of $\mathbb R^{2k}$; on p. 40 Milnor passes from it to focal points, which by Assertion 6.4 are governed by the second fundamental form relative to the first fundamental form $(g_{ij})$, not relative to the identity.

**Proved in Lean.** Let $E$ be a real normed space, $J$ a continuous real-linear map with $J^2 = -1$, $G$ a bilinear form with $G(Jv, Jw) = G(v, w)$ and $L$ a bilinear form with $L(Jv, Jw) = -L(v, w)$, for all $v$, $w$. Then for every real $t$ the forms $G - tL$ and $G + tL$ have the same nullity, and for every real $e$ the forms $L - eG$ and $L + eG$ have the same nullity.

- `Morse.nullity_sub_smul_eq_nullity_add_smul` — Morse/Chapter5/IndexBound.lean, line 174
- `Morse.nullity_sub_smul_eq_nullity_add_smul'` — Morse/Chapter5/IndexBound.lean, line 187

*What differs.*
- With $G = (g_{ij})$, which is $J$-invariant by the Cauchy–Riemann equations, and $L$ the second fundamental form in a normal direction $v$, the nullities of $G \mp tL$ are the multiplicities of $q \pm tv$ as focal points (Assertion 6.4).
- Assertion 1 gives the same conclusion only when the real coordinates are orthonormal at $q$, an assumption Milnor makes in §6 (p. 34) but not on p. 40. This is Assertion 1a of the exposition.

### V5.5. Real orthogonality to a complex subspace

*hypotheses explicit* · $TM_q$ a complex subspace · real orthogonality suffices · not used downstream

**Milnor (§7, proof of Assertion 2, p. 40).** Expanding the Hermitian product $\sum_\alpha w_\alpha(z)\bar v_\alpha$ in holomorphic coordinates as a constant plus a homogeneous quadratic $Q(z)$ plus higher terms, Milnor notes in a parenthesis that the linear terms vanish since $v$ is orthogonal to $M$.

**Proved in Lean.** Let $T$ be a complex linear subspace of a complex inner product space and $v$ a vector with $\mathrm{Re}\langle a, v\rangle = 0$ for every $a \in T$. Then $\langle a, v\rangle = 0$ for every $a \in T$.

- `Morse.inner_eq_zero_of_re_inner_eq_zero` — Morse/Chapter5/IndexBound.lean, line 351

*What differs.*
- The tangent space is a complex subspace and orthogonality is meant in the real sense; the lemma is what turns real orthogonality into the vanishing of the Hermitian products, which is the content of the parenthesis.
- It is stated and proved but not used: the formal route (V5.6–V5.11) avoids power series.

### V5.6. The Hessian of $L_p$ in holomorphic coordinates

*restated* · an explicit Hessian formula · first term $J$-invariant, second anti

**Milnor (§7, proof of Assertion 2, p. 40).** With $z^1, \dots, z^k$ complex coordinates for $M$ near $q$, $w_\alpha(z)$ the coordinates of the inclusion $M \to \mathbb C^n$ and $v$ a unit normal, the real inner product $w \cdot v = \mathrm{Re}\sum_\alpha w_\alpha\bar v_\alpha$ has the real expansion $\text{const} + Q'(x, y) + \text{higher terms}$, and clearly, Milnor says, the quadratic terms $Q'$ determine the second fundamental form of $M$ at $q$ in the normal direction $v$.

**Proved in Lean.** Let $V$ be a complex normed space, $F$ a complex inner product space, $w : V \to F$ complex $C^2$ on a neighbourhood of $q$ (in particular holomorphic there), and $p \in F$. Then the real Hessian at $q$ of $z \mapsto \|w(z) - p\|^2$ is $(\xi, \xi') \mapsto 2(\mathrm{Re}\langle dw_q\xi, dw_q\xi'\rangle + \mathrm{Re}\langle w(q) - p, d^2w_q(\xi, \xi')\rangle)$, where $dw_q$ and $d^2w_q$ are the complex first and second derivatives. The first term is unchanged by $(\xi, \xi') \mapsto (i\xi, i\xi')$, being the first fundamental form of $w$; the second changes sign, being the real part of a complex bilinear form.

- `Morse.hessian_normSq_sub_holomorphic` — Morse/Chapter5/IndexBound.lean, line 462

*What differs.*
- Milnor's remark is replaced by an explicit formula for the whole Hessian of $L_p$ in the chart. For $p = w(q) + tv$, $v$ a unit normal, the second inner product is $-2t\,Q'(\xi)$ on the diagonal, $Q$ being Milnor's quadratic part of $\sum_\alpha w_\alpha\bar v_\alpha$.

### V5.7. Assertion 2, in a holomorphic chart

*restated* · Hessians, not focal points · $n$ any vector · the chart bridge not formalized

**Milnor (§7, Assertion 2, p. 40).** On every normal line the focal points of $(M, q)$ come in pairs placed symmetrically about $q$: with $q + tv$, the point $q - tv$ is a focal point too, of the same multiplicity. The proof: the quadratic terms $Q'$ of $w \cdot v$ determine the second fundamental form in the direction $v$, and by Assertion 1 its eigenvalues occur in equal and opposite pairs.

**Proved in Lean.** With $V$, $F$, $w$, $q$ as in V5.6, for every $n \in F$ and every real $t$, the Hessians at $q$ of $\|w(\cdot) - (w(q) + tn)\|^2$ and of $\|w(\cdot) - (w(q) - tn)\|^2$ have the same nullity. $n$ need be neither normal nor a unit vector, and $q$ need not be critical.

- `Morse.nullity_hessian_normSq_sub_add_eq_sub` — Morse/Chapter5/IndexBound.lean, line 527

*What differs.*
- The statement concerns Hessians in a holomorphic chart. For a unit normal $n$ these nullities are the multiplicities of $w(q) \pm tn$ as focal points, by Assertion 6.4 and the Hessian formula of p. 36, which are formalized for real submanifolds of $\mathbb R^n$ (V4.9, V4.10); but a holomorphic chart of a complex submanifold is not identified with a chart of that real submanifold, so the passage to focal points is not verified.
- The proof: $J = i\cdot$ carries one Hessian into the other (V5.6), as in V5.4. Milnor's route through the eigenvalues of $Q'$ is not used.

### V5.8. The Andreotti–Frankel identity

*not in the book* · replaces the count of focal points · no Lemma 6.9 needed

**Milnor (§7, p. 41).** Not in Milnor's text. On p. 41 he bounds the index of $L_p$ at a critical point $q$ by counting focal points: by Lemma 6.9 it is the number of focal points of $(M, q)$ between $p$ and $q$; there are at most $2k$ on the whole normal line, distributed symmetrically about $q$ by Assertion 2, so at most $k$ between $p$ and $q$. The proof of §7 is credited to Andreotti and Frankel.

**Proved in Lean.** Let $G$, $L$, $H$ be bilinear forms on a real normed space and $J$ any map of it such that, for all $v$, $H(v, v) = G(v, v) - L(v, v)$, $G(Jv, Jv) = G(v, v)$ and $L(Jv, Jv) = -L(v, v)$. Then $H(Jv, Jv) = 2G(v, v) - H(v, v)$. On a complex vector space with $J = i\cdot$ and $L = \mathrm{Re}\,B$, $B$ complex bilinear, the condition on $L$ is automatic; on a complex inner product space with $G(v, v) = \|v\|^2$ it reads $H(iv, iv) = 2\|v\|^2 - H(v, v)$.

- `Morse.apply_J_apply_J_eq` — Morse/Chapter5/IndexBound.lean, line 200
- `Morse.apply_I_smul_apply_I_smul_eq` — Morse/Chapter5/IndexBound.lean, line 293
- `Morse.apply_I_smul_apply_I_smul_eq_two_mul_norm_sq_sub` — Morse/Chapter5/IndexBound.lean, line 406

*What differs.*
- Together with V5.9 it replaces Milnor's count of focal points on p. 41, which needs Lemmas 6.3 and 6.9 and Assertion 2 in its focal-point form.

### V5.9. The index bound

*not in the book* · $W \cap JW = 0$ · half the real dimension

**Milnor (§7, p. 41).** Not stated; it is the abstract form of the conclusion of p. 41, that the index of $L_p$ at $q$ is at most $k$.

**Proved in Lean.** Let $E$ be a finite-dimensional real normed space, $H$ a bilinear form and $J$ an injective real-linear map of $E$ with $H(v, v) + H(Jv, Jv) \ge 0$ for all $v$. Then $2 \cdot \mathrm{index}\,H \le \dim_{\mathbb R} E$. On a finite-dimensional complex vector space $V$, if $H(v, v) + H(iv, iv) \ge 0$ for all $v$, then $\mathrm{index}\,H \le \dim_{\mathbb C} V$.

- `Morse.two_mul_index_le_finrank` — Morse/Chapter5/IndexBound.lean, line 210
- `Morse.index_le_finrank_complex` — Morse/Chapter5/IndexBound.lean, line 257

*What differs.*
- If $H$ is negative definite on $W$, then $W \cap JW = 0$, since a non-zero $Jw \in W$ would make both $H(w, w)$ and $H(Jw, Jw)$ negative; so $2\dim W \le \dim E$.

### V5.10. The index bound for forms of Milnor's shape

*stronger* · no criticality assumed · no non-degeneracy assumed · only the shape of the Hessian

**Milnor (§7, p. 41).** The index of $L_p$ at a critical point $q$ is at most $k$, $M$ having complex dimension $k$.

**Proved in Lean.** Let $V$ be a complex vector space of finite dimension $k$, $G$ a bilinear form with $G(v, v) \ge 0$ and $G(iv, iv) = G(v, v)$, $B$ a continuous complex-bilinear form, and $H$ a bilinear form with $H(v, v) = G(v, v) - \mathrm{Re}\,B(v, v)$ for all $v$. Then $\mathrm{index}\,H \le k$. In particular, on a complex inner product space every form with quadratic form $\|v\|^2 - \mathrm{Re}\,B(v, v)$ has index at most $k$; and for any $f : V \to \mathbb R$ and $q \in V$ whose Hessian has, on the diagonal, the form $G - \mathrm{Re}\,B$, the Hessian has index at most $k$.

- `Morse.index_le_finrank_of_eq_sub_re` — Morse/Chapter5/IndexBound.lean, line 282
- `Morse.index_le_finrank_of_hermitian` — Morse/Chapter5/IndexBound.lean, line 416
- `Morse.index_hessian_le_finrank_complex` — Morse/Chapter5/IndexBound.lean, line 437

*What differs.*
- Neither criticality, nor non-degeneracy, nor any smoothness of $f$ is assumed; only the shape of the Hessian matters.
- The proof is V5.8 and V5.9: if $H(v, v) < 0$ then $H(iv, iv) = 2G(v, v) - H(v, v) > 0$. Milnor's count of focal points is not used.

### V5.11. The index of $L_p$ is at most $k$, in a holomorphic chart

*stronger* · $q$ need not be critical · no non-degeneracy, $dw_q$ arbitrary · in a chart, not on $M$

**Milnor (§7, proof of Theorem 7.2, p. 40).** Choose $p \in \mathbb C^n$ so that $L_p : M \to \mathbb R$ has no degenerate critical points; since $M$ is a closed subset of $\mathbb C^n$, each $M^a$ is compact. By Lemma 6.9 and Assertion 2 the index of $L_p$ at a critical point $q$ is at most $k$, so $M$ has the homotopy type of a CW-complex of dimension at most $k$.

**Proved in Lean.** Let $V$ be a complex vector space of finite dimension $k$, $F$ a complex inner product space, $w : V \to F$ complex $C^2$ on a neighbourhood of $q$, and $p \in F$. Then the Hessian at $q$ of $z \mapsto \|w(z) - p\|^2$ has index at most $k$.

- `Morse.index_hessian_normSq_sub_holomorphic_le` — Morse/Chapter5/IndexBound.lean, line 508

*What differs.*
- $q$ need not be a critical point, the Hessian need not be non-degenerate, and $dw_q$ need not be injective.
- The statement is about the Hessian in a holomorphic chart. When $w$ parametrizes $M$ near a critical point $w(q)$ of $L_p|M$, this Hessian is that of $L_p|M$ in the real coordinates $(x, y)$, and its index is the index of $L_p$ at $w(q)$ by the chart independence of §2 (V1.5); that identification needs $M$ as a real slice submanifold with $w^{-1}$ among its charts, which is not formalized.
- The proof: by V5.6 the Hessian $H$ satisfies $H(\xi, \xi) + H(i\xi, i\xi) = 4\|dw_q\xi\|^2 \ge 0$; then V5.9.

### V5.13. The index of $L_p$ on a complex submanifold

*stronger* · every critical point, degenerate or not · no focal points · tangent spaces invariant under $J$

**Milnor (§7, proof of Theorem 7.2, pp. 39–41).** For a complex manifold $M$ of complex dimension $k$, bianalytically embedded in $\mathbb C^n$, the index of $L_p$ at a non-degenerate critical point is $\le k$: the focal points of $(M, q)$ along a normal line come in pairs symmetric about $q$ (Assertions 1 and 2), and Lemma 6.9 counts those between $p$ and $q$.

**Proved in Lean.** Let $V$ be a finite-dimensional real inner product space and $J$ an orthogonal linear map of $V$ with $J^2 = -1$ (for $V = \mathbb C^m = \mathbb R^{2m}$: multiplication by $i$). A slice submanifold $N \subseteq V$ is called a *complex submanifold* (for $J$) if $J$ maps every tangent space $T_xN$ into itself. For such an $N$, every $p \in V$ and every critical point $q$ of $L_p = \|\cdot - p\|^2$ on $N$, degenerate or not, twice the index of $L_p$ at $q$ is at most $\dim_{\mathbb R}N$; so if $\dim_{\mathbb R}N = 2k$, the index is at most $k$.

- `Morse.IsOrthComplexStructure` — Morse/Chapter5/ComplexIndex.lean, line 60
- `Morse.IsComplexSubmanifold` — Morse/Chapter5/ComplexIndex.lean, line 74
- `Morse.two_mul_indexM_normSq_sub_le` — Morse/Chapter5/ComplexIndex.lean, line 169
- `Morse.indexM_normSq_sub_le` — Morse/Chapter5/Lefschetz.lean, line 262

*What differs.*
- "Complex submanifold" is a slice submanifold of $\mathbb R^{2m}$ whose tangent spaces are invariant under $J$; a bianalytically embedded complex manifold is one, and nothing else is used.
- The bound is for the Hessian of $L_p$ on the real submanifold, in a slice chart: with $J'$ the complex structure read in the chart, $H(J'\xi, J'\xi) = 4\|dx\,\xi\|^2 - H(\xi, \xi)$, so a negative definite subspace meets its image under $J'$ only in $0$. This is the bridge that V5.7 and V5.11 lacked.

### V5.14. The homology of a slab without critical points of a given index

*not in the book* · compact slabs suffice

**Milnor (§§3, 5; used on pp. 39, 42).** §7 applies Theorems 3.1 and 3.2 to $L_p$ on $M$ and to $1/L_p$ on $V$, whose sublevel sets need not be compact.

**Proved in Lean.** Let $N$ be a slice submanifold of a finite-dimensional real inner product space, $F$ a smooth function on the ambient space, $f = F|N$, and $\mathbb k$ a field. Let $a \le b \le a_0$ be such that $f^{-1}(-\infty, a_0]$ is compact (or only the slab $f^{-1}[\ell, a_0]$, for some $\ell \le a$), every critical point of $f$ in it is non-degenerate, and $a$ and $b$ are not critical values. If no critical point $q$ with $a < f(q) < b$ has index $j$, then $H_j(N^b, N^a; \mathbb k) = 0$, where $N^c = f^{-1}(-\infty, c]$. A Morse function on $N$ which is bounded below by $0$ and has compact sublevel sets has regular values $a_0 < 0 \le a_1 \le a_2 \le \dots$ tending to infinity.

- `Morse.critValuesIn` — Morse/Chapter5/Lefschetz.lean, line 82
- `Morse.subsingleton_subsetHomology_sublevel` — Morse/Chapter5/Lefschetz.lean, line 92
- `Morse.subsingleton_subsetHomology_slab` — Morse/Chapter5/LefschetzSlab.lean, line 250
- `Morse.exists_regular_levels` — Morse/Chapter5/Lefschetz.lean, line 201

*What differs.*
- If no critical point between two regular levels has index $j$, then $H_j(N^b, N^a) = 0$ over a field, by induction on the critical values, from Theorems 3.1, 3.2 and Remark 3.3 with the exact sequences of triples. Only the slab between the levels need be compact, which is what $-L_p$ requires.

### V5.15. Theorem 7.2

*restated* · closed, complex tangent spaces · cells of dimension $\le k$ · a countable cell complex

**Milnor (§7, Theorem 7.2, p. 39).** A complex manifold of complex dimension $k$, bianalytically embedded as a closed subset of $\mathbb C^n$, has the homotopy type of a $k$-dimensional CW-complex.

**Proved in Lean.** Let $M \subseteq \mathbb R^n$ be a slice submanifold of dimension $2k$ which is closed in $\mathbb R^n$ and complex for an orthogonal $J$ with $J^2 = -1$ (V5.13). Then $M$ has the homotopy type of a countable cell complex (VA.18) all of whose cells have dimension at most $k$.

- `Morse.theorem_7_2` — Morse/Chapter5/Lefschetz.lean, line 276

*What differs.*
- For a closed slice submanifold of $\mathbb R^n$ of dimension $2k$ with complex tangent spaces. "$k$-dimensional" is "of dimension at most $k$". The complex is the countable tower of cell attachments of VA.18, with arbitrary attaching maps.
- $L_p$ is a Morse function for almost every $p$ (V4.12), with compact sublevel sets because $M$ is closed, and its critical points have index $\le k$ (V5.13).

### V5.16. Theorem 7.1 (Andreotti and Frankel), over a field

*narrower* · coefficients in a field · a closed complex submanifold

**Milnor (§7, Theorem 7.1, p. 39).** If $M \subset \mathbb C^n$ is a non-singular affine algebraic variety of real dimension $2k$, then $H_i(M; \mathbb Z) = 0$ for $i > k$.

**Proved in Lean.** Under the hypotheses of V5.15, $H_i(M; \mathbb k) = 0$ for every field $\mathbb k$ and every $i > k$.

- `Morse.theorem_7_1` — Morse/Chapter5/Lefschetz.lean, line 314

*What differs.*
- Over every field, for the submanifolds of V5.15; that a non-singular affine variety is one is not formalized. The proof uses the filtration by sublevel sets, not cellular homology.

### V5.17. Hyperplane sections, for an abstract pair

*restated* · Hypothesis (N), fixing $A$ · no Lefschetz duality · field coefficients

**Milnor (§7, pp. 41–42).** Corollary 7.3 is proved from the exact sequence of the pair $(V, V \cap P)$, Lefschetz duality, and Theorem 7.1 for $V - (V \cap P)$. Theorem 7.4 is proved from "the hypothesis that some neighborhood $U$ of $V \cap P$ can be deformed into $V \cap P$ within $V$".

**Proved in Lean.** Let $X$ be a compact space, $A \subseteq X$ closed, $M$ as in V5.15, and $e$ a homeomorphism of $M$ onto $X \setminus A$ such that $\|e^{-1}(y)\| \to \infty$ as $y \to A$. *Hypothesis (N)* for $A$ in $X$: there are an open $U \supseteq A$ and a homotopy $H : [0, 1] \times U \to X$ with $H_0$ the inclusion, $H_1(U) \subseteq A$, and $H_t(a) = a$ for all $t$ and all $a \in A$. Under Hypothesis (N), for every field $\mathbb k$: $H_r(X, A; \mathbb k) = 0$ for $r < k$; hence the map $H_r(A; \mathbb k) \to H_r(X; \mathbb k)$ induced by the inclusion is bijective for $r + 1 < k$ and surjective for $r < k$. On the way: at a non-degenerate critical point of $L_p$ on $M$, the function $-L_p$ has index at least $k$.

- `Morse.HypothesisN` — Morse/Chapter5/HyperplaneSection.lean, line 195
- `Morse.le_indexM_neg_normSq_sub` — Morse/Chapter5/HyperplaneSection.lean, line 215
- `Morse.subsingleton_subsetHomology_univ_of_section` — Morse/Chapter5/HyperplaneSection.lean, line 252
- `Morse.corollary_7_3_of_section` — Morse/Chapter5/HyperplaneSection.lean, line 402

*What differs.*
- For $X$ compact, $A$ closed, and $X \setminus A$ a closed complex submanifold of $\mathbb C^n$ going to infinity at $A$: under Hypothesis (N), $H_r(X, A) = 0$ for $r < k$, so $H_r(A) \to H_r(X)$ is bijective for $r < k - 1$ and onto for $r = k - 1$.
- Instead of duality: a neighbourhood $V_R$ of $A$ deforms into $A$, and $H_r(X, V_R)$ vanishes by excision and Morse theory for $-L_p$ on a compact slab, whose critical points have index $\ge k$. The deformation must keep $A$ pointwise fixed, which Milnor does not say.

### V5.18. Corollary 7.3 (Lefschetz), over a field

*narrower* · field coefficients · Hypothesis (N) assumed · pure dimension, said · the hyperplane $z_0 = 0$

**Milnor (§7, Corollary 7.3, p. 41).** Let $V$ be an algebraic variety of complex dimension $k$ in $\mathbb CP_n$ and $P$ a hyperplane containing the singular points of $V$. Then the inclusion $V \cap P \to V$ induces isomorphisms of homology groups in dimensions less than $k - 1$, and is onto in dimension $k - 1$.

**Proved in Lean.** Let $V \subseteq \mathbb CP^n$ (V3.41) be closed and $P$ the hyperplane $z_0 = 0$, the set of projections $Q$ with $Q_{00} = 0$. The *affine part* of $V$ is the set of $u \in \mathbb C^n = \mathbb R^{2n}$ for which the projection onto the line of $(1, u)$ belongs to $V$; it is homeomorphic to $V \setminus P$, and its points go to infinity as their images approach $V \cap P$. Suppose the affine part is a slice submanifold of $\mathbb R^{2n}$ of dimension $2k$, complex for multiplication by $i$, and suppose Hypothesis (N) for $V \cap P$ in $V$ (V5.17). Then for every field $\mathbb k$ the map $H_r(V \cap P; \mathbb k) \to H_r(V; \mathbb k)$ induced by the inclusion is bijective for $r < k - 1$ and surjective for $r = k - 1$.

- `Morse.CP.affinePart` — Morse/Chapter5/ProjectiveSection.lean, line 218
- `Morse.CP.hyperplaneSection` — Morse/Chapter5/ProjectiveSection.lean, line 221
- `Morse.CP.affineHomeomorph` — Morse/Chapter5/ProjectiveSection.lean, line 229
- `Morse.CP.tendsto_norm_affineHomeomorph_symm` — Morse/Chapter5/ProjectiveSection.lean, line 253
- `Morse.corollary_7_3` — Morse/Chapter5/ProjectiveSection.lean, line 291

*What differs.*
- For a closed $V \subseteq \mathbb CP^n$ whose affine part is a complex submanifold of $\mathbb C^n$ of complex dimension $k$: this replaces "algebraic variety with singular points in $P$" and includes pure dimension, which Milnor omits and the statement needs.
- Hypothesis (N), which Milnor draws from triangulability, is assumed. Another hyperplane is brought to $z_0 = 0$ by a unitary change of coordinates, not formalized.

### V5.19. Theorem 7.4 (Lefschetz)

*restated* · as a compression criterion · Hypothesis (N) assumed · $1/(1 + L_p)$ in place of $1/L_p$

**Milnor (§7, Theorem 7.4, pp. 41–42).** Under the same hypotheses, the relative homotopy group $\pi_r(V, V \cap P)$ is zero for $r < k$. The proof uses $f = 0$ on $V \cap P$ and $f = 1/L_p$ elsewhere, whose critical points have index $\ge k$, and a neighbourhood of $V \cap P$ that deforms into $V \cap P$ (from the triangulability of algebraic varieties).

**Proved in Lean.** Under the hypotheses of V5.18: for $r < k$, every continuous map $h : I^r \to V$ is homotopic, relative to $h^{-1}(V \cap P)$, to a map into $V \cap P$; the same holds for maps from any compact space that admits a continuous injection into a real vector space of dimension $< k$, and for the abstract pair $(X, A)$ of V5.17. Consequently, for every $x \in V \cap P$, the map $\pi_i(V \cap P, x) \to \pi_i(V, x)$ induced by the inclusion is bijective for $i + 1 < k$ and surjective for $i < k$.

- `Morse.theorem_7_4_of_section` — Morse/Chapter5/LefschetzHomotopy.lean, line 349
- `Morse.theorem_7_4` — Morse/Chapter5/LefschetzHomotopy.lean, line 551
- `Morse.theorem_7_4_of_embedding` — Morse/Chapter5/LefschetzHomotopy.lean, line 531
- `Morse.theorem_7_4_bijective` — Morse/Chapter5/LefschetzHomotopy.lean, line 559
- `Morse.theorem_7_4_surjective` — Morse/Chapter5/LefschetzHomotopy.lean, line 573

*What differs.*
- Relative homotopy groups are not in Mathlib; the statement is that every map $I^r \to V$, $r < k$, is homotopic, relative to the preimage of $V \cap P$, to a map into $V \cap P$. It gives $\pi_i(V \cap P) \to \pi_i(V)$ bijective for $i < k - 1$ and onto for $i = k - 1$.
- Milnor's $1/L_p$ is infinite at $p$; $1/(1 + L_p)$ is used. The maps are pushed past the critical levels by the lemma of Chapter 13 (V13.13) on a compact slab.

## Chapter 6

*Milnor §§8–9, pp. 43–54: covariant differentiation, the curvature tensor*

### V6.1. Tangent spaces, the projection $P_q$, and vector fields

*narrower* · $N \subseteq V$ with the induced metric · tangent vectors are vectors of $V$

**Milnor (§8, pp. 43–44).** Milnor works on an abstract smooth manifold $M$, with tangent spaces $TM_p$, vector fields $X$, and directional derivatives $X_pf$ of real functions $f$ in the direction of a tangent vector $X_p$.

**Proved in Lean.** In the embedded setting, $V$ is a finite-dimensional real inner product space and $N \subseteq V$ a slice submanifold, closed or not, with the induced metric. $T_qN \subseteq V$ is the range of the derivative at $q$ of the inclusion $N \to V$, and $P_q$ is the orthogonal projection of $V$ onto $T_qN$. For $F : N \to E$ into a normed space, the linear map $dN\,F\,q : V \to E$ is the derivative of $F$ at $q$ read on ambient vectors: on $v \in T_qN$ it is $dF_q(v)$, and if $F = G$ on $N$ near $q$ for some $G : V \to E$ differentiable at $q$, then $dN\,F\,q\,v = dG_q(v)$ for $v \in T_qN$. A vector field is a map $X : N \to V$ with $X(q) \in T_qN$ for every $q$, smooth if it is smooth as a map $N \to V$. The map $q \mapsto P_q$ is smooth, so every tangent vector $u$ at a point extends to the smooth vector field $q \mapsto P_qu$.

- `Morse.tangentSubspace` — Morse/Chapter1/ManifoldSubmanifold.lean, line 294
- `Morse.tanProj` — Morse/Chapter6/Projection.lean, line 433
- `Morse.dN` — Morse/Chapter6/Projection.lean, line 230
- `Morse.dN_eq_fderiv` — Morse/Chapter6/Projection.lean, line 265
- `Morse.IsTangentField` — Morse/Chapter6/Submanifold.lean, line 117
- `Morse.contMDiff_tanProj` — Morse/Chapter6/Projection.lean, line 534
- `Morse.projField` — Morse/Chapter6/Submanifold.lean, line 120
- `Morse.projField_apply_of_mem` — Morse/Chapter6/Submanifold.lean, line 133

*What differs.*
- The substance of §§8–9 is verified for submanifolds of a Euclidean space with the induced metric. Every Riemannian manifold is isometric to such an $N$ by Nash's embedding theorem, which is neither in Mathlib nor proved here, so these are statements about embedded manifolds.
- That every tangent vector extends to a smooth vector field on all of $N$, which arguments chart by chart take for granted, is proved: in a slice chart with parametrization $x$, $P_{x(u)} = A(A^{\mathsf T}A)^{-1}A^{\mathsf T}$ with $A = dx_u$ injective, which is smooth in $A$.

### V6.3. Affine connections on an abstract manifold

*restated* · Mathlib's covariant derivative · (2), (4) where differentiable · (1) a separate class

**Milnor (§8, pp. 43–44).** An affine connection at $p$ is a rule giving, for a tangent vector $X_p$ and a vector field $Y$, a tangent vector $X_p \vdash Y$ at $p$, the covariant derivative of $Y$ along $X_p$; it is bilinear and satisfies $X_p \vdash (fY) = (X_pf)Y_p + f(p)\,X_p \vdash Y$. A global connection is such a rule at every point subject to the smoothness condition (1); it then satisfies (2) bilinearity, (3) $(fX) \vdash Y = f(X \vdash Y)$ and (4) $X \vdash (fY) = (Xf)Y + f(X \vdash Y)$, and (1)–(4) may serve as the definition.

*A footnote identifies $X \vdash Y$ with Nomizu's $\nabla_XY$.*

**Proved in Lean.** Let $M$ be a smooth manifold in Mathlib's sense, modelled on a real normed space, and $\nabla$ a Mathlib covariant derivative on its tangent bundle, $X_p \vdash Y$ being the value at $X_p$ of the linear map $\nabla Y(p) : T_pM \to T_pM$. Then Milnor's (3), $(fX) \vdash Y = f(X \vdash Y)$, holds at every point; (2), additivity in $Y$, holds at every point where both summands are differentiable; and (4), $X \vdash (fY) = (Xf)Y + f(X \vdash Y)$, holds at every point where $f$ and $Y$ are differentiable. Dependence on $X_p$ only, and linearity in $X_p$, are part of the definition.

- `Morse.cov_smul_left` — Morse/Chapter6/Connection.lean, line 91
- `Morse.cov_add_right` — Morse/Chapter6/Connection.lean, line 96
- `Morse.cov_smul_right` — Morse/Chapter6/Connection.lean, line 104

*What differs.*
- Milnor's connection is Mathlib's `CovariantDerivative` on the tangent bundle, and his smoothness condition (1) is the separate class `ContMDiffCovariantDerivative`.
- Mathlib's object is defined on all sections and is unconstrained on sections not differentiable at the point, so (2) and (4) hold where the sections involved are differentiable.

### V6.4. The connection of the induced metric, and rules (1)–(4)

*narrower* · the induced connection only · one global formula, no Christoffel · (2), (4) where differentiable

**Milnor (§8, p. 44).** A global affine connection satisfies (1) $X \vdash Y$ is smooth when $X$ and $Y$ are smooth vector fields; (2) $X \vdash Y$ is bilinear in $X$ and $Y$; (3) $(fX) \vdash Y = f(X \vdash Y)$; (4) $X \vdash (fY) = (Xf)Y + f(X \vdash Y)$. In local coordinates it is determined by its Christoffel symbols, $\partial_i \vdash \partial_j = \sum_k \Gamma^k_{ij}\partial_k$.

**Proved in Lean.** In the embedded setting put $v \vdash Y = P_q(dY_q(v))$ for $v \in T_qN$ and $Y : N \to V$, and $(X \vdash Y)(q) = P_q(dY_q(X(q)))$. Then $X \vdash Y$ is tangent to $N$ at every point, and: (1) $X \vdash Y$ is smooth when $X$ is a smooth vector field and $Y$ is smooth; (2) it is additive in $X$, and additive in $Y$ at every point where both summands are differentiable; (3) $(fX) \vdash Y = f(X \vdash Y)$ for every function $f$; (4) at $q$, $X \vdash (fY) = (Xf)Y + f(X \vdash Y)$ with $Xf = df_q(X(q))$, when $f$ and $Y$ are differentiable at $q$ and $X(q)$, $Y(q)$ are tangent.

- `Morse.covAt` — Morse/Chapter6/Submanifold.lean, line 141
- `Morse.leviCivita` — Morse/Chapter6/Submanifold.lean, line 145
- `Morse.contMDiff_leviCivita` — Morse/Chapter6/Submanifold.lean, line 224
- `Morse.leviCivita_add_left` — Morse/Chapter6/Submanifold.lean, line 162
- `Morse.leviCivita_add_right` — Morse/Chapter6/Submanifold.lean, line 172
- `Morse.leviCivita_smul_left` — Morse/Chapter6/Submanifold.lean, line 167
- `Morse.leviCivita_smul_right` — Morse/Chapter6/Submanifold.lean, line 180

*What differs.*
- Only the connection $P(dY(X))$ of a submanifold with the induced metric is constructed; it is given by one global formula, with no Christoffel symbols and no patching of charts.
- Additivity in $Y$ and the rule (4) need differentiability at the point, which for Milnor's smooth fields is automatic.

### V6.5. Covariant derivative along a curve

*narrower* · $DX/dt = P(X')$ · embedded $N$, induced connection · differentiability at $t$

**Milnor (§8, pp. 45–46).** A vector field $V$ along a parametrized curve $c$ assigns to each $t$ a tangent vector $V_t \in TM_{c(t)}$, smoothly; the velocity field is $dc/dt = c_*(d/dt)$. Given a connection, the covariant derivative $V \mapsto DV/dt$ is characterized by three axioms: (a) $D(V + W)/dt = DV/dt + DW/dt$; (b) $D(fV)/dt = (df/dt)V + f\,DV/dt$ for a smooth real function $f$ on $\mathbb R$; (c) if $V$ is induced by a vector field $Y$, $V_t = Y_{c(t)}$, then $DV/dt$ is the covariant derivative of $Y$ in the direction of the velocity vector of $c$.

**Proved in Lean.** For a curve $c : \mathbb R \to N$, a vector field along $c$ is a map $X : \mathbb R \to V$ with $X(t) \in T_{c(t)}N$ for all $t$; the velocity $c'(t)$ is tangent when $c$ is smooth; and $DX/dt\,(t) = P_{c(t)}(X'(t))$. Then (a) $D(X + Y)/dt = DX/dt + DY/dt$ at $t$ when $X$, $Y$ are differentiable at $t$; (b) $D(fX)/dt = f'X + f\,DX/dt$ at $t$ when $f$, $X$ are differentiable at $t$ and $X(t)$ is tangent; (c) if $c$ is smooth and $Y : N \to V$ is differentiable at $c(t)$, then $D(Y \circ c)/dt\,(t) = c'(t) \vdash Y$.

- `Morse.velocity` — Morse/Chapter6/Parallel.lean, line 94
- `Morse.IsFieldAlong` — Morse/Chapter6/Parallel.lean, line 97
- `Morse.covDeriv` — Morse/Chapter6/Parallel.lean, line 101
- `Morse.deriv_mem_tangentSubspace` — Morse/Chapter6/Projection.lean, line 646
- `Morse.covDeriv_add` — Morse/Chapter6/Parallel.lean, line 112
- `Morse.covDeriv_smul` — Morse/Chapter6/Parallel.lean, line 119
- `Morse.covDeriv_comp` — Morse/Chapter6/Parallel.lean, line 128

*What differs.*
- Only for the induced connection of a submanifold, where the covariant derivative along a curve is the projection of the ordinary derivative. Milnor's fields along curves are smooth by definition; the formal axioms need only differentiability at $t$.

### V6.6. Lemma 8.1

*narrower* · embedded $N$, induced connection · an ambient frame, not a chart

**Milnor (§8, Lemma 8.1, p. 46).** Exactly one operation $V \mapsto DV/dt$ satisfies (a), (b) and (c). The proof writes $V = \sum_j v^j\partial_j$ in a local coordinate system and derives $DV/dt = \sum_k (dv^k/dt + \sum_{i,j} (du^i/dt)\Gamma^k_{ij}v^j)\partial_k$; conversely, defining $DV/dt$ by this formula, (a), (b) and (c) are not difficult to verify.

*The scan prints it as “Lemma 0.1”.*

**Proved in Lean.** Let $c$ be a smooth curve in $N$. Call an operation $D$ on maps $\mathbb R \to V$ admissible if it satisfies (a) for smooth fields along $c$, (b) for smooth $f$ and smooth fields along $c$, and (c) for smooth vector fields $Y$ on $N$. Then $X \mapsto P(X')$ of V6.5 is admissible, and every admissible $D$ agrees with it on every smooth field along $c$.

- `Morse.IsCovDerivAlong` — Morse/Chapter6/Parallel.lean, line 148
- `Morse.isCovDerivAlong_covDeriv` — Morse/Chapter6/Parallel.lean, line 158
- `Morse.IsCovDerivAlong.eq_covDeriv` — Morse/Chapter6/Parallel.lean, line 215

*What differs.*
- Only for the induced connection of a submanifold.
- Instead of a chart, a field along $c$ is expanded as $X = \sum_i \langle e_i, X\rangle\,(E_i \circ c)$ in the smooth fields $E_i(q) = P_qe_i$, $e_i$ an orthonormal basis of $V$, and (a)–(c) determine $DX/dt$. This avoids what the coordinate proof leaves implicit: locality in $t$, and the extension of the coordinate fields to all of $M$.

### V6.7. Global solutions of linear equations

*narrower* · global existence for skew coefficients · uniqueness for every linear equation

**Milnor (§8, proof of Lemma 8.2, p. 47).** The differential equations $dv^k/dt + \sum_{i,j} (du^i/dt)\Gamma^k_{ij}v^j = 0$ have solutions uniquely determined by their initial values; since the equations are linear, Milnor says, the solutions can be defined for all relevant values of $t$, citing Graves.

**Proved in Lean.** Let $A : \mathbb R \to \mathrm{End}(E)$ be continuous. (i) On a real normed space $E$, two solutions of $x' = A(t)x$ on an open interval, or on $\mathbb R$, that agree at one time agree everywhere. (ii) If $E$ is a complete real inner product space and $\langle A(t)x, x\rangle = 0$ for all $t$ and $x$, then for every $t_0$ and $x_0$ there is a solution on all of $\mathbb R$ with $x(t_0) = x_0$.

- `Morse.linearODE_eqOn` — Morse/Chapter6/LinearODE.lean, line 63
- `Morse.linearODE_eq` — Morse/Chapter6/LinearODE.lean, line 72
- `Morse.exists_skewLinearODE` — Morse/Chapter6/LinearODE.lean, line 205

*What differs.*
- Mathlib has local existence (Picard–Lindelöf) and Grönwall uniqueness only. Global existence is proved only for skew-adjoint coefficients, the case parallel transport needs: their solutions have constant norm, so the equation may be truncated outside a ball and solved on any compact interval, and solutions on nested intervals are glued by (i).

### V6.8. Lemma 8.2: parallel fields

*narrower* · embedded $N$, induced connection · any initial time · unique among differentiable fields

**Milnor (§8, Lemma 8.2, p. 47).** Along a curve $c$, every tangent vector $V_0$ at $c(0)$ extends to exactly one parallel vector field $V$, parallel meaning that $DV/dt$ vanishes identically; $V_t$ is then said to come from $V_0$ by parallel translation along $c$.

**Proved in Lean.** A field $X$ along $c$ is parallel if it is differentiable and $DX/dt = 0$ at every $t$. For a smooth curve $c$ in $N$, every $t_0 \in \mathbb R$ and every $v \in T_{c(t_0)}N$ there is exactly one parallel field $X$ along $c$ with $X(t_0) = v$; it is defined on all of $\mathbb R$, and it is smooth.

- `Morse.IsParallel` — Morse/Chapter6/Parallel.lean, line 224
- `Morse.exists_unique_isParallel` — Morse/Chapter6/Parallel.lean, line 317
- `Morse.IsParallel.contDiff` — Morse/Chapter6/Parallel.lean, line 323

*What differs.*
- Only for the induced connection of a submanifold; for it, any initial time is allowed, and uniqueness holds among differentiable fields, not only smooth ones.
- A tangent field is parallel iff $X' = P'X$, where $P(t) = P_{c(t)}$, and uniqueness is V6.7 (i). That equation has no a priori bound, so existence solves instead $X' = (P'P - PP')X$, whose coefficient is skew-adjoint; since $PP'P = 0$, a solution that starts tangent stays tangent, and is then parallel.
- On an abstract manifold the coordinate equations would also have to be patched from chart to chart along the curve; here there is one equation in $V$.

### V6.9. Parallel translation is a linear isometry

*stronger* · compatibility proved, not assumed · linear, onto, transitive · embedded $N$, induced connection

**Milnor (§8, p. 47).** After naming parallel translation, Milnor calls a connection on a Riemannian manifold compatible with the metric when parallel translation preserves inner products, that is, when $\langle P, P'\rangle$ is constant along $c$ for any two parallel fields $P$, $P'$ along any curve $c$.

**Proved in Lean.** For parallel fields $X$, $Y$ along any curve $c$ in $N$, $\langle X(t), Y(t)\rangle$ does not depend on $t$: the induced connection is compatible with the metric in Milnor's sense. For a smooth curve $c$ and times $t_0$, $t_1$, the map sending $v \in T_{c(t_0)}N$ to the value at $t_1$ of the parallel field through $v$ at $t_0$ is a linear isometry of $T_{c(t_0)}N$ onto $T_{c(t_1)}N$; it is the identity when $t_1 = t_0$, and translating from $t_0$ to $t_1$ and then to $t_2$ is translating from $t_0$ to $t_2$.

- `Morse.IsParallel.inner_eq` — Morse/Chapter6/Parallel.lean, line 340
- `Morse.parallelTransport` — Morse/Chapter6/Parallel.lean, line 430
- `Morse.inner_parallelTransport` — Morse/Chapter6/Parallel.lean, line 456
- `Morse.parallelTransport_self` — Morse/Chapter6/Parallel.lean, line 440
- `Morse.parallelTransport_trans` — Morse/Chapter6/Parallel.lean, line 446

*What differs.*
- Compatibility, a definition in the book, is proved for the induced connection.
- Linearity, surjectivity and transitivity of parallel translation are stated and proved; the book uses them without comment.

### V6.10. Lemma 8.3

*narrower* · embedded $N$, induced connection · no parallel frame · fields differentiable at $t$

**Milnor (§8, Lemma 8.3, p. 47).** For a connection compatible with the metric and any two vector fields $V$, $W$ along $c$, $\frac{d}{dt}\langle V, W\rangle = \langle DV/dt, W\rangle + \langle V, DW/dt\rangle$. The proof expands $V$ and $W$ in parallel fields $P_1, \dots, P_n$ along $c$ which are orthonormal at one point, and hence at every point.

**Proved in Lean.** For any curve $c$ in $N$ and fields $X$, $Y$ along $c$ differentiable at $t$, the derivative of $\langle X, Y\rangle$ at $t$ is $\langle DX/dt, Y\rangle + \langle X, DY/dt\rangle$.

- `Morse.hasDerivAt_inner_covDeriv` — Morse/Chapter6/Parallel.lean, line 136

*What differs.*
- Only for the induced connection. Milnor's proof needs Lemma 8.2 for $n$ initial vectors and the smoothness of the coefficients $\langle V, P_i\rangle$; here the product rule in $V$ and $\langle PX', Y\rangle = \langle X', Y\rangle$ for tangent $Y$ suffice, so Lemma 8.3 comes before Lemma 8.2.

### V6.11. Corollary 8.4

*restated* · abstractly, Corollary 8.4 is the definition · proved for the induced connection

**Milnor (§8, Corollary 8.4, p. 48).** For vector fields $Y$, $Y'$ on $M$ and a tangent vector $X_p$, $X_p\langle Y, Y'\rangle = \langle X_p \vdash Y, Y'_p\rangle + \langle Y_p, X_p \vdash Y'\rangle$, by Lemma 8.3 along a curve with velocity $X_p$ at $t = 0$.

**Proved in Lean.** Embedded: if $Y$, $Y'$ are differentiable at $q$ with $Y(q)$, $Y'(q)$ tangent, and $v \in T_qN$, then $v\langle Y, Y'\rangle = \langle v \vdash Y, Y'(q)\rangle + \langle Y(q), v \vdash Y'\rangle$. Abstract: on a manifold whose tangent bundle carries a Riemannian metric (Mathlib's `RiemannianBundle`), a covariant derivative is called compatible if Milnor's identity holds at every point for all vector fields differentiable there; for a finite-dimensional model space and a $C^1$ metric this is Mathlib's `IsMetricCompatible`.

- `Morse.dN_inner_eq_covAt` — Morse/Chapter6/Submanifold.lean, line 191
- `Morse.IsCompatible` — Morse/Chapter6/Connection.lean, line 178
- `Morse.isCompatible_iff_isMetricCompatible` — Morse/Chapter6/Connection.lean, line 185

*What differs.*
- Milnor's definition of compatibility, that parallel translation preserves inner products, cannot be stated for Mathlib's connections, which have no parallel transport; on an abstract manifold Corollary 8.4 is taken as the definition instead, and shown to agree with Mathlib's metric compatibility.
- In the embedded setting it is proved, at points where the fields are differentiable.

### V6.12. The second fundamental form

*not in the book* · the tool for symmetry and curvature · $D_v$ self-adjoint

**Milnor (§6, p. 33).** Not in §§8–9. Milnor meets the second fundamental form in §6, as the normal component of $\partial^2\vec x/\partial u^i\partial u^j$ in a fixed coordinate system, without an invariant definition.

**Proved in Lean.** For $v \in T_qN$ let $D_v$ be the derivative of $q \mapsto P_q$ in the direction $v$, and $\mathrm{II}_q(v, w) = D_vw$. For every vector field $W$ differentiable at $q$, $\mathrm{II}_q(v, W(q)) = dW_q(v) - P_q(dW_q(v))$, the normal part of $dW_q(v)$, which therefore depends only on $v$ and $W(q)$. For $v, w \in T_qN$, $\mathrm{II}_q(v, w)$ is normal to $N$ and $\mathrm{II}_q(v, w) = \mathrm{II}_q(w, v)$; and $\langle \mathrm{II}_q(v, x), y\rangle = \langle x, \mathrm{II}_q(v, y)\rangle$ for all $x, y \in V$: $D_v$ is self-adjoint, maps $T_qN$ to normal vectors and normal vectors to $T_qN$.

- `Morse.secondFundForm` — Morse/Chapter6/Submanifold.lean, line 241
- `Morse.secondFundForm_eq_sub_tanProj` — Morse/Chapter6/Submanifold.lean, line 246
- `Morse.sub_tanProj_dN_eq_of_eq` — Morse/Chapter6/Submanifold.lean, line 258
- `Morse.secondFundForm_mem_orthogonal` — Morse/Chapter6/Submanifold.lean, line 272
- `Morse.dN_tanProj_mem_of_mem_orthogonal` — Morse/Chapter6/Projection.lean, line 618
- `Morse.inner_secondFundForm_comm` — Morse/Chapter6/Submanifold.lean, line 277
- `Morse.secondFundForm_comm` — Morse/Chapter6/Submanifold.lean, line 330

*What differs.*
- No counterpart in §§8–9: it is what makes the symmetry of the connection, the tensor property of $R$ and Lemma 9.3 short consequences in the embedded setting.
- The symmetry is proved in a slice chart $\sigma$: $T_xN$ is the kernel of $d(\sigma_2)_x$, so $d(\sigma_2)_x \circ P_x = 0$ on $N$, and differentiating along $N$ gives $d(\sigma_2)_q(\mathrm{II}(v, w)) = -d^2(\sigma_2)_q(v, w)$, symmetric in $v$ and $w$.

### V6.13. Definition 8.5: symmetric connections

*hypotheses explicit* · symmetric = torsion-free · the ambient bracket is tangent · differentiability at the point

**Milnor (§8, Definition 8.5, p. 48).** A connection is symmetric when $(X \vdash Y) - (Y \vdash X) = [X, Y]$, the bracket being the Poisson bracket $[X, Y]f = X(Yf) - Y(Xf)$. For coordinate fields this says $\Gamma^k_{ij} = \Gamma^k_{ji}$, and Milnor notes the converse.

**Proved in Lean.** Abstract: a covariant derivative is symmetric if $X \vdash Y - Y \vdash X = [X, Y]$ at every point where $X$ and $Y$ are differentiable, $[X, Y]$ being Mathlib's Lie bracket of vector fields, which has Milnor's sign; for a finite-dimensional model space this is “the torsion is zero”. Embedded: the bracket of two maps $X, Y : N \to V$ is $[X, Y](q) = dY_q(X(q)) - dX_q(Y(q))$. For vector fields differentiable at $q$ it is tangent to $N$ at $q$; for smooth $f$ and smooth vector fields, $X(Yf) - Y(Xf) = [X, Y]f$, where $Xf = df(X)$; and the induced connection is symmetric: $X \vdash Y - Y \vdash X = [X, Y]$ at $q$ for vector fields differentiable at $q$.

- `Morse.IsSymmetric` — Morse/Chapter6/Connection.lean, line 120
- `Morse.isSymmetric_iff_torsion_eq_zero` — Morse/Chapter6/Connection.lean, line 125
- `Morse.bracket` — Morse/Chapter6/Submanifold.lean, line 150
- `Morse.bracket_mem` — Morse/Chapter6/Submanifold.lean, line 382
- `Morse.dN_bracket` — Morse/Chapter6/Submanifold.lean, line 404
- `Morse.leviCivita_sub_leviCivita` — Morse/Chapter6/Submanifold.lean, line 394

*What differs.*
- In the embedded setting, that the ambient formula for the bracket is tangent and acts on functions as Milnor's bracket is not automatic: the normal part of $[X, Y]$ is $\mathrm{II}(X, Y) - \mathrm{II}(Y, X)$, which vanishes by the symmetry of $\mathrm{II}$ (V6.12), and the action on functions uses the symmetry of second derivatives.
- The converse “if $\Gamma^k_{ij} = \Gamma^k_{ji}$ then the connection is symmetric” is not formalized, there being no Christoffel symbols.

### V6.14. Lemma 8.6: the fundamental lemma of Riemannian geometry

*narrower* · existence only for embedded $N$ · abstract uniqueness only · Koszul, not Christoffel

**Milnor (§8, Lemma 8.6, p. 48).** On a Riemannian manifold there is exactly one symmetric connection compatible with the metric. Uniqueness: Corollary 8.4 applied to $\partial_i$, $\partial_j$, $\partial_k$ gives three linear equations, whose solution is the first Christoffel identity, and multiplying by $(g^{k\ell})$ gives the second. Conversely, defining $\Gamma^\ell_{ij}$ by this formula, one can verify that the connection is symmetric and compatible with the metric.

**Proved in Lean.** Embedded: call an operation $D$ on maps $N \to V$ symmetric and compatible if, on smooth vector fields, $D(X, Y)$ is tangent, $D(X, Y) - D(Y, X) = [X, Y]$, and $X\langle Y, Y'\rangle = \langle D(X, Y), Y'\rangle + \langle Y, D(X, Y')\rangle$. The induced connection $P(dY(X))$ is such an operation (existence); every such operation satisfies the Koszul formula $2\langle D(X, Y), Z\rangle = X\langle Y, Z\rangle + Y\langle X, Z\rangle - Z\langle X, Y\rangle + \langle [X, Y], Z\rangle - \langle [X, Z], Y\rangle - \langle [Y, Z], X\rangle$ on smooth vector fields; and every such operation agrees with $P(dY(X))$ on smooth vector fields at every point (uniqueness). Abstract: for a manifold with a Riemannian metric on its tangent bundle, two covariant derivatives that are both symmetric and compatible (V6.11, V6.13) satisfy the Koszul formula and agree on every vector field differentiable at the point; with Mathlib's predicates, two torsion-free metric connections agree on such fields, for a finite-dimensional model space and a $C^1$ metric.

- `Morse.IsSymmCompat` — Morse/Chapter6/Submanifold.lean, line 449
- `Morse.isSymmCompat_leviCivita` — Morse/Chapter6/Submanifold.lean, line 464
- `Morse.IsSymmCompat.two_mul_inner` — Morse/Chapter6/Submanifold.lean, line 479
- `Morse.IsSymmCompat.eq_leviCivita` — Morse/Chapter6/Submanifold.lean, line 497
- `Morse.koszul` — Morse/Chapter6/Connection.lean, line 194
- `Morse.two_mul_inner_cov_eq_koszul` — Morse/Chapter6/Connection.lean, line 204
- `Morse.cov_eq_of_isSymmetric_of_isCompatible` — Morse/Chapter6/Connection.lean, line 216
- `Morse.cov_eq_of_torsion_eq_zero_of_isMetricCompatible` — Morse/Chapter6/Connection.lean, line 234

*What differs.*
- Existence is proved only in the embedded setting, where the induced connection is the one; on an abstract manifold only uniqueness is proved, and only on sections differentiable at the point, a Mathlib covariant derivative being unconstrained elsewhere.
- The embedded uniqueness assumes no linearity or tensoriality of $D$, only the three properties on smooth fields; it applies the Koszul formula with $Z$ the field $x \mapsto P_x(D(X, Y)(q) - (X \vdash Y)(q))$.
- The Koszul formula, the coordinate-free form of the first Christoffel identity, replaces Milnor's linear system on p. 49, whose list of three unknowns contains $\langle \partial_i \vdash \partial_j, \partial_k\rangle$ twice by the symmetry he quotes, a misprint. His existence half needs a converse of Lemma 8.3, which he does not state, and a patching of the local connections.

### V6.15. Lemma 8.7

*narrower* · embedded $N$, induced connection · both sides are $P(s_{xy})$

**Milnor (§8, Lemma 8.7, p. 50).** On a parametrized surface $s : \mathbb R^2 \to M$, $DV/\partial x$ is the covariant derivative of $V$ along the curves $x \mapsto s(x, y_0)$. For a symmetric connection, $\frac{D}{\partial x}\frac{\partial s}{\partial y} = \frac{D}{\partial y}\frac{\partial s}{\partial x}$; the proof is a computation in local coordinates.

**Proved in Lean.** For a smooth surface $s : \mathbb R^2 \to N$ the velocity fields $\partial s/\partial x$, $\partial s/\partial y$ are tangent, and $DW/\partial x$ is defined, as in Milnor, as the covariant derivative of $x \mapsto W(x, y_0)$ along the curve $x \mapsto s(x, y_0)$, and similarly $DW/\partial y$; at a point $p$ where $W$ is differentiable it equals $P_{s(p)}(\partial W/\partial x\,(p))$. Then $\frac{D}{\partial x}\frac{\partial s}{\partial y} = \frac{D}{\partial y}\frac{\partial s}{\partial x}$ at every point.

- `Morse.velX` — Morse/Chapter6/Surface.lean, line 135
- `Morse.velY` — Morse/Chapter6/Surface.lean, line 138
- `Morse.covDerivX` — Morse/Chapter6/Surface.lean, line 142
- `Morse.covDerivY` — Morse/Chapter6/Surface.lean, line 146
- `Morse.covDerivX_eq` — Morse/Chapter6/Surface.lean, line 150
- `Morse.covDerivX_velY` — Morse/Chapter6/Surface.lean, line 172

*What differs.*
- Only for the induced connection, which is symmetric (V6.13); both sides equal $P(\partial^2 s/\partial x\,\partial y)$.
- The joint smoothness of $DW/\partial x$ in $(x, y)$, which the definition one curve at a time leaves open, is visible from the formula.

### V6.16. The curvature tensor and its sign

*as in the book*

**Milnor (§9, p. 51).** The curvature tensor of an affine connection measures how far the second covariant derivative $\partial_i \vdash (\partial_j \vdash Z)$ is from being symmetric in $i$ and $j$; it is defined by $R(X, Y)Z = -X \vdash (Y \vdash Z) + Y \vdash (X \vdash Z) + [X, Y] \vdash Z$. A footnote says that Nomizu gives $R$ the opposite sign, and that Milnor's convention makes $\langle R(\partial_h, \partial_i)\partial_j, \partial_k\rangle$ the classical symbol $R_{hijk}$.

**Proved in Lean.** For a covariant derivative on an abstract manifold, Milnor's curvature of vector fields is $R(X, Y)Z = -X \vdash (Y \vdash Z) + Y \vdash (X \vdash Z) + [X, Y] \vdash Z$; it is the negative of Nomizu's, and Kobayashi–Nomizu's, $\nabla_X\nabla_YZ - \nabla_Y\nabla_XZ - \nabla_{[X, Y]}Z$, and $R(Y, X)Z = -R(X, Y)Z$. In the embedded setting the same formula, with the induced connection and the bracket of V6.13, defines $R(X, Y)Z$ for maps $N \to V$. Mathlib defines no curvature, so there is no Mathlib sign to compare with.

- `Morse.milnorCurvature` — Morse/Chapter6/Connection.lean, line 140
- `Morse.nomizuCurvature` — Morse/Chapter6/Connection.lean, line 146
- `Morse.milnorCurvature_eq_neg` — Morse/Chapter6/Connection.lean, line 151
- `Morse.milnorCurvature_swap` — Morse/Chapter6/Connection.lean, line 157
- `Morse.curvature` — Morse/Chapter6/Submanifold.lean, line 518

### V6.17. Lemma 9.1: the curvature is a tensor

*narrower* · embedded $N$, induced connection · an explicit formula in $\mathrm{II}$ · the computation for $Z$ differs

**Milnor (§9, Lemma 9.1, p. 51).** $R(X, Y)Z$ at $p$ is determined by $X_p$, $Y_p$, $Z_p$ alone, whatever the fields do near $p$, and depends trilinearly on them; in short, $R$ is a tensor. The proof checks $R(fX, Y)Z = fR(X, Y)Z$ and leaves the analogous identities for $Y$ and $Z$ to similar computations, which Milnor calls easy.

**Proved in Lean.** In the embedded setting, for smooth vector fields $X$, $Y$, $Z$ and every $q$, $R(X, Y)Z\,(q) = \mathrm{II}_q(Y_q, \mathrm{II}_q(X_q, Z_q)) - \mathrm{II}_q(X_q, \mathrm{II}_q(Y_q, Z_q))$, that is, $R(X, Y) = D_YD_X - D_XD_Y$ on $T_qN$. Consequently $R(X, Y)Z$ at $q$ depends only on $X_q$, $Y_q$, $Z_q$, and it is the value of a trilinear map $T_qN \times T_qN \times T_qN \to T_qN$, the curvature tensor of $N$ at $q$.

- `Morse.curvOp` — Morse/Chapter6/Submanifold.lean, line 524
- `Morse.curvature_eq` — Morse/Chapter6/Submanifold.lean, line 540
- `Morse.curvTensor` — Morse/Chapter6/Submanifold.lean, line 661
- `Morse.curvature_eq_curvTensor` — Morse/Chapter6/Submanifold.lean, line 687
- `Morse.curvature_congr` — Morse/Chapter6/Submanifold.lean, line 697

*What differs.*
- Only for the induced connection of a submanifold, but with more than Milnor states: an explicit formula for $R$ through the second fundamental form.
- Milnor treats $X$ explicitly and leaves $Y$ and $Z$ to similar computations; for $Z$ the computation is a different one. Here, with a smooth ambient representative $G$ of $Z$, $Y \vdash (X \vdash Z)$ at $q$ is $D_YD_XZ$ plus terms that cancel by the symmetry of $d^2G$ and against $[X, Y] \vdash Z$.

### V6.18. The Gauss equation

*not in the book* · with Milnor's sign of $R$ · computes the curvature of the sphere

**Milnor (no counterpart in the book).** The book has no such formula: Milnor never relates the curvature tensor of a submanifold to its second fundamental form.

**Proved in Lean.** For all $x, y, z, w \in V$, $\langle D_yD_xz - D_xD_yz, w\rangle = \langle \mathrm{II}(x, z), \mathrm{II}(y, w)\rangle - \langle \mathrm{II}(x, w), \mathrm{II}(y, z)\rangle$ at $q$; hence, for smooth vector fields $X$, $Y$, $Z$ and any $W : N \to V$, $\langle R(X, Y)Z, W\rangle = \langle \mathrm{II}(X, Z), \mathrm{II}(Y, W)\rangle - \langle \mathrm{II}(X, W), \mathrm{II}(Y, Z)\rangle$ at every point, with Milnor's sign of $R$. With $Z = X$, $W = Y$ and the symmetry of $\mathrm{II}$ this gives $\langle R(X, Y)X, Y\rangle = \langle \mathrm{II}(X, X), \mathrm{II}(Y, Y)\rangle - \|\mathrm{II}(X, Y)\|^2$, Gauss's curvature for a surface in $\mathbb R^3$.

- `Morse.inner_curvOp` — Morse/Chapter6/Submanifold.lean, line 600
- `Morse.gauss_equation` — Morse/Chapter6/Submanifold.lean, line 609

*What differs.*
- No counterpart in the book; it is how curvature is computed in the embedded setting, for instance for the round sphere (V6.25), and its sign confirms Milnor's convention against Gauss's classical formula.

### V6.19. Lemma 9.2

*narrower* · embedded $N$, induced connection · no symmetry of the connection used

**Milnor (§9, Lemma 9.2, p. 52).** For a parametrized surface $s : \mathbb R^2 \to M$ and any vector field $V$ along $s$, $\frac{D}{\partial y}\frac{D}{\partial x}V - \frac{D}{\partial x}\frac{D}{\partial y}V = R(\frac{\partial s}{\partial x}, \frac{\partial s}{\partial y})V$. Proof: express both sides in a local coordinate system and compute, using $\partial_j \vdash (\partial_i \vdash \partial_k) - \partial_i \vdash (\partial_j \vdash \partial_k) = R(\partial_i, \partial_j)\partial_k$.

**Proved in Lean.** For a smooth surface $s : \mathbb R^2 \to N$ and a smooth map $W : \mathbb R^2 \to V$ with $W(p) \in T_{s(p)}N$ for all $p$, $\frac{D}{\partial y}\frac{D}{\partial x}W - \frac{D}{\partial x}\frac{D}{\partial y}W = R(\frac{\partial s}{\partial x}, \frac{\partial s}{\partial y})W$ at every point, with $R(x, y) = D_yD_x - D_xD_y$ the curvature of V6.17.

- `Morse.covDerivY_covDerivX_sub` — Morse/Chapter6/Surface.lean, line 181

*What differs.*
- Only for the induced connection. The proof uses $W = PW$, $PD_vP = 0$, and the fact that $D_v$ maps normal vectors to tangent ones; no symmetry of the connection and no coordinates are used.
- The joint smoothness of the covariant derivatives in $(x, y)$, which the definition one curve at a time leaves open, is again visible from the formula.

### V6.20. Lemma 9.3, symmetries (1)–(3)

*narrower* · embedded $N$, induced connection · no bracket-free extensions needed

**Milnor (§9, Lemma 9.3, p. 53).** The curvature tensor of a Riemannian manifold satisfies (1) $R(X, Y)Z + R(Y, X)Z = 0$, (2) $R(X, Y)Z + R(Y, Z)X + R(Z, X)Y = 0$, (3) $\langle R(X, Y)Z, W\rangle + \langle R(X, Y)W, Z\rangle = 0$. (1) is immediate from the definition; (2) and (3) are proved for fields whose brackets vanish, which suffices since all terms are tensors, (3) being reduced to $\langle R(X, Y)Z, Z\rangle = 0$, clearly an equivalent assertion.

**Proved in Lean.** A trilinear map $R$ on a real inner product space is called a curvature tensor if it satisfies (1) $R(X, Y)Z + R(Y, X)Z = 0$, (2) $R(X, Y)Z + R(Y, Z)X + R(Z, X)Y = 0$ and (3) $\langle R(X, Y)Z, W\rangle + \langle R(X, Y)W, Z\rangle = 0$. For a linear map $T$, $\langle TZ, W\rangle$ is skew in $Z$, $W$ iff $\langle TZ, Z\rangle = 0$ for all $Z$. The curvature tensor of $N$ at each point (V6.17) satisfies (1)–(3). For maps $X$, $Y$, $Z$ of $N$ into $V$, (1) holds with no hypothesis; for smooth vector fields, (2) and (3) hold at every point.

- `Morse.IsCurvatureTensor` — Morse/Chapter6/CurvatureAlgebra.lean, line 151
- `Morse.inner_add_inner_eq_zero_iff` — Morse/Chapter6/CurvatureAlgebra.lean, line 139
- `Morse.isCurvatureTensor_curvTensor` — Morse/Chapter6/Submanifold.lean, line 715
- `Morse.curvature_add_swap` — Morse/Chapter6/Submanifold.lean, line 733
- `Morse.curvature_bianchi` — Morse/Chapter6/Submanifold.lean, line 740
- `Morse.inner_curvature_add_inner` — Morse/Chapter6/Submanifold.lean, line 752

*What differs.*
- Only for the induced connection of a submanifold.
- Milnor proves (2) and (3) for extensions with vanishing brackets, which must be constructed (coordinate fields cut off by a bump function). Here no extensions are needed: (2) is the symmetry of $\mathrm{II}$, and (3) the self-adjointness of $D_v$.

### V6.21. Lemma 9.3, symmetry (4): the octahedron

*stronger* · no linearity used · the signs of the triangles written out

**Milnor (§9, Lemma 9.3, p. 54).** (4) $\langle R(X, Y)Z, W\rangle = \langle R(Z, W)X, Y\rangle$, proved from (1), (2) and (3) with the octahedron of p. 54: by (2), with the help of (1) and (3), the quantities at the vertices of each shaded triangle sum to zero, and adding the identities for the top two shaded triangles and subtracting those for the bottom ones leaves twice the top vertex minus twice the bottom vertex.

**Proved in Lean.** Let $T(X, Y, Z, W)$ be any real function of four arguments that is skew in $(X, Y)$, skew in $(Z, W)$, and satisfies $T(X, Y, Z, W) + T(Y, Z, X, W) + T(Z, X, Y, W) = 0$. Then $T(X, Y, Z, W) = T(Z, W, X, Y)$. Hence every curvature tensor (V6.20) satisfies (4), $\langle R(X, Y)Z, W\rangle = \langle R(Z, W)X, Y\rangle$, and so does $R$ on smooth vector fields of $N$.

- `Morse.octahedron` — Morse/Chapter6/CurvatureAlgebra.lean, line 108
- `Morse.IsCurvatureTensor.inner_comm_pairs` — Morse/Chapter6/CurvatureAlgebra.lean, line 185
- `Morse.inner_curvature_comm_pairs` — Morse/Chapter6/Submanifold.lean, line 767

*What differs.*
- No linearity of $T$ is used: the octahedron argument is pure combinatorics of the three symmetries.
- The four triangle identities, whose signs Milnor leaves to the reader, are written out.

### V6.22. Sectional curvature

*stronger* · any independent pair · depends only on the plane · the same in both sign conventions

**Milnor (§19, Remark after Lemma 19.1, p. 100).** For orthogonal unit vectors $A$, $B$ at $p$, Milnor calls $\langle R(A, B)A, B\rangle$ the sectional curvature determined by $A$ and $B$, and notes that it is the Gaussian curvature of the surface formed by the geodesics through $p$ whose velocities lie in the plane of $A$ and $B$.

**Proved in Lean.** For a trilinear map $R$ and vectors $X$, $Y$, put $K(X, Y) = \langle R(X, Y)X, Y\rangle / (\|X\|^2\|Y\|^2 - \langle X, Y\rangle^2)$, which is $0$ when $X$, $Y$ are dependent; for an orthonormal pair it is Milnor's $\langle R(A, B)A, B\rangle$. If $R$ satisfies (1)–(3), $K$ depends only on the plane: $K(aX + bY, cX + dY) = K(X, Y)$ whenever $ad - bc \ne 0$. With the standard sign, $-R$ also satisfies (1)–(3), and $\langle (-R)(X, Y)Y, X\rangle = \langle R(X, Y)X, Y\rangle$: the sectional curvature is the same number in both conventions.

- `Morse.sectionalCurvature` — Morse/Chapter6/CurvatureAlgebra.lean, line 225
- `Morse.IsCurvatureTensor.sectionalCurvature_smul_add` — Morse/Chapter6/CurvatureAlgebra.lean, line 290
- `Morse.IsCurvatureTensor.neg` — Morse/Chapter6/CurvatureAlgebra.lean, line 192
- `Morse.IsCurvatureTensor.inner_neg_apply_swap` — Morse/Chapter6/CurvatureAlgebra.lean, line 212

*What differs.*
- Defined for any independent pair, and shown to depend only on the plane they span, which the book does not state.
- The identification with the Gaussian curvature of a surface of geodesics is not formalized here; it needs the exponential map (Chapter 11).

### V6.24. Constant curvature

*not in the book* · in Milnor's sign · sectional curvature determines $R$

**Milnor (no counterpart in the book).** The book defines the sectional curvature (p. 100) but does not state that a curvature tensor all of whose sectional curvatures equal $\kappa$ is $\kappa$ times a standard one.

**Proved in Lean.** $R_1(X, Y)Z = \langle X, Z\rangle Y - \langle Y, Z\rangle X$ is a curvature tensor, and $\kappa R_1$ has sectional curvature $\kappa$ on every independent pair. Conversely, if a curvature tensor $R$ has $\langle R(A, B)A, B\rangle = \kappa$ for all orthonormal $A$, $B$, or $K(X, Y) = \kappa$ for all independent $X$, $Y$, then $R(X, Y)Z = \kappa(\langle X, Z\rangle Y - \langle Y, Z\rangle X)$; with the standard sign this is $\kappa(\langle Y, Z\rangle X - \langle X, Z\rangle Y)$. Behind it: $6\langle R(X, Y)Z, W\rangle$ is an explicit combination of the values $\langle R(A, B)A, B\rangle$ at sums of $X$, $Y$, $Z$, $W$, so a curvature tensor is determined by its sectional curvatures.

- `Morse.curvatureOne` — Morse/Chapter6/CurvatureAlgebra.lean, line 431
- `Morse.isCurvatureTensor_curvatureOne` — Morse/Chapter6/CurvatureAlgebra.lean, line 443
- `Morse.sectionalCurvature_smul_curvatureOne` — Morse/Chapter6/CurvatureAlgebra.lean, line 460
- `Morse.IsCurvatureTensor.eq_smul_curvatureOne_of_orthonormal` — Morse/Chapter6/CurvatureAlgebra.lean, line 479
- `Morse.IsCurvatureTensor.apply_eq_of_sectionalCurvature_eq` — Morse/Chapter6/CurvatureAlgebra.lean, line 489
- `Morse.IsCurvatureTensor.polarization` — Morse/Chapter6/CurvatureAlgebra.lean, line 379
- `Morse.IsCurvatureTensor.ext_of_sectionalCurvature` — Morse/Chapter6/CurvatureAlgebra.lean, line 404
- `Morse.neg_smul_curvatureOne_apply` — Morse/Chapter6/CurvatureAlgebra.lean, line 468

*What differs.*
- No counterpart in the book: Lemma 7.2 and Corollary 7.3 of the exposition, the polarization formula and its consequence for constant curvature.

### V6.25. The round sphere

*not in the book* · coordinate-free, by the Gauss equation · sectional curvature $1$

**Milnor (no counterpart in the book).** No counterpart in §§8–9: the book does not compute a curvature tensor there.

**Proved in Lean.** For the unit sphere $S^n \subseteq \mathbb R^{n+1}$, a slice submanifold of the companion project, with the induced metric: $P_qv = v - \langle q, v\rangle q$; $\mathrm{II}_q(v, w) = -\langle v, w\rangle q$ for tangent $v$, $w$; the curvature tensor is $R(x, y)z = \langle x, z\rangle y - \langle y, z\rangle x$ with Milnor's sign; so $S^n$ has sectional curvature $1$, both as $K(x, y) = 1$ for independent tangent $x$, $y$ and as $\langle R(A, B)A, B\rangle = 1$ for orthonormal $A$, $B$.

- `Milnor.Sphere.Sph` — ../Milnor/Chapter5/HairyBall.lean, line 81
- `Milnor.Sphere.sphSub` — ../Milnor/Chapter6/EulerSphere.lean, line 147
- `Morse.tanProj_sph` — Morse/Chapter6/SphereCurvature.lean, line 49
- `Morse.secondFundForm_sph` — Morse/Chapter6/SphereCurvature.lean, line 63
- `Morse.curvOp_sph` — Morse/Chapter6/SphereCurvature.lean, line 92
- `Morse.curvTensor_sph` — Morse/Chapter6/SphereCurvature.lean, line 111
- `Morse.sectionalCurvature_sph` — Morse/Chapter6/SphereCurvature.lean, line 118
- `Morse.inner_curvTensor_sph_orthonormal` — Morse/Chapter6/SphereCurvature.lean, line 125

*What differs.*
- A computation the book does not make in §§8–9, done coordinate-free from the Gauss equation (V6.18); it is the curvature of the sphere used in later chapters of this edition.

## Chapter 7

*Milnor §10, pp. 55–66: geodesics and completeness*

### V7.1. Geodesics

*narrower* · submanifolds of a Euclidean space · geodesics live on open sets · Nash's theorem quoted, not used

**Milnor (§10, p. 55).** On a connected Riemannian manifold $M$, a parametrized path $\gamma : I \to M$, $I$ any interval of the real line, is called a *geodesic* if its acceleration field $\frac{D}{dt}\frac{d\gamma}{dt}$ is identically zero; that is, if the velocity field $\frac{d\gamma}{dt}$ is parallel along $\gamma$. Here $D/dt$ is the covariant derivative along a curve of §8, for the Levi-Civita connection of an abstract Riemannian manifold.

**Proved in Lean.** Let $V$ be a finite-dimensional real inner product space (Milnor's $\mathbb R^K$) and $N \subseteq V$ a slice submanifold with the induced metric; $N$ need not be closed, compact or connected. A curve $\gamma : \mathbb R \to V$ is a geodesic on an open set $s \subseteq \mathbb R$ if it is $C^\infty$ on $s$, $\gamma(t) \in N$ for $t \in s$, and the acceleration $\gamma''(t)$ in $V$ is orthogonal to $T_{\gamma(t)}N$ for every $t \in s$. The velocity of a curve in $N$ is tangent to $N$, so the condition reads $P_{\gamma(t)}\gamma''(t) = 0$, $P$ the orthogonal projection onto the tangent space: this is $\frac{D}{dt}\frac{d\gamma}{dt} = 0$ for the covariant derivative $D/dt = P \circ d/dt$ of Chapter 6, and for a smooth curve $c : \mathbb R \to N$ the equivalence of the two conditions is a theorem. Constant curves at points of $N$ are geodesics.

- `Morse.IsGeodesicOn` — Morse/Chapter7/Geodesic.lean, line 86
- `Morse.hasDerivAt_mem_tangentSubspace` — Morse/Chapter7/Geodesic.lean, line 170
- `Morse.IsGeodesicOn.tanProj_deriv_deriv` — Morse/Chapter7/Geodesic.lean, line 212
- `Morse.isGeodesicOn_univ_iff_covDeriv` — Morse/Chapter7/Geodesic.lean, line 326
- `Morse.isGeodesicOn_const` — Morse/Chapter7/Geodesic.lean, line 157

*What differs.*
- Milnor's $M$ is an abstract Riemannian manifold. In Chapters 7–11 of the formalization it is a submanifold $N$ of a Euclidean space with the induced metric, and every row of these chapters is read in that setting; the narrowing is recorded here once rather than on every row. Every Riemannian manifold is of this kind by Nash's embedding theorem, which is quoted in the Lean files but neither proved nor used.
- Mathlib has no Levi-Civita connection, geodesics or exponential map on an abstract manifold. In the embedded setting the connection is the tangential part of the derivative in $V$, and the Hausdorff property that Milnor uses silently is automatic.
- Geodesics live on open sets: a geodesic on a closed interval, which Milnor allows, is represented by one on a slightly larger open interval. That the two notions give the same exponential map is proved later (V7.7).
- Milnor's standing assumption that $M$ is connected is not made; it is assumed exactly where it is needed (finiteness of the distance, Theorem 10.9 for all pairs, Corollary 10.10, the Hopf–Rinow equivalence).

### V7.2. Constant speed and homogeneity

*stronger* · every affine change $t \mapsto at + b$ · length = speed times $(b - a)$

**Milnor (§10, pp. 55 and 57).** Since $\frac{d}{dt}\langle\frac{d\gamma}{dt}, \frac{d\gamma}{dt}\rangle = 2\langle\frac{D}{dt}\frac{d\gamma}{dt}, \frac{d\gamma}{dt}\rangle = 0$, the length $\|d\gamma/dt\|$ of the velocity vector of a geodesic is constant, and the parameter $t$ is a linear function of arc length (p. 55). On p. 57 Milnor adds homogeneity: if $t \mapsto \gamma(t)$ is a geodesic, then so is $t \mapsto \gamma(ct)$ for every constant $c$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $\gamma$ be a geodesic on an open set $s \subseteq \mathbb R$. Then $\frac{d}{dt}\|\gamma'\|^2 = 2\langle\gamma'', \gamma'\rangle = 0$ on $s$. If $s$ is preconnected (an open interval), the speed $\|\gamma'\|$ is constant on $s$, and the length of $\gamma$ on every $[a, b] \subseteq s$ (V7.11) is $\|\gamma'(t_0)\|\,(b - a)$, for any $t_0 \in s$. For all real $a$ and $b$, the curve $t \mapsto \gamma(at + b)$ is a geodesic on $\{t : at + b \in s\}$.

- `Morse.IsGeodesicOn.hasDerivAt_norm_sq` — Morse/Chapter7/Geodesic.lean, line 239
- `Morse.IsGeodesicOn.norm_deriv_eq` — Morse/Chapter7/Geodesic.lean, line 245
- `Morse.IsGeodesicOn.pathLength_eq` — Morse/Chapter7/Shortest.lean, line 81
- `Morse.IsGeodesicOn.comp_mul_add` — Morse/Chapter7/Geodesic.lean, line 133

*What differs.*
- Milnor's homogeneity is for $t \mapsto \gamma(ct)$; the formal statement allows every affine change of parameter $t \mapsto at + b$, the case $a = 0$ giving a constant curve.
- The length of a geodesic segment, which Milnor uses from Theorem 10.4 on without comment, is computed: speed times the length of the parameter interval.

### V7.3. The geodesic equation

*restated* · $\gamma'' = \mathrm{II}(\gamma', \gamma')$ · no Christoffel symbols · chart solutions are geodesics

**Milnor (§10, p. 55).** In terms of a local coordinate system $u^1, \dots, u^n$, the condition for $\gamma$ to be a geodesic becomes the system of second-order differential equations $\frac{d^2u^k}{dt^2} + \sum_{i,j}\Gamma^k_{ij}\frac{du^i}{dt}\frac{du^j}{dt} = 0$, $k = 1, \dots, n$, with the Christoffel symbols $\Gamma^k_{ij}$ of the connection. The existence of geodesics therefore rests on the existence theorem for such systems.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $\gamma$ be $C^\infty$ on an open set $s$, with $\gamma(s) \subseteq N$. Then $\gamma$ is a geodesic on $s$ iff $\gamma'' = \mathrm{II}_\gamma(\gamma', \gamma')$ on $s$, $\mathrm{II}$ the second fundamental form, iff the lift $t \mapsto (\gamma(t), \gamma'(t))$, which lies in $TN = \{(x, v) : x \in N,\ v \in T_xN\}$, is an integral curve of the geodesic spray $(x, v) \mapsto (v, \mathrm{II}_x(v, v))$. In a slice chart with parametrization $x$ on an open set $T$ of the model space $Z$, put $A^+ = (A^{\mathsf T}A)^{-1}A^{\mathsf T}$ for injective $A$ and $\Gamma(u)(w, w) = (dx_u)^+\big(d^2x_u(w, w)\big)$. The field $(u, w) \mapsto (w, -\Gamma(u)(w, w))$ is smooth on $T \times Z$, and if $(u, w)$ is a $C^\infty$ solution of $u' = w$, $w' = -\Gamma(u)(w, w)$ on an open set, with $u$ in $T$, then $x \circ u$ is a geodesic there.

- `Morse.IsGeodesicOn.deriv_deriv_eq` — Morse/Chapter7/Geodesic.lean, line 221
- `Morse.isGeodesicOn_of_deriv_deriv_eq` — Morse/Chapter7/Geodesic.lean, line 310
- `Morse.geodesicSpray` — Morse/Chapter7/Geodesic.lean, line 340
- `Morse.isGeodesicOn_iff_hasDerivAt_geodesicSpray` — Morse/Chapter7/Geodesic.lean, line 352
- `Morse.chartSpray` — Morse/Chapter7/GeodesicLocal.lean, line 166
- `Morse.contDiffOn_chartSpray` — Morse/Chapter7/GeodesicLocal.lean, line 178
- `Morse.isGeodesicOn_chart` — Morse/Chapter7/GeodesicLocal.lean, line 208

*What differs.*
- The global form of the equation lives in $V$: the acceleration of a geodesic is its normal part $\mathrm{II}(\gamma', \gamma')$, and the geodesics are the projections of the integral curves of a spray on $TN$.
- In a chart, $(dx_u)^+d^2x_u(w, w)$ is the coordinate vector, in the basis $\partial x/\partial u^k$, of the tangential part of $d^2x_u(w, w)$, that is $(\sum_{i,j}\Gamma^k_{ij}w^iw^j)_k$ for the Christoffel symbols of the induced metric. The Lean files define no Christoffel symbols, so this identification is a remark, not a theorem.
- Only the direction "solutions of the chart equation are geodesics" is stated in the chart, which is what existence needs (V7.6); uniqueness is proved from the global form (V7.5).
- The scan shows only the $\Gamma$-term of Milnor's display; the missing $d^2u^k/dt^2$ is a defect of the scan, not a misprint.

### V7.4. Theorem 10.1: existence, uniqueness and smooth dependence for ODEs

*stronger* · proved, not quoted · uniqueness on every common interval · uniqueness for $C^1$ equations

**Milnor (§10, Theorem 10.1, p. 56).** Given a point $(u_1, v_1) \in \mathbb R^{2n}$ and $C^\infty$ functions $F = (F^1, \dots, F^n)$ defined near it, there are a neighbourhood $W$ of $(u_1, v_1)$ and a number $\varepsilon > 0$ such that for every $(u_0, v_0) \in W$ the equation $\frac{d^2u}{dt^2} = F(u, \frac{du}{dt})$ has a unique solution $t \mapsto u(t)$, defined for $|t| < \varepsilon$, with $u(0) = u_0$ and $\frac{du}{dt}(0) = v_0$; moreover the solution is $C^\infty$ as a function of $(u_0, v_0, t)$ on $W \times (-\varepsilon, \varepsilon)$. Milnor passes to the first-order system $du/dt = v$, $dv/dt = F(u, v)$ and quotes Graves.

**Proved in Lean.** *Existence and smooth dependence.* Let $E$ be a finite-dimensional real normed space, $U \subseteq E \times E$ open, $F : E \times E \to E$ smooth on $U$, and $z_1 \in U$. There are a neighbourhood $W$ of $z_1$, an $\varepsilon > 0$ and a map $(z, t) \mapsto u_z(t)$, smooth on $W \times (-\varepsilon, \varepsilon)$, such that for every $z = (u_0, v_0) \in W$: $u_z(0) = u_0$, $u_z'(0) = v_0$, and $(u_z(t), u_z'(t)) \in U$ and $u_z''(t) = F(u_z(t), u_z'(t))$ for $|t| < \varepsilon$. *Uniqueness.* Let $E$ be any real normed space and $G$ of class $C^1$ on an open $U \subseteq E$: two solutions of $x' = G(x)$ with values in $U$, defined on a common open preconnected set and agreeing at one of its times, agree on all of it. In particular, for $F$ of class $C^1$ on $U \subseteq E \times E$, two pairs with $u_i' = v_i$, $v_i' = F(u_i, v_i)$ and $(u_i, v_i) \in U$ on an open interval, with the same position and velocity at one time, have $u_1 = u_2$ on that interval.

- `Morse.exists_localFlow` — Morse/Chapter7/ODE.lean, line 134
- `Morse.theorem_10_1` — Morse/Chapter7/ODE.lean, line 193
- `Morse.ode_eqOn` — Morse/Chapter7/ODE.lean, line 115
- `Morse.theorem_10_1_unique` — Morse/Chapter7/ODE.lean, line 221

*What differs.*
- Milnor quotes the theorem; the formal one is proved. A bump function equal to $1$ near the base point turns the field into a compactly supported one, whose global flow is smooth in $(t, x)$; its bounded speed keeps the flow lines from nearby points, for a uniform time, where the bump function is $1$.
- Uniqueness holds on every common open interval of definition, not only for $|t| < \varepsilon$, and needs only a $C^1$ equation on an arbitrary real normed space: Grönwall's inequality near each time, spread over the interval by connectedness.
- Milnor's $\mathbb R^n$ is any finite-dimensional real normed space.

### V7.5. Uniqueness of geodesics in the large

*hypotheses explicit* · used by the book, never stated · Hausdorff property automatic here

**Milnor (§10, pp. 56–58).** Milnor never states uniqueness of geodesics on a whole interval. Theorem 10.1 gives it for small times in one coordinate system (p. 56); Lemmas 10.2 and 10.3 then speak of *the unique* geodesic on $(-2, 2)$, or of length $< \varepsilon$, and p. 58 asserts that $\exp_q(v)$, if defined at all, is uniquely defined. All of these use uniqueness of geodesics beyond a single chart.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: two geodesics on open sets $s_1$, $s_2$ containing $t_0$, with the same position and the same velocity at $t_0$, agree near $t_0$; and two geodesics on the same open interval (more generally, open preconnected set) $s$, with the same position and velocity at one time of $s$, agree on all of $s$.

- `Morse.projRep` — Morse/Chapter6/Projection.lean, line 512
- `Morse.IsGeodesicOn.eventuallyEq` — Morse/Chapter7/Geodesic.lean, line 256
- `Morse.IsGeodesicOn.eqOn` — Morse/Chapter7/Geodesic.lean, line 291

*What differs.*
- The book uses uniqueness in the large without stating it; the formal statement supplies it (the exposition's Lemma A). It is a connectedness argument from local uniqueness, and on an abstract manifold it would also need the Hausdorff property, which a subset of $V$ has.
- Near $t_0$ both lifts $(\gamma_i, \gamma_i')$ solve $(x, v)' = (v, dQ_x(v)\,v)$, where $Q$ is a smooth extension of $x \mapsto P_x$ to an open set of $V$ given by a slice chart; this field is smooth, so the uniqueness of V7.4 applies.

### V7.6. Lemma 10.2: geodesics for small initial velocities

*stronger* · smooth in $(p, v, t)$ · coordinates bounded by $\|v\|$, uniformly

**Milnor (§10, Lemma 10.2, p. 56).** For every point $p_0 \in M$ there are a neighbourhood $U$ of $p_0$ and a number $\varepsilon > 0$ such that for each $p \in U$ and each tangent vector $v \in TM_p$ of length $< \varepsilon$ there is a unique geodesic $\gamma_v : (-2, 2) \to M$ with $\gamma_v(0) = p$ and $\frac{d\gamma_v}{dt}(0) = v$. The proof (pp. 56–57) takes $\varepsilon_1$, $\varepsilon_2$ from Theorem 10.1 in a coordinate system and rescales, $\gamma_v(t) = \gamma_{v/\varepsilon_2}(\varepsilon_2t)$, for $\|v\| < \varepsilon < \varepsilon_1\varepsilon_2$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: for every $q_0 \in N$ there are an open set $U \ni q_0$ of $V$, an $\varepsilon > 0$ and a map $\Gamma : V \times V \times \mathbb R \to V$, smooth on $U \times \{\|v\| < \varepsilon\} \times (-2, 2)$, such that for every $p \in N \cap U$ and every $v \in T_pN$ with $\|v\| < \varepsilon$ the curve $\gamma_v = \Gamma(p, v, \cdot)$ is a geodesic on $(-2, 2)$ with $\gamma_v(0) = p$ and $\gamma_v'(0) = v$, and every geodesic on $(-2, 2)$ with this position and velocity at $0$ equals $\gamma_v$ on $(-2, 2)$.

- `Morse.LocalSpray` — Morse/Chapter7/GeodesicLocal.lean, line 247
- `Morse.nonempty_localSpray` — Morse/Chapter7/GeodesicLocal.lean, line 260
- `Morse.LocalSpray.isGeodesicOn_geo` — Morse/Chapter7/GeodesicLocal.lean, line 344
- `Morse.LocalSpray.contDiffOn_geo` — Morse/Chapter7/GeodesicLocal.lean, line 367
- `Morse.lemma_10_2` — Morse/Chapter7/GeodesicLocal.lean, line 383

*What differs.*
- The formal statement adds that $\gamma_v(t)$ depends smoothly on $(p, v, t)$, which Milnor does not state here but uses on p. 58 to make $\exp$ smooth near the zero section (V7.8).
- The step from the coordinate neighbourhood $W$ of Theorem 10.1 to the condition "$p \in U$, $\|v\| < \varepsilon_1$" needs a bound for the coordinates of $v$ by $\|v\|$ uniform for $p$ near $p_0$: here $\|d\sigma_p v\| \le \|d\sigma_p\|\,\|v\|$, $\sigma$ the slice chart, with $\|d\sigma_p\|$ bounded near $q_0$.
- Uniqueness on all of $(-2, 2)$ is the uniqueness in the large of V7.5.

### V7.7. The exponential map

*restated* · geodesics near $[0, 1]$, not on $[0, 1]$ · the two domains agree (Ch. 9, 11)

**Milnor (§10, pp. 57–58).** For $v \in TM_q$, suppose there is a geodesic $\gamma : [0, 1] \to M$ with $\gamma(0) = q$ and $\frac{d\gamma}{dt}(0) = v$; then $\exp_q(v) = \gamma(1)$, and by homogeneity $\gamma(t) = \exp_q(tv)$ (p. 57). On p. 58 Milnor notes that $\exp_q(v)$ is defined when $\|v\|$ is small enough, in general not for large $v$, but is always uniquely defined when it is defined at all.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: for $q, v \in V$, a geodesic from $q$ with initial velocity $v$ is a geodesic on an open interval $(-\delta, 1 + \delta)$, $\delta > 0$, with $\gamma(0) = q$ and $\gamma'(0) = v$ (then $q \in N$ and $v \in T_qN$). The domain of $\exp$ is the set of pairs $(q, v)$ for which one exists, and $\exp_q(v) = \gamma(1)$ (off the domain $\exp_q(v)$ is set to $q$, a placeholder). Any two such geodesics agree on an open interval containing $[0, 1]$, so $\exp_q(v)$ is well defined. For $q \in N$, $(q, 0)$ is in the domain and $\exp_q(0) = q$; and for such a $\gamma$, each $s \mapsto \gamma(ts)$ with $t$ near $[0, 1]$ is a geodesic from $q$ with initial velocity $tv$, so $\exp_q(tv) = \gamma(t)$.

- `Morse.IsGeodesicFrom` — Morse/Chapter7/Exp.lean, line 72
- `Morse.expDom` — Morse/Chapter7/Exp.lean, line 77
- `Morse.exp` — Morse/Chapter7/Exp.lean, line 82
- `Morse.IsGeodesicFrom.exp_eq` — Morse/Chapter7/Exp.lean, line 129
- `Morse.exp_zero` — Morse/Chapter7/Exp.lean, line 146
- `Morse.IsGeodesicFrom.exp_smul` — Morse/Chapter7/Exp.lean, line 156
- `Morse.exists_initial_ray` — Morse/Chapter9/GeodesicVariation.lean, line 494
- `Morse.mem_expDom_of_isGeodesicOn` — Morse/Chapter11/ExpSmooth.lean, line 354

*What differs.*
- Milnor's geodesic on the closed interval $[0, 1]$, with one-sided derivatives at the ends, is replaced by one on an open interval containing $[0, 1]$. Restriction gives a geodesic in Milnor's sense with the same value at $1$.
- Conversely, a geodesic on $[0, 1]$ in Milnor's sense agrees there with $t \mapsto \exp_{\gamma(0)}(t\gamma'(0))$, which is a geodesic on an open interval containing $[0, 1]$ (V9.9), so its initial data lie in the formal domain (V11.1): the two domains of $\exp$ coincide. This is proved in Chapters 9 and 11, not in Chapter 7.
- Well-definedness is the uniqueness in the large of V7.5, and $\gamma(t) = \exp_q(tv)$ uses homogeneity (V7.2) together with it.

### V7.8. The tangent manifold, $\exp$ near the zero section, and $d(\exp_q)_0$

*stronger* · one neighbourhood of the zero section · embedded $TN \subseteq V \times V$

**Milnor (§10, p. 58).** The tangent manifold $TM$ is given a $C^\infty$ structure by the coordinates $(u^1, \dots, u^n, t^1, \dots, t^n)$, where $t^1\partial_1 + \dots + t^n\partial_n$ is a tangent vector at a point with coordinates $u$. Lemma 10.2 says that for each $p \in M$ the map $(q, v) \mapsto \exp_q(v)$ is defined throughout a neighbourhood $V$ of $(p, 0)$ in $TM$, and is differentiable there. In the Jacobian of $F(q, v) = (q, \exp_q(v))$ at $(p, 0)$, the column $F_*(\partial/\partial t^j) = \partial/\partial u_2^j$ amounts to $d(\exp_p)_0 = \mathrm{id}$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: $TN = \{(q, v) \in V \times V : q \in N,\ v \in T_qN\}$ is a slice submanifold of $V \times V$ (the companion project). (i) For every $q_0 \in N$ there are an open $U \ni q_0$, an $\varepsilon > 0$ and $F$ smooth on $U \times \{\|v\| < \varepsilon\}$ such that, for $p \in N \cap U$ and $v \in T_pN$ with $\|v\| < \varepsilon$, $(p, v)$ is in the domain of $\exp$ and $\exp_p(v) = F(p, v)$. (ii) There is one open $O \subseteq V \times V$ containing $(q, 0)$ for every $q \in N$ such that every point of $TN \cap O$ is in the domain of $\exp$, and $\exp$ is smooth on $TN \cap O$, both as a restriction of smooth maps on open sets of $V \times V$ and as a map on the manifold $TN$. (iii) For $q \in N$, $\exp_q$, as a map on the vector space $T_qN$, has derivative at $0$ the inclusion $T_qN \to V$.

- `Milnor.Problems.tangentBundleSet` — ../Milnor/Chapter8/TangentBundle.lean, line 133
- `Milnor.Problems.isSliceSubmanifold_tangentBundle` — ../Milnor/Chapter8/TangentBundle.lean, line 161
- `Morse.exists_exp_eq` — Morse/Chapter7/Exp.lean, line 202
- `Morse.exists_isOpen_exp` — Morse/Chapter7/Exp.lean, line 221
- `Morse.contMDiffOn_exp` — Morse/Chapter7/Exp.lean, line 245
- `Morse.hasFDerivAt_exp_zero` — Morse/Chapter7/Exp.lean, line 270

*What differs.*
- Milnor's tangent manifold, with its coordinates $(u, t)$, is the embedded $TN \subseteq V \times V$ of the companion project.
- Milnor gives a neighbourhood of each $(p, 0)$; the formal statement gives one open neighbourhood of the whole zero section on which $\exp$ is defined and smooth.
- The differentiability Milnor cites rests on the smooth dependence in Lemma 10.2, which his statement of that lemma omits (V7.6).

### V7.9. Normal radius

*restated* · the name is the exposition’s · “diffeomorphically” in two senses

**Milnor (§10, Lemma 10.3 (3), p. 59).** Part (3) of Lemma 10.3 says that, for each $q$ in the neighbourhood $W$, $\exp_q$ maps the open $\varepsilon$-ball in $TM_q$ diffeomorphically onto an open set $U_q$. The book has no name for such an $\varepsilon$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: for $q \in N$ and $\varepsilon > 0$, let $B_\varepsilon(q) = \{v \in T_qN : \|v\| < \varepsilon\}$. Then $\varepsilon$ is a *normal radius* at $q$ if there are open sets $O, U \subseteq V$ and maps $F$ smooth on $O$ and $G$ smooth on $U$ with: $B_\varepsilon(q) \subseteq O$, $B_\varepsilon(q)$ in the domain of $\exp_q$ and $\exp_q = F$ there; $\exp_q$ maps $B_\varepsilon(q)$ into $U$ with $G(\exp_q v) = v$; and $G$ maps $U_q = N \cap U$ into $B_\varepsilon(q)$ with $\exp_q(G(y)) = y$. So $\exp_q$ is a bijection of $B_\varepsilon(q)$ onto the open subset $U_q$ of $N$, and it and its inverse are restrictions of smooth maps. A normal radius yields a diffeomorphism in Mathlib's sense: $\exp_q$ restricts to a `PartialDiffeomorph` of the open $\varepsilon$-ball onto $U_q$.

- `Morse.NormalCoord` — Morse/Chapter7/NormalNbhd.lean, line 83
- `Morse.IsNormalRadius` — Morse/Chapter7/NormalNbhd.lean, line 108
- `Morse.expToN` — Morse/Chapter7/NormalNbhd.lean, line 661
- `Morse.NormalCoord.expDiffeo` — Morse/Chapter7/NormalNbhd.lean, line 690

*What differs.*
- The notion is the condition in Lemma 10.3 (3), given a name so that later statements can assume it of a single point.
- "Diffeomorphically" is made precise in Milnor's own sense for subsets of Euclidean space (restrictions of smooth maps on open sets), and the diffeomorphism in Mathlib's sense, for the manifold structure of $N$, follows.

### V7.10. Lemma 10.3: uniformly normal neighbourhoods

*restated* · unique initial vector, not geodesic · inverse, not implicit, function theorem

**Milnor (§10, Lemma 10.3, p. 59).** For each $p \in M$ there are a neighbourhood $W$ of $p$ and a number $\varepsilon > 0$ such that: (1) any two points of $W$ are joined by a unique geodesic in $M$ of length $< \varepsilon$; (2) this geodesic depends smoothly on the two points, in that if $t \mapsto \exp_{q_1}(tv)$, $0 \le t \le 1$, is the geodesic joining $q_1$ and $q_2$, the pair $(q_1, v) \in TM$ depends differentiably on $(q_1, q_2)$; (3) for each $q \in W$, $\exp_q$ maps the open $\varepsilon$-ball in $TM_q$ diffeomorphically onto an open set $U_q \supseteq W$. Proof (pp. 58–59): $F(q, v) = (q, \exp_q v)$ has nonsingular Jacobian $\begin{pmatrix} I & I \\ 0 & I \end{pmatrix}$ at $(p, 0)$, and "the implicit function theorem" gives a local inverse.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: for each $p \in N$ there are an open set $O \ni p$ of $V$ and an $\varepsilon > 0$ such that, with $W = N \cap O$: (1) for all $q_1, q_2 \in W$ there is exactly one $v \in T_{q_1}N$ with $\|v\| < \varepsilon$ and $\exp_{q_1}(v) = q_2$; and a geodesic from $q_1$ with initial velocity of norm $< \varepsilon$ ending at $q_2$ is $t \mapsto \exp_{q_1}(tv)$ for this $v$; (2) there are an open $O_2 \subseteq V \times V$ containing $W \times W$ and $G$ smooth on $O_2$ with $G(q_1, q_2)$ the vector of (1); (3) $\varepsilon$ is a normal radius (V7.9) at every $q \in W$, and $U_q \supseteq W$. In particular every point of $N$ has a normal radius, and $\exp_q$ restricts to a `PartialDiffeomorph` of an open ball of $T_qN$ onto an open neighbourhood of $q$ in $N$.

- `Morse.LocalSpray.chartExp` — Morse/Chapter7/NormalNbhd.lean, line 167
- `Morse.LocalSpray.hasFDerivAt_chartF` — Morse/Chapter7/NormalNbhd.lean, line 246
- `Morse.lemma_10_3` — Morse/Chapter7/NormalNbhd.lean, line 320
- `Morse.lemma_10_3_geodesic` — Morse/Chapter7/NormalNbhd.lean, line 611
- `Morse.exists_isNormalRadius` — Morse/Chapter7/NormalNbhd.lean, line 626
- `Morse.exists_expDiffeo` — Morse/Chapter7/NormalNbhd.lean, line 748

*What differs.*
- In (1), "a unique geodesic of length $< \varepsilon$" becomes the unique initial vector $v$ with $\|v\| < \varepsilon$; the geodesic $t \mapsto \exp_{q_1}(tv)$ on $[0, 1]$ has length $\|v\|$ (V7.15), and the initial vector of a geodesic has norm equal to its length (V7.2).
- The theorem used is the inverse function theorem (the companion project's, on manifolds), applied in the slice chart to $(u, w) \mapsto (u, E(u, w))$, whose derivative at $(u_0, 0)$ is $(a, b) \mapsto (a, a + b)$, Milnor's block matrix.
- Taking the neighbourhood of $(p, 0)$ in the form $\{(q, v) : q \in U', \|v\| < \varepsilon\}$ needs such sets to be a neighbourhood base in $TM$, a comparison of $\|v\|$ with the coordinates of $v$ uniform near $p$; the formal proof supplies it.

### V7.10′. The remark after Lemma 10.3: convex neighbourhoods

*restated* · proved in Chapter 10, for Theorem 17.1 · balls of $V$, not metric balls

**Milnor (§10, Remark, p. 59).** Right after Lemma 10.3 Milnor remarks, without proof, that with more care it would be possible to choose $W$ so that the geodesic joining any two of its points lies completely within $W$, and refers to J. H. C. Whitehead, *Convex regions in the geometry of paths* (1932).

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: an open $O \subseteq V$ is a *good ball* if, for one $\delta > 0$, any two points $y, z$ of $N \cap O$ are at distance $\rho(y, z) < \delta$ and joined as in Corollary 10.8 at the scale $\delta$ (V7.20: a unique geodesic $\sigma_{yz}(s) = \exp_y(s\,v)$ with $\|v\| < \delta$, which is minimal and whose initial vector depends smoothly on $(y, z)$), and $\sigma_{yz}(s) \in N \cap O$ for $0 \le s \le 1$. For every $x \in N$ the balls $\{y : \|y - x\| < r\}$ of $V$ are good for all small $r > 0$; and for every compact $K \subseteq N$ there is $\varepsilon > 0$ such that the ball of radius $\varepsilon$ about each point of $K$ lies in a good ball.

- `Morse.IsGoodBall` — Morse/Chapter10/GoodBalls.lean, line 344
- `Morse.exists_isGoodBall_ball` — Morse/Chapter10/GoodBalls.lean, line 554
- `Morse.exists_lebesgue_goodBall` — Morse/Chapter10/GoodBalls.lean, line 621

*What differs.*
- The verified Chapter 7 lists the remark as not formalized; it is proved in Chapter 10 (`Morse/Chapter10/GoodBalls.lean`), where the modified proof of Theorem 17.1 needs neighbourhoods convex for short geodesics (V10.17).
- Milnor's $W$ is a set as in Lemma 10.3; a good ball is the intersection of $N$ with a small ball of $V$, and its scale $\delta$ plays the role of $\varepsilon$. Convexity is proved with the ambient distance, $(\|\gamma - x\|^2)'' = 2\|\gamma'\|^2 + 2\langle\gamma - x, \mathrm{II}(\gamma', \gamma')\rangle > 0$ along a geodesic near $x$, so no normal coordinates are needed.
- That the good ball also satisfies Lemma 10.3 (3) for the same scale is not stated; what is proved is the convexity Milnor asks for, together with the minimality and smooth dependence of the joining geodesics.

### V7.11. Piecewise smooth paths and their lengths

*hypotheses explicit* · break points as a finite set · admissible paths, a wider class · additivity and invariance proved

**Milnor (§11, p. 67; used from p. 59).** A piecewise smooth path is a map $\omega : [0, 1] \to M$ with a subdivision $0 = t_0 < t_1 < \dots < t_k = 1$ such that each $\omega|[t_{i-1}, t_i]$ is $C^\infty$ (p. 67, where the notion is first defined). From Theorem 10.4 on (p. 59) such paths on intervals $[a, b]$, and their arc lengths $\int\|d\omega/dt\|\,dt$, are used without further comment.

**Proved in Lean.** Let $c$ be a curve in a real normed space (complete, for the statements involving $\int c'$) and $a \le b$. The length of $c$ on $[a, b]$ is $L(c|[a, b]) = \int_a^b\|c'(t)\|\,dt$, $c'$ being $0$ where $c$ is not differentiable. $c$ is *piecewise smooth* on $[a, b]$ if it is continuous there and, for a finite set $B$ of break points, $C^\infty$ (one-sided derivatives at the ends) on every $[s, t] \subseteq [a, b]$, $s < t$, with no point of $B$ in $(s, t)$. $c$ is *admissible* on $[a, b]$ if it is continuous there, differentiable off a countable subset of $(a, b)$, and $\|c'\|$ is integrable. Piecewise smooth paths are admissible. For admissible paths $\int_a^bc' = c(b) - c(a)$, so $\|c(b) - c(a)\| \le L$; length is additive under subdivision; a path of length $0$ is constant; and speed $k$ gives length $k(b - a)$. Restriction, concatenation at a common endpoint, reversal and translation of the parameter preserve piecewise smoothness; lengths add under concatenation and are unchanged by reversal and translation.

- `Morse.pathLength` — Morse/Chapter7/Path.lean, line 83
- `Morse.IsPiecewiseSmooth` — Morse/Chapter7/Path.lean, line 191
- `Morse.IsAdmissible` — Morse/Chapter7/Path.lean, line 87
- `Morse.IsAdmissible.norm_sub_le_pathLength` — Morse/Chapter7/Path.lean, line 127
- `Morse.IsAdmissible.pathLength_add` — Morse/Chapter7/Path.lean, line 132
- `Morse.IsAdmissible.eq_of_pathLength_eq_zero` — Morse/Chapter7/Path.lean, line 147
- `Morse.pathLength_concat` — Morse/Chapter7/Path.lean, line 338
- `Morse.pathLength_reverse` — Morse/Chapter7/Path.lean, line 376

*What differs.*
- The subdivision is given as a finite set of break points, and a path is a map on $\mathbb R$ read on $[a, b]$.
- The facts Milnor uses without comment are stated: integrability of $\|d\omega/dt\|$, additivity of length under subdivision and concatenation, invariance under reversal and translation, and $\|c(b) - c(a)\| \le L$.
- The lower bounds for lengths (V7.13–V7.16) are proved for admissible paths, a class that contains the piecewise smooth paths and is closed under restriction, which is what the shell-crossing argument needs.

### V7.12. Lemma 10.5: the Gauss lemma

*stronger* · the identity for every $x$, not $x \perp w$ · no curve $v(t)$ needed

**Milnor (§10, Lemma 10.5, p. 60).** In $U_q$ the geodesics through $q$ are the orthogonal trajectories of the hypersurfaces $\{\exp_q(v) : \|v\| = \text{constant}\}$. The proof considers the surface $f(r, t) = \exp_q(r\,v(t))$ for a curve $v(t)$ of unit vectors and shows that $\langle\partial f/\partial r, \partial f/\partial t\rangle$ is independent of $r$, hence zero.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $\varepsilon$ be a normal radius at $q \in N$ (V7.9) and regard $\exp_q$ as a map on the vector space $T_qN$. For $w, x \in T_qN$ with $\|w\| < \varepsilon$, $$\langle d(\exp_q)_w(w),\ d(\exp_q)_w(x)\rangle = \langle w, x\rangle;$$ in particular the radial velocity $d(\exp_q)_w(w)$ is orthogonal to $d(\exp_q)_w(x)$ when $x \perp w$. Moreover $d(\exp_q)_w$ is injective on $T_qN$, and $\|d(\exp_q)_{rw}(w)\| = \|w\|$ for $0 \le r \le 1$.

- `Morse.NormalCoord.norm_fderiv_F_apply` — Morse/Chapter7/GaussLemma.lean, line 116
- `Morse.NormalCoord.injective_fderiv_F` — Morse/Chapter7/GaussLemma.lean, line 175
- `Morse.gauss_lemma` — Morse/Chapter7/GaussLemma.lean, line 390
- `Morse.gauss_lemma_orthogonal` — Morse/Chapter7/GaussLemma.lean, line 413

*What differs.*
- The identity holds for every $x \in T_qN$; Milnor's orthogonality of trajectories is its case $x \perp w$, the vectors $x \perp w$ forming the tangent space at $w$ of the sphere $\{\|v\| = \|w\|\}$.
- That the sets $\{\exp_q(v) : \|v\| = \text{constant}\}$ are hypersurfaces with the expected tangent vectors uses that $\exp_q$ is a diffeomorphism on the ball, which the formal statement takes as the normal-radius hypothesis.
- The proof is Milnor's, with $f(r, s) = \exp_q(r(w + sx))$; the symmetry of second derivatives in $V$ replaces Lemma 8.7, and the radial geodesic's normal acceleration kills $\langle\partial^2f/\partial r^2, \partial f/\partial s\rangle$.

### V7.13. Lemma 10.6: length and radius in a normal ball

*narrower* · $r(b) - r(a)$, not $|r(b) - r(a)|$ · equality: $v$ constant only · admissible paths

**Milnor (§10, Lemma 10.6, p. 60).** Let $\omega : [a, b] \to U_q - \{q\}$ be piecewise smooth, written $\omega(t) = \exp_q(r(t)v(t))$ with $0 < r(t) < \varepsilon$ and $\|v(t)\| = 1$. Then $\int_a^b\|d\omega/dt\|\,dt \ge |r(b) - r(a)|$, with equality only if $r$ is monotone and $v$ constant. The proof (p. 61) splits $d\omega/dt = \frac{\partial f}{\partial r}r'(t) + \frac{\partial f}{\partial t}$ into orthogonal parts by the Gauss lemma.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $\varepsilon$ be a normal radius at $q$, with $U_q$ and $G = \exp_q^{-1}$ as in V7.9, and let $c$ be admissible on $[a, b]$ (V7.11) with $c(t) \in U_q$ and $c(t) \ne q$ for $t \in [a, b]$; write $r(t) = \|G(c(t))\| \in (0, \varepsilon)$ and $v(t) = G(c(t))/r(t)$. Then $L(c|[a, b]) \ge r(b) - r(a)$, and if equality holds, $v$ is constant on $[a, b]$. Pointwise, at each $t \in (a, b)$ where $c$ is differentiable, $r$ is differentiable with $|r'(t)| \le \|c'(t)\|$, and $r'(t) = \|c'(t)\|$ forces $v'(t) = 0$.

- `Morse.NormalCoord.hasDerivAt_radius` — Morse/Chapter7/GaussLemma.lean, line 306
- `Morse.NormalCoord.radius_sub_le_pathLength` — Morse/Chapter7/Shortest.lean, line 170
- `Morse.NormalCoord.direction_eq_of_pathLength_eq` — Morse/Chapter7/Shortest.lean, line 199

*What differs.*
- The bound is one-sided, $r(b) - r(a)$ rather than $|r(b) - r(a)|$, which is the case Theorem 10.4 uses; the two-sided form is not formalized.
- The equality clause gives only that $v$ is constant; the monotone parametrization appears in the sharp equality case of Theorem 10.4 (V7.16) instead.
- The paths are admissible rather than piecewise smooth. The step from $\partial f/\partial t = 0$ to $dv/dt = 0$ needs $d(\exp_q)$ injective (V7.12) and $r > 0$; the formal proof avoids the orthogonal splitting, using $\langle d(\exp_q)_w(w), c'\rangle = rr'$ and the Cauchy–Schwarz inequality.

### V7.14. Paths leaving a normal ball: the shell crossing

*restated* · last visit of $q$ replaces $\delta \to 0$ · paths may leave $U_q$ and return

**Milnor (§10, proof of Theorem 10.4, p. 61).** In the proof of Theorem 10.4, Milnor observes that for every $\delta > 0$ a path from $q$ to a point of the shell of radius $r$ contains a segment that joins the shells of radii $\delta$ and $r$ and lies between them; by Lemma 10.6 that segment has length $\ge r - \delta$, and letting $\delta \to 0$ gives length $\ge r$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $\varepsilon$ be a normal radius at $q$ and $0 < s < \varepsilon$. The open normal ball $\exp_q\{\|v\| < s\}$ is the intersection of $N$ with an open set of $V$; the closed normal ball $\exp_q\{\|v\| \le s\}$ is compact, hence closed in $V$. If $c$ is an admissible path in $N$ on $[a, b]$ with $c(a) = q$ and $c(b)$ outside the open normal ball of radius $s$, there are $a \le t_1 < t_2 \le b$ with $c(t_1) = q$, $c(t) \in U_q \setminus \{q\}$ for $t_1 < t \le t_2$, $c(t)$ in the open normal ball for $t_1 \le t < t_2$, $\|G(c(t_2))\| = s$, and $L(c|[t_1, t_2]) \ge s$.

- `Morse.NormalCoord.ballSet` — Morse/Chapter7/Shortest.lean, line 109
- `Morse.NormalCoord.closedBallSet` — Morse/Chapter7/Shortest.lean, line 120
- `Morse.NormalCoord.isCompact_closedBallSet` — Morse/Chapter7/Shortest.lean, line 124
- `Morse.NormalCoord.exists_crossing` — Morse/Chapter7/Shortest.lean, line 283

*What differs.*
- The shells of radius $\delta \to 0$ are replaced by the last visit of $q$ before the first exit from the ball, the limit being taken inside the proof (the exposition's Lemma C).
- A competing path may leave $U_q$ and come back; the segment exists because closed normal balls are closed in $M$, compact in a Hausdorff space, which puts the first exit point on the shell. Milnor's argument leaves this implicit.

### V7.15. Theorem 10.4: short geodesics are shortest

*stronger* · paths on any parameter interval · in (i), admissible paths

**Milnor (§10, Theorem 10.4, p. 59).** Let $W$ and $\varepsilon$ be as in Lemma 10.3, let $\gamma : [0, 1] \to M$ be the geodesic of length $< \varepsilon$ joining two points of $W$, and let $\omega : [0, 1] \to M$ be any other piecewise smooth path joining the same two points. Then $\int_0^1\|d\gamma/dt\|\,dt \le \int_0^1\|d\omega/dt\|\,dt$, where equality can hold only if the point sets $\omega([0, 1])$ and $\gamma([0, 1])$ coincide. Thus $\gamma$ is the shortest path joining its end points. Proof on p. 61.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: (i) if $\varepsilon$ is a normal radius at $q$ and $v \in T_qN$ with $\|v\| < \varepsilon$, then $t \mapsto \exp_q(tv)$ is a geodesic near $[0, 1]$ with initial velocity $v$ and length $\|v\|$ on $[0, 1]$, and every admissible path in $N$, on any $[a, b]$, from $q$ to $\exp_q(v)$ has length $\ge \|v\|$, whether or not it stays in $U_q$. (ii) For each $p \in N$ there are an open $O \ni p$ of $V$ and an $\varepsilon > 0$ such that for all $q_1, q_2 \in N \cap O$ there is $v \in T_{q_1}N$ with $\|v\| < \varepsilon$ and $\exp_{q_1}(v) = q_2$, the geodesic $\gamma(t) = \exp_{q_1}(tv)$, $0 \le t \le 1$, has length $\|v\|$, and every piecewise smooth path $c$ in $N$ on any $[a, b]$ from $q_1$ to $q_2$ has $L(c|[a, b]) \ge \|v\|$, with equality only if $c([a, b]) = \gamma([0, 1])$.

- `Morse.NormalCoord.radial` — Morse/Chapter7/Shortest.lean, line 145
- `Morse.NormalCoord.pathLength_exp_smul` — Morse/Chapter7/Shortest.lean, line 159
- `Morse.NormalCoord.norm_le_pathLength` — Morse/Chapter7/Shortest.lean, line 375
- `Morse.theorem_10_4` — Morse/Chapter7/Shortest.lean, line 513

*What differs.*
- Competing paths are parametrized on any interval $[a, b]$, not only $[0, 1]$, and in (i) they need only be admissible.
- The proof needs the shell-crossing step (V7.14), because a competing path may leave the normal neighbourhood; the equality clause is the sharper V7.16.

### V7.16. The equality case of Theorem 10.4, sharp form

*stronger* · monotone reparametrization · equal images too weak for 10.7

**Milnor (§10, Theorem 10.4, pp. 59 and 61).** Theorem 10.4 says that equality of lengths can hold only if the point sets $\omega([0, 1])$ and $\gamma([0, 1])$ coincide; on p. 61 Milnor adds that if the images differ, a strict inequality is "easily" obtained.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $\varepsilon$ be a normal radius at $q$, $v \in T_qN$ with $0 < \|v\| < \varepsilon$, and $c$ an admissible path in $N$ on $[a, b]$ from $q$ to $\exp_q(v)$ of length exactly $\|v\|$. Then $$c(t) = \exp_q(\rho(t)v),\qquad \rho(t) = L(c|[a, t])/\|v\|,\qquad a \le t \le b,$$ with $\rho$ continuous and nondecreasing, $\rho(a) = 0$ and $\rho(b) = 1$: $c$ is a monotone reparametrization of the geodesic $t \mapsto \exp_q(tv)$, $0 \le t \le 1$. Milnor's conclusion $c([a, b]) = \gamma([0, 1])$ follows.

- `Morse.NormalCoord.eq_exp_of_pathLength_eq` — Morse/Chapter7/Shortest.lean, line 393
- `Morse.IsAdmissible.monotoneOn_pathLength` — Morse/Chapter7/Path.lean, line 163
- `Morse.NormalCoord.image_eq_of_pathLength_eq` — Morse/Chapter7/Shortest.lean, line 476

*What differs.*
- A monotone reparametrization replaces equal images. Equal images are too weak for Corollary 10.7: a path running along $\gamma$ at varying speed has the same image, and the proof of 10.7 needs the reparametrization form (V7.17).
- The equality analysis that Milnor leaves to the reader is carried out: the path is constant before its last visit of $q$ and after its first arrival on the shell, and between them equality in Lemma 10.6 fixes the direction.

### V7.17. Corollary 10.7: shortest paths are geodesics

*stronger* · extends past both ends · needs the sharp equality case

**Milnor (§10, Corollary 10.7, p. 61).** If a path $\omega : [0, \ell] \to M$, parametrized by arc length, has length less than or equal to the length of any other path from $\omega(0)$ to $\omega(\ell)$, then $\omega$ is a geodesic. The proof applies Theorem 10.4 to each segment of $\omega$ that lies in a set $W$ of Lemma 10.3 and has length $< \varepsilon$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $c$ be a piecewise smooth path in $N$ on $[0, \ell]$ with $\|c'(t)\| = 1$ at every $t \in (0, \ell)$ where $c$ is differentiable, whose length is at most that of every piecewise smooth path in $N$, on any parameter interval, from $c(0)$ to $c(\ell)$. Then $c$ is a geodesic on $(0, \ell)$ (in particular smooth there, also at its break points), and $c$ agrees on $[0, \ell]$ with a geodesic defined on an open interval $(-\delta, \ell + \delta)$. On the way: being a geodesic is a local property, and a segment of $c$ inside a set of Lemma 10.3 agrees with a geodesic on an open set containing it.

- `Morse.isGeodesicOn_of_locally` — Morse/Chapter7/Minimal.lean, line 61
- `Morse.minimal_segment` — Morse/Chapter7/Minimal.lean, line 76
- `Morse.corollary_10_7` — Morse/Chapter7/Minimal.lean, line 207
- `Morse.corollary_10_7_extend` — Morse/Chapter7/Minimal.lean, line 238

*What differs.*
- The formal statement adds that $c$ extends to a geodesic on an open interval containing $[0, \ell]$.
- As stated, the equality clause of Theorem 10.4 (equal images) does not make a segment a geodesic; the proof needs V7.16 together with unit speed, which makes the reparametrization affine.
- Also needed: each segment is minimal between its end points (replacing it by the geodesic of Lemma 10.3 gives a competitor, by concatenation), the segments must contain the break points in their interiors, and being a geodesic is local.

### V7.18. The distance $\rho$

*restated* · values in $[0, \infty]$ · positivity is not clear: shell crossing

**Milnor (§10, p. 62).** For $p, q \in M$, $\rho(p, q)$ is the greatest lower bound of the arc lengths of the piecewise smooth paths joining $p$ and $q$, and this "clearly" makes $M$ a metric space.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: for $p, q \in V$, $\rho(p, q) \in [0, \infty]$ is the infimum of the lengths of the piecewise smooth paths $c$ in $N$, on any $[a, b]$, with $c(a) = p$ and $c(b) = q$ ($\infty$ if there is none, as when $q \notin N$). Then $\rho(p, q) \le L(c|[a, b])$ for every such path, $\rho(p, p) = 0$ for $p \in N$, $\rho$ is symmetric and satisfies the triangle inequality; if $\varepsilon$ is a normal radius at $p$ and $0 < s < \varepsilon$, every point outside the open normal ball of radius $s$ about $p$ is at distance $\ge s$; and for $p, q \in N$, $\rho(p, q) = 0$ implies $p = q$. So $\rho$ is a metric on $N$ with values in $[0, \infty]$.

- `Morse.riemDist` — Morse/Chapter7/Distance.lean, line 77
- `Morse.riemDist_le_pathLength` — Morse/Chapter7/Distance.lean, line 80
- `Morse.riemDist_triangle` — Morse/Chapter7/Distance.lean, line 113
- `Morse.NormalCoord.ofReal_le_riemDist` — Morse/Chapter7/Distance.lean, line 157
- `Morse.eq_of_riemDist_eq_zero` — Morse/Chapter7/Distance.lean, line 229

*What differs.*
- $\rho$ is $\infty$ between points that no path joins, and $N$ need not be connected; finiteness needs Milnor's standing assumption that $M$ is connected (V7.21).
- Positivity is not "clear": a path from $p$ to $q$ may leave every normal neighbourhood of $p$, and the lower bound needs the shell-crossing lemma (V7.14).

### V7.19. Metric balls and the topology

*restated* · neighbourhood bases at each point · small metric balls are normal balls

**Milnor (§10, p. 62).** The compatibility of the metric $\rho$ with the usual topology of $M$ follows "easily" from Theorem 10.4.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $\varepsilon$ be a normal radius at $p \in N$. For $v \in T_pN$ with $\|v\| < \varepsilon$, $\rho(p, \exp_pv) = \|v\|$; and for $0 < r \le \varepsilon$, $\rho(p, y) < r$ iff $y$ lies in the normal ball $\exp_p\{v \in T_pN : \|v\| < r\}$. Consequently, for every $p \in N$, the metric balls $\{y : \rho(p, y) < r\}$, $r > 0$, form a basis of the neighbourhoods of $p$ in $N$ for the topology of a subspace of $V$.

- `Morse.NormalCoord.riemDist_exp` — Morse/Chapter7/Distance.lean, line 186
- `Morse.NormalCoord.riemDist_lt_iff` — Morse/Chapter7/Distance.lean, line 197
- `Morse.hasBasis_nhdsWithin_riemDist` — Morse/Chapter7/Distance.lean, line 250

*What differs.*
- Compatibility is stated as the neighbourhood-basis property at each point; the metric space structure it yields is V7.21.
- The "easy" argument needs that small metric balls are normal balls (the shell crossing again) and that normal balls of small radius lie in any given neighbourhood of $p$ (continuity of $\exp_p$ at $0$).

### V7.20. Corollary 10.8: short joins on a compact set

*restated* · uniqueness of the initial vector · finite subcover, Lebesgue number

**Milnor (§10, Corollary 10.8, p. 62).** Given a compact set $K \subseteq M$ there is a number $\delta > 0$ such that any two points of $K$ with distance less than $\delta$ are joined by a unique geodesic of length less than $\delta$; this geodesic is minimal, and depends differentiably on its end points. Proof: cover $K$ by open sets $W$ as in Lemma 10.3 and let $\delta$ be small enough that any two points of $K$ at distance $< \delta$ lie in a common $W$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $K \subseteq N$ be compact. There is $\delta > 0$ such that for all $y, z \in K$ with $\rho(y, z) < \delta$: there is $v \in T_yN$ with $\|v\| < \delta$ and $\exp_y(v) = z$; the geodesic $t \mapsto \exp_y(tv)$, $0 \le t \le 1$, of length $\|v\|$, is minimal, $\rho(y, z) = \|v\|$; $v$ is the only $w \in T_yN$ with $\|w\| < \delta$ and $\exp_y(w) = z$; and there are an open $O_2 \ni (y, z)$ and a map $G$ smooth on $O_2$ with $G(y, z) = v$ such that for $y', z' \in N$ with $(y', z') \in O_2$ and $\rho(y', z') < \delta$, $G(y', z') \in T_{y'}N$, $\|G(y', z')\| < \delta$ and $\exp_{y'}(G(y', z')) = z'$.

- `Morse.IsShortJoin` — Morse/Chapter7/Distance.lean, line 302
- `Morse.exists_isShortJoin` — Morse/Chapter7/Distance.lean, line 314
- `Morse.corollary_10_8` — Morse/Chapter7/Distance.lean, line 369

*What differs.*
- Uniqueness is stated for initial vectors: a geodesic from $y$ defined near $[0, 1]$ and ending at $z$ with initial velocity $w$ has length $\|w\|$ and $\exp_y(w) = z$ (V7.2, V7.7). "Depends differentiably" means that near each pair the initial vector is the restriction of a smooth map on an open set of $V \times V$, on the pairs at distance $< \delta$.
- The choice of $\delta$ is a Lebesgue-number argument with a finite subcover; uniqueness among geodesics of length $< \delta$ needs $\delta$ at most the $\varepsilon$ of each set of the cover, else Lemma 10.3 (1) does not apply; minimality is Theorem 10.4, through $\rho(y, z) = \|v\|$.

### V7.21. Continuity and finiteness of $\rho$; the metric space $(N, \rho)$

*restated* · continuity of $\rho$, used, never stated · connected means preconnected

**Milnor (§10, p. 62).** Milnor says that $\rho$ "clearly" makes $M$ a metric space, compatible with its topology by Theorem 10.4; finiteness rests on the standing assumption that $M$ is connected (p. 55). The continuity of $\rho$ is never stated, but the proof of Theorem 10.9 uses it (p. 63: a point of the compact shell $S$ at minimum distance from $q$, and an equality at the supremum $t_0$ "by continuity").

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: for all $p, q \in V$, $\|q - p\| \le \rho(p, q)$. The function $(x, y) \mapsto \rho(x, y)$, with values in $[0, \infty]$, is continuous on $N \times N$ (topology of a subspace of $V \times V$). If $N$ is (pre)connected, $\rho(p, q) < \infty$ for all $p, q \in N$. Hence $\rho$ makes $N$ an extended metric space whose topology is that of $N$, and, for connected $N$, a metric space with distance $\rho$ and the topology of $N$; these structures are given by name, since $N$ already carries the metric of $V$.

- `Morse.ofReal_norm_sub_le_riemDist` — Morse/Chapter7/Metric.lean, line 78
- `Morse.continuous_riemDist` — Morse/Chapter7/Metric.lean, line 136
- `Morse.riemDist_ne_top` — Morse/Chapter7/Metric.lean, line 147
- `Morse.riemEMetricSpace` — Morse/Chapter7/Metric.lean, line 262
- `Morse.riemMetricSpace` — Morse/Chapter7/Metric.lean, line 269
- `Morse.riemMetricSpace_topology` — Morse/Chapter7/Metric.lean, line 282

*What differs.*
- The continuity of $\rho$, which the book uses in the proof of Theorem 10.9 without stating it, is proved, from $|\rho(x, y) - \rho(x', y')| \le \rho(x, x') + \rho(y, y')$ and V7.19.
- Connectedness is needed only for finiteness; in the formal statements "connected" is preconnected, which also admits $N = \emptyset$. The points at finite distance from $p$ form an open and closed subset of $N$.

### V7.22. Metric and geodesic completeness

*restated* · open intervals, not closed segments · the equivalence glues geodesics

**Milnor (§10, pp. 58, 62 and 64).** $M$ is *geodesically complete* if $\exp_q(v)$ is defined for all $q \in M$ and all $v \in TM_q$; this is "clearly" equivalent to the requirement that every geodesic segment $\gamma_0 : [a, b] \to M$ can be extended to an infinite geodesic $\gamma : \mathbb R \to M$ (p. 58, recalled p. 62). On p. 64: a subset of $M$ is bounded if it has finite diameter, and $M$ is complete as a metric space if every Cauchy sequence converges.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: $(N, \rho)$ is *complete* if every sequence in $N$ that is Cauchy for $\rho$ converges for $\rho$ to some point of $N$; for connected $N$ this is the completeness of the metric space of V7.21. A set $X \subseteq V$ is *bounded* if $\rho(x, y) \le d$ for all $x, y \in X$ and some real $d$ (a nonempty bounded set lies in $N$). $N$ is *geodesically complete* if $\exp_q(v)$ is defined for every $q \in N$ and $v \in T_qN$. If $\exp_q$ is defined on all of $T_qN$, then $t \mapsto \exp_q(tv)$ is a geodesic on $\mathbb R$ for every $v$; and $N$ is geodesically complete iff every geodesic on a nonempty open interval (or preconnected open set) is the restriction of a geodesic on $\mathbb R$.

- `Morse.IsRiemComplete` — Morse/Chapter7/Metric.lean, line 177
- `Morse.IsRiemBounded` — Morse/Chapter7/Metric.lean, line 185
- `Morse.IsGeodesicallyComplete` — Morse/Chapter7/GeodesicFlow.lean, line 562
- `Morse.isGeodesicOn_univ_exp_smul` — Morse/Chapter7/GeodesicFlow.lean, line 567
- `Morse.isGeodesicallyComplete_iff` — Morse/Chapter7/GeodesicFlow.lean, line 607

*What differs.*
- Milnor's segments on closed intervals are replaced by geodesics on open intervals, as in V7.7.
- The "clear" equivalence glues geodesics, which needs their uniqueness in the large (V7.5).

### V7.23. The geodesic flow, and the continuity of $\exp$

*hypotheses explicit* · global continuity of $\exp$, used on p. 64 · smoothness only later (V11.1) · no maximal geodesics

**Milnor (§10, pp. 57, 58, 62 and 64).** Milnor uses, without stating them as results: that a geodesic is $t \mapsto \exp_q(tv)$ (p. 57); that geodesics can be continued (pp. 58, 62); and, in the proof of Corollary 10.10 (p. 64), that $\exp_p$ maps the disk of radius $d$ in $TM_p$ onto a compact set, which needs $\exp_p$ continuous on the whole disk. Lemma 10.2 concerns small vectors only.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: (i) a geodesic on an open interval containing $0$ is $t \mapsto \exp_{\gamma(0)}(t\gamma'(0))$ there. (ii) For $x_0 \in N$ and $R > 0$ there are an open $U \ni x_0$, a time $\tau > 0$ and a map $\Phi$ continuous on $U \times \{\|w\| < R\} \times (-\tau, \tau)$ such that for $y \in N \cap U$ and $w \in T_yN$ with $\|w\| < R$, $t \mapsto \exp_y(tw)$ is a geodesic on $(-\tau, \tau)$ whose position and velocity at time $t$ are $\Phi(y, w, t)$. (iii) Geodesics $t \mapsto \exp_y(tw)$ on an open interval $I \ni 0$ continue, from the position and velocity at any $s \in I$, by the geodesic with those initial data. (iv) The domain of $\exp$ is open in $TN$, and $\exp$ is continuous on it; in particular, if $\exp_p$ is defined on all of $T_pN$, it is continuous there.

- `Morse.IsGeodesicOn.exp_smul_eq` — Morse/Chapter7/GeodesicFlow.lean, line 88
- `Morse.exists_localFlow_exp` — Morse/Chapter7/GeodesicFlow.lean, line 131
- `Morse.isGeodesicOn_exp_smul_union` — Morse/Chapter7/GeodesicFlow.lean, line 267
- `Morse.eventually_mem_expDom_and_continuousWithinAt_exp` — Morse/Chapter7/GeodesicFlow.lean, line 365
- `Morse.continuousOn_exp` — Morse/Chapter7/GeodesicFlow.lean, line 550

*What differs.*
- Corollary 10.10 needs the continuity of $\exp_p$ on a whole disk, a global dependence of geodesics on their initial data that Lemma 10.2 does not give; it is proved here, by covering the compact arc with finitely many sets of (ii) and continuing step by step with (iii).
- Only continuity of $\exp$ on its open domain is proved in Chapter 7, which is all that Corollary 10.10 needs; smoothness on the whole domain is V11.1, proved in Chapter 11.
- Maximal geodesics, which the exposition uses (its Lemma B), are not constructed: geodesics are glued by (iii) instead.

### V7.24. Minimal geodesics

*restated* · a geodesic near $[a, b]$, not on it

**Milnor (§10, pp. 61–62).** A geodesic $\gamma : [a, b] \to M$ is *minimal* if its length is less than or equal to the length of any other piecewise smooth path joining its end points.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: a curve $\gamma$ is a minimal geodesic on $[a, b]$, $a \le b$, if it is a geodesic on some open set containing $[a, b]$ and $L(\gamma|[a, b]) \le L(c|[a', b'])$ for every piecewise smooth path $c$ in $N$, on any $[a', b']$, with $c(a') = \gamma(a)$ and $c(b') = \gamma(b)$. Where $\exp_q(v)$ is defined it lies in $N$. If $v \in T_pN$, $t \mapsto \exp_p(tv)$ is a geodesic on $\mathbb R$ and $\rho(p, \exp_pv) = \|v\|$, then $t \mapsto \exp_p(tv)$ is a minimal geodesic on $[0, 1]$, of length $\|v\|$.

- `Morse.IsMinimalGeodesic` — Morse/Chapter7/HopfRinow.lean, line 101
- `Morse.exp_mem_of_mem_expDom` — Morse/Chapter7/HopfRinow.lean, line 109
- `Morse.isMinimalGeodesic_exp_smul` — Morse/Chapter7/HopfRinow.lean, line 281

*What differs.*
- A geodesic on an open set containing $[a, b]$ replaces one on $[a, b]$, as in V7.7; competing paths may be parametrized on any interval.

### V7.25. The two steps of the proof of Theorem 10.9

*hypotheses explicit* · $\delta < \rho(p, q)$ needed · unit speed on both pieces

**Milnor (§10, proof of Theorem 10.9, pp. 63–64).** In the proof of the Hopf–Rinow theorem: since every path from $p$ to $q$ passes through the shell $S$ of radius $\delta$ about $p$, $\rho(p, q) = \min_{s \in S}(\rho(p, s) + \rho(s, q)) = \delta + \rho(p_0, q)$ for a point $p_0 \in S$ (p. 63). Later (pp. 63–64) a broken geodesic from $p$ through $\gamma(t_0)$ is shown to have minimal length, so it is an unbroken geodesic by Corollary 10.7, "and hence coincides with $\gamma$".

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: (i) let $\varepsilon$ be a normal radius at $p \in N$, $0 < \delta < \varepsilon$, and $q$ with $\delta < \rho(p, q) < \infty$. There is $w \in T_pN$ with $\|w\| = \delta$ and $\rho(p, q) = \delta + \rho(\exp_pw, q)$. (ii) Let $\gamma$ be a geodesic on $\mathbb R$ with $\|\gamma'(0)\| = 1$, $0 < t_0 < t_1$, and $\sigma$ a geodesic on an open (preconnected) set containing $[t_0, t_1]$ with $\|\sigma'(t_0)\| = 1$ and $\sigma(t_0) = \gamma(t_0)$. If $\rho(\gamma(0), \sigma(t_1)) \ge t_1$, i.e. the broken path ($\gamma$ on $[0, t_0]$, then $\sigma$), of length $t_1$, is minimal, then $\sigma(t_1) = \gamma(t_1)$.

- `Morse.NormalCoord.exists_riemDist_eq_add` — Morse/Chapter7/HopfRinow.lean, line 129
- `Morse.broken_geodesic_eq` — Morse/Chapter7/HopfRinow.lean, line 208

*What differs.*
- In (i) the hypothesis $\delta < \rho(p, q)$ is needed, not only $\delta < \varepsilon$: otherwise $q$ lies inside the shell and paths from $p$ to $q$ need not meet it. That every path crosses the shell is V7.14, and the minimum exists because the shell is compact and nonempty and $\rho(\cdot, q)$ is continuous (V7.21).
- In (ii), "coincides with $\gamma$" needs unit speed on both pieces, for Corollary 10.7, and the uniqueness of geodesics in the large (V7.5) from a time before the break.

### V7.26. Theorem 10.9: the Hopf–Rinow theorem

*stronger* · completeness at one point suffices · length equals $\rho(p, q)$

**Milnor (§10, Theorem 10.9, p. 62).** If $M$ is geodesically complete, then any two points can be joined by a minimal geodesic. The proof (pp. 62–64, with Diagram 10) follows the geodesic from $p$ in the direction of the point of a small shell nearest to $q$, and shows by a supremum argument that it reaches $q$ at time $\rho(p, q)$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: (i) let $p \in N$ be such that $\exp_p$ is defined on all of $T_pN$. Every $q \in N$ with $\rho(p, q) < \infty$ is $\exp_p(v)$ for some $v \in T_pN$ with $\|v\| = \rho(p, q)$, and $t \mapsto \exp_p(tv)$ is a minimal geodesic on $[0, 1]$ (V7.24) from $p$ to $q$. (ii) If $N$ is (pre)connected and geodesically complete, any two points $p, q \in N$ are joined by a minimal geodesic $\gamma$ on $[0, 1]$, $\gamma(0) = p$, $\gamma(1) = q$, whose length is $\rho(p, q)$.

- `Morse.theorem_10_9` — Morse/Chapter7/HopfRinow.lean, line 308
- `Morse.theorem_10_9'` — Morse/Chapter7/HopfRinow.lean, line 449

*What differs.*
- Part (i) uses completeness only at $p$, as the exposition remarks after the proof; Milnor assumes $\exp_q$ defined for every $q$.
- The hidden hypotheses of V7.25 are used, together with $\delta' < r - t_0$ in the inductive step (otherwise the new time overshoots $r = \rho(p, q)$); the supremum argument is a continuous induction on $[\delta, r]$, closed by the continuity of $\rho$; connectedness gives $\rho(p, q) < \infty$.

### V7.27. Corollary 10.10: bounded sets and metric completeness

*stronger* · completeness at one point suffices · needs $\exp_p$ continuous on the disk

**Milnor (§10, Corollary 10.10, p. 64).** If $M$ is geodesically complete, then every bounded subset of $M$ has compact closure; consequently $M$ is complete as a metric space. Proof: for $X$ of diameter $d$ and $p \in X$, $\exp_p$ maps the disk of radius $d$ in $TM_p$ onto a compact set which, by Theorem 10.9, contains $X$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: (i) if $N$ is (pre)connected and $\exp_p$ is defined on all of $T_pN$ for some $p \in N$, every bounded $X \subseteq V$ (V7.22) has compact closure, contained in $N$. (ii) If every bounded set has compact closure contained in $N$, then $(N, \rho)$ is complete. (iii) Hence, if $N$ is connected and geodesically complete, every bounded set has compact closure in $N$, and $(N, \rho)$ is complete.

- `Morse.isCompact_closure_of_isRiemBounded` — Morse/Chapter7/HopfRinow.lean, line 464
- `Morse.isRiemComplete_of_forall_isCompact_closure` — Morse/Chapter7/HopfRinow.lean, line 513
- `Morse.corollary_10_10` — Morse/Chapter7/HopfRinow.lean, line 548

*What differs.*
- Part (i) needs completeness at one point only.
- The proof uses the continuity of $\exp_p$ on the whole disk (V7.23 (iv)), which the book takes for granted; connectedness, so that distances are finite and Theorem 10.9 reaches all of $X$; and, for completeness, that a Cauchy sequence is bounded and converges once a subsequence does.
- The closure is taken in $V$; as it lies in $N$, it is also the closure in $N$.

### V7.28. The converse of Corollary 10.10

*stronger* · proved, not left to Hopf–Rinow · no connectedness · Lemma 10.2, not 10.3

**Milnor (§10, p. 64).** Conversely, if $M$ is complete as a metric space, then it is "not difficult, using Lemma 10.3" to prove that $M$ is geodesically complete. Milnor leaves the details to Hopf and Rinow.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: if $(N, \rho)$ is complete (V7.22), then $N$ is geodesically complete. No connectedness is assumed.

- `Morse.isGeodesicallyComplete_of_isRiemComplete` — Morse/Chapter7/GeodesicFlow.lean, line 643

*What differs.*
- Milnor states the converse and gives no proof; the formal statement is proved, and needs no connectedness of $N$ (Milnor's standing assumption).
- The proof uses the uniform local existence of Lemma 10.2 (V7.23 (ii)), not Lemma 10.3: if $\gamma(t) = \exp_q(tv)$ existed only up to $T_0$, the points $\gamma(t_n)$, $t_n \uparrow T_0$, would form a Cauchy sequence, converging to some $x$ near which all geodesics of speed $\|v\|$ exist for a uniform time.

### V7.29. The Hopf–Rinow equivalence

*stronger* · four-way equivalence · completeness at one point · closed bounded sets compact

**Milnor (§10, p. 64).** After Corollary 10.10 and its converse, Milnor no longer distinguishes geodesic from metric completeness, and calls such an $M$ simply a *complete* Riemannian manifold.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: for a (pre)connected nonempty $N$ the following are equivalent: (1) $(N, \rho)$ is complete; (2) $N$ is geodesically complete; (3) $\exp_p$ is defined on all of $T_pN$ for some $p \in N$; (4) every bounded set has compact closure, contained in $N$. If $N$ is connected and $(N, \rho)$ complete, then $N$ is geodesically complete, every geodesic on an open interval is the restriction of a geodesic on $\mathbb R$, any two points are joined by a minimal geodesic on $[0, 1]$ whose length is their distance, and every bounded subset of $N$ that is closed in $N$ is compact.

- `Morse.hopf_rinow` — Morse/Chapter7/HopfRinow.lean, line 590
- `Morse.hopf_rinow_of_isRiemComplete` — Morse/Chapter7/HopfRinow.lean, line 607
- `Morse.isCompact_of_isClosed_of_isRiemBounded` — Morse/Chapter7/HopfRinow.lean, line 571

*What differs.*
- Condition (3), completeness of $\exp$ at a single point, and the compactness of closed bounded sets are not in the book; the equivalence of (1) and (2) is what Milnor's usage presupposes.
- Connectedness is assumed, as Milnor does throughout; the proof is (2) ⇒ (3) since $N \ne \emptyset$, then V7.27 (i), V7.27 (ii) and V7.28.

### V7.30. Closed submanifolds are complete; the sphere

*not in the book* · the source of complete manifolds here · great circles not identified (see V10.23)

**Milnor (§10, cf. p. 65).** The book has no such statement. On p. 65 Milnor shows that the geodesics of the unit sphere $S^n$ are the great circles and discusses which arcs are minimal; the exposition (Chapter 7, §5) notes that compact Riemannian manifolds are complete.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: convergence in $N$ implies convergence for $\rho$. If $N$ is closed in $V$, then $(N, \rho)$ is complete. Hence a (pre)connected $N$ that is closed in $V$, in particular a connected compact one, is geodesically complete, every geodesic extends to $\mathbb R$, and any two of its points are joined by a minimal geodesic on $[0, 1]$ whose length is their distance. The unit sphere $S^n \subseteq \mathbb R^{n+1}$, $n \ge 1$ (the companion project's slice submanifold), is geodesically complete, and any two of its points are joined by a minimal geodesic on $[0, 1]$ of length their distance.

- `Morse.tendsto_riemDist_of_tendsto` — Morse/Chapter7/Metric.lean, line 190
- `Morse.isRiemComplete_of_isClosed` — Morse/Chapter7/Metric.lean, line 203
- `Morse.hopf_rinow_of_isClosed` — Morse/Chapter7/HopfRinow.lean, line 625
- `Morse.hopf_rinow_of_isCompact` — Morse/Chapter7/HopfRinow.lean, line 638
- `Morse.sphere_hopf_rinow` — Morse/Chapter7/HopfRinow.lean, line 651

*What differs.*
- In the embedded setting closedness in $V$ is the practical source of complete manifolds: compact manifolds, spheres and compact matrix groups. Later chapters assume closedness of $N$ where Milnor assumes completeness (V10.22).
- Chapter 7 does not identify the geodesics of $S^n$ with the great circles; that is done in Chapter 10 for the geodesics between two given points (V10.23).

### V7.30′. Familiar examples of geodesics: $\mathbb R^n$ and $S^n$

*narrower* · only $\mathbb R^n$ and $S^n$ · proved in Chapter 10 · uniqueness, not reflections

**Milnor (§10, pp. 65–66).** In Euclidean space $\mathbb R^n$ the equations for a geodesic become $d^2x_i/dt^2 = 0$, whose solutions are the straight lines. The geodesics on $S^n$ are precisely the great circles, the intersections of $S^n$ with the planes through its centre: reflection in such a plane is an isometry fixing the great circle, hence fixing the unique minimal geodesic between two nearby points of it, and there is a great circle through any point in any direction. Antipodal points are joined by a continuum of minimal geodesics; any other two points by a unique minimal geodesic and an infinite family of non-minimal ones. Meridians of a surface of revolution are geodesics, and on a right circular cylinder the geodesics are the generating lines, the circles and the helices, two points being joined by infinitely many.

**Proved in Lean.** (i) On the unit sphere $S^n \subseteq \mathbb R^{n+1}$, $n \ge 1$, with the induced metric: for unit vectors $p \perp u$ and $L \in \mathbb R$, the great circle $c(t) = \cos(Lt)\,p + \sin(Lt)\,u$ is a geodesic on $\mathbb R$; and for any $p, q$, every geodesic $\gamma \in \Omega(S^n; p, q)$ agrees on $[0, 1]$ with such a great circle, with $L \ge 0$. For $q \ne \pm p$ the geodesics from $p$ to $q$ are, up to their values off $[0, 1]$, the arcs $\gamma_0, \gamma_1, \dots$ of V10.23, with strictly increasing energies: infinitely many geodesics. (ii) If every tangent space of $N \subseteq V$ is $V$ (an open subset of $V$, with the flat metric) and the segment from $p$ to $q$ lies in $N$, then $t \mapsto p + t(q - p)$ is a geodesic of $\Omega(N; p, q)$ and every geodesic of $\Omega(N; p, q)$ agrees with it on $[0, 1]$: the geodesics of $V$ are the straight lines.

- `Morse.isGeodesicOn_greatCircle` — Morse/Chapter10/SphereGeodesics.lean, line 217
- `Morse.exists_eqOn_greatCircle` — Morse/Chapter10/SphereGeodesics.lean, line 266
- `Morse.exists_eqOn_sphGeod` — Morse/Chapter10/SphereGeodesics.lean, line 704
- `Morse.strictMono_energy_sphGeod` — Morse/Chapter10/SpherePaths.lean, line 63
- `Morse.unique_geodesic_of_top` — Morse/Chapter10/Incomplete.lean, line 373

*What differs.*
- The verified Chapter 7 lists the examples as not formalized; the sphere and flat open sets are treated in Chapter 10, for the index computation of Corollary 17.4 (V10.23) and the counterexample to Corollary 17.5 (V10.27).
- Not formalized: the continuum of minimal geodesics between antipodal points; the minimality of the short arc $\gamma_0$, which follows from V7.30 and the list of geodesics but is not stated; meridians of surfaces of revolution; the cylinder.
- The great circles are found from the uniqueness of geodesics with given initial data (V7.5, V9.9), not by Milnor's reflection argument.

## Chapter 8

*Milnor §§11–13, pp. 67–76: the path space, the energy, the second variation*

### V8.1. The path space and its “tangent spaces”

*restated* · $\Omega$ has no manifold structure, here too · paths are maps on $\mathbb R$ · break points need not match

**Milnor (§11, p. 67).** $\Omega(M; p, q)$ is the set of piecewise smooth paths $\omega : [0, 1] \to M$ from $p$ to $q$, each $\omega|[t_{i-1}, t_i]$ of class $C^\infty$ for some subdivision. Milnor thinks of $\Omega$ as "something like an infinite dimensional manifold", to be topologized only in §16, and defines its "tangent space" $T\Omega_\omega$ as the vector space of piecewise smooth vector fields $W$ along $\omega$ with $W(0) = 0$ and $W(1) = 0$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric ($P_x$ the projection onto $T_xN$, extended by $P_x = 0$ off $N$): for $p, q \in V$, $\Omega(N; p, q)$ is the set of maps $\omega : \mathbb R \to V$ that are piecewise smooth on $[0, 1]$ (V7.11), with $\omega(t) \in N$ for $t \in [0, 1]$, $\omega(0) = p$ and $\omega(1) = q$. For a map $\omega$, $T\Omega_\omega$ is the real vector space of maps $W$ that are piecewise smooth on $[0, 1]$ and tangent along $\omega$ ($P_{\omega(t)}W(t) = W(t)$ for $t \in [0, 1]$), with $W(0) = W(1) = 0$; it depends only on $\omega$ on $[0, 1]$.

- `Morse.pathSpace` — Morse/Chapter8/Energy.lean, line 313
- `Morse.prj` — Morse/Chapter8/Energy.lean, line 195
- `Morse.pathTangent` — Morse/Chapter8/Energy.lean, line 441
- `Morse.mem_pathTangent` — Morse/Chapter8/Energy.lean, line 457
- `Morse.mem_pathTangent_congr` — Morse/Chapter8/FirstVariation.lean, line 107

*What differs.*
- As in the book, $\Omega$ carries no topology or manifold structure here; $T\Omega_\omega$ is *defined* as a space of fields and is related to $\Omega$ only through variations (V8.2–V8.3).
- Paths and fields are maps on $\mathbb R$ considered on $[0, 1]$, and the subdivision is a finite set of break points; the break points of a field need not be those of $\omega$.
- Smoothness on a closed piece means one-sided derivatives at its ends, which the book leaves implicit.

### V8.2. Variations and variation fields

*stronger* · any open parameter set, any normed space · “clearly” $W \in T\Omega_\omega$ proved

**Milnor (§11, p. 68).** A variation of $\omega$ keeping the end points fixed is a map $\bar\alpha : (-\varepsilon, \varepsilon) \to \Omega$ with $\bar\alpha(0) = \omega$ and a subdivision $0 = t_0 < \dots < t_k = 1$ such that $\alpha(u, t) = \bar\alpha(u)(t)$ is $C^\infty$ on each strip $(-\varepsilon, \varepsilon) \times [t_{i-1}, t_i]$; an $n$-parameter variation replaces $(-\varepsilon, \varepsilon)$ by a neighbourhood of $0$ in $\mathbb R^n$. The variation vector field is $W_t = \frac{\partial\alpha}{\partial u}(0, t)$, and "clearly" $W \in T\Omega_\omega$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $P$ be a real normed space (Milnor's $\mathbb R$ or $\mathbb R^n$) and $U \ni 0$ open in $P$. A map $\alpha(u, t)$ is a variation with break points $B$ (a finite set) if $\alpha(u, t) \in N$ for $u \in U$, $t \in [0, 1]$; $\alpha(u, 0)$ and $\alpha(u, 1)$ do not depend on $u \in U$; and $\alpha$ is $C^\infty$ on every closed strip $U \times [s, t]$, $0 \le s < t \le 1$, with no point of $B$ in $(s, t)$. Every $\alpha(u, \cdot)$ then lies in $\Omega(N; \omega(0), \omega(1))$, $\omega = \alpha(0, \cdot)$, and composing with a smooth map into $P$ sending $0$ into $U$ gives a variation again. For $P = \mathbb R$, $W_t = \frac{\partial\alpha}{\partial u}(0, t)$ lies in $T\Omega_\omega$, and every $\frac{\partial\alpha}{\partial u}(u, t)$ is tangent to $N$ at $\alpha(u, t)$.

- `Morse.IsVariation` — Morse/Chapter8/Energy.lean, line 473
- `Morse.IsVariation.mem_pathSpace` — Morse/Chapter8/Energy.lean, line 499
- `Morse.IsVariation.comp` — Morse/Chapter8/Energy.lean, line 507
- `Morse.varField` — Morse/Chapter8/Energy.lean, line 523
- `Morse.IsVariation.varField_mem` — Morse/Chapter8/Energy.lean, line 549

*What differs.*
- The parameter set is any open set containing $0$ in any real normed space, which covers Milnor's $1$- and $n$-parameter variations at once.
- Behind "clearly": $W$ is continuous at a break point because both adjacent strips compute the velocity of the same curve $u \mapsto \alpha(u, t_i)$, tangent because that curve lies in $N$, and zero at the ends because they are fixed.

### V8.3. Lemma 11.A: every family of tangent fields comes from one variation

*stronger* · any number of parameters · no completeness: uniform $\varepsilon$

**Milnor (§11, pp. 68 and 74).** Given $W \in T\Omega_\omega$ there is a variation with $\bar\alpha(0) = \omega$ and $\frac{d\bar\alpha}{du}(0) = W$: "in fact one can set" $\bar\alpha(u)(t) = \exp_{\omega(t)}(uW_t)$ (p. 68). On p. 74, 2-parameter variations with prescribed variation fields $W_1$, $W_2$ are chosen without comment.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $\omega \in \Omega(N; p, q)$, $P$ a real normed space, and $\Lambda$ a family, piecewise smooth on $[0, 1]$, of continuous linear maps $\Lambda(t) : P \to V$ with values in $T_{\omega(t)}N$ and $\Lambda(0) = \Lambda(1) = 0$. There are $\varepsilon > 0$ and a finite set $B$ such that $\alpha(u, t) = \exp_{\omega(t)}(\Lambda(t)u)$ is a variation with break points $B$ on the ball $\|u\| < \varepsilon$, with $\alpha(0, t) = \omega(t)$ and derivative $\Lambda(t)$ in $u$ at $u = 0$, for $t \in [0, 1]$. In particular every $W \in T\Omega_\omega$ is the variation field of $\exp_{\omega(t)}(uW_t)$, $|u| < \varepsilon$, and any $W_1, W_2 \in T\Omega_\omega$ are the variation fields of the 2-parameter variation $\exp_{\omega(t)}(u_1W_1(t) + u_2W_2(t))$.

- `Morse.exists_variation` — Morse/Chapter8/FirstVariation.lean, line 429
- `Morse.exists_variation_one` — Morse/Chapter8/FirstVariation.lean, line 515
- `Morse.exists_variation_two` — Morse/Chapter8/FirstVariation.lean, line 537

*What differs.*
- Any number of parameters (the exposition's Lemma 11.A); Milnor states the one-parameter case and uses the two-parameter case.
- $\exp$ is defined only near the zero section (V7.8), so $\varepsilon$ must be chosen uniformly along $\omega$, by the compactness of $\omega([0, 1])$ and a bound for $\|\Lambda\|$; completeness of $N$ is not needed.
- The derivative in $u$ at $0$ is $\Lambda(t)$ because $d(\exp_q)_0$ is the inclusion of $T_qN$ (V7.8).

### V8.4. Critical paths of the energy

*narrower* · only for $F = E$ · the derivative must exist

**Milnor (§11, p. 69).** A path $\omega$ is a critical path of a function $F : \Omega \to \mathbb R$ if and only if $\frac{dF(\bar\alpha(u))}{du}\big|_{u=0}$ is zero for every variation $\bar\alpha$ of $\omega$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: a map $\omega$ is a critical path of the energy $E$ (V8.5) if for every 1-parameter variation $\alpha$ with $\alpha(0, t) = \omega(t)$ for $t \in [0, 1]$, the function $u \mapsto E(\alpha(u, \cdot))$ is differentiable at $0$ with derivative $0$.

- `Morse.IsCriticalPath` — Morse/Chapter8/Critical.lean, line 72

*What differs.*
- Critical paths are defined for the energy only, the case of Corollary 12.3; Milnor's definition is for any function on $\Omega$.
- The definition asks that the derivative exist; for $E$ it always does (V8.9).

### V8.5. Energy and length

*stronger* · any $a \le b$, any normed target · “constant” off the break points

**Milnor (§12, p. 70).** For $\omega \in \Omega$ and $0 \le a < b \le 1$, the energy from $a$ to $b$ is $E_a^b(\omega) = \int_a^b\|d\omega/dt\|^2\,dt$, $E = E_0^1$, and $L_a^b$ is the arc length. By Schwarz's inequality $(L_a^b)^2 \le (b - a)E_a^b$, with equality if and only if $\|d\omega/dt\|$ is constant, that is, if and only if the parameter $t$ is proportional to arc length.

**Proved in Lean.** For a map $c$ into a real normed space and $a \le b$, $E_a^b(c) = \int_a^b\|c'(t)\|^2\,dt$, $E = E_0^1$, and $L_a^b(c)$ is the length of V7.11. If $c$ is piecewise smooth on $[a, b]$, then $(L_a^b(c))^2 \le (b - a)E_a^b(c)$, with equality iff $\|c'\|$ takes one and the same value at every point of $(a, b)$ where $c$ is differentiable. An admissible path of constant speed $k$ there has $E_a^b = k^2(b - a)$.

- `Morse.energy` — Morse/Chapter8/Energy.lean, line 318
- `Morse.pathLength_sq_le_energy` — Morse/Chapter8/Energy.lean, line 351
- `Morse.pathLength_sq_eq_energy_iff` — Morse/Chapter8/Energy.lean, line 382
- `Morse.energy_eq_of_norm_deriv` — Morse/Chapter8/Energy.lean, line 367

*What differs.*
- Any $a \le b$ and any normed target, where Milnor has $0 \le a < b \le 1$ and paths in $M$.
- For a speed that is only piecewise continuous, "constant" can only mean constant off the break points; the formal equality condition says so. The proof is the variance identity $(b - a)\int_a^b(g - \bar g)^2 = (b - a)E_a^b - (L_a^b)^2$, $g = \|c'\|$ (the exposition's Lemma 12.A).

### V8.6. Lemma 12.1: the energy at a minimal geodesic

*narrower* · only the inequality · no completeness needed for it · minimal among paths on $[0, 1]$

**Milnor (§12, Lemma 12.1, p. 70).** Let $M$ be complete and $p, q \in M$ at distance $d$. Then the energy function $E : \Omega(M; p, q) \to \mathbb R$ takes on its minimum $d^2$ precisely on the set of minimal geodesics from $p$ to $q$. The proof is the chain $E(\gamma) = L(\gamma)^2 \le L(\omega)^2 \le E(\omega)$ for a minimal geodesic $\gamma$, with the equality cases.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: a path $\gamma \in \Omega(N; p, q)$ is *minimal* if $L(\gamma) \le L(\omega)$ for every $\omega \in \Omega(N; p, q)$. If $\gamma$ is minimal and a geodesic of $\Omega$ (V8.10), then $E(\gamma) \le E(\omega)$ for every $\omega \in \Omega(N; p, q)$.

- `Morse.IsMinimalPath` — Morse/Chapter8/Hessian.lean, line 523
- `Morse.energy_le_of_isMinimalPath` — Morse/Chapter8/Hessian.lean, line 538

*What differs.*
- Only the inequality is formalized. Neither the value $d^2$ of the minimum nor the converse (a path of energy $d^2$ is a minimal geodesic, which needs the equality cases of V8.5 and of Corollary 10.7) is stated.
- Completeness serves only to make a minimal geodesic exist (V7.26); the inequality holds on any $N$.
- Minimality is among the paths of $\Omega$, parametrized on $[0, 1]$; by affine reparametrization this is Milnor's notion (V7.24), an equivalence not stated formally.

### V8.7. Velocity jumps, acceleration and the first variation

*restated* · the sum over all of $(0, 1)$

**Milnor (§12, p. 71).** For $\omega \in \Omega$, Milnor writes $V_t = d\omega/dt$ for the velocity, $A_t = \frac{D}{dt}\frac{d\omega}{dt}$ for the acceleration, and $\Delta_tV = V_{t^+} - V_{t^-}$ for the discontinuity of the velocity at $t$, which is zero for all but finitely many $t$ in $(0, 1)$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: for a map $f$ into $V$, the jump $\Delta_tf' = f'(t^+) - f'(t^-)$ is the difference of the right and the left derivative of $f$ at $t$; it vanishes where $f$ is differentiable. Along a path $\omega$, $\frac{DX}{dt}(t) = P_{\omega(t)}X'(t)$, $V = \omega'$ and $A = \frac{D}{dt}V$. The first variation of $\omega$ in the direction $W$ is $-\sum_{0 < t < 1}\langle W_t, \Delta_tV\rangle - \int_0^1\langle W_t, A_t\rangle\,dt$, the sum being finite: for $\omega$ differentiable off a finite set $B$, it is the sum over the points of $B$ in $(0, 1)$. It depends only on $W$ on $[0, 1]$.

- `Morse.jump` — Morse/Chapter8/Energy.lean, line 152
- `Morse.covD` — Morse/Chapter8/FirstVariation.lean, line 75
- `Morse.accel` — Morse/Chapter8/FirstVariation.lean, line 79
- `Morse.firstVariation` — Morse/Chapter8/FirstVariation.lean, line 90
- `Morse.finsum_jump_eq_sum` — Morse/Chapter8/FirstVariation.lean, line 204

*What differs.*
- The sum is written over all of $(0, 1)$, its terms vanishing off the break points; the formal statement shows it is the finite sum over the break points.

### V8.8. Calculus on closed strips

*not in the book* · mixed partials up to the edges · differentiation under $\int$ · jump terms from the pieces

**Milnor (§§12–13, pp. 71–76).** The book has no such statement. In the proofs of Theorems 12.2 and 13.1 Milnor differentiates under the integral sign, integrates by parts on each $[t_{i-1}, t_i]$ and adds up, and interchanges partial derivatives of a variation, which is smooth only on closed strips, all without comment.

**Proved in Lean.** For $F$ smooth on a closed strip $U \times [a, b]$, $U \subseteq \mathbb R$ open, $a < b$: the partial derivatives $\partial F/\partial u$, $\partial F/\partial t$ computed within the strip are smooth on it, are one-sided $t$-derivatives on the edges, and the mixed partials agree on the whole closed strip, edges included. If $F$ and $F'$ are continuous on the strip and $F'$ is the $u$-derivative of $F$ inside it, then $u \mapsto \int_a^bF(u, t)\,dt$ has derivative $\int_a^bF'(u_0, t)\,dt$ at every $u_0 \in U$, also for integrands that are $C^1$ only piece by piece. If $\int_s^tg = F^-(t) - F^+(s)$ on every piece $[s, t]$ of $[a, b]$ with break points $B$, then $\int_a^bg = F^-(b) - F^+(a) - \sum_{x \in B \cap (a, b)}(F^+(x) - F^-(x))$.

- `Morse.pdU` — Morse/Chapter8/Piecewise.lean, line 235
- `Morse.pdT` — Morse/Chapter8/Piecewise.lean, line 239
- `Morse.pdU_pdT` — Morse/Chapter8/Piecewise.lean, line 317
- `Morse.hasDerivAt_integral_strip` — Morse/Chapter8/Piecewise.lean, line 348
- `Morse.integral_eq_of_piecewise` — Morse/Chapter8/Piecewise.lean, line 209
- `Morse.hasDerivAt_integral_of_piecewise` — Morse/Chapter8/Piecewise.lean, line 382

*What differs.*
- These are the analytic facts behind "differentiate under the integral sign" and "integrate by parts on each interval": smoothness on the closed strips, compactness for the domination bound, and the symmetry of second derivatives on the edges, where the $t$-derivatives are one-sided.
- The last statement is the bookkeeping by which the boundary terms of the pieces telescope into the jump terms of the first and second variation formulas.

### V8.9. Theorem 12.2: the first variation formula

*stronger* · at every $u$, not only $u = 0$ · Lemma 8.7, not 8.5 · differentiability proved

**Milnor (§12, Theorem 12.2, p. 71).** Let $\bar\alpha$ be a variation of $\omega$ with variation field $W$. Then $\frac12\frac{dE(\bar\alpha(u))}{du}\big|_{u=0} = -\sum_t\langle W_t, \Delta_tV\rangle - \int_0^1\langle W_t, A_t\rangle\,dt$. The proof differentiates under the integral sign, uses Lemma 8.3 and "Lemma 8.5" to replace $\frac{D}{\partial u}\frac{\partial\alpha}{\partial t}$ by $\frac{D}{\partial t}\frac{\partial\alpha}{\partial u}$, integrates by parts on each $[t_{i-1}, t_i]$ and adds up.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $\alpha$ be a 1-parameter variation (V8.2) with parameter set $U \subseteq \mathbb R$. For every $u_0 \in U$, $u \mapsto E(\alpha(u, \cdot))$ is differentiable at $u_0$, and $\frac12\frac{d}{du}E(\alpha(u, \cdot))|_{u_0}$ is the first variation (V8.7) of $\alpha(u_0, \cdot)$ in the direction $\frac{\partial\alpha}{\partial u}(u_0, \cdot)$: $$-\sum_t\Big\langle\frac{\partial\alpha}{\partial u}, \Delta_t\frac{\partial\alpha}{\partial t}\Big\rangle - \int_0^1\Big\langle\frac{\partial\alpha}{\partial u}, \frac{D}{\partial t}\frac{\partial\alpha}{\partial t}\Big\rangle\,dt$$ at $(u_0, t)$. At $u_0 = 0$, with $\alpha(0, t) = \omega(t)$ on $[0, 1]$, this is Milnor's formula.

- `Morse.IsVariation.hasDerivAt_energy` — Morse/Chapter8/FirstVariation.lean, line 225
- `Morse.first_variation` — Morse/Chapter8/FirstVariation.lean, line 377

*What differs.*
- The formula holds at every value of the parameter (the exposition's formula (12.2′)), which is what §13 differentiates; the existence of the derivative is part of the conclusion.
- Milnor's reference to Lemma 8.5 should be to Lemma 8.7 (8.5 is the definition of a symmetric connection). The scan loses the leading minus sign of the displayed statement; the end of the proof on p. 72 has it.
- Hidden: differentiation under the integral sign and the symmetry of mixed partials on the closed strips (V8.8); the boundary terms telescope into the jump terms because $\partial\alpha/\partial u$ is continuous in $t$.

### V8.10. Geodesics of $\Omega$, and criticality through the first variation

*restated* · acceleration zero on $(0, 1)$ · criticality needs Lemma 11.A

**Milnor (§12, p. 73).** The path $\omega \in \Omega$ is a geodesic if and only if $\omega$ is $C^\infty$ on the whole interval $[0, 1]$ and its acceleration $\frac{D}{dt}\frac{d\omega}{dt}$ is identically zero along $\omega$. "Clearly" a geodesic is a critical point of $E$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: a map $\omega$ is an (unbroken) geodesic if it is $C^\infty$ on $[0, 1]$, with one-sided derivatives at the ends, and a geodesic on $(0, 1)$ in the sense of V7.1, so that $A = 0$ there. For $\omega \in \Omega(N; p, q)$: $\omega$ is a critical path (V8.4) iff its first variation (V8.7) vanishes in every direction $W \in T\Omega_\omega$. For a geodesic, the first variation vanishes in every direction.

- `Morse.IsUnbrokenGeodesic` — Morse/Chapter8/Critical.lean, line 78
- `Morse.isCriticalPath_iff` — Morse/Chapter8/Critical.lean, line 83
- `Morse.IsUnbrokenGeodesic.firstVariation_eq_zero` — Morse/Chapter8/Critical.lean, line 102

*What differs.*
- The acceleration is required to vanish on $(0, 1)$; at the ends it then vanishes by continuity.
- The converse direction of "critical iff the first variation vanishes on $T\Omega_\omega$" needs every field to be a variation field, Lemma 11.A (V8.3).

### V8.11. Corollary 12.3: the critical paths of $E$ are the geodesics

*hypotheses explicit* · test variations from Lemma 11.A · $W = fA$ continuous at the $t_i$ · a derivative-extension step

**Milnor (§12, Corollary 12.3, p. 73).** The path $\omega$ is a critical point for the function $E$ if and only if $\omega$ is a geodesic. Proof: a variation with $W(t) = f(t)A(t)$, $f$ positive except at the $t_i$, gives $A = 0$ on each piece; one with $W(t_i) = \Delta_{t_i}V$ gives $\Delta_{t_i}V = 0$, so $\omega$ is $C^1$; then $\omega$ is $C^\infty$ "from the uniqueness theorem for differential equations".

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: a path $\omega \in \Omega(N; p, q)$ is a critical path of $E$ iff it is a geodesic (V8.10). The steps, for $\omega$ critical and smooth on the pieces of a finite set $B$: the acceleration vanishes at every $t \in (0, 1) \setminus B$; the one-sided velocities and their jumps are tangent to $N$, and every jump $\Delta_tV$, $0 < t < 1$, vanishes; through every $q \in N$ with any $v \in T_qN$ at any time $x$ there is a geodesic on an interval around $x$; and a path that is a geodesic on both sides of $x$, smooth up to $x$ from each side and differentiable at $x$, is a geodesic near $x$.

- `Morse.accel_eq_zero_of_critical` — Morse/Chapter8/Critical.lean, line 153
- `Morse.jump_eq_zero_of_critical` — Morse/Chapter8/Critical.lean, line 253
- `Morse.exists_isGeodesicOn_through` — Morse/Chapter8/Critical.lean, line 365
- `Morse.isGeodesicOn_of_glue` — Morse/Chapter8/Critical.lean, line 410
- `Morse.corollary_12_3` — Morse/Chapter8/Critical.lean, line 517

*What differs.*
- The test variations exist only by Lemma 11.A (V8.3); $W = fA$ must be continuous at the $t_i$, where the one-sided accelerations differ; and a field with the prescribed values $\Delta_{t_i}V$ has to be constructed. The formal proof uses bump functions at one point at a time.
- The last step needs the lift $(\omega, \omega')$ to solve the geodesic equation at the former break point itself (a derivative-extension argument) before uniqueness for the first-order geodesic system (V7.3, V7.4) applies.

### V8.12. The curvature identity (13.3), and jumps under differentiation

*restated* · (13.3) for a surface · on strips, up to the edges

**Milnor (§13, pp. 75–76).** In the proof of Theorem 13.1, the curvature formula $\frac{D}{\partial u_1}\frac{D}{\partial t}V - \frac{D}{\partial t}\frac{D}{\partial u_1}V = R(V, W_1)V$ (Lemma 9.2) and $\frac{D}{\partial u_1}V = \frac{D}{\partial t}W_1$ (Lemma 8.7) give (13.3): $\frac{D}{\partial u_1}\frac{D}{\partial t}V = \frac{D^2W_1}{dt^2} + R(V, W_1)V$. On p. 75 the second term of the differentiated first variation formula is "rearranged", which differentiates the velocity jumps in $u$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric, $R$ Milnor's curvature tensor with his sign ($0$ off $N$): (i) for $F(u, t)$ smooth on an open subset $O$ of $\mathbb R^2$ with values in $N$, at every point of $O$, $$\frac{D}{\partial u}\frac{D}{\partial t}\frac{\partial F}{\partial t} = \frac{D}{\partial t}\frac{D}{\partial t}\frac{\partial F}{\partial u} + R\Big(\frac{\partial F}{\partial t}, \frac{\partial F}{\partial u}\Big)\frac{\partial F}{\partial t},$$ with $\frac{D}{\partial u}X = P(\partial X/\partial u)$, $\frac{D}{\partial t}X = P(\partial X/\partial t)$. (ii) For a 1-parameter variation $\alpha$, $u_0 \in U$ and $0 < x < 1$, the jump $\Delta_x\frac{\partial\alpha}{\partial t}(u, \cdot)$ is differentiable in $u$ at $u_0$, with derivative $\Delta_x\frac{\partial}{\partial t}\frac{\partial\alpha}{\partial u}(u_0, \cdot)$.

- `Morse.curvR` — Morse/Chapter8/SecondVariation.lean, line 80
- `Morse.curvR_of_mem` — Morse/Chapter8/SecondVariation.lean, line 83
- `Morse.curvature_identity` — Morse/Chapter8/SecondVariation.lean, line 143
- `Morse.IsVariation.hasDerivAt_jump` — Morse/Chapter8/SecondVariation.lean, line 256

*What differs.*
- (i) is (13.3) for a surface, with $x = t$, $y = u$ in Lemma 9.2.
- Lemmas 8.7 and 9.2 are applied by Milnor to a surface defined only on strips; Chapter 6 states them for surfaces on all of $\mathbb R^2$, so the identity is proved near interior points, and differentiating a one-sided $t$-derivative in $u$ needs the symmetry of mixed partials on the edges (V8.8).

### V8.13. Theorem 13.1: the second variation formula

*restated* · the iterated partial derivative · its existence is proved · $E \circ \bar\alpha$ not assumed $C^2$

**Milnor (§13, Theorem 13.1, p. 75).** Let $\bar\alpha : U \to \Omega$ be a 2-parameter variation of the geodesic $\gamma$ with variation fields $W_i = \frac{\partial\bar\alpha}{\partial u_i}(0, 0)$, $i = 1, 2$. Then $$\frac12\frac{\partial^2E(\bar\alpha(u_1, u_2))}{\partial u_1\partial u_2}(0, 0) = -\sum_t\Big\langle W_2(t), \Delta_t\frac{DW_1}{dt}\Big\rangle - \int_0^1\Big\langle W_2, \frac{D^2W_1}{dt^2} + R(V, W_1)V\Big\rangle\,dt.$$ It is introduced on p. 74 to show that $E_{**}$ is well defined, and proved on pp. 75–76 from 12.2, the vanishing of $\Delta_tV$ and $\frac{D}{dt}V$ along a geodesic, (13.2) and (13.3).

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: for a path $\gamma$ with velocity $V$ and fields $W_1, W_2$ along it, let $\Phi(W_1, W_2)$ be the right side above, where $\Delta_t\frac{DW_1}{dt} = P_{\gamma(t)}(\Delta_tW_1')$ is the jump of $\frac{DW_1}{dt} = PW_1'$. Let $\gamma$ be a geodesic (V8.10) and $\alpha(u_1, u_2, t)$ a 2-parameter variation of $\gamma$ ($\alpha(0, 0, t) = \gamma(t)$ on $[0, 1]$) with variation fields $W_1, W_2$. Then $u_1 \mapsto \frac{\partial}{\partial u_2}E(\alpha(u_1, u_2, \cdot))|_{u_2 = 0}$ is differentiable at $u_1 = 0$, with derivative $2\Phi(W_1, W_2)$. Two 2-parameter variations of $\gamma$ whose variation fields agree on $[0, 1]$ give the same value.

- `Morse.secondVariation` — Morse/Chapter8/SecondVariation.lean, line 247
- `Morse.second_variation` — Morse/Chapter8/SecondVariation.lean, line 337
- `Morse.second_variation_eq` — Morse/Chapter8/SecondVariation.lean, line 520

*What differs.*
- Milnor's $\frac{\partial^2E}{\partial u_1\partial u_2}(0, 0)$ is the iterated derivative $\partial/\partial u_1$ of $\partial E/\partial u_2$ along $u_2 = 0$, which is what his proof computes; its existence is part of the conclusion, and $E \circ \bar\alpha$ is not assumed to be of class $C^2$.
- The proof needs formula (12.2′) at every $(u_1, 0)$ (V8.9), and differentiation of the jump and integral terms in $u_1$ (V8.8, V8.12).
- The scan drops the $-\sum_t$ in front of the first term of the displayed statement; (13.2) on the same page has it.

### V8.14. The Hessian $E_{**}$

*restated* · defined by Milnor's formula · identified with his definition · defined at every path of $\Omega$

**Milnor (§13, p. 74).** For a geodesic $\gamma$, the Hessian $E_{**} : T\Omega_\gamma \times T\Omega_\gamma \to \mathbb R$ of $E$ at $\gamma$ is defined by analogy with the Hessian $f_{**}$ of a function on a manifold: given $W_1, W_2 \in T\Omega_\gamma$, choose a 2-parameter variation with these variation fields and put $E_{**}(W_1, W_2) = \frac{\partial^2E(\bar\alpha(u_1, u_2))}{\partial u_1\partial u_2}(0, 0)$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: for $\gamma \in \Omega(N; p, q)$, $E_{**}(W_1, W_2) = 2\Phi(W_1, W_2)$ ($\Phi$ as in V8.13) is a bilinear form on $T\Omega_\gamma$, depending only on the values of the fields on $[0, 1]$. The variation fields of a 2-parameter variation of $\gamma$ lie in $T\Omega_\gamma$. If $\gamma$ is a geodesic, every 2-parameter variation of $\gamma$ with variation fields $W_1, W_2$ has $\frac{\partial^2E}{\partial u_1\partial u_2}(0, 0) = E_{**}(W_1, W_2)$ (in the sense of V8.13), and every pair $W_1, W_2 \in T\Omega_\gamma$ arises (V8.3). So Milnor's definition is well defined and agrees with $E_{**}$.

- `Morse.energyHessian` — Morse/Chapter8/Hessian.lean, line 405
- `Morse.energyHessian_apply` — Morse/Chapter8/Hessian.lean, line 432
- `Morse.IsVariation.partial₁_mem` — Morse/Chapter8/Hessian.lean, line 460
- `Morse.hasDerivAt_energyHessian` — Morse/Chapter8/Hessian.lean, line 477

*What differs.*
- $\Omega$ has no manifold structure, here as in the book, so $E_{**}$ is defined by the second variation formula and identified with Milnor's definition through variations: every pair of fields comes from a variation (Lemma 11.A), and every such variation computes it (Theorem 13.1).
- $E_{**}$ is defined at every $\gamma \in \Omega$; only at a geodesic is it the second derivative of $E$.

### V8.15. Proposition 13.A: the Hessian as an integral

*not in the book* · one integration by parts per piece · used for symmetry and the index

**Milnor (§13, cf. pp. 75–76).** The book has no such statement; it works throughout with the form of the second variation formula containing $\frac{D^2W_1}{dt^2}$ and the jumps of $\frac{DW_1}{dt}$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: for $\gamma \in \Omega(N; p, q)$ and $W_1, W_2 \in T\Omega_\gamma$, $$\tfrac12E_{**}(W_1, W_2) = \int_0^1\Big(\Big\langle\frac{DW_1}{dt}, \frac{DW_2}{dt}\Big\rangle - \langle R(V, W_1)V, W_2\rangle\Big)\,dt.$$ $\gamma$ need not be a geodesic.

- `Morse.hessForm` — Morse/Chapter8/Hessian.lean, line 110
- `Morse.secondVariation_eq_hessForm` — Morse/Chapter8/Hessian.lean, line 259
- `Morse.energyHessian_eq_integral` — Morse/Chapter8/Hessian.lean, line 447

*What differs.*
- The exposition's Proposition 13.A: one integration by parts on each piece (Lemma 8.3), the boundary terms telescoping into the jump terms, $W_2$ vanishing at the ends.
- It carries much of what follows: the symmetry of $E_{**}$ (V8.16), the extension by zero in the index theorem (V9.20), the Poincaré estimate (V9.16) and the test fields of Myers' theorem (V11.11).

### V8.16. Corollary 13.4: $E_{**}$ is symmetric and bilinear

*restated* · symmetry from the integral form · no $C^2$ assumption on $E \circ \bar\alpha$

**Milnor (§13, Corollary 13.4, p. 76).** The expression $E_{**}(W_1, W_2) = \frac{\partial^2E}{\partial u_1\partial u_2}(0, 0)$ is a well defined, symmetric, bilinear function of $W_1$ and $W_2$: well defined and bilinear by the second variation formula, symmetric because $\frac{\partial^2E}{\partial u_1\partial u_2} = \frac{\partial^2E}{\partial u_2\partial u_1}$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: for $\gamma \in \Omega(N; p, q)$, $E_{**}$ is a symmetric bilinear form on $T\Omega_\gamma$. For tangent vectors $v, w_1, w_2$ at $x \in N$, $\langle R(v, w_1)v, w_2\rangle = \langle R(v, w_2)v, w_1\rangle$.

- `Morse.inner_curvR_comm` — Morse/Chapter8/Hessian.lean, line 321
- `Morse.hessForm_comm` — Morse/Chapter8/Hessian.lean, line 342
- `Morse.energyHessian_isSymm` — Morse/Chapter8/Hessian.lean, line 438

*What differs.*
- Milnor's symmetry argument needs $E \circ \bar\alpha$ of class $C^2$ near $(0, 0)$, which the book does not address. Here symmetry and bilinearity come from the integral form (V8.15) and the symmetry of the curvature term (Lemma 9.3 (4), from the Gauss equation), not from second derivatives; well-definedness is V8.13–V8.14.
- Bilinearity in $W_1$ also needs the linearity of $W \mapsto \Delta_t\frac{DW}{dt}$ and $W \mapsto \frac{D^2W}{dt^2}$ on piecewise smooth fields, which the integral form makes unnecessary.

### V8.17. Remark 13.5: the second derivative along a 1-parameter variation

*hypotheses explicit* · $\beta$ is a 2-parameter variation · second derivative shown to exist

**Milnor (§13, Remark 13.5, p. 76).** If $\bar\alpha$ is a 1-parameter variation of the geodesic $\gamma$ with variation field $W$, then $\frac{d^2E(\bar\alpha(u))}{du^2}(0) = E_{**}(W, W)$, by the 2-parameter variation $\beta(u_1, u_2) = \bar\alpha(u_1 + u_2)$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $\gamma \in \Omega(N; p, q)$ be a geodesic and $\alpha$ a 1-parameter variation of $\gamma$ with variation field $W$. Then $u \mapsto \frac{d}{du}E(\alpha(u, \cdot))$ is differentiable at $0$, and $\frac{d^2E(\bar\alpha(u))}{du^2}(0) = E_{**}(W, W)$.

- `Morse.remark_13_5` — Morse/Chapter8/SecondVariation.lean, line 560
- `Morse.hasDerivAt_deriv_energy` — Morse/Chapter8/Hessian.lean, line 510

*What differs.*
- That $\beta$ is a 2-parameter variation with both variation fields equal to $W$ is checked; the proof is Milnor's, Theorem 13.1 for $\beta$, and the second derivative is shown to exist.

### V8.18. Lemma 13.6: the Hessian at a minimal geodesic

*narrower* · index $0$ not stated · minimality alone, no completeness

**Milnor (§13, Lemma 13.6, p. 76).** If $\gamma$ is a minimal geodesic from $p$ to $q$, then the bilinear pairing $E_{**}$ is positive semi-definite. Hence the index $\lambda$ of $E_{**}$ is zero. Proof: $E(\bar\alpha(u)) \ge E(\gamma) = E(\bar\alpha(0))$ forces $\frac{d^2E(\bar\alpha(u))}{du^2}(0) \ge 0$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: if $\gamma \in \Omega(N; p, q)$ is a geodesic and is minimal in the sense of V8.6, then $E_{**}(W, W) \ge 0$ for every $W \in T\Omega_\gamma$.

- `Morse.lemma_13_6` — Morse/Chapter8/Hessian.lean, line 557

*What differs.*
- The formal statement is the positive semi-definiteness. The index of a bilinear form is defined only in Chapter 9 (V9.13), and that the index of $E_{**}$ at a minimal geodesic is $0$ is not stated as a theorem.
- Only minimality is used, not completeness. That a minimum forces a nonnegative second derivative needs an argument when only the second derivative at $0$ is known to exist: if it were negative, $0$ would also be a local maximum, so the function would be locally constant and its second derivative $0$.

## Chapter 9

*Milnor §§14–15, pp. 77–87: Jacobi fields and the index theorem*

### V9.1. Linear equations have global solutions (Lemma 14.A)

*stronger* · proved, not asserted · any continuous coefficients · any complete normed space

**Milnor (§14, p. 77).** The Jacobi equation, a linear second-order differential equation, has $2n$ linearly independent solutions, each of which is "defined throughout $\gamma$" and of class $C^\infty$; a Jacobi field is determined by its initial conditions $J(0)$ and $\frac{DJ}{dt}(0)$. Milnor gives no proof.

**Proved in Lean.** Let $E$ be a complete real normed space and $t \mapsto A(t)$ a continuous map from $\mathbb R$ to the continuous linear maps $E \to E$. (i) For every $t_0 \in \mathbb R$ and $x_0 \in E$ the equation $x' = A(t)x$ has a solution on all of $\mathbb R$ with $x(t_0) = x_0$, and the solution with value $\xi$ at $s$ depends linearly on $\xi$. (ii) If $a < b$ and $f$ is continuous on $[a, b]$ and solves the equation on $(a, b)$, then for every $s \in [a, b]$, end points included, $f$ agrees on $[a, b]$ with the solution whose value at $s$ is $f(s)$. (iii) If $A$ is $C^\infty$ on $[a, b]$ (one-sided derivatives at the ends) and $f'(t) = A(t)f(t)$ at every $t \in [a, b]$, then $f$ is $C^\infty$ on $[a, b]$.

- `Morse.exists_linearODE` — Morse/Chapter9/JacobiODE.lean, line 137
- `Morse.linSol` — Morse/Chapter9/JacobiODE.lean, line 172
- `Morse.eqOn_Icc_linSol` — Morse/Chapter9/JacobiODE.lean, line 219
- `Morse.contDiffOn_Icc_of_hasDerivAt` — Morse/Chapter9/JacobiSystem.lean, line 335

*What differs.*
- The book asserts global solutions without proof; the local existence theorem gives solutions only on intervals of length about $1/\sup\|A\|$, so a global theorem for linear equations is needed. It is proved by truncating the equation radially and bounding the solution by Grönwall's inequality in both time directions, so that the truncation is never active.
- The coefficients may be any continuous family on any complete space, extending the skew-adjoint case of Chapter 6.

### V9.2. Jacobi fields and the Jacobi system

*restated* · no parallel frame: a system in $V \times V$ · along any smooth curve · initial values at any $s$

**Milnor (§14, p. 77).** A vector field $J$ along a geodesic $\gamma$ is a *Jacobi field* if it satisfies the Jacobi differential equation $\frac{D^2J}{dt^2} + R(V, J)V = 0$, $V = d\gamma/dt$. In terms of orthonormal parallel fields $P_1, \dots, P_n$ along $\gamma$, writing $J = \sum f^iP_i$, it becomes a linear system with coefficients $\langle R(V, P_j)V, P_i\rangle$; a Jacobi field is completely determined by its initial conditions $J(0)$ and $\frac{DJ}{dt}(0)$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric. A *smooth curve in $N$ on $[0, 1]$* is a map $\gamma : \mathbb R \to V$ that is $C^\infty$ on $[0, 1]$, with one-sided derivatives at the ends, and has values in $N$ there; every geodesic of $\Omega$ is one. A map $J$ is a *Jacobi field along $\gamma$* if it is $C^\infty$ on $[0, 1]$, tangent along $\gamma$, and $\frac{D^2J}{dt^2} + R(V, J)V = 0$ on $(0, 1)$, $D/dt$ the covariant derivative of V8.7. With $S = P'P - PP'$ and $K(t)v = R(V, P(t)v)V$, the Jacobi system is the linear system $J' = SJ + Y$, $Y' = SY - KJ$ for $(J, Y)$ in $V \times V$; its solution with any value at any time exists on $\mathbb R$. If $s \in [0, 1]$ and both initial values are tangent at $\gamma(s)$, both components stay tangent on $[0, 1]$, the first is a Jacobi field and the second its covariant derivative. Conversely every Jacobi field $J$ agrees on $[0, 1]$ with the solution whose value at $s$ is $(J(s), \frac{DJ}{dt}(s))$; in particular $J(s) = 0$ and $\frac{DJ}{dt}(s) = 0$ force $J = 0$ on $[0, 1]$.

- `Morse.jacobiExpr` — Morse/Chapter8/Jacobi.lean, line 165
- `Morse.IsJacobiField` — Morse/Chapter8/Jacobi.lean, line 171
- `Morse.jacSys` — Morse/Chapter9/JacobiSystem.lean, line 142
- `Morse.jacSol` — Morse/Chapter9/JacobiSystem.lean, line 359
- `Morse.isJacobiField_jacSol` — Morse/Chapter9/JacobiSystem.lean, line 456
- `Morse.IsJacobiField.eqOn_jacSol` — Morse/Chapter9/JacobiSystem.lean, line 494
- `Morse.IsJacobiField.eqOn_zero` — Morse/Chapter9/JacobiSystem.lean, line 561

*What differs.*
- No frame is used: the unknown is $(J, \frac{DJ}{dt})$ in $V \times V$, and the term $S$ keeps solutions with tangent initial values tangent, their normal parts solving a homogeneous linear system and vanishing at $s$.
- Parallel frames along $\gamma$ (Lemma 8.2) are formalized only for curves on all of $\mathbb R$; the frame-free system avoids extending $\gamma$.
- The definition and the solution theory hold along any smooth curve in $N$, not only along a geodesic, with initial values at any $s \in [0, 1]$; the global existence is V9.1.

### V9.3. The space of Jacobi fields (Corollary 14.B)

*stronger* · isomorphism at every $s \in [0, 1]$ · along any smooth curve

**Milnor (§14, p. 77).** The Jacobi equation has $2n$ linearly independent solutions, and a Jacobi field is completely determined by $J(0)$ and $\frac{DJ}{dt}(0)$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $\gamma$ be a smooth curve in $N$ on $[0, 1]$ (V9.2) and $n = \dim N$. $\mathcal J(\gamma)$ is the vector space of the Jacobi fields along $\gamma$ that are constant off $[0, 1]$; every Jacobi field agrees on $[0, 1]$ with one of them. For every $s \in [0, 1]$, $J \mapsto (J(s), \frac{DJ}{dt}(s))$ is a linear isomorphism $\mathcal J(\gamma) \to T_{\gamma(s)}N \times T_{\gamma(s)}N$: every pair of tangent vectors at $\gamma(s)$ is the value and covariant derivative at $s$ of exactly one field of $\mathcal J(\gamma)$; and $\dim\mathcal J(\gamma) = 2n$.

- `Morse.jacobiSpace` — Morse/Chapter9/JacobiSpace.lean, line 112
- `Morse.jacEval` — Morse/Chapter9/JacobiSpace.lean, line 162
- `Morse.jacEval_bijective` — Morse/Chapter9/JacobiSpace.lean, line 178
- `Morse.jacEquiv` — Morse/Chapter9/JacobiSpace.lean, line 207
- `Morse.finrank_jacobiSpace` — Morse/Chapter9/JacobiSpace.lean, line 216

*What differs.*
- The isomorphism holds at every $s \in [0, 1]$, along any smooth curve in $N$; that every pair of initial values occurs is the global existence of V9.1.
- Fields are normalized to be constant off $[0, 1]$, so that the space is finite-dimensional on the nose; its elements are maps on $\mathbb R$.

### V9.4. Conjugate points and their multiplicity

*restated* · parameters, as the footnote advises

**Milnor (§14, p. 77).** For $a \ne b$, the points $p = \gamma(a)$ and $q = \gamma(b)$ are *conjugate* along $\gamma$ if there is a non-zero Jacobi field $J$ along $\gamma$ which vanishes for $t = a$ and $t = b$; the multiplicity of $p$ and $q$ as conjugate points is the dimension of the vector space of all such fields. A footnote warns that if $\gamma$ has self-intersections one should rather say that the parameter values $a$ and $b$ are conjugate.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $\gamma$ be a smooth curve in $N$ on $[0, 1]$. Parameters $a$ and $b$ are *conjugate along $\gamma$* if $a, b \in [0, 1]$, $a \ne b$, and some Jacobi field along $\gamma$ vanishes at $a$ and at $b$ without vanishing identically on $[0, 1]$. Their *multiplicity* is the dimension of the space of fields of $\mathcal J(\gamma)$ vanishing at $a$ and $b$, finite by V9.3; for $a \ne b$ in $[0, 1]$ they are conjugate iff the multiplicity is positive.

- `Morse.IsConjugate` — Morse/Chapter9/JacobiSpace.lean, line 235
- `Morse.conjSpace` — Morse/Chapter9/JacobiSpace.lean, line 241
- `Morse.conjMultiplicity` — Morse/Chapter9/JacobiSpace.lean, line 259
- `Morse.isConjugate_iff` — Morse/Chapter9/JacobiSpace.lean, line 263

*What differs.*
- Conjugacy is a relation between parameter values, as Milnor's footnote recommends; throughout §15, "the conjugate points $\gamma(t)$" are read as the conjugate parameters $t$.

### V9.5. Theorem 14.1: the null vectors of $E_{**}$ are the Jacobi fields

*restated* · jumps of $PW_1'$ vs. jumps of $W_1'$ · pieces joined by a local argument

**Milnor (§14, Theorem 14.1, p. 78).** A vector field $W_1 \in T\Omega_\gamma$ belongs to the null space of $E_{**}$ if and only if $W_1$ is a Jacobi field. Proof (pp. 78–79): a Jacobi field vanishing at the ends is null by the second variation formula; conversely, testing against $W_2 = f(t)(\frac{D^2W_1}{dt^2} + R(V, W_1)V)$, $f$ vanishing exactly at the break points, makes $W_1$ a Jacobi field on each piece, testing against a field with values $\Delta_{t_i}\frac{DW_1}{dt}$ at the break points removes the jumps, and the pieces "fit together" since a solution is determined by $W_1(t_i)$ and $\frac{DW_1}{dt}(t_i)$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $\gamma \in \Omega(N; p, q)$ be a geodesic (V8.10) and $W_1 \in T\Omega_\gamma$. Then $E_{**}(W_1, W_2) = 0$ for every $W_2 \in T\Omega_\gamma$ iff $W_1$ is a Jacobi field along $\gamma$; in particular such a $W_1$ is $C^\infty$ on all of $[0, 1]$. On the way: for a Jacobi field $J$ along any curve, $\Phi(J, Y) = 0$ for every field $Y$; for a null vector the Jacobi operator vanishes off the break points and every jump of $W_1'$ is tangent and zero; and for a smooth tangent field the Jacobi equation is a second-order equation in $V$.

- `Morse.IsJacobiField.mem_pathTangent` — Morse/Chapter8/Jacobi.lean, line 180
- `Morse.IsJacobiField.secondVariation_eq_zero` — Morse/Chapter8/Jacobi.lean, line 187
- `Morse.jacobiExpr_eq_zero_of_null` — Morse/Chapter8/Jacobi.lean, line 246
- `Morse.jump_eq_zero_of_null` — Morse/Chapter8/Jacobi.lean, line 342
- `Morse.smooth_near_of_null` — Morse/Chapter8/Jacobi.lean, line 502
- `Morse.theorem_14_1` — Morse/Chapter8/Jacobi.lean, line 681

*What differs.*
- In $V$, the absence of jumps of $\frac{DW_1}{dt} = PW_1'$ makes $W_1$ of class $C^1$ only because the normal parts of the two one-sided derivatives agree (both are $\mathrm{II}(V, W_1)$).
- The test field with prescribed values at the break points has to be constructed, and Milnor's fitting together needs Jacobi fields along all of $\gamma$ with given initial values (V9.2), stated in the book without proof. The formal proof joins the pieces by a local argument instead: a smooth second-order equation holds on both sides of a former break point with a right side continuous across it.

### V9.6. Theorem 14.1: the null space and the nullity

*restated* · null space read on $[0, 1]$ · parameters $0$ and $1$ for $p$ and $q$

**Milnor (§14, Theorem 14.1, pp. 77–79).** The null space of $E_{**}$ is the space of $W_1 \in T\Omega_\gamma$ with $E_{**}(W_1, W_2) = 0$ for all $W_2$, the nullity $\nu$ is its dimension, and $E_{**}$ is degenerate if $\nu > 0$ (pp. 77–78). Theorem 14.1 continues: hence $E_{**}$ is degenerate if and only if the end points $p$ and $q$ are conjugate along $\gamma$, and the nullity of $E_{**}$ equals their multiplicity as conjugate points. On p. 79: the nullity is always finite.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: for $\gamma \in \Omega(N; p, q)$, the *null space* of $E_{**}$ is the space of the restrictions to $[0, 1]$, extended as constants, of the $W_1 \in T\Omega_\gamma$ with $E_{**}(W_1, W_2) = 0$ for all $W_2 \in T\Omega_\gamma$, and the *nullity* is its dimension. If $\gamma$ is a geodesic, the null space is the space of fields of $\mathcal J(\gamma)$ vanishing at $0$ and $1$; so the nullity is the multiplicity of $0$ and $1$ as conjugate parameters (V9.4), in particular finite, and it is positive iff $0$ and $1$ are conjugate along $\gamma$.

- `Morse.restrictIcc` — Morse/Chapter9/JacobiSpace.lean, line 287
- `Morse.hessNullSpace` — Morse/Chapter9/JacobiSpace.lean, line 298
- `Morse.hessNullity` — Morse/Chapter9/JacobiSpace.lean, line 304
- `Morse.hessNullSpace_eq` — Morse/Chapter9/JacobiSpace.lean, line 309
- `Morse.theorem_14_1_nullity` — Morse/Chapter9/JacobiSpace.lean, line 335
- `Morse.hessNullity_pos_iff` — Morse/Chapter9/JacobiSpace.lean, line 343

*What differs.*
- Fields are maps on $\mathbb R$ whose values off $[0, 1]$ play no role, so the literal kernel of the formal $E_{**}$ contains every field vanishing on $[0, 1]$ and is infinite-dimensional; the null space is therefore taken modulo the values off $[0, 1]$.
- Finiteness needs the identification with a subspace of the $2n$-dimensional $\mathcal J(\gamma)$ (V9.3).

### V9.7. Remark 14.2: the nullity is less than $n$

*stronger* · the constant geodesic included · $n \ge 1$ needed

**Milnor (§14, Remark 14.2, p. 79).** Actually the nullity satisfies $0 \le \nu < n$: the Jacobi fields vanishing for $t = 0$ form a space of dimension precisely $n$, and $J_t = tV_t$ is a Jacobi field vanishing for $t = 0$ but not for $t = 1$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: along a smooth curve $\gamma$ in $N$ on $[0, 1]$, the fields of $\mathcal J(\gamma)$ vanishing at $0$ form a space of dimension $n = \dim N$. If $\gamma$ is moreover a geodesic on $(0, 1)$, then $t \mapsto tV(t)$ is a Jacobi field, and $\gamma$ is constant on $[0, 1]$ if $V(1) = 0$; along a constant curve, $t \mapsto ty$ is a Jacobi field for every tangent vector $y$. Hence, for a geodesic $\gamma \in \Omega(N; p, q)$ and $n \ge 1$, the nullity of $E_{**}$ satisfies $\nu < n$.

- `Morse.finrank_jacobiSpace_zero` — Morse/Chapter9/JacobiSpace.lean, line 351
- `Morse.isJacobiField_smul_vel` — Morse/Chapter9/JacobiSpace.lean, line 379
- `Morse.isJacobiField_const_curve` — Morse/Chapter9/JacobiSpace.lean, line 416
- `Morse.remark_14_2` — Morse/Chapter9/JacobiSpace.lean, line 474

*What differs.*
- Milnor's $J_1 = V_1 \ne 0$ requires $\gamma$ non-constant; the formal statement includes the constant geodesic ($p = q$), with $ty$, $y \ne 0$, in place of $tV$.
- $\nu < n$ requires $n \ge 1$: for $n = 0$, $\nu = 0 = n$.

### V9.7′. Example 1: no conjugate points in a flat space

*narrower* · only codimension $0$: open sets of $V$ · flat tori are not covered · proved in Chapter 10

**Milnor (§14, Example 1, p. 79).** Suppose that $M$ is "flat", in the sense that the curvature tensor is identically zero. Then the Jacobi equation becomes $\frac{D^2J}{dt^2} = 0$; in parallel fields, $J = \sum f^iP_i$ with $\frac{d^2f^i}{dt^2} = 0$. Evidently a Jacobi field along $\gamma$ can have at most one zero; thus there are no conjugate points, and $E_{**}$ is non-degenerate.

**Proved in Lean.** Let $N \subseteq V$ be a slice submanifold every tangent space of which is all of $V$ (for instance an open subset of $V$, which is a slice submanifold of codimension $0$). Then the induced metric is flat ($R = 0$); along a curve in $N$ every Jacobi field is affine, $J(t) = J(0) + t(J(1) - J(0))$ on $[0, 1]$; no two parameters are conjugate along any curve in $N$; and at every geodesic of $\Omega(N; p, q)$ the index and the nullity of $E_{**}$ are $0$.

- `Morse.isSliceSubmanifold_of_isOpen` — Morse/Chapter10/Incomplete.lean, line 128
- `Morse.curvR_eq_zero_of_top` — Morse/Chapter10/Incomplete.lean, line 231
- `Morse.IsJacobiField.eqOn_affine_of_top` — Morse/Chapter10/Incomplete.lean, line 286
- `Morse.not_isConjugate_of_top` — Morse/Chapter10/Incomplete.lean, line 301
- `Morse.hessNullity_eq_zero_of_top` — Morse/Chapter10/Incomplete.lean, line 396

*What differs.*
- The verified Chapter 9 lists Example 1 as not formalized; the case proved, in `Morse/Chapter10/Incomplete.lean`, is the one Chapter 10 needs for its counterexample to Corollary 17.5 (V10.27).
- Milnor's hypothesis is $R \equiv 0$; the formal one is that $N$ has codimension $0$. A flat manifold embedded with positive codimension, such as a flat torus in $\mathbb R^4$, has $R = 0$ but is not covered, since its Jacobi fields are not computed without parallel frames.
- The formal statement also gives index $0$ at every geodesic, which Milnor does not state here.

### V9.7″. Example 2: antipodal points of $S^n$

*stronger* · every great circle, every parameter · Jacobi fields computed, no rotations · proved in Chapter 10

**Milnor (§14, Example 2, pp. 79–80).** Suppose that $p$ and $q$ are antipodal points on the unit sphere $S^n$, and let $\gamma$ be a great circle arc from $p$ to $q$. Then $p$ and $q$ are conjugate with multiplicity $n - 1$, so the nullity of $E_{**}$ takes its largest possible value. Proof (p. 80): rotating the sphere about the axis through $p$ and $q$ gives variations through geodesics, whose variation fields are Jacobi fields vanishing at $p$ and $q$ (Lemma 14.3); rotating in $n - 1$ different directions gives $n - 1$ linearly independent ones.

**Proved in Lean.** On the unit sphere $S^n \subseteq \mathbb R^{n+1}$, $n \ge 1$, with the induced metric: for unit vectors $p \perp u$ and $L \in \mathbb R$, $c(t) = \cos(Lt)\,p + \sin(Lt)\,u$ is a geodesic on $\mathbb R$; for every $e \perp p, u$, $t \mapsto \sin(Lt)\,e$ is a Jacobi field along $c$; and for $L > 0$ and $0 < t \le 1$, the multiplicity of $0$ and $t$ as conjugate parameters along $c$ is $n - 1$ if $Lt$ is a multiple of $\pi$, and $0$ otherwise. For $L = \pi$, $t = 1$ this is Milnor's statement for the great semicircle from $p$ to $-p$.

- `Morse.greatCircle` — Morse/Chapter10/SphereGeodesics.lean, line 134
- `Morse.isGeodesicOn_greatCircle` — Morse/Chapter10/SphereGeodesics.lean, line 217
- `Morse.isJacobiField_sin_smul` — Morse/Chapter10/SphereGeodesics.lean, line 360
- `Morse.conjMultiplicity_greatCircle` — Morse/Chapter10/SphereGeodesics.lean, line 408

*What differs.*
- The verified Chapter 9 lists Example 2 as not formalized; it is proved in `Morse/Chapter10/SphereGeodesics.lean`, where the index of every geodesic between two points of $S^n$ is computed (V10.23).
- The formal statement covers every great circle and every parameter: the conjugate parameters along $c$ are exactly the $t$ with $Lt \in \pi\mathbb Z$, each of multiplicity $n - 1$, which is what the index computation of §17 needs.
- The Jacobi fields are checked directly with $R(x, y)z = \langle x, z\rangle y - \langle y, z\rangle x$ rather than through rotations and Lemma 14.3; the upper bound $n - 1$ comes from Remark 14.2 (V9.7), as in the book.

### V9.8. Lemma 14.3: variations through geodesics give Jacobi fields

*hypotheses explicit* · Lemmas 8.7, 9.2 on a closed strip

**Milnor (§14, Lemma 14.3, p. 80).** A variation of $\gamma$ through geodesics, not necessarily keeping the end points fixed, is a $C^\infty$ map $\alpha : (-\varepsilon, \varepsilon) \times [0, 1] \to M$ with $\alpha(0, t) = \gamma(t)$ and each $\bar\alpha(u)$ a geodesic (p. 79). Lemma 14.3: its variation vector field $W(t) = \frac{\partial\alpha}{\partial u}(0, t)$ is a Jacobi field along $\gamma$. Proof: apply $\frac{D}{\partial u}$ to $\frac{D}{\partial t}\frac{\partial\alpha}{\partial t} = 0$ and use Lemmas 9.2 and 8.7.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $\varepsilon > 0$ and $\alpha(u, t)$ be $C^\infty$ on $(-\varepsilon, \varepsilon) \times [0, 1]$ (one-sided derivatives along the edges $t = 0, 1$), with values in $N$ there, such that each $t \mapsto \alpha(u, t)$, $|u| < \varepsilon$, is a geodesic on $(0, 1)$. Then $W(t) = \frac{\partial\alpha}{\partial u}(0, t)$ is a Jacobi field along $\alpha(0, \cdot)$. Being a Jacobi field along $\gamma$ depends only on $\gamma$ on $[0, 1]$.

- `Morse.IsJacobiField.congr_curve` — Morse/Chapter9/JacobiVariation.lean, line 58
- `Morse.lemma_14_3` — Morse/Chapter9/JacobiVariation.lean, line 83

*What differs.*
- Lemmas 9.2 and 8.7 are applied to a map defined on a strip and smooth up to its edges; the formal proof uses the identity (13.3) of V8.12 on the open strip, and gets the smoothness of $W$ up to $t = 0, 1$ from that of $\alpha$ on the closed strip.

### V9.9. Lemma 14.4: every Jacobi field comes from a variation through geodesics

*as in the book* · proved from initial data · no minimal geodesics needed · geodesic segments extend past the ends

**Milnor (§14, Lemma 14.4, p. 81).** Every Jacobi field along a geodesic $\gamma : [0, 1] \to M$ may be obtained by a variation of $\gamma$ through geodesics. Proof: in a neighbourhood $U$ of $\gamma(0)$ where any two points are joined by a unique minimal geodesic depending differentiably on the end points, with $\gamma(t) \in U$ for $0 \le t \le \delta$, minimal geodesics between the points of two curves $a(u)$, $b(u)$ give Jacobi fields along $\gamma|[0, \delta]$ with arbitrary values at $0$ and $\delta$; so $J \mapsto (J(0), J(\delta))$ is onto, hence an isomorphism (both spaces have dimension $2n$); "using the compactness of $[0, 1]$", the geodesics extend over $[0, 1]$ for small $u$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: (i) for $x_1 \in N$ and $R > 0$ there are an open $U \ni x_1$, an $h > 0$ and $\Phi$, $C^\infty$ on $U \times \{\|w\| < R\} \times (-h, h)$, with $\exp_y(tw) = \Phi(y, w, t)$ a geodesic on $(-h, h)$ for $y \in N \cap U$, $w \in T_yN$, $\|w\| < R$. (ii) A smooth curve $\gamma$ in $N$ on $[0, 1]$ that is a geodesic on $(0, 1)$ agrees on $[0, 1]$ with $t \mapsto \exp_{\gamma(0)}(tV(0))$, a geodesic on an open interval containing $[0, 1]$. (iii) Geodesics $t \mapsto \exp_{c(u)}(t\,w(u))$ with smooth initial data depend smoothly on $(u, t)$ over any compact time interval on which the one at $u = 0$ exists. (iv) **Lemma 14.4:** for such a $\gamma$ and a Jacobi field $J$ along it, there are $\varepsilon > 0$ and $\alpha$ satisfying the hypotheses of Lemma 14.3 (V9.8) on $(-\varepsilon, \varepsilon) \times [0, 1]$, with $\alpha(0, t) = \gamma(t)$ and $\frac{\partial\alpha}{\partial u}(0, t) = J(t)$ for $t \in [0, 1]$.

- `Morse.exists_smooth_ray` — Morse/Chapter9/GeodesicVariation.lean, line 86
- `Morse.exists_initial_ray` — Morse/Chapter9/GeodesicVariation.lean, line 494
- `Morse.RaysGood` — Morse/Chapter9/GeodesicVariation.lean, line 274
- `Morse.raysGood_of_isGeodesicOn` — Morse/Chapter9/GeodesicVariation.lean, line 446
- `Morse.lemma_14_4` — Morse/Chapter9/GeodesicVariation.lean, line 529

*What differs.*
- The statement is Milnor's; the proof departs from his. The variation is built from initial data, $\alpha(u, t) = \exp_{c(u)}(t\,w(u))$ with $c(u) = \exp_{\gamma(0)}(uJ(0))$ and $w(u) = P_{c(u)}(V(0) + u\frac{DJ}{dt}(0))$; its variation field is a Jacobi field with the initial data of $J$, hence equals $J$ (V9.2). No minimal geodesic, restriction to $[0, \delta]$ or dimension count is used.
- Milnor's construction returns $\bar\alpha(0) = \gamma|[0, \delta]$ only if $\gamma|[0, \delta]$ is *the* minimal geodesic between its ends, which $\gamma([0, \delta]) \subseteq U$ does not say; it is true for his $U$ by an argument the book omits. His compactness step is the smooth dependence of geodesics on initial data over a compact interval, (iii), with the openness of the domain of $\exp$ — neither among the statements of §10.
- (ii) is the extension of a geodesic segment past its end points, which makes Milnor's domain of $\exp$ equal to the formal one (V7.7).

### V9.10. A Jacobi field is determined by its values at two non-conjugate points

*stronger* · the values can be prescribed

**Milnor (§14, p. 81).** In the proof of Lemma 14.4, in parentheses and without proof: more generally a Jacobi field is determined by its values at any two non-conjugate points.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $\gamma$ be a smooth curve in $N$ on $[0, 1]$ and $a \ne b$ in $[0, 1]$ parameters that are not conjugate along $\gamma$ (V9.4). Then $J \mapsto (J(a), J(b))$ is a linear isomorphism $\mathcal J(\gamma) \to T_{\gamma(a)}N \times T_{\gamma(b)}N$: a Jacobi field is determined by its values at $a$ and $b$, and these values can be prescribed.

- `Morse.jacEvalEnds` — Morse/Chapter9/IndexForm.lean, line 425
- `Morse.jacEvalEnds_bijective_of_not_isConjugate` — Morse/Chapter9/GeodesicVariation.lean, line 659

*What differs.*
- Injectivity is the definition of non-conjugacy; the formal statement adds surjectivity, by the dimension count of V9.3.

### V9.11. Remark 14.5: Jacobi fields along short geodesics

*restated* · the neighbourhoods of Lemma 10.3 · end values can be prescribed

**Milnor (§14, Remark 14.5, p. 81).** The argument of Lemma 14.4 shows that in any such neighbourhood $U$ the Jacobi fields along a geodesic segment in $U$ are uniquely determined by their values at the end points of the segment.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: (i) let $\varepsilon$ be a normal radius at $q \in N$ (V7.9), $v \in T_qN$ and $\|v\| < \varepsilon$. Then $\sigma(t) = \exp_q(tv)$ is a smooth curve in $N$ on $[0, 1]$; a Jacobi field along $\sigma$ vanishing at $t = 0$ and $t = 1$ vanishes on $[0, 1]$; and $J \mapsto (J(0), J(1))$ is a linear isomorphism $\mathcal J(\sigma) \to T_qN \times T_{\sigma(1)}N$. (ii) Every $p \in N$ has an open neighbourhood $O$ in $V$, with an $\varepsilon > 0$, such that for all $q_1, q_2 \in N \cap O$ there is $v \in T_{q_1}N$ with $\|v\| < \varepsilon$ and $\exp_{q_1}(v) = q_2$, $\varepsilon$ is a normal radius at $q_1$, and a Jacobi field along $t \mapsto \exp_{q_1}(tv)$ vanishing at both ends vanishes on $[0, 1]$.

- `Morse.IsNormalRadius.isSmoothCurveIn_ray` — Morse/Chapter9/JacobiVariation.lean, line 174
- `Morse.remark_14_5_of_isNormalRadius` — Morse/Chapter9/JacobiVariation.lean, line 207
- `Morse.remark_14_5_bijective` — Morse/Chapter9/JacobiVariation.lean, line 368
- `Morse.remark_14_5` — Morse/Chapter9/JacobiVariation.lean, line 355

*What differs.*
- Milnor's $U$ (unique minimal geodesics depending differentiably on their ends) is replaced by the neighbourhoods of Lemma 10.3 (V7.10), and "a geodesic segment in $U$" by $t \mapsto \exp_{q_1}(tv)$ with $\|v\|$ below a normal radius, the shortest path of V7.15.
- Injectivity comes from the local inverse of $\exp_q$: the Jacobi field with $J(0) = 0$, $\frac{DJ}{dt}(0) = w$ is $t \mapsto d(\exp_q)_{tv}(tw)$, and $d(\exp_q)_v$ is injective; surjectivity is the dimension count. Milnor goes the other way, from the surjectivity of his construction.

### V9.12. Remark 14.6: no conjugate points near the start

*narrower* · only $t > 0$ · no statement along an entire geodesic · along any smooth curve

**Milnor (§14, Remark 14.6, p. 82).** The proof of 14.4 also shows that there is a neighbourhood $(-\delta, \delta)$ of $0$ such that $\gamma(t)$ is not conjugate to $\gamma(0)$ along $\gamma$ for $t \in (-\delta, \delta)$; and, by 15.2, the points conjugate to $\gamma(0)$ along an entire geodesic have no cluster points.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: for every smooth curve $\gamma$ in $N$ on $[0, 1]$ there is $\delta > 0$ such that no $t \in (0, \delta)$ is conjugate to $0$ along $\gamma$.

- `Morse.remark_14_6` — Morse/Chapter9/IndexTheorem.lean, line 277

*What differs.*
- Only $t > 0$, $\gamma$ being given on $[0, 1]$; the statement that the conjugate points along an entire geodesic have no cluster points is not formalized (the reparametrization of a geodesic to $[0, 1]$, the exposition's Lemma 14.C, is not formalized).
- It holds along any smooth curve in $N$, with $\delta$ the explicit mesh of V9.16, since no two parameters closer than it are conjugate; Milnor's neighbourhood $U$, which needs $\gamma|[0, t]$ to be the minimal geodesic between its ends, is not used.

### V9.13. The index and the nullity of a bilinear form

*restated* · a supremum, possibly $\infty$ · finiteness is part of Theorem 15.1

**Milnor (§15, p. 83; §2, p. 5).** The index $\lambda$ of $E_{**}$ is the maximum dimension of a subspace of $T\Omega_\gamma$ on which $E_{**}$ is negative definite (p. 83); for a bilinear functional on a vector space, the index and the nullity are defined in §2 (p. 5).

**Proved in Lean.** Let $B$ be a bilinear form on a real vector space $X$. $B$ is negative (positive) definite on a subspace $S$ if $B(x, x) < 0$ ($> 0$) for every $x \ne 0$ in $S$. The *index* of $B$ is the supremum, in $\{0, 1, 2, \dots\} \cup \{\infty\}$, of the dimensions of the finite-dimensional subspaces on which $B$ is negative definite; a finite index is the dimension of such a subspace. A linear map $L$ with $B'(Lx, Ly) = B(x, y)$ does not decrease the index, so an isomorphism carrying $B$ to $B'$ preserves it; on a finite-dimensional space the index is Mathlib's negative index of inertia of $x \mapsto B(x, x)$. The *nullity* is the dimension of $\{x : B(x, y) = 0 \text{ for all } y\}$; for $E_{**}$ the null space is read on $[0, 1]$ (V9.6).

- `Morse.IsNegDefOn` — Morse/Chapter9/FormIndex.lean, line 50
- `Morse.formIndex` — Morse/Chapter9/FormIndex.lean, line 59
- `Morse.le_formIndex` — Morse/Chapter9/FormIndex.lean, line 62
- `Morse.formIndex_le_of_map` — Morse/Chapter9/FormIndex.lean, line 85
- `Morse.formIndex_eq_sigNeg` — Morse/Chapter9/FormIndex.lean, line 246

*What differs.*
- Milnor's "maximum dimension" presupposes that the maximum exists; here the index is a supremum over finite-dimensional subspaces, possibly $\infty$, and its finiteness for $E_{**}$ is part of Theorem 15.1, as in the book. A negative definite subspace of infinite dimension contains finite-dimensional ones of every dimension, and so also gives $\infty$.

### V9.14. Linear algebra for the index theorem (Lemmas 15.A and 15.B)

*not in the book* · used without proof on pp. 85–87 · independence of the compound family

**Milnor (§15, pp. 85–87).** The book has no such statements; on pp. 85–87 Milnor uses without proof: that the index and nullity of $E_{**}$ can be computed on a summand complementary to a perpendicular subspace on which $E_{**}$ is positive definite ("the proof is straightforward", Lemma 15.4); that definiteness of $H_\tau$ on a subspace persists for $H_{\tau'}$ near $H_\tau$; a positive definite subspace of dimension $ni - \lambda(\tau) - \nu$; and a compound matrix that is "certainly negative definite" for small $c$.

**Proved in Lean.** Let $B$ be a bilinear form on a real vector space $X$. (1) If $\dim X = m < \infty$, a negative definite and a positive definite subspace have dimensions adding up to at most $m$. (2) (Sylvester) If $\dim X = m$ and $B$ is symmetric with index $\lambda$ and nullity $\nu$, $B$ is positive definite on a subspace of dimension $m - \lambda - \nu$. (3) If $(B_\tau)$ is a family indexed by a topological space, $S \subseteq X$ is finite-dimensional, $\tau \mapsto B_\tau(x, y)$ is continuous at $\tau_0$ for $x, y \in S$, and $B_{\tau_0}$ is negative (positive) definite on $S$, so is $B_\tau$ for $\tau$ near $\tau_0$. (4) (Lemma 15.B) If $X = A \oplus C$ with $B(a, c) = B(c, a) = 0$ and $B$ positive definite on $C$, then $B$ and $B|A$ have the same index, and the null space of $B$ is that of $B|A$. (5) (the compound matrix) If $B$ is symmetric, $U : \mathbb R^\lambda \to X$ linear with $B(Ua, Ua) < 0$ for $a \ne 0$, and $J, Y : \mathbb R^\nu \to X$ linear with $B(Jb, Ua) = 0$, $B(Jb, Jb') = 0$ and $B(Jb, Yb') = 2\langle b, b'\rangle$, then the index of $B$ is at least $\lambda + \nu$.

- `Morse.finrank_add_finrank_le` — Morse/Chapter9/FormIndex.lean, line 292
- `Morse.exists_isPosDefOn_add` — Morse/Chapter9/FormIndex.lean, line 280
- `Morse.eventually_isNegDefOn` — Morse/Chapter9/FormIndex.lean, line 312
- `Morse.formIndex_eq_restrict_of_isCompl` — Morse/Chapter9/FormIndex.lean, line 116
- `Morse.ker_eq_map_ker_restrict` — Morse/Chapter9/FormIndex.lean, line 156
- `Morse.le_formIndex_of_compound` — Morse/Chapter9/IndexAssertions.lean, line 62

*What differs.*
- These are stated and proved as lemmas. In (5) the hidden point is that a negative definite Gram matrix makes the $\lambda + \nu$ fields linearly independent; (3) is proved by the compactness of the unit sphere of $S$, and (5) from (3) for the family $Ua + c^{-1}Jb - cYb$.

### V9.15. The second variation formula for piecewise Jacobi fields

*hypotheses explicit* · stated once, for any curve

**Milnor (§15, pp. 84 and 87).** In the proof of Lemma 15.3 (p. 84), for a broken Jacobi field $W_1$ and a field $W_2$ vanishing at the break points, the second variation formula reduces to its jump terms; on p. 87 the values of $E_{**}(J_h, \cdot)$ are seen "easily" from the second variation formula.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $\gamma \in \Omega(N; p, q)$, $X, Y \in T\Omega_\gamma$, and $B$ a finite set such that near every $t \in (0, 1) \setminus B$ the field $X$ agrees with some Jacobi field along $\gamma$ (the zero field is one). Then $$E_{**}(X, Y) = -2\sum_{b \in B \cap (0, 1)}\Big\langle Y(b), \Delta_b\frac{DX}{dt}\Big\rangle,$$ $\Delta_b\frac{DX}{dt} = P_{\gamma(b)}(\Delta_bX')$. $\gamma$ need not be a geodesic.

- `Morse.jacobiExpr_congr` — Morse/Chapter9/IndexForm.lean, line 65
- `Morse.isJacobiField_zero` — Morse/Chapter9/IndexForm.lean, line 74
- `Morse.energyHessian_eq_jumps` — Morse/Chapter9/IndexForm.lean, line 87

*What differs.*
- The reduction that Milnor performs twice inside proofs is stated once: the integrand of the second variation formula (V8.13) vanishes off the finite set $B \cup \{1\}$.

### V9.16. Positivity near zeros, and fine subdivisions

*restated* · an explicit mesh $h_0$ · no $\exp$, no minimality · along any smooth curve

**Milnor (§15, pp. 83–84).** Each $\gamma(t)$ lies in an open set $U$ in which any two points are joined by a unique minimal geodesic depending differentiably on the end points (§10), and the subdivision $0 = t_0 < t_1 < \dots < t_k = 1$ is chosen "sufficiently fine" that each $\gamma|[t_{i-1}, t_i]$ lies in such a $U$ and is minimal. Milnor uses two consequences: along each segment the Jacobi fields are determined by their end values, which can be prescribed (Remark 14.5); and each segment has smaller energy than any other path between its end points (p. 84).

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $\gamma$ be a smooth curve in $N$ on $[0, 1]$, $C \ge 0$ a bound for $\|P'(t)\|^2 + \|K(t)\|$ on $[0, 1]$ ($K$ as in V9.2), and $h_0 = 1/(C + 1)$. (i) *Poincaré estimate:* if $X \in T\Omega_\gamma$ and every $t \in [0, 1]$ has a zero $s \in [0, t]$ of $X$ with $t - s \le h_0$, then $\int_0^1\|X\|^2\,dt \le \frac12E_{**}(X, X)$; so $E_{**}(X, X) \le 0$ forces $X = 0$ on $[0, 1]$. (ii) If $0 \le a < b \le 1$ and $b - a \le h_0$, a field of $\mathcal J(\gamma)$ vanishing at $a$ and $b$ is $0$, and $J \mapsto (J(a), J(b))$ is an isomorphism onto $T_{\gamma(a)}N \times T_{\gamma(b)}N$: no two parameters at distance at most $h_0$ are conjugate. (iii) A finite set $B \subseteq (0, \tau)$ is *fine for $[0, \tau]$* if consecutive points of $\{0\} \cup B \cup \{\tau\}$ are at most $h_0$ apart; for every $\tau > 0$ there is one whose last point is within $h_0/2$ of $\tau$.

- `Morse.fineMesh` — Morse/Chapter9/IndexForm.lean, line 152
- `Morse.hessForm_ge` — Morse/Chapter9/IndexForm.lean, line 241
- `Morse.eq_zero_of_short` — Morse/Chapter9/IndexForm.lean, line 365
- `Morse.jacEvalEnds_bijective` — Morse/Chapter9/IndexForm.lean, line 435
- `Morse.IsFine` — Morse/Chapter9/BrokenJacobi.lean, line 106
- `Morse.exists_isFine` — Morse/Chapter9/BrokenJacobi.lean, line 178

*What differs.*
- "Sufficiently fine" becomes the explicit mesh $h_0$, which depends only on bounds for $P'$ and the curvature along $\gamma$; $\gamma$ need not be a geodesic, and neither $\exp$ nor minimal geodesics enter.
- The existence of Milnor's subdivisions needs a Lebesgue number of a finite cover and a length bound for minimality (Theorem 10.4), which the book does not spell out; the Poincaré estimate replaces both of his uses.

### V9.17. Broken Jacobi fields and $T'$

*restated* · for every $\tau \in (0, 1]$ · fields vanishing outside $[0, \tau]$

**Milnor (§15, pp. 83–84 and 86).** $T\Omega_\gamma(t_0, t_1, \dots, t_k)$ is the space of vector fields $W$ along $\gamma$ vanishing at $0$ and $1$ such that each $W|[t_{i-1}, t_i]$ is a Jacobi field along $\gamma|[t_{i-1}, t_i]$: a finite-dimensional space of broken Jacobi fields (p. 83). $T'$ is the space of fields with $W(t_0) = W(t_1) = \dots = W(t_k) = 0$, and "it follows from §14.5" that the broken Jacobi field with given values at the $t_i$ exists and is unique (p. 84). On p. 86, along $\gamma_\tau$, the broken Jacobi fields for $0 < t_1 < \dots < t_i < \tau$ form a space isomorphic to $TM_{\gamma(t_1)} \oplus \dots \oplus TM_{\gamma(t_i)}$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $\gamma$ be a smooth curve in $N$ on $[0, 1]$. For $\tau \in \mathbb R$, the fields along $\gamma|[0, \tau]$ are the fields of $T\Omega_\gamma$ vanishing outside $[0, \tau]$. Let $0 < \tau \le 1$ and $B$ be fine for $[0, \tau]$ (V9.16). A map is a *broken Jacobi field* on $[0, \tau]$ for $B$ if on each piece between consecutive points of $\{0\} \cup B \cup \{\tau\}$ it agrees with a field of $\mathcal J(\gamma)$. Milnor's $T\Omega_\gamma(t_0, \dots, t_k)$ is the space of fields along $\gamma|[0, \tau]$ that are broken Jacobi fields, and $T'$ the fields along $\gamma|[0, \tau]$ vanishing at the points of $B$. $W \mapsto (W(b))_{b \in B}$ is a linear isomorphism from the broken Jacobi fields onto $\bigoplus_{b \in B}T_{\gamma(b)}N$.

- `Morse.fieldsUpTo` — Morse/Chapter9/BrokenJacobi.lean, line 72
- `Morse.IsBrokenJacobi` — Morse/Chapter9/BrokenJacobi.lean, line 228
- `Morse.brokenSpace` — Morse/Chapter9/BrokenJacobi.lean, line 319
- `Morse.nodeZero` — Morse/Chapter9/BrokenJacobi.lean, line 335
- `Morse.exists_isBrokenJacobi` — Morse/Chapter9/BrokenJacobi.lean, line 256
- `Morse.nodeEval_bijective` — Morse/Chapter9/IndexReduction.lean, line 159

*What differs.*
- Everything is along $\gamma|[0, \tau]$ for every $\tau \in (0, 1]$, as fields on $[0, 1]$ vanishing outside $[0, \tau]$; Milnor uses $\tau = 1$ here and $\gamma_\tau$ on p. 86.
- A piece is the restriction of a Jacobi field along all of $\gamma$, which is equivalent to being a Jacobi field along the segment by V9.1–V9.2, an equivalence not stated formally. Existence is by induction over the division points with V9.16 (ii); Milnor's "follows from §14.5" also needs the gluing of the pieces.

### V9.18. Lemma 15.3: the splitting of $T\Omega_\gamma$

*restated* · for every $\tau \in (0, 1]$ · positivity from the Poincaré estimate

**Milnor (§15, Lemma 15.3, p. 84).** $T\Omega_\gamma = T\Omega_\gamma(t_0, \dots, t_k) \oplus T'$, the two subspaces are mutually perpendicular with respect to $E_{**}$, and $E_{**}$ restricted to $T'$ is positive definite. Proof (pp. 84–85): $W = W_1 + (W - W_1)$; perpendicularity from the second variation formula; $E_{**}(W, W) \ge 0$ on $T'$ because each segment is minimal, and $E_{**}(W, W) = 0$ puts $W$ in the null space, so $W$ is a Jacobi field, and $T'$ contains no Jacobi field other than $0$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $\gamma$ be a smooth curve in $N$ on $[0, 1]$, $0 < \tau \le 1$ and $B$ fine for $[0, \tau]$. (i) The fields along $\gamma|[0, \tau]$ are the direct sum of the broken Jacobi fields and $T'$ (V9.17). (ii) For a broken Jacobi field $W_1$ and every field $Y$ along $\gamma|[0, \tau]$, $E_{**}(W_1, Y) = -2\sum_{b \in B}\langle Y(b), \Delta_b\frac{DW_1}{dt}\rangle$; in particular $E_{**}(W_1, W_2) = 0$ for $W_2 \in T'$. (iii) $E_{**}(W, W) > 0$ for every $W \ne 0$ in $T'$.

- `Morse.energyHessian_broken_eq` — Morse/Chapter9/BrokenJacobi.lean, line 408
- `Morse.isCompl_broken_nodeZero` — Morse/Chapter9/IndexReduction.lean, line 85
- `Morse.energyHessian_broken_nodeZero` — Morse/Chapter9/BrokenJacobi.lean, line 428
- `Morse.energyHessian_nodeZero_pos` — Morse/Chapter9/BrokenJacobi.lean, line 436

*What differs.*
- Stated along $\gamma|[0, \tau]$ for every $\tau \in (0, 1]$, for fine subdivisions in the sense of V9.16; Milnor's lemma is $\tau = 1$ for his subdivisions.
- (iii) departs from Milnor's proof: a field of $T'$ has a zero within $h_0$ before every point, so the Poincaré estimate gives $E_{**}(W, W) > 0$ directly, without minimal geodesics, variations or Theorem 14.1.

### V9.19. Lemma 15.4: the index on the broken Jacobi fields

*restated* · for every $\tau \in (0, 1]$ · nullity identified as $\nu(\tau)$ directly

**Milnor (§15, Lemma 15.4, p. 85).** The index (or the nullity) of $E_{**}$ is equal to the index (or the nullity) of $E_{**}$ restricted to the space $T\Omega_\gamma(t_0, \dots, t_k)$ of broken Jacobi fields; in particular the index $\lambda$ is always finite. Milnor adds only that "the proof is straightforward".

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $\gamma$, $\tau$ and $B$ be as in V9.18. The index (V9.13) of $E_{**}$ on the fields along $\gamma|[0, \tau]$ equals its index on the broken Jacobi fields; the null space of $E_{**}$ on the fields along $\gamma|[0, \tau]$ is the null space of its restriction to the broken Jacobi fields, and the latter has dimension $\nu(\tau)$, the multiplicity of $0$ and $\tau$ (V9.4), because a broken Jacobi field without jumps agrees on $[0, \tau]$ with a single field of $\mathcal J(\gamma)$. In particular the index is at most the dimension of the broken Jacobi fields, hence finite, for every $\tau \in (0, 1]$.

- `Morse.lemma_15_4` — Morse/Chapter9/IndexReduction.lean, line 112
- `Morse.lemma_15_4_ker` — Morse/Chapter9/IndexReduction.lean, line 129
- `Morse.eq_jacobi_of_jumps_zero` — Morse/Chapter9/IndexReduction.lean, line 194
- `Morse.finrank_ker_broken` — Morse/Chapter9/IndexReduction.lean, line 269
- `Morse.indexUpTo_lt_top` — Morse/Chapter9/IndexReduction.lean, line 376

*What differs.*
- The "straightforward" proof is the abstract Lemma 15.B (V9.14 (4)) applied to Lemma 15.3.
- Stated along $\gamma|[0, \tau]$ (Milnor states $\tau = 1$ and applies it to $\gamma_\tau$ on p. 86), for subdivisions fine in the sense of V9.16; the theorem needs only one fine subdivision.
- The nullity on the broken Jacobi fields is identified with $\nu(\tau)$ directly; Milnor gets this on p. 86 from Theorem 14.1 for $\gamma_\tau$.

### V9.20. $\lambda(\tau)$, and Assertions (1) and (2)

*restated* · restriction of $E_{**}$, not a new Hessian · no minimality for (2)

**Milnor (§15, p. 85).** For $0 < \tau \le 1$, let $\gamma_\tau = \gamma|[0, \tau]$, a geodesic from $\gamma(0)$ to $\gamma(\tau)$, and let $\lambda(\tau)$ be the index of the associated Hessian $(E_0^\tau)_{**}$; so $\lambda(1)$ is the index we are trying to compute. Assertion (1): $\lambda(\tau)$ is a monotone function of $\tau$, because a field along $\gamma_\tau$ vanishing at both ends extends by zero to one along $\gamma_{\tau'}$. Assertion (2): $\lambda(\tau) = 0$ for small $\tau$, because $\gamma_\tau$ is then a minimal geodesic (Lemma 13.6).

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: for a smooth curve $\gamma$ in $N$ on $[0, 1]$ and $\tau \in \mathbb R$, $\lambda(\tau)$ is the index of $E_{**}$ (of $\gamma$ on $[0, 1]$) restricted to the fields along $\gamma|[0, \tau]$, i.e. vanishing outside $[0, \tau]$ (V9.17); $\lambda(1)$ is the index of $E_{**}$ on all of $T\Omega_\gamma$. (1) $\lambda(\tau) \le \lambda(\tau')$ for $\tau \le \tau'$. (2) $\lambda(\tau) = 0$ for $0 < \tau \le h_0$ (V9.16).

- `Morse.indexUpTo` — Morse/Chapter9/IndexReduction.lean, line 360
- `Morse.indexUpTo_one` — Morse/Chapter9/IndexReduction.lean, line 419
- `Morse.indexUpTo_mono` — Morse/Chapter9/IndexReduction.lean, line 365
- `Morse.indexUpTo_eq_zero` — Morse/Chapter9/IndexReduction.lean, line 381

*What differs.*
- $\lambda(\tau)$ is the index of a restriction of $E_{**}$, not of a Hessian along $\gamma_\tau$ on its own interval: the fields along $\gamma_\tau$ vanishing at $0$ and $\tau$, extended by zero as in Milnor's proof of (1), with $\frac12E_{**}$ given on them by the integral over $[0, \tau]$ (V8.15). With this definition (1) is immediate, and no rescaling of $\gamma_\tau$ to $[0, 1]$ (the exposition's Lemma 13.B) is needed.
- (2) comes from the Poincaré estimate (V9.16 (i)): $E_{**}$ is positive definite on the fields along $\gamma|[0, \tau]$ when $\tau \le h_0$. Milnor's route needs short geodesics to be minimal (Theorem 10.4) and Lemma 13.6.

### V9.21. The forms $H_\tau$ and their continuity (Lemma 15.C)

*hypotheses explicit* · “evidently continuous” proved · needs the last segment non-conjugate

**Milnor (§15, p. 86).** With the subdivision chosen so that $t_i < \tau < t_{i+1}$, $\lambda(\tau)$ is the index of a quadratic form $H_\tau$ on the broken Jacobi fields along $\gamma_\tau$ for $0 < t_1 < \dots < t_i < \tau$, a space isomorphic to $\Sigma = TM_{\gamma(t_1)} \oplus \dots \oplus TM_{\gamma(t_i)}$, which is independent of $\tau$. "Evidently" $H_\tau$ varies continuously with $\tau$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $\gamma$ be a smooth curve in $N$ on $[0, 1]$ and $B$ a finite set; $\tau$ is *valid* for $B$ if $0 < \tau \le 1$ and $B$ is fine for $[0, \tau]$. For valid $\tau$, $H_\tau$ is the symmetric bilinear form on $\Sigma = \bigoplus_{b \in B}T_{\gamma(b)}N$ given by $E_{**}$ on the broken Jacobi fields along $\gamma|[0, \tau]$ with these values at the points of $B$ (V9.17). For valid $\tau$, the index of $H_\tau$ is $\lambda(\tau)$ and its nullity is $\nu(\tau)$. For $x, y \in \Sigma$, $\tau \mapsto H_\tau(x, y)$ is continuous on the set of valid $\tau$; and if $B$ is fine for $[0, \tau]$ with its last point $m$ within $h_0/2$ of $\tau$, every $\tau' \in (m, \tau + h_0/2)$ with $\tau' \le 1$ is valid.

- `Morse.validFor` — Morse/Chapter9/IndexContinuity.lean, line 111
- `Morse.Hform` — Morse/Chapter9/IndexContinuity.lean, line 137
- `Morse.formIndex_Hform` — Morse/Chapter9/IndexContinuity.lean, line 161
- `Morse.finrank_ker_Hform` — Morse/Chapter9/IndexContinuity.lean, line 169
- `Morse.continuousWithinAt_Hform` — Morse/Chapter9/IndexContinuity.lean, line 379
- `Morse.mem_validFor_of_near` — Morse/Chapter9/IndexContinuity.lean, line 422

*What differs.*
- The continuity needs that the subdivision stays fine for $\tau'$ near $\tau$, that the last division point and $\tau$ are not conjugate (so that the Jacobi field with prescribed values there exists), the linear dependence of Jacobi fields on their initial values, and the continuity of the solution of an injective linear system; all are supplied.
- The formal proof reads $H_\tau$ through its jump terms (V9.18 (ii)), where only the covariant derivative at the last division point depends on $\tau$; this replaces Cramer's rule in the exposition's proof.

### V9.22. Assertion (3): $\lambda$ is continuous from the left

*as in the book* · $\lambda$ as defined in V9.20

**Milnor (§15, Assertion (3), p. 85).** $\lambda(\tau - \varepsilon) = \lambda(\tau)$ for all sufficiently small $\varepsilon > 0$. Proof (p. 86): $H_\tau$ is negative definite on a subspace of $\Sigma$ of dimension $\lambda(\tau)$, hence so is $H_{\tau'}$ for $\tau'$ near $\tau$, giving $\lambda(\tau') \ge \lambda(\tau)$, and Assertion (1) gives the reverse inequality for $\tau' < \tau$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: for a smooth curve $\gamma$ in $N$ on $[0, 1]$ and $0 < \tau \le 1$, $\lambda(\tau') = \lambda(\tau)$ for all $\tau' < \tau$ close enough to $\tau$, $\lambda$ as in V9.20.

- `Morse.assertion_3` — Morse/Chapter9/IndexAssertions.lean, line 162

*What differs.*
- The proof is Milnor's, with V9.21 and the persistence of definiteness (V9.14 (3)); it needs $\lambda(\tau)$ finite and attained (V9.13, V9.19).

### V9.23. Assertion (4): the jump of $\lambda$

*stronger* · $\ge$ for every $\tau' \in (\tau, 1]$ · $\nu$ is the multiplicity $\nu(\tau)$

**Milnor (§15, Assertion (4), p. 86).** If $\nu$ is the nullity of $(E_0^\tau)_{**}$, then $\lambda(\tau + \varepsilon) = \lambda(\tau) + \nu$ for all sufficiently small $\varepsilon > 0$. Proof of $\le$: $H_\tau$ is positive definite on a subspace of dimension $ni - \lambda(\tau) - \nu$, hence so is $H_{\tau'}$ for $\tau'$ near $\tau$. Proof of $\ge$ (pp. 86–87): with $W_1, \dots, W_\lambda$ spanning a negative definite space, Jacobi fields $J_1, \dots, J_\nu$ vanishing at $0$ and $\tau$, and fields $X_k$ with $\langle\frac{DJ_h}{dt}(\tau), X_k(\tau)\rangle = \delta_{hk}$, all extended by $0$ beyond $\tau$, the fields $W_i$, $c^{-1}J_h - cX_h$ span a $(\lambda + \nu)$-dimensional space on which $(E_0^{\tau+\varepsilon})_{**}$ is negative definite for small $c$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $\gamma$ be a smooth curve in $N$ on $[0, 1]$, $0 < \tau < 1$, and $\nu(\tau)$ the multiplicity of $0$ and $\tau$ (V9.4). (i) $\lambda(\tau') \le \lambda(\tau) + \nu(\tau)$ for all $\tau' > \tau$ close enough to $\tau$. (ii) If $J \in \mathcal J(\gamma)$ vanishes at $0$ and $\tau$ and $\hat J$ is $J$ on $[0, \tau]$ and $0$ elsewhere, $E_{**}(\hat J, Z) = 2\langle Z(\tau), \frac{DJ}{dt}(\tau)\rangle$ for every $Z \in T\Omega_\gamma$. (iii) Linearly independent tangent vectors $d_1, \dots, d_\nu$ at a point have tangent vectors $x_k$ there with $\langle d_h, x_k\rangle = \delta_{hk}$. (iv) $\lambda(\tau') \ge \lambda(\tau) + \nu(\tau)$ for every $\tau' \in (\tau, 1]$. Hence $\lambda(\tau') = \lambda(\tau) + \nu(\tau)$ for all $\tau' > \tau$ close enough to $\tau$.

- `Morse.assertion_4_le` — Morse/Chapter9/IndexAssertions.lean, line 187
- `Morse.energyHessian_cut` — Morse/Chapter9/IndexAssertions.lean, line 218
- `Morse.exists_dual` — Morse/Chapter9/IndexAssertions.lean, line 267
- `Morse.assertion_4_ge` — Morse/Chapter9/IndexAssertions.lean, line 298
- `Morse.assertion_4` — Morse/Chapter9/IndexAssertions.lean, line 414

*What differs.*
- The lower bound (iv) holds for every $\tau' \in (\tau, 1]$, not only for $\tau'$ near $\tau$.
- Milnor's $\nu$, the nullity of $(E_0^\tau)_{**}$, is the multiplicity $\nu(\tau)$, which equals the nullity of $E_{**}$ along $\gamma|[0, \tau]$ by V9.19 and V9.21.
- Hidden: Sylvester's law of inertia and the nullity of $H_\tau$ for $\le$; for $\ge$, the linear independence of the $\frac{DJ_h}{dt}(\tau)$ (uniqueness, V9.2), the construction of the $X_k$ (a bump function times the vectors of (iii)), and the linear independence of the $\lambda + \nu$ fields (V9.14 (5)).

### V9.24. Theorem 15.1: the Morse index theorem

*stronger* · parameters, as the footnote advises · the identity along any smooth curve · finiteness of the set proved first

**Milnor (§15, Theorem 15.1, p. 83).** (Morse.) The index $\lambda$ of $E_{**}$ is equal to the number of points $\gamma(t)$, with $0 < t < 1$, such that $\gamma(t)$ is conjugate to $\gamma(0)$ along $\gamma$, each such conjugate point being counted with its multiplicity. The index $\lambda$ is always finite. On p. 87 the theorem "clearly follows" from Assertions (2), (3) and (4).

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: (i) let $\ell, \nu : \mathbb R \to \{0, 1, 2, \dots\}$ and $h_0 > 0$, with $\ell$ non-decreasing on $(0, 1]$, $\ell = 0$ on $(0, h_0]$, $\ell$ continuous from the left on $(0, 1]$, and $\ell(\tau') = \ell(\tau) + \nu(\tau)$ for $\tau' > \tau$ near $\tau$, $0 < \tau < 1$. Then $\nu(t) \ne 0$ for only finitely many $t \in (0, 1)$, and $\ell(1) = \sum_{0 < t < 1}\nu(t)$. (ii) For every smooth curve $\gamma$ in $N$ on $[0, 1]$, $\nu(t) \ne 0$ for only finitely many $t \in (0, 1)$, and $\lambda(1) = \sum_{0 < t < 1}\nu(t)$. (iii) **Theorem 15.1:** for a geodesic $\gamma \in \Omega(N; p, q)$, the parameters $t \in (0, 1)$ conjugate to $0$ along $\gamma$ form a finite set, and the index of $E_{**}$ on $T\Omega_\gamma$ (V9.13) is $\lambda = \sum_{0 < t < 1}\nu(t)$, each conjugate parameter counted with its multiplicity; in particular $\lambda$ is finite.

- `Morse.eq_finsum_of_jumps` — Morse/Chapter9/IndexTheorem.lean, line 58
- `Morse.indexUpTo_one_eq` — Morse/Chapter9/IndexTheorem.lean, line 213
- `Morse.theorem_15_1` — Morse/Chapter9/IndexTheorem.lean, line 243

*What differs.*
- Conjugate parameters replace conjugate points (V9.4), as Milnor's footnote of p. 77 recommends for geodesics with self-intersections.
- (ii) holds along any smooth curve in $N$; when $\gamma$ is not a geodesic, $E_{**}$ is the form of V8.14, not the Hessian of the energy.
- "Clearly follows" hides a step: the finiteness of the set of conjugate parameters has to be proved first, from Assertions (1) and (4) and the finiteness of $\lambda(1)$, before the jumps can be added up; then $\lambda(\tau) - \sum_{t < \tau}\nu(t)$ is locally constant on $(0, 1]$, and it vanishes for small $\tau$.

### V9.25. Corollary 15.2: finitely many conjugate points

*restated* · parameters for points

**Milnor (§15, Corollary 15.2, p. 83).** A geodesic segment $\gamma : [0, 1] \to M$ can contain only finitely many points which are conjugate to $\gamma(0)$ along $\gamma$; an "immediate consequence" of Theorem 15.1.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: for a geodesic $\gamma \in \Omega(N; p, q)$, the set of parameters conjugate to $0$ along $\gamma$ is finite.

- `Morse.corollary_15_2` — Morse/Chapter9/IndexTheorem.lean, line 267

*What differs.*
- Conjugate parameters replace conjugate points (V9.4); the proof is V9.24, plus the parameter $t = 1$.

## Chapter 10

*Milnor §§16–17, pp. 88–97: the finite-dimensional approximation, the full path space*

### V10.1. Milnor's metric on $\Omega$

*restated* · a pseudometric on maps $\mathbb R \to V$ · Minkowski for the triangle inequality

**Milnor (§16, p. 88).** The path space $\Omega$ can be topologized by the distance $d(\omega, \omega') = \max_t\rho(\omega(t), \omega'(t)) + \big[\int_0^1(\frac{ds}{dt} - \frac{ds'}{dt})^2dt\big]^{1/2}$, where $s(t)$ and $s'(t)$ are the arc lengths of $\omega$ and $\omega'$ from $0$ to $t$, and $\rho$ is the distance of §10.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric and its distance $\rho$ (V7.18): for $\omega, \eta \in \Omega(N; p, q)$, with speeds $\dot s_\omega = \|\omega'\|$ and $\dot s_\eta = \|\eta'\|$, $$d(\omega, \eta) = \sup_{0 \le t \le 1}\rho(\omega(t), \eta(t)) + \Big(\int_0^1(\dot s_\omega - \dot s_\eta)^2\,dt\Big)^{1/2}.$$ This is an extended pseudometric on $\Omega$ (values in $[0, \infty]$, symmetric, with the triangle inequality), and two paths that agree on $[0, 1]$ are at distance $0$. From now on $\Omega$ and its subsets carry the topology of $d$.

- `Morse.PathSp` — Morse/Chapter10/PathMetric.lean, line 185
- `Morse.PathSp.speed` — Morse/Chapter10/PathMetric.lean, line 196
- `Morse.PathSp.supDist` — Morse/Chapter10/PathMetric.lean, line 200
- `Morse.PathSp.l2Dist` — Morse/Chapter10/PathMetric.lean, line 203
- `Morse.PathSp.instPseudoEMetricSpace` — Morse/Chapter10/PathMetric.lean, line 257
- `Morse.PathSp.edist_eq_zero_of_eqOn` — Morse/Chapter10/Omega.lean, line 65

*What differs.*
- Paths are maps on $\mathbb R$ whose values off $[0, 1]$ play no role, and $d$ sees only $[0, 1]$, so it is a pseudometric; on paths $[0, 1] \to N$ it is Milnor's metric. Three conventions follow throughout the chapter: identities between paths hold on $[0, 1]$, homeomorphisms become homotopy equivalences up to paths at distance $0$, and geodesics are counted by their values on $[0, 1]$.
- The triangle inequality for the second term is Minkowski's inequality in $L^2$; $\frac{ds}{dt}$ exists except at finitely many points.

### V10.2. The energy is continuous for $d$ (Lemmas 16.A and 16.B)

*stronger* · $\sqrt{E}$ is $1$-Lipschitz · uniformly small energy on short intervals

**Milnor (§16, p. 88).** The last term of $d$ is added so that the energy $E_a^b(\omega) = \int_a^b(\frac{ds}{dt})^2dt$ is a continuous function on $\Omega$. Hence $\Omega^c = E^{-1}([0, c])$ is closed and $\operatorname{Int}\Omega^c = E^{-1}([0, c))$ is open.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: (i) for $\omega, \eta \in \Omega$ and $0 \le a \le b \le 1$, $|\sqrt{E_a^b(\omega)} - \sqrt{E_a^b(\eta)}| \le (\int_0^1(\dot s_\omega - \dot s_\eta)^2dt)^{1/2}$; hence $\sqrt{E_a^b}$ is $1$-Lipschitz for $d$, $E_a^b$ is continuous on $\Omega$, $\Omega^c$ is closed and $\operatorname{Int}\Omega^c$ is open. (ii) (Lemma 16.B) If $\omega_n \to \omega$ in $\Omega$, then for every $\epsilon > 0$ there is $\delta > 0$ with $E_a^b(\omega_n) < \epsilon$ for all $n$ and all $0 \le a \le b \le 1$ with $b - a < \delta$.

- `Morse.PathSp.abs_sqrt_energy_sub_le` — Morse/Chapter10/PathMetric.lean, line 285
- `Morse.PathSp.lipschitzWith_sqrt_energy` — Morse/Chapter10/PathMetric.lean, line 315
- `Morse.PathSp.continuous_energy` — Morse/Chapter10/PathMetric.lean, line 326
- `Morse.PathSp.isClosed_sublevel` — Morse/Chapter10/PathMetric.lean, line 333
- `Morse.PathSp.isOpen_sublevel_lt` — Morse/Chapter10/PathMetric.lean, line 337
- `Morse.PathSp.exists_energy_lt_of_tendsto` — Morse/Chapter10/PathMetric.lean, line 355

*What differs.*
- $\sqrt{E_a^b} = \|\dot s\|_{L^2[a, b]}$, and Minkowski's inequality on $[a, b]$ makes it $1$-Lipschitz for $d$; with the uniform term alone the energy is not continuous.
- (ii) is not in the book; it is what the continuity of Milnor's deformation $r_u$ needs (V10.7). The Lipschitz bound is also what makes Milnor's map $h$ of §17 discontinuous (V10.19′).

### V10.3. The ball $S$, subdivisions, and Milnor’s choices

*restated* · completeness only as compactness of $S$ · $\delta$ also below a normal radius

**Milnor (§16, pp. 88–89).** $\Omega(t_0, \dots, t_k)$ is the space of paths $\omega$ with each $\omega|[t_{i-1}, t_i]$ a geodesic, and $\operatorname{Int}\Omega(t_0, \dots, t_k)^c = (\operatorname{Int}\Omega^c) \cap \Omega(t_0, \dots, t_k)$ (p. 88). On p. 89: every $\omega \in \Omega^c$ lies in the ball $S$ of radius $\sqrt c$ about $p$, by $L^2 \le E \le c$; $S$ is compact since $M$ is complete; by 10.8 there is $\varepsilon > 0$ such that two points of $S$ at distance less than $\varepsilon$ are joined by a unique geodesic of length less than $\varepsilon$, depending differentiably on them; and the subdivision is chosen with each $t_i - t_{i-1} < \varepsilon^2/c$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $c > 0$ and $S = \{x \in N : \rho(p, x) \le \sqrt c\}$. (i) Every $\omega \in \Omega$ with $E(\omega) \le c$ maps $[0, 1]$ into $S$. (ii) $S$ is compact if $N$ is closed in $V$, or connected and complete. (iii) For every compact $K \subseteq N$ there is $\delta > 0$ such that points of $K$ at distance $< \delta$ are joined as in Corollary 10.8 at the scale $\delta$, and $\delta$ is at most a normal radius at every point of $K$. (iv) *Milnor's data* (V10.3): $p, q \in N$, $c > 0$ with $S = \{x \in N : \rho(p, x) \le \sqrt c\}$ compact, a scale $\delta$ as in Corollary 10.8 for $K = S$ that is also at most a normal radius on $S$ (Milnor's $\varepsilon$), and a subdivision $0 = t_0 < \dots < t_{m+1} = 1$ with $c\,(t_{i+1} - t_i) < \delta^2$. If $p, q \in N$ and $S$ is compact, every subdivision of small enough mesh, and some subdivision into equal parts, is part of such data. (v) For Milnor's data, $B = \operatorname{Int}\Omega(t_0, \dots, t_k)^c$ is the set of $\omega \in \Omega$ with $E(\omega) < c$ that are geodesics on each $(t_i, t_{i+1})$, and $B^a = \{\omega \in B : E(\omega) \le a\}$.

- `Morse.closedRiemBall` — Morse/Chapter10/Broken.lean, line 299
- `Morse.mem_closedRiemBall_of_energy_le` — Morse/Chapter10/Broken.lean, line 376
- `Morse.isCompact_closedRiemBall_of_isClosed` — Morse/Chapter10/Broken.lean, line 309
- `Morse.corollary_10_8'` — Morse/Chapter10/Broken.lean, line 273
- `Morse.BrokenSetup` — Morse/Chapter10/Broken.lean, line 450
- `Morse.exists_brokenSetup` — Morse/Chapter10/Broken.lean, line 466
- `Morse.BrokenSetup.brokenPaths` — Morse/Chapter10/BrokenPaths.lean, line 73

*What differs.*
- Completeness enters only as the compactness of $S$, which is the Hopf–Rinow theorem (Corollary 10.10, V7.27) and holds in particular when $N$ is closed in $V$.
- $\delta$ is also asked to be at most a normal radius on $S$, which (iii) provides at no cost and which keeps the ends of each segment non-conjugate (V10.10).

### V10.4. Lemma 16.1: the manifold of broken geodesics

*stronger* · $\Omega^c \neq \emptyset$ not needed · the manifold is $U \subseteq N^m$ itself

**Milnor (§16, Lemma 16.1, p. 88).** Let $M$ be complete and $c > 0$ with $\Omega^c$ non-vacuous. Then for all sufficiently fine subdivisions $(t_0, \dots, t_k)$ of $[0, 1]$, $\operatorname{Int}\Omega(t_0, \dots, t_k)^c$ can be given the structure of a smooth finite dimensional manifold "in a natural way". Proof (p. 89): for a broken geodesic $(L_{t_{i-1}}^{t_i}\omega)^2 = (t_i - t_{i-1})E_{t_{i-1}}^{t_i}\omega < \varepsilon^2$, so each segment is determined by its end points, and $\omega$ by $(\omega(t_1), \dots, \omega(t_{k-1})) \in M \times \dots \times M$; this is a homeomorphism onto an open subset of the product, whose differentiable structure is taken over.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: fix Milnor's data. For $y = (y_1, \dots, y_m) \in V^m$ put $x_0 = p$, $x_j = y_j$, $x_{m+1} = q$, and $E'(y) = \sum_{i=0}^m\rho(x_i, x_{i+1})^2/(t_{i+1} - t_i)$; let $U$ be the set of $y \in N^m$ with every $\rho(x_i, x_{i+1})$ finite and $E'(y) < c$. (i) $U = N^m \cap O$ for an open $O \subseteq V^m$, and every such set is a slice submanifold of $V^m$, with tangent space $T_{y_1}N \times \dots \times T_{y_m}N$. (ii) For $y \in U$, the broken geodesic $\omega_y$, on $[t_i, t_{i+1}]$ the short geodesic from $x_i$ to $x_{i+1}$ run at constant speed, lies in $B$, has break points $y$, and $E(\omega_y) = E'(y)$. (iii) Every $\omega \in B$ has its break points $y$ in $U$, and $\omega_y = \omega$ on $[0, 1]$. So $y \mapsto \omega_y$ and $\omega \mapsto (\omega(t_1), \dots, \omega(t_m))$ are inverse bijections between $U$ and $B$, paths compared on $[0, 1]$.

- `Morse.BrokenSetup.energy'` — Morse/Chapter10/Broken.lean, line 549
- `Morse.BrokenSetup.nodes` — Morse/Chapter10/Broken.lean, line 554
- `Morse.BrokenSetup.path` — Morse/Chapter10/Broken.lean, line 625
- `Morse.BrokenSetup.energy_path` — Morse/Chapter10/Broken.lean, line 780
- `Morse.BrokenSetup.lemma_16_1` — Morse/Chapter10/BrokenPaths.lean, line 238
- `Morse.BrokenSetup.exists_isOpen_nodes` — Morse/Chapter10/BrokenEnergy.lean, line 100
- `Morse.isSliceSubmanifold_pi_inter` — Morse/Chapter10/Product.lean, line 135

*What differs.*
- Milnor's hypothesis that $\Omega^c$ is non-vacuous is not needed (an empty manifold is a manifold).
- The manifold is the open subset $U$ of $N^m$, rather than a structure transported to $B$; the topologies are compared in V10.5.
- Hidden: that the image is exactly the open set $U$ (the vertices of a point of $U$ lie in $S$ by the Cauchy–Schwarz inequality, consecutive ones at distance $< \delta$); that a geodesic segment is the radial geodesic of its initial vector (V9.9) and, that vector being shorter than $\delta$, the short geodesic; and that a broken geodesic is smooth up to the ends of its segments.

### V10.5. Broken geodesics and their break points: a homeomorphism up to distance $0$

*restated* · homotopy equivalence, not homeomorphism · continuity of short geodesics in $d$

**Milnor (§16, p. 89).** "Evidently" the correspondence $\omega \mapsto (\omega(t_1), \dots, \omega(t_{k-1}))$ defines a homeomorphism between $\operatorname{Int}\Omega(t_0, \dots, t_k)^c$ and an open subset of $M \times \dots \times M$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: for Milnor's data, $y \mapsto \omega_y$ is continuous from $U$ (topology of $V^m$) to $(\Omega, d)$, and $\omega \mapsto (\omega(t_1), \dots, \omega(t_m))$ is continuous from $\Omega$ to $V^m$. For every $a$ they restrict to continuous maps between $B^a$ and $\{y \in U : E'(y) \le a\}$, inverse to each other up to paths at distance $0$; so the two sets are homotopy equivalent (for $a \ge c$, $B$ and $U$).

- `Morse.BrokenSetup.continuous_pathP` — Morse/Chapter10/Omega.lean, line 102
- `Morse.BrokenSetup.continuous_nodeVal` — Morse/Chapter10/Omega.lean, line 138
- `Morse.BrokenSetup.homotopyEquivNodes` — Morse/Chapter10/Omega.lean, line 162

*What differs.*
- A homotopy equivalence, indeed a homeomorphism up to the identification of paths at distance $0$, replaces the homeomorphism, since paths are maps on $\mathbb R$.
- "Evidently" hides the continuity of $y \mapsto \omega_y$ for $d$: the uniform term needs the continuity of short geodesics in their end points (Corollary 10.8 and the continuity of $\exp$, V7.23), and the $L^2$ term that of the speeds $\rho(x_i, x_{i+1})/(t_{i+1} - t_i)$.

### V10.6. Theorem 16.2: $E'$ is smooth and $B^a$ is compact

*restated* · $\rho^2 = \|v\|^2$ makes $E'$ smooth · exponent $2$, not the printed $c$

**Milnor (§16, Theorem 16.2, pp. 90–91).** The function $E' : B \to \mathbb R$, the restriction of $E$, is smooth; for each $a < c$ the set $B^a = (E')^{-1}[0, a]$ is compact. On p. 90 $E'$ depends smoothly on the break points by the explicit formula $E'(\omega) = \sum_i\rho(\omega(t_{i-1}), \omega(t_i))^2/(t_i - t_{i-1})$; on p. 91 $B^a$ is homeomorphic to a set of $(k - 1)$-tuples in $S \times \dots \times S$ that is closed in a compact set.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: for Milnor's data: (i) every $y_0 \in U$ has an open neighbourhood $O$ in $V^m$ with a function smooth on $O$ that equals $E'$ on $U \cap O$; hence $E'$ is continuous on $U$, and smooth on the manifold $N^m \cap O$ for every open $O \subseteq V^m$ with $N^m \cap O \subseteq U$. (ii) For $a < c$, $\{y \in U : E'(y) \le a\}$ is compact.

- `Morse.contMDiffAt_of_locally_eq` — Morse/Chapter10/Product.lean, line 207
- `Morse.BrokenSetup.exists_smooth_energy'` — Morse/Chapter10/BrokenEnergy.lean, line 131
- `Morse.BrokenSetup.contMDiff_energy'` — Morse/Chapter10/BrokenEnergy.lean, line 172
- `Morse.BrokenSetup.isCompact_sublevel` — Morse/Chapter10/BrokenEnergy.lean, line 184

*What differs.*
- $\rho$ is not smooth on the diagonal; $E'$ is smooth because $\rho(x, x')^2 = \|v(x, x')\|^2$ with $v$ the smooth initial vector of Corollary 10.8. The set of tuples is closed only because the distances are finite.
- As reproduced in the scan, the condition defining the tuples reads $\rho(p_{i-1}, p_i)^c/(t_i - t_{i-1}) \le a$, with exponent $c$ and no summation sign; the formal condition is $E'(p_1, \dots, p_{k-1}) \le a$, the sum with exponent $2$.
- Compactness is stated for the set of break points, which is homotopy equivalent to $B^a$ by V10.5.

### V10.7. Milnor’s deformation $r_u$ (Lemma 16.C)

*restated* · “easily verified” continuity proved · short geodesic for minimal geodesic

**Milnor (§16, p. 91).** The retraction $r : \operatorname{Int}\Omega^c \to B$ sends $\omega$ to the broken geodesic which on each $[t_{i-1}, t_i]$ is the geodesic of length less than $\varepsilon$ from $\omega(t_{i-1})$ to $\omega(t_i)$; "clearly" $E(r(\omega)) \le E(\omega) < c$. For $t_{i-1} \le u \le t_i$, $r_u(\omega)$ is $r(\omega)$ on $[0, t_{i-1}]$, the minimal geodesic from $\omega(t_{i-1})$ to $\omega(u)$ on $[t_{i-1}, u]$, and $\omega$ on $[u, 1]$; $r_0$ is the identity, $r_1 = r$, and "it is easily verified" that $r_u(\omega)$ is continuous as a function of both variables.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: for Milnor's data, $\omega \in \Omega$ with $E(\omega) < c$ and $t_i \le u \le t_{i+1}$, $r_u(\omega)$ is the broken geodesic of the break points of $\omega$ on $[0, t_i]$, the short geodesic from $\omega(t_i)$ to $\omega(u)$ at constant speed on $[t_i, u]$, and $\omega$ on $[u, 1]$; the formulas of neighbouring segments agree at $u = t_{i+1}$. On $[0, 1]$: $r_u(\omega) \in \Omega$, $E(r_u(\omega)) \le E(\omega)$, $r_0(\omega) = \omega$, $r_1(\omega) = \omega_y$ for the break points $y$ of $\omega$, and $r_u(\omega) = \omega$ for $\omega \in B$. Completed by $\omega$ off $[0, 1]$, and by $\omega$ itself when $u \notin [0, 1]$ or $E(\omega) \ge c$, $(u, \omega) \mapsto r_u(\omega)$ is a map $\mathbb R \times \Omega \to \Omega$, continuous on $[0, 1] \times \operatorname{Int}\Omega^c$.

- `Morse.BrokenSetup.retr` — Morse/Chapter10/Retraction.lean, line 178
- `Morse.BrokenSetup.energy_retr_le` — Morse/Chapter10/Retraction.lean, line 447
- `Morse.BrokenSetup.retr_of_mem_brokenPaths` — Morse/Chapter10/Retraction.lean, line 488
- `Morse.BrokenSetup.deform` — Morse/Chapter10/Deformation.lean, line 123
- `Morse.BrokenSetup.continuousOn_deform` — Morse/Chapter10/Deformation.lean, line 196

*What differs.*
- Milnor's minimal geodesic is the short geodesic of Corollary 10.8, which is minimal; it exists since $\rho(\omega(t_i), \omega(u))^2 \le (u - t_i)E(\omega) < \delta^2$.
- Hidden: the formulas must agree where neighbouring intervals meet; $r_u$ fixes $B$ because a sub-arc of a short geodesic is the short geodesic between its ends; and $E(r_u(\omega)) \le E(\omega)$ holds segment by segment, by $\rho^2 \le (b - a)E_a^b$.
- The continuity needs, for the uniform term, the continuity of short geodesics in their end points and the equicontinuity of the paths of energy $< c$, and, for the $L^2$ term near $u = t_i$, the bound $\rho(\omega(t_i), \omega(u))^2/(u - t_i) \le E_{t_i}^u(\omega)$ with Lemma 16.B (V10.2).

### V10.8. Theorem 16.2: $B^a$ is a deformation retract of $\Omega^a$

*restated* · strong deformation retraction, stated · exact, not only on $[0, 1]$

**Milnor (§16, Theorem 16.2, pp. 90–91).** For each $a < c$, $B^a$ is a deformation retract of $\Omega^a$; a footnote adds that $B$ itself is similarly a deformation retract of $\operatorname{Int}\Omega^c$. On p. 91: since $E(r_u(\omega)) \le E(\omega)$, "it is clear" that each $B^a$ is a deformation retract of $\Omega^a$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: for Milnor's data and $a < c$, the deformation of V10.7 is continuous on $[0, 1] \times \Omega^a$, does not increase the energy (so each $r_u$ maps $\Omega^a$ into itself), starts at the identity, ends in $B$, and fixes every point of $B$ for $0 \le u \le 1$. So $B^a$ is a strong deformation retract of $\Omega^a$ and the inclusion $B^a \subseteq \Omega^a$ is a homotopy equivalence; likewise $B$ is a strong deformation retract of $\operatorname{Int}\Omega^c$.

- `Morse.BrokenSetup.deform_zero` — Morse/Chapter10/Deformation.lean, line 155
- `Morse.BrokenSetup.energy_deform_le` — Morse/Chapter10/Deformation.lean, line 174
- `Morse.BrokenSetup.deform_one_mem_brokenPaths` — Morse/Chapter10/Deformation.lean, line 183
- `Morse.BrokenSetup.theorem_16_2_deformationRetract` — Morse/Chapter10/Deformation.lean, line 237
- `Morse.BrokenSetup.homotopyEquivBroken` — Morse/Chapter10/Deformation.lean, line 282

*What differs.*
- The strong deformation retraction is stated through the listed properties of $(u, \omega) \mapsto r_u(\omega)$, which hold exactly, not only on $[0, 1]$, thanks to the completion of V10.7; the hidden hypotheses are those of V10.7.

### V10.9. Theorem 16.2: the critical points of $E'$

*restated* · $E'$ read through an ambient extension · variations through broken geodesics

**Milnor (§16, Theorem 16.2, pp. 90–91).** The critical points of $E'$ are precisely the critical points of $E$ in $\operatorname{Int}\Omega^c$, namely the unbroken geodesics from $p$ to $q$ of length less than $\sqrt c$. On p. 91: every geodesic is a broken geodesic, so every critical point of $E$ in $\operatorname{Int}\Omega^c$ lies in $B$, and with the first variation formula (12.2) "it is clear" that the critical points of $E'$ are the unbroken geodesics.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: fix Milnor's data. (i) Every tangent vector of a slice submanifold is the velocity of a smooth curve in it; for a smooth curve $y(u)$ in $U$, $(u, t) \mapsto \omega_{y(u)}(t)$ is a variation through broken geodesics, smooth on each strip, whose variation field takes the value $y'(0)_j$ at $t_j$. (ii) At $\gamma = \omega_y$ the first variation in the direction $X$ is $-\sum_j\langle X(t_j), \Delta_{t_j}\gamma'\rangle$. (iii) Let $O \subseteq V^m$ be open with $N^m \cap O \subseteq U$ and $F$ smooth on $V^m$ with $F = E'$ on $N^m \cap O$. Then $dF_y(w) = -2\sum_j\langle w_j, \Delta_{t_j}\omega_y'\rangle$ for tangent $w$, and $y$ is a critical point of $E' = F|(N^m \cap O)$ iff $\omega_y$ is an unbroken geodesic. (iv) Every geodesic $\gamma \in \Omega$ with $E(\gamma) < c$ has its break points $y$ in $U$, $\omega_y = \gamma$ on $[0, 1]$, and $E'(y) = E(\gamma)$.

- `Morse.exists_curve_of_mem_tangentSubspace` — Morse/Chapter10/BrokenVariation.lean, line 61
- `Morse.BrokenSetup.exists_variation_path` — Morse/Chapter10/BrokenVariation.lean, line 98
- `Morse.BrokenSetup.fderiv_eq_jumps` — Morse/Chapter10/BrokenVariation.lean, line 285
- `Morse.BrokenSetup.isCriticalPointM_iff` — Morse/Chapter10/BrokenVariation.lean, line 317
- `Morse.BrokenSetup.eqOn_path_nodeVal_of_isUnbrokenGeodesic` — Morse/Chapter10/Finite.lean, line 115

*What differs.*
- The critical points of $E$ are the unbroken geodesics by Corollary 12.3; $E'$ is read through a smooth ambient extension $F$, as functions on submanifolds are in Part I, and the statement holds for every such $F$ and $O$.
- Hidden: every tangent vector of $B$ at $\gamma$ must be the variation field of a variation through broken geodesics, smooth on the strips, which needs the smooth dependence of a geodesic segment on its end points over the whole segment (V9.9 (iii)); the test is one break point at a time, with the tangent vector $\Delta_{t_j}\gamma'$; and a broken geodesic without velocity jumps is unbroken (Corollary 12.3).

### V10.10. Lemma 15.4 for the subdivision of §16

*hypotheses explicit* · §15 subdivisions differ from §16 ones · Lemma 15.4 proved anew

**Milnor (§16, pp. 91–92).** On pp. 91–92 the tangent space $TB_\gamma$ is identified with the space $T\Omega_\gamma(t_0, \dots, t_k)$ of broken Jacobi fields of §15, and the equality of the indices and nullities "is an immediate consequence of Lemma 15.4".

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: fix Milnor's data and $y \in U$ with $\gamma = \omega_y$ an unbroken geodesic. (i) A Jacobi field along $\gamma$, restricted to a segment and reparametrized affinely, is a Jacobi field along the reparametrized segment. (ii) For every $i$, $t_i$ and $t_{i+1}$ are not conjugate along $\gamma$. (iii) The broken Jacobi fields along $\gamma$ with break points $t_1, \dots, t_m$ take arbitrary tangent values at the $t_j$ and are determined by them. (iv) For every $\omega \in \Omega$, $E'(\omega(t_1), \dots, \omega(t_m)) \le E(\omega)$; hence $E_{**}(W, W) \ge 0$ for $W \in T\Omega_\gamma$ vanishing at the $t_j$, and $> 0$ if moreover $W \ne 0$ vanishes off $[0, 1]$. (v) The fields of $T\Omega_\gamma$ vanishing off $[0, 1]$ are the direct sum of the broken Jacobi fields and of those vanishing at the $t_j$; the index of $E_{**}$ is that of its restriction to the broken Jacobi fields, and so is the nullity.

- `Morse.IsJacobiField.comp_affine` — Morse/Chapter10/BrokenSplitting.lean, line 89
- `Morse.BrokenSetup.energy'_nodeVal_le` — Morse/Chapter10/BrokenSplitting.lean, line 146
- `Morse.BrokenSetup.not_isConjugate_seg` — Morse/Chapter10/BrokenSplitting.lean, line 206
- `Morse.BrokenSetup.brokenNodeMap_bijective` — Morse/Chapter10/BrokenSplitting.lean, line 391
- `Morse.BrokenSetup.energyHessian_nodeZero_pos` — Morse/Chapter10/BrokenSplitting.lean, line 483
- `Morse.BrokenSetup.formIndex_brokenSpace` — Morse/Chapter10/BrokenSplitting.lean, line 580
- `Morse.BrokenSetup.finrank_ker_brokenSpace` — Morse/Chapter10/BrokenSplitting.lean, line 608

*What differs.*
- Lemma 15.4 (V9.19) is proved for a subdivision chosen in §15, which the subdivision of §16 need not be; its proof needs (a) Jacobi fields on each segment with arbitrary, unique end values and (b) $E_{**}$ positive definite on the fields vanishing at the break points. For §16, (a) holds because each segment is the radial geodesic of a vector shorter than a normal radius (V9.11), and (b) because the broken geodesic minimizes the energy among the paths through its break points.
- (iv)–(v) are therefore Lemma 15.4 proved anew for this subdivision; the "immediate consequence" is not immediate.

### V10.11. Theorem 16.2: the index and nullity of $E'$

*hypotheses explicit* · “clearly a broken Jacobi field” proved · compared as quadratic forms, polarized

**Milnor (§16, Theorem 16.2, pp. 90 and 92).** The index (or the nullity) of the Hessian $E'_{**}$ at each critical point $\gamma$ is equal to the index (or the nullity) of $E_{**}$ at $\gamma$. On p. 92: for a variation $\bar\alpha : (-\varepsilon, \varepsilon) \to B$ through broken geodesics the variation field is "clearly a broken Jacobi field" (compare 14.3); then Lemma 15.4.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $O$, $F$ be as in V10.9 (iii) and $y \in N^m \cap O$ with $\gamma = \omega_y$ an unbroken geodesic; let $x$ be the parametrization of a slice chart of $N^m \cap O$ at $y$, $z_0$ the chart point of $y$, and $\Lambda z$ the broken Jacobi field with values $dx_{z_0}(z)$ at the break points, a linear isomorphism onto the broken Jacobi fields. (i) For $G$ of class $C^2$ near $z_0$, the second derivative at $0$ of $u \mapsto G(z_0 + uz)$ is $G_{**}(z, z)$. (ii) $(F \circ x)_{**}(z, z') = E_{**}(\Lambda z, \Lambda z')$. (iii) **Theorem 16.2:** the index of $E'$ at $y$ equals the index of $E_{**}$ at $\gamma$ (V9.13), and the nullity of $E'$ at $y$ equals the nullity of $E_{**}$ at $\gamma$ (V9.6).

- `Morse.hasDerivAt_deriv_line` — Morse/Chapter10/BrokenIndex.lean, line 66
- `Morse.BrokenSetup.chartBrokenEquiv` — Morse/Chapter10/BrokenIndex.lean, line 205
- `Morse.BrokenSetup.hessian_eq_energyHessian` — Morse/Chapter10/BrokenIndex.lean, line 350
- `Morse.BrokenSetup.theorem_16_2_index` — Morse/Chapter10/BrokenIndex.lean, line 378

*What differs.*
- The variation field of a variation through broken geodesics is, on each segment, a Jacobi field along the segment reparametrized to $[0, 1]$ (Lemma 14.3 with V10.10 (i)); that it is the broken Jacobi field with the same values at the break points needs their uniqueness (V10.10 (iii)).
- The Hessians are compared first as quadratic forms, through Remark 13.5 along the variation $F(x(z_0 + uz)) = E(\omega_{x(z_0 + uz)})$, then polarized.

### V10.12. Theorem 16.3 in the finite-dimensional model

*narrower* · $a$ not the energy of a geodesic · cells along arbitrary attaching maps · $B$ is not compact: extend $E'$

**Milnor (§16, Theorem 16.3, and §3.5, p. 90).** Theorem 16.3 is proved in one line: "This follows from 16.2 together with §3.5." Theorem 3.5 is the description of a manifold with compact sublevel sets and no degenerate critical points as a CW-complex with one cell for each critical point.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: (i) if $K \subseteq S'$ are subsets of a finite-dimensional normed space, $K$ compact, and $f$ agrees on $S'$ near each point of $K$ with a function smooth on an open set, then $f$ agrees on $K$ with a function smooth everywhere. (ii) (Theorem 3.5 for a compact sublevel set) for $f = F|N$ with $F$ smooth on $V$ and a level $a_0$ that is not a critical value, with $N^{a_0} = f^{-1}(-\infty, a_0]$ compact and every critical point in it non-degenerate, those critical points are finitely many and $N^{a_0}$ has the homotopy type of an iterated adjunction space with one cell of dimension the index for each. (iii) For Milnor's data and $a < c$, if $E'(y) \ne a$ for every $y \in U$ with $\omega_y$ a geodesic, and $E_{**}$ has nullity $0$ at every such $\omega_y$ with $E'(y) \le a$, then these $y$ are finitely many, and $\{y \in U : E'(y) \le a\}$ has the homotopy type of an iterated adjunction space with one cell of dimension the index of $E_{**}$ at $\omega_y$ for each, attached in order of non-decreasing energy.

- `Morse.exists_contDiff_eq_of_locally` — Morse/Chapter10/SublevelCW.lean, line 54
- `Morse.isFiniteCellComplexType_sublevel_of_isCompact` — Morse/Chapter10/SublevelCW.lean, line 170
- `Morse.BrokenSetup.theorem_16_3` — Morse/Chapter10/Finite.lean, line 132
- `Morse.BrokenSetup.theorem_16_3_count` — Morse/Chapter10/Finite.lean, line 240

*What differs.*
- Theorem 3.5 concerns a function with compact sublevel sets and no degenerate critical point at all, while $B$ is not compact and only the critical points in $B^a$ are assumed non-degenerate. The formal proof extends $E'$ by (i) from the compact set $\{E' \le (a + c)/2\}$ to a smooth function on $V^m$ and applies (ii) there.
- $a$ must not be a critical value of $E'$: Milnor's hypothesis does not exclude a geodesic of energy exactly $a$, and then $B^a$ is a critical sublevel set. The formal statement assumes it.
- The CW-complex is an iterated adjunction space whose attaching maps need not be cellular (V2.11).

### V10.13. Theorem 16.3: the homotopy type of $\Omega^a$

*narrower* · $a$ not the energy of a geodesic · non-conjugacy as nullity $0$ · cells along arbitrary attaching maps

**Milnor (§16, Theorem 16.3, p. 90).** If $M$ is complete and $p, q \in M$ are not conjugate along any geodesic of length $\le \sqrt a$, then $\Omega^a$ has the homotopy type of a finite CW-complex, with one cell of dimension $\lambda$ for each geodesic in $\Omega^a$ along which $E_{**}$ has index $\lambda$. In particular $\Omega^a$ contains only finitely many geodesics.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let Milnor's data be given with $c > a$ (they exist for every $c > 0$ when $N$ is closed in $V$, or connected and complete, V10.3), and suppose that no geodesic $\gamma \in \Omega$ has $E(\gamma) = a$ and that $E_{**}$ has nullity $0$ at every geodesic $\gamma \in \Omega$ with $E(\gamma) \le a$. Then the geodesics in $\Omega^a$ are finitely many, and $\Omega^a$, with the metric $d$, has the homotopy type of an iterated adjunction space with one cell of dimension $\lambda$ for each geodesic in $\Omega^a$ of index $\lambda$, attached in order of non-decreasing energy.

- `Morse.BrokenSetup.theorem_16_3_Omega` — Morse/Chapter10/Omega.lean, line 192
- `Morse.BrokenSetup.theorem_16_3_Omega_count` — Morse/Chapter10/Omega.lean, line 212

*What differs.*
- $a$ must not be the energy of a geodesic (as in V10.12); the case of a critical level is not formalized.
- Non-conjugacy of $p$ and $q$ along the geodesics is stated as nullity $0$, equivalent by Theorem 14.1 (V9.6); completeness enters only through Milnor's data (the compactness of $S$).
- The CW-complex is an iterated adjunction space (V2.11). The proof transports V10.12 along V10.5 and V10.8; every geodesic of $\Omega^a$ is some $\omega_y$ on $[0, 1]$ (V10.9 (iv)).

### V10.14. The Remark on p. 92: a minimum of $E'$

*narrower* · minimal for the energy, not length

**Milnor (§16, Remark, p. 92).** As a consequence of Theorem 16.2, an alternative proof of the existence of a minimal geodesic joining two points $p, q$ of a complete manifold: if $\Omega^a(p, q)$ is non-vacuous, then $B^a$ is compact and non-vacuous, so the continuous function $E' : B^a \to \mathbb R$ takes on its minimum at some point $\gamma \in B^a$, and this $\gamma$ "will be the required minimal geodesic".

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: for Milnor's data, every $\omega \in \Omega$ with $E(\omega) < c$ has its break points $y$ in $U$, with $E'(y) \le E(\omega)$; and if some $\omega_0 \in \Omega$ has $E(\omega_0) < c$, there is $y \in U$ such that $\omega_y$ is an unbroken geodesic and $E(\omega_y) \le E(\omega)$ for every $\omega \in \Omega$.

- `Morse.BrokenSetup.nodeVal_mem_nodes_of_energy_lt` — Morse/Chapter10/Finite.lean, line 287
- `Morse.BrokenSetup.exists_energy_minimizing` — Morse/Chapter10/Finite.lean, line 304

*What differs.*
- Minimality is proved for the energy on all of $\Omega$; that $\omega_y$ is then a minimal geodesic in the sense of V7.24 (shortest) is not stated.
- Hidden: that $\gamma$ minimizes $E$ on all of $\Omega$ needs $E(\omega) \ge E'(\omega(t_1), \dots, \omega(t_m))$ for every $\omega$ (Schwarz's inequality), and that it is a geodesic, that a minimum is a critical point (V10.9).

### V10.15. The full path space $\Omega^*$ and the inclusion $i$

*restated* · $d^*$ measured with the norm of $V$

**Milnor (§17, p. 93).** $\Omega^*$ is the space of all continuous paths $\omega : [0, 1] \to M$ from $p$ to $q$, with the compact-open topology, which can also be described as that induced by the metric $d^*(\omega, \omega') = \max_t\rho(\omega(t), \omega'(t))$. Since $d \ge d^*$, the natural map $i : \Omega \to \Omega^*$ is continuous.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: $\Omega^*(N; p, q)$ is the set of continuous maps $\omega : [0, 1] \to V$ with values in $N$, $\omega(0) = p$ and $\omega(1) = q$, as a subspace of the continuous maps $[0, 1] \to V$ with the uniform distance $d^*(\omega, \eta) = \max_t\|\omega(t) - \eta(t)\|$, whose topology is the compact-open topology. The map $i : \Omega \to \Omega^*$ restricts a path to $[0, 1]$; $d^*(i\omega, i\eta) \le d(\omega, \eta)$, so $i$ is continuous.

- `Morse.pathCSet` — Morse/Chapter10/FullPathSpace.lean, line 180
- `Morse.PathC` — Morse/Chapter10/FullPathSpace.lean, line 184
- `Morse.PathSp.toPathC` — Morse/Chapter10/FullPathSpace.lean, line 195
- `Morse.PathSp.edist_toPathC_le` — Morse/Chapter10/FullPathSpace.lean, line 202
- `Morse.pathIncl` — Morse/Chapter10/FullPathTheorem.lean, line 71

*What differs.*
- $d^*$ is measured with the norm of $V$ rather than with $\rho$; on $N$ the two distances define the same topology (V7.21), so both give the compact-open topology, and $\|x - y\| \le \rho(x, y)$ gives the inequality.

### V10.16. Convergence in $\Omega$ controls the velocities

*not in the book* · $L^2$ convergence of velocities · maps given by smooth formulas

**Milnor (§17, cf. p. 94).** The book has no such statement. It is what the continuity, for $d$, of the maps in the proof of Theorem 17.1 needs, since $d$ involves only the speeds $\frac{ds}{dt}$, not the velocities.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: (i) if $\omega_j \to \omega$ in $(\Omega, d)$, along any filter, then $\int_0^1\|\omega_j' - \omega'\|^2dt \to 0$. (ii) Conversely, if $\omega_j(s) \to \omega(s)$ for every $s \in [0, 1]$ and $\int_0^1\|\omega_j' - \omega'\|^2dt \to 0$, then $\omega_j \to \omega$ in $\Omega$. (iii) If $\Phi$ is of class $C^1$ on an open set containing $F([a, b])$, $F_j \to F$ uniformly on $[a, b]$, and the velocities $F_j'$ are bounded in $L^2$ and converge to $F'$ in $L^2$, then $(\Phi \circ F_j)' \to (\Phi \circ F)'$ in $L^2$.

- `Morse.PathSp.tendsto_integral_norm_deriv_sub_sq` — Morse/Chapter10/FullPathSpace.lean, line 379
- `Morse.PathSp.tendsto_of_tendsto_apply_of_integral` — Morse/Chapter10/FullPathSpace.lean, line 409
- `Morse.tendsto_integral_deriv_comp_sub_sq` — Morse/Chapter10/FullPathOmega.lean, line 62

*What differs.*
- These are the analytic facts that make maps given pointwise by smooth formulas, such as the deformation of V10.18, continuous for $d$. (i) holds although $d$ involves only the speeds: the energies converge (V10.2), and the velocities converge weakly in $L^2$ by integration by parts on the smooth pieces.

### V10.17. Good balls and join systems (Lemma 17.B)

*not in the book* · convex balls, after Whitehead · one smooth join on each whole ball · needs $\exp$ smooth everywhere (V11.1)

**Milnor (§17, p. 93).** In the proof of Theorem 17.1, Milnor takes a continuous $f : M \to [0, \infty)$ with each $f^{-1}([0, r])$ compact, and lets $\varepsilon_1(r) \le \infty$ be the largest number such that any two points of $f^{-1}([0, r])$ at distance less than $\varepsilon_1(r)$ are joined by a unique minimal geodesic which varies differentiably with the end points.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: for $y, z \in V$ the minimal join vector $v(y, z)$ is the unique $v \in T_yN$ with $\exp_y(v) = z$, $\rho(y, z) = \|v\|$ and Corollary 10.8 holding at some scale $\delta > \|v\|$ ($0$ if there is none), and $\sigma_{yz}(s) = \exp_y(s\,v(y, z))$. A *good ball* (V7.10′) is an open $O$ such that, for one $\delta > 0$, any two points of $N \cap O$ are at distance $< \delta$ and joined as in Corollary 10.8 at the scale $\delta$, and $\sigma_{yz}([0, 1]) \subseteq N \cap O$. (i) Small balls of $V$ about points of $N$ are good. (ii) Compact subsets of $N$ have a Lebesgue number for good balls. (iii) In a good ball $\sigma_{yz}$ is the unique minimal geodesic from $y$ to $z$, its sub-arcs are minimal, and $(y, z, s) \mapsto \sigma_{yz}(s)$ is locally the restriction of a smooth map. (iv) Local smooth extensions glue, by a partition of unity, into a *join system*: open good sets, convex for the joins, with one smooth map of $(y, z, s)$ on each and a Lebesgue number for every compact subset of $N$.

- `Morse.IsMinJoin` — Morse/Chapter10/GoodBalls.lean, line 102
- `Morse.minJoin` — Morse/Chapter10/GoodBalls.lean, line 110
- `Morse.minGeo` — Morse/Chapter10/GoodBalls.lean, line 114
- `Morse.IsGoodBall` — Morse/Chapter10/GoodBalls.lean, line 344
- `Morse.IsGoodBall.exists_smooth_minGeo` — Morse/Chapter10/GoodBalls.lean, line 502
- `Morse.exists_smooth_glue` — Morse/Chapter10/GoodJoin.lean, line 42
- `Morse.JoinSystem` — Morse/Chapter10/FullPathDeform.lean, line 91
- `Morse.goodJoin` — Morse/Chapter10/GoodJoin.lean, line 152

*What differs.*
- The modified proof of Theorem 17.1 needs regions that are convex for the short geodesics (J. H. C. Whitehead's convex balls, as in Milnor's remark after Lemma 10.3, V7.10′), one smooth map of $(y, z, s)$ on each whole region, and a uniform scale; Milnor's $\varepsilon_1$ provides none of these.
- Good balls are balls of $V$ intersected with $N$, not metric balls of $\rho$; their convexity is proved with the ambient distance, and the smoothness in $(y, z, s)$ uses the smoothness of $\exp$ on its whole domain (V11.1).

### V10.18. Dyadic broken geodesics as homotopy inverses (Lemma 17.C)

*restated* · the subdivision fixed on each $Y_k$ · points move along joins, not breaks

**Milnor (§17, p. 94).** For $\omega \in \Omega^*$, $h(\omega)$ is the broken geodesic which agrees with $\omega$ at $t = 0, A(\omega), 2A(\omega), \dots, kA(\omega)$ and $1$; "an argument similar to that in §16" shows that $h \circ i$ and $i \circ h$ are homotopic to the identity maps of $\Omega$ and $\Omega^*$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: fix a join system (V10.17). For $k \ge 0$ let $Y_k \subseteq \Omega^*$ be the set of paths each of whose dyadic pieces $\omega([j2^{-k}, (j + 1)2^{-k}])$ lies in a good set, and $X_k = i^{-1}(Y_k) \subseteq \Omega$. (i) The $Y_k$ are open, increasing, and cover $\Omega^*$. (ii) For $\omega \in Y_k$ let $b(\omega)$ be the broken geodesic with vertices $\omega(j2^{-k})$, joined by the joins, and $H(\omega, u)(s)$ the point at time $u$ of the join from $\omega(s)$ to $b(\omega)(s)$. Then $H$ is continuous from $Y_k \times [0, 1]$ to $Y_k$ for $d^*$ and from $X_k \times [0, 1]$ to $X_k$ for $d$, and $b$ is continuous from $(Y_k, d^*)$ to $(X_k, d)$. (iii) Hence $i : X_k \to Y_k$ is a homotopy equivalence with homotopy inverse $b$.

- `Morse.JoinSystem.YSet` — Morse/Chapter10/FullPathDeform.lean, line 285
- `Morse.JoinSystem.isOpen_YSet` — Morse/Chapter10/FullPathDeform.lean, line 310
- `Morse.JoinSystem.broken` — Morse/Chapter10/FullPathDeform.lean, line 115
- `Morse.JoinSystem.interp` — Morse/Chapter10/FullPathDeform.lean, line 120
- `Morse.JoinSystem.continuous_brokenΩ` — Morse/Chapter10/FullPathOmega.lean, line 485
- `Morse.JoinSystem.isHomotopyEquiv_toY` — Morse/Chapter10/FullPathOmega.lean, line 840

*What differs.*
- The dyadic sets $Y_k$ and $X_k$, on each of which the subdivision is fixed, are not in the book; on them the broken geodesic $b$ is continuous for $d$, unlike Milnor's $h$, whose subdivision moves with $\omega$ (V10.19′).
- The deformation moves every point $\omega(s)$ along the join to $b(\omega)(s)$, instead of moving a break point along the path as Milnor's $r_u$ does; it stays where the joins are defined by convexity (V10.17), and its continuity for $d$ needs V10.16. $b \circ i \simeq \mathrm{id}$ holds up to paths at distance $0$.

### V10.19. Theorem 17.1: $\Omega$ and $\Omega^*$ are homotopy equivalent

*as in the book* · the theorem is true; the proof is not · proved by Theorem A on telescopes · no completeness

**Milnor (§17, Theorem 17.1, p. 93).** Let $M$ be a Riemannian manifold, not necessarily complete, and $p, q \in M$. The natural map $i : \Omega \to \Omega^*$ is a homotopy equivalence between $\Omega$, with the metric $d$, and the space $\Omega^*$ of continuous paths. The proof (pp. 93–94) builds a continuous $A : \Omega^* \to (0, 1]$ and the broken geodesic $h(\omega)$ through $\omega(0), \omega(A), \dots, \omega(kA), \omega(1)$, asserts "Clearly $h$ is continuous", and shows $h \circ i \simeq \mathrm{id}$, $i \circ h \simeq \mathrm{id}$ by "an argument similar to that in §16".

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: (i) if $Y$ is paracompact and Hausdorff, $B_0 \subseteq B_1 \subseteq \cdots$ are subsets of $Y$ such that every point lies in the interior of some $B_n$, and $g : X \to Y$ is continuous, then $X$ is the homotopy direct limit of the sets $g^{-1}(B_n)$. (ii) For every join system, $i : \Omega(N; p, q) \to \Omega^*(N; p, q)$ is a homotopy equivalence. (iii) **Theorem 17.1:** for every slice submanifold $N$ of $V$, complete or not, and all $p, q$, the inclusion $i : \Omega \to \Omega^*$, with Milnor's metric $d$ on $\Omega$ and the compact-open topology on $\Omega^*$, is a homotopy equivalence.

- `Morse.isHomotopyDirectLimit_preimage` — Morse/Chapter10/FullPathSpace.lean, line 139
- `Morse.theoremA_general` — Morse/Appendix/MonotoneUnion.lean, line 533
- `Morse.JoinSystem.isHomotopyEquiv_toPathC` — Morse/Chapter10/FullPathTheorem.lean, line 80
- `Morse.theorem_17_1` — Morse/Chapter10/FullPathTheorem.lean, line 110

*What differs.*
- The statement is Milnor's, and it holds without completeness, as in the book. **One step of the printed proof does not hold as we read it**: "Clearly $h$ is continuous" fails for the metric $d$ (V10.19′), so what is verified is the theorem itself, by the exposition's modified proof.
- The modified proof: the open sets $Y_k$ exhaust the metric, hence paracompact, space $\Omega^*$, which is therefore the homotopy direct limit of the $Y_k$ (Example 1 of the Appendix), and $\Omega$ is that of the $X_k = i^{-1}(Y_k)$ by (i); $i$ carries each $X_k$ into $Y_k$ by a homotopy equivalence (V10.18); Theorem A with no closedness hypothesis (VA.15) concludes.
- $\Omega$ is not Hausdorff for $d$, so Example 1 is applied to $\Omega^*$ and pulled back by $i$; Theorem A is needed for open, not closed, pieces.

### V10.19′. Milnor’s map $h$ is not continuous: a step in the proof of Theorem 17.1

*not in the book* · a step of the book that does not hold as we read it · counterexample on $M = \mathbb R$ · Theorem 17.1 itself is true (V10.19)

**Milnor (§17, proof of Theorem 17.1, p. 94).** In the proof of Theorem 17.1, with $\varepsilon(\omega) = \varepsilon_2(\max_tf(\omega(t)))$ and $F(\omega, \alpha) = (\alpha - 1)\varepsilon(\omega) + \max_{|t - t'| \le \alpha}\rho(\omega(t), \omega(t'))$, the zero $\alpha = 2A(\omega)$ of $F(\omega, \cdot)$ defines a continuous $A : \Omega^* \to (0, 1]$. Then $h(\omega) \in \Omega$ is the path which agrees with $\omega$ at $t = 0, A(\omega), 2A(\omega), \dots, kA(\omega)$, $k$ the largest integer $\le 1/A(\omega)$, and at $t = 1$, and is a geodesic on each intermediate interval. Milnor writes: "Clearly $h$ is continuous."

**Proved in Lean.** Take $M = \mathbb R$, $p = q = 0$ (so $\rho(x, y) = |x - y|$), Milnor's $f(x) = |x|$ and the admissible choice $\varepsilon_2 \equiv 1$; $2A(\omega)$ is the unique zero of $F(\omega, \cdot)$ in $[0, 1]$, as Milnor claims, and $h(\omega)$ is the piecewise affine interpolation of $\omega$ at $0, A, \dots, kA, 1$, a map $h : \Omega^* \to \Omega$. Let $\omega_\lambda(t) = \lambda((1 - t)^{1/3} - (1 - t))$ and $\lambda_* = \sqrt3/2$. Then $\omega_\lambda \to \omega_{\lambda_*}$ uniformly as $\lambda \to \lambda_*$, while $E(h(\omega_\lambda)) \to \infty$ as $\lambda \downarrow \lambda_*$ ($E(h(\omega_{\lambda_*})) \le 1$). Since $\sqrt E$ is $1$-Lipschitz for $d$, $d(h(\omega_\lambda), h(\omega_{\lambda_*})) \to \infty$: **$h$ is not continuous at $\omega_{\lambda_*}$**, hence not continuous.

- `Morse.MilnorH.milnorF` — Morse/Chapter10/MilnorH.lean, line 126
- `Morse.MilnorH.twoA_spec` — Morse/Chapter10/MilnorH.lean, line 247
- `Morse.MilnorH.hMap` — Morse/Chapter10/MilnorH.lean, line 502
- `Morse.MilnorH.tendsto_omegaFam` — Morse/Chapter10/MilnorH.lean, line 614
- `Morse.MilnorH.tendsto_energy_hPath` — Morse/Chapter10/MilnorH.lean, line 760
- `Morse.MilnorH.tendsto_edist_hMap` — Morse/Chapter10/MilnorH.lean, line 775
- `Morse.milnor_h_not_continuous` — Morse/Chapter10/MilnorH.lean, line 796
- `Morse.milnor_h_not_continuous'` — Morse/Chapter10/MilnorH.lean, line 807

*What differs.*
- This row records a step that does not hold as we read it, not a difference of formulation: Milnor's "Clearly $h$ is continuous" (p. 94) is false for the metric $d$ of $\Omega$, the topology in which Theorem 17.1 is stated; $h$ is continuous only for $d^*$. The counterexample is machine-checked for an admissible instance of Milnor's own choices: $f(x) = |x|$ and $\varepsilon_2 \equiv 1$, legitimate because on $\mathbb R$ any two points are joined by a unique minimal geodesic depending smoothly on them, so $\varepsilon_1 \equiv \infty$. Other constants $\varepsilon_2 \equiv c$ only rescale the family (a remark, not formalized).
- The failure is in the $L^2$ term of $d$. When $1/A(\omega)$ crosses an integer, $h(\omega)$ acquires a new last segment of duration $\delta \to 0$ and length $\ell \to 0$, whose energy $\ell^2/\delta$ need not tend to $0$: here $\ell = \lambda(\delta^{1/3} - \delta)$ gives energy at least $\frac{27}{64}\delta^{-1/3}$. Milnor's $A$ is not at fault: $A(\omega_\lambda) = (1 - \lambda c_0)/2$, with $c_0 = 2\sqrt3/9$ the maximum of $(1 - t)^{1/3} - (1 - t)$ on $[0, 1]$, depends continuously on $\lambda$, and $k = 3$ for $\lambda_* \le \lambda \le \frac54\lambda_*$; what moves is the last break point $kA = 3A$, which leaves $1$.
- Only this step fails: the theorem is proved by a different route (V10.17–V10.19), with subdivisions kept fixed on open sets and Theorem A of the Appendix. (Also, $A$ takes its values in $(0, \frac12]$, not $(0, 1]$.)

### V10.20. Relative cell complexes and the tower

*restated* · a tower up to homotopy suffices · no nested subdivisions · a relative Theorem 3.5

**Milnor (§17, p. 95).** In the proof of Theorem 17.3: by 16.2 together with 3.3 and 3.7, each $\Omega^{a_i}$ has the homotopy type of $\Omega^{a_{i-1}}$ with finitely many cells attached; "just as in the proof of 3.5", one constructs CW-complexes $K_0 \subset K_1 \subset \cdots$ with cells of the required description and homotopy equivalences $\Omega^{a_i} \to K_i$, each extending the previous one, forming a commutative diagram.

**Proved in Lean.** (i) A map $\iota : A \to X$ is, *up to homotopy, the inclusion of $A$ with cells $(\lambda_1, \dots, \lambda_k)$ attached* if there are a space $K$ obtained from $A$ by attaching a $\lambda_1$-cell, then a $\lambda_2$-cell, and so on, with $j : A \to K$ the inclusion, and a homotopy equivalence $e : X \to K$ with $e \circ \iota \simeq j$. (ii) (Lemma 3.7, relative and iterated) such attachments transport along homotopy equivalences, and the notion is invariant under homotopy-commutative squares of homotopy equivalences. (iii) (relative Theorem 3.5) for $f = F|N$ on a slice submanifold, $F$ smooth, and levels $b \le a_0$, neither critical, with $N^{a_0}$ compact and the critical points in it non-degenerate, $N^b \to N^{a_0}$ is, up to homotopy, $N^b$ with one cell of dimension the index for each critical point in $f^{-1}(b, a_0)$, in order of value. (iv) (the tower) if $E : X \to \mathbb R$ is continuous, $a_n \to \infty$, $X^{a_0}$ has the homotopy type of a finite cell complex with cells $\mathrm{cells}_0$, and each $X^{a_n} \to X^{a_{n+1}}$ is, up to homotopy, the inclusion with cells $\mathrm{cells}_{n+1}$ attached, then $X$ has the homotopy type of the countable cell complex with cells $\mathrm{cells}_0, \mathrm{cells}_1, \dots$ (VA.18).

- `Morse.IsRelCellComplexType` — Morse/Chapter10/RelativeCells.lean, line 100
- `Morse.IsRelCellAttachment.transport` — Morse/Chapter10/RelativeCells.lean, line 83
- `Morse.IsRelCellComplexType.of_square` — Morse/Chapter10/RelativeCells.lean, line 140
- `Morse.isRelCellComplexType_sublevel_of_isCompact` — Morse/Chapter10/RelativeCells.lean, line 344
- `Morse.isCountableCellComplexType_of_relSublevel` — Morse/Chapter10/RelativeCells.lean, line 573

*What differs.*
- "Each extending the previous one" is not available: Lemma 3.7 extends a homotopy equivalence over the new cells, but $\Omega^{a_{i+1}}$ is only homotopy equivalent to $\Omega^{a_i}$ with cells attached, by retractions that move $\Omega^{a_i}$, so the extension holds only up to homotopy (strict compatibility would need nested subdivisions).
- The Appendix's comparison of telescopes needs only homotopy-commutative squares (VA.16, VA.19), so the tower is built up to homotopy. The step also needs a relative form of Theorem 3.5, for pairs of sublevel sets, which the book does not state.

### V10.21. The step from $\Omega^a$ to $\Omega^b$

*restated* · any finite number of critical values · its own $B$ for each step

**Milnor (§17, p. 95).** Each $\Omega^{a_i}$ has the homotopy type of $\Omega^{a_{i-1}}$ with one $\lambda$-cell attached for each geodesic of index $\lambda$ with energy in $(a_{i-1}, a_i)$, by 16.2 together with 3.3 and 3.7.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: (i) for Milnor's data and levels $a \le b < c$, if neither $a$ nor $b$ is $E'(y)$ for a $y \in U$ with $\omega_y$ a geodesic, and every such $\omega_y$ with $E'(y) \le b$ has nullity $0$, then $\Omega^a \to \Omega^b$ is, up to homotopy, $\Omega^a$ with one cell of dimension the index of $E_{**}$ at $\omega_y$ for each such $y$ with $a < E'(y) < b$, attached in order of energy; the homotopy equivalences $\Omega^t \simeq \{y \in U : E'(y) \le t\}$ are all given by $\omega \mapsto$ the break points of $r_1(\omega)$, so they commute with the inclusions. (ii) Under nullity $0$, such geodesics are finitely many; if $N$ is closed in $V$, $p, q \in N$, and every geodesic in $\Omega$ has nullity $0$, the energies at most $b$ of the geodesics in $\Omega$ are finitely many, for every $b$. (iii) The index of a geodesic, as a natural number, equals the index of $E_{**}$ at it (finite by Theorem 15.1).

- `Morse.PathSp.energyC` — Morse/Chapter10/FundamentalTheorem.lean, line 92
- `Morse.BrokenSetup.isRelCellComplexType_Omega` — Morse/Chapter10/FundamentalTheorem.lean, line 240
- `Morse.BrokenSetup.finite_geodesics` — Morse/Chapter10/FundamentalTheorem.lean, line 261
- `Morse.finite_geodesicEnergies` — Morse/Chapter10/FundamentalTheorem.lean, line 446
- `Morse.geodesicIndex` — Morse/Chapter10/FundamentalTheorem.lean, line 331
- `Morse.geodesicIndex_eq` — Morse/Chapter10/FundamentalTheorem.lean, line 335

*What differs.*
- Each step uses its own manifold of broken geodesics, with an energy bound $c > b$, and allows any finite number of critical values between $a$ and $b$.
- Hidden: the choice of levels needs the critical values of $E$ to be discrete, which follows from Theorem 16.3 (finitely many geodesics below each level); and the homotopy equivalences with the models must commute with the inclusions.

### V10.22. Theorem 17.3: the fundamental theorem of Morse theory

*narrower* · $N$ closed in $V$, for completeness · for $\Omega$, not $\Omega^*$ · countable cell complex: a telescope

**Milnor (§17, Theorem 17.3, p. 95).** If $M$ is complete and $p, q \in M$ are not conjugate along any geodesic, then $\Omega(M; p, q)$ (or $\Omega^*(M; p, q)$) has the homotopy type of a countable CW-complex which contains one cell of dimension $\lambda$ for each geodesic from $p$ to $q$ of index $\lambda$. Proof: levels $a_0 < a_1 < \cdots$, not critical values, with "precisely one" critical value in each interval and $\Omega^{a_0}$ empty; the tower of CW-complexes; the direct limit map $\Omega \to K$ induces isomorphisms of homotopy groups, hence is a homotopy equivalence by Whitehead's theorem, $\Omega$ having the homotopy type of a CW-complex by 17.2. A different proof, not using 17.1, is referred to the Appendix.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric, closed in $V$, and $p, q \in N$: (i) suppose every geodesic in $\Omega$ has nullity $0$, and let $a_0 \le a_1 \le \cdots$ be levels tending to $\infty$, $a_0 < 0$, none of which is the energy of a geodesic. Then there are finite lists $\mathrm{geo}_0 = \emptyset, \mathrm{geo}_1, \dots$ of geodesics, $\mathrm{geo}_{n+1}$ containing exactly one representative of each geodesic with energy in $(a_n, a_{n+1})$, ordered by energy, such that $\Omega$, with Milnor's metric, has the homotopy type of the countable cell complex (VA.18) with one cell of dimension the index of $E_{**}$ at $\gamma$ for each entry $\gamma$. (ii) **Theorem 17.3:** if every geodesic in $\Omega$ has nullity $0$, there are finite lists of geodesics from $p$ to $q$ such that every geodesic agrees on $[0, 1]$ with exactly one entry of exactly one list, energies increase strictly from list to list and weakly within a list, and $\Omega(N; p, q)$ has the homotopy type of the countable cell complex with one cell of dimension $\lambda$ for each entry of index $\lambda$. (iii) The same holds if $q$ is not conjugate to $p$ along any geodesic (V11.4).

- `Morse.theorem_17_3_of_levels` — Morse/Chapter10/FundamentalTheorem.lean, line 351
- `Morse.theorem_17_3` — Morse/Chapter10/FundamentalTheorem.lean, line 467
- `Morse.theorem_17_3_nonconj` — Morse/Chapter10/FundamentalTheorem.lean, line 549

*What differs.*
- Completeness is replaced by the closedness of $N$ in $V$, which implies it (V7.30) and is used only through the compactness of the balls $S$ (V10.3).
- The statement is for $\Omega$; for $\Omega^*$ it would follow by composing with Theorem 17.1 (V10.19), but is not stated. The countable CW-complex is the mapping telescope of a tower of cell attachments along arbitrary maps (VA.18).
- The proof is Milnor's second route, Theorem A of the Appendix (VA.19), through V10.20 and V10.21; neither Whitehead's theorem nor Corollary 17.2 is used. "Precisely one" critical value per interval is impossible when there are finitely many geodesics, and "at most one" is not needed: several are attached in order of energy. The levels must tend to infinity.
- Geodesics are counted by their values on $[0, 1]$, as paths are maps on $\mathbb R$.

### V10.23. The geodesics from $p$ to $q$ on $S^n$, and their indices

*restated* · “$k$ occurrences” as $k\pi < L_k < (k+1)\pi$ · the list of geodesics shown complete

**Milnor (§17, pp. 95–96; §14, Example 2).** For $q \ne p, p'$ on $S^n$, $p'$ the antipode of $p$, the geodesics from $p$ to $q$ are $\gamma_0$, the short great circle arc, $\gamma_1$, the long arc $pq'p'q$, $\gamma_2 = pqp'q'pq$, and so on. The index $\lambda(\gamma_k)$ is $k(n - 1)$: $k$ is the number of times $p$ or $p'$ occurs in the interior of $\gamma_k$, and each of these points is conjugate to $p$ with multiplicity $n - 1$ (Example 2 of §14).

**Proved in Lean.** On the unit sphere $S^n \subseteq \mathbb R^{n+1}$, $n \ge 1$: (i) for unit $p \perp u$ and $L \in \mathbb R$, $c(t) = \cos(Lt)\,p + \sin(Lt)\,u$ is a geodesic on $\mathbb R$ of energy $L^2$ on $[0, 1]$, and every geodesic $\gamma \in \Omega(S^n; p, q)$ agrees on $[0, 1]$ with such a $c$, $L \ge 0$. (ii) The conjugate parameters along $c$ are as in V9.7″. (iii) Let $q \ne \pm p$, $\theta \in (0, \pi)$ the angle between $p$ and $q$, $u \perp p$ the unit vector with $q = \cos\theta\,p + \sin\theta\,u$; let $\gamma_{2j}$ be the great circle along $u$ with $L_{2j} = \theta + 2\pi j$, and $\gamma_{2j+1}$ the one along $-u$ with $L_{2j+1} = 2\pi(j + 1) - \theta$. These are geodesics in $\Omega(S^n; p, q)$ with $E(\gamma_k) = L_k^2$ and $k\pi < L_k < (k + 1)\pi$; every geodesic in $\Omega(S^n; p, q)$ agrees on $[0, 1]$ with some $\gamma_k$; $q$ is not conjugate to $p$ along any geodesic; and the index of $E_{**}$ at $\gamma_k$, and at every geodesic that agrees with it on $[0, 1]$, is $k(n - 1)$.

- `Morse.sphLen` — Morse/Chapter10/SphereGeodesics.lean, line 561
- `Morse.sphGeod` — Morse/Chapter10/SphereGeodesics.lean, line 567
- `Morse.mul_pi_lt_sphLen` — Morse/Chapter10/SphereGeodesics.lean, line 670
- `Morse.energy_sphGeod` — Morse/Chapter10/SphereGeodesics.lean, line 696
- `Morse.exists_eqOn_sphGeod` — Morse/Chapter10/SphereGeodesics.lean, line 704
- `Morse.notMem_conjLocus_sph` — Morse/Chapter10/SphereGeodesics.lean, line 858
- `Morse.formIndex_sphGeod` — Morse/Chapter10/SphereGeodesics.lean, line 836
- `Morse.formIndex_eq_of_eqOn_sphGeod` — Morse/Chapter10/SphereGeodesics.lean, line 847

*What differs.*
- Milnor's count of the interior occurrences of $p$ and $p'$ is the inequality $k\pi < L_k < (k + 1)\pi$; the index comes from Theorem 15.1.
- Hidden: that $q \ne p, p'$ makes $p$, $q$ non-conjugate along every geodesic needs the conjugate points along every great circle through $p$ and the list of all geodesics from $p$ to $q$; that every geodesic is a great circle uses uniqueness after extending the segment past $t = 0$ (V9.9). Of the rephrasing of non-conjugacy as $q \ne p, p'$, the direction Theorem 17.3 needs is proved.
- The Jacobi fields are checked directly with $R(x, y)z = \langle x, z\rangle y - \langle y, z\rangle x$, not by rotations and Lemma 14.3.

### V10.24. Corollary 17.4: the cells of the path space of $S^n$

*narrower* · paths with $q \ne \pm p$; loops: V10.30 · $n \ge 2$

**Milnor (§17, Corollary 17.4, p. 96).** The loop space $\Omega(S^n)$ has the homotopy type of a CW-complex with one cell each in the dimensions $0, n - 1, 2(n - 1), 3(n - 1), \dots$. It is derived from Theorem 17.3 and the example of the geodesics from $p$ to a point $q \ne p, p'$.

**Proved in Lean.** (i) Let $N \subseteq V$ be closed in $V$, $p, q \in N$, every geodesic in $\Omega$ of nullity $0$, and suppose the geodesics in $\Omega$ are, up to their values off $[0, 1]$, a sequence $g_0, g_1, \dots$ with strictly increasing energies tending to $\infty$, every geodesic agreeing with $g_k$ on $[0, 1]$ having index $d_k$. Then $\Omega$ has the homotopy type of the countable cell complex with one cell of dimension $d_k$ at stage $k + 1$. (ii) **Corollary 17.4:** for $n \ge 2$ and $p, q \in S^n$ with $q \ne p$ and $q \ne -p$, the path space $\Omega(S^n; p, q)$, with Milnor's metric, has the homotopy type of the countable cell complex with one cell in each of the dimensions $0, n - 1, 2(n - 1), \dots$, attached in this order.

- `Morse.oneCellEach` — Morse/Chapter10/PathHomology.lean, line 308
- `Morse.omega_cells_of_unique` — Morse/Chapter10/PathHomology.lean, line 316
- `Morse.strictMono_energy_sphGeod` — Morse/Chapter10/SpherePaths.lean, line 63
- `Morse.corollary_17_4` — Morse/Chapter10/SpherePaths.lean, line 83

*What differs.*
- The path space $\Omega(S^n; p, q)$ with $q \ne \pm p$, which is what Milnor's argument gives, replaces the loop space: in the loop space $p$ is conjugate to itself along every great circle, and passing to loops needs that $\Omega^*(S^n; p, q)$ does not depend on $q$ up to homotopy (the exposition's Lemma 17.D) together with Theorem 17.1; that change of end point is V10.28, and the loop space is V10.30.
- $n \ge 2$; the case $n = 1$, with every cell a point, is not stated. The cell complex is a countable cell complex in the sense of VA.18.

### V10.25. The homology of a path space read off from its geodesics

*restated* · filtration by energy, not cellular homology · coefficients in a field

**Milnor (§17, p. 96).** For $n > 2$, the homology of $\Omega(S^n)$ "can be computed immediately" from the cell structure of Corollary 17.4.

**Proved in Lean.** Homology is singular homology with coefficients in a field $\Bbbk$, and $b_i = \dim_\Bbbk H_i$. (i) Let $A_0 \subseteq A_1 \subseteq \cdots$ be subsets of a space $X$ such that every compact subset of $X$ lies in some $A_k$. If $H_j(A_k, A_{k_0}) = 0$ for all $k \ge k_0$, then $H_j(X, A_{k_0}) = 0$; and if the steps $H_*(A_{k+1}, A_k)$ vanish in degrees $i$ and $i + 1$ for all $k \ge k_0$, then $b_i(X) = \dim H_i(A_{k_0})$. (ii) For Milnor's data and levels $a \le b < c$, neither the energy of a geodesic, with at most one energy of a geodesic in $(a, b)$ and every geodesic of energy at most $b$ of nullity $0$, $H_j(\Omega^b, \Omega^a)$ is finite-dimensional, of dimension the number of geodesics with energy in $(a, b)$ and index $j$. (iii) In the situation of V10.24 (i) with $d_k = kr$, $r \ge 2$, $b_i(\Omega) = 1$ when $r$ divides $i$ and $0$ otherwise.

- `Morse.Homology.bettiNumber_eq_of_steps` — Morse/Chapter10/SublevelHomology.lean, line 330
- `Morse.Homology.sublevel_step_of_isCompact` — Morse/Chapter10/SublevelHomology.lean, line 465
- `Morse.BrokenSetup.finrank_subsetHomology_Omega` — Morse/Chapter10/PathHomology.lean, line 79
- `Morse.windowLevels` — Morse/Chapter10/PathHomology.lean, line 224
- `Morse.bettiNumber_omega_of_unique` — Morse/Chapter10/PathHomology.lean, line 456

*What differs.*
- Reading the homology off the cells is cellular homology, which needs cellular attaching maps; here the homology is computed from the filtration of $\Omega$ by the $\Omega^a$, with the lacunary principle on the finite stages (Corollary 5.4), rather than from a cellular chain complex.
- That the homology of $\Omega$ is the limit of that of the $\Omega^a$ needs every compact subset of $\Omega$ to have bounded energy, true for $d$ since $E$ is continuous, false for $d^*$; the vanishing is needed in degrees $i$ and $i + 1$. Coefficients are in a field.

### V10.26. The homology of the path space of $S^n$

*narrower* · paths with $q \ne \pm p$, not loops · field coefficients, not $\mathbb Z$

**Milnor (§17, p. 96).** For $n > 2$ the homology of $\Omega(S^n)$ "can be computed immediately" from Corollary 17.4 (the cells lie in the dimensions $k(n - 1)$, no two of them consecutive, so every cell contributes a free generator); in particular $\Omega(S^n)$ has non-trivial homology in infinitely many dimensions, which is what Corollary 17.5 uses.

**Proved in Lean.** For $n \ge 3$, $p, q \in S^n$ with $q \ne p$ and $q \ne -p$, and every field $\Bbbk$, $\dim_\Bbbk H_i(\Omega(S^n; p, q); \Bbbk)$ is $1$ if $n - 1$ divides $i$ and $0$ otherwise.

- `Morse.bettiNumber_sphere_paths` — Morse/Chapter10/SpherePaths.lean, line 96

*What differs.*
- The path space with $q \ne \pm p$ replaces the loop space, as in V10.24, and coefficients are in a field, not the integers.
- $n > 2$ is needed, so that no two cells have consecutive dimensions; for $n = 2$ there is a cell in every dimension and the lacunary principle does not apply.

### V10.27. Corollary 17.5 needs completeness

*not in the book* · punctured space: a counterexample · completeness is a missing hypothesis

**Milnor (§17, Corollary 17.5, p. 96).** Corollary 17.5: if $M$ has the homotopy type of $S^n$, $n > 2$, then any two non-conjugate points of $M$ are joined by infinitely many geodesics. Completeness is not among its hypotheses, although the proof rests on Theorem 17.3, which assumes it; the Remark that follows (p. 97) assumes it.

**Proved in Lean.** (i) An open subset of $V$ is a slice submanifold of codimension $0$, every tangent space being $V$. (ii) If every tangent space of $N$ is $V$, the induced metric is flat; every geodesic in $\Omega(N; p, q)$ agrees on $[0, 1]$ with the segment $t \mapsto p + t(q - p)$; no two parameters are conjugate along a curve in $N$, and every geodesic has index $0$ and nullity $0$; and if the segment from $p$ to $q$ lies in $N$, it is the unique geodesic in $\Omega(N; p, q)$ up to values off $[0, 1]$. (iii) For $n \ge 1$, $N = \mathbb R^{n+1} \setminus \{0\}$ with the induced metric is homotopy equivalent to $S^n$ and path-connected; it is neither closed in $\mathbb R^{n+1}$ nor geodesically complete; no point of $N$ is conjugate to another along any geodesic; and there are $p \ne q$ in $N$ joined by exactly one geodesic.

- `Morse.isSliceSubmanifold_of_isOpen` — Morse/Chapter10/Incomplete.lean, line 128
- `Morse.unique_geodesic_of_top` — Morse/Chapter10/Incomplete.lean, line 373
- `Morse.puncturedSub` — Morse/Chapter10/Incomplete.lean, line 416
- `Morse.not_isGeodesicallyComplete_puncturedSub` — Morse/Chapter10/Incomplete.lean, line 474
- `Morse.puncturedHomotopyEquiv` — Morse/Chapter10/Incomplete.lean, line 525
- `Morse.remark_17_5_completeness` — Morse/Chapter10/Incomplete.lean, line 567

*What differs.*
- For $n \ge 3$, $\mathbb R^{n+1} \setminus \{0\}$ satisfies the hypotheses of Corollary 17.5 as printed and not its conclusion, so the hypothesis that $M$ is complete, which the book omits, cannot be dropped.
- Corollary 17.5 itself, for complete $M$, is not formalized; nor is the fact that $\Omega(N; p, q)$ is not contractible here, which would contradict Theorem 17.3 without completeness for every $n \ge 1$. What is proved is that $N$ satisfies every hypothesis of the formal Theorem 17.3 except closedness in the ambient space.

### V10.28. Moving the end point

*not in the book* · $\Omega(N; p, q) \simeq \Omega(N; p, q')$ · non-conjugate points are dense

**Milnor (§17, p. 96; §19, p. 106).** The loop space of $S^n$ is treated through the paths from $p$ to a point $q \neq p, p'$, and Theorem 19.6 is stated for all $p, q$ but proved for non-conjugate ones; that the end point may be moved is not said.

**Proved in Lean.** Let $N$ be a slice submanifold of $V$ and $p, q \in N$. (i) Two points of $N$ at finite Riemannian distance are joined by a path in $N$, and $q$ is joined by a path in $N$ to a point $q' \in N$ which is not conjugate to $p$ along any geodesic. (ii) A path in $N$ from $q$ to $q'$ gives a homotopy equivalence $\Omega(N; p, q) \simeq \Omega(N; p, q')$ of path spaces with Milnor's metric. (iii) Homotopy equivalent spaces have isomorphic homology over a field, hence the same Betti numbers.

- `Morse.joined_of_riemDist_lt_top` — Morse/Chapter10/CWType.lean, line 64
- `Morse.exists_joined_notMem_conjLocus` — Morse/Chapter10/CWType.lean, line 88
- `Morse.pathSpHomotopyEquiv` — Morse/Chapter10/CWType.lean, line 110
- `Morse.Homology.spaceHomologyEquivOfHomotopyEquiv` — Morse/Chapter10/CWType.lean, line 141
- `Morse.Homology.bettiNumber_eq_of_homotopyEquiv` — Morse/Chapter10/CWType.lean, line 151

*What differs.*
- Every $q$ is joined in $N$ to a point $q'$ not conjugate to $p$ (V11.6), and a path from $q$ to $q'$ gives a homotopy equivalence of the path spaces with Milnor's metric, through Theorem 17.1 (V10.19) and composition of paths.

### V10.29. Corollary 17.2

*restated* · without Milnor's theorem of 1959 · $N$ closed in $V$ · a countable cell complex

**Milnor (§17, Corollary 17.2, p. 95).** "It is known that the space $\Omega^*$ has the homotopy type of a CW-complex" (Milnor, 1959). Therefore $\Omega$ has the homotopy type of a CW-complex.

**Proved in Lean.** Let $N$ be closed in $V$ and $p, q \in N$. Then $\Omega(N; p, q)$, with Milnor's metric, has the homotopy type of a countable cell complex (VA.18), and so does the space $\Omega^*(N; p, q)$ of continuous paths with the compact-open topology.

- `Morse.corollary_17_2` — Morse/Chapter10/CWType.lean, line 122
- `Morse.corollary_17_2_pathC` — Morse/Chapter10/CWType.lean, line 130

*What differs.*
- The end point is moved to a non-conjugate one (V10.28) and Theorem 17.3 (V10.22) gives the complex; so $N$ must be complete, which Milnor's corollary does not assume, but the complex is countable and explicit. The same holds for $\Omega^*$.

### V10.30. Corollary 17.4 for the loop space

*narrower* · $n \ge 2$ · the end point is moved · homology over fields, $n \ge 3$

**Milnor (§17, Corollary 17.4, p. 96).** The loop space $\Omega(S^n)$ has the homotopy type of a CW-complex with one cell each in the dimensions $0, n - 1, 2(n - 1), 3(n - 1), \dots$.

**Proved in Lean.** Let $n \ge 2$ and $p \in S^n$. The loop space $\Omega(S^n; p, p)$ is homotopy equivalent to $\Omega(S^n; p, q)$ for some $q \neq \pm p$, and it has the homotopy type of the countable cell complex with one cell in each of the dimensions $0, n - 1, 2(n - 1), 3(n - 1), \dots$, attached in this order. For $n \ge 3$ and every field $\mathbb k$, $\dim H_i(\Omega(S^n; p, p); \mathbb k)$ is $1$ if $n - 1$ divides $i$ and $0$ otherwise.

- `Morse.exists_loop_homotopyEquiv_sph` — Morse/Chapter10/CWType.lean, line 159
- `Morse.corollary_17_4_loop` — Morse/Chapter10/CWType.lean, line 184
- `Morse.bettiNumber_sphere_loops` — Morse/Chapter10/CWType.lean, line 192

*What differs.*
- $p$ is conjugate to itself along every great circle, so Theorem 17.3 does not apply to loops: $\Omega(S^n; p, p) \simeq \Omega(S^n; p, q)$ for some $q \neq \pm p$ (V10.28), and V10.24 applies. For $n \ge 3$ the Betti numbers over a field are $1$ in the degrees divisible by $n - 1$.

## Chapter 11

*Milnor §§18–19, pp. 98–108: non-conjugate points, topology and curvature*

### V11.1. $\exp$ is smooth on its whole domain

*stronger* · the whole domain, not near the zero section · no completeness

**Milnor (§18, p. 98).** A critical point is defined for a smooth map between manifolds of the same dimension and applied to $\exp = \exp_p : TM_p \to M$, so $\exp_p$ is treated as smooth on all of $TM_p$. $M$ is assumed complete so that $\exp$ is everywhere defined, "although this assumption could easily be eliminated".

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: (i) let $E$ be a real normed space, $U_0 \subseteq E$ open, $u_0 \in U_0$, and $c, w$ of class $C^\infty$ on $U_0$ with $c(u) \in N$, $w(u) \in T_{c(u)}N$. If $t \mapsto \exp_{c(u_0)}(t\,w(u_0))$ is a geodesic on $(-\delta, B + \delta)$, $B \ge 0$, there are $\varepsilon, \eta > 0$ such that every $t \mapsto \exp_{c(u)}(t\,w(u))$ with $\|u - u_0\| < \varepsilon$ is a geodesic on $(-\eta, B + \eta)$ and $(u, t) \mapsto \exp_{c(u)}(t\,w(u))$ is $C^\infty$ there. (ii) Every point of $N$ has an open neighbourhood $U$ in $V$ with a $C^\infty$ retraction $U \to N$. (iii) The domain of $\exp$ lies in $TN$, contains $(y, w)$ as soon as $t \mapsto \exp_y(tw)$ is a geodesic on an open interval containing $[0, 1]$, and equals $TN \cap O'$ for an open $O' \subseteq V \times V$; near each of its points $\exp$ is the restriction of a $C^\infty$ map on an open set of $V \times V$, and $(q, v) \mapsto \exp_q(v)$ is $C^\infty$ on it as a map on the manifold $TN$.

- `Morse.RaysGoodE` — Morse/Chapter11/ExpSmooth.lean, line 117
- `Morse.raysGoodE_of_isGeodesicOn` — Morse/Chapter11/ExpSmooth.lean, line 280
- `Morse.exists_retraction` — Morse/Chapter11/ExpSmooth.lean, line 328
- `Morse.mem_expDom_of_isGeodesicOn` — Morse/Chapter11/ExpSmooth.lean, line 354
- `Morse.exists_contDiffOn_exp` — Morse/Chapter11/ExpSmooth.lean, line 365
- `Morse.exists_isOpen_expDom` — Morse/Chapter11/ExpSmooth.lean, line 406
- `Morse.contMDiffOn_exp_expDom` — Morse/Chapter11/ExpSmooth.lean, line 418

*What differs.*
- §10 gives the smoothness of $\exp$ only near the zero section (Lemma 10.2, V7.8), and Chapter 7 only its continuity on the domain (V7.23); Milnor uses smoothness everywhere from §18 on without proof. It is the smooth dependence of geodesics on their initial data over a compact time interval.
- The domain of $\exp$ is open in $TN$ and $\exp$ is smooth on it, with no completeness, as Milnor says could "easily" be arranged.

### V11.2. $\exp_q$, its derivative, and critical points of $\exp_q$

*restated* · $T(TM_p)_v$ identified with $T_qN$ · domain open and star-shaped

**Milnor (§18, p. 98).** A smooth map $f : N \to M$ between manifolds of the same dimension is *critical* at $x$ if $f_* : TN_x \to TM_{f(x)}$ is not one-to-one. This is applied to $\exp = \exp_p : TM_p \to M$, with $X \in T(TM_p)_v$ the tangent space at $v$ of $TM_p$ "considered as a manifold"; $\gamma_v$ is the geodesic $t \mapsto \exp(tv)$ from $p$ to $\exp v$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: for $q \in N$ let $\mathcal D_q \subseteq T_qN$ be the set of $v$ with $(q, v)$ in the domain of $\exp$. It contains $0$, contains $tv$ for $v \in \mathcal D_q$ and $0 \le t \le 1$, is open in $T_qN$, and $\exp_q$ is $C^\infty$ on it as a map from the vector space $T_qN$ to $V$. $d(\exp_q)_v : T_qN \to V$ is the derivative of this map at $v$, and $\exp_q$ is *critical* at $v$ if $d(\exp_q)_v$ is not one-to-one. For $v \in \mathcal D_q$, $\gamma_v(t) = \exp_q(tv)$ is a geodesic on an open interval containing $[0, 1]$ and a smooth curve in $N$ on $[0, 1]$. If $N$ is geodesically complete, $\mathcal D_q = T_qN$.

- `Morse.expDomAt` — Morse/Chapter11/ExpSmooth.lean, line 441
- `Morse.isOpen_expDomAt` — Morse/Chapter11/ExpSmooth.lean, line 467
- `Morse.contDiffOn_expAt` — Morse/Chapter11/ExpSmooth.lean, line 473
- `Morse.dExpAt` — Morse/Chapter11/ExpSmooth.lean, line 521
- `Morse.isGeodesicOn_ray` — Morse/Chapter11/ExpSmooth.lean, line 481
- `Morse.isSmoothCurveIn_ray` — Morse/Chapter11/ExpSmooth.lean, line 488
- `Morse.expDomAt_eq_univ` — Morse/Chapter11/NonConjugate.lean, line 231

*What differs.*
- $T(TM_p)_v$ is identified with $T_qN$, as Milnor does on p. 99 (paths $v(u)$ in $TM_p$ with $\frac{dv}{du}(0) = X$), and $d(\exp_q)_v$ takes values in $V$; whether it is one-to-one does not depend on the target.
- Without completeness, the domain of $\exp_q$ is shown open and star-shaped about $0$ (V11.1), which is what the statements of §18 need.

### V11.3. Theorem 18.1: conjugate points are critical values of $\exp$

*stronger* · multiplicity $= \dim\ker d(\exp_q)_v$ · no completeness · needs $\exp$ smooth (V11.1)

**Milnor (§18, Theorem 18.1, p. 98).** The point $q = \exp v$ is conjugate to $p$ along the geodesic $\gamma_v$ from $p$ to $\exp v$ if and only if the mapping $\exp$ is critical at $v$. Proof (pp. 98–99): if $\exp_*X = 0$ with $X \ne 0$, the variation $\alpha(u, t) = \exp tv(u)$ through geodesics, for a path $v(u)$ with $v(0) = v$ and $\frac{dv}{du}(0) = X$, has a variation field $W$ with $W(0) = 0$, $W(1) = \exp_*X = 0$ and $\frac{DW}{dt}(0) \ne 0$; conversely, if $\exp_*$ is non-singular at $v$, independent $X_1, \dots, X_n$ give $n$ Jacobi fields vanishing at $p$ with independent values at $\exp v$, and "clearly" no non-trivial Jacobi field vanishes at both ends.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $q \in N$ and $v \in \mathcal D_q$ (V11.2). For $X \in T_qN$ let $W_X(t) = t\,d(\exp_q)_{tv}(X)$ on $[0, 1]$, constant off $[0, 1]$. (i) $X \mapsto W_X$ is linear and each $W_X$ is a Jacobi field along $\gamma_v$ with $W_X(0) = 0$, $\frac{DW_X}{dt}(0) = X$ and $W_X(1) = d(\exp_q)_v(X)$. (ii) $X \mapsto W_X$ is injective, and every Jacobi field along $\gamma_v$ vanishing at $0$ is a $W_X$. (iii) The Jacobi fields vanishing at $0$ and $1$ are the $W_X$ with $X \in \ker d(\exp_q)_v$, so the multiplicity of the conjugate parameters $0$ and $1$ is $\dim\ker d(\exp_q)_v$. (iv) **Theorem 18.1:** $0$ and $1$ are conjugate along $\gamma_v$ iff $\exp_q$ is critical at $v$.

- `Morse.expJacobi` — Morse/Chapter11/ExpSmooth.lean, line 500
- `Morse.isJacobiField_expJacobi` — Morse/Chapter11/ExpSmooth.lean, line 539
- `Morse.expJacobi_injective` — Morse/Chapter11/ExpSmooth.lean, line 625
- `Morse.conjSpace_eq_map_ker` — Morse/Chapter11/ExpSmooth.lean, line 658
- `Morse.theorem_18_1_multiplicity` — Morse/Chapter11/ExpSmooth.lean, line 677
- `Morse.theorem_18_1` — Morse/Chapter11/ExpSmooth.lean, line 686

*What differs.*
- The multiplicity of the conjugate point equals the dimension of the kernel of $d(\exp_q)_v$, which Milnor does not state (the exposition's form of 18.1); no completeness is assumed.
- Hidden: the smoothness of $\exp_q$ on its domain (V11.1); $\frac{DW}{dt}(0) = \frac{D}{du}v(u)$ needs the symmetry lemma 8.7 along the constant curve $u \mapsto p$. The formal proof uses the straight line $v(u) = v + uX$ and $d(\exp_q)_0 = \mathrm{id}$ instead, and the uniqueness of Jacobi fields from initial data in place of the dimension count.
- "$\exp v$ conjugate to $p$ along $\gamma_v$" is the conjugacy of the parameters $0$ and $1$ (V9.4).

### V11.4. The conjugate locus is the set of critical values of $\exp_p$

*not in the book* · every geodesic from $p$ is radial · the conjugate locus named

**Milnor (§18, p. 99).** The book has no such statement. Milnor says that Corollary 18.2 "follows immediately from 18.1 together with Sard's theorem (6.1)", which needs every point conjugate to $p$ along some geodesic to be a critical value of $\exp_p$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: for $p \in V$, the conjugate locus $C(p)$ is the set of $q$ for which there is a geodesic $\gamma$ from $p$ (a smooth curve in $N$ on $[0, 1]$ that is a geodesic on $(0, 1)$, $\gamma(0) = p$) with $\gamma(1) = q$ along which $0$ and $1$ are conjugate. Let $p \in N$. For every geodesic $\gamma$ from $p$, its initial velocity $v$ lies in $\mathcal D_p$, $\exp_p(v) = \gamma(1)$, and $0$ and $1$ are conjugate along $\gamma$ iff $\exp_p$ is critical at $v$. Hence $C(p) = \exp_p(\{v \in \mathcal D_p : \exp_p \text{ critical at } v\})$, the set of critical values of $\exp_p$; if $N$ is geodesically complete, $\mathcal D_p = T_pN$.

- `Morse.conjLocus` — Morse/Chapter11/NonConjugate.lean, line 76
- `Morse.IsConjugate.congr_curve_iff` — Morse/Chapter11/NonConjugate.lean, line 89
- `Morse.theorem_18_1_of_geodesic` — Morse/Chapter11/NonConjugate.lean, line 97
- `Morse.conjLocus_eq` — Morse/Chapter11/NonConjugate.lean, line 118
- `Morse.conjLocus_eq_of_complete` — Morse/Chapter11/NonConjugate.lean, line 236

*What differs.*
- The conjugate locus is named and identified as a set. "Follows immediately" hides that every geodesic from $p$ is a radial geodesic $t \mapsto \exp_p(tv)$ (uniqueness of geodesics, and the extension of a segment past its end points, V9.9), and, without completeness, that the domain of $\exp_p$ is open (V11.1).

### V11.5. Corollary 18.2: almost every point is non-conjugate

*restated* · measure zero read in every chart · Sard from the companion project

**Milnor (§18, Corollary 18.2, p. 99).** If $p \in M$, then for almost all $q \in M$, $p$ is not conjugate to $q$ along any geodesic. It follows "immediately from 18.1 together with Sard's theorem (6.1)".

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $p \in N$, let $\sigma$ be a slice chart of $N$, and $\mu$ a Haar measure on the model space $Z$. Then the image of $C(p) \cap \operatorname{dom}\sigma$ under the chart is $\mu$-null: $C(p)$ has measure zero in $N$.

- `Morse.corollary_18_2` — Morse/Chapter11/NonConjugate.lean, line 140
- `Milnor.sard` — ../Milnor/Chapter3/Sard.lean, line 112

*What differs.*
- "Measure zero" in a manifold is not defined in the book (Theorem 6.1 uses the phrase for a manifold target); here it is read in every slice chart, for every Haar measure on the model space.
- The proof applies the companion project's Sard theorem to $z \mapsto \sigma(\exp_p(e(z)))$, $e : Z \to T_pN$ a linear isomorphism: a derivative that is not one-to-one stays so after composing, and a linear map of $Z$ to itself is onto iff it is one-to-one.

### V11.6. Non-conjugate points exist, are dense, and are non-degenerate

*stronger* · dense, not only existing · nullity $0$, as 16.3 and 17.3 use

**Milnor (§18, p. 98).** Theorem 17.3 describes $\Omega(M; p, q)$ when $p$ and $q$ are not conjugate along any geodesic, and "this section will justify this result by showing that such non-conjugate points always exist".

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: for $p \in N$, the points of $N$ outside $C(p)$ are dense in $N$. If $q \notin C(p)$, then at every geodesic $\gamma \in \Omega(N; p, q)$ the nullity of $E_{**}$ is $0$.

- `Morse.dense_compl_conjLocus` — Morse/Chapter11/NonConjugate.lean, line 200
- `Morse.hessNullity_eq_zero_of_notMem_conjLocus` — Morse/Chapter11/NonConjugate.lean, line 221

*What differs.*
- Milnor promises existence; density is proved, and the non-degeneracy that Theorems 16.3 and 17.3 actually use (nullity $0$, by Theorem 14.1).
- From measure zero to existence needs that a null set has empty interior, a non-empty open subset of $Z$ having positive Haar measure.

### V11.7. Lemma 19.1: no conjugate points in non-positive curvature

*restated* · any two parameters $a < b$ · the identity along any smooth curve

**Milnor (§19, Lemma 19.1, p. 100).** Suppose that the sectional curvature of $M$ is everywhere $\le 0$, i.e. $\langle R(A, B)A, B\rangle \le 0$ for every pair of vectors $A, B$ in $TM_p$ and every $p$. Then no two points of $M$ are conjugate along any geodesic. Proof: $\langle\frac{D^2J}{dt^2}, J\rangle = -\langle R(V, J)V, J\rangle \ge 0$, so $\langle\frac{DJ}{dt}, J\rangle$ is monotonically increasing, strictly so unless $\frac{DJ}{dt} = 0$; if $J(0) = J(t_0) = 0$ it vanishes on $[0, t_0]$, so $J(0) = \frac{DJ}{dt}(0) = 0$ and $J \equiv 0$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: $N$ has *non-positive curvature* if $\langle R(A, B)A, B\rangle \le 0$ for all $A, B \in T_qN$ and all $q \in N$; equivalently, every sectional curvature of $N$ is $\le 0$. (i) For a smooth curve $\gamma$ in $N$ on $[0, 1]$ and a Jacobi field $J$ along it, $\frac{d}{dt}\langle\frac{DJ}{dt}, J\rangle = \|\frac{DJ}{dt}\|^2 - \langle R(V, J)V, J\rangle$ on $(0, 1)$. (ii) If $N$ has non-positive curvature and $\gamma$ is a smooth curve in $N$ on $[0, 1]$ which is a geodesic on $(0, 1)$, a Jacobi field along $\gamma$ vanishing at two parameters $a < b$ of $[0, 1]$ vanishes on $[0, 1]$: no two parameters are conjugate along $\gamma$.

- `Morse.NonposCurvature` — Morse/Chapter11/Curvature.lean, line 144
- `Morse.nonposCurvature_iff_sectionalCurvature` — Morse/Chapter11/Curvature.lean, line 150
- `Morse.hasDerivAt_inner_covAlong` — Morse/Chapter11/Curvature.lean, line 95
- `Morse.IsJacobiField.eqOn_zero_of_nonpos` — Morse/Chapter11/Curvature.lean, line 179
- `Morse.lemma_19_1` — Morse/Chapter11/Curvature.lean, line 234

*What differs.*
- Any two parameters $a < b$ in $[0, 1]$, where Milnor treats $0$ and $t_0$; conjugate parameters for points (V9.4). The identity (i) holds along any smooth curve.
- $\frac{DJ}{dt}(0) = 0$ comes from $\frac{DJ}{dt} = 0$ on $(0, t_0)$ by continuity, a step the book leaves implicit.

### V11.8. Non-positive curvature: index $0$, and $\exp_p$ nowhere critical

*stronger* · $E_{**}$ positive definite · no completeness, no simple connectivity

**Milnor (§19, proof of Theorem 19.2, pp. 102–103).** In the proof of Theorem 19.2: since there are no conjugate points, "it follows from the index theorem that every geodesic from $p$ to $q$ has index $\lambda = 0$" (p. 102); and "it follows from 18.1 that $\exp_p$ is non-critical everywhere" (p. 103).

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $N$ have non-positive curvature. At every geodesic $\gamma \in \Omega(N; p, q)$ the index and the nullity of $E_{**}$ are $0$, and $E_{**}(W, W) > 0$ for every $W \in T\Omega_\gamma$ that does not vanish identically on $[0, 1]$. For $p \in N$, $\exp_p$ is critical at no point of $\mathcal D_p$.

- `Morse.formIndex_eq_zero_of_nonpos` — Morse/Chapter11/Curvature.lean, line 246
- `Morse.energyHessian_pos_of_nonpos` — Morse/Chapter11/Curvature.lean, line 267
- `Morse.injective_dExpAt_of_nonpos` — Morse/Chapter11/Curvature.lean, line 300

*What differs.*
- Positive definiteness of $E_{**}$ is not in the book; neither completeness nor simple connectivity is assumed.
- The proof is the index theorem (V9.24) with Lemma 19.1; a $W$ with $E_{**}(W, W) = 0$ is a null vector of the semi-definite form, hence a Jacobi field vanishing at $0$ and $1$ (V9.5), hence $0$; the last statement is Theorem 18.1 with Lemma 19.1.

### V11.9. The Ricci tensor and Milnor’s Assertion

*as in the book*

**Milnor (§19, p. 104).** Definition: the Ricci tensor at a point $p$ of a Riemannian manifold is the bilinear pairing $K : TM_p \times TM_p \to \mathbb R$, $K(U_1, U_2)$ the trace of the linear transformation $W \mapsto R(U_1, W)U_2$ of $TM_p$; "it follows easily from 9.3 that $K$ is symmetric". Assertion: for an orthonormal basis $U_1, \dots, U_n$ of $TM_p$, $K(U_n, U_n)$ is the sum of the sectional curvatures $\langle R(U_n, U_i)U_n, U_i\rangle$, $i = 1, \dots, n - 1$, because the $n$-th diagonal term of the matrix $(\langle R(U_n, U_i)U_n, U_j\rangle)$ is zero.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: for $q \in N$ and $U_1, U_2 \in T_qN$, $K(U_1, U_2)$ is the trace of $W \mapsto R(U_1, W)U_2$ on $T_qN$. For an orthonormal basis $E_1, \dots, E_n$ of $T_qN$, $K(U_1, U_2) = \sum_i\langle R(U_1, E_i)U_2, E_i\rangle$, and $K(U_1, U_2) = K(U_2, U_1)$. **Assertion:** for an orthonormal basis $U_1, \dots, U_n$, $K(U_n, U_n) = \sum_{i \ne n}\langle R(U_n, U_i)U_n, U_i\rangle$.

- `Morse.ricci` — Morse/Chapter11/Myers.lean, line 98
- `Morse.ricci_eq_sum` — Morse/Chapter11/Myers.lean, line 103
- `Morse.ricci_comm` — Morse/Chapter11/Myers.lean, line 113
- `Morse.curvOp_self` — Morse/Chapter11/Myers.lean, line 123
- `Morse.ricci_eq_sum_erase` — Morse/Chapter11/Myers.lean, line 130

### V11.10. A geodesic as a smooth curve with a parallel frame

*hypotheses explicit* · frames need $\gamma$ extended past its ends · $V$ parallel, frame orthonormal everywhere

**Milnor (§19, proof of Theorem 19.4, p. 104).** In the proof of Theorem 19.4: for a geodesic $\gamma : [0, 1] \to M$ of length $L$, choose parallel vector fields $P_1, \dots, P_n$ along $\gamma$ which are orthonormal at one point, and hence everywhere, with $P_n$ pointing along $\gamma$, so that $V = \frac{d\gamma}{dt} = LP_n$ and $\frac{DP_i}{dt} = 0$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $\gamma \in \Omega(N; p, q)$ be a geodesic of length $L$. (i) There are a $C^\infty$ curve $c : \mathbb R \to N$ equal to $\gamma$ on $[0, 1]$ and a $C^\infty$ tangent field $V$ along $c$, equal to $\gamma'$ on $(0, 1)$, with $\|V\| = L$ and $L^{-1}V$ parallel along $c$. (ii) If $L > 0$, there are such $c$ and $V$ and $n - 1$ parallel unit fields $P_1, \dots, P_{n-1}$ along $c$ such that, for every $r$ for which $K(U, U) \ge (n - 1)/r^2$ for every unit tangent vector $U$ at every point, $n = \dim N$, $\sum_{i=1}^{n-1}\langle R(V, P_i)V, P_i\rangle \ge L^2(n - 1)/r^2$ at every $t$.

- `Morse.exists_smooth_clamp` — Morse/Chapter11/Myers.lean, line 141
- `Morse.exists_smooth_extension` — Morse/Chapter11/Myers.lean, line 266
- `Morse.exists_parallel_frame` — Morse/Chapter11/Myers.lean, line 328

*What differs.*
- Parallel fields along $\gamma : [0, 1] \to M$ (Lemma 8.2) are formalized for curves on $\mathbb R$, so $\gamma$ is first extended past its ends (the radial geodesic of $\gamma'(0)$, composed with a smooth clamp).
- $V = LP_n$ needs the constant speed $L$ and that $V$ itself is parallel; the frame must be orthonormal at every $t$, parallel translation being an isometry, for the Assertion (V11.9) to apply.

### V11.11. The test fields $\sin(\pi t)P_i(t)$

*restated* · $\cos^2$ in place of $\sin^2$, same integral · $n \ge 2$

**Milnor (§19, proof of Theorem 19.4, p. 105).** With $W_i(t) = (\sin\pi t)P_i(t)$, $\frac12E_{**}(W_i, W_i) = -\int_0^1\langle W_i, \frac{D^2W_i}{dt^2} + R(V, W_i)V\rangle\,dt = \int_0^1(\sin\pi t)^2(\pi^2 - L^2\langle R(P_n, P_i)P_n, P_i\rangle)\,dt$. Summing for $i = 1, \dots, n - 1$ gives $\int_0^1(\sin\pi t)^2((n - 1)\pi^2 - L^2K(P_n, P_n))\,dt$, which is negative if $K(P_n, P_n) \ge (n - 1)/r^2$ and $L > \pi r$; hence $E_{**}(W_i, W_i) < 0$ for some $i$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: (i) let $\gamma \in \Omega(N; p, q)$ agree on $[0, 1]$ with a $C^\infty$ curve $c : \mathbb R \to N$, $P$ a parallel unit field along $c$, and $V$ a field equal to $\gamma'$ on $(0, 1)$. Then $W(t) = \sin(\pi t)P(t)$ lies in $T\Omega_\gamma$ and $\frac12E_{**}(W, W) = \int_0^1(\pi^2\cos^2(\pi t) - \sin^2(\pi t)\langle R(V, P)V, P\rangle)\,dt$. (ii) If $n \ge 2$, $r > 0$, $K(U, U) \ge (n - 1)/r^2$ for every unit tangent vector $U$ at every point, $n = \dim N$, and $\gamma \in \Omega(N; p, q)$ is a geodesic of length $> \pi r$, then $E_{**}(X, X) < 0$ for some $X \in T\Omega_\gamma$.

- `Morse.integral_sin_sq_pi_mul` — Morse/Chapter11/Myers.lean, line 188
- `Morse.integral_cos_sq_pi_mul` — Morse/Chapter11/Myers.lean, line 197
- `Morse.energyHessian_sin_parallel` — Morse/Chapter11/Myers.lean, line 212
- `Morse.exists_energyHessian_neg` — Morse/Chapter11/Myers.lean, line 410

*What differs.*
- The integral form of $E_{**}$ (V8.15) gives $\pi^2\cos^2(\pi t)$ where Milnor's form gives $\pi^2\sin^2(\pi t)$; both integrate to $\pi^2/2$.
- $n \ge 2$ is needed for a field $P_i$ perpendicular to $\gamma$. The $\frac12$, $\sum$ and $\int$ missing from the scan's display of the sum are dropped glyphs, not misprints.

### V11.12. Theorem 19.4 (Myers)

*hypotheses explicit* · $n \ge 2$, which the book omits · does not hold as printed for $n = 1$

**Milnor (§19, Theorem 19.4, p. 104).** (Myers.) Suppose that the Ricci curvature $K$ satisfies $K(U, U) \ge (n - 1)/r^2$ for every unit vector $U$ at every point of $M$, where $r$ is a positive constant. Then every geodesic on $M$ of length $> \pi r$ contains conjugate points, and hence is not minimal. On p. 105: $E_{**}(W_i, W_i) < 0$ makes the index of $\gamma$ positive, the index theorem gives conjugate points, and a variation with variation field $W_i$ decreases the energy.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $n = \dim N \ge 2$, $r > 0$, and $K(U, U) \ge (n - 1)/r^2$ for every unit tangent vector $U$ at every point, $n = \dim N$. Then every geodesic $\gamma \in \Omega(N; p, q)$ of length $> \pi r$ has a parameter $t \in (0, 1)$ conjugate to $0$, and is not minimal: some path of $\Omega(N; p, q)$ is shorter (V8.6).

- `Morse.RicciLowerBound` — Morse/Chapter11/Myers.lean, line 258
- `Morse.theorem_19_4` — Morse/Chapter11/Myers.lean, line 486

*What differs.*
- $n \ge 2$ is a hypothesis the book leaves silent, and it is needed: for $n = 1$ the Ricci tensor vanishes, Milnor's hypothesis holds for every $r$, and a segment of a line longer than $\pi r$ has no conjugate points and is minimal.
- "Contains conjugate points" is "has a parameter in $(0, 1)$ conjugate to $0$"; minimality is among the paths of $\Omega(N; p, q)$. The proof is Milnor's: the index is positive (V11.11), the index theorem (V9.24) gives the conjugate parameter, and Lemma 13.6 (V8.18) excludes minimality.

### V11.13. Corollary 19.5: compactness and diameter

*hypotheses explicit* · connectedness, for minimal geodesics · $n \ge 2$ forced by $(n - 1)/r^2 > 0$

**Milnor (§19, Corollary 19.5, p. 105).** If $M$ is complete, and $K(U, U) \ge (n - 1)/r^2 > 0$ for all unit vectors $U$, then $M$ is compact, with diameter $\le \pi r$. Proof: a minimal geodesic from $p$ to $q$ has length $\le \pi r$, and closed bounded sets in a complete manifold are compact.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: a minimal geodesic on $[0, 1]$ (V7.24) is a geodesic of $\Omega(N; \gamma(0), \gamma(1))$ minimal in the sense of V8.6. Let $N$ be (pre)connected, $(N, \rho)$ complete, $r > 0$ with $(n - 1)/r^2 > 0$, and $K(U, U) \ge (n - 1)/r^2$ for every unit tangent vector $U$ at every point, $n = \dim N$. Then $\rho(p, q) \le \pi r$ for all $p, q \in N$, and $N$ is compact.

- `Morse.IsMinimalGeodesic.isMinimalPath` — Morse/Chapter11/Myers.lean, line 520
- `Morse.corollary_19_5` — Morse/Chapter11/Myers.lean, line 533

*What differs.*
- Connectedness (Milnor's standing assumption) is needed for minimal geodesics to exist; $n \ge 2$ is forced by $(n - 1)/r^2 > 0$. The proof is Hopf–Rinow (V7.29) with V11.12.

### V11.14. Example: the sphere

*narrower* · only the unit sphere · “best possible” not proved

**Milnor (§19, Example, p. 105).** If $M$ is a sphere of radius $r$ then every sectional curvature is equal to $1/r^2$, hence $K(U, U)$ takes the constant value $(n - 1)/r^2$. It follows from 19.4 that every geodesic of length $> \pi r$ contains conjugate points: "a best possible result".

**Proved in Lean.** On the unit sphere $S^n \subseteq \mathbb R^{n+1}$ with the induced metric, $K(U, U) = (n - 1)\|U\|^2$, so the hypothesis of Theorem 19.4 holds with $r = 1$. For $n \ge 2$, every geodesic of $\Omega(S^n; p, q)$ of length $> \pi$ has a parameter in $(0, 1)$ conjugate to $0$ and is not minimal, and $\rho(p, q) \le \pi$ for all $p, q \in S^n$.

- `Morse.ricci_sph` — Morse/Chapter11/Myers.lean, line 564
- `Morse.ricciLowerBound_sph` — Morse/Chapter11/Myers.lean, line 586
- `Morse.sphere_myers` — Morse/Chapter11/Myers.lean, line 595

*What differs.*
- Only the unit sphere, not a sphere of radius $r$; and "best possible" (that a geodesic of length $\pi$ has no interior conjugate point) is not stated here, although it follows from the computation of the conjugate points along great circles in Chapter 10 (V9.7″).

### V11.15. Test fields on disjoint pieces

*hypotheses explicit* · “a similar argument” carried out · any piece $[a, b]$

**Milnor (§19, proof of Theorem 19.6, p. 106).** For a geodesic of length $> k\pi r$, "a similar argument" gives, for each $i = 1, \dots, k$, a vector field $X_i$ along $\gamma$ which vanishes outside the interval $(\frac{i-1}k, \frac ik)$ and has $E_{**}(X_i, X_i) < 0$; "clearly" $E_{**}(X_i, X_j) = 0$ for $i \ne j$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $\gamma$, $c$, $V$ be as in V11.11 (i), $V$ smooth and tangent along $c$, $P$ parallel along $c$, and $0 \le a < b \le 1$. The field $X$ equal to $\sin(\kappa(t - a))P(t)$, $\kappa = \pi/(b - a)$, on $[a, b]$ and to $0$ elsewhere lies in $T\Omega_\gamma$, and if $\|P\| = 1$, $\frac12E_{**}(X, X) = \int_a^b(\kappa^2\cos^2(\kappa(t - a)) - \sin^2(\kappa(t - a))\langle R(V, P)V, P\rangle)\,dt$. Two such fields on $[a, b]$ and $[a', b']$ with $b \le a'$ have $E_{**}(X, X') = 0$. If $n \ge 2$, $r > 0$, the $P_i$ are as in V11.10 (ii) and $L(\gamma)(b - a) > \pi r$, the field built on $[a, b]$ from some $P_i$ has $E_{**}(X, X) < 0$.

- `Morse.sinBump` — Morse/Chapter11/LongGeodesics.lean, line 126
- `Morse.sinBump_mem_pathTangent` — Morse/Chapter11/LongGeodesics.lean, line 172
- `Morse.energyHessian_sinBump` — Morse/Chapter11/LongGeodesics.lean, line 211
- `Morse.energyHessian_sinBump_disjoint` — Morse/Chapter11/LongGeodesics.lean, line 256
- `Morse.exists_sinBump_neg` — Morse/Chapter11/LongGeodesics.lean, line 295

*What differs.*
- The construction of the $X_i$, the computation of V11.11 on a piece of length $1/k$, is carried out for any piece $[a, b]$; the orthogonality holds because the integrand of the integral form vanishes off $[a, b]$, and for two pieces off their common end point.

### V11.16. Theorem 19.6: the index estimate

*hypotheses explicit* · continuity of $K(U, U)$ proved · $n \ge 2$ · the $X_i$ independent: disjoint supports

**Milnor (§19, proof of Theorem 19.6, p. 106).** Since the space of all unit vectors $U$ on the compact $M$ is compact, the continuous function $K(U, U) > 0$ takes on a minimum, which can be denoted by $(n - 1)/r^2 > 0$. Then every geodesic $\gamma \in \Omega(M; p, q)$ of length $> \pi r$ has index $\lambda \ge 1$; more generally one of length $> k\pi r$ has index $\lambda \ge k$, since $X_1, \dots, X_k$ span a $k$-dimensional subspace of $T\Omega_\gamma$ on which $E_{**}$ is negative definite.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: (i) if $N$ is compact, $n = \dim N \ge 2$, and the Ricci tensor is positive definite at every point, there is $r > 0$ with $K(U, U) \ge (n - 1)/r^2$ for every unit tangent vector $U$ at every point, $n = \dim N$. (ii) Let $n \ge 2$, $r > 0$ and $K(U, U) \ge (n - 1)/r^2$ for every unit tangent vector $U$ at every point, $n = \dim N$; let $\gamma \in \Omega(N; p, q)$ be a geodesic and $k \ge 0$ an integer. If $L(\gamma) > k\pi r$, the index of $E_{**}$ at $\gamma$ is at least $k$, and the parameters $t \in (0, 1)$ conjugate to $0$, counted with multiplicity, number at least $k$. Equivalently, a geodesic of index $< k$ has length $\le k\pi r$.

- `Morse.continuous_trace_ricciMap` — Morse/Chapter11/PositiveRicci.lean, line 109
- `Morse.exists_ricciLowerBound` — Morse/Chapter11/PositiveRicci.lean, line 159
- `Morse.theorem_19_6_index` — Morse/Chapter11/LongGeodesics.lean, line 378
- `Morse.pathLength_le_of_formIndex_lt` — Morse/Chapter11/LongGeodesics.lean, line 456
- `Morse.le_finsum_conjMultiplicity_of_ricci` — Morse/Chapter11/LongGeodesics.lean, line 465

*What differs.*
- The continuity of $K(U, U)$ on the unit tangent bundle is used without proof: the Ricci tensor is a trace over the moving subspace $T_qN$; it equals the trace over the fixed space $V$ of $W \mapsto R(U, P_qW)U$, which is continuous in $(q, U)$. The compactness of the unit tangent vectors (a closed subset of $N \times S$, $S$ the unit sphere of $V$) is also made explicit.
- $n \ge 2$ is needed, as in Theorem 19.4; and the $X_i$ are linearly independent because they are non-zero with disjoint supports.
- The verified Chapter 11 took the bound $(n - 1)/r^2$ as a hypothesis; the first step of Milnor's proof, (i), is now proved (`Morse/Chapter11/PositiveRicci.lean`).

### V11.17. Theorem 19.2 (Cartan–Hadamard)

*as in the book* · proved through the covering $\exp_p$ · the argument runs in reverse order

**Milnor (§19, Theorem 19.2, p. 102).** (Cartan.) Suppose that $M$ is a simply connected, complete Riemannian manifold, and that the sectional curvature $\langle R(A, B)A, B\rangle$ is everywhere $\le 0$. Then any two points of $M$ are joined by a unique geodesic. Furthermore, $M$ is diffeomorphic to the Euclidean space $\mathbb R^n$. Proof (pp. 102–103): by the index theorem and 17.3, $\Omega(M; p, q)$ has the homotopy type of a $0$-dimensional complex with one vertex for each geodesic; it is connected since $M$ is simply connected, so there is precisely one geodesic from $p$ to $q$. Therefore $\exp_p : TM_p \to M$ is one-one and onto; by 18.1 it is non-critical, hence locally a diffeomorphism, hence a global diffeomorphism.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $N$ be geodesically complete (for instance closed in $V$), simply connected (as a topological space, with the topology of $V$), and of non-positive curvature. Then any two points $p, q \in N$ are joined by a geodesic $\gamma \in \Omega(N; p, q)$, and every geodesic in $\Omega(N; p, q)$ agrees with $\gamma$ on $[0, 1]$; and $N$ is diffeomorphic to $\mathbb R^n$, $n = \dim N$, for its manifold structure as a slice submanifold. More precisely, $\exp_p : T_pN \to N$ is itself a diffeomorphism: it is a covering map (V11.19), injective because $N$ is simply connected, and onto by the Hopf–Rinow theorem.

- `Morse.isGeodesicallyComplete_of_isClosed` — Morse/Chapter11/CartanHadamard.lean, line 190
- `Morse.injective_expToN_of_simplyConnected` — Morse/Chapter11/CartanHadamard.lean, line 133
- `Morse.surjective_expToN` — Morse/Chapter11/CartanHadamard.lean, line 154
- `Morse.expDiffeomorph` — Morse/Chapter11/CartanHadamard.lean, line 196
- `Morse.theorem_19_2` — Morse/Chapter11/CartanHadamard.lean, line 214

*What differs.*
- The statement is Milnor's. The order of the argument is reversed: Milnor deduces the uniqueness of geodesics from the connectedness of the path space and then the injectivity of $\exp_p$; here the covering $\exp_p$ (V11.19) gives injectivity directly (the image of a segment of $T_pN$ with both ends over one point is a null-homotopic loop, whose lift is closed), and uniqueness follows. Both routes rest on Lemma 19.1.
- Milnor's route silently uses Theorem 17.1, to identify the components of $\Omega(M; p, q)$ with the homotopy classes of paths; the covering route needs instead the completeness of the metric pulled back to $T_pN$, his "it is clear" of p. 103.
- "Hence a global diffeomorphism" is the fact that a bijective local diffeomorphism is a diffeomorphism (Mathlib); that $\exp_p$ is onto is the Hopf–Rinow theorem, which needs $M$ connected, part of "simply connected".

### V11.18. The path space in non-positive curvature

*stronger* · simply connected or not · a discrete space, through the covering · contractible when simply connected

**Milnor (§19, proof of Theorem 19.2, p. 102).** In the proof of Theorem 19.2: since every geodesic from $p$ to $q$ has index $0$, Theorem 17.3 asserts that the path space $\Omega(M; p, q)$ has the homotopy type of a $0$-dimensional CW-complex, with one vertex for each geodesic. The hypothesis that $M$ is simply connected implies that $\Omega(M; p, q)$ is connected, and a connected $0$-dimensional CW-complex must consist of a single point.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric, of non-positive curvature: (i) if $N$ is closed in $V$ and $p, q \in N$, $\Omega(N; p, q)$ has the homotopy type of a countable cell complex (VA.18) all of whose cells are $0$-cells, one for each geodesic from $p$ to $q$ (Theorem 17.3 with all indices $0$). (ii) If $N$ is geodesically complete, the fibre of $\exp_p : T_pN \to N$ over $q$ is discrete and countable, its points $v$ correspond bijectively to the geodesics $t \mapsto \exp_p(tv)$ from $p$ to $q$, and $\Omega(N; p, q)$, with Milnor's metric, is homotopy equivalent to it. (iii) If moreover $N$ is simply connected, $\Omega(N; p, q)$ is contractible, and (for $N$ closed) it has the homotopy type of a cell complex with exactly one cell, a $0$-cell.

- `Morse.omega_cells_of_nonpos` — Morse/Chapter11/CartanHadamard.lean, line 340
- `Morse.geodesic_iff_mem_fiber` — Morse/Chapter11/CartanHadamard.lean, line 453
- `Morse.nonempty_homotopyEquiv_pathC_fiber` — Morse/Chapter11/CartanHadamard.lean, line 364
- `Morse.omega_homotopyEquiv_fiber` — Morse/Chapter11/CartanHadamard.lean, line 480
- `Morse.contractibleSpace_pathSp` — Morse/Chapter11/CartanHadamard.lean, line 547
- `Morse.omega_single_cell` — Morse/Chapter11/CartanHadamard.lean, line 561

*What differs.*
- The homotopy type is obtained for every complete $N$ of non-positive curvature, simply connected or not: lifting a path from $p$ to $q$ from $0 \in T_pN$ and taking the end point is a homotopy equivalence of $\Omega^*$ with the fibre of $\exp_p$ over $q$, and $\Omega \simeq \Omega^*$ by Theorem 17.1.
- That a countable cell complex with only $0$-cells, in the sense of VA.18 (a mapping telescope of finite stages), is homotopy equivalent to a discrete space is not formalized; (ii) reaches the discrete space directly.
- For simply connected $N$ the contraction is explicit: $\Omega^*$ contracts onto a geodesic through the diffeomorphism $\exp_p$, and $\Omega \simeq \Omega^*$.

### V11.19. $\exp_p$ is a covering map

*not in the book* · $T_pN$ is the universal covering · Gauss lemma beyond a normal ball · “it is clear” made precise

**Milnor (§19, p. 103).** The book has no such statement. At the end of the proof of 19.2 Milnor notes that by 18.1 $\exp_p$ is non-critical everywhere, "so that $\exp_p$ is locally a diffeomorphism". For a complete $M$ of curvature $\le 0$ that is not simply connected, Theorem 19.2 is applied to the universal covering space $\tilde M$, which, "it is clear", inherits from $M$ a Riemannian metric that is geodesically complete and of curvature $\le 0$.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: (i) the Gauss lemma holds on the whole domain of $\exp_p$: $\langle d(\exp_p)_w(w), d(\exp_p)_w(x)\rangle = \langle w, x\rangle$ for $w \in \mathcal D_p$, $x \in T_pN$. (ii) $\exp_p : T_pN \to N$ is a local diffeomorphism at every point where $d(\exp_p)$ is one-to-one. Now let $N$ be geodesically complete and $\exp_p$ nowhere critical. (iii) A lift $\Gamma$ through $\exp_p$ of a smooth curve of speed $\le L$ on $[0, T]$ satisfies $\|\Gamma(t)\| \le \|\Gamma(0)\| + 1 + Lt$. (iv) Smooth curves in $N$ lift through $\exp_p$, uniquely, from any point over the initial point. (v) $\exp_p : T_pN \to N$ is a covering map. In non-positive curvature (V11.8) all of this applies.

- `Morse.gauss_lemma_expDomAt` — Morse/Chapter11/ExpCovering.lean, line 103
- `Morse.isLocalDiffeomorphAt_expToN` — Morse/Chapter11/ExpCovering.lean, line 240
- `Morse.isLocalDiffeomorph_expToN` — Morse/Chapter11/ExpCovering.lean, line 287
- `Morse.norm_expLift_le` — Morse/Chapter11/ExpCovering.lean, line 343
- `Morse.exists_expLift` — Morse/Chapter11/ExpCovering.lean, line 412
- `Morse.expLift_unique` — Morse/Chapter11/ExpCovering.lean, line 525
- `Morse.isCoveringMap_expToN` — Morse/Chapter11/ExpCovering.lean, line 547
- `Morse.isCoveringMap_expToN_of_nonpos` — Morse/Chapter11/CartanHadamard.lean, line 126

*What differs.*
- The universal covering of p. 103 and of Corollary 19.3 is $\exp_p : T_pN \to N$ itself, so no abstract covering space and no metric on it are needed; the covering argument is the standard proof of the Cartan–Hadamard theorem, not Milnor's, who works with the path space.
- The only analytic input beyond Lemma 19.1 is the completeness of the metric pulled back to $T_pN$ — Milnor's "it is clear" — used in the form (iii): by the Gauss lemma the radius of a lift grows no faster than the length of the curve. This needs the Gauss lemma on the whole domain of $\exp_p$, while Milnor states it only in a normal neighbourhood (Lemma 10.5).
- "Locally a diffeomorphism" is the inverse function theorem on manifolds (the companion project's): the derivative of $\exp_p$ into $N$ is one-to-one, and onto because $\dim T_pN = \dim N$.

### V11.20. Each homotopy class of paths contains exactly one geodesic

*as in the book* · the covering is $\exp_p$, not $\tilde M$

**Milnor (§19, p. 103).** More generally, suppose that $M$ is complete with sectional curvature $\le 0$ but not simply connected (for example a flat torus, or a compact surface of genus $\ge 2$ with constant negative curvature). Theorem 19.2 applies to the universal covering space $\tilde M$; given two points $p, q \in M$, it follows that each homotopy class of paths from $p$ to $q$ contains precisely one geodesic.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $N$ be geodesically complete and of non-positive curvature, and $p, q \in N$. Every continuous path $c$ in $N$ from $p$ to $q$ is homotopic, relative to its end points, to a geodesic $\gamma \in \Omega(N; p, q)$; and two geodesics in $\Omega(N; p, q)$ that are both homotopic to $c$ agree on $[0, 1]$.

- `Morse.pathOfMem` — Morse/Chapter11/CartanHadamard.lean, line 603
- `Morse.homotopy_class_unique_geodesic` — Morse/Chapter11/CartanHadamard.lean, line 615

*What differs.*
- The statement is Milnor's, for every complete $N$ of curvature $\le 0$. The geodesics from $p$ are the images of the segments from $0$ in $T_pN$, which are their lifts through the covering $\exp_p$ (V11.19); homotopic paths have lifts from $0$ with the same end point, and two paths of $T_pN$ with the same end points are homotopic.

### V11.21. Corollary 19.3: the homotopy groups in non-positive curvature

*narrower* · only $\pi_i(M) = 0$ for $i > 1$ · torsion-freeness of $\pi_1$ not proved

**Milnor (§19, Corollary 19.3, p. 103).** If $M$ is complete with $\langle R(A, B)A, B\rangle \le 0$, then the homotopy groups $\pi_i(M)$ are zero for $i > 1$, and $\pi_1(M)$ contains no element of finite order other than the identity. Proof: clearly $\pi_i(M) = \pi_i(\tilde M) = 0$ for $i > 1$, $\tilde M$ being contractible; and since the cohomology of $M$ is that of the group $\pi_1(M)$ (Hu), a non-trivial finite cyclic subgroup $G$ would give a covering $\hat M$ with $H^k(G) = H^k(\hat M) = 0$ for $k > n$, while the cohomology of a finite cyclic group is non-trivial in arbitrarily high dimensions.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: if $N$ is geodesically complete and of non-positive curvature, then $\pi_i(N, x) = 0$ for every $i > 1$ and every base point $x \in N$ (Mathlib's homotopy groups); on the way, every map of the cube $I^i$, $i \ge 2$, constant on the boundary, is null-homotopic relative to the boundary.

- `Morse.contractibleSpace_cube` — Morse/Chapter11/CartanHadamard.lean, line 254
- `Morse.isPreconnected_cube_face` — Morse/Chapter11/CartanHadamard.lean, line 264
- `Morse.genLoop_homotopic_const` — Morse/Chapter11/CartanHadamard.lean, line 286
- `Morse.corollary_19_3` — Morse/Chapter11/CartanHadamard.lean, line 325

*What differs.*
- Only the first half is formalized. That $\pi_1(M)$ has no non-trivial element of finite order needs the cohomology of groups ($H^k(M) \cong H^k(\pi_1(M))$ for $M$ with contractible universal covering) and the cohomology of finite cyclic groups, which are not available.
- "Clearly $\pi_i(M) = \pi_i(\tilde M)$" is proved by lifting: a map of the cube lifts through the covering $\exp_x$ because the cube is simply connected and locally path connected, and the lift is constant on the boundary because the fibre is discrete and the boundary of the cube is connected for $i \ge 2$ — which is where the argument, and the statement, stop for $i = 1$.

### V11.22. Theorem 19.6: positive Ricci curvature and the path space

*narrower* · $p$, $q$ not conjugate along any geodesic · $n \ge 2$ · countable cell complex: a telescope

**Milnor (§19, Theorem 19.6, p. 106).** If $M$ is a compact manifold, and if the Ricci tensor $K$ of $M$ is everywhere positive definite, then the path space $\Omega(M; p, q)$ has the homotopy type of a CW-complex having only finitely many cells in each dimension. Proof: by the index estimate a geodesic of length $> k\pi r$ has index $\ge k$; if $p$ and $q$ are not conjugate along any geodesic, then by 16.3 there are only finitely many geodesics of length $\le k\pi r$, hence only finitely many with index $< k$; together with 17.3 this completes the proof.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $N$ be compact, $n = \dim N \ge 2$, with Ricci tensor positive definite at every point, and $p, q \in N$ with $q$ not conjugate to $p$ along any geodesic ($q \notin C(p)$, V11.4). Then $\Omega(N; p, q)$, with Milnor's metric, has the homotopy type of a countable cell complex (VA.18) in which each dimension $d$ occurs at only finitely many of the stages, each stage attaching finitely many cells: only finitely many cells of each dimension. The same holds for $N$ closed in $V$ with $K(U, U) \ge (n - 1)/r^2$ for every unit tangent vector $U$ at every point, $n = \dim N$ for some $r > 0$; on the way, a geodesic of index $\le d$ has energy $\le ((d + 1)\pi r)^2$.

- `Morse.energy_le_of_geodesicIndex_le` — Morse/Chapter11/PositiveRicci.lean, line 211
- `Morse.theorem_19_6_of_ricciLowerBound` — Morse/Chapter11/PositiveRicci.lean, line 226
- `Morse.theorem_19_6` — Morse/Chapter11/PositiveRicci.lean, line 258

*What differs.*
- Milnor's proof covers only end points not conjugate along any geodesic, while the theorem is stated for all $p, q$. This item is that case; the general case, through a nearby non-conjugate $q'$ (Corollary 18.2) and the change of end point $\Omega(M; p, q) \simeq \Omega(M; p, q')$ (the exposition's Lemma 17.D, through Theorem 17.1), is V11.24.
- Counting the cells: Theorem 16.3 gives finitely many energy values below each level, the stages of the complex of 17.3 are ordered by energy, and a geodesic of index $\le d$ has length $\le (d + 1)\pi r$, hence energy $\le ((d + 1)\pi r)^2$, energy being length squared at constant speed.
- $n \ge 2$ is needed (for $n = 1$ the Ricci tensor vanishes, so the hypothesis cannot hold on a nonempty $N$); the CW-complex is a countable cell complex with arbitrary attaching maps (VA.18).

### V11.23. The homology of the path space in positive Ricci curvature

*not in the book* · finite Betti numbers, field coefficients · energy filtration, not cellular homology

**Milnor (§19, cf. Theorem 19.6, p. 106).** The book draws no homological consequence from Theorem 19.6; with cellular homology it would be immediate that each $H_i(\Omega(M; p, q))$ is finitely generated, as on p. 96 Milnor reads the homology of $\Omega(S^n)$ off its cells.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric, closed in $V$, and $p, q \in N$ with every geodesic in $\Omega(N; p, q)$ of nullity $0$: for levels $a \le b$ that are not energies of geodesics, $H_j(\Omega^b, \Omega^a; \Bbbk)$ is finite-dimensional, and zero if no geodesic with energy in $(a, b)$ has index $j$. Hence, if $n = \dim N \ge 2$, $r > 0$, $K(U, U) \ge (n - 1)/r^2$ for every unit tangent vector $U$ at every point, $n = \dim N$, and $q \notin C(p)$, then $H_i(\Omega(N; p, q); \Bbbk)$ is finite-dimensional for every $i$ and every field $\Bbbk$; in particular under Milnor's hypotheses of Theorem 19.6 (compact $N$, positive definite Ricci tensor).

- `Morse.slabEnergies` — Morse/Chapter11/RicciHomology.lean, line 61
- `Morse.slab_homology` — Morse/Chapter11/RicciHomology.lean, line 68
- `Morse.finiteDimensional_spaceHomology_omega` — Morse/Chapter11/RicciHomology.lean, line 170
- `Morse.finiteDimensional_spaceHomology_omega_of_compact` — Morse/Chapter11/RicciHomology.lean, line 244

*What differs.*
- The cell complexes of VA.18 have non-cellular attaching maps, so cellular homology is not available; the homology is computed from the energy filtration of $\Omega$: above the energy $((i + 2)\pi r)^2$ every geodesic has index $\ge i + 2$, so the slabs there have no homology in degrees $i$ and $i + 1$, and $H_i(\Omega^a) \cong H_i(\Omega)$ for a regular level $a$ above it.
- As in V11.22, end points conjugate along some geodesic are not treated.

### V11.24. Theorem 19.6 for all end points

*hypotheses explicit* · the missing case of the proof supplied · $n \ge 2$ · countable cell complex: a telescope

**Milnor (§19, Theorem 19.6, p. 106).** If $M$ is a compact manifold, and if the Ricci tensor $K$ of $M$ is everywhere positive definite, then the path space $\Omega(M; p, q)$ has the homotopy type of a CW-complex having only finitely many cells in each dimension — stated for all $p, q$; the proof treats $p, q$ not conjugate along any geodesic.

**Proved in Lean.** For a submanifold $N$ of a Euclidean space $V$, with the induced metric: let $N$ be compact, $n = \dim N \ge 2$, with Ricci tensor positive definite at every point. Then for all $p, q \in N$, $\Omega(N; p, q)$ has the homotopy type of a countable cell complex (VA.18) with only finitely many cells of each dimension, and $H_i(\Omega(N; p, q); \Bbbk)$ is finite-dimensional for every $i$ and every field $\Bbbk$. On the way, $q$ is joined in $N$ to a point $q'$ not conjugate to $p$ along any geodesic, and $\Omega(N; p, q) \simeq \Omega(N; p, q')$.

- `Morse.exists_joined_notMem_conjLocus` — Morse/Chapter10/CWType.lean, line 88
- `Morse.pathSpHomotopyEquiv` — Morse/Chapter10/CWType.lean, line 110
- `Morse.IsCountableCellComplexType.of_homotopyEquiv` — Morse/Appendix/MonotoneUnion.lean, line 373
- `Morse.theorem_19_6_all` — Morse/Chapter11/PositiveRicciAll.lean, line 52
- `Morse.finiteDimensional_spaceHomology_omega_all` — Morse/Chapter11/PositiveRicciAll.lean, line 63

*What differs.*
- Milnor's proof needs $p$ and $q$ not conjugate along any geodesic; the general case moves $q$ to a nearby non-conjugate $q'$ (Corollary 18.2, V11.5–V11.6) and uses $\Omega(N; p, q) \simeq \Omega(N; p, q')$ (the exposition's Lemma 17.D, through Theorem 17.1), under which the conclusion is invariant. No connectedness of $N$ is needed: $q'$ lies in a small Riemannian ball about $q$.
- As in V11.22, $n \ge 2$ and the cell complex is a countable telescope (VA.18).

## Chapter 12

*Milnor §§20–21, pp. 109–117: symmetric spaces, Lie groups*

### V12.1. The algebraic model of a bi-invariant metric

*restated* · an abstract Lie algebra with a form

**Milnor (§21, p. 113).** Milnor works with the Lie algebra $\mathfrak g$ of left-invariant vector fields on a Lie group $G$ with a left and right invariant metric, the bracket of vector fields, and the connection $X \vdash Y$ of the metric; Theorem 21.3 (a) is the identity $\langle[X, Y], Z\rangle = \langle X, [Y, Z]\rangle$.

**Proved in Lean.** For a real Lie algebra $L$ (standing for Milnor's $\mathfrak g$ of left-invariant fields) with a bilinear form $B$ (his inner product on $\mathfrak g$): $B$ is ad-invariant if $B([X, Y], Z) = B(X, [Y, Z])$ for all $X, Y, Z$, which is Mathlib's Lie invariance. A bilinear $D : L \times L \to L$, standing for $X \vdash Y$, is Levi-Civita for $B$ if $D(X, Y) - D(Y, X) = [X, Y]$ and $B(D(X, Y), Z) + B(Y, D(X, Z)) = 0$.

- `Morse.IsAdInvariant` — Morse/Chapter12/BiInvariant.lean, line 136
- `Morse.isAdInvariant_iff_lieInvariant` — Morse/Chapter12/BiInvariant.lean, line 138
- `Morse.IsLeviCivita` — Morse/Chapter12/BiInvariant.lean, line 152

*What differs.*
- The group, its left-invariant fields and its metric are replaced by an abstract Lie algebra with a bilinear form. That $X \vdash Y$ is again left-invariant, which Milnor uses without comment when he applies (d) twice, is built into the definition. For matrix groups the model is derived from the geometry (V12.17).

### V12.2. Theorem 21.3 (d): $X \vdash Y = \frac12[X, Y]$

*restated* · $X \vdash X = 0$ is a hypothesis

**Milnor (§21, proof of Theorem 21.3, pp. 113–114).** In the proof of Theorem 21.3: the integral curves of a left-invariant $X$ are left translates of one-parameter subgroups, hence geodesics, so $X \vdash X = 0$; expanding $(X + Y) \vdash (X + Y) = 0$ and adding $X \vdash Y - Y \vdash X = [X, Y]$ gives (d), $X \vdash Y = \frac12[X, Y]$.

**Proved in Lean.** For a real Lie algebra $L$ (standing for Milnor's $\mathfrak g$ of left-invariant fields) with a bilinear form $B$ (his inner product on $\mathfrak g$): if $D$ is Levi-Civita for $B$ (no condition on $B$) and $D(X, X) = 0$ for every $X$, then $D(X, Y) = \frac12[X, Y]$ for all $X, Y$.

- `Morse.IsLeviCivita.conn_eq` — Morse/Chapter12/BiInvariant.lean, line 160

*What differs.*
- $X \vdash X = 0$ rests on Lemma 21.2 and on left translations being isometries; here it is a hypothesis. For matrix groups it is proved (V12.15, V12.17).

### V12.3. Theorem 21.3 (a): the metric is ad-invariant

*restated* · geometric inputs as hypotheses

**Milnor (§21, Theorem 21.3 (a), p. 113).** Let $G$ have a bi-invariant metric and $X, Y, Z \in \mathfrak g$. Then $\langle[X, Y], Z\rangle = \langle X, [Y, Z]\rangle$. Proof (p. 114): $Y\langle X, Z\rangle = \langle Y \vdash X, Z\rangle + \langle X, Y \vdash Z\rangle$, the left side vanishes since $\langle X, Z\rangle$ is constant, and (d) is substituted.

**Proved in Lean.** For a real Lie algebra $L$ (standing for Milnor's $\mathfrak g$ of left-invariant fields) with a bilinear form $B$ (his inner product on $\mathfrak g$): if $D$ is Levi-Civita for $B$ and $D(X, X) = 0$ for every $X$, then $B$ is ad-invariant.

- `Morse.IsLeviCivita.isAdInvariant` — Morse/Chapter12/BiInvariant.lean, line 174

*What differs.*
- The constancy of $\langle X, Z\rangle$ for left-invariant fields is built into the compatibility condition of V12.1, and $X \vdash X = 0$ is a hypothesis.

### V12.4. The Koszul formula: the connection is forced to be $\frac12[\,,\,]$

*not in the book* · the converse route, from ad-invariance

**Milnor (§21, cf. Theorem 21.3, p. 113).** The book has no such statement. Milnor derives (d) from $X \vdash X = 0$; that the Levi-Civita connection of a bi-invariant metric must be $\frac12[\,,\,]$ on left-invariant fields is the uniqueness of Lemma 8.6 in this setting.

**Proved in Lean.** For a real Lie algebra $L$ (standing for Milnor's $\mathfrak g$ of left-invariant fields) with a bilinear form $B$ (his inner product on $\mathfrak g$): if $B$ is symmetric and $D$ Levi-Civita for $B$, then $2B(D(X, Y), Z) = B([X, Y], Z) - B([Y, Z], X) + B([Z, X], Y)$; if moreover $B$ is ad-invariant and non-degenerate, $D(X, Y) = \frac12[X, Y]$. Conversely, for every ad-invariant $B$, $\frac12[\,,\,]$ is Levi-Civita for $B$.

- `Morse.IsLeviCivita.koszul` — Morse/Chapter12/BiInvariant.lean, line 183
- `Morse.IsLeviCivita.conn_eq_of_isAdInvariant` — Morse/Chapter12/BiInvariant.lean, line 199
- `Morse.halfLie` — Morse/Chapter12/BiInvariant.lean, line 214
- `Morse.halfLie_apply` — Morse/Chapter12/BiInvariant.lean, line 216
- `Morse.isLeviCivita_halfLie` — Morse/Chapter12/BiInvariant.lean, line 220

*What differs.*
- Derives (d) from the ad-invariance of the metric instead of from $X \vdash X = 0$.

### V12.5. Theorem 21.3 (b): $R(X, Y)Z = \frac14[[X, Y], Z]$

*restated* · the curvature of $D = \frac12[\,,\,]$

**Milnor (§21, Theorem 21.3 (b), p. 113).** Let $G$ have a bi-invariant metric and $X, Y, Z \in \mathfrak g$. Then $R(X, Y)Z = \frac14[[X, Y], Z]$. Proof (p. 114): substitute (d) in $R(X, Y)Z = -X \vdash (Y \vdash Z) + Y \vdash (X \vdash Z) + [X, Y] \vdash Z$ and use the Jacobi identity.

**Proved in Lean.** In any real Lie algebra, with Milnor's sign $R(X, Y)Z = -D(X, D(Y, Z)) + D(Y, D(X, Z)) + D([X, Y], Z)$ and $D = \frac12[\,,\,]$: $R(X, Y)Z = \frac14[[X, Y], Z]$.

- `Morse.curv` — Morse/Chapter12/BiInvariant.lean, line 233
- `Morse.curv_halfLie` — Morse/Chapter12/BiInvariant.lean, line 236

*What differs.*
- A computation in the Lie algebra; that it is the curvature of the group is V12.17 for matrix groups.

### V12.6. Theorem 21.3 (c)

*restated* · for the algebraic curvature

**Milnor (§21, Theorem 21.3 (c), p. 113).** $\langle R(X, Y)Z, W\rangle = \frac14\langle[X, Y], [Z, W]\rangle$; it "follows from (a) and (b)" (p. 114).

**Proved in Lean.** For a real Lie algebra $L$ (standing for Milnor's $\mathfrak g$ of left-invariant fields) with a bilinear form $B$ (his inner product on $\mathfrak g$): if $B$ is ad-invariant, then $B(R(X, Y)Z, W) = \frac14B([X, Y], [Z, W])$ for $D = \frac12[\,,\,]$.

- `Morse.curv_inner` — Morse/Chapter12/BiInvariant.lean, line 243

*What differs.*
- As in V12.5.

### V12.7. Cartan's 3-form

*narrower* · only the skew-symmetry

**Milnor (§21, footnote, p. 114).** The trilinear function $\langle[X, Y], Z\rangle$ is skew-symmetric in all three variables, so it defines a left-invariant 3-form; Cartan used it to prove $H^3(G) \neq 0$ for a compact connected non-abelian Lie group.

**Proved in Lean.** For a real Lie algebra $L$ (standing for Milnor's $\mathfrak g$ of left-invariant fields) with a bilinear form $B$ (his inner product on $\mathfrak g$): $B([Y, X], Z) = -B([X, Y], Z)$ for every $B$, and $B([X, Z], Y) = -B([X, Y], Z)$ if $B$ is ad-invariant; so $(X, Y, Z) \mapsto B([X, Y], Z)$ is alternating.

- `Morse.cartan_form_swap₁₂` — Morse/Chapter12/BiInvariant.lean, line 550
- `Morse.cartan_form_swap₂₃` — Morse/Chapter12/BiInvariant.lean, line 554

*What differs.*
- The differential form, its de Rham class and Cartan's theorem are not formalized.

### V12.8. Corollary 21.4: the sectional curvature

*stronger* · for all $X, Y$, not only orthonormal pairs

**Milnor (§21, Corollary 21.4, p. 115).** The sectional curvature $\langle R(X, Y)X, Y\rangle = \frac14\langle[X, Y], [X, Y]\rangle$ is always $\ge 0$, with equality iff $[X, Y] = 0$.

**Proved in Lean.** For a real Lie algebra $L$ (standing for Milnor's $\mathfrak g$ of left-invariant fields) with a bilinear form $B$ (his inner product on $\mathfrak g$): if $B$ is ad-invariant, $B(R(X, Y)X, Y) = \frac14B([X, Y], [X, Y])$ for all $X, Y$; if $B$ is also positive definite this is $\ge 0$, and $0$ iff $[X, Y] = 0$. With the standard sign, $B(-R(X, Y)Y, X) = \frac14B([X, Y], [X, Y])$.

- `Morse.sectional` — Morse/Chapter12/BiInvariant.lean, line 248
- `Morse.sectional_nonneg` — Morse/Chapter12/BiInvariant.lean, line 296
- `Morse.sectional_eq_zero_iff` — Morse/Chapter12/BiInvariant.lean, line 309
- `Morse.sectional_std` — Morse/Chapter12/BiInvariant.lean, line 303

### V12.9. Corollary 21.5, the algebraic step: positive Ricci curvature

*narrower* · only the positivity of the Ricci curvature · $G$ must be connected

**Milnor (§21, Corollary 21.5, p. 115).** If the Lie algebra $\mathfrak g$ of a Lie group $G$ with a bi-invariant metric has trivial centre, then $G$ is compact with finite fundamental group. Proof: the Ricci curvature $K(X_1, X_1) = \sum_i\langle R(X_1, X_i)X_1, X_i\rangle$ is strictly positive and bounded away from zero, and Myers' theorem (Corollary 19.5) applies.

**Proved in Lean.** Let $K_V = -\frac14\operatorname{ad}_V^2$, so that $K_V(W) = R(V, W)V$ for $D = \frac12[\,,\,]$. In every real Lie algebra $\operatorname{tr}K_V = -\frac14\kappa(V, V)$, $\kappa$ the Killing form. If $L$ is finite-dimensional, $B$ symmetric, positive definite and ad-invariant and the centre of $L$ is $0$, then $\operatorname{tr}K_V > 0$ for $V \neq 0$; equivalently $\kappa$ is negative definite.

- `Morse.jacobiOp` — Morse/Chapter12/BiInvariant.lean, line 259
- `Morse.curv_halfLie_eq_jacobiOp` — Morse/Chapter12/BiInvariant.lean, line 266
- `Morse.trace_jacobiOp` — Morse/Chapter12/BiInvariant.lean, line 442
- `Morse.trace_eq_sum_of_isOrtho` — Morse/Chapter12/BiInvariant.lean, line 450
- `Morse.trace_jacobiOp_pos` — Morse/Chapter12/BiInvariant.lean, line 462
- `Morse.killingForm_neg` — Morse/Chapter12/BiInvariant.lean, line 498

*What differs.*
- The uniform bound, Myers' theorem for $G$, compactness and the finiteness of $\pi_1$ are not formalized. Milnor omits "connected", which cannot be dropped ($SO(3) \times \mathbb Z$).

### V12.10. Corollary 21.6, the algebraic step: splitting off the centre

*narrower* · an ideal, not only a subalgebra · the group is not split

**Milnor (§21, Corollary 21.6, p. 115).** A simply connected Lie group $G$ with a bi-invariant metric splits as $G' \times \mathbb R^k$, $G'$ compact with Lie algebra of trivial centre. Proof (pp. 115–116): the orthogonal complement $\mathfrak g'$ of the centre $\mathfrak c$ is a subalgebra, since $\langle[X, Y], C\rangle = \langle X, [Y, C]\rangle = 0$, and $\mathfrak g = \mathfrak g' \oplus \mathfrak c$.

**Proved in Lean.** For a real Lie algebra $L$ (standing for Milnor's $\mathfrak g$ of left-invariant fields) with a bilinear form $B$ (his inner product on $\mathfrak g$): for ad-invariant $B$, $\mathfrak g' = \{X : B(C, X) = 0 \text{ for } C \in \mathfrak c\}$ is a Lie ideal; if $L$ is finite-dimensional and $B$ symmetric, positive definite and ad-invariant, $L = \mathfrak c \oplus \mathfrak g'$ and $\mathfrak g'$ has trivial centre.

- `Morse.centerCompl` — Morse/Chapter12/BiInvariant.lean, line 508
- `Morse.mem_centerCompl` — Morse/Chapter12/BiInvariant.lean, line 512
- `Morse.isCompl_center_centerCompl` — Morse/Chapter12/BiInvariant.lean, line 517
- `Morse.eq_zero_of_mem_centerCompl` — Morse/Chapter12/BiInvariant.lean, line 532

*What differs.*
- The splitting of the simply connected group and the compactness of $G'$ are not formalized. $\mathfrak g'$ is shown to be an ideal, which is what the splitting uses.

### V12.11. The operator $K_V$ in the proof of Theorem 21.7

*stronger* · the kernel of $K_V$ is the centralizer

**Milnor (§21, proof of Theorem 21.7, pp. 116–117).** $K_V(W) = R(V, W)V = \frac14[[V, W], V]$, so $K_V = -\frac14(\operatorname{Ad}V)\circ(\operatorname{Ad}V)$, and $\operatorname{Ad}V$ is skew-symmetric by 21.3 (a).

**Proved in Lean.** For a real Lie algebra $L$ (standing for Milnor's $\mathfrak g$ of left-invariant fields) with a bilinear form $B$ (his inner product on $\mathfrak g$) ad-invariant: $\operatorname{ad}_V$ is skew, $K_V$ is self-adjoint and $B(K_VW, W) = \frac14B([V, W], [V, W])$. If $B$ is also positive definite, $K_V$ is positive semi-definite, $K_VW = 0$ iff $[V, W] = 0$, every eigenvalue of $K_V$ is $\ge 0$, and the only real eigenvalue of $\operatorname{ad}_V$ is $0$.

- `Morse.jacobiOp_apply` — Morse/Chapter12/BiInvariant.lean, line 262
- `Morse.ad_skew` — Morse/Chapter12/BiInvariant.lean, line 252
- `Morse.jacobiOp_symm` — Morse/Chapter12/BiInvariant.lean, line 270
- `Morse.jacobiOp_self` — Morse/Chapter12/BiInvariant.lean, line 277
- `Morse.jacobiOp_self_nonneg` — Morse/Chapter12/BiInvariant.lean, line 289
- `Morse.jacobiOp_eq_zero_iff` — Morse/Chapter12/BiInvariant.lean, line 320
- `Morse.eigenvalue_nonneg` — Morse/Chapter12/BiInvariant.lean, line 332
- `Morse.ad_eigenvalue_eq_zero` — Morse/Chapter12/BiInvariant.lean, line 342

### V12.12. The non-zero eigenvalues of $K_V$ occur in pairs

*restated* · a complex structure, not the normal form

**Milnor (§21, proof of Theorem 21.7, p. 117).** Choosing an orthonormal basis that puts $\operatorname{Ad}V$ in block form with blocks $\begin{pmatrix}0 & a_i\\ -a_i & 0\end{pmatrix}$, $(\operatorname{Ad}V)^2$ is diagonal with entries $-a_1^2, -a_1^2, -a_2^2, \dots$; so the non-zero eigenvalues of $K_V$ are positive and occur in pairs.

**Proved in Lean.** For a real Lie algebra $L$ (standing for Milnor's $\mathfrak g$ of left-invariant fields) with a bilinear form $B$ (his inner product on $\mathfrak g$) ad-invariant and positive definite, $L$ finite-dimensional: $K_VW = \mu W$ iff $[V, [V, W]] = -4\mu W$; $\operatorname{ad}_V$ preserves each eigenspace $E_\mu$; for $\mu > 0$, $J = (2\sqrt\mu)^{-1}\operatorname{ad}_V$ satisfies $J^2 = -1$ on $E_\mu$ and preserves $B$; so every eigenspace of $K_V$ for $\mu \neq 0$ has even dimension.

- `Morse.jacobiOp_of_lie_lie` — Morse/Chapter12/BiInvariant.lean, line 355
- `Morse.lie_lie_of_jacobiOp` — Morse/Chapter12/BiInvariant.lean, line 361
- `Morse.lie_mem_eigenspace` — Morse/Chapter12/BiInvariant.lean, line 370
- `Morse.eigenJ` — Morse/Chapter12/BiInvariant.lean, line 379
- `Morse.eigenJ_comp_self` — Morse/Chapter12/BiInvariant.lean, line 389
- `Morse.eigenJ_isometry` — Morse/Chapter12/BiInvariant.lean, line 425
- `Morse.even_finrank_of_comp_self_eq_neg_id` — Morse/Chapter12/BiInvariant.lean, line 122
- `Morse.even_finrank_eigenspace` — Morse/Chapter12/BiInvariant.lean, line 407

*What differs.*
- The normal form of a skew-symmetric map, quoted without proof, is replaced by the complex structure $J$ on each eigenspace, which is what "occur in pairs" needs.

### V12.13. Even index from paired eigenvalues

*restated* · the index of a spectrum · not joined to V12.12

**Milnor (§21, proof of Theorem 21.7, p. 117).** By 20.5 the conjugate points occur in pairs, every conjugate point has even multiplicity, and with the Index Theorem the index of every geodesic from $p$ to $q$ is even.

**Proved in Lean.** For real numbers $e_1, \dots, e_N$ (a spectrum of $K_V$ with multiplicity), the index of the spectrum is $\sum_{0 < t < 1}\#\{i : e_i > 0,\ t \in \pi\mathbb Z/\sqrt{e_i}\}$ (Theorems 20.5 and 15.1 written as a definition, V14.7–V14.8). If every positive value occurs an even number of times, the index is even.

- `Morse.even_spectralIndex` — Morse/Chapter14/IndexCount.lean, line 272
- `Morse.spectralIndex` — Morse/Chapter14/IndexCount.lean, line 217
- `Morse.conjParams` — Morse/Chapter14/IndexCount.lean, line 143

*What differs.*
- Theorems 20.5 and 15.1 enter as a definition here; for $SU(n)$ they are proved (V14.18, V14.19). Passing from even-dimensional eigenspaces (V12.12) to even multiplicities in a list needs the spectral theorem for $K_V$, which is not formalized in this form, so Theorem 21.7 is not assembled.

### V12.14. Matrix groups and their bi-invariant metric

*narrower* · groups given as matrices only · no Haar averaging

**Milnor (§21, p. 112; §23, p. 125).** A Lie group $G$ with a metric invariant under left and right translations; if $G$ is compact such a metric exists, by averaging any metric with the Haar measure (p. 112). For $U(n)$ the tangent space at $I$ is the space of skew-Hermitian matrices (p. 125, (6)).

**Proved in Lean.** Multiplication by a unitary matrix is a linear isometry of $M_n(\mathbb K)$. A matrix group is a slice submanifold $G \subseteq M_n(\mathbb K)$ with a real Lie subalgebra $\mathfrak g$ such that every $g \in G$ is unitary, $G$ is closed under products and adjoints, $\mathfrak g$ consists of skew-Hermitian matrices and is invariant under $X \mapsto gXg^*$, $\exp\mathfrak g \subseteq G$, and $\dim G = \dim\mathfrak g$. Then $T_gG = g\mathfrak g$, left and right translations by elements of $G$ are isometries of $M_n(\mathbb K)$ preserving $G$ (the metric is bi-invariant), and the inner product on $\mathfrak g$ is ad-invariant and positive definite.

- `Morse.MatrixInner.innerProductSpace` — Morse/Chapter12/MatrixInner.lean, line 113
- `Morse.inner_def` — Morse/Chapter12/MatrixInner.lean, line 175
- `Morse.inner_mul_left_of_unitary` — Morse/Chapter12/MatrixInner.lean, line 192
- `Morse.inner_mul_right_of_unitary` — Morse/Chapter12/MatrixInner.lean, line 198
- `Morse.exp_conjTranspose_mul_exp_of_skew` — Morse/Chapter12/MatrixInner.lean, line 274
- `Morse.IsMatrixGroup` — Morse/Chapter12/MatrixGroups.lean, line 224
- `Morse.IsMatrixGroup.tangentSubspace_eq` — Morse/Chapter12/MatrixGroups.lean, line 286
- `Morse.IsMatrixGroup.mulLeftIso_image` — Morse/Chapter12/MatrixGroups.lean, line 336
- `Morse.IsMatrixGroup.mulRightIso_image` — Morse/Chapter12/MatrixGroups.lean, line 349
- `Morse.frobForm` — Morse/Chapter12/GroupGeodesics.lean, line 175
- `Morse.isAdInvariant_frobForm` — Morse/Chapter12/GroupGeodesics.lean, line 187
- `Morse.frobForm_pos` — Morse/Chapter12/GroupGeodesics.lean, line 194

*What differs.*
- Milnor's abstract Lie groups and left-invariant fields are replaced by groups of matrices with the induced metric; every compact Lie group is one (Peter–Weyl), which is not needed for §§23–24. The algebra of V12.1–V12.13 applies to $(\mathfrak g, \langle\,,\rangle)$.

### V12.15. Lemma 21.2: the geodesics are the one-parameter subgroups

*narrower* · matrix groups · acceleration computed, no Lemma 20.1

**Milnor (§21, Lemma 21.2, p. 113).** The geodesics $\gamma$ with $\gamma(0) = e$ are precisely the one-parameter subgroups of $G$. (By Corollary 20.2, p. 110, a symmetric space is complete.)

**Proved in Lean.** For a matrix group $(G, \mathfrak g)$ — a slice submanifold $G$ of the space $M_n(\mathbb K)$ of matrices ($\mathbb K = \mathbb R$ or $\mathbb C$), with the induced metric of $\langle A, B\rangle = \operatorname{Re}\operatorname{tr}(A^*B)$, and a Lie algebra $\mathfrak g$ of skew-Hermitian matrices (V12.14): $t \mapsto g\exp(tX)$, $g \in G$, $X \in \mathfrak g$, is a geodesic on $\mathbb R$; a geodesic on a preconnected open set $s \ni t_0$ is $\gamma(t_0)\exp((t - t_0)X)$ with $X = \gamma(t_0)^*\gamma'(t_0) \in \mathfrak g$. (i) A geodesic $\gamma : \mathbb R \to G$ with $\gamma(0) = I$ is $t \mapsto \exp(t\gamma'(0))$ and satisfies $\gamma(s + t) = \gamma(s)\gamma(t)$. (ii) A differentiable $\theta : \mathbb R \to G$ with $\theta(0) = I$ and $\theta(s + t) = \theta(s)\theta(t)$ is a geodesic. $\exp_g(gX) = g\exp X$, and $G$ is geodesically complete.

- `Morse.IsMatrixGroup.isGeodesicOn_mul_exp_smul` — Morse/Chapter12/GroupGeodesics.lean, line 251
- `Morse.IsMatrixGroup.eqOn_mul_exp_smul` — Morse/Chapter12/GroupGeodesics.lean, line 280
- `Morse.IsMatrixGroup.lemma_21_2` — Morse/Chapter12/GroupGeodesics.lean, line 310
- `Morse.IsMatrixGroup.eq_exp_of_oneParam` — Morse/Chapter12/GroupGeodesics.lean, line 324
- `Morse.IsMatrixGroup.isGeodesicOn_of_oneParam` — Morse/Chapter12/GroupGeodesics.lean, line 361
- `Morse.IsMatrixGroup.exp_eq` — Morse/Chapter12/GroupGeodesics.lean, line 378
- `Morse.IsMatrixGroup.isGeodesicallyComplete` — Morse/Chapter12/GroupGeodesics.lean, line 390

*What differs.*
- For matrix groups only. Milnor's proof of (i) uses 20.1 and passes from commensurable parameters to all of $\mathbb R$ "by continuity"; here the acceleration $g\exp(tX)X^2$ is normal ($X^2$ is Hermitian), and uniqueness of geodesics gives the converse.

### V12.16. Lemma 21.1: the reflection $\sigma \mapsto \tau\sigma^{-1}\tau$

*narrower* · matrix groups · "symmetric space" not defined

**Milnor (§21, Lemma 21.1, p. 112).** If $G$ has a bi-invariant metric, then for each $\tau$ the map $I_\tau(\sigma) = \tau\sigma^{-1}\tau$ is an isometry which fixes $\tau$ and reverses geodesics through $\tau$; so $G$ is a symmetric space.

**Proved in Lean.** For a matrix group $(G, \mathfrak g)$ — a slice submanifold $G$ of the space $M_n(\mathbb K)$ of matrices ($\mathbb K = \mathbb R$ or $\mathbb C$), with the induced metric of $\langle A, B\rangle = \operatorname{Re}\operatorname{tr}(A^*B)$, and a Lie algebra $\mathfrak g$ of skew-Hermitian matrices (V12.14): for unitary $\tau$, $A \mapsto \tau A^*\tau$ is an involutive linear isometry of $M_n(\mathbb K)$, equal to $\sigma \mapsto \tau\sigma^{-1}\tau$ on $G$; for $\tau \in G$ it maps $G$ into $G$, fixes $\tau$, and $I_\tau(\tau\exp(tX)) = \tau\exp(-tX)$ for $X \in \mathfrak g$.

- `Morse.IsMatrixGroup.symmIso` — Morse/Chapter12/GroupGeodesics.lean, line 406
- `Morse.IsMatrixGroup.symmIso_mem` — Morse/Chapter12/GroupGeodesics.lean, line 435
- `Morse.IsMatrixGroup.symmIso_self` — Morse/Chapter12/GroupGeodesics.lean, line 440
- `Morse.IsMatrixGroup.symmIso_mul_exp_smul` — Morse/Chapter12/GroupGeodesics.lean, line 446

*What differs.*
- By V12.15 the curves $\tau\exp(tX)$ are all the geodesics through $\tau$. A symmetric space is not defined, so the last clause is not a formal statement; it would also need $G$ connected.

### V12.17. Theorem 21.3 and Corollary 21.4 for matrix groups

*narrower* · matrix groups · by the Gauss equation

**Milnor (§21, Theorem 21.3 and Corollary 21.4, p. 113).** Let $G$ have a bi-invariant metric and $X, Y, Z, W \in \mathfrak g$. Then (a) $\langle[X, Y], Z\rangle = \langle X, [Y, Z]\rangle$, (b) $R(X, Y)Z = \frac14[[X, Y], Z]$, (c) $\langle R(X, Y)Z, W\rangle = \frac14\langle[X, Y], [Z, W]\rangle$; in the proof, (d) $X \vdash Y = \frac12[X, Y]$. Corollary 21.4 (p. 115): $\langle R(X, Y)X, Y\rangle = \frac14\langle[X, Y], [X, Y]\rangle \ge 0$.

**Proved in Lean.** For a matrix group $(G, \mathfrak g)$ — a slice submanifold $G$ of the space $M_n(\mathbb K)$ of matrices ($\mathbb K = \mathbb R$ or $\mathbb C$), with the induced metric of $\langle A, B\rangle = \operatorname{Re}\operatorname{tr}(A^*B)$, and a Lie algebra $\mathfrak g$ of skew-Hermitian matrices (V12.14), $g \in G$, $X, Y, Z, W \in \mathfrak g$: (a) holds; (d) the covariant derivative of $q \mapsto qY$ in the direction $gX$ is $g\cdot\frac12[X, Y]$; the second fundamental form is $\mathrm{II}_g(gX, gY) = \frac12g(XY + YX)$; (b) $R(gX, gY)gZ = \frac14g[[X, Y], Z]$ (Milnor's sign), which is $g$ times the algebraic curvature of V12.5, and $R(gA, gW)gA = g\,K_A(W)$; (c) $\langle R(gX, gY)gZ, gW\rangle = \frac14\langle[X, Y], [Z, W]\rangle$; and $\langle R(gX, gY)gX, gY\rangle = \frac14\|[X, Y]\|^2 \ge 0$, zero iff $XY = YX$.

- `Morse.inner_lie_left` — Morse/Chapter12/GroupGeodesics.lean, line 123
- `Morse.inner_gauss_identity` — Morse/Chapter12/GroupGeodesics.lean, line 114
- `Morse.IsMatrixGroup.tanProj_eq` — Morse/Chapter12/GroupGeodesics.lean, line 231
- `Morse.IsMatrixGroup.secondFundForm_mul` — Morse/Chapter12/GroupGeodesics.lean, line 469
- `Morse.IsMatrixGroup.covAt_mul_right` — Morse/Chapter12/GroupGeodesics.lean, line 544
- `Morse.IsMatrixGroup.curvOp_mul` — Morse/Chapter12/GroupGeodesics.lean, line 496
- `Morse.IsMatrixGroup.inner_curvOp_mul` — Morse/Chapter12/GroupGeodesics.lean, line 577
- `Morse.IsMatrixGroup.sectional_mul` — Morse/Chapter12/GroupGeodesics.lean, line 523
- `Morse.IsMatrixGroup.sectional_mul_nonneg` — Morse/Chapter12/GroupGeodesics.lean, line 534
- `Morse.IsMatrixGroup.curvOp_eq_curv_halfLie` — Morse/Chapter12/GroupGeodesics.lean, line 560
- `Morse.IsMatrixGroup.curvOp_eq_jacobiOp` — Morse/Chapter12/GroupGeodesics.lean, line 585

*What differs.*
- For matrix groups. (b) is proved by the Gauss equation of the submanifold $G$ (V6.18) and a trace identity, not by substituting (d) into the definition of $R$; this removes, for matrix groups, the hypotheses of V12.1–V12.3.

### V12.18. Theorem 20.5 for matrix groups: the Jacobi equation along $\exp(tA)$

*narrower* · one-parameter subgroups of matrix groups · no eigenbasis · multiplicities: $SU(n)$ only (V14.18)

**Milnor (§20, Theorem 20.5, p. 110).** Let $\gamma$ be a geodesic in a locally symmetric manifold with $\gamma(0) = p$, $\gamma'(0) = V$, and $e_1, \dots, e_n$ the eigenvalues of $K_V(W) = R(V, W)V$. The conjugate points to $p$ along $\gamma$ are the $\gamma(\pi k/\sqrt{e_i})$, $k$ a non-zero integer, $e_i > 0$; the multiplicity of $\gamma(t)$ is the number of $e_i$ such that $t$ is a multiple of $\pi/\sqrt{e_i}$. Proof (p. 111): in a parallel orthonormal eigenframe the Jacobi equation is $w_i'' + e_iw_i = 0$.

**Proved in Lean.** For a matrix group $(G, \mathfrak g)$ — a slice submanifold $G$ of the space $M_n(\mathbb K)$ of matrices ($\mathbb K = \mathbb R$ or $\mathbb C$), with the induced metric of $\langle A, B\rangle = \operatorname{Re}\operatorname{tr}(A^*B)$, and a Lie algebra $\mathfrak g$ of skew-Hermitian matrices (V12.14), $A \in \mathfrak g$, $\gamma(t) = \exp(tA)$, $h(t) = \exp(tA/2)$: the covariant derivative of $hUh$ along $\gamma$ is $hU'h$ for $\mathfrak g$-valued $U$, and $R(\gamma', hMh)\gamma' = h\,K_A(M)\,h$ with $K_A(M) = \frac14[[A, M], A]$. Hence if $U$ is smooth with $U'' + K_A(U) = 0$, $hUh$ is a Jacobi field along $\gamma$ with covariant derivative $U'(0)$ at $0$.

- `Morse.halfExp` — Morse/Chapter12/GroupJacobi.lean, line 62
- `Morse.jacK` — Morse/Chapter12/GroupJacobi.lean, line 119
- `Morse.IsMatrixGroup.covD_conj` — Morse/Chapter12/GroupJacobi.lean, line 158
- `Morse.IsMatrixGroup.curvR_conj` — Morse/Chapter12/GroupJacobi.lean, line 199
- `Morse.IsMatrixGroup.isJacobiField_conj` — Morse/Chapter12/GroupJacobi.lean, line 223
- `Morse.IsMatrixGroup.covAlong_conj_zero` — Morse/Chapter12/GroupJacobi.lean, line 261

*What differs.*
- Only along one-parameter subgroups of matrix groups, and only the implication from the constant-coefficient equation $U'' + K_A(U) = 0$ to Jacobi fields. The frame $U \mapsto hUh$ replaces the parallel eigenframe. The count of conjugate points with multiplicities is proved for $SU(n)$ (V14.18); locally symmetric spaces are not defined.

## Chapter 13

*Milnor §22, pp. 118–123: whole manifolds of minimal geodesics*

### V13.1. The space $\Omega^d$ of minimal geodesics

*restated* · defined by least energy

**Milnor (§22, p. 118).** $\Omega^d$ denotes the space of minimal geodesics from $p$ to $q$, where $d = \rho(p, q)^2$ and $M$ is complete.

**Proved in Lean.** For a slice submanifold $N$ of a finite-dimensional inner product space $V$, with the induced metric, $p, q \in N$ and $\Omega = \Omega(N; p, q)$ with Milnor's metric (V10.1): $\Omega^d$ is the set of paths whose energy is at most that of every path of $\Omega$; a path of least energy is an unbroken geodesic.

- `Morse.minPaths` — Morse/Chapter13/Theorem22.lean, line 72
- `Morse.isUnbrokenGeodesic_of_minimal` — Morse/Chapter13/MinimalDeform.lean, line 53

*What differs.*
- By Lemma 12.1 (V8.6) the paths of least energy are the minimal geodesics parametrized proportionally to arc length, and $d = \rho(p, q)^2$; here $d$ is not named.

### V13.2. Theorem 22.1

*narrower* · neighbourhood retract assumed (no Hanner) · relative form, every compact $P$ · compact balls for completeness

**Milnor (§22, Theorem 22.1, p. 118).** If the space $\Omega^d$ of minimal geodesics from $p$ to $q$ is a topological manifold, and if every non-minimal geodesic from $p$ to $q$ has index $\ge \lambda_0$, then $\pi_i(\Omega, \Omega^d) = 0$ for $0 \le i < \lambda_0$. ($M$ is complete throughout §22; proof pp. 122–123.)

**Proved in Lean.** For a slice submanifold $N$ of a finite-dimensional inner product space $V$, with the induced metric, $p, q \in N$ and $\Omega = \Omega(N; p, q)$ with Milnor's metric (V10.1): let the closed balls about $p$ be compact, let every geodesic of $\Omega$ not of least energy have index $\ge \lambda_0$, and let $\Omega^d$ be a retract of an open neighbourhood in $\Omega$ (an open $O \supseteq \Omega^d$ and $\rho : O \to \Omega^d$, continuous on $O$, the identity on $\Omega^d$). Let $P$ be compact with a continuous injection into a real vector space of dimension $< \lambda_0$ (e.g. $I^i$, $i < \lambda_0$). Then every map $h : P \to \Omega$ is homotopic, relative to $h^{-1}(\Omega^d)$, to a map into $\Omega^d$; equivalently the inclusion $\Omega^d \to \Omega$ compresses maps from $P$.

- `Morse.theorem_22_1` — Morse/Chapter13/Theorem22.lean, line 76
- `Morse.minPathsIncl` — Morse/Chapter13/Theorem22.lean, line 244
- `Morse.compresses_minPaths` — Morse/Chapter13/Theorem22.lean, line 250

*What differs.*
- The hypothesis "$\Omega^d$ is a topological manifold" is replaced by its consequence that $\Omega^d$ is a retract of an open neighbourhood, which is all the proof uses: Milnor gets it from Hanner's theorem, which is not formalized. For the sphere and for $SU(2m)$ the retraction is constructed (V13.8, V14.21).
- The conclusion is stronger than "$\pi_i(\Omega, \Omega^d) = 0$": homotopies relative to the whole part already in $\Omega^d$, at all base points, for every compact $P$ of small dimension.
- No reparametrization $F \circ E$ is needed: Lemma 22.5 is used below a level (V13.14). Paths are functions on $\mathbb R$, so the final homotopy is corrected on paths at distance $0$.

### V13.3. The inclusion $\Omega^d \to \Omega$ on homotopy groups

*narrower* · under the retract hypothesis of V13.2 · $\pi_0$ treated like the rest

**Milnor (§22, p. 118).** It follows (from the exact sequence of the pair) that the inclusion homomorphism $\pi_i\Omega^d \to \pi_i\Omega$ is an isomorphism for $i \le \lambda_0 - 2$; it is onto for $i = \lambda_0 - 1$.

**Proved in Lean.** For a slice submanifold $N$ of a finite-dimensional inner product space $V$, with the induced metric, $p, q \in N$ and $\Omega = \Omega(N; p, q)$ with Milnor's metric (V10.1), under the hypotheses of V13.2: at every $\gamma \in \Omega^d$ the inclusion induces a bijection $\pi_i(\Omega^d, \gamma) \to \pi_i(\Omega, \gamma)$ for $i \le \lambda_0 - 2$ and a surjection for $i \le \lambda_0 - 1$, $\pi_0$ included; for $i \ge 1$ the induced map is a homomorphism, hence an isomorphism.

- `Morse.theorem_22_1_bijective` — Morse/Chapter13/Theorem22.lean, line 270
- `Morse.theorem_22_1_surjective` — Morse/Chapter13/Theorem22.lean, line 291

*What differs.*
- Inherits the hypothesis of V13.2. No exact sequence of the pair: compressing cubes gives surjectivity and compressing cylinders $I \times I^i$ injectivity.

### V13.4. Corollary 22.2

*narrower* · under the retract hypothesis of V13.2 · no connectedness of $N$ · the base point made explicit

**Milnor (§22, Corollary 22.2, p. 118).** With the hypotheses of Theorem 22.1, $\pi_i\Omega^d$ is isomorphic to $\pi_{i+1}M$ for $0 \le i \le \lambda_0 - 2$. Proof: $\pi_i\Omega^d \cong \pi_i\Omega$, and $\pi_i\Omega \cong \pi_{i+1}M$.

**Proved in Lean.** For a slice submanifold $N$ of a finite-dimensional inner product space $V$, with the induced metric, $p, q \in N$ and $\Omega = \Omega(N; p, q)$ with Milnor's metric (V10.1), under the hypotheses of V13.2: for every $\gamma \in \Omega^d$ there is a bijection $\pi_i(\Omega^d, \gamma) \cong \pi_{i+1}(N, p)$ for $i \le \lambda_0 - 2$, and a surjection $\pi_i(\Omega^d, \gamma) \to \pi_{i+1}(N, p)$ for $i \le \lambda_0 - 1$.

- `Morse.pathCHomeomorph` — Morse/Chapter13/Corollaries.lean, line 55
- `Morse.contractLoop` — Morse/Chapter13/Corollaries.lean, line 76
- `Morse.contractPath` — Morse/Chapter13/Corollaries.lean, line 105
- `Morse.corollary_22_2` — Morse/Chapter13/Corollaries.lean, line 116
- `Morse.corollary_22_2_surjective` — Morse/Chapter13/Freudenthal.lean, line 64

*What differs.*
- $\pi_i(\Omega, \gamma)$ is at a minimal geodesic while $\pi_i(\Omega M) \cong \pi_{i+1}M$ concerns the constant loop: the bijection passes through Theorem 17.1 (V10.19), $\delta \mapsto \delta\cdot\gamma^{-1}$, and a change of basepoint from $\gamma\cdot\gamma^{-1}$ to the constant loop. Using $\gamma$ itself, no connectedness of $N$ is needed.
- The surjection one degree higher is not in Milnor's 22.2; it follows from the surjectivity in V13.3.

### V13.5. Corollary 22.2 as groups; change of basepoint is a homomorphism

*narrower* · under the retract hypothesis of V13.2 · change of basepoint proved multiplicative

**Milnor (§22, Corollary 22.2, p. 118).** The isomorphisms of Corollary 22.2 are isomorphisms of groups for $i \ge 1$.

**Proved in Lean.** For a path $\omega$ from $y_0$ to $y_1$ in any space and $i \ge 1$, change of basepoint along $\omega$ is a group isomorphism $\pi_i(Y, y_0) \cong \pi_i(Y, y_1)$. For a slice submanifold $N$ of a finite-dimensional inner product space $V$, with the induced metric, $p, q \in N$ and $\Omega = \Omega(N; p, q)$ with Milnor's metric (V10.1): $\pi_{j+1}(\Omega, \gamma) \cong \pi_{j+2}(N, p)$ as groups for every $\gamma \in \Omega$; under the hypotheses of V13.2, $\pi_i(\Omega^d, \gamma) \cong \pi_{i+1}(N, p)$ as groups for $1 \le i \le \lambda_0 - 2$, with a surjective homomorphism for $1 \le i \le \lambda_0 - 1$.

- `Morse.Homotopy.evalZeroHomotopyEquiv` — Morse/Homotopy/ChangeOfBaseGroup.lean, line 59
- `Morse.Homotopy.changeBaseMap_mul` — Morse/Homotopy/ChangeOfBaseGroup.lean, line 114
- `Morse.Homotopy.changeBaseMulEquiv` — Morse/Homotopy/ChangeOfBaseGroup.lean, line 130
- `Morse.nonempty_mulEquiv_pathSp` — Morse/Chapter13/CorollaryGroups.lean, line 54
- `Morse.corollary_22_2_mulEquiv` — Morse/Chapter13/CorollaryGroups.lean, line 74
- `Morse.corollary_22_2_surjective_hom` — Morse/Chapter13/CorollaryGroups.lean, line 91

*What differs.*
- That the change of basepoint hidden in "$\pi_i\Omega \cong \pi_{i+1}M$" is a homomorphism is proved through the free path space: $(\mathrm{ev}_1)_* = c_\omega\circ(\mathrm{ev}_0)_*$ with $(\mathrm{ev}_0)_*$ onto and both evaluations homomorphisms.

### V13.6. Lemma A: the minimal geodesics between antipodes are the equator

*restated* · homeomorphic only after separation quotient · a homotopy equivalence on the nose

**Milnor (§22, proof of Corollary 22.3, p. 119).** Let $p, q = -p$ be antipodal on $S^{n+1}$. Then the space $\Omega^{\pi^2}$ of minimal geodesics from $p$ to $q$ "can be identified with" the equator $S^n$. (The exposition states this as Lemma A, with the list of all geodesics from $p$ to $-p$.)

**Proved in Lean.** On the unit sphere $S^{n+1} \subseteq \mathbb R^{n+2}$: every geodesic from $p$ to $-p$ agrees on $[0, 1]$ with $t \mapsto \cos(Lt)p + \sin(Lt)u$, $u \perp p$ a unit vector, $L = (2m + 1)\pi$, and each of these is one; every path from $p$ to $-p$ has energy $\ge \pi^2$; the paths of least energy are the semicircles $\gamma_u$ ($L = \pi$), $u$ in the equator. $u \mapsto \gamma_u$ is continuous for Milnor's metric, a homotopy equivalence from the equator to $\Omega^d$ with homotopy inverse $\gamma \mapsto \gamma(\frac12)$, and a homeomorphism of the equator onto the separation quotient of $\Omega^d$.

- `Morse.exists_eqOn_greatCircle_antipode` — Morse/Chapter13/SphereMinimal.lean, line 151
- `Morse.greatCircle_mem_pathSpace_antipode` — Morse/Chapter13/SphereMinimal.lean, line 133
- `Morse.pi_sq_le_energy_sph` — Morse/Chapter13/SphereMinimal.lean, line 177
- `Morse.equator` — Morse/Chapter13/SphereMinimal.lean, line 233
- `Morse.semicircle` — Morse/Chapter13/SphereMinimal.lean, line 241
- `Morse.exists_eqOn_semicircle` — Morse/Chapter13/SphereMinimal.lean, line 287
- `Morse.continuous_semicircle` — Morse/Chapter13/SphereMinimal.lean, line 262
- `Morse.sphMinPathsHomotopyEquiv` — Morse/Chapter13/SphereMinimal.lean, line 350
- `Morse.sphMinPathsHomeomorph` — Morse/Chapter13/SphereMinimal.lean, line 374

*What differs.*
- Paths are functions on $\mathbb R$ and Milnor's metric does not see their values off $[0, 1]$, so $\Omega^d$ is homeomorphic to the equator only after identifying paths at distance $0$; the homotopy equivalence is what the homotopy groups need.
- Continuity: all semicircles have speed $\pi$, so the $L^2$ part of Milnor's metric vanishes on them.

### V13.7. Lemma B: the index of a geodesic between antipodes

*as in the book* · the index computed exactly

**Milnor (§22, proof of Corollary 22.3, p. 119).** Every non-minimal geodesic from $p$ to $-p$ must wind one and a half times around $S^{n+1}$, and therefore has index $\ge 2n$ (it passes through two conjugate points of multiplicity $n$ in its interior).

**Proved in Lean.** The geodesic $t \mapsto \cos((2m + 1)\pi t)p + \sin((2m + 1)\pi t)u$ from $p$ to $-p$ on $S^{n+1}$ has index $2mn$; every geodesic from $p$ to $-p$ not of least energy has index $\ge 2n$.

- `Morse.formIndex_greatCircle_antipode` — Morse/Chapter13/SphereMinimal.lean, line 194
- `Morse.le_formIndex_of_not_minimal_sph` — Morse/Chapter13/SphereMinimal.lean, line 211

*What differs.*
- By the index theorem (V9.24): the parameters $j/(2m + 1)$, $1 \le j \le 2m$, each of multiplicity $n$ (V10.23); the end point $t = 1$ is conjugate but does not count.

### V13.8. The neighbourhood retraction for the sphere

*not in the book* · Hanner replaced by a formula

**Milnor (§22, proof of Corollary 22.3, p. 119).** "Evidently the hypotheses of Theorem 22.1 are satisfied with $\lambda_0 = 2n$": $\Omega^d \cong S^n$ is a manifold. No retraction is written down.

**Proved in Lean.** In $\Omega(S^{n+1}; p, -p)$, the set $O$ of paths with $\omega(\frac12) \neq \pm p$ is open and contains $\Omega^d$; $\omega \mapsto$ the semicircle through the normalized component of $\omega(\frac12)$ orthogonal to $p$, changed to the identity on $\Omega^d$, is a retraction of $O$ onto $\Omega^d$, continuous on $O$.

- `Morse.eqComp` — Morse/Chapter13/Freudenthal.lean, line 100
- `Morse.sphNbhd` — Morse/Chapter13/Freudenthal.lean, line 120
- `Morse.isOpen_sphNbhd` — Morse/Chapter13/Freudenthal.lean, line 123
- `Morse.sphRetrPath` — Morse/Chapter13/Freudenthal.lean, line 129
- `Morse.continuousOn_sphRetrPath` — Morse/Chapter13/Freudenthal.lean, line 133
- `Morse.exists_retraction_minPaths_sph` — Morse/Chapter13/Freudenthal.lean, line 172

*What differs.*
- This proves the hypothesis of V13.2 for the sphere, so Corollary 22.3 does not depend on Hanner's theorem.

### V13.9. Corollary 22.3 (Freudenthal)

*stronger* · plus onto for $i = 2n - 1$ · all base points · unconditional

**Milnor (§22, Corollary 22.3, p. 119).** $\pi_iS^n \cong \pi_{i+1}S^{n+1}$ for $i \le 2n - 2$.

**Proved in Lean.** For all $x \in S^n$, $y \in S^{n+1}$: $\pi_i(S^n, x) \cong \pi_{i+1}(S^{n+1}, y)$ for $i \le 2n - 2$ (a bijection), as groups for $1 \le i \le 2n - 2$; and for $i \le 2n - 1$ a surjection $\pi_i(S^n, x) \to \pi_{i+1}(S^{n+1}, y)$, a homomorphism for $i \ge 1$.

- `Morse.equatorHomeomorph` — Morse/Chapter13/Freudenthal.lean, line 198
- `Morse.hidx_sph` — Morse/Chapter13/Freudenthal.lean, line 222
- `Morse.hball_sph` — Morse/Chapter13/Freudenthal.lean, line 228
- `Morse.corollary_22_3` — Morse/Chapter13/Freudenthal.lean, line 234
- `Morse.corollary_22_3_surjective` — Morse/Chapter13/Freudenthal.lean, line 246
- `Morse.corollary_22_3_mulEquiv` — Morse/Chapter13/CorollaryGroups.lean, line 113
- `Morse.corollary_22_3_surjective_hom` — Morse/Chapter13/CorollaryGroups.lean, line 127

*What differs.*
- The second half of Freudenthal's theorem, the surjection for $i = 2n - 1$, is not in Milnor's 22.3; it follows from the surjectivity in V13.3 (his remark on $\pi_{\lambda_0 - 1}$).
- Unconditional: the retraction is V13.8, and the equator is $S^n$ by an isometry of $p^\perp$ with $\mathbb R^{n+1}$. That the isomorphism is the suspension homomorphism is not formalized.

### V13.10. Lemma 22.4

*stronger* · $f$ only $C^2$ · operator norms for partials · no eigenvalues

**Milnor (§22, Lemma 22.4, p. 119).** Let $K$ be a compact subset of an open $U \subseteq \mathbb R^n$ and $f : U \to \mathbb R$ smooth, all of whose critical points in $K$ have index $\ge \lambda_0$. If $g : U \to \mathbb R$ is smooth and its first and second partial derivatives are within $\varepsilon$ of those of $f$ uniformly on $K$, $\varepsilon$ small, then every critical point of $g$ in $K$ has index $\ge \lambda_0$. Proof (pp. 120–121): the $\lambda$-th eigenvalue of the Hessian is continuous, and "a uniform continuity argument which will be left to the reader".

**Proved in Lean.** Let $E$ be a finite-dimensional real normed space, $K \subseteq U \subseteq E$ with $K$ compact and $U$ open, and $f : E \to \mathbb R$ of class $C^2$ on $U$ with every critical point in $K$ of index $\ge \lambda_0$. There is $\varepsilon > 0$ such that every $g$ with $\|dg_x - df_x\| < \varepsilon$ and $\|d^2g_x - d^2f_x\| < \varepsilon$ (operator norms) at each $x \in K$ has all its critical points in $K$ of index $\ge \lambda_0$; likewise for $g = f + h$ with the first two derivatives of $h$ smaller than $\varepsilon$ on $K$.

- `Morse.exists_negDef_margin` — Morse/Chapter13/Perturbation.lean, line 68
- `Morse.le_index_of_norm_sub_lt` — Morse/Chapter13/Perturbation.lean, line 109
- `Morse.lemma_22_4` — Morse/Chapter13/Perturbation.lean, line 125
- `Morse.lemma_22_4_add` — Morse/Chapter13/Perturbation.lean, line 215

*What differs.*
- Closeness is measured by operator norms of $dg - df$ and $d^2g - d^2f$, equivalent to Milnor's partial derivatives up to constants; $f$ need only be $C^2$ and may have degenerate critical points, as Theorem 22.1 needs.
- The proof uses no eigenvalues: a negative definite subspace keeps a margin $\mu$ and stays negative definite under perturbations smaller than $\mu$; compactness of $K$ is the "uniform continuity argument".

### V13.11. Lemma 22.4 on a submanifold, for linear perturbations

*narrower* · linear perturbations only

**Milnor (§22, proof of Lemma 22.5, p. 122).** In the proof of Lemma 22.5: $g$ is chosen with first and second derivatives so close to those of $f$ that Lemma 22.4 applies "in a coordinate neighbourhood" of each point of a compact set.

**Proved in Lean.** Let $N \subseteq V$ be a slice submanifold, $F : V \to \mathbb R$ smooth and $K \subseteq N$ compact, with every critical point of $F|N$ in $K$ of index $\ge \lambda_0$. There is $\delta > 0$ such that for every linear form $a$ on $V$ with $\|a\| < \delta$, every critical point of $(F + a)|N$ in $K$ has index $\ge \lambda_0$.

- `Morse.exists_perturb_slice` — Morse/Chapter13/Perturbation.lean, line 245
- `Morse.lemma_22_4_submanifold` — Morse/Chapter13/Perturbation.lean, line 333

*What differs.*
- Only linear perturbations: those by which Corollary 6.8 (V4.22) produces Morse functions, which is what Lemma 22.5 needs. Finitely many slice charts cover $K$.

### V13.12. Pushing maps, and pushing off cells

*not in the book* · replaces $\pi_r(X, A) = 0$ · push-off lemma of cellular approximation

**Milnor (§22, proof of Lemma 22.5, p. 122).** "Since $r < \lambda_0$ it follows that $h$ is homotopic within $(M^c, M^0)$ to a map $h'$ into $g^{-1}(-\infty, 2\delta]$": maps of dimension below $\lambda_0$ can be pushed off cells of dimension $\ge \lambda_0$.

**Proved in Lean.** $A$ pushes maps from $P$ out of $X$ ($A, X \subseteq T$) if every map $P \to T$ with values in $X$ is homotopic in $T$, relative to the preimage of $A$, to a map into $A$. This is transitive and monotone; a strong deformation retract pushes maps from every $P$; and if $T$ is Hausdorff, $A$ closed, $P$ compact with a continuous injection into a real vector space of dimension $d$, and $e_1, \dots, e_k$ are disjoint embedded closed cells of dimensions $> d$ meeting $A$ exactly in their boundary spheres, then $A$ pushes maps from $P$ out of $A \cup e_1 \cup \dots \cup e_k$.

- `Morse.PushesInto` — Morse/Chapter13/Compression.lean, line 68
- `Morse.PushesInto.trans` — Morse/Chapter13/Compression.lean, line 80
- `Morse.PushesInto.mono` — Morse/Chapter13/Compression.lean, line 76
- `Morse.pushesInto_of_isStrongDeformationRetract` — Morse/Chapter13/Compression.lean, line 94
- `Morse.pushesInto_union_cell` — Morse/Chapter13/Compression.lean, line 131
- `Morse.pushesInto_union_cells` — Morse/Chapter13/Compression.lean, line 161

*What differs.*
- The notion replaces relative homotopy groups throughout §22. One cell is the compression lemma for attaching a cell (Hatcher, Lemma 4.10), which Milnor uses without comment.

### V13.13. Lemma D: passing critical levels of high index

*hypotheses explicit* · deformations fixing the lower level · finitely many critical points, said

**Milnor (§22, proof of Lemma 22.5, p. 122).** $g$ has only non-degenerate critical points, of index $\ge \lambda_0$, in $g^{-1}[2\delta, c + \delta]$; so $g^{-1}(-\infty, c + \delta]$ has the homotopy type of $g^{-1}(-\infty, 2\delta]$ with cells of dimension $\ge \lambda_0$ attached.

**Proved in Lean.** Let $N \subseteq V$ be a slice submanifold, $F : V \to \mathbb R$ smooth, $f = F|N$, $f^{-1}(-\infty, a_0]$ compact, $a$ a regular value, and every critical point $q$ with $a < f(q) \le a_0$ non-degenerate of index $\ge \lambda_0$. For $P$ compact injected into a real vector space of dimension $< \lambda_0$ and $a \le b < a_0$, $N^a$ pushes maps from $P$ out of $N^b$.

- `Morse.exists_gap_of_finite` — Morse/Chapter13/Compression.lean, line 216
- `Morse.lemma_D` — Morse/Chapter13/Compression.lean, line 232

*What differs.*
- A homotopy type alone would not do: the argument needs the deformations of Theorem 3.1 and Remark 3.3 (V2.3, V2.9), which fix the lower level, and V13.12 for the cells.
- The critical points above $a$ are finitely many: isolated in a compact set, and not accumulating at the regular level $a$. Milnor does not say so.

### V13.14. Lemma 22.5

*narrower* · the neighbourhood $U$ assumed (no Hanner) · one compact sublevel set suffices

**Milnor (§22, Lemma 22.5, p. 121).** Let $f : M \to \mathbb R$ be smooth with minimum $0$ and each $M^c = f^{-1}[0, c]$ compact. If the set $M^0$ of minimal points is a manifold and every critical point in $M - M^0$ has index $\ge \lambda_0$, then $\pi_r(M, M^0) = 0$ for $0 \le r < \lambda_0$. Proof (pp. 121–122): by Hanner, $M^0$ is a retract of a neighbourhood $U$ which deforms into $M^0$; a smooth approximation $g$ of $f$ pushes $h$ into $U$.

**Proved in Lean.** Let $N \subseteq V$ be a slice submanifold, $F$ smooth, $f = F|N \ge d$, $M^0 = f^{-1}(d)$, $P$ compact injected into a real vector space of dimension $< \lambda_0$, and $U \supseteq M^0$ open with $M^0$ pushing maps from $P$ out of $U$ (e.g. $U$ deforms into $M^0$ fixing it). (i) If $f^{-1}(-\infty, a_0]$ is compact and the critical points with $d < f < a_0$ have index $\ge \lambda_0$, $M^0$ pushes maps from $P$ out of $f^{-1}(-\infty, b]$ for every $b < a_0$. (ii) With all sublevel sets compact and every critical point off $M^0$ of index $\ge \lambda_0$, $M^0$ pushes maps from $P$ out of $N$.

- `Morse.pushesInto_of_deformation` — Morse/Chapter13/ManifoldOfMinima.lean, line 67
- `Morse.criticalPoint_hessianM_congr` — Morse/Chapter13/ManifoldOfMinima.lean, line 88
- `Morse.lemma_22_5_sublevel` — Morse/Chapter13/ManifoldOfMinima.lean, line 120
- `Morse.lemma_22_5` — Morse/Chapter13/ManifoldOfMinima.lean, line 319

*What differs.*
- The conclusion of Milnor's first step (Hanner's theorem plus short geodesics) is a hypothesis.
- Milnor's $g$ lives on the compact $M^{c + 2\delta}$, too little for Theorems 3.1 and 3.2; here $g = F + \rho\ell$ with $\ell$ a small linear form making $(F + \ell)|N$ Morse and $\rho$ a bump function, and the lower level is chosen regular ($2\delta$ might be critical). $M^0$ compact is implicit in the book.

### V13.15. Deforming a neighbourhood of the minimal geodesics

*hypotheses explicit* · the tube lemma, said · the retraction transported to break points

**Milnor (§22, proof of Lemma 22.5, p. 121).** "$M^0$ is a retract of some neighborhood $U$ … taking $U$ small, we may assume that each point of $U$ is joined to its image under the retraction by a unique minimal geodesic; hence $U$ can be deformed into $M^0$ within $M$."

**Proved in Lean.** In the finite-dimensional model of Chapter 10 (a broken-geodesic setup with energy bound $c$), let $N^m \cap O$, $O$ open, consist of admissible break points, and $d < c$. If $\{\gamma : E(\gamma) \le d\}$ is a retract of an open set of $\Omega$ containing it, then $\{y \in N^m \cap O : E'(y) \le d\}$ has an open neighbourhood in $N^m \cap O$ from which it pushes maps from every $P$.

- `Morse.BrokenSetup.mem_ball_of_mem_nodes` — Morse/Chapter13/MinimalDeform.lean, line 74
- `Morse.BrokenSetup.joinVec_self` — Morse/Chapter13/MinimalDeform.lean, line 80
- `Morse.BrokenSetup.exists_pushesInto_nodes` — Morse/Chapter13/MinimalDeform.lean, line 90

*What differs.*
- Each break point moves to that of the retracted path along the short geodesic of Corollary 10.8; the deformation stays in the open manifold $N^m \cap O$ near $M^0$ by the tube lemma; the retraction in $\Omega$ is transported to break points.

### V13.16. Theorem 22.1 for an open and closed set of paths

*narrower* · under the retract hypothesis of V13.2 · any open and closed set

**Milnor (§24, p. 147).** In the case $k \equiv 2 \pmod 4$ of §24: "we will need a variant of Theorem 22.1 for the component $\Omega^{(c)}$ of the path space". (The exposition states it as Lemma 6.2 of its Chapter 15.)

**Proved in Lean.** For a slice submanifold $N$ of a finite-dimensional inner product space $V$, with the induced metric, $p, q \in N$ and $\Omega = \Omega(N; p, q)$ with Milnor's metric (V10.1), under the compact-ball and retract hypotheses of V13.2, let $\Omega' \subseteq \Omega$ be open and closed with every geodesic in $\Omega'$ not of least energy of index $\ge \lambda_0$. Then every map $h : P \to \Omega'$ is homotopic, relative to $h^{-1}(\Omega^d)$, to a map into $\Omega^d \cap \Omega'$; the inclusion $\Omega^d \cap \Omega' \to \Omega'$ is bijective on $\pi_i$, $i \le \lambda_0 - 2$, and $\Omega^d \to \Omega$ is bijective on $\pi_i$, $1 \le i \le \lambda_0 - 2$, at the points of $\Omega^d \cap \Omega'$.

- `Morse.PathSp.mem_of_edist_eq_zero` — Morse/Chapter13/Componentwise.lean, line 59
- `Morse.theorem_22_1_clopen` — Morse/Chapter13/Componentwise.lean, line 71
- `Morse.compresses_clopenIncl` — Morse/Chapter13/Componentwise.lean, line 294
- `Morse.theorem_22_1_clopen_bijective` — Morse/Chapter13/Componentwise.lean, line 369
- `Morse.theorem_22_1_clopen_bijective_minPathsIncl` — Morse/Chapter13/Componentwise.lean, line 377
- `Morse.Homotopy.bijective_homotopyGroupMap_clopen` — Morse/Homotopy/BundlesUnitary.lean, line 395

*What differs.*
- Where the proof of 22.1 must see $\Omega'$ is made explicit: $r_u$ keeps a path in its component, the manifold of break points is cut down to the paths in $\Omega'$, and the last homotopy stays there. $d$ is the least energy on all of $\Omega$, and $\Omega'$ need not contain a minimal geodesic.

## Chapter 14

*Milnor §23, pp. 124–132: Bott periodicity for the unitary group*

### V14.1. $\exp A = -I$ for diagonal $A$

*narrower* · diagonal $A$ (general $A$: V14.14)

**Milnor (§23, p. 127).** For $A = \operatorname{diag}(ia_1, \dots, ia_n)$, $\exp A = \operatorname{diag}(e^{ia_1}, \dots, e^{ia_n})$, so $\exp A = -I$ iff $A = \operatorname{diag}(k_1i\pi, \dots, k_ni\pi)$ with odd integers $k_j$; a general skew-Hermitian $A$ is first conjugated to diagonal form (pp. 126–127).

**Proved in Lean.** For real $a$, $e^{ia} = -1$ iff $a$ is $\pi$ times an odd integer; so $\exp\operatorname{diag}(ia_1, \dots, ia_n) = -I$ iff every $a_j$ is an odd multiple of $\pi$.

- `Morse.exp_ofReal_mul_I_eq_neg_one_iff` — Morse/Chapter14/SUMatrices.lean, line 246
- `Morse.exp_diagonal_eq_neg_one_iff` — Morse/Chapter14/SUMatrices.lean, line 277

### V14.2. Length and trace of the velocity

*restated* · trace identities (length: V14.15)

**Milnor (§23, pp. 127, 130).** The geodesic $t \mapsto \exp tA$ has length $|A| = \sqrt{\operatorname{tr}AA^*} = \pi\sqrt{k_1^2 + \dots + k_n^2}$; $A$ lies in the Lie algebra of $SU(n)$ iff the odd $k_j$ have sum zero.

**Proved in Lean.** For integers $k_j$ and $A = \operatorname{diag}(i\pi k_j)$: $\operatorname{tr}(AA^*) = \pi^2\sum k_j^2$ and $\operatorname{tr}A = i\pi\sum k_j$.

- `Morse.suDiag` — Morse/Chapter14/SUMatrices.lean, line 73
- `Morse.trace_suDiag_mul_conjTranspose` — Morse/Chapter14/SUMatrices.lean, line 232
- `Morse.trace_suDiag` — Morse/Chapter14/SUMatrices.lean, line 242

### V14.3. Minimal geodesics, arithmetically

*restated* · minimal = least $\sum k_j^2$ (see V14.15)

**Milnor (§23, p. 127).** $A$ determines a minimal geodesic iff each $k_j = \pm1$; in $SU(2m)$ the condition $\operatorname{tr}A = 0$ makes $\operatorname{Eigen}(i\pi)$ $m$-dimensional.

**Proved in Lean.** For odd $k_1, \dots, k_n$, $\sum k_j^2 \ge n$, with equality iff every $k_j = \pm1$; if $n = 2m$, all $k_j = \pm1$ and $\sum k_j = 0$, then $m$ of them are $1$ and $m$ are $-1$.

- `Morse.card_le_sum_sq` — Morse/Chapter14/IndexCount.lean, line 389
- `Morse.sum_sq_eq_card_iff` — Morse/Chapter14/IndexCount.lean, line 395
- `Morse.card_eq_of_minimal` — Morse/Chapter14/IndexCount.lean, line 404

### V14.4. Lemma 23.1 as a statement about projections

*narrower* · sets of matrices (topology: V14.16–V14.17)

**Milnor (§23, pp. 127–128).** A minimal $A$ is completely determined by $\operatorname{Eigen}(i\pi)$, an arbitrary subspace, of dimension $m$ in $SU(2m)$.

**Proved in Lean.** A skew-Hermitian $A$ has $A^2 = -\pi^2I$ iff $A = i\pi(2P - I)$ for a Hermitian projection $P$; $\operatorname{tr}(i\pi(2P - I)) = i\pi(2\operatorname{tr}P - n)$.

- `Morse.sq_eq_neg_pi_sq_iff` — Morse/Chapter14/SUMatrices.lean, line 285
- `Morse.trace_pi_smul_projection` — Morse/Chapter14/SUMatrices.lean, line 311

*What differs.*
- "Completely determined by $\operatorname{Eigen}(i\pi)$" uses that $A$ is normal; the identity gives the projection without the spectral theorem.

### V14.5. The operator $K_A$ for diagonal $A$

*restated* · $K_A$ defined by the matrix formula

**Milnor (§23, pp. 130–131).** By Theorem 20.5 the conjugate points are determined by $K_A(W) = R(A, W)A = \frac14[[A, W], A]$; a short computation gives $K_A(W) = (\frac{\pi^2}4(k_j - k_l)^2w_{jl})$.

**Proved in Lean.** With $K_A(W) = \frac14[[A, W], A]$: for $A = \operatorname{diag}(i\pi k_j)$ the $(j, l)$ entry of $K_A(W)$ is $\frac{\pi^2}4(k_j - k_l)^2w_{jl}$.

- `Morse.jacobiMat` — Morse/Chapter14/SUMatrices.lean, line 76
- `Morse.commutator_diagonal_apply` — Morse/Chapter14/SUMatrices.lean, line 81
- `Morse.jacobiMat_suDiag_apply` — Morse/Chapter14/SUMatrices.lean, line 87

*What differs.*
- That it is $W \mapsto R(A, W)A$ for $SU(n)$ is V12.17.

### V14.6. Milnor's eigenvectors, and that they span

*narrower* · spanning, not independence

**Milnor (§23, p. 131).** A basis of the Lie algebra of $SU(n)$ of eigenvectors of $K_A$: $E_{jl}$ and $E'_{jl}$, $j < l$, with eigenvalue $\frac{\pi^2}4(k_j - k_l)^2$, and the diagonal matrices, with eigenvalue $0$.

**Proved in Lean.** $E_{jl}$ ($1$ at $(j, l)$, $-1$ at $(l, j)$) and $E'_{jl}$ ($i$ at both) are skew-Hermitian, traceless for $j \neq l$, and eigenvectors of $K_A$ with eigenvalue $\frac{\pi^2}4(k_j - k_l)^2$; diagonal matrices are in the kernel; every skew-Hermitian $W$ is its diagonal part plus $\sum_{j<l}(\operatorname{Re}w_{jl}E_{jl} + \operatorname{Im}w_{jl}E'_{jl})$.

- `Morse.eReal` — Morse/Chapter14/SUMatrices.lean, line 95
- `Morse.eImag` — Morse/Chapter14/SUMatrices.lean, line 98
- `Morse.jacobiMat_eReal` — Morse/Chapter14/SUMatrices.lean, line 101
- `Morse.jacobiMat_eImag` — Morse/Chapter14/SUMatrices.lean, line 118
- `Morse.jacobiMat_diagonal` — Morse/Chapter14/SUMatrices.lean, line 135
- `Morse.eq_diagonal_add_sum_eReal_eImag` — Morse/Chapter14/SUMatrices.lean, line 160

*What differs.*
- Milnor does not say why these vectors span; linear independence is not formalized. The formal index computation (V14.18–V14.19) needs no eigenbasis.

### V14.7. Conjugate parameters of an eigenvalue: Theorem 20.5 as a definition

*restated* · a definition · $k_j - k_l$ even, said

**Milnor (§20, Theorem 20.5, p. 110; §23, p. 131).** Each eigenvalue $e > 0$ gives conjugate points at $t = \pi/\sqrt e, 2\pi/\sqrt e, \dots$; here $t = 2/(k_j - k_l), 4/(k_j - k_l), \dots$, and the number in $(0, 1)$ is "evidently" $(k_j - k_l)/2 - 1$.

**Proved in Lean.** The conjugate parameters of $e$ are the $t \in (0, 1)$ of the form $\pi s/\sqrt e$, $s \in \mathbb Z$ (none if $e \le 0$); a finite set, equal to $\{1/d, \dots, (d - 1)/d\}$ for $e = (\pi d)^2$, $d \ge 1$.

- `Morse.conjParams` — Morse/Chapter14/IndexCount.lean, line 143
- `Morse.conjParams_finite` — Morse/Chapter14/IndexCount.lean, line 161
- `Morse.conjParams_sq` — Morse/Chapter14/IndexCount.lean, line 165
- `Morse.ncard_conjParams_sq` — Morse/Chapter14/IndexCount.lean, line 196

*What differs.*
- Theorem 20.5 is its conclusion taken as a definition; for $SU(n)$ the theorem is V14.18. "Evidently" needs $k_j - k_l$ even.

### V14.8. The index of a spectrum: Theorems 20.5 and 15.1 as a definition

*restated* · a definition (theorem for $SU(n)$: V14.19)

**Milnor (§23, p. 131).** Applying the Index Theorem and "adding over all $j, l$".

**Proved in Lean.** For a finite family $e = (e_i)$ of reals, the multiplicity of $t$ is the number of $i$ with $t$ a conjugate parameter of $e_i$, and the index of $e$ is the sum of the multiplicities; it equals $\sum_i\#\{\text{conjugate parameters of } e_i\}$; doubling every value doubles it.

- `Morse.conjMult` — Morse/Chapter14/IndexCount.lean, line 212
- `Morse.spectralIndex` — Morse/Chapter14/IndexCount.lean, line 217
- `Morse.spectralIndex_eq` — Morse/Chapter14/IndexCount.lean, line 221
- `Morse.spectralIndex_double` — Morse/Chapter14/IndexCount.lean, line 265

*What differs.*
- "Adding over all $j, l$" exchanges two finite sums.

### V14.9. The index formula from Milnor's spectrum

*restated* · index of the spectrum (geodesic: V14.19)

**Milnor (§23, p. 131).** $\lambda = \sum_{k_j > k_l}(k_j - k_l - 2)$: each pair $k_j > k_l$ gives two copies of $\frac{\pi^2}4(k_j - k_l)^2$, contributing $2((k_j - k_l)/2 - 1)$.

**Proved in Lean.** Put $\operatorname{bott}(k) = \sum_{k_i > k_j}(k_i - k_j - 2)$. For odd $k_j$, the index (V14.8) of the spectrum consisting of $\frac{\pi^2}4(k_i - k_j)^2$ for each pair $k_i > k_j$, each twice, is $\operatorname{bott}(k)$.

- `Morse.bottIndex` — Morse/Chapter14/IndexCount.lean, line 294
- `Morse.pairSpectrum` — Morse/Chapter14/IndexCount.lean, line 356
- `Morse.suSpectrum` — Morse/Chapter14/IndexCount.lean, line 366
- `Morse.two_mul_ncard_conjParams` — Morse/Chapter14/IndexCount.lean, line 340
- `Morse.spectralIndex_suSpectrum` — Morse/Chapter14/IndexCount.lean, line 371

### V14.10. Elementary properties of the index formula

*as in the book*

**Milnor (§23, pp. 130–132).** Milnor normalizes $k_1 \ge \dots \ge k_n$, treats "(say) negative" by symmetry, and notes that a minimal geodesic (all $k_j = \pm1$) has index $0$.

**Proved in Lean.** For odd $k_j$, $\operatorname{bott}(k) \ge 0$; $\operatorname{bott}(-k) = \operatorname{bott}(k)$; $\operatorname{bott}$ does not depend on the order; and it is $0$ if every $k_j = \pm1$.

- `Morse.bottIndex_nonneg` — Morse/Chapter14/IndexCount.lean, line 311
- `Morse.bottIndex_neg` — Morse/Chapter14/IndexCount.lean, line 315
- `Morse.bottIndex_comp_equiv` — Morse/Chapter14/IndexCount.lean, line 323
- `Morse.bottIndex_eq_zero_of_minimal` — Morse/Chapter14/IndexCount.lean, line 422

### V14.11. Lemma 23.2, combinatorially

*restated* · about the formula (geodesics: V14.20)

**Milnor (§23, Lemma 23.2, p. 128; proof p. 132).** Every non-minimal geodesic from $I$ to $-I$ in $SU(2m)$ has index $\ge 2m + 2$. Proof (p. 132): Case 1, at least $m + 1$ of the $k_j$ (say) negative; Case 2, $m$ of each sign, not all $\pm1$.

**Proved in Lean.** For odd $k_1, \dots, k_{2m}$ with $\sum k_j = 0$, not all $\pm1$: $\operatorname{bott}(k) \ge 2m + 2$.

- `Morse.bottIndex_ge` — Morse/Chapter14/IndexCount.lean, line 507
- `Morse.exists_pos_neg_data` — Morse/Chapter14/IndexCount.lean, line 459
- `Morse.sum_pos_neg_le_bottIndex` — Morse/Chapter14/IndexCount.lean, line 432

*What differs.*
- Both cases through the sum over pairs (positive $k_i$, negative $k_j$), reproducing Milnor's bounds $2N$ and $4m$; his "one is $\ge 3$" uses $\sum k_j = 0$.

### V14.12. Why $SU(2m)$ and not $U(n)$

*not in the book* · the hypothesis of 22.1 fails in $U(n)$

**Milnor (§23, p. 127).** The space of minimal geodesics in $U(n)$ is "rather inconvenient", having components of varying dimensions; so Milnor passes to $SU(2m)$.

**Proved in Lean.** For $k = (3, 1, \dots, 1) \in \mathbb Z^{n+1}$: $\operatorname{bott}(k) = 0$, not every $k_j = \pm1$, and $\sum k_j = n + 3$, whereas every family of entries $\pm1$ has $|\sum k_j|$ at most the number of entries.

- `Morse.remarkK` — Morse/Chapter14/IndexCount.lean, line 541
- `Morse.bottIndex_remarkK` — Morse/Chapter14/IndexCount.lean, line 547
- `Morse.not_minimal_remarkK` — Morse/Chapter14/IndexCount.lean, line 552
- `Morse.sum_remarkK` — Morse/Chapter14/IndexCount.lean, line 557
- `Morse.abs_sum_le_card_of_minimal` — Morse/Chapter14/IndexCount.lean, line 564

*What differs.*
- The exposition's stronger reason: this non-minimal geodesic has index $0$ in a component of the path space without minimal geodesics. That $\sum k_j$ is constant on components is not formalized.

### V14.13. $U(n)$ and $SU(n)$ as compact matrix groups

*restated* · regular level sets, not $\exp$ charts · $SU(n)$ via $\operatorname{Im}\det$

**Milnor (§23, pp. 124–126).** $U(n)$ is a compact smooth submanifold of $M_n(\mathbb C)$ and a Lie group, with tangent space $\mathfrak u(n)$ (skew-Hermitian matrices) at $I$ (Milnor's (5), (6), using $\exp$ near $0$ as a chart); its Lie bracket is the commutator and $\operatorname{Re}\operatorname{tr}(AB^*)$ gives a bi-invariant metric; $\det\exp A = e^{\operatorname{tr}A}$, and $SU(n)$ has Lie algebra $\mathfrak{su}(n)$.

**Proved in Lean.** $U(n)$ is a compact slice submanifold of $M_n(\mathbb C)$ modelled on $\mathfrak u(n)$, a regular level set of $A \mapsto A^*A - I$, and a matrix group (V12.14) with $\mathfrak u(n)$; for $n \ge 1$, $SU(n)$ is a compact slice submanifold modelled on $\mathfrak{su}(n)$ and a matrix group with $\mathfrak{su}(n)$. Jacobi's formula $d(\det)_A(AX) = \det A\operatorname{tr}X$, and $\det\exp(tX) = 1$ for $\operatorname{tr}X = 0$.

- `Morse.isRegularValue_unitaryMap` — Morse/Chapter12/MatrixGroups.lean, line 428
- `Morse.isSliceSubmanifold_unitaryGroup` — Morse/Chapter12/MatrixGroups.lean, line 451
- `Morse.isMatrixGroup_unitaryGroup` — Morse/Chapter12/MatrixGroups.lean, line 461
- `Morse.isCompact_unitaryGroup` — Morse/Chapter12/MatrixGroups.lean, line 489
- `Morse.isRegularValue_suMap` — Morse/Chapter12/MatrixGroups.lean, line 696
- `Morse.isSliceSubmanifold_specialUnitaryGroup` — Morse/Chapter12/MatrixGroups.lean, line 741
- `Morse.isMatrixGroup_specialUnitaryGroup` — Morse/Chapter12/MatrixGroups.lean, line 758
- `Morse.isCompact_specialUnitaryGroup` — Morse/Chapter12/MatrixGroups.lean, line 782
- `Morse.fderiv_det_mul` — Morse/Chapter12/MatrixInner.lean, line 325
- `Morse.det_exp_smul_of_trace_eq_zero` — Morse/Chapter12/MatrixInner.lean, line 351

*What differs.*
- $SU(n)$ is not a regular level set of $(A^*A - I, \det A - 1)$; it is the open piece $\operatorname{Re}\det > 0$ of the regular level set $\{A^*A = I, \operatorname{Im}\det A = 0\}$.
- Only the traceless case of $\det\exp A = e^{\operatorname{tr}A}$ is proved. That $\exp$ is onto and $SU(n)$ connected is not formalized (not needed).

### V14.14. The geodesics from $I$ to $-I$ in $SU(n)$

*as in the book* · Mathlib's spectral theorem

**Milnor (§23, pp. 126–127, 130).** A geodesic from $I$ to $-I$ is $t \mapsto \exp tA$ with $\exp A = -I$; after conjugation by a unitary $T$, $A = \operatorname{diag}(i\pi k_j)$ with odd $k_j$, and in $SU(n)$ with $\sum k_j = 0$.

**Proved in Lean.** Every geodesic of $SU(n)$ on $[0, 1]$ starting at $I$ agrees there with $t \mapsto \exp(tA)$, $A \in \mathfrak{su}(n)$. If $A \in \mathfrak{su}(n)$ and $\exp A = -I$, then $A = T\operatorname{diag}(i\pi k_j)T^*$ with $T$ unitary, $k_j$ odd and $\sum k_j = 0$; conversely such $A$ lies in $\mathfrak{su}(n)$, $\exp A = -I$, and $t \mapsto \exp(tA)$ is a geodesic from $I$ to $-I$.

- `Morse.eqOn_exp_smul_of_isUnbrokenGeodesic_su` — Morse/Chapter13/SUInstance.lean, line 50
- `Morse.exists_unitary_suDiag` — Morse/Chapter12/SUIndex.lean, line 389
- `Morse.exp_conj_suDiag` — Morse/Chapter12/SUIndex.lean, line 375
- `Morse.conj_suDiag_mem` — Morse/Chapter12/SUIndex.lean, line 361
- `Morse.mem_pathSpace_exp` — Morse/Chapter12/SUIndex.lean, line 440
- `Morse.isUnbrokenGeodesic_exp` — Morse/Chapter12/SUIndex.lean, line 448

### V14.15. The distance from $I$ to $-I$, and the minimal geodesics

*narrower* · $SU(2m)$ only, not $U(n)$ · Hopf–Rinow, said

**Milnor (§23, p. 127).** The geodesic $t \mapsto \exp tA$ has length $\pi(\sum k_j^2)^{1/2}$; it is minimal iff every $k_j = \pm1$.

**Proved in Lean.** For skew-Hermitian $A$ the length of $t \mapsto \exp(tA)$ on $[0, 1]$ is $\|A\|$, which is $\pi(\sum k_j^2)^{1/2} \ge \pi\sqrt n$ for $A = T\operatorname{diag}(i\pi k_j)T^*$, $k_j$ odd. In $SU(2m)$, $m \ge 1$: $\rho(I, -I) = \pi\sqrt{2m}$, and for $A \in \mathfrak{su}(2m)$ with $\exp A = -I$ the geodesic $t \mapsto \exp(tA)$ is minimal iff $A^2 = -\pi^2I$, iff all $k_j = \pm1$.

- `Morse.pathLength_exp_smul` — Morse/Chapter12/SUMinimal.lean, line 85
- `Morse.norm_conj_suDiag_sq` — Morse/Chapter12/SUMinimal.lean, line 80
- `Morse.pi_sqrt_card_le_norm` — Morse/Chapter12/SUMinimal.lean, line 144
- `Morse.riemDist_one_neg_one` — Morse/Chapter12/SUMinimal.lean, line 151
- `Morse.sq_conj_suDiag_iff` — Morse/Chapter12/SUMinimal.lean, line 201
- `Morse.isMinimalGeodesic_exp_iff` — Morse/Chapter12/SUMinimal.lean, line 240

*What differs.*
- That a geodesic of length $\pi\sqrt n$ is minimal needs a shortest geodesic to exist (Hopf–Rinow, in the compact group) and every geodesic from $I$ to be an $\exp(tA)$ (V12.15). Only $SU(2m)$, the case used, is treated.

### V14.16. Lemma 23.1: the velocities of the minimal geodesics form $G_m(\mathbb C^{2m})$

*restated* · minimal geodesics as initial velocities · $G_m$ as projections of trace $m$

**Milnor (§23, Lemma 23.1, p. 128).** The space of minimal geodesics from $I$ to $-I$ in $SU(2m)$ is homeomorphic to the complex Grassmann manifold $G_m(\mathbb C^{2m})$.

**Proved in Lean.** Let $|\iota| = 2m$ and $\operatorname{minVel} = \{A \in \mathfrak{su}(2m) : A^2 = -\pi^2I\}$. Then $A \in \operatorname{minVel}$ iff $\exp A = -I$ and $t \mapsto \exp(tA)$ is a minimal geodesic; and $A \mapsto \frac12(I - \frac i\pi A)$ is a homeomorphism of $\operatorname{minVel}$ onto $G_m(\mathbb C^{2m})$, the Hermitian projections of trace $m$, with inverse $P \mapsto i\pi(2P - I)$.

- `Morse.minVel` — Morse/Chapter12/SUMinimal.lean, line 302
- `Morse.grassmannian` — Morse/Chapter12/SUMinimal.lean, line 307
- `Morse.exp_eq_neg_one_of_sq` — Morse/Chapter12/SUMinimal.lean, line 312
- `Morse.mem_minVel_iff` — Morse/Chapter12/SUMinimal.lean, line 367
- `Morse.lemma_23_1` — Morse/Chapter12/SUMinimal.lean, line 419

*What differs.*
- Milnor matches the two spaces only as sets (`Exposition/Findings.md`); here the topology is that of matrices. The space of paths is V14.17.

### V14.17. Lemma 23.1 in the path space

*restated* · homeomorphic only after separation quotient · a homotopy equivalence on the nose

**Milnor (§23, Lemma 23.1, p. 128).** The space of minimal geodesics from $I$ to $-I$ in $SU(2m)$ (as a subspace of $\Omega$) is homeomorphic to $G_m(\mathbb C^{2m})$.

**Proved in Lean.** Let $|\iota| = 2m$. Every path from $I$ to $-I$ in $SU(2m)$ has energy $\ge 2m\pi^2$; for $A \in \operatorname{minVel}$, $t \mapsto \exp(tA)$ lies in $\Omega^d$, and every $\gamma \in \Omega^d$ agrees on $[0, 1]$ with one of these, $A = \pi\gamma(\frac12)$. $A \mapsto (t \mapsto \exp tA)$ is continuous for Milnor's metric and is a homotopy equivalence $\operatorname{minVel} \simeq \Omega^d$ (inverse $\gamma \mapsto \pi\gamma(\frac12)$), and a homeomorphism onto the separation quotient of $\Omega^d$.

- `Morse.exp_half_smul_of_mem_minVel` — Morse/Chapter14/MinimalPaths.lean, line 63
- `Morse.pi_sq_le_energy` — Morse/Chapter14/MinimalPaths.lean, line 129
- `Morse.expPath_mem_minPaths` — Morse/Chapter14/MinimalPaths.lean, line 155
- `Morse.exists_minVel_of_mem_minPaths` — Morse/Chapter14/MinimalPaths.lean, line 195
- `Morse.continuous_expPath` — Morse/Chapter14/MinimalPaths.lean, line 162
- `Morse.minPathsHomotopyEquiv` — Morse/Chapter14/MinimalPaths.lean, line 270
- `Morse.minVelHomeomorph` — Morse/Chapter14/MinimalPaths.lean, line 295

*What differs.*
- Paths are functions on $\mathbb R$, so $\Omega^d$ is homeomorphic to $G_m(\mathbb C^{2m})$ only after identifying paths agreeing on $[0, 1]$; the homotopy equivalence is what Theorem 23.3 uses.
- Continuity for Milnor's metric: all minimal geodesics have speed $\pi\sqrt{2m}$, so the $L^2$ part vanishes, and $\exp(A/2) = A/\pi$ recovers the velocity from the midpoint.

### V14.18. Theorem 20.5 for $SU(n)$

*narrower* · $SU(n)$ only · no eigenbasis · $T$ carried through, no reduction

**Milnor (§20, Theorem 20.5, p. 110; §23, pp. 130–131).** By Theorem 20.5 the conjugate points along $t \mapsto \exp tA$ are determined by the eigenvalues of $K_A(W) = \frac14[[A, W], A]$: an eigenvalue $e > 0$ gives conjugate points at the multiples of $\pi/\sqrt e$, the multiplicity counting the eigenvalues; "adding over all $j, l$".

**Proved in Lean.** For $A = T\operatorname{diag}(ia_j)T^* \in \mathfrak{su}(n)$, $T$ unitary, and $C \in \mathfrak{su}(n)$, $J_C(t) = e^{tA/2}T(S(t) \odot T^*CT)T^*e^{tA/2}$, with $S(t) \odot W$ the matrix of $\frac{\sin(b_{jl}t)}{b_{jl}}w_{jl}$, $b_{jl} = (a_j - a_l)/2$, is a Jacobi field along $\exp(tA)$ with $J_C(0) = 0$, $DJ_C/dt(0) = C$. The multiplicity of $t_0 \in [0, 1]$ as a parameter conjugate to $0$ is $\dim\{W \in \mathfrak{su}(n) : S(t_0) \odot W = 0\}$, which for $a = \pi k$ and $0 < t_0 < 1$ equals the multiplicity computed from Milnor's spectrum (V14.8–V14.9).

- `Morse.jacSin` — Morse/Chapter12/SUJacobi.lean, line 50
- `Morse.hadSin` — Morse/Chapter12/SUJacobi.lean, line 116
- `Morse.suSol` — Morse/Chapter12/SUJacobi.lean, line 230
- `Morse.suSol_ode` — Morse/Chapter12/SUJacobi.lean, line 258
- `Morse.suJac` — Morse/Chapter12/SUJacobi.lean, line 316
- `Morse.isJacobiField_suJac` — Morse/Chapter12/SUJacobi.lean, line 326
- `Morse.covAlong_suJac_zero` — Morse/Chapter12/SUJacobi.lean, line 335
- `Morse.hadKer` — Morse/Chapter12/SUIndex.lean, line 84
- `Morse.conjMultiplicity_su` — Morse/Chapter12/SUIndex.lean, line 277
- `Morse.finrank_hadKer` — Morse/Chapter12/SUIndex.lean, line 262

*What differs.*
- The multiplicity is the dimension of a space of Jacobi fields, so all Jacobi fields vanishing at $0$ must be described: here explicitly, entry by entry, in the frame of V12.18, and by uniqueness.
- Milnor's reduction to diagonal $A$ by an isometry fixing $\pm I$ (p. 130) is replaced by carrying $T$ through the computation.

### V14.19. The index of a geodesic from $I$ to $-I$ in $SU(n)$

*as in the book* · by the Index Theorem (V9.24)

**Milnor (§23, p. 131).** By the Index Theorem, the index of $t \mapsto \exp tA$, $0 \le t \le 1$, is $\lambda = \sum_{k_j > k_l}(k_j - k_l - 2)$.

**Proved in Lean.** For integers $k_j$ with $\sum k_j = 0$, $T$ unitary and $A = T\operatorname{diag}(i\pi k_j)T^*$ with $t \mapsto \exp(tA)$ a path from $I$ to $-I$, the index of $E_{**}$ at this geodesic is the index of Milnor's spectrum; hence every geodesic $t \mapsto \exp(tA)$ from $I$ to $-I$ in $SU(n)$ has index $\sum_{k_i > k_j}(k_i - k_j - 2)$ for its odd $k_j$ (V14.14).

- `Morse.formIndex_su_geodesic` — Morse/Chapter12/SUIndex.lean, line 472
- `Morse.index_su_eq_bottIndex` — Morse/Chapter12/SUIndex.lean, line 493

### V14.20. Lemma 23.2 for geodesics

*as in the book* · "non-minimal" as "not of least energy"

**Milnor (§23, Lemma 23.2, p. 128).** Every non-minimal geodesic from $I$ to $-I$ in $SU(2m)$ has index $\ge 2m + 2$.

**Proved in Lean.** Let $|\iota| = 2m$. A geodesic $t \mapsto \exp(tA)$ from $I$ to $-I$ in $SU(2m)$ has index $0$ if all $k_j = \pm1$ and $\ge 2m + 2$ otherwise; every geodesic of $\Omega(SU(2m); I, -I)$ not of least energy has index $\ge 2m + 2$.

- `Morse.lemma_23_2_index` — Morse/Chapter12/SUIndex.lean, line 508
- `Morse.energy_exp_smul` — Morse/Chapter13/SUInstance.lean, line 83
- `Morse.le_formIndex_of_not_minimal_su` — Morse/Chapter13/SUInstance.lean, line 96

*What differs.*
- The last clause is the index hypothesis of Theorem 22.1 (V13.2) with $\lambda_0 = 2m + 2$.

### V14.21. The neighbourhood retraction for $SU(2m)$, and Corollary 22.2 for it

*not in the book* · Hanner replaced by a spectral projection

**Milnor (§23, p. 128).** By Lemma 23.1, $\Omega^d$ is a manifold, and by Lemma 23.2 every non-minimal geodesic has index $\ge 2m + 2$; with Theorem 22.1 this gives the result. No retraction is written down.

**Proved in Lean.** Let $|\iota| = 2m$. With $Q(H)$ the spectral projection of a Hermitian $H$ onto the eigenvalues $> \frac12$ (continuous where $\frac12$ is not an eigenvalue), the paths $\omega$ for which $\frac12$ is not an eigenvalue of $H(\omega)$, the Hermitian part of $\frac12(I - i\omega(\frac12))$, and $|\operatorname{tr}Q(H(\omega)) - m| < \frac12$ form an open set $O \supseteq \Omega^d$, and $\omega \mapsto (t \mapsto \exp(t\,i\pi(2Q - I)))$, changed to the identity on $\Omega^d$, retracts $O$ onto $\Omega^d$. Hence $\pi_i(\Omega^d, \gamma) \cong \pi_{i+1}(SU(2m), I)$ for $i \le 2m$, as groups for $1 \le i \le 2m$.

- `Morse.specProj` — Morse/Chapter14/MinimalRetract.lean, line 70
- `Morse.continuousOn_specProj` — Morse/Chapter14/MinimalRetract.lean, line 89
- `Morse.hermOf` — Morse/Chapter14/MinimalRetract.lean, line 165
- `Morse.minNbhd` — Morse/Chapter14/MinimalRetract.lean, line 206
- `Morse.retrPath` — Morse/Chapter14/MinimalRetract.lean, line 244
- `Morse.exists_retraction_minPaths_su` — Morse/Chapter14/MinimalRetract.lean, line 302
- `Morse.corollary_22_2_su'` — Morse/Chapter14/MinimalRetract.lean, line 328
- `Morse.corollary_22_2_su_mulEquiv` — Morse/Chapter14/PeriodicityGroups.lean, line 55

*What differs.*
- This proves the hypothesis of V13.2 for $SU(2m)$, so Theorem 23.3 is unconditional. The trace is locally constant on projections, which keeps the rank $m$.

### V14.22. Theorem 23.3 (Bott)

*restated* · groups for $i \ge 1$, a bijection at $0$ · the inclusion statement is V13.3

**Milnor (§23, Theorem 23.3, p. 128).** The inclusion $G_m(\mathbb C^{2m}) \to \Omega(SU(2m); I, -I)$ induces isomorphisms of homotopy groups in dimensions $\le 2m$. Hence $\pi_iG_m(\mathbb C^{2m}) \cong \pi_{i+1}SU(2m)$ for $0 \le i \le 2m$.

**Proved in Lean.** Let $|\iota| = 2m$. For every $P \in G_m(\mathbb C^{2m})$ and $i \le 2m$ there is a bijection $\pi_i(G_m(\mathbb C^{2m}), P) \cong \pi_{i+1}(SU(2m), I)$, and a group isomorphism for $1 \le i \le 2m$.

- `Morse.theorem_23_3` — Morse/Chapter14/Periodicity.lean, line 62
- `Morse.theorem_23_3_mulEquiv` — Morse/Chapter14/PeriodicityGroups.lean, line 69

*What differs.*
- The isomorphism is the composite of Lemma 23.1 (V14.16), the homotopy equivalence of V14.17 and Corollary 22.2 for $SU(2m)$ (V14.21). The statement about the inclusion is V13.3 for $\Omega^d$ with $\lambda_0 = 2m + 2$, $\Omega^d$ being identified with $G_m$ by V14.16–V14.17.
- Theorem 22.1 is proved as a compression, which gives bijections; group isomorphisms in the degrees where both sides are groups need change of basepoint to be a homomorphism (V13.5).

### V14.23. Coset bundles: local sections, Stiefel manifolds, $U(m + 1) \to S^{2m+1}$

*restated* · concrete matrices, not coset spaces · Steenrod's argument proved

**Milnor (§23, pp. 128–129).** $U(m + 1)/U(m) \cong S^{2m+1}$; the complex Stiefel manifold $U(2m)/U(m)$; the fibrations $U(m) \to U(m + 1) \to S^{2m+1}$ and $U(m) \to U(2m) \to U(2m)/U(m)$, from Steenrod (a coset map with local cross-sections is a bundle).

**Proved in Lean.** An equivariant map onto a space with a transitive group action is locally trivial with fibre the fibre over $b_0$ if the orbit map at $b_0$ has a continuous local section. $U(n)$ acts transitively on the Stiefel manifold $V_k(\mathbb K^n) = \{F : F^*F = I\}$, with an explicit continuous local section near the base frame. Restricting frames to their last vectors is locally trivial with fibre a Stiefel manifold, $g \mapsto gF_0$, $U(n) \to V_k(\mathbb K^n)$, is locally trivial with fibre $U(n - k)$, and $V_1(\mathbb K^n)$ is the unit sphere, so $U(m + 1) \to S^{2m+1}$ is locally trivial with fibre $U(m)$.

- `Morse.Homotopy.exists_triv_of_orbitSection` — Morse/Homotopy/Homogeneous.lean, line 104
- `Morse.Homotopy.Stiefel` — Morse/Homotopy/Stiefel.lean, line 67
- `Morse.Homotopy.secMat_mem_unitaryGroup` — Morse/Homotopy/Stiefel.lean, line 207
- `Morse.Homotopy.secMat_mul_baseFrame` — Morse/Homotopy/Stiefel.lean, line 149
- `Morse.Homotopy.exists_unitary_smul_baseFrame` — Morse/Homotopy/Stiefel.lean, line 306
- `Morse.Homotopy.stiefelRestrict_locallyTrivial` — Morse/Homotopy/Stiefel.lean, line 428
- `Morse.Homotopy.unitaryOrbit_locallyTrivial` — Morse/Homotopy/Stiefel.lean, line 520
- `Morse.Homotopy.stiefelSphere` — Morse/Homotopy/BundlesUnitary.lean, line 176
- `Morse.Homotopy.isLocallyTrivial_sphereOrbit` — Morse/Homotopy/BundlesUnitary.lean, line 209

*What differs.*
- No coset space appears: the bundles are orbit maps between spaces of matrices, with the local section written down. Locally trivial maps are Serre fibrations with an exact homotopy sequence (Part XII).

### V14.24. The Grassmannian bundle $U(m) \to V_m \to G_m$

*restated* · projections, frame-to-span map

**Milnor (§23, p. 129).** $G_m(\mathbb C^{2m})$ can be identified with $U(2m)/U(m) \times U(m)$, and there is a fibration $U(m) \to U(2m)/U(m) \to G_m(\mathbb C^{2m})$.

**Proved in Lean.** Every $P \in G_m(\mathbb K^n)$ (Hermitian projections of trace $m$) is $FF^*$ for an orthonormal $m$-frame; $F \mapsto FF^*$, $V_m(\mathbb K^n) \to G_m(\mathbb K^n)$, is continuous, equivariant for the transitive action $P \mapsto gPg^*$, and locally trivial with fibre $U(m)$, the local section being Gram–Schmidt. The Grassmannian of Lemma 23.1 is this one.

- `Morse.Homotopy.Grassmannian` — Morse/Homotopy/Grassmannian.lean, line 125
- `Morse.Homotopy.eq_of_mul_eq_of_trace_eq` — Morse/Homotopy/Grassmannian.lean, line 102
- `Morse.Homotopy.frameSpan` — Morse/Homotopy/Grassmannian.lean, line 183
- `Morse.Homotopy.exists_frame_of_mem_grassmannian` — Morse/Homotopy/Grassmannian.lean, line 252
- `Morse.Homotopy.continuousAt_gsFrame` — Morse/Homotopy/Grassmannian.lean, line 416
- `Morse.Homotopy.exists_unitary_smul_grassBase` — Morse/Homotopy/Grassmannian.lean, line 503
- `Morse.Homotopy.frameSpan_locallyTrivial` — Morse/Homotopy/Grassmannian.lean, line 586
- `Morse.Homotopy.grassmannian_eq_Grassmannian` — Morse/Homotopy/BundlesUnitary.lean, line 309

### V14.25. Lemma 23.4: stability, and the connectivity of Stiefel manifolds

*stronger* · every $V_k(\mathbb C^n)$ · all base points

**Milnor (§23, Lemma 23.4, pp. 128–129).** $\pi_{i-1}U(m) \cong \pi_{i-1}U(m + 1) \cong \pi_{i-1}U(m + 2) \cong \cdots$ for $i \le 2m$, induced by the inclusions; $\pi_{2m}U(m) \to \pi_{2m}U(m + 1)$ is onto; and $\pi_i(U(2m)/U(m)) = 0$ for $i \le 2m$.

**Proved in Lean.** $\pi_iS^{2n-1} = 0$ for $i < 2n - 1$. $\pi_iV_k(\mathbb C^n) = 0$ for $k \le n$, $i \le 2(n - k)$. The inclusion $U(m) \to U(m + k)$, $S \mapsto \operatorname{diag}(S, I_k)$, induces bijections on $\pi_i$ for $i < 2m$ and surjections for $i \le 2m$, at every base point.

- `Morse.Homotopy.SphereConnected` — Morse/Homotopy/BundleHomotopy.lean, line 234
- `Morse.Homotopy.subsingleton_pi_stiefel` — Morse/Homotopy/BundleHomotopy.lean, line 241
- `Morse.Homotopy.unitaryInclC` — Morse/Homotopy/BundleHomotopy.lean, line 291
- `Morse.Homotopy.bijective_homotopyGroupMap_unitaryIncl` — Morse/Homotopy/BundleHomotopy.lean, line 314
- `Morse.Homotopy.sphereConnected_complex` — Morse/Homotopy/BundlesUnitary.lean, line 190
- `Morse.Homotopy.subsingleton_pi_stiefel_complex` — Morse/Homotopy/BundlesUnitary.lean, line 238
- `Morse.Homotopy.bijective_homotopyGroupMap_unitaryIncl_complex` — Morse/Homotopy/BundlesUnitary.lean, line 224
- `Morse.Homotopy.surjective_homotopyGroupMap_unitaryIncl_complex` — Morse/Homotopy/BundlesUnitary.lean, line 231

*What differs.*
- The connectivity of every Stiefel manifold, by induction on $k$ through the restriction bundles, instead of Milnor's exact-sequence argument for $U(2m)/U(m)$ alone.

### V14.26. Lemma 23.4: $\pi_iG_m(\mathbb C^{2m}) \cong \pi_{i-1}U(m)$

*restated* · groups for $i \ge 2$, a bijection at $1$ · every base point

**Milnor (§23, Lemma 23.4, p. 129).** For $1 \le i \le 2m$, $\pi_iG_m(\mathbb C^{2m}) \cong \pi_{i-1}U(m)$ (from the exact sequence of $U(m) \to U(2m)/U(m) \to G_m(\mathbb C^{2m})$).

**Proved in Lean.** For $1 \le i \le 2m$ and every $P \in G_m(\mathbb C^{2m})$ there is a bijection $\pi_i(G_m(\mathbb C^{2m}), P) \cong \pi_{i-1}(U(m), I)$, a group isomorphism for $2 \le i \le 2m$; the same for the space $\operatorname{minVel}$ of V14.16.

- `Morse.Homotopy.grassmannianEquiv` — Morse/Homotopy/BundleHomotopy.lean, line 372
- `Morse.Homotopy.grassmannianEquiv_complex` — Morse/Homotopy/BundlesUnitary.lean, line 244
- `Morse.Homotopy.nonempty_mulEquiv_grassmannian_complex` — Morse/Homotopy/BundlesUnitary.lean, line 251
- `Morse.Homotopy.grassmannianPiEquiv` — Morse/Homotopy/BundlesUnitary.lean, line 332
- `Morse.Homotopy.nonempty_mulEquiv_grassmannianPi` — Morse/Homotopy/BundlesUnitary.lean, line 340
- `Morse.Homotopy.minVelPiEquiv` — Morse/Homotopy/BundlesUnitary.lean, line 351

*What differs.*
- For $i = 1$ both sides are trivial, which is not stated separately; the isomorphism is the boundary map of the bundle, whose total space is $2m$-connected (V14.25), moved to any $P$ by a unitary motion.

### V14.27. Lemma 23.4: $\pi_jSU(m) \cong \pi_jU(m)$

*narrower* · $j \ge 2$; $j = 0$ not formalized

**Milnor (§23, Lemma 23.4, p. 129).** $\pi_jU(m) \cong \pi_jSU(m)$ for $j \neq 1$, from $SU(m) \to U(m) \to S^1$.

**Proved in Lean.** $U(n) \cong S^1 \times SU(n)$ by $g \mapsto (\det g, gD(\det g)^{-1})$; $\pi_jS^1 = 0$ for $j \ge 2$; and for $n \ge 1$ the inclusion $SU(n) \to U(n)$ induces bijections on $\pi_j$, $j \ge 2$, at every point.

- `Morse.Homotopy.unitaryProd` — Morse/Homotopy/BundlesUnitary.lean, line 530
- `Morse.Homotopy.isLocallyTrivial_detCircle` — Morse/Homotopy/BundlesUnitary.lean, line 557
- `Morse.Homotopy.subsingleton_pi_circle` — Morse/Homotopy/BundlesUnitary.lean, line 462
- `Morse.Homotopy.suInclC` — Morse/Homotopy/BundlesUnitary.lean, line 563
- `Morse.Homotopy.bijective_homotopyGroupMap_suInclC` — Morse/Homotopy/BundlesUnitary.lean, line 585

*What differs.*
- $j = 0$ (both groups connected) is not formalized and is not used.

### V14.28. The periodicity theorem

*restated* · range $1 \le i \le 2m - 2$ · no stable group $\pi_iU$ defined · groups for $i \ge 2$

**Milnor (§23, p. 129).** Periodicity theorem: $\pi_{i-1}U \cong \pi_{i+1}U$, the stable groups $\pi_jU = \pi_jU(m)$, $j \le 2m - 1$; proof: $\pi_{i-1}U(m) \cong \pi_iG_m(\mathbb C^{2m}) \cong \pi_{i+1}SU(2m) \cong \pi_{i+1}U(2m)$ for $i \le 2m$ (Lemma 23.4, Theorem 23.3, Lemma 23.4).

**Proved in Lean.** For $1 \le i \le 2m$, $\pi_{i-1}(U(m), I) \cong \pi_{i+1}(U(2m), I)$, as groups for $2 \le i \le 2m$. For $1 \le i \le 2m - 2$, $\pi_{i-1}(U(m), I) \cong \pi_{i+1}(U(m), I)$, as groups for $2 \le i \le 2m - 2$.

- `Morse.nonempty_equiv_pi_unitary_two_mul` — Morse/Chapter14/Periodicity.lean, line 79
- `Morse.periodicity_theorem` — Morse/Chapter14/Periodicity.lean, line 92
- `Morse.nonempty_mulEquiv_pi_unitary_two_mul` — Morse/Chapter14/PeriodicityGroups.lean, line 86
- `Morse.periodicity_theorem_mulEquiv` — Morse/Chapter14/PeriodicityGroups.lean, line 105

*What differs.*
- The stable group $\pi_jU$ is not defined as a limit; periodicity is stated inside one $U(m)$. Landing back in $U(m)$ from $U(2m)$ needs stability in degree $i + 1 < 2m$, hence $i \le 2m - 2$; every stable degree is reached for $m$ large.
- For $i = 1$, $\pi_0$ is a pointed set and the isomorphism a bijection.

### V14.29. Theorem 23.5 (Bott), as sets

*restated* · in the stable range of $U(m)$ · bijection with $\mathbb Z$

**Milnor (§23, Theorem 23.5, p. 130).** The stable homotopy groups of the unitary group are $\pi_0U \cong \pi_2U \cong \pi_4U \cong \cdots \cong 0$ and $\pi_1U \cong \pi_3U \cong \pi_5U \cong \cdots \cong \mathbb Z$. Proof: $U(1) = S^1$ and periodicity.

**Proved in Lean.** For $j \le 2m - 1$: $\pi_j(U(m), I)$ is trivial for even $j$ and in bijection with $\mathbb Z$ for odd $j$. On the way: $\pi_1(S^1) \cong \mathbb Z$ as sets, by the boundary map of the covering $\mathbb Z \to \mathbb R \to S^1$; $\det : U(1) \to S^1$ is a homeomorphism.

- `Morse.Homotopy.nonempty_pi_one_circle_equiv_int` — Morse/Chapter14/Periodicity.lean, line 129
- `Morse.Homotopy.unitaryOneHomeomorph` — Morse/Chapter14/Periodicity.lean, line 140
- `Morse.Homotopy.nonempty_pi_unitary_equiv_circle` — Morse/Chapter14/Periodicity.lean, line 155
- `Morse.theorem_23_5` — Morse/Chapter14/Periodicity.lean, line 170

*What differs.*
- Statements about $\pi_jU(m)$ for $j \le 2m - 1$ rather than a limit group; the odd groups as groups are V14.30.

### V14.30. Theorem 23.5 as groups

*restated* · $\pi_1S^1 \cong \mathbb Z$ proved · in the stable range of $U(m)$

**Milnor (§23, Theorem 23.5, p. 130).** $\pi_1U \cong \pi_3U \cong \pi_5U \cong \cdots$ are infinite cyclic; $\pi_1S^1 \cong \mathbb Z$ is quoted.

**Proved in Lean.** $\pi_1(S^1, 1) \cong \mathbb Z$ as groups. For $2k + 2 \le 2m$, $\pi_{2k+1}(U(m), I) \cong \mathbb Z$ as groups; in the stable range $\pi_jU(m) \cong \pi_1U(m)$ for odd $j$ and $\cong \pi_2U(m)$ for even $j \ge 2$, as groups.

- `Morse.Homotopy.piOneCircleMulEquiv` — Morse/Chapter14/CircleGroup.lean, line 56
- `Morse.Homotopy.nonempty_mulEquiv_pi_one_unitary_circle` — Morse/Chapter14/CircleGroup.lean, line 71
- `Morse.theorem_23_5_mulEquiv` — Morse/Chapter14/CircleGroup.lean, line 87
- `Morse.nonempty_mulEquiv_pi_unitary_odd` — Morse/Chapter14/PeriodicityGroups.lean, line 119
- `Morse.nonempty_mulEquiv_pi_unitary_even` — Morse/Chapter14/PeriodicityGroups.lean, line 130

*What differs.*
- $\pi_1S^1 \cong \mathbb Z$ comes from Mathlib's covering-space theory: the monodromy of $t \mapsto e^{it}$, whose deck group $2\pi\mathbb Z$ is abelian.

## Chapter 15

*Milnor §24, pp. 133–148: periodicity for the orthogonal group*

### V15.1. Complex structures

*stronger* · $n$ even is derived

**Milnor (§24, p. 133).** For $n$ even, a complex structure on $\mathbb R^n$ is a $J \in O(n)$ with $J^2 = -I$; the space of all of them is $\Omega_1(n)$. Since $JJ^* = I$ and $JJ = -I$, $J^* = -J$ (p. 135).

**Proved in Lean.** A complex structure on $\mathbb R^n$ is a matrix $J \in O(n)$ with $J^2 = -I$. Equivalently, $J^{\mathsf T} = -J$ and $J^2 = -I$. A complex structure exists only if $n$ is even, and every complex structure has $\operatorname{tr}(J^{\mathsf T}J) = n$.

- `Morse.IsComplexStructure` — Morse/Chapter15/ComplexStructure.lean, line 97
- `Morse.isComplexStructure_iff` — Morse/Chapter15/ComplexStructure.lean, line 100
- `Morse.IsComplexStructure.even_card` — Morse/Chapter15/ComplexStructure.lean, line 128
- `Morse.IsComplexStructure.trace_transpose_mul_self` — Morse/Chapter15/ComplexStructure.lean, line 138

*What differs.*
- Equivalently $J^{\mathsf T} = -J$ and $J^2 = -I$. The parity of $n$ is a conclusion.

### V15.2. $\exp(\theta J) = \cos\theta\,I + \sin\theta\,J$

*narrower* · the matrix identity only

**Milnor (§24, proof of Lemma 24.1, pp. 134–135).** In a suitable basis $\exp(\pi A)$ is block diagonal with rotation blocks; for a complex structure $J$, $\exp\pi J = -I$.

**Proved in Lean.** If $J^2 = -I$, then $\exp(\theta J) = \cos\theta\,I + \sin\theta\,J$ for every real $\theta$; in particular $\exp(\pi J) = -I$.

- `Morse.exp_smul_of_mul_self_eq_neg_one` — Morse/Chapter15/ComplexStructure.lean, line 222
- `Morse.exp_pi_smul` — Morse/Chapter15/ComplexStructure.lean, line 236

*What differs.*
- Only the identity, for every real $\theta$. That $t \mapsto \exp(\pi tJ)$ is a minimal geodesic, and Lemma 24.1 itself, are V15.24–V15.26.

### V15.3. Lemma 24.2, from Milnor's spectrum

*restated* · the spectrum is the input · geodesics: V15.30

**Milnor (§24, Lemma 24.2, p. 135).** Any non-minimal geodesic from $I$ to $-I$ in $O(2m)$ has index $\ge 2m - 2$. For $A$ with blocks $a_j\bigl(\begin{smallmatrix}0 & 1\\ -1 & 0\end{smallmatrix}\bigr)$, $a_1 \ge \dots \ge a_m > 0$ odd, the non-zero eigenvalues of $K_A$ are $(a_i + a_j)^2/4$ for $i < j$ and $(a_i - a_j)^2/4$ for $i < j$ with $a_i \neq a_j$, each counted twice; so $\lambda = \sum_{i<j}(a_i + a_j - 2) + \sum_{a_i > a_j}(a_i - a_j - 2)$.

**Proved in Lean.** For integers $a_1, \dots, a_m$ put $\lambda(a) = \sum_{i < j}(a_i + a_j - 2) + \sum_{a_i > a_j}(a_i - a_j - 2)$, the second sum over ordered pairs. Let all $a_j$ be odd and positive. (i) The index, in the sense of Chapter 14 (V14.8), of the spectrum consisting of $\tfrac{\pi^2}{4}(a_i + a_j)^2$ for $i < j$ and $\tfrac{\pi^2}{4}(a_i - a_j)^2$ for $a_i > a_j$, each counted twice, is $\lambda(a)$. (ii) If all $a_j = 1$, $\lambda(a) = 0$. (iii) If not all $a_j = 1$, $\lambda(a) \ge 2m - 2$.

- `Morse.bottIndexO` — Morse/Chapter14/IndexCount.lean, line 613
- `Morse.oSpectrum` — Morse/Chapter14/IndexCount.lean, line 618
- `Morse.spectralIndex_oSpectrum` — Morse/Chapter14/IndexCount.lean, line 624
- `Morse.bottIndexO_eq_zero` — Morse/Chapter14/IndexCount.lean, line 645
- `Morse.bottIndexO_ge` — Morse/Chapter14/IndexCount.lean, line 650

*What differs.*
- Milnor's spectrum is taken as given: its computation, and Theorem 20.5 for $O(n)$, are not formalized. The index is the count of conjugate parameters of V14.8, for the velocity $\pi A$.
- The bound for the geodesics themselves is V15.30, proved without the spectrum.

### V15.4. The spaces $\Omega_k(n)$

*stronger* · for any fixed matrices $J_\alpha$

**Milnor (§24, p. 136).** With fixed anticommuting complex structures $J_1, \dots, J_{k-1}$, $\Omega_k(n)$ is the set of all complex structures which anticommute with them. $\Omega_k(n) \subset \Omega_{k-1}(n) \subset \dots \subset \Omega_1(n) \subset O(n)$; "clearly each $\Omega_k(n)$ is a compact set"; $\Omega_0(n) = O(n)$.

**Proved in Lean.** $\Omega_0(n) = O(n)$, and for $k \ge 1$, $\Omega_k(n)$ is the set of complex structures $J$ with $J_\alpha J = -JJ_\alpha$ for $1 \le \alpha \le k - 1$. For any fixed matrices $J_\alpha$, $\Omega_{k+1}(n) \subseteq \Omega_k(n)$, and every $\Omega_k(n)$ is closed and compact. $J_1, \dots, J_k$ form an anticommuting family if each is a complex structure and $J_\alpha J_\beta = -J_\beta J_\alpha$ for $\alpha \neq \beta$; then $J_k \in \Omega_k(n)$ for $k \ge 1$.

- `Morse.Omega` — Morse/Chapter15/ComplexStructure.lean, line 144
- `Morse.omega_succ_subset` — Morse/Chapter15/ComplexStructure.lean, line 149
- `Morse.isClosed_omega` — Morse/Chapter15/ComplexStructure.lean, line 180
- `Morse.isCompact_omega` — Morse/Chapter15/ComplexStructure.lean, line 194
- `Morse.IsAnticommFamily` — Morse/Chapter15/ComplexStructure.lean, line 202
- `Morse.IsAnticommFamily.mem_omega` — Morse/Chapter15/ComplexStructure.lean, line 207

*What differs.*
- The inclusions and the compactness hold for any fixed matrices $J_\alpha$. An anticommuting family $J_1, \dots, J_k$ includes the base point $J_k \in \Omega_k(n)$.

### V15.5. Lemma 24.4: the reflection preserves $\Omega_k(n)$

*narrower* · the algebraic invariance only

**Milnor (§24, p. 136).** Each component of $\Omega_k(n)$ is a symmetric space: the isometric reflection of $O(n)$ in a point of $\Omega_k(n)$ automatically carries $\Omega_k(n)$ to itself.

**Proved in Lean.** For $k \ge 1$ and $P, J' \in \Omega_k(n)$, $-PJ'P \in \Omega_k(n)$. Since $J'^{-1} = -J'$ for a complex structure, $-PJ'P = PJ'^{-1}P$ is the image of $J'$ under $\sigma \mapsto P\sigma^{-1}P$, the reflection of $O(n)$ in $P$ (Lemma 21.1).

- `Morse.reflection_mem_omega` — Morse/Chapter15/ComplexStructure.lean, line 361

*What differs.*
- Only $-PJ'P \in \Omega_k(n)$. That the reflection is an isometry and that the components are symmetric spaces are not formalized.

### V15.6. Assertions 1 and 2, the "if" halves

*stronger* · "if" for every skew $A$ · "only if": V15.22

**Milnor (§24, Assertions 1 and 2, p. 137).** For small skew $A$: $J\exp A$ is a complex structure if and only if $A$ anticommutes with $J$ (Assertion 1); $J\exp A$ anticommutes with $J_1, \dots, J_{k-1}$ if and only if $A$ commutes with them (Assertion 2).

**Proved in Lean.** If $J$ is a complex structure and $A$ is skew with $AJ = -JA$, then $J\exp A$ is a complex structure. If $J_\alpha J = -JJ_\alpha$ and $A$ commutes with $J_\alpha$, then $J_\alpha$ anticommutes with $J\exp A$.

- `Morse.isComplexStructure_mul_exp` — Morse/Chapter15/ComplexStructure.lean, line 337
- `Morse.anticomm_mul_exp` — Morse/Chapter15/ComplexStructure.lean, line 353

*What differs.*
- The "if" halves need no smallness. The "only if" halves are V15.22.

### V15.7. From $\Omega_k(n)$ to $\Omega_{k+1}(n)$, algebraically; the Remark

*narrower* · the curve; geodesics: V15.25–V15.26

**Milnor (§24, proof of Lemma 24.4 and Remark, pp. 137–138).** For $J_k \in \Omega_k(n)$ and a complex structure $J = J_kA$ anticommuting with $J_1, \dots, J_k$, $A$ is a complex structure which anticommutes with $J_k$ and commutes with $J_1, \dots, J_{k-1}$; so $t \mapsto J_k\exp(\pi tA)$ is a geodesic from $J_k$ to $-J_k$ in $\Omega_k(n)$; and conversely. Remark: $J_kA$ is the midpoint $\gamma(\tfrac12)$.

**Proved in Lean.** Let $J_1, \dots, J_k$ ($k \ge 1$) be an anticommuting family. (i) If $J' \in \Omega_{k+1}(n)$, then $A = -J_kJ'$ ($= J_k^{-1}J'$) is a complex structure that anticommutes with $J_k$ and commutes with $J_1, \dots, J_{k-1}$, and $J' = J_kA$. (ii) Conversely, for every such $A$, $J_kA \in \Omega_{k+1}(n)$. (iii) For $J' \in \Omega_{k+1}(n)$ and every real $t$, $\cos t\,J_k + \sin t\,J' \in \Omega_k(n)$, and $J_k\exp(tA) = \cos t\,J_k + \sin t\,J'$ for $A = -J_kJ'$: the curve $t \mapsto J_k\exp(tA)$ stays in $\Omega_k(n)$, passes through $J'$ at $t = \pi/2$ and reaches $-J_k$ at $t = \pi$. (iv) A complex structure $J'$ anticommuting with a matrix $J$ satisfies $\operatorname{tr}(J'^{\mathsf T}J) = 0$.

- `Morse.omega_succ_decomp` — Morse/Chapter15/ComplexStructure.lean, line 244
- `Morse.mul_mem_omega_succ` — Morse/Chapter15/ComplexStructure.lean, line 267
- `Morse.semicircle_mem_omega` — Morse/Chapter15/ComplexStructure.lean, line 288
- `Morse.mul_exp_eq_semicircle` — Morse/Chapter15/ComplexStructure.lean, line 316
- `Morse.trace_transpose_mul_eq_zero` — Morse/Chapter15/ComplexStructure.lean, line 380

*What differs.*
- (iii) is about the curve $\cos t\,J_k + \sin t\,J'$ staying in $\Omega_k(n)$; that it is a minimal geodesic, and that all minimal geodesics arise so, are V15.25–V15.26.
- (iv), the orthogonality of $J'$ and $J$ for the trace form, is not in the book.

### V15.8. Milnor's imbedding $\Omega_k(n) \to \Omega_k(n + n')$

*narrower* · no direct limit $\Omega_k$

**Milnor (§24, p. 138).** Choose fixed anticommuting complex structures $J'_1, \dots, J'_k$ on $\mathbb R^{n'}$. Then each $J \in \Omega_k(n)$ determines a complex structure $J \oplus J'_k$ on $\mathbb R^n \oplus \mathbb R^{n'}$ which anticommutes with $J_\alpha \oplus J'_\alpha$ for $\alpha = 1, \dots, k - 1$.

**Proved in Lean.** If $J_1, \dots, J_k$ and $J'_1, \dots, J'_k$ are anticommuting families on $\mathbb R^n$ and $\mathbb R^{n'}$, the block matrices $J_\alpha \oplus J'_\alpha$ form an anticommuting family on $\mathbb R^n \oplus \mathbb R^{n'}$. For any fixed matrices and every $k$: if $P \in \Omega_k(n)$ for the $J_\alpha$ and $P' \in \Omega_k(n')$ for the $J'_\alpha$, then $P \oplus P' \in \Omega_k(n + n')$ for the $J_\alpha \oplus J'_\alpha$. With $P' = J'_k$ (V15.4) this is Milnor's map $J \mapsto J \oplus J'_k$.

- `Morse.IsAnticommFamily.fromBlocks` — Morse/Chapter15/Clifford.lean, line 241
- `Morse.fromBlocks_mem_omega` — Morse/Chapter15/Clifford.lean, line 256

*What differs.*
- $\mathbb R^{n'}$ must carry $k$ anticommuting complex structures (V15.9 supplies them for $n' = 16r'$). The direct limit $\Omega_k$ is not formed; the compatibility with $\varphi$ is V15.41.

### V15.9. Explicit anticommuting complex structures

*not in the book* · eight on every $\mathbb R^{16r}$

**Milnor (§24, pp. 136, 139).** "Assume that $n$ is divisible by a high power of $2$", and let $J_1, \dots, J_{k-1}$ be fixed complex structures which anticommute; later, $n = 16r$. The structures are never written down.

**Proved in Lean.** With $\sigma = \begin{pmatrix}0 & -1\\ 1 & 0\end{pmatrix}$, $\tau = \begin{pmatrix}1 & 0\\ 0 & -1\end{pmatrix}$, $\kappa = \begin{pmatrix}0 & 1\\ 1 & 0\end{pmatrix}$, explicit Kronecker products give one complex structure on $\mathbb R^2$ ($\sigma$), three anticommuting ones on $\mathbb R^4$ ($1 \otimes \sigma$, $\sigma \otimes \tau$, $\sigma \otimes \kappa$), seven on $\mathbb R^8$, and eight on $\mathbb R^{16}$ (the seven tensored with $\tau$, and $1 \otimes 1 \otimes 1 \otimes \sigma$). Renaming the coordinates and repeating block-diagonally ($J_\alpha \oplus \dots \oplus J_\alpha$) preserve anticommuting families; so $\mathbb R^{16r}$ carries eight anticommuting complex structures for every $r$.

- `Morse.bott4` — Morse/Chapter15/Clifford.lean, line 119
- `Morse.bott8` — Morse/Chapter15/Clifford.lean, line 129
- `Morse.bott16` — Morse/Chapter15/Clifford.lean, line 144
- `Morse.isAnticommFamily_bott2` — Morse/Chapter15/Clifford.lean, line 158
- `Morse.isAnticommFamily_bott4` — Morse/Chapter15/Clifford.lean, line 164
- `Morse.isAnticommFamily_bott8` — Morse/Chapter15/Clifford.lean, line 172
- `Morse.isAnticommFamily_bott16` — Morse/Chapter15/Clifford.lean, line 181
- `Morse.IsAnticommFamily.blockDiagonal` — Morse/Chapter15/Clifford.lean, line 222
- `Morse.IsAnticommFamily.reindex` — Morse/Chapter15/Clifford.lean, line 216
- `Morse.isAnticommFamily_bott16r` — Morse/Chapter15/Clifford.lean, line 234

*What differs.*
- Explicit Kronecker products make the standing assumptions of §24 non-vacuous for $n = 16r$ and $k \le 8$.

### V15.10. Products of anticommuting complex structures

*stronger* · the full commutation table, in any ring

**Milnor (§24, pp. 139–143).** $J_1J_2J_3$ has square $+I$ and commutes with $J_1$ and $J_2$; $J_3J_4$ anticommutes with it; the corresponding statements for $J_1J_4J_5$, $J_2J_4J_6$, $J_1J_6J_7$ and $J_7J_8$; for $k = 7$, $J_7 = \pm J_1J_2J_3J_4J_5J_6$. Stated without computation.

**Proved in Lean.** In any ring, call $J_1, \dots, J_k$ Clifford if $J_\alpha^2 = -1$ and $J_\alpha J_\beta = -J_\beta J_\alpha$ for $\alpha \neq \beta$ ($1 \le \alpha, \beta \le k$); an anticommuting family of matrices is Clifford. Put $\theta_3 = J_1J_2J_3$, $\theta_5 = J_1J_4J_5$, $\theta_6 = J_2J_4J_6$, $\theta_7 = J_1J_6J_7$ and $\omega_7 = J_1J_2\cdots J_7$. Then, whenever $k$ is large enough for the indices involved: $\theta_3^2 = 1$, $\theta_3$ commutes with $J_1, J_2, J_3$ and anticommutes with $J_\alpha$ for $4 \le \alpha \le k$; $J_3J_4$ anticommutes with $\theta_3$ and commutes with $J_1, J_2$; $\theta_5^2 = 1$, $\theta_5$ commutes with $J_1, J_4, J_5, \theta_3$ and anticommutes with $J_2, J_3$; $\theta_6^2 = 1$, $\theta_6$ commutes with $J_2, J_4, J_6, \theta_3, \theta_5$ and anticommutes with $J_1, J_3, J_5$; $\theta_7^2 = 1$, $\theta_7$ commutes with $J_1, J_6, J_7, \theta_3, \theta_5, \theta_6$ and anticommutes with $J_2, \dots, J_5$; $J_7J_8$ commutes with $\theta_3, \theta_5, \theta_6$ and anticommutes with $\theta_7$; $\omega_7 = -\theta_3\theta_5\theta_7$, and it commutes with $J_1, \dots, J_7$.

- `Morse.IsClifford` — Morse/Chapter15/Relations.lean, line 62
- `Morse.IsAnticommFamily.isClifford` — Morse/Chapter15/Clifford.lean, line 200
- `Morse.θ₃_spec` — Morse/Chapter15/Relations.lean, line 119
- `Morse.θ₃_anticommute` — Morse/Chapter15/Relations.lean, line 123
- `Morse.θ₅_spec` — Morse/Chapter15/Relations.lean, line 129
- `Morse.θ₆_spec` — Morse/Chapter15/Relations.lean, line 141
- `Morse.θ₇_spec` — Morse/Chapter15/Relations.lean, line 154
- `Morse.J₃J₄_spec` — Morse/Chapter15/Relations.lean, line 175
- `Morse.J₇J₈_spec` — Morse/Chapter15/Relations.lean, line 168
- `Morse.ω₇_spec` — Morse/Chapter15/Relations.lean, line 181

*What differs.*
- Every sign Milnor uses on pp. 139–143, proved once in an arbitrary ring.

### V15.11. Lemma 24.6, the odd steps (3), (5), (6), (7)

*narrower* · bijections with involutions

**Milnor (§24, Lemma 24.6 (3), (5), (6), (7), pp. 139–141).** $\Omega_3(16r)$ is the quaternionic Grassmann manifold of $\mathbb H^{4r}$, through the $+1$-eigenspace $V_1$ of $J_1J_2J_3$; $\Omega_5(16r)$ the subspaces $W \subset V_1$ closed under $J_1$ with $V_1 = W \oplus J_2W$; $\Omega_6(16r)$ the real subspaces $X \subset W$ with $W = X \oplus J_1X$; $\Omega_7(16r)$ the real Grassmann manifold of $X \cong \mathbb R^{2r}$.

**Proved in Lean.** Let $J_1, \dots, J_k$ be an anticommuting family and $1 \le a < b \le k$. For $J' \in \Omega_{k+1}(n)$, $\theta = J_aJ_bJ'$ is symmetric with $\theta^2 = I$, commutes with $J_a$ and $J_b$, and anticommutes with every other $J_c$, $c \le k$. Conversely, for every such $\theta$, $J' = J_bJ_a\theta$ lies in $\Omega_{k+1}(n)$ and $J_aJ_bJ' = \theta$; and $J_bJ_a(J_aJ_bJ') = J'$ for every $J'$. So $J' \mapsto J_aJ_bJ'$ is a bijection of $\Omega_{k+1}(n)$ onto the symmetric involutions with this commutation pattern. With $(a, b, k) = (1, 2, 2), (1, 4, 4), (2, 4, 5), (1, 6, 6)$ it is the passage $J_3 \mapsto \theta_3$, $J_5 \mapsto \theta_5$, $J_6 \mapsto \theta_6$, $J_7 \mapsto \theta_7$ of 24.6 (3), (5), (6), (7).

- `Morse.theta_of_mem_omega` — Morse/Chapter15/ComplexStructure.lean, line 392
- `Morse.mem_omega_of_theta` — Morse/Chapter15/ComplexStructure.lean, line 422
- `Morse.mul_theta_mul` — Morse/Chapter15/ComplexStructure.lean, line 451

*What differs.*
- $J' \mapsto J_aJ_bJ'$ is a bijection of $\Omega_{k+1}(n)$ onto the symmetric involutions with the right commutation pattern. The passage from involutions to Milnor's subspaces, and the Grassmannians as spaces, are not formalized.
- Of the even steps, (8) is V15.42; (4) is covered only algebraically (V15.7).

### V15.12. Lemma 24.6, the dimensions

*stronger* · equal halves are forced

**Milnor (§24, pp. 139–141).** The splittings $V_1 \oplus V_2$, $W \oplus J_2W$, $X \oplus J_1X$, $X_1 \oplus X_2$. Milnor restricts attention to the components with $\dim_{\mathbb H}V_1 = \dim_{\mathbb H}V_2 = 2r$ and with $\dim X_1 = \dim X_2 = r$.

**Proved in Lean.** On a finite-dimensional real vector space $V$, if $\theta^2 = 1$ and an injective $P$ anticommutes with $\theta$, then $\dim V = 2\dim\{\theta = 1\}$ ($P$ exchanges the $\pm1$-eigenspaces of $\theta$). Hence, for Clifford $J_1, \dots, J_8$ on $V$, with $V_1 = \{\theta_3 = 1\}$, $W = V_1 \cap \{\theta_5 = 1\}$, $X = W \cap \{\theta_6 = 1\}$ and $X_1 = X \cap \{\theta_7 = 1\}$: $\dim V = 2\dim V_1 = 4\dim W = 8\dim X = 16\dim X_1$, the halvings being effected by $J_4$, $J_2$, $J_1$ and $J_7J_8$. For $\mathbb R^{16r}$ with the structures of V15.9, $\dim V_1 = 8r$, $\dim W = 4r$, $\dim X = 2r$ and $\dim X_1 = r$.

- `Morse.eigV₁` — Morse/Chapter15/CliffordModules.lean, line 279
- `Morse.eigW` — Morse/Chapter15/CliffordModules.lean, line 282
- `Morse.eigX` — Morse/Chapter15/CliffordModules.lean, line 285
- `Morse.jointEigen` — Morse/Chapter15/CliffordModules.lean, line 288
- `Morse.finrank_eq_two_mul_of_anticomm` — Morse/Chapter15/CliffordModules.lean, line 143
- `Morse.finrank_chain` — Morse/Chapter15/CliffordModules.lean, line 337
- `Morse.finrank_eq_sixteen_mul` — Morse/Chapter15/CliffordModules.lean, line 345
- `Morse.finrank_jointEigen_bott16r` — Morse/Chapter15/CliffordModules.lean, line 420

*What differs.*
- An invertible map anticommuting with an involution exchanges its eigenspaces. So once the later structures exist the halves are equal, and the restriction to components is automatic: the dimensions are $8r$, $4r$, $2r$, $r$.

### V15.13. Minimal spaces and the numbers $m_k$

*restated* · $m_k$ defined by the table

**Milnor (§24, p. 143).** $V$ is a minimal $(J_1, \dots, J_k)$-space if no proper, non-trivial subspace is closed under the action of $J_1, \dots, J_k$. $m_k$ is the dimension of a minimal space: $m_0, \dots, m_8 = 1, 2, 4, 4, 8, 8, 8, 8, 16$, and for $k > 8$ "it can be shown that $m_k = 16m_{k-8}$".

**Proved in Lean.** A real vector space $V$ with linear maps $J_1, J_2, \dots$ is minimal for $J_1, \dots, J_k$ if $V \neq 0$ and every subspace closed under $J_1, \dots, J_k$ is $0$ or $V$. The numbers $m_k$ are defined by the table $m_0, \dots, m_8 = 1, 2, 4, 4, 8, 8, 8, 8, 16$ and $m_{k+8} = 16m_k$.

- `Morse.IsMinimalCliffordModule` — Morse/Chapter15/CliffordModules.lean, line 524
- `Morse.milnorM` — Morse/Chapter15/Clifford.lean, line 285

*What differs.*
- $m_k$ is defined by the table and the recursion; that it is the dimension of every minimal space is V15.16, for $k \le 8$.

### V15.14. $m_k$ divides the dimension, and is the least one

*narrower* · $k \le 8$ · every space, not only minimal ones

**Milnor (§24, p. 143).** The values $m_0, \dots, m_8$ are read off from the description of the minimal spaces: lines over $\mathbb R$, $\mathbb C$, $\mathbb H$, then $H \oplus H'$, $L$, $L \oplus L'$. For $k > 8$ "it can be shown that $m_k = 16 m_{k-8}$", and the Remark that follows (pp. 143–144) takes a space of dimension $r m_k$, for any $k$.

**Proved in Lean.** On a real vector space: one $J$ with $J^2 = -1$ makes the dimension even ($V$ is a $\mathbb C$-module); two anticommuting ones make it divisible by $4$ ($V$ is an $\mathbb H$-module, through Mathlib's quaternion algebra); four Clifford maps on a finite-dimensional $V$ make it divisible by $8$; and for $k \le 8$, Clifford $J_1, \dots, J_k$ on a finite-dimensional $V$ force $m_k \mid \dim V$. For matrices: if $\mathbb R^n$ carries $k \le 8$ anticommuting complex structures then $m_k \mid n$, and $\mathbb R^{m_k}$ carries $k$ of them; so $m_k$ is the least positive $n$ for which $\mathbb R^n$ carries $k$ anticommuting complex structures.

- `Morse.two_dvd_finrank_of_sq` — Morse/Chapter15/CliffordModules.lean, line 95
- `Morse.four_dvd_finrank_of_anticomm` — Morse/Chapter15/CliffordModules.lean, line 120
- `Morse.eight_dvd_finrank` — Morse/Chapter15/CliffordModules.lean, line 251
- `Morse.milnorM_dvd_finrank` — Morse/Chapter15/CliffordModules.lean, line 354
- `Morse.milnorM_dvd_card` — Morse/Chapter15/CliffordModules.lean, line 387
- `Morse.exists_isAnticommFamily_fin` — Morse/Chapter15/Clifford.lean, line 297
- `Morse.isLeast_milnorM` — Morse/Chapter15/CliffordModules.lean, line 408

*What differs.*
- For $k \le 8$, $m_k$ divides the dimension of every space with $k$ Clifford maps, and $\mathbb R^{m_k}$ carries $k$ anticommuting complex structures.
- Milnor's claim is for every $k$. In the formal results $m_{k+8} = 16 m_k$ is the definition of `milnorM`, not a theorem: Clifford periodicity is not formalized, so nothing is proved for $k > 8$. The cases $k \le 8$ are all that §24 uses, as Milnor says (p. 143). Relabelled from *stronger* on 2026-11-04, as the round-trip audit found.

### V15.15. The Clifford algebra

*not in the book* · Mathlib's Clifford algebra, $\dim = 2^k$

**Milnor (§24, footnote, p. 136).** These structures make $\mathbb R^n$ into a module over a suitable Clifford algebra; "the Clifford algebras will be suppressed in the following presentation".

**Proved in Lean.** Let $C_k$ be Mathlib's Clifford algebra of the quadratic form $Q(x) = -\sum x_i^2$ on $\mathbb R^k$. Clifford elements $J_1, \dots, J_k$ of a real algebra $A$ determine an algebra homomorphism $C_k \to A$ sending the $i$-th basis vector to $J_i$; $\dim C_k = 2^k$; and a minimal $(J_1, \dots, J_k)$-space has dimension at most $2^k$, being the image of $C_k$ under $c \mapsto c\cdot u$ for any $u \neq 0$.

- `Morse.cliffQ` — Morse/Chapter15/CliffordModules.lean, line 439
- `Morse.cliffordLift` — Morse/Chapter15/CliffordModules.lean, line 501
- `Morse.cliffordLift_ι` — Morse/Chapter15/CliffordModules.lean, line 507
- `Morse.finrank_cliffordAlgebra` — Morse/Chapter15/CliffordModules.lean, line 486
- `Morse.finrank_le_two_pow` — Morse/Chapter15/CliffordModules.lean, line 530

*What differs.*
- Clifford maps give a module over $C_k$, of dimension $2^k$; so a minimal space has dimension $\le 2^k$, the tool of V15.16.

### V15.16. Lemma 24.8: minimal spaces have dimension $m_k$

*narrower* · $k \le 8$ · no inner product needed

**Milnor (§24, p. 143).** A minimal space is a line over $\mathbb R$, $\mathbb C$, $\mathbb H$ for $k = 0, 1, 2$; a quaternionic line with $J_3 = \pm J_1J_2$ for $k = 3$; $H \oplus H'$ for $k = 4, 5, 6$; for $k = 7$, $J_7 = \pm J_1J_2J_3J_4J_5J_6$; $L \oplus L'$ for $k = 8$. The proof "follows that of 24.6".

**Proved in Lean.** Let $k \le 8$ and let $J_1, \dots, J_k$ be Clifford on a finite-dimensional real $V$. If $V$ is minimal, $\dim V = m_k$; conversely, if $\dim V = m_k$, $V$ is minimal; a minimal $V$ has $m_k \le \dim V \le 2^k$. An involution commuting with all $J_\alpha$ acts on a minimal space as $1$ or as $-1$; hence a minimal space for $k = 3$ (resp. $7$) is minimal for $J_1, J_2$ (resp. $J_1, \dots, J_6$), the involution being $J_1J_2J_3$ (resp. $J_1\cdots J_7$).

- `Morse.finrank_eq_milnorM_of_isMinimal` — Morse/Chapter15/MinimalModules.lean, line 563
- `Morse.isMinimal_of_finrank_eq_milnorM` — Morse/Chapter15/CliffordModules.lean, line 568
- `Morse.milnorM_le_finrank_le` — Morse/Chapter15/CliffordModules.lean, line 580
- `Morse.finrank_eq_milnorM_of_le_two` — Morse/Chapter15/CliffordModules.lean, line 588
- `Morse.central_involution` — Morse/Chapter15/MinimalModules.lean, line 496
- `Morse.minimal_three` — Morse/Chapter15/MinimalModules.lean, line 533
- `Morse.minimal_seven` — Morse/Chapter15/MinimalModules.lean, line 548

*What differs.*
- For $k \le 8$, a space with $k$ Clifford maps is minimal iff its dimension is $m_k$. The proof is a cyclic-vector argument in $C_k$, not Milnor's list of cases.
- $J_1J_2J_3$ and $J_1\cdots J_7$ act as $\pm1$ on a minimal space because they are central involutions.

### V15.17. Lemma 24.8 (Bott and Shapiro): uniqueness

*narrower* · a linear isomorphism, not an isometry · $k \le 8$

**Milnor (§24, Lemma 24.8, p. 143).** For $k \not\equiv 3 \pmod 4$, any two minimal $(J_1, \dots, J_k)$ vector spaces are isomorphic: there is an isometry between them which commutes with the action of $J_1, \dots, J_k$.

**Proved in Lean.** Let $k \le 8$ with $k \not\equiv 3 \pmod 4$, and let $V$, $V'$ be finite-dimensional real spaces with Clifford $J_1, \dots, J_k$ and $J'_1, \dots, J'_k$, both minimal. Then there is a linear isomorphism $T : V \to V'$ with $T(J_\alpha v) = J'_\alpha(Tv)$ for all $\alpha \le k$ and $v \in V$.

- `Morse.exists_iso_of_isMinimal` — Morse/Chapter15/MinimalModules.lean, line 597
- `Morse.cyclicMap` — Morse/Chapter15/MinimalModules.lean, line 203
- `Morse.range_cyclicMap_eq_top` — Morse/Chapter15/MinimalModules.lean, line 223
- `Morse.minimal_of_fixed` — Morse/Chapter15/MinimalModules.lean, line 311
- `Morse.exists_iso_of_equiv` — Morse/Chapter15/MinimalModules.lean, line 580

*What differs.*
- A linear isomorphism commuting with the $J_\alpha$, for $k \le 8$; no inner product is used. The isometric form would follow by polar decomposition, which is not formalized.

### V15.18. Vector fields on spheres

*narrower* · the identities; no Hurwitz–Radon count

**Milnor (§24, Remark, pp. 143–144).** For anticommuting $J_1, \dots, J_k$ on a space of dimension $rm_k$ and each unit vector $u$, the $k$ vectors $J_1u, \dots, J_ku$ are perpendicular to each other and to $u$: $k$ linearly independent vector fields on an $(rm_k - 1)$-sphere; $3$ on a $(4r - 1)$-sphere, $7$ on an $(8r - 1)$-sphere, $8$ on a $(16r - 1)$-sphere (Hurwitz and Radon; Adams: best possible).

**Proved in Lean.** If $J_1, \dots, J_k$ are anticommuting complex structures on $\mathbb R^n$, then for every $u$, $\langle J_\alpha u, J_\beta u\rangle = \delta_{\alpha\beta}|u|^2$ and $\langle J_\alpha u, u\rangle = 0$; so for $|u| = 1$ the $J_\alpha u$ are $k$ orthonormal vectors tangent to the unit sphere at $u$. This is written out for the eight structures of V15.9 on $\mathbb R^{16r}$ (eight fields on $S^{16r-1}$), and the general statement applies to the block-diagonal families on $\mathbb R^{4r}$ and $\mathbb R^{8r}$ built from V15.9 (three and seven fields).

- `Morse.IsAnticommFamily.dotProduct_mulVec` — Morse/Chapter15/Clifford.lean, line 353
- `Morse.IsComplexStructure.dotProduct_mulVec_self` — Morse/Chapter15/Clifford.lean, line 333
- `Morse.bott16r_vectorFields` — Morse/Chapter15/Clifford.lean, line 362

*What differs.*
- The orthonormality identities, written out for the eight structures on $\mathbb R^{16r}$. The general count and Adams's theorem are not formalized.

### V15.19. The index count for $k \not\equiv 2 \pmod 4$, from the spectrum

*restated* · the eigenvalues are the input · geodesics: V15.30

**Milnor (§24, Assertions, pp. 145–146).** $K_A$ has at least $s - 1$ eigenvalues which are $\ge (3 + 1)^2/4 = 4$. Each eigenvalue $e^2$ of $K_A$ gives rise to conjugate points for $t = e^{-1}, 2e^{-1}, 3e^{-1}, \dots$; hence the index of a non-minimal geodesic from $J$ to $-J$ in $\Omega_k(n)$ is $\ge n/m_{k+1} - 1$.

**Proved in Lean.** The index of a spectrum (in the sense of Chapter 14, V14.8) is at least the number of its eigenvalues greater than $\pi^2$. Hence, for integers $a_1, \dots, a_s \ge 1$ with some $a_{h_0} \ge 3$, the $s - 1$ eigenvalues $\tfrac{\pi^2}{4}(a_{h_0} + a_j)^2$, $j \neq h_0$, already have index at least $s - 1$.

- `Morse.card_lt_le_spectralIndex` — Morse/Chapter14/IndexCount.lean, line 247
- `Morse.card_sub_one_le_spectralIndex` — Morse/Chapter14/IndexCount.lean, line 693

*What differs.*
- A count: each eigenvalue greater than $\pi^2$ (for the velocity $\pi A$) contributes at least one to the index. The eigenvalues are input; the bound for geodesics is V15.30.
- Oddness of the $a_j$ is not needed.

### V15.20. The index count for $k \equiv 2 \pmod 4$, from the spectrum

*value differs* · $4\lambda \ge r - |c|$, both signs · geodesics: V15.38

**Milnor (§24, pp. 147–148).** On a fixed component, $a_1, \dots, a_r$ are odd with sum $c$ and $\max|a_h| \ge 3$, and $2\lambda \ge \sum_{a_h > a_j}(a_h - a_j - 2)$. "Suppose for example that some $a_h$ is equal to $-3$": then $4\lambda \ge 2p \ge r + c$, where $r = n/m_k$.

**Proved in Lean.** Let $a_1, \dots, a_r$ be odd integers, some $|a_h| \ge 3$, and $c = \sum_h a_h$. Then $\sum_{a_h > a_j}(a_h - a_j - 2) \ge (r - |c|)/2$; equivalently, the index (V14.8) of the spectrum with one eigenvalue $\tfrac{\pi^2}{4}(a_h - a_j)^2$ for each pair $a_h > a_j$ is at least $(r - |c|)/4$.

- `Morse.card_sub_abs_sum_le_two_mul_bottIndex` — Morse/Chapter14/IndexCount.lean, line 574
- `Morse.card_sub_abs_sum_le_four_mul_spectralIndex` — Morse/Chapter14/IndexCount.lean, line 596

*What differs.*
- Milnor treats only the example of an $a_h$ equal to $-3$, and his strict inequality fails when no $a_h$ is positive (e.g. $a = (-1, -3)$). The formal bound $4\lambda \ge r - |c|$ covers both signs of the large $|a_h|$.
- The eigenvalues are input; the bound for geodesics is V15.38.

### V15.21. Totally geodesic sets of orthogonal matrices

*restated* · the geodesics are listed directly · no comparison with $O(n)$

**Milnor (§24, footnote, p. 136; p. 137).** A submanifold of a Riemannian manifold is called totally geodesic if each geodesic in the submanifold is also a geodesic in the larger manifold. The description of $\Omega_k(n)$ near $J$ as the points $J\exp A$, $A$ in a linear subspace, "clearly implies" that $\Omega_k(n)$ is a totally geodesic submanifold of $O(n)$.

**Proved in Lean.** Let $N \subseteq M_n(\mathbb R)$ be a slice submanifold consisting of orthogonal matrices, and for each $x \in N$ let $T_x$ be a space of skew matrices with $\dim T_x = \dim N$, such that $x\exp A \in N$ and $A \in T_{x\exp A}$ whenever $A \in T_x$. Then: (i) the tangent space of $N$ at $x$ is $x\,T_x$; (ii) for $A \in T_x$ the curve $t \mapsto x\exp(tA)$ is a geodesic of $N$ on all of $\mathbb R$; (iii) every unbroken geodesic $\gamma \in \Omega(N; p, q)$ agrees on $[0, 1]$ with $s \mapsto p\exp(sV)$ for some $V \in T_p$; (iv) the Riemannian exponential of $N$ is $\exp_x(xA) = x\exp A$ for $A \in T_x$, and $N$ is geodesically complete. Also, as a tool for V15.23: let $S$ be a subset of a real normed space $V$ such that near each $x \in S$ there is a smooth $\Phi : Z \times W \to V$ ($Z$, $W$ finite-dimensional) with $\Phi(0) = x$ and invertible derivative at $0$, for which, near $0$, the points $\Phi(z, 0)$ lie in $S$ and every point $\Phi(q) \in S$ equals $\Phi(g(q), 0)$ with $g(q) \to 0$ as $q \to 0$; then $S$ is a slice submanifold modelled on $Z$.

- `Morse.isSliceSubmanifold_of_param` — Morse/Chapter15/TotallyGeodesic.lean, line 59
- `Morse.IsTotGeo` — Morse/Chapter15/TotallyGeodesic.lean, line 109
- `Morse.IsTotGeo.tangentSubspace_eq` — Morse/Chapter15/TotallyGeodesic.lean, line 153
- `Morse.IsTotGeo.isGeodesicOn_mul_exp_smul` — Morse/Chapter15/TotallyGeodesic.lean, line 185
- `Morse.IsTotGeo.eqOn_of_isUnbrokenGeodesic` — Morse/Chapter15/TotallyGeodesic.lean, line 268
- `Morse.IsTotGeo.exp_eq` — Morse/Chapter15/TotallyGeodesic.lean, line 244
- `Morse.IsTotGeo.isGeodesicallyComplete` — Morse/Chapter15/TotallyGeodesic.lean, line 255

*What differs.*
- What Milnor uses of "totally geodesic" is the list of geodesics: they are the curves $x\exp(tA)$, $A \in T_x$. This is proved from the normality of the acceleration $x\exp(tA)A^2$, without comparing the geodesics of $N$ with those of $O(n)$.
- The exponential map of $N$ is $xA \mapsto x\exp A$, so $N$ is complete.

### V15.22. Assertions 1 and 2 in both directions; $\Omega_k(n)$ near a point

*hypotheses explicit* · "small": the Frobenius norm · $C$ need not be assumed skew

**Milnor (§24, Assertions 1 and 2, p. 137).** For small skew $A$: $J\exp A$ is a complex structure if and only if $A$ anticommutes with $J$; $J\exp A$ anticommutes with $J_1, \dots, J_{k-1}$ if and only if $A$ commutes with them. Thus a neighborhood of $J$ in $\Omega_k(n)$ consists of all points $J\exp A$ where $A$ ranges over all small matrices in a linear subspace of the Lie algebra.

**Proved in Lean.** For a matrix $x$ let $\mathcal T_x$ be the space of skew matrices $A$ with $Ax = -xA$ and $AJ_\alpha = J_\alpha A$ for $1 \le \alpha \le k - 1$; for $k = 0$ the first condition is dropped, so that $\mathcal T_x$ is the space $\mathfrak o(n)$ of all skew matrices, the same for every $x$. (i) For any fixed matrices $J_\alpha$: if $x \in \Omega_k(n)$ and $A \in \mathcal T_x$, then $x\exp A \in \Omega_k(n)$ and $A \in \mathcal T_{x\exp A}$. (ii) There is $\varepsilon > 0$ such that $\exp$ is injective on the matrices of norm $< \varepsilon$. For every such $\varepsilon$, every anticommuting family $J_1, \dots, J_k$, every $x \in \Omega_k(n)$ and every matrix $C$ with $\|C\| < \varepsilon$: if $x\exp C \in \Omega_k(n)$, then $C \in \mathcal T_x$. (iii) Hence, for an anticommuting family and $x \in \Omega_k(n)$, there is a map $L$ with $L(y) \to 0$ as $y \to x$, such that every $y \in \Omega_k(n)$ near $x$ satisfies $L(y) \in \mathcal T_x$ and $y = x\exp(L(y))$.

- `Morse.tanAlg` — Morse/Chapter15/OmegaManifold.lean, line 156
- `Morse.mem_tanAlg` — Morse/Chapter15/OmegaManifold.lean, line 170
- `Morse.tanAlg_zero` — Morse/Chapter15/OmegaManifold.lean, line 342
- `Morse.mul_exp_mem_omega` — Morse/Chapter15/OmegaManifold.lean, line 180
- `Morse.mem_tanAlg_mul_exp` — Morse/Chapter15/OmegaManifold.lean, line 194
- `Morse.exists_exp_injective` — Morse/Chapter15/OmegaManifold.lean, line 68
- `Morse.mem_tanAlg_of_mul_exp_mem` — Morse/Chapter15/OmegaManifold.lean, line 211
- `Morse.exists_local_log` — Morse/Chapter15/OmegaManifold.lean, line 380

*What differs.*
- "Since $A$ is small" is the injectivity of $\exp$ on a ball, applied to $C^{\mathsf T}$, $x^{\mathsf T}Cx$ and $J_\alpha CJ_\alpha^{\mathsf T}$; the ball must be invariant under transposition and orthogonal conjugation, as the Frobenius ball is.
- In the converse $C$ is any small matrix with $x\exp C \in \Omega_k(n)$; that it is skew is a conclusion.

### V15.23. Lemma 24.4, first half: a smooth, totally geodesic submanifold

*restated* · stratum by stratum · in $M_n(\mathbb R)$, not in $O(n)$

**Milnor (§24, Lemma 24.4, p. 136).** Each $\Omega_k(n)$ is a smooth, totally geodesic submanifold of $O(n)$.

*p. 139: $\Omega_3(16r)$ "contains components of varying dimension"; p. 141: so does $\Omega_7(16r)$.*

**Proved in Lean.** The *stratum* of $\Omega_k(n)$ through a matrix $p$ is the set of $x \in \Omega_k(n)$ with $\dim\mathcal T_x = \dim\mathcal T_p$. (i) $\dim\mathcal T_{x\exp A} = \dim\mathcal T_x$ for $A \in \mathcal T_x$. Let $J_1, \dots, J_k$ be an anticommuting family. (ii) The stratum is open in $\Omega_k(n)$ (each of its points has a neighbourhood in $M_n(\mathbb R)$ whose points in $\Omega_k(n)$ belong to it), closed in $M_n(\mathbb R)$, and compact. (iii) It is a slice submanifold of $M_n(\mathbb R)$ modelled on $\mathcal T_p$, and it satisfies the hypotheses of V15.21 with $T_x = \mathcal T_x$. Consequently its tangent space at $x$ is $x\mathcal T_x$, its geodesics are the curves $t \mapsto x\exp(tA)$ with $A \in \mathcal T_x$, and it is geodesically complete. For $k = 0$ the stratum through any $p$ is $O(n)$.

- `Morse.omegaStratum` — Morse/Chapter15/OmegaManifold.lean, line 413
- `Morse.finrank_tanAlg_mul_exp` — Morse/Chapter15/OmegaManifold.lean, line 349
- `Morse.eventually_mem_omegaStratum` — Morse/Chapter15/OmegaManifold.lean, line 423
- `Morse.isClosed_omegaStratum` — Morse/Chapter15/OmegaManifold.lean, line 429
- `Morse.isCompact_omegaStratum` — Morse/Chapter15/OmegaManifold.lean, line 438
- `Morse.isSliceSubmanifold_omegaStratum` — Morse/Chapter15/OmegaManifold.lean, line 447
- `Morse.isTotGeo_omegaStratum` — Morse/Chapter15/OmegaManifold.lean, line 543
- `Morse.omegaStratum_zero` — Morse/Chapter15/FiniteStage.lean, line 233

*What differs.*
- $\Omega_k(n)$ is not a manifold of one dimension. The statement is for the stratum through $p$, the set where $\dim\mathcal T_x = \dim\mathcal T_p$, which is open and closed in $\Omega_k(n)$ and compact.
- It is a submanifold of the space of matrices, with tangent spaces $x\mathcal T_x$ and geodesics $x\exp(tA)$, $A \in \mathcal T_x$ (V15.21).

### V15.24. Lemma 24.1: the length of a geodesic from $I$ to $-I$

*restated* · no normal form · $V = \pi A$

**Milnor (§24, proof of Lemma 24.1, p. 134).** In the block normal form with $a_1, \dots, a_m \ge 0$: $\exp(\pi A) = -I$ if and only if $a_1, \dots, a_m$ are odd integers; $\langle A, A\rangle = 2(a_1^2 + \dots + a_m^2)$; therefore the geodesic $\exp(\pi tA)$ from $I$ to $-I$ is minimal if and only if $a_1 = \dots = a_m = 1$, and then $A^2 = -I$.

**Proved in Lean.** Let $V$ be a skew matrix with $\exp V = -I$. If $E \neq 0$ is a matrix and $V^2E = -\lambda E$ for a real $\lambda$, then $\lambda \ge \pi^2$. Hence $\|V\|^2 \ge \pi^2n$, and if $\|V\|^2 \le \pi^2n$ then $V^2 = -\pi^2I$.

- `Morse.pi_sq_le_of_sq_mul` — Morse/Chapter15/OmegaMinimal.lean, line 100
- `Morse.pi_sq_mul_card_le_norm_sq` — Morse/Chapter15/OmegaMinimal.lean, line 211
- `Morse.mul_self_eq_of_norm_sq_le` — Morse/Chapter15/OmegaMinimal.lean, line 220

*What differs.*
- For skew $V$ with $\exp V = -I$, every eigenvalue of $V^{\mathsf T}V$ is $\ge \pi^2$; so $\|V\|^2 \ge \pi^2n$, with equality only if $V^2 = -\pi^2I$. Proved by the spectral theorem and an argument with $c' = Vc$ for each eigenvalue, not by the normal form.

### V15.25. The distance from $J_k$ to $-J_k$, and the minimal geodesics

*restated* · Hopf–Rinow in the stratum · any $p$, not only $J_k$

**Milnor (§24, proof of Lemma 24.4, pp. 137–138).** $t \mapsto J_k\exp(\pi tA)$ defines a geodesic from $J_k$ to $-J_k$ in $\Omega_k(n)$; "since this geodesic is minimal in $O(n)$, it is certainly minimal in $\Omega_k(n)$". Conversely, a minimal geodesic from $J_k$ to $-J_k$ in $\Omega_k(n)$ is $J_k\exp(\pi tA)$ with $A$ a complex structure (by 24.1) which commutes with $J_1, \dots, J_{k-1}$ and anticommutes with $J_k$. Remark: $J_kA$ is the midpoint $\gamma(\tfrac12)$.

**Proved in Lean.** Let $J_1, \dots, J_k$ be an anticommuting family, $p \in \Omega_k(n)$, $N$ the stratum through $p$, and $\mathcal C_p = \{A \in \mathcal T_p : A^2 = -I\}$; suppose $\mathcal C_p \neq \emptyset$. For $A \in \mathcal C_p$ put $\gamma_A(t) = p\exp(\pi tA)$. Then: (i) $-p \in N$; (ii) the Riemannian distance in $N$ is $\rho(p, -p) = \pi\sqrt n$, and every path in $\Omega(N; p, -p)$ has energy $\ge \pi^2n$; (iii) every $\gamma_A$, $A \in \mathcal C_p$, is a path of least energy in $\Omega(N; p, -p)$, and its midpoint is $\gamma_A(\tfrac12) = pA$; (iv) every path of least energy agrees on $[0, 1]$ with $\gamma_A$ for some $A \in \mathcal C_p$.

- `Morse.minVelO` — Morse/Chapter15/OmegaMinimal.lean, line 249
- `Morse.omegaGeo` — Morse/Chapter15/OmegaMinimal.lean, line 252
- `Morse.neg_mem_omegaStratum` — Morse/Chapter15/OmegaMinimal.lean, line 271
- `Morse.riemDist_omegaStratum` — Morse/Chapter15/OmegaMinimal.lean, line 294
- `Morse.pi_sq_card_le_energy` — Morse/Chapter15/OmegaMinimal.lean, line 338
- `Morse.omegaPath_mem_minPaths` — Morse/Chapter15/OmegaMinimal.lean, line 359
- `Morse.exists_minVelO_of_mem_minPaths` — Morse/Chapter15/OmegaMinimal.lean, line 369
- `Morse.omegaGeo_half` — Morse/Chapter15/OmegaMinimal.lean, line 398

*What differs.*
- Distances in $\Omega_k(n)$ and in $O(n)$ are not compared: the stratum is complete, so a shortest geodesic exists (Hopf–Rinow, V7.26); it is $p\exp(tV)$ with $\exp V = -I$, and $\|V\| \ge \pi\sqrt n$ (V15.24).
- "Minimal" is "of least energy". The statement holds at every $p \in \Omega_k(n)$ for which some $A \in \mathcal T_p$ has $A^2 = -I$.

### V15.26. Lemma 24.1, and Lemma 24.4, second half: minimal geodesics and $\Omega_{k+1}(n)$

*restated* · homeomorphic after a quotient · a homotopy equivalence on the nose · needs $J_{k+1}$

**Milnor (§24, Lemma 24.1, p. 133; Lemma 24.4, p. 136).** The space of minimal geodesics from $I$ to $-I$ in $O(n)$ is homeomorphic to the space $\Omega_1(n)$ of complex structures on $\mathbb R^n$ (24.1). The space of minimal geodesics from $J_\ell$ to $-J_\ell$ in $\Omega_\ell(n)$ is homeomorphic to $\Omega_{\ell+1}(n)$, for $0 \le \ell < k$ (24.4).

**Proved in Lean.** Let $J_1, \dots, J_k$ be an anticommuting family, with base point $J_k$ ($J_0 = I$). (i) $A \in \mathcal C_{J_k}$ if and only if $J_kA \in \Omega_{k+1}(n)$; $A \mapsto J_kA$ is a homeomorphism of $\mathcal C_{J_k}$ onto $\Omega_{k+1}(n)$, with inverse $J' \mapsto J_k^{\mathsf T}J'$; and for $J' \in \Omega_{k+1}(n)$ and $A = J_k^{\mathsf T}J'$, $\gamma_A(t) = \cos(\pi t)\,J_k + \sin(\pi t)\,J'$ for all $t$. (ii) In the setting of V15.25, $A \mapsto \gamma_A$ is a homotopy equivalence of $\mathcal C_p$ with $\Omega^d(N; p, -p)$, and a homeomorphism of $\mathcal C_p$ onto the quotient of $\Omega^d$ in which paths at distance $0$ are identified. (iii) If $J_1, \dots, J_{k+1}$ is an anticommuting family and $N$ is the stratum of $\Omega_k(n)$ through $J_k$, the map $\varphi : \Omega_{k+1}(n) \to \Omega(N; J_k, -J_k)$, $\varphi(J')(t) = \cos(\pi t)\,J_k + \sin(\pi t)\,J'$, is continuous, and it is the inclusion $\Omega^d \to \Omega$ composed with a homotopy equivalence $\Omega_{k+1}(n) \to \Omega^d$. For $k = 0$, $N = O(n)$ and $\Omega_1(n)$ is the set of all complex structures: this is Lemma 24.1.

- `Morse.basePt` — Morse/Chapter15/OmegaMinimal.lean, line 537
- `Morse.mem_minVelO_iff` — Morse/Chapter15/OmegaMinimal.lean, line 548
- `Morse.minVelOHomeomorph` — Morse/Chapter15/OmegaMinimal.lean, line 579
- `Morse.omegaGeo_eq_semicircle` — Morse/Chapter15/OmegaMinimal.lean, line 597
- `Morse.omegaMinPathsHomotopyEquiv` — Morse/Chapter15/OmegaMinimal.lean, line 487
- `Morse.omegaMinPathsHomeomorph` — Morse/Chapter15/OmegaMinimal.lean, line 512
- `Morse.omegaPhi` — Morse/Chapter15/FiniteStage.lean, line 88
- `Morse.omegaPhi_apply` — Morse/Chapter15/FiniteStage.lean, line 94
- `Morse.isHomotopyEquiv_omegaPhi_minPaths` — Morse/Chapter15/FiniteStage.lean, line 101

*What differs.*
- The minimal directions $A$ correspond homeomorphically to the points $J' = J_kA$ of $\Omega_{k+1}(n)$, and the geodesic of $J'$ is the semicircle $\cos(\pi t)J_k + \sin(\pi t)J'$.
- Paths are functions on $\mathbb R$, so the space $\Omega^d$ of minimal paths is homotopy equivalent to $\Omega_{k+1}(n)$, and homeomorphic to it only after identifying paths that agree on $[0, 1]$. Milnor's "$0 \le \ell < k$" tacitly needs $\Omega_{\ell+1}(n) \neq \emptyset$.

### V15.27. The neighbourhood retraction for $\Omega_k(n)$

*not in the book* · Hanner replaced by polar decomposition

**Milnor (§24, pp. 135–136).** Theorem 22.1 is applied with "the statement that $\Omega_1(n)$ is a manifold" (and likewise for $\Omega_{k+1}(n)$). No retraction is written down.

**Proved in Lean.** In the setting of V15.25, $\Omega^d(N; p, -p)$ is a retract of an open neighbourhood: there are an open $O \supseteq \Omega^d$ in $\Omega(N; p, -p)$ and a map $\rho : O \to \Omega^d$, continuous on $O$ and equal to the identity on $\Omega^d$. Here, for a matrix $Y$, let $Y_1$ be the orthogonal projection of $p^{\mathsf T}Y$ onto $\mathcal T_p$; if $\det(Y_1^{\mathsf T}Y_1) \neq 0$, then $Y_1(Y_1^{\mathsf T}Y_1)^{-1/2} \in \mathcal C_p$. $O$ is the set of paths $\omega$ whose midpoint $Y = \omega(\tfrac12)$ has $\det(Y_1^{\mathsf T}Y_1) \neq 0$, an open set, and off $\Omega^d$ the retraction is $\rho(\omega) = \gamma_A$ with $A = Y_1(Y_1^{\mathsf T}Y_1)^{-1/2}$.

- `Morse.midDir` — Morse/Chapter15/OmegaRetract.lean, line 122
- `Morse.polarDir` — Morse/Chapter15/OmegaRetract.lean, line 127
- `Morse.polarDir_mem` — Morse/Chapter15/OmegaRetract.lean, line 136
- `Morse.omegaNbhd` — Morse/Chapter15/OmegaRetract.lean, line 197
- `Morse.isOpen_omegaNbhd` — Morse/Chapter15/OmegaRetract.lean, line 206
- `Morse.exists_retraction_minPaths_omega` — Morse/Chapter15/OmegaRetract.lean, line 272

*What differs.*
- This proves the hypothesis of V13.2 for every stratum: project $p^{\mathsf T}\omega(\tfrac12)$ onto $\mathcal T_p$ and take the polar part, the nearest complex structure in $\mathcal T_p$.

### V15.28. Killing fields are Jacobi fields; a lower bound for the index

*restated* · no curvature of $\Omega_k(n)$ · isometries give the Jacobi fields

**Milnor (§24, pp. 144, 146).** Since $\Omega_k(n)$ is a totally geodesic submanifold of $O(n)$, $K_A$ can be computed by $K_AB = -\tfrac14[A, [A, B]]$ on $T$. Each eigenvalue $e^2$ of $K_A$ gives rise to conjugate points for $t = e^{-1}, 2e^{-1}, 3e^{-1}, \dots$ by 20.5; then apply the index theorem.

**Proved in Lean.** Let $J_1, \dots, J_k$ be an anticommuting family, $p \in \Omega_k(n)$, $N$ the stratum through $p$, and $V \in \mathcal T_p$. The *isotropy algebra* of $p$ is the space of skew matrices commuting with $p$ and with $J_1, \dots, J_{k-1}$. (i) For $X$ in the isotropy algebra, $K(t) = X\gamma(t) - \gamma(t)X$ is a Jacobi field along $\gamma(t) = p\exp(tV)$ in $N$. (ii) Let $\gamma \in \Omega(N; p, q)$ be an unbroken geodesic equal to $t \mapsto p\exp(tV)$ on $[0, 1]$, let $\tau \in [0, 1]$, and let $\mathcal X$ be a subspace of the isotropy algebra whose elements commute with $\exp(\tau V)$ and none of whose non-zero elements commutes with $V$. Then $\gamma(\tau)$ is conjugate to $\gamma(0)$ along $\gamma$ with multiplicity (V9.4) at least $\dim\mathcal X$. (iii) For a finite set $T \subset (0, 1)$ and such subspaces $\mathcal X_\tau$, $\tau \in T$, the index of $\gamma$ is at least $\sum_{\tau \in T}\dim\mathcal X_\tau$.

- `Morse.isoAlg` — Morse/Chapter15/OmegaKilling.lean, line 68
- `Morse.killing` — Morse/Chapter15/OmegaKilling.lean, line 83
- `Morse.isJacobiField_killing` — Morse/Chapter15/OmegaKilling.lean, line 112
- `Morse.finrank_le_conjMultiplicity` — Morse/Chapter15/OmegaKilling.lean, line 206
- `Morse.sum_finrank_le_formIndex` — Morse/Chapter15/OmegaKilling.lean, line 247

*What differs.*
- Neither the curvature of the totally geodesic $\Omega_k(n)$ nor Theorem 20.5 for it is formalized. For a lower bound, Jacobi fields vanishing at $0$ and $\tau$ suffice; they are the variation fields of the isometries $y \mapsto gyg^{-1}$, $g = \exp(uX)$, for $X$ commuting with $\exp(\tau V)$.
- The index bound is then the Index Theorem (V9.24).

### V15.29. The splitting into minimal pieces; Lemma 24.8 between two pieces

*restated* · $k \le 7$ · only $c \ge 1$ is used · a linear isomorphism

**Milnor (§24, pp. 144–145).** $\mathbb R^n = M_1 \oplus \dots \oplus M_s$, mutually orthogonal subspaces closed and minimal under the action of $J_1, \dots, J_{k-1}$, $J$ and $A$. The eigenvalues of $A$ on $M_h$ "must be all equal, except for sign": $\pm ia_h$, with $a_h$ odd and positive. $J' = a_h^{-1}JA|M_h$ makes $M_h$ a minimal $(J_1, \dots, J_{k-1}, J, J')$-space, so $\dim M_h = m_{k+1}$ and $s = n/m_{k+1}$. For $h \neq j$ an isometry from $M_h$ to $\bar M_j$ "exists by 24.8".

**Proved in Lean.** Let $E$ be a finite-dimensional real inner product space and $\mathcal G$ a set of operators on $E$, each self-adjoint or skew-adjoint. A subspace is *minimal invariant* if it is non-zero, invariant under $\mathcal G$, and contains no invariant subspace other than $0$ and itself. (i) Every invariant subspace $U$ is spanned by a list of pairwise orthogonal minimal invariant subspaces of $U$ whose dimensions add up to $\dim U$; and a self-adjoint operator that commutes with $\mathcal G$ and preserves a minimal invariant $M$ is a scalar on $M$. (ii) Let $A$ be skew-adjoint, let $J, J_1, \dots, J_{k-1}$ be skew-adjoint operators with square $-1$, anticommuting with one another, and let $A$ anticommute with $J$ and commute with the $J_\alpha$ (for $k = 0$: $J = 1$ and there are no $J_\alpha$); put $\mathcal G = \{A, J, J_1, \dots, J_{k-1}\}$. On each minimal invariant $M$, $A^2 = -c$ for a real $c$; and for real $s$ with $s^2c = 1$ the restrictions of $J_1, \dots, J_{k-1}, J, sJA$ to $M$ satisfy the Clifford relations (V15.10) and make $M$ a minimal space for $k + 1$ structures (V15.13). For matrices: if $A$ is skew, $\exp(\pi A) = -I$, and $A^2 = -c$ on a non-zero subspace of $\mathbb R^n$, then $c \ge 1$. (iii) If $k \le 7$, $k \not\equiv 2 \pmod 4$, and $M_0$, $M_1$ are minimal invariant with $A^2 = -a_0^2$ on $M_0$ and $A^2 = -b^2$ on $M_1$, $a_0, b > 0$, there is a linear isomorphism $T : M_0 \to M_1$ that commutes with $J$ and the $J_\alpha$ and carries $a_0^{-1}JA$ to $-b^{-1}JA$. (iv) If moreover $c \ge 1$ on every minimal invariant subspace and $A^2 \neq -1$, then in a splitting (i) of $E$ some piece $M_0$ has $c > 1$; and there are an integer $s$ with $(s + 1)m_{k+1} = \dim E$, reals $a_0 > 1$ and $b_1, \dots, b_s \ge 1$, and operators $D_1, \dots, D_s$ on $E$ (each the projection onto $M_0$ followed by an isomorphism (iii) onto another piece) which commute with $J$ and the $J_\alpha$, satisfy $b_jD_jA = -a_0AD_j$, $A^2D_j = -b_j^2D_j$ and $D_jA^2 = -a_0^2D_j$, and for which the $AD_j$ are separated by projections (for $k = 0$ there are two for each $j$, $D_j$ and $D_jA$).

- `Morse.IsInvar` — Morse/Chapter15/InvariantSplitting.lean, line 50
- `Morse.IsMinInvar` — Morse/Chapter15/InvariantSplitting.lean, line 53
- `Morse.IsStarSigned` — Morse/Chapter15/InvariantSplitting.lean, line 57
- `Morse.exists_minInvar_decomp` — Morse/Chapter15/InvariantSplitting.lean, line 99
- `Morse.IsMinInvar.exists_scalar` — Morse/Chapter15/InvariantSplitting.lean, line 134
- `Morse.IsOmegaOps` — Morse/Chapter15/SplittingClifford.lean, line 55
- `Morse.omegaGens` — Morse/Chapter15/SplittingClifford.lean, line 71
- `Morse.IsOmegaOps.exists_sq_eq` — Morse/Chapter15/SplittingClifford.lean, line 117
- `Morse.one_le_of_minInvar` — Morse/Chapter15/IndexBound.lean, line 120
- `Morse.IsOmegaOps.isClifford_cliffFam` — Morse/Chapter15/SplittingClifford.lean, line 230
- `Morse.IsOmegaOps.isMinimal_cliffFam` — Morse/Chapter15/SplittingClifford.lean, line 263
- `Morse.IsOmegaOps.exists_inter` — Morse/Chapter15/SplittingData.lean, line 104
- `Morse.IsOmegaOps.exists_piece_gt` — Morse/Chapter15/SplittingData.lean, line 67
- `Morse.IsOmegaOps.exists_omegaPieceData` — Morse/Chapter15/SplittingData.lean, line 118

*What differs.*
- $a_h = \sqrt c$, where $A^2 = -c$ on the piece; that $a_h$ is an odd integer is not used, only $c \ge 1$. Complements of invariant subspaces are invariant because the operators are skew.
- Milnor changes the sign of $J$ on $M_j$; changing the sign of the last structure instead is equivalent and keeps $T$ commuting with $J$. $T$ is linear, not isometric, which suffices.

### V15.30. Lemma 24.2, and the index of a non-minimal geodesic for $k \not\equiv 2 \pmod 4$

*narrower* · $k \le 7$ · by Killing fields · the bound, not the formula

**Milnor (§24, Lemma 24.2, p. 135; Assertion, p. 146).** Any non-minimal geodesic from $I$ to $-I$ in $O(2m)$ has index $\ge 2m - 2$ (Lemma 24.2). For $k \not\equiv 2 \pmod 4$, the index of a non-minimal geodesic from $J$ to $-J$ in $\Omega_k(n)$ is $\ge n/m_{k+1} - 1$ (Assertion).

**Proved in Lean.** Let $J_1, \dots, J_k$ be an anticommuting family on $\mathbb R^n$ with $\mathcal C_{J_k} \neq \emptyset$ (equivalently $\Omega_{k+1}(n) \neq \emptyset$, V15.26), let $k \le 7$ and $k \not\equiv 2 \pmod 4$, and let $N$ be the stratum through $J_k$. If $\gamma \in \Omega(N; J_k, -J_k)$ is an unbroken geodesic which is not of least energy, then $m_{k+1}$ divides $n$ and the index of $\gamma$ is at least $n/m_{k+1} - 1$; for $k = 0$ it is at least $2(n/2 - 1) = n - 2$.

- `Morse.IsInterRel` — Morse/Chapter15/OmegaIntertwiners.lean, line 124
- `Morse.IsInterRel.commute_exp` — Morse/Chapter15/OmegaIntertwiners.lean, line 151
- `Morse.exists_killing_spaces` — Morse/Chapter15/OmegaIntertwiners.lean, line 185
- `Morse.exists_killing_spaces_omega` — Morse/Chapter15/IndexBound.lean, line 144
- `Morse.le_formIndex_of_not_minimal_omega` — Morse/Chapter15/IndexBound.lean, line 226
- `Morse.omega_hidx` — Morse/Chapter15/FiniteStage.lean, line 110

*What differs.*
- For $k = 0$ this is Lemma 24.2 as stated; for $1 \le k \le 7$, Milnor's Assertion. The Jacobi fields come from $X_j = D_j - D_j^{\mathsf T}$, with $D_j$ the intertwiners of V15.29, which commute with $\exp(\tau_j\pi A)$ at $\tau_j = 2/(a_0 + b_j)$; their independence, which Milnor does not discuss, is proved.
- The exact formula of Lemma 24.2 is not proved for geodesics (V15.3). "Non-minimal" is "not of least energy".

### V15.31. Theorem 24.5 for each $n$, $k \not\equiv 2 \pmod 4$

*restated* · $k \le 7$ · bijections of pointed sets · every base point

**Milnor (§24, p. 146; Theorem 24.5, p. 138).** The inclusion map $\Omega_{k+1}(n) \to \Omega\Omega_k(n)$ induces isomorphisms of homotopy groups in dimensions $\le n/m_{k+1} - 3$. (Theorem 24.5: $\pi_hO \cong \pi_{h-1}\Omega_1 \cong \pi_{h-2}\Omega_2 \cong \dots \cong \pi_1\Omega_{h-1}$.)

**Proved in Lean.** Let $J_1, \dots, J_{k+1}$ be an anticommuting family on $\mathbb R^n$, $k \le 7$, $k \not\equiv 2 \pmod 4$, let $N$ be the stratum of $\Omega_k(n)$ through $J_k$, and let $i + 2 \le n/m_{k+1} - 1$ (for $k = 0$: $i + 2 \le n - 2$). Then: (i) the inclusion $\Omega^d \to \Omega(N; J_k, -J_k)$ induces a bijection on $\pi_i$ at every minimal path; (ii) for every $J' \in \Omega_{k+1}(n)$, the map $\varphi$ of V15.26 induces a bijection $\pi_i(\Omega_{k+1}(n), J') \to \pi_i(\Omega(N; J_k, -J_k), \varphi(J'))$; (iii) for every $J' \in \Omega_{k+1}(n)$ there is a bijection $\pi_i(\Omega_{k+1}(n), J') \cong \pi_{i+1}(\Omega_k(n), J_k)$. On the way: $N$ is open and closed in $\Omega_k(n)$, and $\pi_{j+1}(N, x) \cong \pi_{j+1}(\Omega_k(n), x)$ for $x \in N$ and $j \ge 0$.

- `Morse.omega_theorem_22_1_bijective` — Morse/Chapter15/FiniteStage.lean, line 129
- `Morse.omegaPhi_bijective` — Morse/Chapter15/FiniteStage.lean, line 148
- `Morse.stratumIn` — Morse/Chapter15/FiniteStage.lean, line 166
- `Morse.isClopen_stratumIn` — Morse/Chapter15/FiniteStage.lean, line 169
- `Morse.nonempty_pi_stratum_equiv` — Morse/Chapter15/FiniteStage.lean, line 191
- `Morse.omega_pi_equiv` — Morse/Chapter15/FiniteStage.lean, line 211

*What differs.*
- Theorem 22.1 and Corollary 22.2 (V13.2–V13.4) for the stratum of $J_k$, with the retraction of V15.27 and the index bound of V15.30. The path space is that of piecewise smooth paths with Milnor's metric.
- Also $\pi_i\Omega_{k+1}(n) \cong \pi_{i+1}\Omega_k(n)$, as sets; the stratum is open and closed in $\Omega_k(n)$ and carries its higher homotopy groups.

### V15.32. Theorem 24.3 (Bott)

*restated* · bijections of pointed sets · every base point

**Milnor (§24, Theorem 24.3, p. 136).** The inclusion map $\Omega_1(n) \to \Omega O(n)$ induces isomorphisms of homotopy groups in dimensions $\le n - 4$. Hence $\pi_i\Omega_1(n) \cong \pi_{i+1}O(n)$ for $i \le n - 4$.

**Proved in Lean.** Suppose $\mathbb R^n$ carries a complex structure (so $n$ is even), and let $i + 4 \le n$. For every complex structure $J'$ on $\mathbb R^n$, the map $\varphi : \Omega_1(n) \to \Omega(O(n); I, -I)$, $\varphi(J)(t) = \cos(\pi t)\,I + \sin(\pi t)\,J$, induces a bijection on $\pi_i$ at $J'$, and there is a bijection $\pi_i(\Omega_1(n), J') \cong \pi_{i+1}(O(n), I)$.

- `Morse.theorem_24_3` — Morse/Chapter15/FiniteStage.lean, line 242

*What differs.*
- The case $k = 0$ of V15.31: the stratum is $O(n)$ itself, and the range is $i + 2 \le n - 2$. The second isomorphism is a bijection of sets, not shown to be a homomorphism.

### V15.33. Angles, and the paths with a given end angle

*not in the book* · classes open and closed

**Milnor (§24, pp. 147–148).** $f$ maps the geodesic into a closed loop on $S^1$ "which is completely determined by the trace of $A$. It follows that this trace is invariant under homotopy of the geodesic within the path space". Then: "restrict attention to some fixed component of $\Omega\Omega_k(n)$".

**Proved in Lean.** Let $F$ be a complex-valued function on a finite-dimensional real inner product space $V$ and $\omega : \mathbb R \to V$. An *angle* of $F \circ \omega$ is a continuous $\theta : [0, 1] \to \mathbb R$ with $\theta(0) = 0$ and $F(\omega(t)) = e^{i\theta(t)}$ for $t \in [0, 1]$. An angle is unique, and it exists whenever $t \mapsto F(\omega(t))$ is continuous on $[0, 1]$, of modulus $1$, with $F(\omega(0)) = 1$. For $N \subseteq V$, points $p$, $q$ and a real $w$, let $\Omega_w \subseteq \Omega(N; p, q)$ be the set of paths $\omega$ for which $F \circ \omega$ has an angle with $\theta(1) = w$. If $F$ is continuous and $|F| = 1$ on a compact set containing $N$, every $\Omega_w$ is open and closed in $\Omega(N; p, q)$; and $\Omega_w$, $\Omega_{w'}$ are disjoint for $w \neq w'$.

- `Morse.IsAngleLift` — Morse/Chapter15/Winding.lean, line 54
- `Morse.IsAngleLift.unique` — Morse/Chapter15/Winding.lean, line 58
- `Morse.exists_isAngleLift` — Morse/Chapter15/OmegaComponents.lean, line 64
- `Morse.IsAngleLift.perturb` — Morse/Chapter15/Winding.lean, line 74
- `Morse.windSet` — Morse/Chapter15/Winding.lean, line 116
- `Morse.isClopen_windSet` — Morse/Chapter15/Winding.lean, line 155
- `Morse.disjoint_windSet` — Morse/Chapter15/OmegaComponents.lean, line 92

*What differs.*
- Theorem 22.1 is applied to one class of paths, which must be open and closed in the path space (V13.16). The classes are defined by the end value of the continuous angle of $F \circ \omega$, and are open and closed for every continuous $F$ of modulus $1$.

### V15.34. The complex determinant of a real matrix

*restated* · no complex basis

**Milnor (§24, pp. 146–147).** Make $\mathbb R^n$ into an $(n/2)$-dimensional complex vector space by $iv = J_1J_2\cdots J_{k-1}v$. A unitary complex linear transformation "has a well defined complex determinant", and $f(J\exp(\pi tA)) = \det(\exp(\pi tA)) = e^{\pi t\operatorname{trace}A}$.

**Proved in Lean.** For real $n \times n$ matrices $\mathbf i$ and $M$ put $\det_{\mathbb C}M = \det(M_{\mathbb C}P_+ + P_-)$, a complex number, where $M_{\mathbb C}$ is $M$ read as a complex matrix and $P_\pm = \tfrac12(1 \mp \sqrt{-1}\,\mathbf i_{\mathbb C})$. Then $\det_{\mathbb C}I = 1$, and, if $\mathbf i^2 = -I$: $\det_{\mathbb C}(MN) = \det_{\mathbb C}M\,\det_{\mathbb C}N$ whenever $N$ commutes with $\mathbf i$; $|\det_{\mathbb C}M| = 1$ when $\mathbf i$ is skew and $M$ is orthogonal and commutes with $\mathbf i$; and $\det_{\mathbb C}\exp(tV) = e^{-\sqrt{-1}\,t\operatorname{tr}(V\mathbf i)/2}$ for every real $t$, when $V$ commutes with $\mathbf i$ and $\operatorname{tr}V = 0$.

- `Morse.cplx` — Morse/Chapter15/Winding.lean, line 177
- `Morse.projP` — Morse/Chapter15/Winding.lean, line 193
- `Morse.projM` — Morse/Chapter15/Winding.lean, line 196
- `Morse.cdet` — Morse/Chapter15/Winding.lean, line 199
- `Morse.cdet_mul` — Morse/Chapter15/Winding.lean, line 246
- `Morse.cdet_one` — Morse/Chapter15/Winding.lean, line 265
- `Morse.norm_cdet` — Morse/Chapter15/Winding.lean, line 297
- `Morse.cdet_exp` — Morse/Chapter15/Winding.lean, line 358

*What differs.*
- $\det_{\mathbb C}M = \det(M_{\mathbb C}P_+ + P_-)$, with $P_\pm$ the projections onto the $\pm\sqrt{-1}$-eigenspaces of $\mathbf i$ in $\mathbb C^n$. The complex trace of $V$ is $\tfrac12(\operatorname{tr}V - \sqrt{-1}\operatorname{tr}(V\mathbf i))$, so Milnor's $e^{\pi t\operatorname{trace}A}$ is $e^{-\sqrt{-1}\,\pi t\operatorname{tr}(A\mathbf i)/2}$.

### V15.35. Milnor's $i$ and $f$, and the classes $\Omega^{(c)}$

*restated* · $i$ axiomatized; proved for $k = 2, 6$ · $m_{k+1} = m_k$ for $k = 2, 6$

**Milnor (§24, pp. 146–148).** $iv = J_1J_2\cdots J_{k-1}v$; "the condition $k \equiv 2 \pmod 4$ guarantees that $i^2 = -1$, and that $J_1, J_2, \dots, J_{k-1}$ commute with $i$". For $J' \in \Omega_k(n)$ the composition $J^{-1}J'$ commutes with $i$, and $f(J') = \det_{\mathbb C}(J^{-1}J') \in S^1$. A component of $\Omega\Omega_k(n)$ is fixed by $\operatorname{trace}A = icm_k/2$.

**Proved in Lean.** Call a matrix $\mathbf i$ *central for $k$* if $\mathbf i^2 = -I$, $\mathbf i^{\mathsf T} = -\mathbf i$, $\mathbf i$ commutes with $J_1, \dots, J_{k-1}$ and with every matrix that commutes with all of them, and $\mathbf i$ anticommutes with every matrix that anticommutes with all of them. The product $\mathbf i = J_1J_2\cdots J_{k-1}$ is central for $k = 2$ when $J_1$ is a complex structure, and for $k = 6$ when $J_1, \dots, J_5$ is an anticommuting family. Let $\mathbf i$ be central for $k \ge 1$, $p \in \Omega_k(n)$, and $f(X) = \det_{\mathbb C}(p^{\mathsf T}X)$ (V15.34 with this $\mathbf i$). Then $|f| = 1$ on $\Omega_k(n)$, $f(p) = 1$, and $f(p\exp(tV)) = e^{-\sqrt{-1}\,t\operatorname{tr}(V\mathbf i)/2}$ for $V \in \mathcal T_p$. Now let $J_1, \dots, J_k$ be an anticommuting family, $k \ge 1$, $p = J_k$, $N$ the stratum through $J_k$, and let $\Omega_w \subseteq \Omega(N; J_k, -J_k)$ be the set of paths whose $f$-angle ends at $w$ (V15.33). Each $\Omega_w$ is open and closed, different $w$ give disjoint sets, and a path that agrees on $[0, 1]$ with $t \mapsto J_k\exp(tV)$, $V \in \mathcal T_{J_k}$, lies in $\Omega_w$ if and only if $w = -\operatorname{tr}(V\mathbf i)/2$. For an integer $c$, $\Omega^{(c)}$ denotes $\Omega_w$ with $w = \pi m_{k+1}c/2$.

- `Morse.IsCentralI` — Morse/Chapter15/OmegaWinding.lean, line 45
- `Morse.iWordM` — Morse/Chapter15/OmegaWinding.lean, line 55
- `Morse.isCentralI_two` — Morse/Chapter15/OmegaWinding.lean, line 63
- `Morse.isCentralI_six` — Morse/Chapter15/OmegaWinding.lean, line 73
- `Morse.omegaF` — Morse/Chapter15/OmegaWinding.lean, line 103
- `Morse.norm_omegaF` — Morse/Chapter15/OmegaWinding.lean, line 129
- `Morse.omegaF_self` — Morse/Chapter15/OmegaWinding.lean, line 139
- `Morse.omegaF_geo` — Morse/Chapter15/OmegaWinding.lean, line 145
- `Morse.omegaComp` — Morse/Chapter15/OmegaWinding.lean, line 157
- `Morse.isClopen_omegaComp` — Morse/Chapter15/OmegaWinding.lean, line 162
- `Morse.disjoint_omegaComp` — Morse/Chapter15/OmegaComponents.lean, line 369
- `Morse.mem_omegaComp_geo_iff` — Morse/Chapter15/OmegaWinding.lean, line 169

*What differs.*
- The properties of $i$ that are used (it commutes with everything commuting with $J_1, \dots, J_{k-1}$, and anticommutes with everything anticommuting with them) are proved for $k = 2$ and $k = 6$.
- $\Omega^{(c)}$ is the set of paths whose $f$-angle ends at $\pi m_{k+1}c/2$. It is open and closed, and contains the geodesic $J_k\exp(\pi tA)$ exactly when $-\operatorname{tr}(A\mathbf i) = m_kc$, which is Milnor's $\operatorname{trace}A = icm_k/2$.

### V15.36. Every path lies in exactly one $\Omega^{(c)}$

*not in the book* · $c$ is an integer for every path · $k = 6$: $f$ is a fourth power

**Milnor (§24, p. 148).** "Let us look only at matrices $A$ such that $\operatorname{trace}A = icm_k/2$ where $c$ is some constant integer."

**Proved in Lean.** Let $k = 2$ or $k = 6$, let $J_1, \dots, J_k$ be an anticommuting family, $\mathbf i = J_1\cdots J_{k-1}$ and $N$ the stratum through $J_k$. Every path in $\Omega(N; J_k, -J_k)$ lies in $\Omega^{(c)}$ for exactly one integer $c$. For $k = 6$ the proof uses that $f = G^4$ on $\Omega_6(n)$, where $G(X) = \det\bigl((J_6^{\mathsf T}X)_{\mathbb C}Q + 1 - Q\bigr)$ and $Q$ is the product of the projections $P_+$ of V15.34 for $\mathbf i$, $J_1J_2$ and $J_3J_4$.

- `Morse.existsUnique_mem_omegaComp` — Morse/Chapter15/OmegaComponents.lean, line 374
- `Morse.exists_mem_omegaComp_two` — Morse/Chapter15/OmegaComponents.lean, line 331
- `Morse.exists_mem_omegaComp_six` — Morse/Chapter15/OmegaComponents.lean, line 285
- `Morse.pdet` — Morse/Chapter15/OmegaComponents.lean, line 108
- `Morse.pdet_split` — Morse/Chapter15/OmegaComponents.lean, line 139
- `Morse.omegaF_eq_pow_four` — Morse/Chapter15/OmegaComponents.lean, line 260

*What differs.*
- For an arbitrary path the end angle is a multiple of $2\pi$ because $f(-J_k) = 1$ (as $4 \mid n$): Milnor's "closed loop". For $k = 6$ the normalization needs multiples of $4\pi$, which holds because $f$ is the fourth power of a continuous function on $\Omega_6(n)$.

### V15.37. The pieces for $k \equiv 2 \pmod 4$

*restated* · no complex eigenspaces · a linear isomorphism

**Milnor (§24, p. 147).** On each $M_h$ the complex linear transformation $A|M_h$ "can have only one eigenvalue, say $ia_h$", so $A|M_h$ coincides with $a_hJ_1J_2\cdots J_{k-1}|M_h$. $M_h$ is minimal under $J_1, \dots, J_{k-1}, J$, of complex dimension $m_k/2$; therefore $\operatorname{trace}A = i(a_1 + \dots + a_r)m_k/2$. By 24.8 there is an isometry $M_h \to M_j$ which commutes with $J_1, \dots, J_{k-1}$ and anticommutes with $J$.

**Proved in Lean.** In the setting of V15.29 (ii) with $k \ge 1$, let $\mathbf i = J_1\cdots J_{k-1}$ and suppose that $\mathbf i$ is skew-adjoint with $\mathbf i^2 = -1$, commutes with $A$ and the $J_\alpha$, and anticommutes with $J$. (i) On each minimal invariant $M$, $A = c\,\mathbf i$ for a real $c$. (ii) For matrices: if $\mathbf i$ is skew with $\mathbf i^2 = -I$ and commutes with $A$, $\exp(\pi A) = -I$, and $Aw = c\,\mathbf iw$ for a vector $w \neq 0$, then $c$ is an odd integer. (iii) If $k \le 7$ and the scalars $c$ of (i) are odd integers, then there are pairwise orthogonal minimal invariant subspaces $M_1, \dots, M_\nu$ of $E$ with $A = a_h\mathbf i$ on $M_h$, $a_h$ an odd integer, $\nu m_{k+1} = \dim E$, $\operatorname{tr}(A\mathbf i) = -m_{k+1}\sum_h a_h$, and $A^2 = -1$ if every $a_h = \pm1$. (iv) If $k \le 8$, $k \not\equiv 3 \pmod 4$, and $M_0$, $M_1$ are minimal invariant with $A = c_0\mathbf i$ on $M_0$ and $A = c_1\mathbf i$ on $M_1$, $c_0, c_1 \neq 0$, there is a linear isomorphism $M_0 \to M_1$ that commutes with the $J_\alpha$ and anticommutes with $J$.

- `Morse.iWord` — Morse/Chapter15/SplittingTwo.lean, line 59
- `Morse.IsIOps` — Morse/Chapter15/SplittingTwo.lean, line 92
- `Morse.IsOmegaOps.exists_eq_smul_iWord` — Morse/Chapter15/SplittingTwo.lean, line 165
- `Morse.exists_odd_of_mulVec` — Morse/Chapter15/IndexBoundTwo.lean, line 48
- `Morse.exists_decomp_two` — Morse/Chapter15/SplittingTwoData.lean, line 62
- `Morse.exists_inter_two` — Morse/Chapter15/SplittingTwo.lean, line 252

*What differs.*
- $A\mathbf i$ is self-adjoint and commutes with all the operators, hence is a scalar on a minimal piece: $A = a_h\mathbf i$. With $\exp(\pi A) = -I$, $a_h$ is an odd integer; and $\operatorname{tr}(A\mathbf i) = -m_{k+1}\sum a_h$.

### V15.38. The index bound on $\Omega^{(c)}$

*value differs* · $4\lambda \ge \nu - |c|$, both signs · by Killing fields

**Milnor (§24, pp. 147–148).** $2\lambda \ge \sum_{a_h > a_j}(a_h - a_j - 2)$. "Suppose for example that some $a_h$ is equal to $-3$": then $4\lambda \ge 2p \ge r + c$, where $r = n/m_k$ tends to infinity with $n$.

**Proved in Lean.** Let $J_1, \dots, J_k$ be an anticommuting family on $\mathbb R^n$ with $1 \le k \le 7$, $k \not\equiv 3 \pmod 4$, such that $\mathbf i = J_1\cdots J_{k-1}$ is central for $k$ and $\mathcal C_{J_k} \neq \emptyset$, and let $c$ be an integer. If $\gamma \in \Omega^{(c)}$ is an unbroken geodesic which is not of least energy, then $n = \nu m_{k+1}$ for an integer $\nu$, and the index of $\gamma$ is at least $\lfloor(\nu - |c|)/4\rfloor$ (at least $0$ if $|c| > \nu$).

- `Morse.IsInterRelI` — Morse/Chapter15/KillingTwo.lean, line 49
- `Morse.IsInterRelI.commute_exp` — Morse/Chapter15/KillingTwo.lean, line 96
- `Morse.exists_killing_spaces_two` — Morse/Chapter15/KillingTwo.lean, line 198
- `Morse.le_formIndex_of_not_minimal_omega_two` — Morse/Chapter15/IndexBoundTwo.lean, line 203
- `Morse.omega_hidx_two` — Morse/Chapter15/FiniteStageTwo.lean, line 81

*What differs.*
- A geodesic in $\Omega^{(c)}$ which is not of least energy has index $\ge \lfloor(\nu - |c|)/4\rfloor$, $\nu = n/m_{k+1}$, whichever sign the large $|a_h|$ has; the case $a_h \le -3$ is reduced to the other by passing to $-A$.
- The Jacobi fields come from $X_j = D_j\mathbf i - (D_j\mathbf i)^{\mathsf T}$, which commute with $\exp(\tau\pi A)$ at $\tau = 2s/(a_{h_0} - a_j)$. Only pairs with $a_j$ of the opposite sign are used.

### V15.39. Theorem 24.5 for each $n$, $k = 2, 6$

*restated* · explicit ranges · class by class · bijections of pointed sets

**Milnor (§24, p. 148).** "The component of $\Omega\Omega_k(n)$ is approximated up to higher and higher dimensions by the corresponding component of $\Omega_{k+1}(n)$, as $n \to \infty$."

**Proved in Lean.** Let $k = 2$ or $k = 6$, let $J_1, \dots, J_{k+1}$ be an anticommuting family on $\mathbb R^n$, $\nu = n/m_{k+1}$, and $c$ an integer. (i) For $J' \in \Omega_{k+1}(n)$, $\varphi(J')$ lies in $\Omega_w$ with $w = -\pi\operatorname{tr}(J_k^{\mathsf T}J'\mathbf i)/2$; so $\varphi(J') \in \Omega^{(c)}$ exactly when $-\operatorname{tr}(J_k^{\mathsf T}J'\mathbf i) = m_{k+1}c$. (ii) For $j + 2 \le \lfloor(\nu - |c|)/4\rfloor$, the inclusion $\Omega^d \cap \Omega^{(c)} \to \Omega^{(c)}$ induces a bijection on $\pi_j$ at every point. (iii) For $j + 3 \le \lfloor(\nu - |c|)/4\rfloor$ and $J' \in \Omega_{k+1}(n)$ with $\varphi(J') \in \Omega^{(c)}$, $\varphi$ induces a bijection on $\pi_{j+1}$ at $J'$, and there is a bijection $\pi_{j+1}(\Omega_{k+1}(n), J') \cong \pi_{j+2}(\Omega_k(n), J_k)$.

- `Morse.isCentralI_iWordM` — Morse/Chapter15/FiniteStageTwo.lean, line 51
- `Morse.omegaPhi_mem_omegaComp` — Morse/Chapter15/FiniteStageTwo.lean, line 64
- `Morse.omega_minPaths_bijective_two` — Morse/Chapter15/FiniteStageTwo.lean, line 102
- `Morse.omegaPhi_bijective_two` — Morse/Chapter15/FiniteStageTwo.lean, line 123
- `Morse.theorem_24_5_two_six` — Morse/Chapter15/FiniteStageTwo.lean, line 151
- `Morse.omega_pi_equiv_two` — Morse/Chapter15/FiniteStageTwo.lean, line 161

*What differs.*
- Theorem 22.1 for an open and closed set of paths (V13.16), with V15.27 and V15.38. At a point $J'$ whose semicircle lies in $\Omega^{(c)}$, $\varphi$ is bijective on $\pi_{j+1}$ for $j + 3 \le \lfloor(\nu - |c|)/4\rfloor$, and $\pi_{j+1}\Omega_{k+1}(n) \cong \pi_{j+2}\Omega_k(n)$.
- $\varphi(J') \in \Omega^{(c)}$ exactly when $-\operatorname{tr}(J_k^{\mathsf T}J'\mathbf i) = m_{k+1}c$.

### V15.40. Theorem 24.5 for each $n$, $k = 2, 6$: path components

*narrower* · only $|c| \le n/m_{k+1} - 8$ at a fixed $n$

**Milnor (§24, pp. 146, 148).** $\Omega\Omega_k(n)$ has infinitely many components, while the approximating subspace $\Omega_{k+1}(n)$ has only finitely many. Passing to the direct limit, one obtains a homotopy equivalence on each component.

**Proved in Lean.** In the setting of V15.39, let $\lfloor(\nu - |c|)/4\rfloor \ge 2$. (i) Every path in $\Omega^{(c)}$ can be joined, by a path in $\Omega(N; J_k, -J_k)$, to $\varphi(J')$ for some $J' \in \Omega_{k+1}(n)$. (ii) If $\varphi(J') \in \Omega^{(c)}$, then for every $J'' \in \Omega_{k+1}(n)$: $J'$ and $J''$ can be joined in $\Omega_{k+1}(n)$ if and only if $\varphi(J')$ and $\varphi(J'')$ can be joined in $\Omega(N; J_k, -J_k)$.

- `Morse.theorem_24_5_pi0_two_six` — Morse/Chapter15/OmegaComponents.lean, line 419

*What differs.*
- For the classes with $|c| \le \nu - 8$: every path of $\Omega^{(c)}$ can be joined to a semicircle, and two points of $\Omega_{k+1}(n)$ can be joined iff their semicircles can. The other classes are controlled only in the limit, which is not formed.

### V15.41. The structures on $\mathbb R^{16r}$, and stabilization

*narrower* · no limit map · the class $c$ is stable

**Milnor (§24, pp. 138–139).** $\Omega_k(n)$ can be imbedded in $\Omega_k(n + n')$ by $J \mapsto J \oplus J'_k$. "It is not difficult to see that the inclusions $\Omega_{k+1}(n) \to \Omega\Omega_k(n)$ give rise, in the limit, to inclusions $\Omega_{k+1} \to \Omega\Omega_k$." Later it is convenient to set $n = 16r$.

**Proved in Lean.** On $\mathbb R^{16r} = \mathbb R^{16} \otimes \mathbb R^r$ let $J_\alpha = J'_\alpha \oplus \dots \oplus J'_\alpha$ ($r$ summands), where $J'_1, \dots, J'_8$ are the structures of V15.9 on $\mathbb R^{16}$; $J_1, \dots, J_8$ is an anticommuting family. Identify $\mathbb R^{16r} \oplus \mathbb R^{16}$ with $\mathbb R^{16(r+1)}$, the new block last, and put $s(X) = X \oplus J'_k$ (for $k = 0$: $X \oplus I_{16}$). Then: (i) for $k \le 8$, $s$ maps $\Omega_k(16r)$ into $\Omega_k(16r + 16)$ and carries $J_k$ to $J_k$; (ii) for $k \le 7$ and $J' \in \Omega_{k+1}(16r)$, $\varphi(J' \oplus J'_{k+1})(t) = \varphi(J')(t) \oplus \bigl(\cos(\pi t)\,J'_k + \sin(\pi t)\,J'_{k+1}\bigr)$ for all $t$; (iii) for $k = 2, 6$ and every matrix $X$ on $\mathbb R^{16r}$, $\operatorname{tr}\bigl(J_k^{\mathsf T}(X \oplus J'_{k+1})\,\mathbf i\bigr) = \operatorname{tr}(J_k^{\mathsf T}X\mathbf i)$, the left side computed on $\mathbb R^{16(r+1)}$, so that by V15.39 (i) the class $c$ of $\varphi(J')$ does not change under stabilization; (iv) for $k = 2, 6$, $\varphi(J_{k+1}) \in \Omega^{(0)}$.

- `Morse.bottJ` — Morse/Chapter15/BottChain.lean, line 46
- `Morse.isAnticommFamily_bottJ` — Morse/Chapter15/BottChain.lean, line 49
- `Morse.stabEquiv` — Morse/Chapter15/Stabilization.lean, line 46
- `Morse.stab` — Morse/Chapter15/Stabilization.lean, line 98
- `Morse.stab_mem_omega` — Morse/Chapter15/Stabilization.lean, line 123
- `Morse.stab_basePt` — Morse/Chapter15/Stabilization.lean, line 132
- `Morse.omegaPhi_stab` — Morse/Chapter15/Stabilization.lean, line 144
- `Morse.omegaLabel_stab` — Morse/Chapter15/Stabilization.lean, line 184
- `Morse.omegaPhi_bottJ_mem_omegaComp` — Morse/Chapter15/BottChain.lean, line 67

*What differs.*
- With the explicit structures on $\mathbb R^{16r}$: $\varphi(J' \oplus J'_{k+1}) = \varphi(J') \oplus \delta_k$, where $\delta_k(t) = \cos(\pi t)J'_k + \sin(\pi t)J'_{k+1}$; and for $k = 2, 6$ the class $c$ does not change, the base point having $c = 0$.
- The limits $\Omega_k$, the limit map and the naturality of the bijections of V15.31 and V15.39 are not formalized.

### V15.42. Lemma 24.6 (8): $\Omega_8(16r) \cong O(r)$

*restated* · by the commutant of $J_1, \dots, J_7$ · a homeomorphism

**Milnor (§24, Lemma 24.6 (8), pp. 141–142).** $\Omega_8(16r)$ can be identified with the set of all real isometries from $X_1$ to $X_2$: $J_7J_8$ maps $X_1$ isomorphically onto $X_2$, and "clearly this isomorphism determines $J_8$ uniquely". Thus $\Omega_8(16r)$ is diffeomorphic to the orthogonal group $O(r)$.

**Proved in Lean.** (i) A $16 \times 16$ matrix that commutes with $J'_1, \dots, J'_7$ is $b\,I + c\,W$ for real $b$, $c$, where $W = 1 \otimes 1 \otimes 1 \otimes \tau$ in the notation of V15.9. (ii) With $P_\pm = \tfrac12(1 \pm W)$ and $q(U, V) = P_+ \otimes U + P_- \otimes V$ for $r \times r$ matrices $U$, $V$: every matrix on $\mathbb R^{16r}$ that commutes with $J_1, \dots, J_7$ (V15.41) is $q(U, V)$ for some $U$, $V$. (iii) $\Omega_8(16r)$, for the structures of V15.41, is homeomorphic to $O(r)$: $J$ corresponds to the $U$ with $-J_8J = q(U, U^{\mathsf T})$, and $U$ to $J_8\,q(U, U^{\mathsf T})$; the base point $J_8$ corresponds to $I$.

- `Morse.W16` — Morse/Chapter15/EightCommutant.lean, line 128
- `Morse.eq_of_commute_bott16` — Morse/Chapter15/EightCommutant.lean, line 150
- `Morse.qOf` — Morse/Chapter15/OmegaEight.lean, line 116
- `Morse.eq_qOf_of_commute` — Morse/Chapter15/OmegaEight.lean, line 161
- `Morse.omegaEightHomeomorph` — Morse/Chapter15/OmegaEight.lean, line 257
- `Morse.omegaEightHomeomorph_basePt` — Morse/Chapter15/OmegaEight.lean, line 304

*What differs.*
- For the explicit structures: a matrix commuting with $J_1, \dots, J_7$ is $P_+ \otimes U + P_- \otimes V$, and $J \in \Omega_8(16r)$ iff $-J_8J$ has this form with $U$ orthogonal and $V = U^{\mathsf T}$. The commutant on $\mathbb R^{16}$ is found by a finite check on the $256$ Kronecker words.
- A homeomorphism with $J_8 \mapsto I$, not a diffeomorphism.

### V15.43. Bott's chain at $n = 16r$

*restated* · finite stage: $r \ge 2i + 7$ · bijections of sets

**Milnor (§24, Theorem 24.5, p. 138; p. 142).** $\pi_hO \cong \pi_{h-1}\Omega_1 \cong \pi_{h-2}\Omega_2 \cong \dots \cong \pi_1\Omega_{h-1}$; and $\Omega_8$ is homeomorphic to the infinite orthogonal group $O$, "combining this fact with Theorem 24.5".

**Proved in Lean.** For the structures of V15.41, every $i \ge 0$ and every $r \ge 2i + 7$, there are bijections $\pi_i(\Omega_8(16r), J_8) \cong \pi_{i+8}(O(16r), I)$ and $\pi_i(O(r), I) \cong \pi_{i+8}(O(16r), I)$.

- `Morse.bott_chain` — Morse/Chapter15/BottChain.lean, line 90
- `Morse.bott_chain_of_le` — Morse/Chapter15/StablePeriodicity.lean, line 85
- `Morse.bott_periodicity_finite` — Morse/Chapter15/OmegaEight.lean, line 314
- `Morse.bott_periodicity_finite_of_le` — Morse/Chapter15/StablePeriodicity.lean, line 146

*What differs.*
- Eight steps at $n = 16r$, base point to base point: V15.31 for $k = 7, 5, 4, 3, 1$; V15.39 with $c = 0$ for $k = 6, 2$; V15.32 for $k = 0$; then V15.42. The steps through $\Omega_6$ and $\Omega_2$ decide the range.

### V15.44. Stability of $\pi_iO(n)$ and $\pi_iU(n)$

*not in the book* · for $O(n)$: $i + 2 \le n$

**Milnor (§23, proof of Lemma 23.4, pp. 128–129).** $\pi_{i-1}U(m) \cong \pi_{i-1}U(m + 1)$ for $i \le 2m$, from the fibration $U(m) \to U(m + 1) \to S^{2m+1}$. For $O$ no such statement is made: $\pi_iO$ is the homotopy group of the direct limit.

**Proved in Lean.** Let $\mathbb K = \mathbb R$ with $d = 1$, or $\mathbb K = \mathbb C$ with $d = 2$, and let $U_{\mathbb K}(m)$ be $O(m)$, resp. $U(m)$. If $i + 2 \le dm + d - 1$ and $i + 2 \le dm' + d - 1$, there is a bijection $\pi_i(U_{\mathbb K}(m), I) \cong \pi_i(U_{\mathbb K}(m'), I)$. So $\pi_iO(n) \cong \pi_iO(n')$ whenever $i + 2 \le n$ and $i + 2 \le n'$, and $\pi_iU(n) \cong \pi_iU(n')$ whenever $i < 2n$ and $i < 2n'$.

- `Morse.Homotopy.sphereConnected_real` — Morse/Homotopy/BundlesOrthogonal.lean, line 74
- `Morse.Homotopy.nonempty_pi_unitary_equiv_of_le` — Morse/Chapter15/StablePeriodicity.lean, line 63
- `Morse.Homotopy.nonempty_pi_unitary_equiv_stable` — Morse/Chapter15/StablePeriodicity.lean, line 73

*What differs.*
- $\pi_iO(n)$ is independent of $n \ge i + 2$, and $\pi_iU(n)$ of $n > i/2$, up to bijection. For $O$ this is what lets Theorem 24.7 be stated without the limit (V15.45).

### V15.45. Theorem 24.7 (Bott), in the stable range

*narrower* · finite groups in the stable range · a bijection of sets · no $O \simeq \Omega^8O$

**Milnor (§24, Theorem 24.7, p. 142).** The infinite orthogonal group $O$ has the same homotopy type as its own 8-th loop space. Hence the homotopy group $\pi_iO$ is isomorphic to $\pi_{i+8}O$ for $i \ge 0$.

**Proved in Lean.** For every $i \ge 0$, $n \ge i + 2$ and $n' \ge i + 10$ there is a bijection $\pi_i(O(n), I) \cong \pi_{i+8}(O(n'), I)$.

- `Morse.theorem_24_7` — Morse/Chapter15/StablePeriodicity.lean, line 158

*What differs.*
- $\pi_i(O(n), I) \cong \pi_{i+8}(O(n'), I)$ for $n \ge i + 2$ and $n' \ge i + 10$, where both sides are Milnor's stable groups (V15.44). The limit group $O$, the homotopy equivalence with $\Omega^8O$, the group structure of the isomorphism and the table of $\pi_iO$ are not formalized.

### V15.46. The periodicity theorem for $U$ in the stable range

*restated* · between any two stable groups · a bijection of sets

**Milnor (§23, Periodicity Theorem, p. 129).** $\pi_{i-1}U \cong \pi_{i+1}U$ for $i \ge 1$, where $\pi_{i-1}U = \pi_{i-1}U(m)$ for $i \le 2m$.

**Proved in Lean.** For $i < 2n$ and $i + 2 < 2n'$ there is a bijection $\pi_i(U(n), I) \cong \pi_{i+2}(U(n'), I)$.

- `Morse.periodicity_theorem_stable` — Morse/Chapter15/StablePeriodicity.lean, line 172

*What differs.*
- V14.28 with stability (V15.44) on both sides: $\pi_i(U(n), I) \cong \pi_{i+2}(U(n'), I)$ for $i < 2n$ and $i + 2 < 2n'$, so the statement no longer refers to one $m$. As groups: V14.28 and V14.30.

## Appendix

*Milnor pp. 149–153: the homotopy type of a monotone union*

### VA.2. The telescope and homotopy direct limits

*hypotheses explicit* · Milnor's definition verbatim · (T1), used without comment

**Milnor (Appendix, p. 149).** For a topological space $X$ and a sequence $X_0 \subset X_1 \subset X_2 \subset \cdots$ of subspaces, it is convenient to consider the infinite union $X_\Sigma = X_0 \times [0, 1] \cup X_1 \times [1, 2] \cup X_2 \times [2, 3] \cup \cdots$, "to be topologized as a subset of $X \times \mathbb R$". Definition: $X$ is the *homotopy direct limit* of the sequence $\{X_i\}$ if the projection map $p : X_\Sigma \to X$, $p(x, \tau) = x$, is a homotopy equivalence.

**Proved in Lean.** Spaces are arbitrary topological spaces, with no separation axiom unless stated; for subsets $X_0, X_1, \dots$ of $X$, the telescope is $X_\Sigma = \bigcup_nX_n \times [n, n + 1] \subseteq X \times \mathbb R$, with the subspace topology; the $n$-th strip is the map $X_n \times [0, 1] \to X_\Sigma$, $(x, t) \mapsto (x, n + t)$; $p(x, \tau) = x$; and $X$ is the homotopy direct limit of $\{X_i\}$ if $p$ is a homotopy equivalence. **(T1)** For a monotone sequence, $(x, \tau) \in X_\Sigma$ iff $x \in X_n$ for some integer $0 \le n \le \tau$; so raising $\tau$ stays in $X_\Sigma$.

- `Morse.telescope` — Morse/Appendix/Telescope.lean, line 172
- `Morse.mem_telescope_iff` — Morse/Appendix/Telescope.lean, line 184
- `Morse.stripMap` — Morse/Appendix/Telescope.lean, line 221
- `Morse.telescopeProj` — Morse/Appendix/Telescope.lean, line 424
- `Morse.IsHomotopyDirectLimit` — Morse/Appendix/Telescope.lean, line 433

*What differs.*
- The definition is Milnor's; the elementary fact (T1), that a point of the telescope may be raised, is used throughout his proof without comment and is stated here.

### VA.3. Pasting maps along the strips (T3)

*not in the book* · the hidden closedness hypothesis · strips closed, locally finite

**Milnor (Appendix, pp. 151–153).** The book has no such statement. Every map and homotopy on a telescope in the proof of Theorem A (pp. 151–153) is given strip by strip, by formulas in $(x, n + t)$, $0 \le t \le 1$, and its continuity is taken for granted.

**Proved in Lean.** Spaces are arbitrary topological spaces, with no separation axiom unless stated; if every $X_n$ is closed in $X$, then for every space $P$ a function $F$ on $P \times X_\Sigma$ is continuous as soon as each $(p, x, t) \mapsto F(p, (x, n + t))$ is continuous on $P \times X_n \times [0, 1]$. Hence, for a monotone sequence of closed sets, maps $\Phi_n : P \times X_n \times [0, 1] \to Z$ with $\Phi_{n+1}(p, x, 0) = \Phi_n(p, x, 1)$ define a continuous map on $P \times X_\Sigma$; in particular maps on $X_\Sigma$, and homotopies between them, may be given strip by strip.

- `Morse.continuous_of_stripMap` — Morse/Appendix/Telescope.lean, line 288
- `Morse.telescopeLift` — Morse/Appendix/Telescope.lean, line 373
- `Morse.telescopeDesc` — Morse/Appendix/Telescope.lean, line 392
- `Morse.telescopeHomotopy` — Morse/Appendix/Telescope.lean, line 406

*What differs.*
- This is where closedness enters, a hypothesis Milnor never states: when the $X_n$ are closed, the strips are closed in $X_\Sigma$ and form a locally finite family, and pasting is legitimate. Without it Milnor's maps can be discontinuous (VA.10); the device that removes the hypothesis altogether is the mapping telescope (VA.13, VA.15).

### VA.4. The map of telescopes, and “clearly sufficient”

*as in the book* · neither closedness nor monotonicity

**Milnor (Appendix, proof of Theorem A, p. 150).** Define $f_\Sigma : X_\Sigma \to Y_\Sigma$ by $f_\Sigma(x, t) = (f(x), t)$. Then "it is clearly sufficient to prove that $f_\Sigma$ is a homotopy equivalence".

**Proved in Lean.** Spaces are arbitrary topological spaces, with no separation axiom unless stated; if $f : X \to Y$ carries each $X_n$ into $Y_n$, then $f_\Sigma(x, \tau) = (f(x), \tau)$ is a map $X_\Sigma \to Y_\Sigma$ with $p_Yf_\Sigma = fp_X$. If $X$ and $Y$ are the homotopy direct limits of $\{X_i\}$ and $\{Y_i\}$ and $f_\Sigma$ is a homotopy equivalence, then so is $f$.

- `Morse.telescopeMap` — Morse/Appendix/Telescope.lean, line 446
- `Morse.telescopeProj_comp_telescopeMap` — Morse/Appendix/Telescope.lean, line 457
- `Morse.IsHomotopyEquiv.of_telescopeMap` — Morse/Appendix/Telescope.lean, line 464

*What differs.*
- No hidden hypothesis: neither closedness nor monotonicity is needed. The proof is $f \simeq fp_Xs = p_Yf_\Sigma s$ for a homotopy inverse $s$ of $p_X$.

### VA.5. Truncations of the telescope (T2)

*restated* · truncations are always closed · homotopy equivalence for retract

**Milnor (Appendix, p. 152).** In Case 2, $X_\Sigma^n$ is the subset of $X_\Sigma$ of pairs $(x, \tau)$ with $\tau \le n$, i.e. $X_0 \times [0, 1] \cup \dots \cup X_{n-1} \times [n - 1, n] \cup X_n \times [n]$. "In fact $X_\Sigma^n$ contains $X_n \times [n]$ as deformation retract", and the composition $Gf_\Sigma$ carries $X_\Sigma^n$ into itself.

**Proved in Lean.** Spaces are arbitrary topological spaces, with no separation axiom unless stated; the truncation $X^n_\Sigma = \{(x, \tau) \in X_\Sigma : \tau \le n\}$ is closed in $X_\Sigma$, and $X^0_\Sigma \subseteq X^1_\Sigma \subseteq \cdots$, whatever the $X_i$. For a monotone sequence, $x \mapsto (x, n)$ is a homotopy equivalence $X_n \to X^n_\Sigma$ with homotopy inverse $(x, \tau) \mapsto x$, the homotopy raising $\tau$ to $n$; and a function on $X_\Sigma$ that sends the $n$-th strip to levels $\le n + 1$ and $X_n \times \{n\}$ to levels $\le n$ sends each $X^m_\Sigma$ to levels $\le m$.

- `Morse.truncation` — Morse/Appendix/Telescope.lean, line 482
- `Morse.isClosed_truncation` — Morse/Appendix/Telescope.lean, line 485
- `Morse.truncIncl` — Morse/Appendix/Telescope.lean, line 499
- `Morse.isHomotopyEquiv_truncIncl` — Morse/Appendix/Telescope.lean, line 550
- `Morse.isHomotopyEquiv_truncProj` — Morse/Appendix/Telescope.lean, line 554
- `Morse.level_le_of_stripMap` — Morse/Appendix/Telescope.lean, line 561

*What differs.*
- The two facts Milnor states are proved; the deformation retraction is stated as a homotopy equivalence, its homotopy being the one that raises $\tau$ to $n$.
- That truncations are always closed, with no closedness of the $X_i$, is what lets Case 2 need closedness only of the $Y_i$ (VA.11).

### VA.6. A level function makes a homotopy direct limit (Lemmas 2.1, 2.2)

*hypotheses explicit* · “clearly a deformation retract” proved · used silently at the end of Case 2

**Milnor (Appendix, Example 1, p. 149).** In Example 1, given $f : X \to \mathbb R$ with $f(x) \ge i + 1$ for $x \notin X_i$ and $f \ge 0$, the correspondence $x \mapsto (x, f(x))$ maps $X$ homeomorphically onto a subset of $X_\Sigma$ "which is clearly a deformation retract". At the end of Case 2 (p. 153), Case 1 is applied to the sequence of truncations $\{X_\Sigma^n\}$, which uses that $X_\Sigma$ is their homotopy direct limit.

**Proved in Lean.** Spaces are arbitrary topological spaces, with no separation axiom unless stated; (i) for a monotone sequence, if $f : X \to \mathbb R$ is continuous, $f \ge 0$, and $f(x) \ge n + 1$ whenever $x \notin X_n$, then $X$ is the homotopy direct limit of $\{X_i\}$. (ii) For any sequence, $X_\Sigma$ is the homotopy direct limit of its truncations $\{X^n_\Sigma\}$.

- `Morse.isHomotopyDirectLimit_of_level` — Morse/Appendix/Telescope.lean, line 584
- `Morse.isHomotopyDirectLimit_truncation` — Morse/Appendix/Telescope.lean, line 616

*What differs.*
- (i) needs no paracompactness once $f$ is given: the homotopy $(x, (1 - s)f(x) + s\tau)$ stays in $X_\Sigma$ by (T1). (ii) is (i) with $f(x, \tau) = \tau + 1$, and is the step Milnor's Case 2 uses without mention (VA.11).

### VA.7. Example 1, and sublevel sets

*stronger* · sublevel sets: no paracompactness · Hausdorff, for partitions of unity

**Milnor (Appendix, Example 1, p. 149).** Suppose that each point of $X$ lies in the interior of some $X_i$, and that $X$ is paracompact. Then using a partition of unity one can construct a map $f : X \to \mathbb R$ so that $f(x) \ge i + 1$ for $x \notin X_i$ and $f(x) \ge 0$ for all $x$; and $X$ is a homotopy direct limit.

**Proved in Lean.** Spaces are arbitrary topological spaces, with no separation axiom unless stated; (i) let $X$ be paracompact and Hausdorff, and $X_0 \subseteq X_1 \subseteq \cdots$ with every point of $X$ in the interior of some $X_i$; then $X$ is the homotopy direct limit of $\{X_i\}$. (ii) Let $E : X \to \mathbb R$ be continuous, on any space $X$, and $a_0 \le a_1 \le \cdots$ with $a_i \to \infty$. Then $X$ is the homotopy direct limit of the sublevel sets $\{x : E(x) \le a_i\}$.

- `Morse.example1` — Morse/Appendix/Examples.lean, line 68
- `Morse.isHomotopyDirectLimit_sublevel` — Morse/Appendix/Examples.lean, line 101

*What differs.*
- (ii) needs no paracompactness, with $f = \sum_j\min(1, \max(0, E - a_j + 1))$, locally a finite sum; it covers the sublevel sets of the energy in Theorem 17.3, where Milnor uses Example 1 and the paracompactness of a metric space.
- In (i) Milnor's "paracompact" is read with the Hausdorff axiom, as Mathlib's partitions of unity need a normal space.

### VA.8. Example 3

*as in the book* · proved; the book gives no proof · indexed from $0$

**Milnor (Appendix, Example 3, p. 150).** The unit interval $[0, 1]$ is not the homotopy direct limit of the sequence of closed subsets $[0] \cup [1/i, 1]$. No proof is given.

**Proved in Lean.** Let $X_n = \{0\} \cup [\frac1{n+1}, 1] \subseteq [0, 1]$. The $X_n$ are closed and increasing, with union $[0, 1]$, and $[0, 1]$ is not the homotopy direct limit of $\{X_n\}$.

- `Morse.example3Set` — Morse/Appendix/Examples.lean, line 149
- `Morse.isClosed_example3Set` — Morse/Appendix/Examples.lean, line 160
- `Morse.iUnion_example3Set` — Morse/Appendix/Examples.lean, line 165
- `Morse.example3` — Morse/Appendix/Examples.lean, line 176

*What differs.*
- The proof: $\{0\} \times [0, \infty)$ is open and closed in $X_\Sigma$, so $X_\Sigma$ is not connected, while a homotopy inverse of $p$ would join $(0, 0)$ to $(1, 0)$ by a path. The sequence is indexed from $0$.

### VA.9. Milnor’s maps $h_1$ and their homotopy inverse $g$

*hypotheses explicit* · the $X_n$ closed, for the pasting · “completely analogous” carried out

**Milnor (Appendix, Case 1, pp. 151–152).** Any map $h_1 : X_\Sigma \to X_\Sigma$ with $h_1(x, n + t) = (x, n + 2t)$ for $0 \le t \le \frac12$ and $h_1(x, n + t) \in X_{n+1} \times [n + 1]$ for $\frac12 \le t \le 1$ is a homotopy equivalence, with homotopy inverse $g(x, n + t) = (x, n + 2t)$ for $t \le \frac12$, $h_1(x, n + \frac32 - t)$ for $t \ge \frac12$, well defined since $h_1(x, n + \frac12) = h_1(x, n + 1) = (x, n + 1)$. $h_1g \simeq \mathrm{id}$ by a homotopy $H_u$, $0 \le u \le \frac12$, ending at $(x, n + \min(4t, 1))$, "clearly" homotopic to the identity; $gh_1 \simeq \mathrm{id}$ "by a completely analogous argument".

**Proved in Lean.** Spaces are arbitrary topological spaces, with no separation axiom unless stated; let $X_0 \subseteq X_1 \subseteq \cdots$ be closed in $X$. (i) For a map $\rho : I \to I$ with $\rho(0) = 0$, $\rho(1) = 1$, $(x, n + t) \mapsto (x, n + \rho(t))$ is homotopic to the identity of $X_\Sigma$. (ii) Let $\psi : X_\Sigma \to X_\Sigma$ be a map with $\psi(x, n + t) = (x, n + 2t)$ for $t \le \frac12$ and $\psi(x, n + t)$ at level $n + 1$ for $t \ge \frac12$. Then $\psi$ fixes the points at integer levels and is a homotopy equivalence, with homotopy inverse Milnor's $g$.

- `Morse.reparam_homotopic` — Morse/Appendix/TheoremA.lean, line 118
- `Morse.IsMilnorMap` — Morse/Appendix/TheoremA.lean, line 175
- `Morse.milnorInv` — Morse/Appendix/TheoremA.lean, line 230
- `Morse.isHomotopyEquiv_of_milnorMap` — Morse/Appendix/TheoremA.lean, line 447

*What differs.*
- The $X_n$ must be closed for the strip-by-strip formulas to define continuous maps (VA.3); the formula for $h_1g$ uses that $h_1$ fixes the integer levels.
- With $u$ rescaled, Milnor's $H_u$ is a single formula, and the "completely analogous" homotopy for $gh_1$ is written out; both end at $(x, n + \min(4t, 1))$, homotopic to the identity by (i).

### VA.10. Theorem A, Case 1, and a possible misprint $(4 - 3t)u$

*value differs* · $(4t - 3)u$, not the printed $(4 - 3t)u$ · the $X_n$ closed

**Milnor (Appendix, Case 1, pp. 150–152).** Case 1: suppose that $X_i = Y_i$ and that each $f_i : X_i \to Y_i$ is homotopic to the identity; then $f_\Sigma$ is a homotopy equivalence. With one-parameter families $h^n_u : X_n \to X_n$, $h^n_0 = f_n$, $h^n_1 = \mathrm{id}$, the homotopy $h_u : X_\Sigma \to X_\Sigma$ is $(h^n_u(x), n + 2t)$ for $0 \le t \le \frac12$, $(h^n_{(3-4t)u}(x), n + 1)$ for $\frac12 \le t \le \frac34$, and $(h^{n+1}_{(4-3t)u}(x), n + 1)$ for $\frac34 \le t \le 1$. "Taking $u = 0$ this defines a map $h_0$ which is clearly homotopic to $f_\Sigma$", and $h_1$ has the properties of VA.9.

**Proved in Lean.** Spaces are arbitrary topological spaces, with no separation axiom unless stated; let $X_0 \subseteq X_1 \subseteq \cdots$ be closed in $X$, and $\varphi : X \to X$ a map carrying each $X_n$ into itself by a map $\varphi_n$ homotopic, in $X_n$, to the identity of $X_n$. Then $\varphi_\Sigma$ is a homotopy equivalence. With homotopies $h^n_u$ from $\varphi_n$ to the identity, the homotopy is $(h^n_u(x), n + 2t)$ for $t \le \frac12$, $(h^n_{(3-4t)u}(x), n + 1)$ for $\frac12 \le t \le \frac34$, and $(h^{n+1}_{(4t-3)u}(x), n + 1)$ for $\frac34 \le t \le 1$; it is continuous in $(u, z)$, $h_0 = \varphi_\Sigma \circ R_2$ is homotopic to $\varphi_\Sigma$, and $h_1$ is a map as in VA.9.

- `Morse.case1Fun` — Morse/Appendix/TheoremA.lean, line 466
- `Morse.case1Family` — Morse/Appendix/TheoremA.lean, line 514
- `Morse.case1Map_zero` — Morse/Appendix/TheoremA.lean, line 534
- `Morse.case1Map_one` — Morse/Appendix/TheoremA.lean, line 550
- `Morse.theoremA_case1` — Morse/Appendix/TheoremA.lean, line 572

*What differs.*
- The third line is $h^{n+1}_{(4t-3)u}$: the printed $(4 - 3t)u$ is a misprint, which at $t = \frac34$ gives $h^{n+1}_{7u/4}$, where continuity with the second line needs $h^{n+1}_0 = \varphi_{n+1}$; the corrected formula gives it.
- The $X_n$ must be closed, for the continuity of $h_u$ and of $g$ (VA.3); without it Milnor's $g$ can be discontinuous (the exposition's example $X = [0, 1]$, $X_0 = (0, 1]$). This case does not use that $X$ is a homotopy direct limit.

### VA.11. Theorem A, Case 2: $f_\Sigma$ is a homotopy equivalence

*narrower* · the $Y_n$ closed · the $X_n$ need not be closed · no homotopy direct limit needed

**Milnor (Appendix, Case 2, pp. 152–153).** Now let $X$ and $Y$ be arbitrary. With homotopy inverses $g_n$ of the $f_n$, $i_ng_n \simeq g_{n+1}f_{n+1}i_ng_n = g_{n+1}j_nf_ng_n \simeq g_{n+1}j_n$; with a homotopy $h^n_u$ from $i_ng_n$ to $g_{n+1}j_n$, $G(y, n + t) = (g_n(y), n + 2t)$ for $t \le \frac12$ and $(h^n_{2t-1}(y), n + 1)$ for $t \ge \frac12$. $Gf_\Sigma$ carries $X^n_\Sigma$ into itself by a map homotopic to the identity, so "we can apply Case 1 to the sequence $\{X_\Sigma^n\}$, and conclude that $Gf_\Sigma$ is a homotopy equivalence"; similarly $f_\Sigma G$; so $f_\Sigma$ has a left and a right homotopy inverse.

**Proved in Lean.** Spaces are arbitrary topological spaces, with no separation axiom unless stated; (i) let $X_0 \subseteq X_1 \subseteq \cdots$ be monotone, closed or not, and $F : X_\Sigma \to X_\Sigma$ a map carrying each truncation $X^m_\Sigma$ into itself, with $F(x, m) = (e_m(x), m)$ for maps $e_m : X_m \to X_m$ homotopic to the identity. Then $F$ is a homotopy equivalence. (ii) Let $X_0 \subseteq X_1 \subseteq \cdots$ in $X$ and $Y_0 \subseteq Y_1 \subseteq \cdots$ in $Y$, the $Y_n$ closed, and let $f : X \to Y$ carry each $X_n$ into $Y_n$ by a homotopy equivalence $f_n$. Then $f_\Sigma : X_\Sigma \to Y_\Sigma$ is a homotopy equivalence.

- `Morse.isHomotopyEquiv_of_truncation` — Morse/Appendix/TheoremA.lean, line 597
- `Morse.homotopic_square` — Morse/Appendix/TheoremA.lean, line 687
- `Morse.case2Inv` — Morse/Appendix/TheoremA.lean, line 646
- `Morse.theoremA_telescope` — Morse/Appendix/TheoremA.lean, line 712

*What differs.*
- The $Y_n$ must be closed, for the continuity of $G$ (VA.3), where Milnor's Case 2 has no hypothesis; this is removed for Theorem A in VA.15.
- Conversely, the $X_n$ need not be closed, and no homotopy direct limit hypothesis is used: Case 1 is applied only to the truncations, which are always closed (VA.5).
- Hidden: the return from Case 1, which is about the induced map of the telescope of $\{X^n_\Sigma\}$, to $Gf_\Sigma$ itself needs $X_\Sigma$ to be the homotopy direct limit of its truncations (VA.6 (ii)); and "$Gf_\Sigma$ on $X^m_\Sigma$ is homotopic to the identity" is a chain of homotopies through the maps of VA.5.

### VA.12. Theorem A, by Milnor’s proof

*narrower* · the $Y_i$ closed · removed in VA.15

**Milnor (Appendix, Theorem A, p. 150).** Suppose that $X$ is the homotopy direct limit of $\{X_i\}$ and $Y$ is the homotopy direct limit of $\{Y_i\}$. Let $f : X \to Y$ be a map which carries each $X_i$ into $Y_i$ by a homotopy equivalence. Then $f$ itself is a homotopy equivalence.

**Proved in Lean.** Spaces are arbitrary topological spaces, with no separation axiom unless stated; let $X$ be the homotopy direct limit of $X_0 \subseteq X_1 \subseteq \cdots$ and $Y$ that of $Y_0 \subseteq Y_1 \subseteq \cdots$, the $Y_i$ closed in $Y$, and let $f : X \to Y$ carry each $X_i$ into $Y_i$ by a homotopy equivalence $f_i : X_i \to Y_i$. Then $f$ is a homotopy equivalence.

- `Morse.theoremA` — Morse/Appendix/TheoremA.lean, line 757

*What differs.*
- Milnor's proof, as written, needs the $Y_i$ closed (VA.11), and only these: Case 1 as written needs closed sets, but Case 2 applies it only to truncations, which are closed. The hypothesis is removed in VA.15, by running the same proof on mapping telescopes.

### VA.13. The mapping telescope

*not in the book* · pasting with no closedness · stands for a union of complexes

**Milnor (Appendix, pp. 149–153).** The book has no such construction. The Appendix works with the telescope $X_\Sigma$ of a sequence of subspaces of one space $X$, and the application to Theorem 17.3 with a union $K = \bigcup K_i$ of complexes $K_0 \subset K_1 \subset \cdots$.

**Proved in Lean.** For a sequence of spaces and maps $K_0 \xrightarrow{c_0} K_1 \xrightarrow{c_1} \cdots$, the mapping telescope $T$ is the quotient of the disjoint union of the blocks $K_n \times [0, 1]$ by $(k, 1)_n \sim (c_n(k), 0)_{n+1}$; $(k, t)_n$ is at level $n + t$, a continuous function on $T$. Maps out of $T$, and out of $P \times T$ for locally compact $P$, may be given block by block, compatibly with the gluing, with no closedness condition. The truncations $T_n = \{\text{level} \le n\}$ are closed and increasing, $T$ is the homotopy direct limit of $\{T_n\}$, and $k \mapsto (k, 0)_n$ is an embedding $K_n \to T$ and a homotopy equivalence $K_n \to T_n$. For subsets $X_0 \subseteq X_1 \subseteq \cdots$ of $X$, the mapping telescope of the inclusions is homotopy equivalent to $X_\Sigma$ (homeomorphic when the $X_n$ are closed).

- `Morse.MappingTelescope` — Morse/Appendix/MappingTelescope.lean, line 77
- `Morse.MappingTelescope.desc` — Morse/Appendix/MappingTelescope.lean, line 110
- `Morse.MappingTelescope.trunc` — Morse/Appendix/MappingTelescope.lean, line 179
- `Morse.MappingTelescope.isHomotopyDirectLimit_trunc` — Morse/Appendix/MappingTelescope.lean, line 191
- `Morse.MappingTelescope.isHomotopyEquiv_levelIncl` — Morse/Appendix/MappingTelescope.lean, line 509
- `Morse.isHomotopyEquiv_telescopeComparison` — Morse/Appendix/MonotoneUnion.lean, line 474
- `Morse.telescopeComparisonHomeomorph` — Morse/Appendix/MonotoneUnion.lean, line 457

*What differs.*
- This is the device that removes the closedness hypotheses (VA.15), pasting being automatic in a quotient, and that replaces a union of complexes which are not subspaces of one space (VA.16, VA.17).
- The product of a quotient map with a locally compact space is a quotient map, which is what makes homotopies on $T$ definable block by block.

### VA.15. Theorem A, exactly as Milnor states it

*as in the book* · no closedness hypothesis · Milnor's proof, on mapping telescopes

**Milnor (Appendix, Theorem A, p. 150).** Suppose that $X$ is the homotopy direct limit of $\{X_i\}$ and $Y$ is the homotopy direct limit of $\{Y_i\}$. Let $f : X \to Y$ be a map which carries each $X_i$ into $Y_i$ by a homotopy equivalence. Then $f$ itself is a homotopy equivalence.

**Proved in Lean.** Spaces are arbitrary topological spaces, with no separation axiom unless stated; let $X$ be the homotopy direct limit of $X_0 \subseteq X_1 \subseteq \cdots$ and $Y$ that of $Y_0 \subseteq Y_1 \subseteq \cdots$, arbitrary subsets, and let $f : X \to Y$ carry each $X_i$ into $Y_i$ by a homotopy equivalence $f_i : X_i \to Y_i$. Then $f$ is a homotopy equivalence.

- `Morse.mappingTelescopeMap` — Morse/Appendix/MonotoneUnion.lean, line 506
- `Morse.mapsTo_mappingTelescopeMap` — Morse/Appendix/MonotoneUnion.lean, line 520
- `Morse.theoremA_general` — Morse/Appendix/MonotoneUnion.lean, line 533

*What differs.*
- The statement is Milnor's, with no closedness hypothesis. The proof departs from his only in the space on which it is run: the induced map of the mapping telescopes of the inclusions carries each closed truncation into the corresponding one by a map homotopic to a composite of homotopy equivalences, so Milnor's proof (VA.12) applies, and the mapping telescopes are homotopy equivalent to $X$ and $Y$ by maps commuting with $f$ (VA.13).
- This general form is what Theorem 17.1 needs, its pieces being open sets (V10.19).

### VA.16. Monotone unions, and the final step of Theorem 17.3

*restated* · squares commute only up to homotopy · the mapping telescope stands for $K$

**Milnor (Appendix, p. 150).** Assuming Theorem A, the alternative proof of Theorem 17.3: the constructed homotopy equivalences $\Omega^{a_i} \to K_i$ form a commutative diagram with $K_0 \subset K_1 \subset \cdots$; since $\Omega = \bigcup\Omega^{a_i}$ and $K = \bigcup K_i$ are homotopy direct limits (Examples 1 and 2), the limit mapping $\Omega \to K$ is also a homotopy equivalence.

**Proved in Lean.** Spaces are arbitrary topological spaces, with no separation axiom unless stated; (i) if $X$ is the homotopy direct limit of $X_0 \subseteq X_1 \subseteq \cdots$, the $Y_i \subseteq Y$ are closed and increasing, and $f : X \to Y$ carries each $X_i$ into $Y_i$ by a homotopy equivalence, then $X$ is homotopy equivalent to the telescope $Y_\Sigma$. (ii) If $X$ is the homotopy direct limit of $X_0 \subseteq X_1 \subseteq \cdots$ (closed or not), $K_0 \xrightarrow{c_0} K_1 \xrightarrow{c_1} \cdots$ is a sequence of spaces and maps, and $g_n : X_n \to K_n$ are homotopy equivalences with $c_ng_n \simeq g_{n+1}$ on $X_n$, then $X$ is homotopy equivalent to the mapping telescope of the $K_n$.

- `Morse.nonempty_homotopyEquiv_telescope` — Morse/Appendix/MonotoneUnion.lean, line 135
- `Morse.compareMap` — Morse/Appendix/MonotoneUnion.lean, line 175
- `Morse.isHomotopyEquiv_compareMap` — Morse/Appendix/MonotoneUnion.lean, line 232
- `Morse.nonempty_homotopyEquiv_mappingTelescope` — Morse/Appendix/MonotoneUnion.lean, line 256

*What differs.*
- The conclusion is a homotopy equivalence with the mapping telescope of the $K_n$, which stands for the union $K$ with the weak topology; the two are homotopy equivalent by Example 2, which needs Whitehead's theorem and is not formalized.
- The squares need only commute up to homotopy, and the $K_n$ need not be subspaces of one space: Milnor's limit mapping exists only because each map extends the previous one, which is not available in the proof of Theorem 17.3 (V10.20).
- The proof is Milnor's map $G$ of Case 2, built from homotopy inverses of the $g_n$ and defined from the mapping telescope, where it is continuous block by block.

### VA.17. The Corollary: homotopy direct limits of CW-complexes

*narrower* · a mapping telescope, not a CW-complex · no cellular approximation

**Milnor (Appendix, Corollary, p. 153).** Suppose that $X$ is the homotopy direct limit of $\{X_i\}$. If each $X_i$ has the homotopy type of a CW-complex, then $X$ itself has the homotopy type of a CW-complex. "The proof is not difficult".

**Proved in Lean.** Spaces are arbitrary topological spaces, with no separation axiom unless stated; (i) if $X$ is the homotopy direct limit of $X_0 \subseteq X_1 \subseteq \cdots$ and each $X_n$ is homotopy equivalent to a space $K_n$, there are maps $K_0 \to K_1 \to \cdots$ such that $X$ is homotopy equivalent to their mapping telescope. (ii) If each $X_n$ has the homotopy type of a finite cell complex with cells $\mathrm{cells}_n$ (an iterated adjunction space, V2.11), $X$ is homotopy equivalent to the mapping telescope of a sequence of iterated adjunction spaces $K_n$ with these cells. No closedness of the $X_n$ is assumed.

- `Morse.corollary_appendix` — Morse/Appendix/MonotoneUnion.lean, line 274
- `Morse.corollary_cellComplex` — Morse/Appendix/MonotoneUnion.lean, line 298

*What differs.*
- The conclusion is a mapping telescope of the $K_n$, not a CW-complex: that a telescope of CW-complexes is a CW-complex needs cellular maps (cellular approximation) and the CW structure of mapping telescopes, neither of which is in Mathlib. For finite complexes, iterated adjunction spaces replace CW-complexes.

### VA.18. Countable cell complexes

*narrower* · attaching maps need not be cellular · a telescope stands for the union

**Milnor (Appendix, pp. 149–150).** Each $\Omega^{a_i}$ has the homotopy type of "a certain CW-complex", and the union $\Omega$ should have the homotopy type of a CW-complex (p. 149); in the final step of Theorem 17.3 the complexes form a nested sequence $K_0 \subset K_1 \subset \cdots$ with union $K$ (p. 150).

**Proved in Lean.** A space $K$ is obtained from $L$ by attaching cells of dimensions $(\lambda_1, \dots, \lambda_k)$ if it is obtained by attaching a $\lambda_1$-cell to $L$, then a $\lambda_2$-cell, and so on, each along an arbitrary map of its boundary sphere into the space built so far. A *cell tower* with cells $\mathrm{cells}_0, \mathrm{cells}_1, \dots$ (finite lists of dimensions) is a sequence $K_0 \to K_1 \to \cdots$ in which $K_0$ is an iterated adjunction space with cells $\mathrm{cells}_0$ and $K_{n+1}$ is obtained from $K_n$ by attaching the cells $\mathrm{cells}_{n+1}$. A space *has the homotopy type of a countable cell complex* with these cells if it is homotopy equivalent to the mapping telescope of such a tower; this is invariant under homotopy equivalence.

- `Morse.IsRelCellAttachment` — Morse/Appendix/MonotoneUnion.lean, line 313
- `Morse.CellTower` — Morse/Appendix/MonotoneUnion.lean, line 331
- `Morse.IsCountableCellComplexType` — Morse/Appendix/MonotoneUnion.lean, line 370
- `Morse.IsCountableCellComplexType.of_homotopyEquiv` — Morse/Appendix/MonotoneUnion.lean, line 373

*What differs.*
- Weaker than a CW-complex: the attaching maps need not be cellular, and the mapping telescope of the tower stands for the union of the $K_n$ with the weak topology, to which it is homotopy equivalent by Example 2, not verified. Every "CW-complex" of Theorems 17.3, 19.6 and Corollary 17.4 in the formalization is of this kind.

### VA.19. The topological part of Theorem 17.3

*stronger* · no paracompactness · squares up to homotopy in (i)

**Milnor (Appendix, p. 150).** The alternative final step of Theorem 17.3: a commutative diagram of homotopy equivalences $\Omega^{a_i} \to K_i$, Examples 1 and 2, and Theorem A make the limit mapping $\Omega \to K$ a homotopy equivalence.

**Proved in Lean.** Spaces are arbitrary topological spaces, with no separation axiom unless stated; (i) if $X$ is the homotopy direct limit of $X_0 \subseteq X_1 \subseteq \cdots$ and $g_n : X_n \to K_n$ are homotopy equivalences to the stages of a cell tower with $c_ng_n \simeq g_{n+1}$ on $X_n$, then $X$ has the homotopy type of the countable cell complex. (ii) Let $E : X \to \mathbb R$ be continuous, $a_0 \le a_1 \le \cdots$ with $a_n \to \infty$, and $g_n : \{E \le a_n\} \to K_n$ homotopy equivalences to the stages of a cell tower with $c_ng_n = g_{n+1}$ on $\{E \le a_n\}$. Then $X$ has the homotopy type of the countable cell complex with cells $\mathrm{cells}_0, \mathrm{cells}_1, \dots$.

- `Morse.isCountableCellComplexType_of_tower` — Morse/Appendix/MonotoneUnion.lean, line 387
- `Morse.isCountableCellComplexType_of_sublevel` — Morse/Appendix/MonotoneUnion.lean, line 400
- `Morse.isCountableCellComplexType_of_sublevel'` — Morse/Appendix/MonotoneUnion.lean, line 417

*What differs.*
- No paracompactness: the sublevel sets of a continuous function with levels tending to infinity always form a homotopy direct limit (VA.7 (ii)). The levels must tend to infinity, so that the sublevel sets exhaust $X$, which the book leaves implicit.
- "CW-complex" is read in the sense of VA.18; the application to the path space is Chapter 10 (V10.20–V10.22).

## Not formalized

*What the book states and the formalization does not prove, and what it does instead*

### G.1. The torus: the intermediate sublevel sets and the cell attachments

*not formalized*

**Milnor (§1, pp. 1–3).** For $f(p) < a < f(q)$, $f(q) < a < f(r)$ and $f(r) < a < f(s)$, $M^a$ is homeomorphic to a 2-cell, to a cylinder and to a compact genus-one surface bounded by a circle; up to homotopy type, passing $p$, $q$, $r$, $s$ attaches a 0-cell, a 1-cell, a 1-cell and a 2-cell (p. 2).

**Proved in Lean.** **What is proved is the frame, not the pictures.** The torus of revolution is a compact surface whose height function has exactly four critical points, non-degenerate, of indices $0, 1, 1, 2$ (V3.22, V3.23); $T^a$ is empty below $0$ and all of $T$ from $2R + 2\rho$ on, and between critical values Theorem 3.1 holds (V3.24). The homeomorphism types of (2)–(4) would need explicit homeomorphisms, and Theorem 3.2 on submanifolds (V2.8), which would give the cell attachments up to homotopy, has not been applied to the torus. Morse theory with the height function gives only $b_0 \le 1$, $b_1 \le 2$, $b_2 \le 1$ and $b_0 - b_1 + b_2 = 0$; the Betti numbers $1, 2, 1$ are not derived.


### G.2. Regular sublevel sets are manifolds with boundary

*not formalized*

**Milnor (§2, p. 4).** If $a$ is not a critical value of $f$, the implicit function theorem makes $M^a$ a smooth manifold-with-boundary, whose boundary $f^{-1}(a)$ is a smooth submanifold of $M$.

**Proved in Lean.** **Not restated.** It is the companion project's Lemma 3 (`Milnor.isHalfSliceSubmanifold_of_regularValue`) applied to $a - f$. Theorems 3.1 and 3.2 are stated here for sublevel sets as topological subspaces, without a structure of manifold with boundary.


### G.3. The intrinsic Hessian

*not formalized*

**Milnor (§2, pp. 4–5).** $f_{**}(v, w) = \tilde v_p(\tilde w(f))$ for vector fields $\tilde v$, $\tilde w$ extending $v$, $w$; it is symmetric because $[\tilde v, \tilde w]_p(f) = 0$ at a critical point, and therefore independent of both extensions.

**Proved in Lean.** **The coordinate formula instead.** The formal Hessian is the second derivative read in the preferred chart, Milnor's matrix of second partial derivatives (V1.4), and its independence of the extensions is replaced by its independence of the chart (V1.5).


### G.4. Example (b), and the submanifold claims of (d) and (e)

*not formalized*

**Milnor (§2, pp. 8–9).** (b) $F(x) = e^{-1/x^2}\sin^2(1/x)$ has a degenerate, non-isolated critical point at the origin; in (d) the critical set is a submanifold of $\mathbb R^2$, and in (e) it is not even a submanifold.

**Proved in Lean.** **Not done.** The smoothness of (b) at $0$ needs the flatness of $e^{-1/x^2}$ against the growth of the derivatives of $\sin^2(1/x)$. The critical sets of (d) and (e) are computed and shown to be degenerate (V1.12), but whether they are submanifolds is not formalized.


### G.5. Lemma 2.4 on a manifold

*not formalized*

**Milnor (§2, Lemma 2.4, p. 10).** A smooth vector field on a manifold $M$ which vanishes outside a compact set generates a unique 1-parameter group of diffeomorphisms of $M$.

**Proved in Lean.** **Vector spaces only.** Lemma 2.4, and the smooth dependence of the flow on the initial point, are proved on a Banach space (V1.14, V1.15); Mathlib has no smooth dependence on initial conditions on manifolds. On submanifolds of $\mathbb R^K$, which is where flows are needed, Chapter 2 uses instead the ambient flow of a compactly supported field tangent to the submanifold, which preserves it (V2.3).


### G.6. Compact support cannot be omitted

*not formalized*

**Milnor (§2, Remark, p. 11).** Without compact support Lemma 2.4 fails: the standard vector field $d/dt$ on the open interval $(0, 1)$ generates no 1-parameter group of diffeomorphisms.

**Proved in Lean.** **Not formalized.** The example plays no role later; the analogous remark on Theorem 3.1, p. 13, is formalized (V2.5).


### G.7. Theorem 3.1 on a non-compact abstract manifold

*not formalized*

**Milnor (§3, Theorem 3.1, p. 12).** For a smooth $f$ on any manifold $M$, with $f^{-1}[a, b]$ compact and free of critical points, $M^a$ is diffeomorphic to $M^b$ and is a deformation retract of it.

**Proved in Lean.** **Three classes of spaces, not all manifolds.** Proved on $\mathbb R^n$ (V2.2), on submanifolds of $\mathbb R^K$, closed or not (V2.3), and on compact Hausdorff manifolds through Mathlib's Whitney embedding (V2.4). A non-compact abstract manifold would need either a closed embedding into Euclidean space or flows of vector fields on manifolds, and Mathlib has neither.


### G.8. Theorems 3.2 and 3.5, Remarks 3.3 and 3.4, on abstract manifolds

*not formalized*

**Milnor (§3, pp. 14–24).** Each is stated for a function on an abstract manifold.

**Proved in Lean.** **Not transferred.** Theorem 3.1 is carried to compact abstract manifolds through the Whitney embedding (V2.4), but the cell-attaching statements are proved only on $\mathbb R^n$ (V2.6, V2.10) and for $f = F|N$ on submanifolds of a Euclidean space (V2.8, V2.9, V2.12, V2.15). The transfer, along the lines of V2.4 and V4.24, has not been made.


### G.9. Remark 3.4 on submanifolds, and the Remark of p. 24 at a critical value

*not formalized*

**Milnor (§3, pp. 20 and 24).** $M^c$ is a deformation retract of $M^{c+\epsilon}$, and $M^{c-\epsilon} \cup e^\lambda$ one of $M^c$; hence each $M^a$ has the homotopy type of a finite CW-complex with one cell for each critical point in $M^a$, even if $a$ is a critical value.

**Proved in Lean.** **Only on $\mathbb R^n$, and at regular values.** Remark 3.4 is proved on $\mathbb R^n$ (V2.10); on submanifolds it is not, so the Remark of p. 24 is proved only for $a$ not a critical value (V2.15).


### G.10. The CW structure in Theorem 3.5

*not formalized*

**Milnor (§3, Theorem 3.5, p. 20).** $M$ has the homotopy type of a CW-complex, the attaching maps being made cellular by cellular approximation (p. 23).

**Proved in Lean.** **An iterated adjunction space instead.** The formal Theorem 3.5 produces a space built from the empty space by attaching cells one at a time along arbitrary continuous maps, with exactly $C_\lambda$ cells of dimension $\lambda$ (V2.11, V2.12). Mathlib has no cellular approximation theorem, so the attaching maps are not made cellular and the result is not shown to be a CW-complex.


### G.11. Theorem 3.5 for a non-compact manifold

*not formalized*

**Milnor (§3, proof of Theorem 3.5, p. 23).** If $M$ is not compact but all critical points lie in one compact $M^a$, then $M^a$ is a deformation retract of $M$; with infinitely many critical points, the union of the complexes $K_i$ with the direct limit topology and Whitehead's theorem give a homotopy equivalence $M \to K$ (pp. 23–24).

**Proved in Lean.** **Compact submanifolds only.** With finitely many critical points the non-compact case needs a deformation of $M$ onto some $M^a$ obtained by patching flows; with infinitely many it needs Whitehead's theorem and the fact that a manifold is dominated by a CW-complex, neither of which Mathlib provides.


### G.12. Smale's handles

*not formalized*

**Milnor (§3, Remark, p. 17).** In Smale's terminology $M^{c-\epsilon} \cup H$ is $M^{c-\epsilon}$ with a handle attached, and by Theorem 3.1 the manifold-with-boundary $M^{c-\epsilon} \cup H$ is diffeomorphic to $M^{c+\epsilon}$.

**Proved in Lean.** **Not recorded.** It is Theorem 3.1 applied to $F$, which the proof of Theorem 3.2 uses (Assertion 3, as a strong deformation retraction), but the diffeomorphism itself is not stated.


### G.13. Reeb's theorem with degenerate critical points

*not formalized*

**Milnor (§4, Remark 1, p. 25).** The theorem remains true even if the critical points are degenerate, but the proof is more difficult; Milnor cites his own paper and one of R. Rosen.

**Proved in Lean.** **Not formalized.** A proof needs M. Brown's monotone union theorem, which is not in Mathlib; a proof by that route is written out in the exposition, Chapter 3, §1.


### G.14. Exotic spheres

*not formalized*

**Milnor (§4, Remark 2, p. 25).** The theorem gives no diffeomorphism with the standard $S^n$, and none need exist: the 7-sphere with an exotic differentiable structure of Milnor's 1956 paper is shown to be homeomorphic to $S^7$ by means of a function with two non-degenerate critical points.

**Proved in Lean.** **Out of scope.** It needs characteristic classes and the signature theorem. The formal proof of Reeb's theorem shows where smoothness is lost: Alexander's cone is not differentiable at the centre (V3.5).


### G.15. Manifolds with three critical points

*not formalized*

**Milnor (§4, p. 26).** If an $n$-manifold carries a differentiable function with only three critical points, these have index $0$, $n$ and $n/2$ (by Poincaré duality), and the manifold has the homotopy type of an $n/2$-sphere with an $n$-cell attached; such functions exist on the real and complex projective planes.

**Proved in Lean.** **Not formalized.** Singular homology with its exact sequences is available (V3.26–V3.31), but Poincaré duality, needed mod 2 since $\mathbb RP^2$ is not orientable, is not; the homotopy type would also need Theorem 3.5 on abstract manifolds.


### G.16. Complex projective space: what remains

*not formalized*

**Milnor (§4, pp. 26–27).** On $\mathbb CP_n$ the function $f(z_0 : \dots : z_n) = \sum_j c_j|z_j|^2$, with distinct constants $c_j$, has $n + 1$ critical points, every even index between $0$ and $2n$ occurring exactly once; so $\mathbb CP_n$ has the homotopy type of $e^0 \cup e^2 \cup \dots \cup e^{2n}$, and $H_i(\mathbb CP_n; \mathbb Z)$ is $\mathbb Z$ for $i = 0, 2, \dots, 2n$ and $0$ otherwise.

**Proved in Lean.** **Now proved** for the submanifold of rank-one projections: the coordinates (V3.41), the critical points and indices of $f$ (V3.42), the cells and the Betti numbers over every field (V3.43). What remains: the CW-complex in the strict sense (cells are attached along arbitrary maps, V2.12) and the integral homology (next entry).


### G.17. Integral homology

*not formalized*

**Milnor (§4, p. 27, and §5, p. 31).** The homology groups of $\mathbb CP_n$ are given with integer coefficients, and Corollary 5.4 is said to find them without Theorem 3.5.

**Proved in Lean.** **Fields only.** §5 works over a field, and so do V3.32–V3.39. The integral groups, and more generally the exposition's Proposition G (in the lacunary case $H_\lambda(M; \mathbb Z)$ is free of rank $C_\lambda$), are not derived, although relative homology and the cell computations are available with integer coefficients (V3.26–V3.31).


### G.18. Sard's theorem for $C^1$ maps

*not formalized*

**Milnor (§6, Theorem 6.1, p. 33).** For a $C^1$ map between manifolds of the same dimension with countable bases, the image of the set of critical points has measure $0$.

**Proved in Lean.** **Smooth maps into a vector space.** Sard's theorem is proved for smooth maps from a second countable manifold into a finite-dimensional vector space, in any dimensions (V4.3), which is every use Milnor makes of it; the Milnor project proves the Euclidean case for smooth maps only.


### G.19. Corollary 6.7 for a non-compact abstract manifold

*not formalized*

**Milnor (§6, Corollary 6.7, p. 36).** On any manifold there is a function with no degenerate critical points all of whose sublevel sets are compact, by Whitney's embedding as a closed subset of $\mathbb R^{2n+1}$.

**Proved in Lean.** **Closed submanifolds and compact manifolds.** Proved for closed submanifolds of $\mathbb R^n$ (V4.13) and for compact Hausdorff manifolds (V4.17). Mathlib's Whitney embedding is for compact manifolds only, so a non-compact abstract manifold has no closed embedding into Euclidean space here; the abstract forms of Corollary 6.8 (V4.22) are limited in the same way.


### G.20. Application 1: the homotopy type of a CW-complex

*not formalized*

**Milnor (§6, Application 1, p. 36).** A differentiable manifold has the homotopy type of a CW-complex, by Corollary 6.7 and Theorem 3.5.

**Proved in Lean.** **Not formalized.** Theorem 3.5 is proved only for compact submanifolds of Euclidean space and only as an iterated adjunction space, Mathlib having no cellular approximation (V2.11, V2.12); it has not been transferred to abstract manifolds, and the non-compact case needs Whitehead's theorem.


### G.21. Application 2 as Milnor argues it

*not formalized*

**Milnor (§6, Application 2, p. 36).** On a compact manifold the index sum of $\mathrm{grad} f$ is $\chi(M)$, and the index sum of any vector field is $\chi(M)$ because it is a topological invariant (Steenrod, §39.7).

**Proved in Lean.** **Run the other way, on an embedded copy.** $\chi$ enters as the Poincaré–Hopf integer of the Milnor project (V3.17, V4.18) and is identified with $\sum_i (-1)^i \dim H_i(M; F)$ afterwards (V3.38). The topological invariance quoted from Steenrod is not formalized, and vector fields on an abstract manifold are not treated, only on an embedded copy (V4.19).


### G.22. Independence of the principal curvatures

*not formalized*

**Milnor (§6, p. 34).** The principal curvatures are the eigenvalues of $(\vec v \cdot \vec\ell_{ij})$ in coordinates with $(g_{ij})$ the identity at $q$, tacitly independent of the coordinates chosen.

**Proved in Lean.** **Not proved, and not needed.** The principal curvatures are the eigenvalues of the shape operator of the chosen slice chart (V4.6), and every statement that uses them is proved in that chart.


### G.23. Theorem 7.2 for complex manifolds, and CW-complexes

*not formalized*

**Milnor (§7, Theorem 7.2, p. 39).** A complex manifold of complex dimension $k$, embedded bianalytically as a closed subset of $\mathbb C^n$, is homotopy equivalent to a CW-complex of dimension $k$.

**Proved in Lean.** **Proved for closed submanifolds with complex tangent spaces** (V5.15), as a countable cell complex with cells of dimension at most $k$. What remains: that a bianalytically embedded complex manifold is such a submanifold (holomorphic charts are not formalized as charts of the real submanifold), and a CW-complex in the strict sense, with cellular attaching maps.


### G.24. Theorem 7.1 with integral coefficients

*not formalized*

**Milnor (§7, Theorem 7.1, p. 39).** A non-singular affine algebraic variety $M \subset \mathbb C^n$ of real dimension $2k$ has $H_i(M; \mathbb Z) = 0$ in every degree $i > k$.

**Proved in Lean.** **Proved over every field** (V5.16), for closed submanifolds with complex tangent spaces. What remains: integral coefficients, and that a non-singular affine algebraic variety is such a submanifold.


### G.25. Assertion 2 for focal points, and the count of p. 41

*not formalized*

**Milnor (§7, pp. 40–41).** The focal points of $(M, q)$ along a normal line occur in symmetric pairs about $q$; there are at most $2k$ of them on the line, hence at most $k$ between $p$ and $q$, which by Lemma 6.9 bounds the index of $L_p$.

**Proved in Lean.** **Replaced.** Assertion 2 is proved for Hessians in a holomorphic chart (V5.7), and the index bound by the Andreotti–Frankel identity (V5.8–V5.11), on the real submanifold in V5.13; these need neither focal points nor Lemma 6.9. The focal-point form is not formalized.


### G.26. Corollary 7.3 with integral coefficients; Hypothesis (N)

*not formalized*

**Milnor (§7, Corollary 7.3, p. 41).** For an algebraic variety $V$ of complex dimension $k$ in $\mathbb CP_n$ and a hyperplane $P$ containing its singular points, the inclusion $V \cap P \to V$ induces isomorphisms of integral homology in dimensions less than $k - 1$, and a surjection in dimension $k - 1$.

**Proved in Lean.** **Proved over every field** (V5.17, V5.18), without Lefschetz duality, for a closed $V \subseteq \mathbb CP^n$ whose affine part is a complex submanifold, under Hypothesis (N). What remains: integral homology; algebraic varieties (that their affine parts satisfy the hypothesis); and Hypothesis (N) itself, the deformation of a neighbourhood of $V \cap P$ into it.


### G.27. Theorem 7.4: triangulability

*not formalized*

**Milnor (§7, Theorem 7.4, p. 41).** Under the same hypotheses the relative homotopy groups $\pi_r(V, V \cap P)$ vanish for $r < k$.

**Proved in Lean.** **Proved under Hypothesis (N)** (V5.19), as the compression criterion for $\pi_r(V, V \cap P) = 0$. What remains: Hypothesis (N), which Milnor obtains from the triangulability of algebraic varieties (quoted), and relative homotopy groups as objects.


### G.28. §§8–9 on an abstract Riemannian manifold

*not formalized*

**Milnor (§§8–9, p. 43).** Connections, Christoffel symbols, covariant derivatives along curves, parallel translation, the Levi-Civita connection and the curvature tensor are developed on an abstract Riemannian manifold, in local coordinates.

**Proved in Lean.** **Embedded manifolds instead.** The substance of §§8–9 is proved for submanifolds of a Euclidean space with the induced metric (V6.1–V6.21). On an abstract manifold only Milnor's rules for Mathlib's covariant derivatives, the definitions of compatibility and symmetry, the uniqueness half of Lemma 8.6, and the curvature formula with its sign (V6.3, V6.11, V6.13, V6.14, V6.16). Mathlib has no curvature, Christoffel symbols, covariant derivative along curves, parallel transport or Levi-Civita connection, and the embedded results reach an arbitrary Riemannian manifold only through Nash's embedding theorem, which is not proved. The induced connection is not constructed as a Mathlib covariant derivative, so the embedded existence and the abstract uniqueness are parallel results, not one theorem.


### G.29. Symmetric Christoffel symbols, and the second covariant derivative

*not formalized*

**Milnor (§8, p. 48).** If $\Gamma^k_{ij} = \Gamma^k_{ji}$ then the connection is symmetric throughout the coordinate neighbourhood; and, in a footnote, a connection is symmetric iff the covariant second derivative $X_p(Yf) - (X_p \vdash Y)f$ is symmetric in $X_p$ and $Y_p$.

**Proved in Lean.** **Not formalized**, there being no Christoffel symbols in either setting; the second covariant derivative of a function is not defined.


### G.30. Parallel fields along a flat surface

*not formalized*

**Milnor (§9, pp. 52–53).** If the curvature tensor vanishes, a vector field $P$ along a parametrized surface with $DP/\partial x = DP/\partial y = 0$ and a given value at the origin can be constructed.

**Proved in Lean.** **Not formalized.** Lemma 9.2, on which the construction rests, is proved for embedded manifolds (V6.19).


### G.31. Geodesics and path spaces on an abstract Riemannian manifold

*not formalized*

**Milnor (§§10–19, p. 55).** Milnor's §§10–19 are written for an abstract Riemannian manifold $M$: the Levi-Civita connection of §8, geodesics and the exponential map, the distance and completeness, the path space $\Omega(M; p, q)$ with its energy, Jacobi fields, the index theorem, and the topology of $\Omega$.

**Proved in Lean.** **Everything in Chapters 7–11 is proved for a submanifold $N$ of a Euclidean space $V$ with the induced metric** (V7.1). Mathlib has no Levi-Civita connection, geodesics or exponential map on an abstract manifold, and the Christoffel-symbol form of the geodesic equation is not formalized (V7.3). Every Riemannian manifold is isometric to such an $N$ by Nash's embedding theorem, which is quoted in the Lean files but neither proved nor used, so the formal results reach an abstract manifold only through it. Within the setting, completeness is often obtained from closedness of $N$ in $V$, which implies it (V7.30, V10.22).


### G.32. The remarks on minimal geodesics

*not formalized*

**Milnor (§10, p. 62).** Theorem 10.4 asserts that any sufficiently small segment of a geodesic is minimal. On the other hand a long geodesic may not be minimal: a great circle arc on the unit sphere of length greater than $\pi$ is certainly not. In general minimal geodesics are not unique: two antipodal points of a unit sphere are joined by infinitely many.

**Proved in Lean.** Not stated as such. The short geodesics of Lemma 10.3 and Corollary 10.8 are shortest (V7.15, V7.20), from which the first remark follows for every geodesic, but the step is not written. For long arcs, every geodesic of $S^n$, $n \ge 2$, of length $> \pi$ is not minimal (V11.14, from Myers' theorem). The non-uniqueness of minimal geodesics between antipodal points is not formalized.


### G.33. Geodesics of surfaces, and the footnote on $U(n)$

*not formalized*

**Milnor (§10, pp. 57 and 65–66).** Among the familiar examples of p. 65: meridians of a surface of revolution are geodesics; the geodesics of a right circular cylinder are the generating lines, the circles cut by perpendicular planes, and the helices, so that two points of the cylinder are joined by infinitely many; antipodal points of $S^n$ are joined by a continuum of minimal geodesics. A footnote on p. 57 explains the name "exponential": on the group of unitary matrices, $\exp_I(A) = I + A + \frac1{2!}A^2 + \dots$.

**Proved in Lean.** The geodesics of $\mathbb R^n$ and of $S^n$ are V7.30′. Surfaces of revolution, the cylinder, the continuum of minimal geodesics between antipodal points, and the identification of the Riemannian exponential of $U(n)$ with the matrix exponential (which needs a bi-invariant metric) are not formalized.


### G.34. Induced maps and Hessians of functions on $\Omega$

*not formalized*

**Milnor (§§11 and 13, pp. 68–69 and 74).** To motivate the definitions, Milnor defines the induced map $F_* : T\Omega_\omega \to T\mathbb R_{F(\omega)}$ of a real function $F$ on $\Omega$ through variations, noting that without hypotheses on $F$ there is no guarantee that it exists or is independent of the variation; and he observes that if $F$ takes its minimum at $\omega_0$ and the derivatives $dF(\bar\alpha(u))/du$ are all defined, then $\omega_0$ is a critical path (p. 69). On p. 74 he recalls the Hessian $f_{**}$ of a function on a finite-dimensional manifold, defined through 2-parameter maps.

**Proved in Lean.** Not formalized: critical paths are defined only for the energy (V8.4), and the Hessian only for $E$ (V8.14), where Theorem 13.1 shows it to be well defined. The Hessian of a function on a finite-dimensional manifold is that of Part I.


### G.35. Corollary 17.2 by Milnor's route

*not formalized*

**Milnor (§17, Corollary 17.2, p. 95).** The path space $\Omega$ has the homotopy type of a CW-complex: by Theorem 17.1 it is homotopy equivalent to $\Omega^*$, which has the homotopy type of a CW-complex by Milnor's theorem (*On spaces having the homotopy type of a CW-complex*, 1959). It is used with Whitehead's theorem in the first proof of Theorem 17.3.

**Proved in Lean.** **Proved for $N$ closed in $V$** (V10.29), by moving the end point to a non-conjugate one and Theorem 17.3, which gives a countable cell complex in the sense of VA.18. What remains: Milnor's theorem of 1959 and Whitehead's theorem, which are not in Mathlib, and the corollary for manifolds that are not complete. Theorem 17.3 does not use it (V10.22).


### G.36. Corollary 17.5: infinitely many geodesics

*not formalized*

**Milnor (§17, Corollary 17.5, p. 96).** Let $M$ have the homotopy type of $S^n$, $n > 2$. Then any two non-conjugate points of $M$ are joined by infinitely many geodesics: the homotopy type of $\Omega^*(M)$, and hence of $\Omega(M)$, depends only on that of $M$, so there must be at least one geodesic of index $0$, at least one of index $n - 1$, $2(n - 1)$, and so on.

**Proved in Lean.** Not formalized. It needs the homotopy invariance of $\Omega^*$ (the path spaces of homotopy equivalent spaces are weakly equivalent, with the same homology) and the homology of the countable cell complex of Theorem 17.3 in each dimension. What is formalized is that the corollary as printed omits a hypothesis: $\mathbb R^{n+1} \setminus \{0\}$ has the homotopy type of $S^n$ and no conjugate points, yet two of its points are joined by a single geodesic (V10.27), so $M$ must be complete. For $M = S^n$ itself the geodesics and the homology of $\Omega(S^n; p, q)$ are computed (V10.23, V10.26).


### G.37. Serre's remark, and the suspension theorem

*not formalized*

**Milnor (§17, Remark, p. 97).** More generally, if $M$ is any complete manifold which is not contractible, then any two non-conjugate points of $M$ are joined by infinitely many geodesics (compare Serre, *Homologie singulière des espaces fibrés*, 1951). As another application of 17.4 one can give a proof of the Freudenthal suspension theorem (compare §22.3).

**Proved in Lean.** Not formalized: Serre's theorem on the homology of loop spaces (the spectral sequence of the path fibration) and the passage to the universal covering are not available. The suspension theorem belongs to §22, which is not formalized.


### G.38. Corollary 19.3: no torsion in $\pi_1$

*not formalized*

**Milnor (§19, Corollary 19.3, p. 103).** If $M$ is complete with $\langle R(A, B)A, B\rangle \le 0$, then $\pi_1(M)$ contains no element of finite order other than the identity. Proof: the universal covering $\tilde M$ being contractible, $H^k(M)$ is the cohomology of the group $\pi_1(M)$ (Hu); a non-trivial finite cyclic subgroup $G$ would give a covering $\hat M$ with $H^k(G) = H^k(\hat M) = 0$ for $k > n$, while the cohomology groups of a finite cyclic group are non-trivial in arbitrarily high dimensions.

**Proved in Lean.** Not formalized: the cohomology of groups, of finite cyclic groups in particular, and the identification $H^k(M) \cong H^k(\pi_1(M))$ are not available. The first half of the corollary, $\pi_i(M) = 0$ for $i > 1$, is V11.21, where the universal covering is $\exp_p : T_pN \to N$ (V11.19).


### G.39. Finiteness of $\pi_1$ in positive Ricci curvature

*not formalized*

**Milnor (§19, p. 105).** Corollary 19.5 applies also to the universal covering space $\tilde M$ of $M$. Since $\tilde M$ is compact, the fundamental group $\pi_1(M)$ is finite.

**Proved in Lean.** Not formalized: universal coverings with a lifted metric are not formalized. In non-positive curvature the universal covering is $\exp_p$ itself (V11.19), but in positive Ricci curvature $\exp_p$ has critical points (Myers' theorem), so it is no covering. Corollary 19.5, compactness and the bound $\pi r$ on the diameter, is V11.13.


### G.40. Sectional curvature as a Gaussian curvature

*not formalized*

**Milnor (§19, Remark, p. 100).** If $A$ and $B$ are orthogonal unit vectors at $p$, the sectional curvature $\langle R(A, B)A, B\rangle$ is equal to the Gaussian curvature of the surface $(u_1, u_2) \mapsto \exp_p(u_1A + u_2B)$ spanned by the geodesics through $p$ with velocity vectors in the plane of $A$ and $B$ (Laugwitz).

**Proved in Lean.** Not formalized: the Gaussian curvature of this surface is not defined. The sectional curvature is that of Chapter 6, and the hypothesis of Lemma 19.1 is shown equivalent to all sectional curvatures being $\le 0$ (V11.7).


### G.41. The optics of curvature, and examples of curvature $\le 0$

*not formalized*

**Milnor (§19, pp. 101–102).** Intuitively, curvature can be described through "optics", geodesics being the paths of light rays: a short segment of length $L$ at $\exp_p(rU)$ in the direction $W$ appears to have length $L(1 + \frac{r^2}6\langle R(U, W)U, W\rangle + \dots)$, and a small object of volume $v$ appears to have volume $v(1 + \frac{r^2}6K(U, U) + \dots)$. Examples of complete manifolds of curvature $\le 0$: Euclidean space, the paraboloid $z = x^2 - y^2$, the hyperboloid of rotation $x^2 + y^2 - z^2 = 1$, the helicoid. The pseudo-sphere has constant curvature $-1$ and no conjugate points, but is not complete; by a theorem of Hilbert no complete surface of constant negative curvature can be imbedded in $\mathbb R^3$, although complete, even compact, ones exist, such as surfaces of genus $\ge 2$.

**Proved in Lean.** Not formalized; none of these statements is used later in the book.


### G.42. The remarks after Theorem 19.6

*not formalized*

**Milnor (§19, pp. 106–107).** Milnor does not know whether Theorem 19.6 remains true for $M$ complete but non-compact; the proof breaks down on the paraboloid $z = x^2 + y^2$, where $K(U, U)$ is not bounded away from $0$. The product $S^m \times S^k$, $m, k \ge 2$, has positive definite Ricci tensor while some sectional curvatures vanish; it is not known whether it can be remetrized with all sectional curvatures positive, and by a theorem of Synge such a metric could not be invariant under $(x, y) \mapsto (-x, -y)$.

**Proved in Lean.** Not formalized.


### G.43. Example 2 of the Appendix: CW-complexes

*not formalized*

**Milnor (Appendix, Example 2, p. 149).** Let $X$ be a CW-complex and let the $X_i$ be subcomplexes with union $X$. Since $p : X_\Sigma \to X$ induces isomorphisms of homotopy groups in all dimensions, it follows from Whitehead's theorem that $X$ is a homotopy direct limit.

**Proved in Lean.** Not formalized: it needs Whitehead's theorem, the fact that a compact subset of a CW-complex lies in a finite subcomplex, and the CW topology of products, none of which is in Mathlib. Hence the mapping telescope of a cell tower is not compared with the union of its stages in the weak topology, and the "countable CW-complexes" of Theorems 17.3 and 19.6 are mapping telescopes of iterated adjunction spaces (VA.18). Example 1, the case used for the path space, is VA.7.


### G.44. The Remark on Case 1 of Theorem A

*not formalized*

**Milnor (Appendix, Remark, p. 150).** Under the conditions of Case 1 it would be natural to conjecture that $f_\Sigma$ must actually be homotopic to the identity; however counterexamples can be given.

**Proved in Lean.** Not formalized: the exposition's counterexample, a phantom map, needs cellular cohomology and $\mathbb{CP}^\infty$. Case 1 itself is VA.10.


### G.45. Symmetric spaces: Lemma 20.1 and Corollaries 20.2–20.4

*not formalized*

**Milnor (§20, pp. 109–110).** A symmetric space is a connected Riemannian manifold with, for each $p$, an isometry $I_p$ fixing $p$ and reversing geodesics through $p$. Lemma 20.1: $I_qI_p$ translates a geodesic through $p = \gamma(0)$ and $q = \gamma(c)$ along itself, $\gamma(t) \mapsto \gamma(t + 2c)$, and parallel fields likewise. Corollaries: 20.2, a symmetric space is complete; 20.3, $I_p$ is unique; 20.4, $R(U, V)W$ is parallel along $\gamma$ when $U, V, W$ are. Locally symmetric spaces; Cartan's theorem relating them.

**Proved in Lean.** Not formalized: isometries of an abstract Riemannian manifold and symmetric spaces are not defined. For matrix groups, completeness and the reflection are V12.15–V12.16, and the conclusion of 20.4 is used through the explicit frame of V12.18.


### G.46. Theorem 20.5 for a general locally symmetric space

*not formalized*

**Milnor (§20, Theorem 20.5, p. 110).** In a locally symmetric manifold the conjugate points along a geodesic and their multiplicities are given by the positive eigenvalues of $K_V$.

**Proved in Lean.** Proved only along one-parameter subgroups of matrix groups (the Jacobi equation, V12.18) and, with the multiplicities, for $SU(n)$ (V14.18).


### G.47. The bi-invariant metric of a compact Lie group

*not formalized*

**Milnor (§21, p. 112).** A compact Lie group has a bi-invariant metric, obtained by averaging any metric with the Haar measure; a left-invariant metric is bi-invariant iff it is invariant under $\operatorname{Ad}$.

**Proved in Lean.** Not formalized; the groups of §§23–24 are matrix groups with the induced metric, which is bi-invariant (V12.14).


### G.48. Corollaries 21.5 and 21.6: the topology

*not formalized*

**Milnor (§21, pp. 115–116).** 21.5: trivial centre makes $G$ compact with finite $\pi_1$ (Myers). 21.6: a simply connected $G$ with a bi-invariant metric is $G' \times \mathbb R^k$ with $G'$ compact; conversely such products have bi-invariant metrics.

**Proved in Lean.** Only the Lie-algebra steps (V12.9, V12.10). Myers' theorem itself is V11.12–V11.13, but it is not applied to a Lie group; integrating an ideal decomposition to a product of groups is not formalized.


### G.49. Theorem 21.7 (Bott): only even cells

*not formalized*

**Milnor (§21, Theorem 21.7, p. 116).** If $G$ is compact and simply connected, $\Omega(G)$ has the homotopy type of a CW-complex with no odd-dimensional cells and only finitely many $\lambda$-cells for each even $\lambda$; so $H_\lambda(\Omega G; \mathbb Z)$ is $0$ for odd $\lambda$ and free of finite rank for even $\lambda$. Remarks: the complex is infinite-dimensional; the theorem extends to non-compact $G$ (Iwasawa).

**Proved in Lean.** Not formalized: only the algebra behind the evenness of the index (V12.11–V12.13). Theorem 17.3 (V10.22) and the Index Theorem (V9.24) are available, but Theorem 20.5 for a general compact group, the finiteness of §19.4 for it, and the passage to the loop space are not assembled.


### G.50. Hanner's theorem, and Theorem 22.1 for a manifold $\Omega^d$

*not formalized*

**Milnor (§22, pp. 118, 121).** Theorem 22.1 and Lemma 22.5 assume that $\Omega^d$ (resp. $M^0$) is a topological manifold; the proof uses Hanner's theorem: a manifold is a retract of a neighbourhood.

**Proved in Lean.** Not formalized. The formal Theorem 22.1 assumes the neighbourhood retraction (V13.2); for the sphere and for $SU(2m)$ it is constructed (V13.8, V14.21), so Corollary 22.3 and Theorem 23.3 are unconditional.


### G.51. The homological form of Theorem 22.1

*not formalized*

**Milnor (§22, p. 118).** By the relative Hurewicz theorem, $H_i(\Omega, \Omega^d) = 0$ for $i < \lambda_0$, so $H_i\Omega^d \cong H_i\Omega$ for $i \le \lambda_0 - 2$.

**Proved in Lean.** Not formalized (relative Hurewicz is not available).


### G.52. $U(n)$: the distance from $I$ to $-I$ and the space of all subspaces

*not formalized*

**Milnor (§23, p. 127).** In $U(n)$ the minimal geodesics from $I$ to $-I$ have length $\pi\sqrt n$ and correspond to all subspaces of $\mathbb C^n$, a space with components of varying dimensions; $\exp$ is onto.

**Proved in Lean.** Only $SU(2m)$ is treated (V14.15–V14.17); V14.12 records why $U(n)$ cannot be used.


### G.53. $\pi_0$ in Lemma 23.4

*not formalized*

**Milnor (§23, Lemma 23.4, pp. 128–129).** $\pi_0U(m) \cong \pi_0SU(m)$ (both groups are connected), and the case $i = 1$ of $\pi_iG_m(\mathbb C^{2m}) \cong \pi_{i-1}U(m)$ as groups.

**Proved in Lean.** For $i = 1$ the formal statement is a bijection of pointed sets (V14.26); the connectedness of $U(m)$ and $SU(m)$ is not formalized.


### G.54. The limit spaces, and Theorem 24.5 as a homotopy equivalence

*not formalized*

**Milnor (§24, Theorem 24.5, p. 138; pp. 146, 148).** $\Omega_k$ is the direct limit of the $\Omega_k(n)$ with the direct limit topology, and $O = \Omega_0$ the infinite orthogonal group. For each $k \ge 0$ the limit map $\Omega_{k+1} \to \Omega\Omega_k$ is a homotopy equivalence: it induces isomorphisms of homotopy groups in all dimensions, both spaces have the homotopy type of a CW-complex ("it can be shown"), and Whitehead's theorem applies.

**Proved in Lean.** Not formalized: no direct limits, no CW homotopy types, no Whitehead theorem. Theorem 24.5 is proved for each $n$, as bijections of homotopy groups in a range growing with $n$ (V15.31, V15.39, V15.40), for $k \le 7$; the compatibility with stabilization is V15.41, but the bijections are not shown natural.


### G.55. Theorem 24.7 as $O \simeq \Omega^8O$, and the group structure

*not formalized*

**Milnor (§24, Theorem 24.7, p. 142).** The infinite orthogonal group $O$ has the same homotopy type as its own 8-th loop space; $O$ has the homotopy type of $\Omega\Omega\Omega\Omega Sp$, and $Sp$ that of $\Omega\Omega\Omega\Omega O$.

**Proved in Lean.** Only $\pi_iO(n) \cong \pi_{i+8}O(n')$ in the stable range, as a bijection of sets (V15.45). The bijections along the chain are not shown to be homomorphisms, and nothing is proved about $Sp$.


### G.56. The table of $\pi_iO$ and $\pi_iSp$

*not formalized*

**Milnor (§24, p. 142).** $\pi_iO = \mathbb Z_2, \mathbb Z_2, 0, \mathbb Z, 0, 0, 0, \mathbb Z$ and $\pi_iSp = 0, 0, 0, \mathbb Z, \mathbb Z_2, \mathbb Z_2, 0, \mathbb Z$ for $i \equiv 0, \dots, 7 \pmod 8$; "the verification that these groups are correct will be left to the reader".

**Proved in Lean.** Not formalized.


### G.57. Symmetric spaces, and $\Omega_1(n) \cong O(n)/U(n/2)$

*not formalized*

**Milnor (§24, pp. 133, 136).** Each component of $\Omega_k(n)$ is a symmetric space. Remark: $\Omega_1(n)$ can be identified with the quotient space $O(n)/U(n/2)$.

**Proved in Lean.** Only the algebraic invariance of $\Omega_k(n)$ under the reflections (V15.5); the manifold structure is V15.23. The isotropy algebra of a point enters V15.28, but no quotient space is formed.


### G.58. Lemma 24.6 (2)–(7): the spaces $\Omega_2, \dots, \Omega_7$

*not formalized*

**Milnor (§24, pp. 138–141).** $\Omega_2(n) \cong U(n/2)/Sp(n/4)$; $\Omega_3(16r)$ the quaternionic Grassmann manifold; $\Omega_4(16r)$ diffeomorphic to $Sp(2r)$; $\Omega_5(16r) \cong Sp(2r)/U(2r)$; $\Omega_6(16r) \cong U(2r)/O(2r)$; the largest component of $\Omega_7(16r)$ diffeomorphic to the Grassmann manifold of $r$-dimensional subspaces of $\mathbb R^{2r}$; and, for $k > 8$, $\Omega_k(16r)$ diffeomorphic to $\Omega_{k-8}(r)$ (footnote, p. 142).

**Proved in Lean.** Only the bijections with involutions and the dimensions (V15.11, V15.12), and step (8) as a homeomorphism (V15.42). The periodicity theorem does not need the other identifications.


### G.59. The curvature of $\Omega_k(n)$, and the exact index of a geodesic

*not formalized*

**Milnor (§24, pp. 135, 144–146).** The index of a geodesic is computed from the eigenvalues of $K_A = -\tfrac14(\operatorname{Ad}A)^2$, by Theorem 20.5 and the index theorem; on $\Omega_k(n)$, $K_A$ is given by the same formula because $\Omega_k(n)$ is totally geodesic. For $O(2m)$: $\lambda = \sum_{i<j}(a_i + a_j - 2) + \sum_{a_i > a_j}(a_i - a_j - 2)$.

**Proved in Lean.** The lower bounds that Theorem 22.1 needs are proved for geodesics through Killing fields (V15.28, V15.30, V15.38). The exact formulas are obtained only as counts from Milnor's spectra (V15.3, V15.19, V15.20); the curvature of a totally geodesic submanifold and Theorem 20.5 for $\Omega_k(n)$ are not formalized.


### G.60. Lemma 24.8 for $k = 3, 7$ and $k > 8$; isometries

*not formalized*

**Milnor (§24, p. 143).** For $k = 3$ and $k = 7$ there are two non-isomorphic minimal spaces; for $k > 8$ "the situation repeats more or less periodically", and $m_k = 16m_{k-8}$; the isomorphisms of Lemma 24.8 are isometries.

**Proved in Lean.** For $k \le 8$: the dimension $m_k$ (V15.16) and, for $k \not\equiv 3 \pmod 4$, uniqueness up to a linear isomorphism (V15.17). For $k = 3, 7$ only that the central involution acts as $\pm1$; nothing for $k > 8$.


### G.61. Hurwitz–Radon and Adams

*not formalized*

**Milnor (§24, Remark, p. 144).** The vector fields obtained from Clifford modules are those of Hurwitz and Radon, and "J. F. Adams has recently proved that these estimates are best possible".

**Proved in Lean.** Only the $k$ orthonormal fields from $k$ anticommuting complex structures (V15.18); no count for general $n$, and no upper bound.


