# Morse Theory: sign-off checklist

Generated from the sign-off section of `Exposition/Verification.md` on 2026-10-23: 396 items. For each item: open its V-item in the verified edition (the statement with all its hypotheses), open Milnor's page, and tick the box if the formal statement says what Milnor means; write objections under the item. The tag in brackets is the comparison's label for the same V-item; `narrower` and `restated` items are where a disagreement is most likely, so read those with the most care.

| Section | Items | narrower | restated | stronger | explicit/same | other |
|---|---|---|---|---|---|---|
| Chapter 1 (Milnor §§1–2) | 14 | 2 | 3 | 5 | 1 | 3 |
| Chapter 2 (Milnor §3) | 15 | 10 | 1 | 2 | 2 | 0 |
| Chapter 3 (Milnor §§4–5) | 43 | 10 | 14 | 3 | 6 | 10 |
| Chapter 4 (Milnor §6) | 24 | 5 | 6 | 6 | 4 | 3 |
| Chapter 5 (Milnor §7) | 19 | 2 | 6 | 4 | 1 | 6 |
| Chapter 6 (Milnor §§8–9) | 25 | 12 | 2 | 3 | 2 | 6 |
| Chapter 7 (Milnor §10) | 30 | 2 | 11 | 12 | 4 | 1 |
| Chapter 8 (Milnor §§11–13) | 18 | 3 | 7 | 4 | 2 | 2 |
| Chapter 9 (Milnor §§14–15) | 25 | 1 | 12 | 6 | 5 | 1 |
| Chapter 10 (Milnor §§16–17) | 30 | 7 | 14 | 2 | 3 | 4 |
| Chapter 11 (Milnor §§18–19) | 24 | 3 | 4 | 5 | 9 | 3 |
| Chapter 12 (Milnor §§20–21) | 18 | 8 | 7 | 2 | 0 | 1 |
| Chapter 13 (Milnor §22) | 16 | 7 | 2 | 2 | 3 | 2 |
| Chapter 14 (Milnor §23) | 30 | 6 | 17 | 1 | 4 | 2 |
| Chapter 15 (Milnor §24) | 46 | 13 | 19 | 5 | 1 | 8 |
| Appendix (Milnor pp. 149–153) | 19 | 4 | 2 | 2 | 6 | 5 |

## Chapter 1 (Milnor §§1–2)

- [ ] **1.** (V1.2) `[same]` $X \cup_\varphi e^n$ is the quotient of $X \sqcup D^n$ identifying each $u \in S^{n-1}$ with $\varphi(u)$, that is, the pushout of $X \leftarrow S^{n-1} \to D^n$. — Milnor §1, pp. 2–3
- [ ] **2.** (V1.3) `[restated]` In coordinates, a critical point is a zero of the derivative, the Hessian is the second derivative, the index is the largest dimension of a subspace on which the Hessian is negative definite, the nullity is the dimension of its null space, and non-degenerate means nullity $0$, equivalently a non-singular matrix of second partial derivatives. — Milnor §2, pp. 4–5
- [ ] **3.** (V1.4) `[restated]` On a manifold, with no Hausdorff hypothesis, the same notions are read in the preferred chart at $p$, critical points agree with those of the companion volume, and a Morse function is a smooth function all of whose critical points are non-degenerate. — Milnor §2, pp. 4–5
- [ ] **4.** (V1.5) `[stronger]` At a critical point of a function $C^2$ there, criticality, the Hessian (transformed as a bilinear form by the derivative of the change of coordinates), non-degeneracy, index and nullity do not depend on the coordinate system. — Milnor §2, pp. 4–5
- [ ] **5.** (V1.6) `[extra]` For $f = F|N$ on a slice submanifold $N$ of $V$, a point $q$ is critical exactly when $dF_q$ vanishes on $T_qN$ (for an inner product, when $\nabla F(q) \perp T_qN$), the Hessian, index and nullity can be computed in any slice parametrization, and for $L_p$ Milnor's criterion and Hessian formula of pp. 35–36 hold. — Milnor §6, pp. 35–36
- [ ] **6.** (V1.7) `[stronger]` A function smooth on an open convex neighbourhood $V$ of $0$ in $\mathbb R^n$ with $f(0) = 0$ is $\sum_i x_i g_i(x)$ with $g_i$ smooth on $V$ and $g_i(0) = \partial f/\partial x_i(0)$; on an open star-shaped $V$ in any normed space it is $L(x)x$ with $L$ smooth and $L(0) = df_0$, and if also $df_0 = 0$ it is $B(x)(x, x)$ with $B$ smooth and symmetric and $B(0) = \tfrac12 d^2 f_0$. — Milnor §2, Lemma 2.1
- [ ] **7.** (V1.8) `[stronger]` Near a non-degenerate critical point $p$ of index $\lambda$ of a function smooth near $p$, on $\mathbb R^n$ or on any smooth manifold, there are coordinates with $f = f(p) - \sum_{i \le \lambda}(y^i)^2 + \sum_{i > \lambda}(y^i)^2$. — Milnor §2, Lemma 2.2
- [ ] **8.** (V1.9) `[stronger]` If $f$ has such a normal form with $k$ minus signs in some coordinate system around $p$, then $p$ is a non-degenerate critical point of index $k$. — Milnor §2, proof of Lemma 2.2
- [ ] **9.** (V1.10) `[stronger]` A non-degenerate critical point of a function $C^2$ at that point has a neighbourhood containing no other critical point. — Milnor §2, Corollary 2.3
- [ ] **10.** (V1.11) `[extra]` A $C^2$ function whose critical points are all non-degenerate has only finitely many critical points in each compact set. — Milnor §3, proof of Theorem 3.5
- [ ] **11.** (V1.12) `[sign]` The origin is the only critical point of $x^3$ and of $x^3 - 3xy^2$, and is degenerate; the critical points of $x^2$ (the $y$ axis) and of $x^2y^2$ (the two axes) are all degenerate. — Milnor §2, pp. 8–9
- [ ] **12.** (V1.13) `[narrower]` A one-parameter group of diffeomorphisms of $E$ is a jointly smooth $\varphi$ with each $\varphi_t$ a diffeomorphism and $\varphi_{t+s} = \varphi_t\circ\varphi_s$; $X$ generates it when $X(x)$ is the velocity of $t \mapsto \varphi_t(x)$ at $t = 0$, and then its orbits are integral curves of $X$. — Milnor §2, pp. 9–10
- [ ] **13.** (V1.14) `[restated]` A $C^n$ ($1 \le n \le \infty$) compactly supported vector field on a Banach space has a global flow, $C^n$ in $(t, x)$, each $\varphi_t$ being a $C^n$ diffeomorphism. — Milnor §2, pp. 10–11
- [ ] **14.** (V1.15) `[narrower]` A smooth vector field on $E$ vanishing outside a compact set generates exactly one one-parameter group of diffeomorphisms of $E$. — Milnor §2, Lemma 2.4

## Chapter 2 (Milnor §3)

- [ ] **15.** (V2.1) `[stronger]` $A$ is a strong deformation retract of $X$ if some homotopy from the identity of $X$ to a map into $A$ fixes $A$ at all times; the inclusion of such an $A$ is a homotopy equivalence. — Milnor §3, pp. 12–13
- [ ] **16.** (V2.2) `[narrower]` On $\mathbb R^n$ with an inner product, if $f^{-1}[a, b]$ is compact and free of critical points, a diffeomorphism of $\mathbb R^n$ carries $M^a$ onto $M^b$, and $M^a$ is a strong deformation retract of $M^b$. — Milnor §3, Theorem 3.1
- [ ] **17.** (V2.3) `[narrower]` The same holds for $f = F|N$ on a slice submanifold $N \subseteq \mathbb R^K$, closed or not, with a diffeomorphism of $N$. — Milnor §3, Theorem 3.1
- [ ] **18.** (V2.4) `[narrower]` The same holds on a compact Hausdorff manifold, where $f^{-1}[a, b]$ need only be free of critical points. — Milnor §3, Theorem 3.1
- [ ] **19.** (V2.5) `[restated]` On $\mathbb C \setminus \{i\}$ with $f = |z|^2$, the set $f^{-1}[\tfrac14, 4]$ contains no critical points but is not compact, and $M^{1/4}$ and $M^4$ are not homotopy equivalent. — Milnor §3, Remark after Theorem 3.1
- [ ] **20.** (V2.6) `[narrower]` On $\mathbb R^n$, under the hypotheses of Theorem 3.2 and for all small $\epsilon$, $M^{c+\epsilon}$ strongly deformation retracts onto $M^{c-\epsilon}$ together with an embedded $\lambda$-cell meeting $M^{c-\epsilon}$ in its boundary sphere, and so is homotopy equivalent to $M^{c-\epsilon}$ with a $\lambda$-cell attached. — Milnor §3, Theorem 3.2
- [ ] **21.** (V2.7) `[explicit]` In a Hausdorff space, a closed set $A$ together with an embedded closed disk meeting $A$ exactly in its boundary sphere is $A$ with a cell attached along the restriction of the embedding to the sphere. — Milnor §3, proof of Theorem 3.2
- [ ] **22.** (V2.8) `[narrower]` Theorem 3.2 holds for $f = F|N$ on a slice submanifold $N \subseteq \mathbb R^K$, and its topological half (given Assertion 3) holds in any Morse coordinate patch of a Hausdorff space. — Milnor §3, Theorem 3.2
- [ ] **23.** (V2.9) `[narrower]` With finitely many non-degenerate critical points on the level $c$ and none other near it, $N^{c+\epsilon}$ strongly deformation retracts onto $N^{c-\epsilon}$ together with pairwise disjoint cells, one of dimension $\lambda_p$ for each critical point $p$. — Milnor §3, Remark 3.3
- [ ] **24.** (V2.10) `[narrower]` On $\mathbb R^n$, $M^c$ is a strong deformation retract of $M^{c+\epsilon}$, and $M^{c-\epsilon} \cup e^\lambda$ is one of $M^c$. — Milnor §3, Remark 3.4
- [ ] **25.** (V2.11) `[narrower]` An iterated adjunction space is built from the empty space by attaching cells one at a time along arbitrary continuous maps; it replaces Milnor's CW-complex, without the cellular condition. — Milnor §3, Theorem 3.5
- [ ] **26.** (V2.12) `[narrower]` A compact slice submanifold on which $F|N$ has only non-degenerate critical points has the homotopy type of an iterated adjunction space with exactly $C_\lambda$ cells of dimension $\lambda$, attached in order of critical value. — Milnor §3, Theorem 3.5
- [ ] **27.** (V2.13) `[same]` Attaching an $n$-cell along homotopic maps gives homotopy equivalent spaces, by a homotopy equivalence which is the identity on $X$. — Milnor §3, Lemma 3.6
- [ ] **28.** (V2.14) `[stronger]` A homotopy equivalence $f : X \to Y$, extended by the identity on the cell, is a homotopy equivalence $X \cup_\varphi e^n \to Y \cup_{f\varphi} e^n$. — Milnor §3, Lemma 3.7
- [ ] **29.** (V2.15) `[narrower]` For $a$ not a critical value, $N^a$ has the homotopy type of an iterated adjunction space with one $\lambda$-cell for each critical point of index $\lambda$ below $a$. — Milnor §3, Remark after Theorem 3.5

## Chapter 3 (Milnor §§4–5)

- [ ] **30.** (V3.1) A local extremum is a critical point, and at a non-degenerate one the index is $0$ for a minimum and $\dim M$ for a maximum.
- [ ] **31.** (V3.2) `[restated]` Near a non-degenerate minimum $f = f(p) + \|y\|^2$ in smooth coordinates, and when the minimum is strict and the space compact, each small sublevel set $\{f \le f(p) + \varepsilon\}$ is the image of the closed unit ball, with the unit sphere going onto the level set. — Milnor §4, proof of Theorem 4.1
- [ ] **32.** (V3.3) `[explicit]` On a compact manifold of positive dimension, a smooth function with exactly two critical points, both non-degenerate, has them at its strict minimum and its strict maximum, of indices $0$ and $\dim M$. — Milnor §4, proof of Theorem 4.1
- [ ] **33.** (V3.4) `[stronger]` If $f^{-1}[a, b]$ is compact and free of critical points, a diffeomorphism carries $N^a$ onto $N^b$ and the level $f^{-1}(a)$ onto $f^{-1}(b)$. — Milnor §4, proof of Theorem 4.1
- [ ] **34.** (V3.5) `[explicit]` A Hausdorff space that is the union of two embedded closed $n$-balls meeting exactly in their common boundary sphere is homeomorphic to $S^n$. — Milnor §4, proof of Theorem 4.1
- [ ] **35.** (V3.6) `[narrower]` A compact submanifold of a finite-dimensional space carrying a smooth function with exactly two critical points, both non-degenerate, is homeomorphic to $S^n$, $n$ its dimension. — Milnor §4, Theorem 4.1 (Reeb)
- [ ] **36.** (V3.7) `[restated]` A function $S$ on pairs $a \le b$ of a preordered set is subadditive if $S(a, c) \le S(a, b) + S(b, c)$ for $a \le b \le c$, additive if equality holds. — Milnor §5, Definition
- [ ] **37.** (V3.8) `[explicit]` For subadditive $S$ and a chain $X_0 \le \dots \le X_n$ with $n \ge 1$, $S(X_0, X_n) \le \sum_k S(X_k, X_{k+1})$, with equality for additive $S$. — Milnor §5, Lemma 5.1
- [ ] **38.** (V3.9) `[restated]` A homology of a filtration is a family of finite-dimensional vector spaces $H_i(a, b)$, $a \le b$, with a long exact sequence for every triple ending in $0$; nothing else is assumed. — Milnor §5, pp. 28–30
- [ ] **39.** (V3.10) `[restated]` For such a structure $\dim H_\lambda$ is subadditive, and the Euler characteristic truncated at $N$ is additive when $H_{N+1}$ vanishes. — Milnor §5, p. 28
- [ ] **40.** (V3.11) `[narrower]` For such a structure and a chain, $R_\lambda \le C_\lambda$, and the alternating sums of the $R_i$ and $C_i$ up to $N$ agree when the slabs have no homology in degree $N + 1$; under the cell hypothesis $C_\lambda$ is the number of critical points of index $\lambda$. — Milnor §5, Theorem 5.2
- [ ] **41.** (V3.12) `[restated]` $S_\lambda = R_\lambda - R_{\lambda-1} + \dots \pm R_0$ is subadditive, by Milnor's rank computation. — Milnor §5, Lemma 5.3
- [ ] **42.** (V3.13) `[narrower]` $R_\lambda - R_{\lambda-1} + \dots \pm R_0 \le C_\lambda - C_{\lambda-1} + \dots \pm C_0$ for every $\lambda$. — Milnor §5, the Morse inequalities
- [ ] **43.** (V3.14) `[explicit]` The strong inequalities imply the weak ones, become equalities when $C_{\lambda+1} = 0$, and give $\sum (-1)^i R_i = \sum_p (-1)^{\operatorname{ind}(p)}$. — Milnor §5, p. 30
- [ ] **44.** (V3.15) `[stronger]` If $C_{\lambda+1} = C_{\lambda-1} = 0$ then $R_\lambda = C_\lambda$ and $R_{\lambda \pm 1} = 0$; if no two consecutive $C_i$ are nonzero, $R_i = C_i$ for all $i$. — Milnor §5, Corollary 5.4
- [ ] **45.** (V3.16) `[restated]` $C_\lambda(f)$ is the number of critical points of $f$ of index $\lambda$, and the sum of $(-1)^{\operatorname{index}}$ over the critical points is $\sum_\lambda (-1)^\lambda C_\lambda(f)$. — Milnor §5, p. 29
- [ ] **46.** (V3.17) `[restated]` An Euler number of a compact nonempty $N \subseteq \mathbb R^{K+1}$ is an integer equal to the index sum of every smooth tangent field with finitely many zeros; one exists for $K \ge 1$. — Milnor §5, p. 28, and §6, Application 2
- [ ] **47.** (V3.18) For a non-degenerate symmetric form $H(v, w) = \langle Av, w\rangle$, $\operatorname{sgn} \det A = (-1)^{\operatorname{index} H}$.
- [ ] **48.** (V3.19) `[narrower]` At a non-degenerate critical point of index $\lambda$ of $F|_N$, the gradient field of $F|_N$ for the induced metric has index $(-1)^\lambda$. — Milnor §6, Application 2
- [ ] **49.** (V3.20) `[restated]` On a compact $N \subseteq \mathbb R^{K+1}$, $K \ge 1$, $\dim N \ge 1$, every Morse function has $\sum_\lambda (-1)^\lambda C_\lambda = \chi(N)$, the Poincaré–Hopf integer; so this sum does not depend on the Morse function. — Milnor §5, formula (3), and §6, Application 2
- [ ] **50.** (V3.21) Every Morse function on $S^n$, $n \ge 1$, has $\sum_\lambda (-1)^\lambda C_\lambda = 1 + (-1)^n$; the height function has exactly two critical points, of indices $0$ and $n$.
- [ ] **51.** (V3.22) `[restated]` For $0 < \rho < R$ the torus of revolution is a compact smooth surface in $\mathbb R^3$, the regular zero set of a quartic polynomial. — Milnor §1, p. 1
- [ ] **52.** (V3.23) `[restated]` The height of the upright torus above its tangent plane has exactly four critical points, all non-degenerate, of indices $0, 1, 1, 2$, at heights $0, 2\rho, 2R, 2R + 2\rho$. — Milnor §1, p. 3
- [ ] **53.** (V3.24) `[narrower]` $T^a$ is empty for $a < 0$ and all of $T$ for $a \ge 2R + 2\rho$, and between consecutive critical values Theorem 3.1 holds on $T$. — Milnor §1, p. 1
- [ ] **54.** (V3.25) `[extra]` The Euler number of the torus is $0$, by Morse theory and by a nowhere-zero field, so every Morse function on it has $C_0 - C_1 + C_2 = 0$. — Milnor §1, p. 2
- [ ] **55.** (V3.26) `[extra]` Relative singular homology $H_n(X, A)$ is functorial in pairs, has the exact sequence of a pair, is homotopy invariant, and $H_n(B, A) \cong H_n(X, A)$ when $B \supseteq A$ is a strong deformation retract of $X$. — Milnor §5, pp. 28–29
- [ ] **56.** (V3.27) `[extra]` A triple $Z \subseteq Y \subseteq X$ has an exact sequence $\cdots \to H_n(Y, Z) \to H_n(X, Z) \to H_n(X, Y) \to H_{n-1}(Y, Z) \to \cdots \to H_0(X, Y) \to 0$. — Milnor §5, pp. 28–30
- [ ] **57.** (V3.28) `[extra]` If the closure of $Z$ lies in the interior of $A$, then $(X \setminus Z, A \setminus Z) \to (X, A)$ induces isomorphisms in homology. — Milnor §5, p. 29
- [ ] **58.** (V3.29) If the interiors of $A$ and $B$ cover $X$, the Mayer–Vietoris sequence of $A \cap B$, $A$ and $B$, and $X$ is exact.
- [ ] **59.** (V3.30) `[extra]` $H_i(D^n, S^{n-1})$ is the coefficient ring for $i = n$ and $0$ otherwise, and $H_i(S^n)$, $n \ge 1$, is the coefficient ring for $i = 0$ and $i = n$ and $0$ otherwise. — Milnor §5, p. 29
- [ ] **60.** (V3.31) `[stronger]` Attaching disjoint cells to a closed subset $Y$ of a Hausdorff space gives $H_i(X, Y) \cong R^{c_i}$, $c_i$ the number of cells of dimension $i$. — Milnor §5, p. 29
- [ ] **61.** (V3.32) `[restated]` For a filtration $X_0 \subseteq \dots \subseteq X_n$ whose steps have finite-dimensional homology, the Betti numbers of $(X_n, X_0)$ satisfy the weak and strong Morse inequalities and the Euler characteristic formula against the sums $C_i$ over the steps. — Milnor §5, pp. 28–30
- [ ] **62.** (V3.33) `[restated]` If $A$, $B \cup \bigcup_j e_j$ and $X'$ are strong deformation retracts of $B$, $X'$ and $X$ respectively, then $\dim H_i(X, A)$ is the number of cells $e_j$ of dimension $i$. — Milnor §5, pp. 28–29
- [ ] **63.** (V3.34) `[narrower]` For a function with non-degenerate critical points on a compact submanifold, a slab between two non-critical levels containing one critical value has homology of dimension the number of critical points of each index in it; $H_*(N)$ is finite-dimensional. — Milnor §5, p. 29
- [ ] **64.** (V3.35) `[narrower]` For such a function on a compact $N$, over every field, $b_\lambda(N) \le C_\lambda$, $\sum (-1)^i b_i = \sum (-1)^\lambda C_\lambda$, and $b_i = 0$ above $\dim N$. — Milnor §5, Theorem 5.2
- [ ] **65.** (V3.36) `[narrower]` For such a function, $b_\lambda - b_{\lambda-1} + \dots \pm b_0 \le C_\lambda - C_{\lambda-1} + \dots \pm C_0$. — Milnor §5, the Morse inequalities
- [ ] **66.** (V3.37) `[narrower]` If $C_{\lambda+1} = C_{\lambda-1} = 0$, then $b_\lambda = C_\lambda$ and $b_{\lambda \pm 1} = 0$; if no two consecutive $C_i$ are nonzero, then $b_i = C_i$ for all $i$. — Milnor §5, Corollary 5.4
- [ ] **67.** (V3.38) `[restated]` The Poincaré–Hopf integer of a compact submanifold, and $\chi(M)$ of a compact manifold, equal $\sum_i (-1)^i \dim H_i(\,\cdot\,; \Bbbk)$ for every field $\Bbbk$. — Milnor §5, p. 28, and formula (3)
- [ ] **68.** (V3.39) `[explicit]` On every compact Hausdorff manifold and for every Morse function, the weak and strong inequalities, formula (3) and the lacunary principle hold for the Betti numbers over every field. — Milnor §5, Theorem 5.2 and Corollary 5.4
- [ ] **69.** (V3.40) Over every field: a function with exactly two critical points, both non-degenerate, on $M^n$, $n \ge 2$, forces $b_0 = b_n = 1$ and $b_i = 0$ otherwise; $S^n$ has Euler characteristic $1 + (-1)^n$; the torus has $b_0 - b_1 + b_2 = 0$.
- [ ] **70.** (V3.41) `[restated]` The Hermitian projections of trace $1$ in $M_{n+1}(\mathbb C)$ form a compact submanifold of dimension $2n$, which is $\mathbb CP^n$, and Milnor's functions $x_j, y_j$ on $U_k$ are coordinates on it. — Milnor §4, p. 26
- [ ] **71.** (V3.42) `[same]` For distinct $c_j$, $f = \sum c_j|z_j|^2$ on $\mathbb CP^n$ has exactly the $n + 1$ critical points $p_k$, all non-degenerate, $p_k$ of index $2\,\#\{j : c_j < c_k\}$; so there is one critical point of each index $0, 2, \dots, 2n$. — Milnor §4, pp. 26–27
- [ ] **72.** (V3.43) `[narrower]` $\mathbb CP^n$ has the homotopy type of a space with one cell in each dimension $0, 2, \dots, 2n$, and over every field its Betti numbers are $1$ in those degrees and $0$ elsewhere. — Milnor §4, p. 27

## Chapter 4 (Milnor §6)

- [ ] **73.** (V4.1) `[stronger]` For a $k$-dimensional submanifold $M \subseteq \mathbb R^n$, the normal bundle $N$ is an $n$-dimensional submanifold of $\mathbb R^n \times \mathbb R^n$, and $E(q, v) = q + v$. — Milnor §6, p. 32
- [ ] **74.** (V4.2) `[explicit]` $e$ is a focal point of $(M, q)$ of multiplicity $\mu$ iff $(q, e - q) \in N$ and $dE$ has nullity $\mu > 0$ there; the focal points of $M$ are the critical values of $E$. — Milnor §6, Definition
- [ ] **75.** (V4.3) `[narrower]` For a smooth map from a second countable manifold into a finite-dimensional vector space, the image of the points where the derivative is not onto has measure zero. — Milnor §6, Theorem 6.1 (Sard)
- [ ] **76.** (V4.4) `[explicit]` Almost no point of $\mathbb R^n$ is a focal point of $M$. — Milnor §6, Corollary 6.2
- [ ] **77.** (V4.5) `[restated]` In the slice-chart coordinates $x$ at $q$, $g = \langle dx\,\cdot, dx\,\cdot\rangle$ and $\ell_v = \langle v, d^2x(\cdot, \cdot)\rangle$ are Milnor's first and second fundamental forms. — Milnor §6, pp. 33–34
- [ ] **78.** (V4.6) `[restated]` The principal curvatures in a normal direction $v$ are the eigenvalues, with multiplicity, of the self-adjoint shape operator $S_v$ on $T_qM$. — Milnor §6, p. 34
- [ ] **79.** (V4.7) `[stronger]` The focal points of $(M, q)$ on the normal line $q + tv$ are the points $q + K^{-1}v$, $K \ne 0$ a principal curvature, with the multiplicity of $K$; at most $k$ of them counted with multiplicity. — Milnor §6, Lemma 6.3
- [ ] **80.** (V4.8) `[restated]` The nullity of $dE$ at $(q, v) \in N$ equals the nullity of $g - \ell_v$. — Milnor §6, proof of Lemma 6.3
- [ ] **81.** (V4.9) `[stronger]` $q + tv$ is a focal point of $(M, q)$ of multiplicity $\mu$ iff $g - t\ell_v$ has nullity $\mu > 0$; $q$ itself is never one. — Milnor §6, Assertion 6.4
- [ ] **82.** (V4.10) `[stronger]` $q$ is a critical point of $L_p$ iff $p - q$ is normal to $M$ at $q$, and the Hessian of $L_p$ in the coordinates $x$ is $2(g - \ell_{p-q})$. — Milnor §6, pp. 35–36
- [ ] **83.** (V4.11) `[explicit]` $q$ is a degenerate critical point of $L_p$ iff $p$ is a focal point of $(M, q)$, the nullity being the multiplicity. — Milnor §6, Lemma 6.5
- [ ] **84.** (V4.12) `[stronger]` For almost every $p \in \mathbb R^n$, $L_p$ is a Morse function on $M$. — Milnor §6, Theorem 6.6
- [ ] **85.** (V4.13) `[narrower]` A closed submanifold of $\mathbb R^n$ carries a Morse function all of whose sublevel sets are compact. — Milnor §6, Corollary 6.7
- [ ] **86.** (V4.14) `[extra]` The image of a smooth topological embedding with injective derivative is a submanifold, and the embedding is a diffeomorphism onto it. — Milnor §6, proof of Corollary 6.7
- [ ] **87.** (V4.15) `[extra]` Critical points, Hessians, non-degeneracy, index, nullity and the numbers $C_\lambda$ are preserved by diffeomorphisms. — Milnor §6, p. 36
- [ ] **88.** (V4.16) `[narrower]` Every compact Hausdorff manifold is diffeomorphic to a compact submanifold of some $\mathbb R^{K+1}$, $K \ge 1$. — Milnor §6, proof of Corollary 6.7
- [ ] **89.** (V4.17) `[narrower]` Every compact Hausdorff manifold carries a Morse function. — Milnor §6, Corollary 6.7
- [ ] **90.** (V4.18) `[restated]` $\chi(M)$ is defined as $\sum_\lambda (-1)^\lambda C_\lambda(f)$ for a chosen Morse function $f$. — Milnor §5, formula (3)
- [ ] **91.** (V4.19) `[restated]` On a compact Hausdorff manifold every Morse function gives the same $\sum_\lambda (-1)^\lambda C_\lambda = \chi(M)$, which is the index sum of every tangent field on every embedded copy. — Milnor §6, Application 2
- [ ] **92.** (V4.20) `[extra]` For every smooth $f$ on a submanifold of $\mathbb R^n$, $f + \langle a, \cdot\rangle$ is a Morse function for almost every $a$. — Milnor §6, proof of Corollary 6.8
- [ ] **93.** (V4.21) `[stronger]` Every smooth function on a submanifold of $\mathbb R^n$, bounded or not, is a uniform limit of Morse functions, with derivatives up to any order converging on compact pieces of coordinate charts. — Milnor §6, Corollary 6.8
- [ ] **94.** (V4.22) `[narrower]` The same holds on every compact Hausdorff manifold. — Milnor §6, Corollary 6.8
- [ ] **95.** (V4.23) `[restated]` The index of $L_p$ at a non-degenerate critical point $q$ is the number of focal points of $(M, q)$ on the segment from $q$ to $p$, counted with multiplicity. — Milnor §6, Lemma 6.9
- [ ] **96.** (V4.24) `[explicit]` A compact Hausdorff manifold carrying a smooth function with exactly two critical points, both non-degenerate, is homeomorphic to $S^n$. — Milnor §4, Theorem 4.1 (Reeb)

## Chapter 5 (Milnor §7)

- [ ] **97.** (V5.1) The Hessian is the second derivative, defined at every point; the index of a bilinear form is the largest dimension of a subspace on which it is negative definite, and the nullity is the dimension of its null space.
- [ ] **98.** (V5.2) `[stronger]` $\operatorname{Re}B$ of a complex bilinear form is Milnor's $Q'$, multiplication by $i$ is an orthogonal map with square $-1$, and it changes the sign of $\operatorname{Re}B$. — Milnor §7, p. 39
- [ ] **99.** (V5.3) `[restated]` The eigenvalues of the matrix of $Q'$ come in pairs $\pm e$ of equal multiplicity. — Milnor §7, Assertion 1
- [ ] **100.** (V5.4) `[extra]` If $G$ is $J$-invariant and $L$ is $J$-anti-invariant, then $G - tL$ and $G + tL$ have the same nullity, and so do $L - eG$ and $L + eG$. — Milnor §7, p. 40
- [ ] **101.** (V5.5) `[explicit]` A vector whose real inner product with every vector of a complex subspace vanishes is Hermitian-orthogonal to that subspace. — Milnor §7, proof of Assertion 2
- [ ] **102.** (V5.6) `[restated]` In holomorphic coordinates the Hessian of $\|w(\cdot) - p\|^2$ is twice the first fundamental form plus twice $\operatorname{Re}\langle w(q) - p, d^2w_q\rangle$. — Milnor §7, proof of Assertion 2
- [ ] **103.** (V5.7) `[restated]` In a holomorphic chart, the Hessians of $L_p$ for $p = w(q) \pm tn$ have the same nullity (Assertion 2, before the translation into focal points). — Milnor §7, Assertion 2
- [ ] **104.** (V5.8) `[extra]` If $H = G - L$ on the diagonal with $G$ $J$-invariant and $L$ $J$-anti-invariant, then $H(Jv, Jv) = 2G(v, v) - H(v, v)$. — Milnor §7, p. 41
- [ ] **105.** (V5.9) `[extra]` If $H(v, v) + H(Jv, Jv) \ge 0$ for an injective linear $J$, the index of $H$ is at most half the real dimension. — Milnor §7, p. 41
- [ ] **106.** (V5.10) `[stronger]` A real form $G - \operatorname{Re}B$ on $\mathbb C^k$, with $G \ge 0$ invariant under $v \mapsto iv$ and $B$ complex bilinear, has index at most $k$. — Milnor §7, p. 41
- [ ] **107.** (V5.11) `[stronger]` For $w$ holomorphic near $q$ on a $k$-dimensional complex space, the Hessian of $\|w(\cdot) - p\|^2$ at $q$ has index at most $k$, whether or not $q$ is critical or non-degenerate. — Milnor §7, proof of Theorem 7.2
- [ ] **108.** (V5.12) If moreover $G$ is positive definite and the space is non-zero, the form takes a positive value.
- [ ] **109.** (V5.13) `[stronger]` On a submanifold of $\mathbb R^{2m}$ whose tangent spaces are complex subspaces, of real dimension $2k$, every critical point of $L_p = \|\cdot - p\|^2$ has index at most $k$. — Milnor §7, proof of Theorem 7.2, pp. 39–41
- [ ] **110.** (V5.14) `[extra]` If no critical point between two regular levels $a < b$ has index $j$, and the slab between them is compact with non-degenerate critical points, then $H_j(N^b, N^a) = 0$ over a field. — Milnor §§3, 5; used on pp. 39, 42
- [ ] **111.** (V5.15) `[restated]` Theorem 7.2: a closed submanifold of $\mathbb R^{2m}$ of dimension $2k$ with complex tangent spaces has the homotopy type of a countable cell complex with cells of dimension at most $k$. — Milnor §7, Theorem 7.2
- [ ] **112.** (V5.16) `[narrower]` Theorem 7.1 over a field: such a submanifold has no homology above degree $k$. — Milnor §7, Theorem 7.1
- [ ] **113.** (V5.17) `[restated]` If $X$ is compact, $X \setminus A$ is such a submanifold going to infinity at $A$, and a neighbourhood of $A$ deforms into $A$ keeping $A$ fixed, then $H_r(X, A) = 0$ for $r < k$ over a field, and $H_r(A) \to H_r(X)$ is bijective for $r < k - 1$ and surjective for $r = k - 1$. — Milnor §7, pp. 41–42
- [ ] **114.** (V5.18) `[narrower]` Corollary 7.3 over a field: this holds for a closed $V \subseteq \mathbb CP^n$ and the hyperplane $P = \{z_0 = 0\}$, when the affine part of $V$ is a complex submanifold of complex dimension $k$ and a neighbourhood of $V \cap P$ deforms into it. — Milnor §7, Corollary 7.3
- [ ] **115.** (V5.19) `[restated]` Theorem 7.4: under the same hypotheses every map $I^r \to V$, $r < k$, deforms into $V \cap P$ relative to the part already there; so $\pi_i(V \cap P) \to \pi_i(V)$ is bijective for $i < k - 1$ and surjective for $i = k - 1$. — Milnor §7, Theorem 7.4, pp. 41–42

## Chapter 6 (Milnor §§8–9)

- [ ] **116.** (V6.1) `[narrower]` In the embedded setting, $T_qN$ is the range of the derivative of the inclusion, $P_q$ the orthogonal projection onto it, and a vector field is a map $N \to V$ with tangent values. — Milnor §8, pp. 43–44
- [ ] **117.** (V6.2) $q \mapsto P_q$ is smooth, so every tangent vector $u$ at a point extends to the smooth vector field $q \mapsto P_qu$.
- [ ] **118.** (V6.3) `[restated]` A Mathlib covariant derivative satisfies Milnor's rules (2)–(4) at points where the sections involved are differentiable; his (1) is a separate smoothness class. — Milnor §8, pp. 43–44
- [ ] **119.** (V6.4) `[narrower]` $X \vdash Y = P(dY(X))$ is tangent and satisfies Milnor's rules (1)–(4). — Milnor §8, p. 44
- [ ] **120.** (V6.5) `[narrower]` $DX/dt = P(X')$ satisfies Milnor's axioms (a), (b), (c). — Milnor §8, pp. 45–46
- [ ] **121.** (V6.6) `[narrower]` Every operation satisfying (a), (b), (c) along a smooth curve equals $P(X')$ on smooth fields along the curve. — Milnor §8, Lemma 8.1
- [ ] **122.** (V6.7) `[narrower]` Linear equations $x' = A(t)x$ have unique solutions, and global ones when $A(t)$ is skew-adjoint. — Milnor §8, proof of Lemma 8.2
- [ ] **123.** (V6.8) `[narrower]` Along a smooth curve, through every tangent vector at any time there is exactly one parallel field, defined for all $t$ and smooth. — Milnor §8, Lemma 8.2
- [ ] **124.** (V6.9) `[stronger]` Parallel fields have constant inner products, and parallel translation is a linear isometry between tangent spaces, the identity at equal times and transitive. — Milnor §8, p. 47
- [ ] **125.** (V6.10) `[narrower]` $\frac{d}{dt}\langle X, Y\rangle = \langle DX/dt, Y\rangle + \langle X, DY/dt\rangle$ for fields along any curve. — Milnor §8, Lemma 8.3
- [ ] **126.** (V6.11) `[restated]` $v\langle Y, Y'\rangle = \langle v \vdash Y, Y'\rangle + \langle Y, v \vdash Y'\rangle$; on an abstract manifold this identity is the definition of compatibility, equal to Mathlib's. — Milnor §8, Corollary 8.4
- [ ] **127.** (V6.12) `[extra]` $\mathrm{II}_q(v, w) = D_vw$ is the normal part of $dW_q(v)$ for any field $W$ with $W(q) = w$; it is normal, symmetric, and $D_v$ is self-adjoint. — Milnor §6, p. 33
- [ ] **128.** (V6.13) `[explicit]` The ambient bracket of tangent fields is tangent and is Milnor's Poisson bracket, and the induced connection is symmetric; on an abstract manifold symmetric means torsion-free. — Milnor §8, Definition 8.5
- [ ] **129.** (V6.14) `[narrower]` $P(dY(X))$ is symmetric and compatible, and any symmetric compatible operation agrees with it on smooth fields; on an abstract manifold two symmetric compatible connections agree on differentiable fields. — Milnor §8, Lemma 8.6
- [ ] **130.** (V6.15) `[narrower]` $\frac{D}{\partial x}\frac{\partial s}{\partial y} = \frac{D}{\partial y}\frac{\partial s}{\partial x}$ for every smooth surface in $N$. — Milnor §8, Lemma 8.7
- [ ] **131.** (V6.16) `[same]` Milnor's $R(X, Y)Z = -X \vdash (Y \vdash Z) + Y \vdash (X \vdash Z) + [X, Y] \vdash Z$ is the negative of Nomizu's curvature. — Milnor §9, p. 51
- [ ] **132.** (V6.17) `[narrower]` For smooth vector fields on $N$, $R(X, Y)Z = \mathrm{II}(Y, \mathrm{II}(X, Z)) - \mathrm{II}(X, \mathrm{II}(Y, Z))$, so $R$ is a tensor. — Milnor §9, Lemma 9.1
- [ ] **133.** (V6.18) `[extra]` $\langle R(X, Y)Z, W\rangle = \langle\mathrm{II}(X, Z), \mathrm{II}(Y, W)\rangle - \langle\mathrm{II}(X, W), \mathrm{II}(Y, Z)\rangle$, with Milnor's sign.
- [ ] **134.** (V6.19) `[narrower]` $\frac{D}{\partial y}\frac{D}{\partial x}W - \frac{D}{\partial x}\frac{D}{\partial y}W = R(\partial s/\partial x, \partial s/\partial y)W$ for every smooth tangent field along a smooth surface. — Milnor §9, Lemma 9.2
- [ ] **135.** (V6.20) `[narrower]` The curvature of $N$ satisfies Lemma 9.3 (1)–(3), pointwise and for smooth vector fields. — Milnor §9, Lemma 9.3
- [ ] **136.** (V6.21) `[stronger]` Skew-symmetry in each pair and the cyclic identity imply pair symmetry (Lemma 9.3 (4)). — Milnor §9, Lemma 9.3
- [ ] **137.** (V6.22) `[stronger]` The sectional curvature $K(X, Y)$ depends only on the plane, and is the same in Milnor's and in the standard sign convention. — Milnor §19, Remark after Lemma 19.1
- [ ] **138.** (V6.23) A curvature tensor is determined by its sectional curvatures.
- [ ] **139.** (V6.24) `[extra]` Constant sectional curvature $\kappa$ means $R(X, Y)Z = \kappa(\langle X, Z\rangle Y - \langle Y, Z\rangle X)$ in Milnor's sign.
- [ ] **140.** (V6.25) `[extra]` The unit sphere has $\mathrm{II}_q(v, w) = -\langle v, w\rangle q$ and constant sectional curvature $1$.

## Chapter 7 (Milnor §10)

- [ ] **141.** (V7.1) `[narrower]` A geodesic of $N$ on an open interval is a smooth curve in $N$ whose acceleration in $V$ is normal to $N$, that is, $\frac{D}{dt}\frac{d\gamma}{dt} = 0$. — Milnor §10, p. 55
- [ ] **142.** (V7.2) `[stronger]` A geodesic on an interval has constant speed, its length on $[a, b]$ is its speed times $b - a$, and $t \mapsto \gamma(at + b)$ is again a geodesic. — Milnor §10, pp. 55 and 57
- [ ] **143.** (V7.3) `[restated]` A smooth curve in $N$ is a geodesic iff $\gamma'' = \mathrm{II}(\gamma', \gamma')$, iff $(\gamma, \gamma')$ is an integral curve of the spray $(x, v) \mapsto (v, \mathrm{II}_x(v, v))$; solutions of the chart equation $u'' = -\Gamma(u)(u', u')$ are geodesics. — Milnor §10, p. 55
- [ ] **144.** (V7.4) `[stronger]` $u'' = F(u, u')$, $F$ smooth, has solutions for a uniform time, depending smoothly on $(u_0, v_0, t)$, and two solutions with the same initial data agree on every common interval. — Milnor §10, Theorem 10.1
- [ ] **145.** (V7.5) `[explicit]` Two geodesics on an interval with the same position and velocity at one time coincide. — Milnor §10, pp. 56–58
- [ ] **146.** (V7.6) `[stronger]` Near each point there are $U$ and $\varepsilon$ such that every tangent vector $v$ at $p \in U$ with $\|v\| < \varepsilon$ is the initial velocity of a unique geodesic on $(-2, 2)$, depending smoothly on $(p, v, t)$. — Milnor §10, Lemma 10.2
- [ ] **147.** (V7.7) `[restated]` $\exp_q(v) = \gamma(1)$ for the geodesic $\gamma$, defined near $[0, 1]$, with $\gamma(0) = q$ and $\gamma'(0) = v$; it is well defined, $\exp_q(0) = q$, and $\gamma(t) = \exp_q(tv)$. — Milnor §10, pp. 57–58
- [ ] **148.** (V7.8) `[stronger]` $\exp$ is defined and smooth on a neighbourhood of the zero section of $TN$, and the derivative of $\exp_q$ at $0$ is the inclusion of $T_qN$. — Milnor §10, p. 58
- [ ] **149.** (V7.9) `[restated]` $\varepsilon$ is a normal radius at $q$ when $\exp_q$ maps the open $\varepsilon$-ball of $T_qN$ diffeomorphically onto an open subset of $N$. — Milnor §10, Lemma 10.3 (3)
- [ ] **150.** (V7.10) `[restated]` Every point has a neighbourhood $W$ and an $\varepsilon > 0$ such that for $q_1, q_2 \in W$ exactly one $v$ with $\|v\| < \varepsilon$ has $\exp_{q_1}(v) = q_2$, $v$ depends smoothly on $(q_1, q_2)$, and $\varepsilon$ is a normal radius at every point of $W$. — Milnor §10, Lemma 10.3
- [ ] **151.** (V7.11) `[explicit]` Lengths of piecewise smooth paths are additive, unchanged by reversal and translation, at least the distance in $V$ of the endpoints, and zero only for constant paths. — Milnor §11, p. 67; used from p. 59
- [ ] **152.** (V7.12) `[stronger]` $\langle d(\exp_q)_w(w), d(\exp_q)_w(x)\rangle = \langle w, x\rangle$ inside a normal ball; in particular the radial geodesics are orthogonal to the images of the spheres. — Milnor §10, Lemma 10.5
- [ ] **153.** (V7.13) `[narrower]` Along a path in a punctured normal neighbourhood, the length is at least the increase of the radius $r$, and with equality the direction $v$ is constant. — Milnor §10, Lemma 10.6
- [ ] **154.** (V7.14) `[restated]` A path from $q$ that leaves the open normal ball of radius $s$ has a segment, from its last visit of $q$ to its first arrival on the shell of radius $s$, of length at least $s$. — Milnor §10, proof of Theorem 10.4, p. 61
- [ ] **155.** (V7.15) `[stronger]` The geodesic $t \mapsto \exp_{q_1}(tv)$ of Lemma 10.3 is not longer than any piecewise smooth path in $N$ with the same endpoints, and equality forces the same image. — Milnor §10, Theorem 10.4
- [ ] **156.** (V7.16) `[stronger]` A path from $q$ to $\exp_q(v)$ of length $\|v\|$ is $t \mapsto \exp_q(\rho(t)v)$ with $\rho$ continuous and nondecreasing from $0$ to $1$. — Milnor §10, Theorem 10.4, pp. 59 and 61
- [ ] **157.** (V7.17) `[stronger]` A piecewise smooth path parametrized by arc length and not longer than any path with the same endpoints is a geodesic, smooth at its break points, and extends to a geodesic on an open interval. — Milnor §10, Corollary 10.7
- [ ] **158.** (V7.18) `[restated]` The infimum $\rho$ of the lengths of joining paths is a metric on $N$ with values in $[0, \infty]$. — Milnor §10, p. 62
- [ ] **159.** (V7.19) `[restated]` Within a normal radius, $\rho(p, \exp_p v) = \|v\|$ and the metric balls are the normal balls; the metric balls form neighbourhood bases of the topology of $N$. — Milnor §10, p. 62
- [ ] **160.** (V7.20) `[restated]` For compact $K \subseteq N$ there is $\delta > 0$ such that points of $K$ at distance $< \delta$ are joined by a unique geodesic of length $< \delta$, which is minimal and depends smoothly on its endpoints. — Milnor §10, Corollary 10.8
- [ ] **161.** (V7.21) `[restated]` $\rho$ is at least the distance in $V$, continuous on $N \times N$, finite when $N$ is connected, and makes $N$ a metric space with its own topology. — Milnor §10, p. 62
- [ ] **162.** (V7.22) `[restated]` $(N, \rho)$ is complete if every $\rho$-Cauchy sequence converges in $N$; $N$ is geodesically complete if $\exp_q$ is defined on all of $T_qN$ for every $q$, which holds iff every geodesic on an open interval extends to a geodesic on $\mathbb R$. — Milnor §10, pp. 58, 62 and 64
- [ ] **163.** (V7.23) `[explicit]` Every geodesic is $t \mapsto \exp_q(tv)$; near each point geodesics of bounded speed exist for a uniform time and can be continued, and $\exp$ is continuous on its domain, which is open in $TN$. — Milnor §10, pp. 57, 58, 62 and 64
- [ ] **164.** (V7.24) `[restated]` A minimal geodesic on $[a, b]$ is a geodesic no longer than any piecewise smooth path in $N$ with the same endpoints; $t \mapsto \exp_p(tv)$ on $[0, 1]$ is one when $\rho(p, \exp_p v) = \|v\|$. — Milnor §10, pp. 61–62
- [ ] **165.** (V7.25) `[explicit]` For $0 < \delta < \varepsilon$ and $\delta < \rho(p, q) < \infty$ some point $p_0$ of the sphere of radius $\delta$ about $p$ has $\rho(p, q) = \delta + \rho(p_0, q)$; a broken path made of two unit-speed geodesics and of minimal length is unbroken. — Milnor §10, proof of Theorem 10.9, pp. 63–64
- [ ] **166.** (V7.26) `[stronger]` If $\exp_p$ is defined on all of $T_pN$, every point at finite distance from $p$ is joined to $p$ by a minimal geodesic of length $\rho(p, q)$; in a connected geodesically complete $N$ any two points are. — Milnor §10, Theorem 10.9
- [ ] **167.** (V7.27) `[stronger]` If $N$ is connected and $\exp_p$ is defined on all of $T_pN$ for one $p$, every bounded set has compact closure in $N$, and then $(N, \rho)$ is complete. — Milnor §10, Corollary 10.10
- [ ] **168.** (V7.28) `[stronger]` If $(N, \rho)$ is complete, $N$ is geodesically complete. — Milnor §10, p. 64
- [ ] **169.** (V7.29) `[stronger]` For connected nonempty $N$, metric completeness, geodesic completeness, completeness of $\exp_p$ at one point, and compactness of the closures of bounded sets are equivalent; then closed bounded sets are compact. — Milnor §10, p. 64
- [ ] **170.** (V7.30) `[extra]` A connected submanifold that is closed in $V$, for instance a compact one, is complete in all these senses; any two points of $S^n$, $n \ge 1$, are joined by a minimal geodesic. — Milnor §10, cf. p. 65

## Chapter 8 (Milnor §§11–13)

- [ ] **171.** (V8.1) `[restated]` $\Omega(N; p, q)$ is the set of piecewise smooth paths in $N$ on $[0, 1]$ from $p$ to $q$, and $T\Omega_\omega$ the vector space of piecewise smooth tangent fields along $\omega$ vanishing at $0$ and $1$. — Milnor §11, p. 67
- [ ] **172.** (V8.2) `[stronger]` A variation is a map $\alpha(u, t)$, $u$ in an open set around $0$, with values in $N$ for $t \in [0, 1]$, fixed end points, and smooth on the closed strips of a subdivision; its variation field lies in $T\Omega_\omega$. — Milnor §11, p. 68
- [ ] **173.** (V8.3) `[stronger]` Every finite family of fields in $T\Omega_\omega$ is the family of variation fields of the variation $\exp_{\omega(t)}(\sum_j u_jW_j(t))$, $\|u\|$ small, without completeness. — Milnor §11, pp. 68 and 74
- [ ] **174.** (V8.4) `[narrower]` $\omega$ is a critical path of $E$ if every variation of $\omega$ has $\frac{d}{du} E(\bar\alpha(u)) = 0$ at $u = 0$. — Milnor §11, p. 69
- [ ] **175.** (V8.5) `[stronger]` $E_a^b = \int_a^b \|c'\|^2$, and $(L_a^b)^2 \le (b - a)E_a^b$, with equality iff the speed is constant off the break points. — Milnor §12, p. 70
- [ ] **176.** (V8.6) `[narrower]` A geodesic that is no longer than any path of $\Omega$ has energy at most that of every path of $\Omega$. — Milnor §12, Lemma 12.1
- [ ] **177.** (V8.7) `[restated]` The first variation of $\omega$ in the direction $W$ is $-\sum_t\langle W_t, \Delta_tV\rangle - \int_0^1\langle W_t, A_t\rangle\,dt$, $\Delta_tV$ the jump of the velocity and $A$ the acceleration. — Milnor §12, p. 71
- [ ] **178.** (V8.8) `[extra]` On closed strips the mixed partials commute up to the edges, one may differentiate under the integral sign, and integration by parts over the pieces produces the jump terms. — Milnor §§12–13, pp. 71–76
- [ ] **179.** (V8.9) `[stronger]` For every variation and every $u$, $\frac12\frac{d}{du}E(\bar\alpha(u))$ is the first variation of $\bar\alpha(u)$ in the direction $\frac{\partial\alpha}{\partial u}(u, \cdot)$; at $u = 0$ this is Theorem 12.2. — Milnor §12, Theorem 12.2
- [ ] **180.** (V8.10) `[restated]` A geodesic of $\Omega$ is a path smooth on $[0, 1]$ with zero acceleration; a path of $\Omega$ is critical iff its first variation vanishes on $T\Omega_\omega$. — Milnor §12, p. 73
- [ ] **181.** (V8.11) `[explicit]` A path of $\Omega$ is a critical path of the energy iff it is a geodesic. — Milnor §12, Corollary 12.3
- [ ] **182.** (V8.12) `[restated]` $\frac{D}{\partial u}\frac{D}{\partial t}\frac{\partial F}{\partial t} = \frac{D}{\partial t}\frac{D}{\partial t}\frac{\partial F}{\partial u} + R(\frac{\partial F}{\partial t}, \frac{\partial F}{\partial u})\frac{\partial F}{\partial t}$ with Milnor's $R$, and the jumps of $\partial\alpha/\partial t$ can be differentiated in $u$. — Milnor §13, pp. 75–76
- [ ] **183.** (V8.13) `[restated]` For a 2-parameter variation of a geodesic, $\frac12\frac{\partial^2E}{\partial u_1 \partial u_2}(0, 0)$ exists and equals $-\sum_t\langle W_2, \Delta_t\frac{DW_1}{dt}\rangle - \int_0^1\langle W_2, \frac{D^2W_1}{dt^2} + R(V, W_1)V\rangle\,dt$. — Milnor §13, Theorem 13.1
- [ ] **184.** (V8.14) `[restated]` $E_{**}$, defined on $T\Omega_\gamma$ by this formula, is Milnor's Hessian: at a geodesic every 2-parameter variation computes it, and every pair of fields comes from one. — Milnor §13, p. 74
- [ ] **185.** (V8.15) `[extra]` $\frac12E_{**}(W_1, W_2) = \int_0^1(\langle\frac{DW_1}{dt}, \frac{DW_2}{dt}\rangle - \langle R(V, W_1)V, W_2\rangle)\,dt$. — Milnor §13, cf. pp. 75–76
- [ ] **186.** (V8.16) `[restated]` $E_{**}$ is a symmetric bilinear form on $T\Omega_\gamma$. — Milnor §13, Corollary 13.4
- [ ] **187.** (V8.17) `[explicit]` For a 1-parameter variation of a geodesic with variation field $W$, $\frac{d^2E(\bar\alpha(u))}{du^2}(0) = E_{**}(W, W)$. — Milnor §13, Remark 13.5
- [ ] **188.** (V8.18) `[narrower]` At a minimal geodesic, $E_{**}(W, W) \ge 0$ for every $W \in T\Omega_\gamma$. — Milnor §13, Lemma 13.6

## Chapter 9 (Milnor §§14–15)

- [ ] **189.** (V9.1) `[stronger]` Linear equations $x' = A(t)x$ with continuous coefficients have solutions on all of $\mathbb R$ through every initial value, unique on closed intervals and smooth where $A$ is. — Milnor §14, p. 77
- [ ] **190.** (V9.2) `[restated]` A Jacobi field is a smooth tangent field with $\frac{D^2J}{dt^2} + R(V, J)V = 0$; one exists for all tangent initial values $(J(s), \frac{DJ}{dt}(s))$, and it is determined by them. — Milnor §14, p. 77
- [ ] **191.** (V9.3) `[stronger]` The Jacobi fields along $\gamma$ form a $2n$-dimensional space, isomorphic to $T_{\gamma(s)}N \times T_{\gamma(s)}N$ by $J \mapsto (J(s), \frac{DJ}{dt}(s))$ for every $s$. — Milnor §14, p. 77
- [ ] **192.** (V9.4) `[restated]` Parameters $a \ne b$ are conjugate if a non-zero Jacobi field vanishes at both; the multiplicity is the dimension of the space of such fields. — Milnor §14, p. 77
- [ ] **193.** (V9.5) `[restated]` At a geodesic, $W_1 \in T\Omega_\gamma$ is a null vector of $E_{**}$ iff it is a Jacobi field. — Milnor §14, Theorem 14.1
- [ ] **194.** (V9.6) `[restated]` At a geodesic, the nullity of $E_{**}$ is the multiplicity of $0$ and $1$ as conjugate parameters, and $E_{**}$ is degenerate iff they are conjugate. — Milnor §14, Theorem 14.1, pp. 77–79
- [ ] **195.** (V9.7) `[stronger]` At a geodesic, the nullity of $E_{**}$ is less than $n = \dim N$ when $n \ge 1$. — Milnor §14, Remark 14.2
- [ ] **196.** (V9.8) `[explicit]` The variation field of a smooth variation through geodesics is a Jacobi field. — Milnor §14, Lemma 14.3
- [ ] **197.** (V9.9) `[same]` Every Jacobi field along a geodesic $\gamma : [0, 1] \to N$ is the variation field of a smooth variation of $\gamma$ through geodesics. — Milnor §14, Lemma 14.4
- [ ] **198.** (V9.10) `[stronger]` At two non-conjugate parameters, the values of a Jacobi field determine it and can be prescribed. — Milnor §14, p. 81
- [ ] **199.** (V9.11) `[restated]` Along the short geodesic joining two points of a neighbourhood of Lemma 10.3, Jacobi fields are determined by their end values, which can be prescribed. — Milnor §14, Remark 14.5
- [ ] **200.** (V9.12) `[narrower]` Along any smooth curve, no parameter in some interval $(0, \delta)$ is conjugate to $0$. — Milnor §14, Remark 14.6
- [ ] **201.** (V9.13) `[restated]` The index of a bilinear form is the supremum of the dimensions of the finite-dimensional subspaces on which it is negative definite. — Milnor §15, p. 83; §2, p. 5
- [ ] **202.** (V9.14) `[extra]` A perpendicular summand on which the form is positive definite changes neither the index nor the null space; definiteness on a finite-dimensional subspace persists under continuous perturbation; and Milnor's compound matrix gives index at least $\lambda + \nu$. — Milnor §15, pp. 85–87
- [ ] **203.** (V9.15) `[explicit]` If $X$ is piecewise a Jacobi field, $E_{**}(X, Y)$ is $-2$ times the sum of the jumps of $\frac{DX}{dt}$ paired with the values of $Y$. — Milnor §15, pp. 84 and 87
- [ ] **204.** (V9.16) `[restated]` If a field has a zero within $h_0$ before every point, $\frac12E_{**}(X, X) \ge \int_0^1\|X\|^2$; hence parameters at most $h_0$ apart are never conjugate. — Milnor §15, pp. 83–84
- [ ] **205.** (V9.17) `[restated]` For a fine subdivision, broken Jacobi fields along $\gamma|[0, \tau]$ correspond bijectively to their values at the division points. — Milnor §15, pp. 83–84 and 86
- [ ] **206.** (V9.18) `[restated]` Lemma 15.3: the fields along $\gamma|[0, \tau]$ split into the broken Jacobi fields and $T'$, perpendicular for $E_{**}$, with $E_{**}$ positive definite on $T'$. — Milnor §15, Lemma 15.3
- [ ] **207.** (V9.19) `[restated]` Lemma 15.4: the index and the null space of $E_{**}$ along $\gamma|[0, \tau]$ are those on the broken Jacobi fields; the index is finite and the nullity is $\nu(\tau)$. — Milnor §15, Lemma 15.4
- [ ] **208.** (V9.20) `[restated]` $\lambda(\tau)$, the index of $E_{**}$ on the fields vanishing outside $[0, \tau]$, is non-decreasing and $0$ for small $\tau$, and $\lambda(1)$ is the index of $E_{**}$. — Milnor §15, p. 85
- [ ] **209.** (V9.21) `[explicit]` $\lambda(\tau)$ and $\nu(\tau)$ are the index and the nullity of a form $H_\tau$ on a fixed finite-dimensional space, continuous in $\tau$. — Milnor §15, p. 86
- [ ] **210.** (V9.22) `[same]` $\lambda$ is continuous from the left. — Milnor §15, Assertion (3)
- [ ] **211.** (V9.23) `[stronger]` $\lambda$ jumps by $\nu(\tau)$ just after $\tau$, and $\lambda(\tau') \ge \lambda(\tau) + \nu(\tau)$ for every $\tau' > \tau$. — Milnor §15, Assertion (4)
- [ ] **212.** (V9.24) `[stronger]` At a geodesic, the index of $E_{**}$ is the number of parameters in $(0, 1)$ conjugate to $0$, counted with multiplicity, and is finite. — Milnor §15, Theorem 15.1
- [ ] **213.** (V9.25) `[restated]` A geodesic segment has only finitely many parameters conjugate to $0$. — Milnor §15, Corollary 15.2

## Chapter 10 (Milnor §§16–17)

- [ ] **214.** (V10.1) `[restated]` Milnor's distance $d$, the largest distance of corresponding points plus the $L^2$ distance of the speeds, is a pseudometric on paths, vanishing for paths that agree on $[0, 1]$. — Milnor §16, p. 88
- [ ] **215.** (V10.2) `[stronger]` $\sqrt{E_a^b}$ is $1$-Lipschitz for $d$, so the energy is continuous, and a convergent sequence of paths has uniformly small energy on short intervals. — Milnor §16, p. 88
- [ ] **216.** (V10.3) `[restated]` Paths of energy at most $c$ lie in the ball $S$ of radius $\sqrt c$ about $p$, which is compact when $N$ is closed (or connected and complete), and all subdivisions with $t_{i+1} - t_i < \delta^2/c$ are fine enough. — Milnor §16, pp. 88–89
- [ ] **217.** (V10.4) `[stronger]` Lemma 16.1: the broken geodesics of energy less than $c$ correspond bijectively to their break points, which form an open subset $U$ of $N \times \dots \times N$, and their energy is $\sum_i\rho(x_i, x_{i+1})^2/(t_{i+1} - t_i)$. — Milnor §16, Lemma 16.1
- [ ] **218.** (V10.5) `[restated]` This correspondence and its inverse are continuous, and identify each $B^a$ with its set of break points up to homotopy. — Milnor §16, p. 89
- [ ] **219.** (V10.6) `[restated]` $E'$ is smooth on $U$, and its sublevel sets $B^a$, $a < c$, are compact. — Milnor §16, Theorem 16.2, pp. 90–91
- [ ] **220.** (V10.7) `[restated]` Milnor's deformation $r_u$ does not increase the energy, runs from the identity to the retraction onto $B$, fixes $B$, and is continuous in both variables. — Milnor §16, p. 91
- [ ] **221.** (V10.8) `[restated]` For $a < c$, $B^a$ is a strong deformation retract of $\Omega^a$. — Milnor §16, Theorem 16.2, pp. 90–91
- [ ] **222.** (V10.9) `[restated]` The critical points of $E'$ are exactly the break points of the unbroken geodesics of energy less than $c$, and every such geodesic is a broken geodesic. — Milnor §16, Theorem 16.2, pp. 90–91
- [ ] **223.** (V10.10) `[explicit]` For the subdivision of §16, broken Jacobi fields take arbitrary values at the break points and are determined by them, $E_{**}$ is positive definite on the fields vanishing there, and Lemma 15.4 holds. — Milnor §16, pp. 91–92
- [ ] **224.** (V10.11) `[explicit]` At a geodesic, the Hessian of $E'$ is $E_{**}$ on the broken Jacobi fields, so the two have the same index and the same nullity. — Milnor §16, Theorem 16.2, pp. 90 and 92
- [ ] **225.** (V10.12) `[narrower]` If $a < c$ is not the energy of a geodesic and the geodesics of energy at most $a$ are non-degenerate, they are finitely many, and $B^a$ has the homotopy type of a cell complex with one $\lambda$-cell for each of them of index $\lambda$. — Milnor §16, Theorem 16.3, and §3.5
- [ ] **226.** (V10.13) `[narrower]` Theorem 16.3: under the same hypotheses, $\Omega^a$ has that homotopy type and contains finitely many geodesics. — Milnor §16, Theorem 16.3
- [ ] **227.** (V10.14) `[narrower]` If some path has energy less than $c$, a minimum of $E'$ is a geodesic minimizing the energy on all of $\Omega$. — Milnor §16, Remark, p. 92
- [ ] **228.** (V10.15) `[restated]` $\Omega^*$ is the space of continuous paths with the topology of uniform convergence, and the inclusion $\Omega \to \Omega^*$ is continuous since $d^* \le d$. — Milnor §17, p. 93
- [ ] **229.** (V10.16) `[extra]` Convergence for $d$ implies $L^2$ convergence of the velocities, and, together with pointwise convergence, is implied by it. — Milnor §17, cf. p. 94
- [ ] **230.** (V10.17) `[extra]` Small ambient balls are good: two of their points are joined by a unique minimal geodesic, which stays in the ball and depends smoothly on its end points, and every compact set has a Lebesgue number for good balls. — Milnor §17, p. 93
- [ ] **231.** (V10.18) `[restated]` On the open set $Y_k$ of paths whose dyadic pieces of level $k$ lie in good balls, the dyadic broken geodesic is a homotopy inverse of the inclusion of $X_k = Y_k \cap \Omega$. — Milnor §17, p. 94
- [ ] **232.** (V10.19) `[same]` Theorem 17.1: the inclusion of $\Omega$, with Milnor's metric, into $\Omega^*$ is a homotopy equivalence; Milnor's map $h$ is not continuous for $d$, and the proof verified is the exposition's repair. — Milnor §17, Theorem 17.1
- [ ] **233.** (V10.20) `[restated]` Relative cell attachments carry over along homotopy equivalences, the relative Theorem 3.5 holds below a compact sublevel set, and a tower of relative cell attachments over sublevel sets that exhaust a space gives a countable cell complex. — Milnor §17, p. 95
- [ ] **234.** (V10.21) `[restated]` Between two levels below $c$ that are not energies of geodesics, $\Omega^b$ is, up to homotopy, $\Omega^a$ with one $\lambda$-cell attached for each geodesic of index $\lambda$ with energy in between. — Milnor §17, p. 95
- [ ] **235.** (V10.22) `[narrower]` Theorem 17.3: for $N$ closed in $V$ and $q$ not conjugate to $p$ along any geodesic, $\Omega(N; p, q)$ has the homotopy type of a countable cell complex with one $\lambda$-cell for each geodesic from $p$ to $q$ of index $\lambda$. — Milnor §17, Theorem 17.3
- [ ] **236.** (V10.23) `[restated]` For $q \ne \pm p$ on $S^n$, the geodesics from $p$ to $q$ are the great-circle arcs $\gamma_k$ with $k\pi < L(\gamma_k) < (k + 1)\pi$, $q$ is not conjugate to $p$ along any of them, and $\gamma_k$ has index $k(n - 1)$. — Milnor §17, pp. 95–96; §14, Example 2
- [ ] **237.** (V10.24) `[narrower]` Corollary 17.4 for $\Omega(S^n; p, q)$, $q \ne \pm p$, $n \ge 2$: one cell in each of the dimensions $0, n - 1, 2(n - 1), \dots$. — Milnor §17, Corollary 17.4
- [ ] **238.** (V10.25) `[restated]` A path space with one geodesic of index $kr$, $r \ge 2$, in the $k$-th energy window has Betti numbers $1$ in the degrees divisible by $r$ and $0$ in the others. — Milnor §17, p. 96
- [ ] **239.** (V10.26) `[narrower]` For $n \ge 3$ and $q \ne \pm p$, $H_i(\Omega(S^n; p, q))$ over a field has dimension $1$ if $n - 1$ divides $i$ and $0$ otherwise. — Milnor §17, p. 96
- [ ] **240.** (V10.27) `[extra]` $\mathbb R^{n+1} \setminus \{0\}$ has the homotopy type of $S^n$, no conjugate points and two points joined by a single geodesic, so Corollary 17.5 needs completeness. — Milnor §17, Corollary 17.5
- [ ] **241.** (V10.28) `[extra]` Every $q$ can be joined in $N$ to a point not conjugate to $p$, and a path from $q$ to $q'$ makes $\Omega(N; p, q)$ and $\Omega(N; p, q')$ homotopy equivalent. — Milnor §17, p. 96; §19, p. 106
- [ ] **242.** (V10.29) `[restated]` Corollary 17.2: for $N$ closed in a Euclidean space, $\Omega(N; p, q)$ and $\Omega^*(N; p, q)$ have the homotopy type of a countable cell complex. — Milnor §17, Corollary 17.2
- [ ] **243.** (V10.30) `[narrower]` Corollary 17.4 for loops: for $n \ge 2$ the loop space of $S^n$ has the homotopy type of a cell complex with one cell in each dimension $k(n - 1)$; for $n \ge 3$ its Betti numbers over a field are $1$ in the degrees divisible by $n - 1$ and $0$ otherwise. — Milnor §17, Corollary 17.4

## Chapter 11 (Milnor §§18–19)

- [ ] **244.** (V11.1) `[stronger]` The exponential map is defined on an open subset of $TN$ and is smooth there, without completeness. — Milnor §18, p. 98
- [ ] **245.** (V11.2) `[restated]` The domain of $\exp_q$ in $T_qN$ is open and star-shaped, $\exp_q$ is smooth on it, and $\exp_q$ is critical at $v$ when $d(\exp_q)_v$ is not one-to-one. — Milnor §18, p. 98
- [ ] **246.** (V11.3) `[stronger]` Theorem 18.1: $\exp_q(v)$ is conjugate to $q$ along $t \mapsto \exp_q(tv)$ iff $\exp_q$ is critical at $v$, the multiplicity being $\dim\ker d(\exp_q)_v$. — Milnor §18, Theorem 18.1
- [ ] **247.** (V11.4) `[extra]` The points conjugate to $p$ along some geodesic are exactly the critical values of $\exp_p$. — Milnor §18, p. 99
- [ ] **248.** (V11.5) `[restated]` Corollary 18.2: these points form a set of measure zero in every chart of $N$. — Milnor §18, Corollary 18.2
- [ ] **249.** (V11.6) `[stronger]` The points not conjugate to $p$ along any geodesic are dense, and every geodesic from $p$ to such a point has nullity $0$. — Milnor §18, p. 98
- [ ] **250.** (V11.7) `[restated]` Lemma 19.1: with $\langle R(A, B)A, B\rangle \le 0$, no two parameters are conjugate along any geodesic. — Milnor §19, Lemma 19.1
- [ ] **251.** (V11.8) `[stronger]` With $\langle R(A, B)A, B\rangle \le 0$, every geodesic has index and nullity $0$, $E_{**}$ is positive definite, and $\exp_p$ is nowhere critical. — Milnor §19, proof of Theorem 19.2, pp. 102–103
- [ ] **252.** (V11.9) `[same]` The Ricci tensor $K(U_1, U_2)$ is the trace of $W \mapsto R(U_1, W)U_2$; it is symmetric, and $K(U_n, U_n)$ is the sum of the sectional curvatures of the planes through $U_n$ and $U_i$. — Milnor §19, p. 104
- [ ] **253.** (V11.10) `[explicit]` A geodesic segment extends to a smooth curve on $\mathbb R$ along which its velocity is parallel, with parallel unit fields $P_1, \dots, P_{n-1}$ such that $\sum\langle R(V, P_i)V, P_i\rangle \ge L^2(n - 1)/r^2$ under the Ricci bound. — Milnor §19, proof of Theorem 19.4, p. 104
- [ ] **254.** (V11.11) `[restated]` $\frac12E_{**}(\sin(\pi t)P, \sin(\pi t)P) = \int_0^1(\pi^2\cos^2\pi t - \sin^2\pi t\, \langle R(V, P)V, P\rangle)\,dt$, and under the Ricci bound a geodesic longer than $\pi r$ has a field with $E_{**}(X, X) < 0$. — Milnor §19, proof of Theorem 19.4, p. 105
- [ ] **255.** (V11.12) `[explicit]` Theorem 19.4: for $n \ge 2$ and $K(U, U) \ge (n - 1)/r^2$, a geodesic longer than $\pi r$ contains a conjugate point and is not minimal. — Milnor §19, Theorem 19.4
- [ ] **256.** (V11.13) `[explicit]` Corollary 19.5: if moreover $N$ is connected and complete, its diameter is at most $\pi r$ and $N$ is compact. — Milnor §19, Corollary 19.5
- [ ] **257.** (V11.14) `[narrower]` The unit sphere $S^n$ has $K(U, U) = (n - 1)\|U\|^2$, so for $n \ge 2$ its geodesics longer than $\pi$ are not minimal and its diameter is at most $\pi$. — Milnor §19, Example, p. 105
- [ ] **258.** (V11.15) `[explicit]` Test fields supported in disjoint intervals are $E_{**}$-orthogonal, and on a piece $[a, b]$ with $L(b - a) > \pi r$ one of them has $E_{**}(X, X) < 0$. — Milnor §19, proof of Theorem 19.6, p. 106
- [ ] **259.** (V11.16) `[explicit]` Under the Ricci bound, a geodesic of length $> k\pi r$ has index at least $k$. — Milnor §19, proof of Theorem 19.6, p. 106
- [ ] **260.** (V11.17) `[same]` Theorem 19.2: a simply connected complete $N$ of curvature $\le 0$ has exactly one geodesic between any two points, and $\exp_p : T_pN \to N$ is a diffeomorphism. — Milnor §19, Theorem 19.2
- [ ] **261.** (V11.18) `[stronger]` In curvature $\le 0$, $\Omega(N; p, q)$ has the homotopy type of the discrete set of geodesics from $p$ to $q$, and is contractible when $N$ is simply connected. — Milnor §19, proof of Theorem 19.2, p. 102
- [ ] **262.** (V11.19) `[extra]` For complete $N$ with $\exp_p$ nowhere critical (e.g. curvature $\le 0$), $\exp_p : T_pN \to N$ is a covering map. — Milnor §19, p. 103
- [ ] **263.** (V11.20) `[same]` In a complete $N$ of curvature $\le 0$, each homotopy class of paths from $p$ to $q$ contains exactly one geodesic. — Milnor §19, p. 103
- [ ] **264.** (V11.21) `[narrower]` Corollary 19.3, first half: in a complete $N$ of curvature $\le 0$, $\pi_i(N) = 0$ for $i > 1$. — Milnor §19, Corollary 19.3
- [ ] **265.** (V11.22) `[narrower]` For $N$ compact with positive definite Ricci tensor and $q$ not conjugate to $p$, $\Omega(N; p, q)$ has the homotopy type of a countable cell complex with finitely many cells in each dimension. — Milnor §19, Theorem 19.6
- [ ] **266.** (V11.23) `[extra]` Under the same hypotheses its homology over any field is finite-dimensional in each degree. — Milnor §19, cf. Theorem 19.6, p. 106
- [ ] **267.** (V11.24) `[explicit]` Theorem 19.6 for all $p, q$: the same conclusions without the non-conjugacy hypothesis. — Milnor §19, Theorem 19.6

## Chapter 12 (Milnor §§20–21)

- [ ] **268.** (V12.1) `[restated]` A bi-invariant metric is modelled by a bilinear form on a Lie algebra, and its Levi-Civita connection on left-invariant fields by a bilinear $D$ with $D(X, Y) - D(Y, X) = [X, Y]$ and $B(D(X, Y), Z) + B(Y, D(X, Z)) = 0$. — Milnor §21, p. 113
- [ ] **269.** (V12.2) `[restated]` If moreover $D(X, X) = 0$ for all $X$, then $D(X, Y) = \tfrac12[X, Y]$. — Milnor §21, proof of Theorem 21.3, pp. 113–114
- [ ] **270.** (V12.3) `[restated]` Under the same hypotheses, $B([X, Y], Z) = B(X, [Y, Z])$. — Milnor §21, Theorem 21.3 (a)
- [ ] **271.** (V12.4) `[extra]` For a symmetric, non-degenerate, ad-invariant $B$, the Levi-Civita connection on the Lie algebra must be $\tfrac12[\,\cdot\,, \cdot\,]$, and it is one. — Milnor §21, cf. Theorem 21.3, p. 113
- [ ] **272.** (V12.5) `[restated]` With $D = \tfrac12[\,\cdot\,, \cdot\,]$, Milnor's curvature is $R(X, Y)Z = \tfrac14[[X, Y], Z]$. — Milnor §21, Theorem 21.3 (b)
- [ ] **273.** (V12.6) `[restated]` For ad-invariant $B$, $B(R(X, Y)Z, W) = \tfrac14B([X, Y], [Z, W])$. — Milnor §21, Theorem 21.3 (c)
- [ ] **274.** (V12.7) `[narrower]` For ad-invariant $B$, $B([X, Y], Z)$ is alternating in $X, Y, Z$. — Milnor §21, footnote, p. 114
- [ ] **275.** (V12.8) `[stronger]` $B(R(X, Y)X, Y) = \tfrac14B([X, Y], [X, Y])$, which is $\ge 0$ and vanishes iff $[X, Y] = 0$ when $B$ is positive definite. — Milnor §21, Corollary 21.4
- [ ] **276.** (V12.9) `[narrower]` With trivial centre and a positive definite ad-invariant $B$, the Ricci curvature $\operatorname{tr}K_V$ is positive for $V \neq 0$; it equals $-\tfrac14$ of the Killing form. — Milnor §21, Corollary 21.5
- [ ] **277.** (V12.10) `[narrower]` The orthogonal complement of the centre is an ideal, complementary to the centre, with trivial centre. — Milnor §21, Corollary 21.6
- [ ] **278.** (V12.11) `[stronger]` $K_V = -\tfrac14\operatorname{ad}_V^2$ is self-adjoint and positive semidefinite, with kernel the centralizer of $V$. — Milnor §21, proof of Theorem 21.7, pp. 116–117
- [ ] **279.** (V12.12) `[restated]` Every eigenspace of $K_V$ for a non-zero eigenvalue carries a complex structure and so has even dimension. — Milnor §21, proof of Theorem 21.7, p. 117
- [ ] **280.** (V12.13) `[restated]` A spectrum in which every positive eigenvalue has even multiplicity has even index, the index being defined by Theorems 20.5 and 15.1. — Milnor §21, proof of Theorem 21.7, p. 117
- [ ] **281.** (V12.14) `[narrower]` A matrix group $G$ with Lie algebra $\mathfrak g$ has $T_gG = g\mathfrak g$, its induced metric is bi-invariant, and the inner product on $\mathfrak g$ is ad-invariant. — Milnor §21, p. 112; §23, p. 125
- [ ] **282.** (V12.15) `[narrower]` The geodesics of a matrix group are the curves $t \mapsto g\exp(tX)$; those through $I$ are the one-parameter subgroups, and the group is complete. — Milnor §21, Lemma 21.2
- [ ] **283.** (V12.16) `[narrower]` $\sigma \mapsto \tau\sigma^{-1}\tau$ is an isometry of $G$ fixing $\tau$ and reversing the geodesics through $\tau$. — Milnor §21, Lemma 21.1
- [ ] **284.** (V12.17) `[narrower]` On a matrix group, $X \vdash Y = \tfrac12[X, Y]$, $R(X, Y)Z = \tfrac14[[X, Y], Z]$, and the sectional curvature is $\tfrac14\|[X, Y]\|^2 \ge 0$. — Milnor §21, Theorem 21.3 and Corollary 21.4
- [ ] **285.** (V12.18) `[narrower]` Along $\exp(tA)$, $\exp(tA/2)U(t)\exp(tA/2)$ is a Jacobi field whenever $U'' + \tfrac14[[A, U], A] = 0$ in $\mathfrak g$. — Milnor §20, Theorem 20.5

## Chapter 13 (Milnor §22)

- [ ] **286.** (V13.1) `[restated]` $\Omega^d$ is the set of paths of least energy, and these are geodesics. — Milnor §22, p. 118
- [ ] **287.** (V13.2) `[narrower]` Theorem 22.1: if the closed balls about $p$ are compact, every geodesic not of least energy has index $\ge \lambda_0$, and $\Omega^d$ is a retract of an open neighbourhood, then every map of a compact $P$ of dimension $< \lambda_0$ into $\Omega$ is homotopic, relative to the part already in $\Omega^d$, to a map into $\Omega^d$. — Milnor §22, Theorem 22.1
- [ ] **288.** (V13.3) `[narrower]` The inclusion $\Omega^d \to \Omega$ is bijective on $\pi_i$ for $i \le \lambda_0 - 2$ and onto for $i \le \lambda_0 - 1$, at every point of $\Omega^d$. — Milnor §22, p. 118
- [ ] **289.** (V13.4) `[narrower]` Corollary 22.2: $\pi_i(\Omega^d, \gamma) \cong \pi_{i+1}(N, p)$ for $i \le \lambda_0 - 2$ (bijection), onto for $i \le \lambda_0 - 1$. — Milnor §22, Corollary 22.2
- [ ] **290.** (V13.5) `[narrower]` Change of basepoint is a group isomorphism, and Corollary 22.2 holds as groups for $1 \le i \le \lambda_0 - 2$. — Milnor §22, Corollary 22.2
- [ ] **291.** (V13.6) `[restated]` The geodesics from $p$ to $-p$ on $S^{n+1}$ are the great circles of length $(2m + 1)\pi$, the minimal ones are the semicircles, and these form a space homotopy equivalent to the equator, and homeomorphic to it after identifying paths that agree on $[0, 1]$. — Milnor §22, proof of Corollary 22.3, p. 119
- [ ] **292.** (V13.7) `[same]` The great circle of length $(2m + 1)\pi$ from $p$ to $-p$ has index $2mn$; the non-minimal ones have index $\ge 2n$. — Milnor §22, proof of Corollary 22.3, p. 119
- [ ] **293.** (V13.8) `[extra]` $\Omega^d(S^{n+1}; p, -p)$ is a retract of the open set of paths whose midpoint is not $\pm p$. — Milnor §22, proof of Corollary 22.3, p. 119
- [ ] **294.** (V13.9) `[stronger]` Corollary 22.3: $\pi_iS^n \cong \pi_{i+1}S^{n+1}$ for $i \le 2n - 2$ (groups for $i \ge 1$), and onto for $i = 2n - 1$. — Milnor §22, Corollary 22.3
- [ ] **295.** (V13.10) `[stronger]` Lemma 22.4: a $C^2$-small perturbation of $f$ near a compact $K$ has no critical points in $K$ of index below $\lambda_0$ if $f$ has none. — Milnor §22, Lemma 22.4
- [ ] **296.** (V13.11) `[narrower]` On a submanifold, small linear perturbations keep the indices of critical points in a compact set $\ge \lambda_0$. — Milnor §22, proof of Lemma 22.5, p. 122
- [ ] **297.** (V13.12) `[extra]` Pushing maps is transitive, holds for strong deformation retracts, and holds for a closed set with finitely many disjoint cells of dimension $> \dim P$ attached. — Milnor §22, proof of Lemma 22.5, p. 122
- [ ] **298.** (V13.13) `[explicit]` Lemma D: across critical levels whose critical points are non-degenerate of index $\ge \lambda_0$, $N^a$ pushes maps of dimension $< \lambda_0$ out of $N^b$. — Milnor §22, proof of Lemma 22.5, p. 122
- [ ] **299.** (V13.14) `[narrower]` Lemma 22.5: given a neighbourhood $U$ of the minimum set from which it pushes maps, and indices $\ge \lambda_0$ off the minimum, the minimum set pushes maps of dimension $< \lambda_0$ out of every compact sublevel set. — Milnor §22, Lemma 22.5
- [ ] **300.** (V13.15) `[explicit]` In the model of broken geodesics, a neighbourhood retraction of $\Omega^d$ gives a neighbourhood of the minimum that deforms into it. — Milnor §22, proof of Lemma 22.5, p. 121
- [ ] **301.** (V13.16) `[narrower]` Theorem 22.1 holds for an open and closed set $\Omega'$ of paths when the index bound holds for the geodesics in $\Omega'$. — Milnor §24, p. 147

## Chapter 14 (Milnor §23)

- [ ] **302.** (V14.1) `[narrower]` $\exp\operatorname{diag}(ia_1, \dots, ia_n) = -I$ iff every $a_j$ is an odd multiple of $\pi$. — Milnor §23, p. 127
- [ ] **303.** (V14.2) `[restated]` For $A = \operatorname{diag}(i\pi k_j)$, $\operatorname{tr}AA^* = \pi^2\sum k_j^2$ and $\operatorname{tr}A = i\pi\sum k_j$. — Milnor §23, pp. 127, 130
- [ ] **304.** (V14.3) `[restated]` For odd $k_j$, $\sum k_j^2 \ge n$ with equality iff all $k_j = \pm1$; with $\sum k_j = 0$ and $n = 2m$, then $m$ are $+1$ and $m$ are $-1$. — Milnor §23, p. 127
- [ ] **305.** (V14.4) `[narrower]` A skew-Hermitian $A$ has $A^2 = -\pi^2I$ iff $A = i\pi(2P - I)$ for a Hermitian projection $P$, and then $\operatorname{tr}A = 0$ iff $\operatorname{tr}P = n/2$. — Milnor §23, pp. 127–128
- [ ] **306.** (V14.5) `[restated]` For diagonal $A = \operatorname{diag}(i\pi k_j)$, $\tfrac14[[A, W], A]$ multiplies the $(j, l)$ entry of $W$ by $\tfrac{\pi^2}{4}(k_j - k_l)^2$. — Milnor §23, pp. 130–131
- [ ] **307.** (V14.6) `[narrower]` $E_{jl}$, $E'_{jl}$ are skew-Hermitian traceless eigenvectors with eigenvalue $\tfrac{\pi^2}{4}(k_j - k_l)^2$, diagonal matrices are in the kernel, and together they span the skew-Hermitian matrices. — Milnor §23, p. 131
- [ ] **308.** (V14.7) `[restated]` The conjugate parameters of an eigenvalue $e$ are the $t \in (0, 1)$ in $\pi\mathbb Z/\sqrt e$, and for $e = (\pi d)^2$ there are $d - 1$ of them. — Milnor §20, Theorem 20.5, p. 110; §23, p. 131
- [ ] **309.** (V14.8) `[restated]` The index of a spectrum is the number of conjugate parameters in $(0, 1)$ counted with multiplicity, equivalently the sum over the eigenvalues of their numbers of conjugate parameters. — Milnor §23, p. 131
- [ ] **310.** (V14.9) `[restated]` For odd $k_j$, Milnor's spectrum has index $\sum_{k_i > k_j}(k_i - k_j - 2)$. — Milnor §23, p. 131
- [ ] **311.** (V14.10) `[same]` The formula is non-negative, symmetric under $k \mapsto -k$, independent of the order, and zero when all $k_j = \pm1$. — Milnor §23, pp. 130–132
- [ ] **312.** (V14.11) `[restated]` For odd $k_1, \dots, k_{2m}$ with sum $0$, not all $\pm1$, the formula is at least $2m + 2$. — Milnor §23, Lemma 23.2, p. 128; proof p. 132
- [ ] **313.** (V14.12) `[extra]` In $U(n + 1)$, $k = (3, 1, \dots, 1)$ gives index $0$ although it is not minimal, and its $\sum k_j$ is larger than that of any minimal geodesic. — Milnor §23, p. 127
- [ ] **314.** (V14.13) `[restated]` $U(n)$ and $SU(n)$ are compact submanifolds of the space of matrices and matrix groups, with Lie algebras $\mathfrak u(n)$ and $\mathfrak{su}(n)$. — Milnor §23, pp. 124–126
- [ ] **315.** (V14.14) `[same]` Every geodesic from $I$ to $-I$ in $SU(n)$ is $t \mapsto \exp(tA)$ with $A = T\operatorname{diag}(i\pi k_j)T^*$, $T$ unitary, $k_j$ odd, $\sum k_j = 0$. — Milnor §23, pp. 126–127, 130
- [ ] **316.** (V14.15) `[narrower]` In $SU(2m)$ the distance from $I$ to $-I$ is $\pi\sqrt{2m}$, and $\exp(tA)$ is minimal iff $A^2 = -\pi^2I$, iff all $k_j = \pm1$. — Milnor §23, p. 127
- [ ] **317.** (V14.16) `[restated]` The initial velocities of the minimal geodesics form a space homeomorphic to $G_m(\mathbb C^{2m})$, by $A \mapsto \tfrac12(I - \tfrac i\pi A)$. — Milnor §23, Lemma 23.1
- [ ] **318.** (V14.17) `[restated]` The space $\Omega^d$ of minimal paths is homotopy equivalent to that space of velocities, and homeomorphic to it after identifying paths that agree on $[0, 1]$. — Milnor §23, Lemma 23.1
- [ ] **319.** (V14.18) `[narrower]` Theorem 20.5 for $SU(n)$: the multiplicity of a conjugate parameter along $\exp(tA)$ is the dimension of an explicit kernel, which equals the count from Milnor's spectrum. — Milnor §20, Theorem 20.5, p. 110; §23, pp. 130–131
- [ ] **320.** (V14.19) `[same]` Every geodesic from $I$ to $-I$ in $SU(n)$ has index $\sum_{k_i > k_j}(k_i - k_j - 2)$. — Milnor §23, p. 131
- [ ] **321.** (V14.20) `[same]` In $SU(2m)$ every geodesic from $I$ to $-I$ not of least energy has index $\ge 2m + 2$. — Milnor §23, Lemma 23.2
- [ ] **322.** (V14.21) `[extra]` $\Omega^d(SU(2m); I, -I)$ is a neighbourhood retract, so $\pi_i\Omega^d \cong \pi_{i+1}SU(2m)$ for $i \le 2m$ (groups for $i \ge 1$). — Milnor §23, p. 128
- [ ] **323.** (V14.22) `[restated]` Theorem 23.3: $\pi_iG_m(\mathbb C^{2m}) \cong \pi_{i+1}SU(2m)$ for $i \le 2m$, at every point, as groups for $i \ge 1$. — Milnor §23, Theorem 23.3
- [ ] **324.** (V14.23) `[restated]` An equivariant map onto a homogeneous space with a local section of the orbit map is locally trivial; restricting frames and $U(n) \to V_k(\mathbb K^n)$ are locally trivial. — Milnor §23, pp. 128–129
- [ ] **325.** (V14.24) `[restated]` The frame-to-span map $V_m(\mathbb K^n) \to G_m(\mathbb K^n)$ is locally trivial with fibre $U(m)$. — Milnor §23, p. 129
- [ ] **326.** (V14.25) `[stronger]` $V_k(\mathbb C^n)$ is $2(n - k)$-connected, and $U(m) \to U(m + k)$ is bijective on $\pi_i$ for $i < 2m$, onto for $i \le 2m$. — Milnor §23, Lemma 23.4, pp. 128–129
- [ ] **327.** (V14.26) `[restated]` Lemma 23.4: $\pi_iG_m(\mathbb C^{2m}) \cong \pi_{i-1}U(m)$ for $1 \le i \le 2m$, as groups for $i \ge 2$. — Milnor §23, Lemma 23.4
- [ ] **328.** (V14.27) `[narrower]` $SU(n) \to U(n)$ is bijective on $\pi_j$ for $j \ge 2$. — Milnor §23, Lemma 23.4
- [ ] **329.** (V14.28) `[restated]` $\pi_{i-1}U(m) \cong \pi_{i+1}U(2m)$ for $1 \le i \le 2m$, and periodicity $\pi_{i-1}U(m) \cong \pi_{i+1}U(m)$ for $1 \le i \le 2m - 2$ (groups for $i \ge 2$). — Milnor §23, p. 129
- [ ] **330.** (V14.29) `[restated]` Theorem 23.5: for $j \le 2m - 1$, $\pi_jU(m)$ is trivial for even $j$ and in bijection with $\mathbb Z$ for odd $j$. — Milnor §23, Theorem 23.5, p. 130
- [ ] **331.** (V14.30) `[restated]` $\pi_1S^1 \cong \mathbb Z$ and $\pi_{2k+1}U(m) \cong \mathbb Z$ for $2k + 2 \le 2m$, as groups. — Milnor §23, Theorem 23.5, p. 130

## Chapter 15 (Milnor §24)

- [ ] **332.** (V15.1) `[stronger]` A complex structure is an orthogonal $J$ with $J^2 = -I$, equivalently a skew $J$ with $J^2 = -I$; it forces $n$ even. — Milnor §24, p. 133
- [ ] **333.** (V15.2) `[narrower]` If $J^2 = -I$ then $\exp(\theta J) = \cos\theta\,I + \sin\theta\,J$, so $\exp(\pi J) = -I$. — Milnor §24, proof of Lemma 24.1, pp. 134–135
- [ ] **334.** (V15.3) `[restated]` For odd positive $a_j$, Milnor's spectrum for $O(2m)$ has index $\sum_{i<j}(a_i + a_j - 2) + \sum_{a_i > a_j}(a_i - a_j - 2)$, which is $0$ when all $a_j = 1$ and at least $2m - 2$ otherwise. — Milnor §24, Lemma 24.2
- [ ] **335.** (V15.4) `[stronger]` $\Omega_k(n)$ is the set of complex structures anticommuting with $J_1, \dots, J_{k-1}$; these sets decrease with $k$ and are compact. — Milnor §24, p. 136
- [ ] **336.** (V15.5) `[narrower]` For $P, J' \in \Omega_k(n)$, the reflection $PJ'^{-1}P = -PJ'P$ lies in $\Omega_k(n)$. — Milnor §24, p. 136
- [ ] **337.** (V15.6) `[stronger]` For skew $A$ anticommuting with $J$, $J\exp A$ is a complex structure, and it anticommutes with every $J_\alpha$ that anticommutes with $J$ and commutes with $A$. — Milnor §24, Assertions 1 and 2, p. 137
- [ ] **338.** (V15.7) `[narrower]` $J' \in \Omega_{k+1}(n)$ iff $J' = J_kA$ with $A$ a complex structure anticommuting with $J_k$ and commuting with $J_1, \dots, J_{k-1}$; then $J_k\exp(tA) = \cos t\,J_k + \sin t\,J'$ stays in $\Omega_k(n)$ and passes through $J'$ at $t = \pi/2$. — Milnor §24, proof of Lemma 24.4 and Remark, pp. 137–138
- [ ] **339.** (V15.8) `[narrower]` $P \oplus P'$ lies in $\Omega_k(n + n')$ for the structures $J_\alpha \oplus J'_\alpha$ whenever $P \in \Omega_k(n)$ and $P' \in \Omega_k(n')$. — Milnor §24, p. 138
- [ ] **340.** (V15.9) `[extra]` Explicit matrices give $1$, $3$, $7$, $8$ anticommuting complex structures on $\mathbb R^2$, $\mathbb R^4$, $\mathbb R^8$, $\mathbb R^{16}$, and $8$ on every $\mathbb R^{16r}$. — Milnor §24, pp. 136, 139
- [ ] **341.** (V15.10) `[stronger]` The products $J_1J_2J_3$, $J_1J_4J_5$, $J_2J_4J_6$, $J_1J_6J_7$, $J_3J_4$, $J_7J_8$ and $J_1\cdots J_7$ have exactly the squares and commutation properties Milnor uses on pp. 139–143. — Milnor §24, pp. 139–143
- [ ] **342.** (V15.11) `[narrower]` $J' \mapsto J_aJ_bJ'$ is a bijection of $\Omega_{k+1}(n)$ onto the symmetric involutions commuting with $J_a, J_b$ and anticommuting with the other $J_c$, $c \le k$. — Milnor §24, Lemma 24.6 (3), (5), (6), (7), pp. 139–141
- [ ] **343.** (V15.12) `[stronger]` With eight structures, $V_1 \supset W \supset X \supset X_1$ halve the dimension at each step, and in $\mathbb R^{16r}$ they have dimensions $8r$, $4r$, $2r$, $r$. — Milnor §24, pp. 139–141
- [ ] **344.** (V15.13) `[restated]` A minimal space is a non-zero space with no proper non-zero subspace closed under $J_1, \dots, J_k$; $m_k$ is Milnor's table. — Milnor §24, p. 143
- [ ] **345.** (V15.14) `[narrower]` For $k \le 8$, $m_k$ divides the dimension of every space with $k$ Clifford maps, and is the least positive dimension carrying $k$ anticommuting complex structures. — Milnor §24, p. 143
- [ ] **346.** (V15.15) `[extra]` $k$ Clifford maps make a space a module over the Clifford algebra $C_k$ of dimension $2^k$, so a minimal space has dimension at most $2^k$. — Milnor §24, footnote, p. 136
- [ ] **347.** (V15.16) `[narrower]` For $k \le 8$ a space with $k$ Clifford maps is minimal iff its dimension is $m_k$. — Milnor §24, p. 143
- [ ] **348.** (V15.17) `[narrower]` For $k \le 8$, $k \not\equiv 3 \pmod 4$, any two minimal spaces are isomorphic by a linear isomorphism commuting with the $J_\alpha$. — Milnor §24, Lemma 24.8
- [ ] **349.** (V15.18) `[narrower]` For anticommuting complex structures, $J_1u, \dots, J_ku$ are orthonormal and orthogonal to a unit vector $u$. — Milnor §24, Remark, pp. 143–144
- [ ] **350.** (V15.19) `[restated]` Eigenvalues greater than $\pi^2$ each contribute at least one to the index; so $s - 1$ such eigenvalues give index at least $s - 1$. — Milnor §24, Assertions, pp. 145–146
- [ ] **351.** (V15.20) `[sign]` For odd $a_h$ with some $|a_h| \ge 3$ and sum $c$, the pairs $a_h > a_j$ alone give $4\lambda \ge r - |c|$. — Milnor §24, pp. 147–148
- [ ] **352.** (V15.21) `[restated]` If $x\exp A \in N$ and $A \in T_{x\exp A}$ for $A \in T_x$, with $\dim T_x = \dim N$, then the geodesics of $N$ are exactly the curves $t \mapsto x\exp(tA)$, $A \in T_x$, and $N$ is complete. — Milnor §24, footnote, p. 136; p. 137
- [ ] **353.** (V15.22) `[explicit]` Assertions 1 and 2: for $x \in \Omega_k(n)$ and $A \in \mathcal T_x$, $x\exp A \in \Omega_k(n)$; conversely, if $C$ is small and $x\exp C \in \Omega_k(n)$, then $C \in \mathcal T_x$. — Milnor §24, Assertions 1 and 2, p. 137
- [ ] **354.** (V15.23) `[restated]` The set of points of $\Omega_k(n)$ where $\mathcal T$ has a given dimension is open and closed in $\Omega_k(n)$, compact, a submanifold of $M_n(\mathbb R)$ with tangent spaces $x\mathcal T_x$, and its geodesics are the curves $x\exp(tA)$, $A \in \mathcal T_x$. — Milnor §24, Lemma 24.4
- [ ] **355.** (V15.24) `[restated]` A skew $V$ with $\exp V = -I$ has $\|V\|^2 \ge \pi^2n$, with equality only if $V^2 = -\pi^2I$. — Milnor §24, proof of Lemma 24.1, p. 134
- [ ] **356.** (V15.25) `[restated]` If some $A \in \mathcal T_p$ has $A^2 = -I$, the distance from $p$ to $-p$ in the stratum of $p$ is $\pi\sqrt n$, and the paths of least energy are, on $[0, 1]$, exactly the curves $p\exp(\pi tA)$ with $A \in \mathcal T_p$, $A^2 = -I$. — Milnor §24, proof of Lemma 24.4, pp. 137–138
- [ ] **357.** (V15.26) `[restated]` These $A$, for $p = J_k$, correspond homeomorphically to the points $J' = J_kA$ of $\Omega_{k+1}(n)$, the geodesic of $J'$ being $\cos(\pi t)J_k + \sin(\pi t)J'$; and $\Omega_{k+1}(n)$ is homotopy equivalent to the space of minimal paths from $J_k$ to $-J_k$ (homeomorphic after identifying paths that agree on $[0, 1]$). — Milnor §24, Lemma 24.1, p. 133; Lemma 24.4, p. 136
- [ ] **358.** (V15.27) `[extra]` The minimal paths from $p$ to $-p$ form a retract of an open neighbourhood in the path space. — Milnor §24, pp. 135–136
- [ ] **359.** (V15.28) `[restated]` For skew $X$ commuting with $p$ and $J_1, \dots, J_{k-1}$, $X\gamma - \gamma X$ is a Jacobi field along $\gamma(t) = p\exp(tV)$; spaces of such $X$ commuting with $\exp(\tau V)$ but not with $V$ bound the multiplicity of $\gamma(\tau)$, and so the index, from below. — Milnor §24, pp. 144, 146
- [ ] **360.** (V15.29) `[restated]` $\mathbb R^n$ splits orthogonally into subspaces minimal under $A, J, J_1, \dots, J_{k-1}$; on each, $A^2$ is a scalar $-c$, with $c \ge 1$ if $\exp(\pi A) = -I$; each is a minimal space for $k + 1$ structures; and for $k \le 7$, $k \not\equiv 2 \pmod 4$, any two are related by an isomorphism as in Milnor's p. 145. — Milnor §24, pp. 144–145
- [ ] **361.** (V15.30) `[narrower]` For $k \le 7$, $k \not\equiv 2 \pmod 4$, a geodesic from $J_k$ to $-J_k$ in $\Omega_k(n)$ that is not of least energy has index $\ge n/m_{k+1} - 1$, and $\ge n - 2$ in $O(n)$ ($k = 0$). — Milnor §24, Lemma 24.2, p. 135; Assertion, p. 146
- [ ] **362.** (V15.31) `[restated]` For $k \le 7$, $k \not\equiv 2 \pmod 4$ and $i \le n/m_{k+1} - 3$, the map $J' \mapsto (\cos(\pi t)J_k + \sin(\pi t)J')$ is bijective on $\pi_i$ at every point, and $\pi_i\Omega_{k+1}(n) \cong \pi_{i+1}\Omega_k(n)$. — Milnor §24, p. 146; Theorem 24.5, p. 138
- [ ] **363.** (V15.32) `[restated]` Theorem 24.3: for $i \le n - 4$, $\Omega_1(n) \to \Omega(O(n); I, -I)$ is bijective on $\pi_i$, and $\pi_i\Omega_1(n) \cong \pi_{i+1}O(n)$. — Milnor §24, Theorem 24.3
- [ ] **364.** (V15.33) `[extra]` For a continuous $F$ of modulus $1$, the set of paths along which the angle of $F$ ends at a given value is open and closed in the path space. — Milnor §24, pp. 147–148
- [ ] **365.** (V15.34) `[restated]` $\det_{\mathbb C}$, defined without a complex basis, is multiplicative, has modulus $1$ on orthogonal matrices commuting with $\mathbf i$, and $\det_{\mathbb C}\exp(tV) = e^{-\sqrt{-1}\,t\operatorname{tr}(V\mathbf i)/2}$. — Milnor §24, pp. 146–147
- [ ] **366.** (V15.35) `[restated]` $\mathbf i = J_1\cdots J_{k-1}$ has the properties Milnor uses for $k = 2, 6$; $f = \det_{\mathbb C}(J_k^{\mathsf T}\,\cdot\,)$ has modulus $1$ on $\Omega_k(n)$; and $\Omega^{(c)}$, the paths whose $f$-angle ends at $\pi m_{k+1}c/2$, is open and closed and contains the geodesic $J_k\exp(\pi tA)$ exactly when $-\operatorname{tr}(A\mathbf i) = m_{k+1}c$. — Milnor §24, pp. 146–148
- [ ] **367.** (V15.36) `[extra]` For $k = 2, 6$ every path from $J_k$ to $-J_k$ lies in exactly one $\Omega^{(c)}$, $c$ an integer. — Milnor §24, p. 148
- [ ] **368.** (V15.37) `[restated]` For $k \equiv 2 \pmod 4$, on each minimal piece $A = a_h\mathbf i$ with $a_h$ an odd integer, and $\operatorname{tr}(A\mathbf i) = -m_{k+1}\sum a_h$. — Milnor §24, p. 147
- [ ] **369.** (V15.38) `[sign]` For $k = 2, 6$, a geodesic in $\Omega^{(c)}$ that is not of least energy has index $\ge \lfloor(n/m_{k+1} - |c|)/4\rfloor$. — Milnor §24, pp. 147–148
- [ ] **370.** (V15.39) `[restated]` For $k = 2, 6$ and $j + 3 \le \lfloor(n/m_{k+1} - |c|)/4\rfloor$, at a point $J'$ whose semicircle lies in $\Omega^{(c)}$, the map of item 31 is bijective on $\pi_{j+1}$, and $\pi_{j+1}\Omega_{k+1}(n) \cong \pi_{j+2}\Omega_k(n)$. — Milnor §24, p. 148
- [ ] **371.** (V15.40) `[narrower]` For $k = 2, 6$ and $|c| \le n/m_{k+1} - 8$, the path components of $\Omega^{(c)}$ correspond bijectively to those of the part of $\Omega_{k+1}(n)$ mapped into it. — Milnor §24, pp. 146, 148
- [ ] **372.** (V15.41) `[narrower]` On $\mathbb R^{16r}$ with the explicit structures, $J \mapsto J \oplus J'_k$ maps $\Omega_k(16r)$ into $\Omega_k(16r + 16)$ compatibly with the maps of item 31, and for $k = 2, 6$ without changing $c$. — Milnor §24, pp. 138–139
- [ ] **373.** (V15.42) `[restated]` $\Omega_8(16r)$ is homeomorphic to $O(r)$, the base point $J_8$ corresponding to $I$. — Milnor §24, Lemma 24.6 (8), pp. 141–142
- [ ] **374.** (V15.43) `[restated]` For $r \ge 2i + 7$: $\pi_i\Omega_8(16r) \cong \pi_{i+8}O(16r)$ and $\pi_iO(r) \cong \pi_{i+8}O(16r)$, as sets. — Milnor §24, Theorem 24.5, p. 138; p. 142
- [ ] **375.** (V15.44) `[extra]` $\pi_iO(n)$ does not depend on $n \ge i + 2$, and $\pi_iU(n)$ does not depend on $n > i/2$, up to bijection. — Milnor §23, proof of Lemma 23.4, pp. 128–129
- [ ] **376.** (V15.45) `[narrower]` Theorem 24.7 in the stable range: $\pi_iO(n) \cong \pi_{i+8}O(n')$, as sets, for $n \ge i + 2$ and $n' \ge i + 10$. — Milnor §24, Theorem 24.7
- [ ] **377.** (V15.46) `[restated]` $\pi_iU(n) \cong \pi_{i+2}U(n')$, as sets, for $i < 2n$ and $i + 2 < 2n'$. — Milnor §23, Periodicity Theorem, p. 129

## Appendix (Milnor pp. 149–153)

- [ ] **378.** (VA.1) A homotopy equivalence is a map with a two-sided homotopy inverse; a map with a left and a right homotopy inverse is one.
- [ ] **379.** (VA.2) `[explicit]` The telescope is $X_\Sigma = \bigcup_nX_n \times [n, n + 1] \subseteq X \times \mathbb R$, and $X$ is the homotopy direct limit of $\{X_i\}$ when $(x, \tau) \mapsto x$ is a homotopy equivalence; raising $\tau$ stays in $X_\Sigma$. — Milnor Appendix, p. 149
- [ ] **380.** (VA.3) `[extra]` If the $X_n$ are closed, a map on $X_\Sigma$ (or $P \times X_\Sigma$) continuous on each strip is continuous. — Milnor Appendix, pp. 151–153
- [ ] **381.** (VA.4) `[same]` If $f_\Sigma$ is a homotopy equivalence between homotopy direct limits, so is $f$. — Milnor Appendix, proof of Theorem A, p. 150
- [ ] **382.** (VA.5) `[restated]` $X_n \to X^n_\Sigma$, $x \mapsto (x, n)$, is a homotopy equivalence, with no closedness. — Milnor Appendix, p. 152
- [ ] **383.** (VA.6) `[explicit]` A function $f \ge 0$ with $f \ge n + 1$ off $X_n$ makes $X$ a homotopy direct limit, and $X_\Sigma$ is always the homotopy direct limit of its truncations. — Milnor Appendix, Example 1, p. 149
- [ ] **384.** (VA.7) `[stronger]` Example 1 holds for paracompact Hausdorff $X$; sublevel sets $\{E \le a_i\}$ of a continuous $E$ with $a_i \to \infty$ need no paracompactness. — Milnor Appendix, Example 1
- [ ] **385.** (VA.8) `[same]` Example 3: $[0, 1]$ is not the homotopy direct limit of $\{0\} \cup [\frac1{n+1}, 1]$. — Milnor Appendix, Example 3
- [ ] **386.** (VA.9) `[explicit]` For closed $X_n$, Milnor's maps $h_1$ are homotopy equivalences with inverse $g$. — Milnor Appendix, Case 1, pp. 151–152
- [ ] **387.** (VA.10) `[sign]` Case 1: for closed $X_n$ and $\varphi_n \simeq \mathrm{id}$, $\varphi_\Sigma$ is a homotopy equivalence; the third line of $h_u$ is $h^{n+1}_{(4t-3)u}$. — Milnor Appendix, Case 1, pp. 150–152
- [ ] **388.** (VA.11) `[narrower]` Case 2: if the $Y_n$ are closed and every $f_n$ is a homotopy equivalence, $f_\Sigma$ is a homotopy equivalence; the $X_n$ need not be closed. — Milnor Appendix, Case 2, pp. 152–153
- [ ] **389.** (VA.12) `[narrower]` Theorem A by Milnor's proof, with the $Y_i$ closed. — Milnor Appendix, Theorem A
- [ ] **390.** (VA.13) `[extra]` The mapping telescope of $K_0 \to K_1 \to \cdots$ is the homotopy direct limit of its closed truncations, each homotopy equivalent to the corresponding $K_n$. — Milnor Appendix, pp. 149–153
- [ ] **391.** (VA.14) The mapping telescope of the inclusions $X_n \subseteq X_{n+1}$ is homotopy equivalent to $X_\Sigma$, and to $X$ when $X$ is the homotopy direct limit.
- [ ] **392.** (VA.15) `[same]` Theorem A holds exactly as Milnor states it, with no closedness hypothesis. — Milnor Appendix, Theorem A
- [ ] **393.** (VA.16) `[restated]` A homotopy direct limit of the $X_n$ is homotopy equivalent to the mapping telescope of any sequence $K_n$ with compatible homotopy equivalences $X_n \to K_n$. — Milnor Appendix, p. 150
- [ ] **394.** (VA.17) `[narrower]` The Corollary, with the mapping telescope of the $K_n$ in place of a CW-complex. — Milnor Appendix, Corollary, p. 153
- [ ] **395.** (VA.18) `[narrower]` A countable cell complex is the mapping telescope of a tower of cell attachments. — Milnor Appendix, pp. 149–150
- [ ] **396.** (VA.19) `[stronger]` A space exhausted by sublevel sets homotopy equivalent to the compatible stages of a cell tower has the homotopy type of the countable cell complex. — Milnor Appendix, p. 150
