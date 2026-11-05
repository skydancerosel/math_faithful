## Part VI. Geodesics and completeness (Milnor §10)

Milnor's §10 (pp. 55–66) turns a Riemannian manifold into a metric space whose shortest paths are geodesics: geodesics solve a differential equation (Theorem 10.1, Lemma 10.2), are collected into the exponential map, a diffeomorphism near the origin of each tangent space uniformly in the base point (Lemma 10.3), are locally shortest (Theorem 10.4, from Lemmas 10.5 and 10.6), and shortest paths are geodesics (Corollary 10.7); the infimum of lengths is a distance $\rho$ (Corollary 10.8), and geodesic and metric completeness agree (Theorem 10.9, Corollary 10.10 and its converse). This part retells the formal proof of every numbered statement from Theorem 10.1 to Corollary 10.10, of the converse of Corollary 10.10, of the four-way Hopf–Rinow equivalence, and of the completeness of closed submanifolds, among them the round sphere.

The setting is that of Part V. $V$ is a finite-dimensional real inner product space (Milnor's $\mathbb R^K$) and $N \subseteq V$ a slice submanifold modelled on a finite-dimensional $Z$, with finite-dimensional complement $W$ (§0.1, §0.3), with the induced metric. $N$ need not be closed, compact or connected; connectedness is assumed exactly where it is used. Every Riemannian manifold is isometric to such an $N$ by Nash's embedding theorem, which is neither in Mathlib nor proved here, so what follows are theorems about embedded manifolds. Two of Milnor's silent hypotheses disappear: $N$ is Hausdorff, which uniqueness of geodesics and the closedness of normal balls need, and its topology is metric from the start.

The formal route differs from Milnor's in these places, each explained where it occurs. A geodesic is a curve whose acceleration in $V$ is normal to $N$, and no Christoffel symbols are defined. Theorem 10.1 is proved, not quoted, with a cut-off and the flow library of Part I. Existence of geodesics is solved in a slice chart, uniqueness in $V \times V$ and on whole intervals. $\exp$ is defined through geodesics on open intervals containing $[0, 1]$. Lemma 10.3 uses the inverse function theorem. The Gauss lemma is proved for every direction, and Lemma 10.6 follows from it by Cauchy–Schwarz. Theorem 10.4 is proved for a class of paths closed under restriction, with a sharp equality case that Corollary 10.7 needs. $\rho$ takes values in $[0, \infty]$ and its continuity is proved; the continuity of $\exp$ on its whole domain is proved by continuing geodesics; Theorem 10.9 needs completeness at one point only.

**Map.**

- `Chapter7/ODE`: Theorem 10.1, existence with smooth dependence and uniqueness on intervals.
- `Chapter7/Geodesic`: geodesics, the geodesic equation, the spray, constant speed, homogeneity, uniqueness.
- `Chapter7/GeodesicLocal`: the pseudo-inverse, the geodesic equation in a chart, Lemma 10.2.
- `Chapter7/Exp`: the exponential map, smoothness near the zero section, $d(\exp_q)_0 = \mathrm{id}$.
- `Chapter7/NormalNbhd`: normal radii, $\exp$ read in a chart, Milnor's Jacobian, Lemma 10.3, $\exp_q$ as a partial diffeomorphism.
- `Chapter7/GaussLemma`: the Gauss lemma and the pointwise form of Lemma 10.6.
- `Chapter7/Path`: piecewise smooth and admissible paths, their lengths.
- `Chapter7/Shortest`: Lemma 10.6, paths leaving a normal ball, Theorem 10.4 with its sharp equality case.
- `Chapter7/Minimal`: Corollary 10.7.
- `Chapter7/Distance`: the distance $\rho$, its axioms, normal balls as metric balls, Corollary 10.8.
- `Chapter7/Metric`: continuity and finiteness of $\rho$, the metric space $(N, \rho)$, metric completeness.
- `Chapter7/GeodesicFlow`: the geodesic flow, continuation of geodesics, continuity of $\exp$, geodesic completeness, the converse of Corollary 10.10.
- `Chapter7/HopfRinow`: minimal geodesics, Theorem 10.9, Corollary 10.10, the Hopf–Rinow equivalence, closed submanifolds and the sphere.

The labels V7.1–V7.30 are those of the verified edition.

### VI.1 The setting: charts, tangent spaces, the projection and the second fundamental form

Recalled from §0.3 and Part V (§V.10–§V.14, §V.17), for use throughout.

**Charts and parametrizations.** A slice chart of $N$ is a partial diffeomorphism $\sigma$ from an open subset of $V$ onto an open subset of $Z \times W$ which, on its domain, carries $N$ exactly onto $Z \times \{0\}$ ⟦Milnor/Chapter2/Submanifold · SliceChart⟧; $N$ is a slice submanifold if every point of $N$ lies in the domain of one ⟦Milnor/Chapter2/Submanifold · IsSliceSubmanifold⟧. For each $q \in N$ one such chart is chosen once and for all; call it $\sigma_q$ ⟦Chapter6/Projection · sliceAt⟧ ⟦Chapter6/Projection · mem_sliceAt_source⟧. A slice chart has a parametrization $x(u) = \sigma^{-1}(u, 0)$ ⟦Chapter1/ManifoldSubmanifold · sliceParam⟧, meaningful on the open set $T_\sigma = \{u \in Z : (u, 0) \text{ is in the image of } \sigma\}$ ⟦Chapter1/ManifoldSubmanifold · isOpen_toChart_target⟧. It is smooth there ⟦Chapter1/ManifoldSubmanifold · contDiffOn_sliceParam⟧, takes values in $N$ ⟦Chapter1/ManifoldSubmanifold · sliceParam_mem⟧, satisfies $x((\sigma q)_1) = q$ for $q \in N$ in the domain of $\sigma$ ⟦Chapter1/ManifoldSubmanifold · sliceParam_toChart⟧, and has injective derivative, as one sees by differentiating $\sigma(x(u)) = (u, 0)$ ⟦Chapter6/Projection · injective_fderiv_sliceParam⟧. Here and below $(a, b)_1 = a$ and $(a, b)_2 = b$.

**Tangent spaces.** $T_qN \subseteq V$ is the range of the derivative at $q$ of the inclusion $N \to V$ ⟦Chapter1/ManifoldSubmanifold · tangentSubspace⟧. For any slice chart $\sigma$ around $q$ it is the range of $dx$ at $(\sigma q)_1$ ⟦Chapter1/ManifoldSubmanifold · tangentSubspace_eq_range_fderiv_sliceParam⟧ and the kernel of $v \mapsto (d\sigma_q v)_2$ ⟦Milnor/Chapter8/TangentBundle · sliceChart_mem_tangentSpace_iff⟧. Formally $T_qN$ is indexed by a point of $N$ (a point with a proof of membership), and equal points have equal tangent spaces ⟦Chapter7/Geodesic · tangentSubspace_congr⟧.

**The tangent projection.** $P_q$ is the orthogonal projection of $V$ onto $T_qN$ ⟦Chapter6/Projection · tanProj⟧. In a chart it is a formula. For an injective linear map $A$ into $V$, the operator $A(A^{\mathsf T}A)^{-1}A^{\mathsf T}$ ⟦Chapter6/Projection · gramProj⟧ is the orthogonal projection onto the range of $A$ ⟦Chapter6/Projection · gramProj_eq_starProjection⟧ and depends smoothly on $A$ ⟦Chapter6/Projection · contDiffAt_gramProj⟧. Taking $A = dx$ at $(\sigma y)_1$ defines an operator $Q_\sigma(y)$ for every $y$ in the domain of $\sigma$ ⟦Chapter6/Projection · projRep⟧. It equals $P_y$ for $y \in N$ ⟦Chapter6/Projection · projRep_eq⟧ and is smooth near every point of $N$ in the domain ⟦Chapter6/Projection · contDiffAt_projRep⟧. So $Q_\sigma$ extends $q \mapsto P_q$ smoothly to an open set of $V$ (used in §VI.4).

**The second fundamental form.** For $v \in T_qN$ let $D_v$ be the derivative of $q \mapsto P_q$ along $N$ in the direction $v$ ⟦Chapter6/Projection · dN⟧; it is the ambient derivative of any smooth extension, $D_v = dQ_\sigma(v)$ at $q$ ⟦Chapter6/Projection · dN_tanProj_eq_fderiv⟧. The second fundamental form is $\mathrm{II}_q(v, w) = D_v w$ ⟦Chapter6/Submanifold · secondFundForm⟧, and for tangent $v, w$ it is normal to $N$ ⟦Chapter6/Submanifold · secondFundForm_mem_orthogonal⟧. The covariant derivative of a field $X$ along a curve $c$ in $N$ is $\frac{D}{dt}X = P_{c(t)}X'(t)$ ⟦Chapter6/Parallel · covDeriv⟧, and the velocity of $c$ is $c'$ ⟦Chapter6/Parallel · velocity⟧ (Part V).

**The tangent bundle.** $TN = \{(q, v) \in V \times V : q \in N,\ v \in T_qN\}$ ⟦Milnor/Chapter8/TangentBundle · tangentBundleSet⟧ is a slice submanifold of $V \times V$ modelled on $Z \times Z$ ⟦Milnor/Chapter8/TangentBundle · isSliceSubmanifold_tangentBundle⟧ (Problem 10 of the companion volume). It is Milnor's tangent manifold (p. 58).

**Three small lemmas.**

- *Velocities are tangent.* If $c : \mathbb R \to V$ lies in $N$ near $t$ and is differentiable at $t$, then $c'(t) \in T_{c(t)}N$ ⟦Chapter7/Geodesic · hasDerivAt_mem_tangentSubspace⟧. *Proof.* Let $\sigma = \sigma_{c(t)}$. For $s$ near $t$, $c(s)$ lies in $N$ and in the domain of $\sigma$, so the $W$-component of $\sigma(c(s))$ vanishes identically near $t$. Its derivative at $t$, which is $(d\sigma\, c'(t))_2$ by the chain rule, is therefore $0$, and the kernel description of $T_{c(t)}N$ applies.
- *The projection along a curve.* Under the same hypotheses, with $\sigma = \sigma_{c(t)}$, the operator-valued curve $s \mapsto Q_\sigma(c(s))$ has derivative $D_{c'(t)}$ at $t$ ⟦Chapter7/Geodesic · hasDerivAt_projRep_comp⟧: this is the chain rule for the smooth $Q_\sigma$, together with $dQ_\sigma(v) = D_v$ for tangent $v$.
- *Curves in a subspace.* A curve that stays near $t$ in a linear subspace $K$ of $V$ and is differentiable at $t$ has its derivative in $K$ ⟦Chapter7/GaussLemma · hasDerivAt_mem_of_eventually_mem⟧: the projection onto $K$ fixes the curve near $t$, hence fixes its derivative.

### VI.2 Geodesics, the geodesic equation, constant speed and homogeneity

**Definition (V7.1; §0.9).** Let $s \subseteq \mathbb R$ be open, in practice an open interval. A curve $\gamma : \mathbb R \to V$ is a *geodesic on $s$* if $\gamma$ is $C^\infty$ on $s$, $\gamma(t) \in N$ for every $t \in s$, and the acceleration $\gamma''(t)$ is orthogonal to $T_{\gamma(t)}N$ for every $t \in s$ ⟦Chapter7/Geodesic · IsGeodesicOn⟧.

Curves are maps on all of $\mathbb R$, but only their values on $s$ matter: a curve that agrees on the open set $s$ with a geodesic is one ⟦Chapter7/Geodesic · IsGeodesicOn.congr⟧. A geodesic on $s$ is a geodesic on every open subset of $s$ ⟦Chapter7/Geodesic · IsGeodesicOn.mono⟧, constant curves at points of $N$ are geodesics ⟦Chapter7/Geodesic · isGeodesicOn_const⟧, and being a geodesic is a local property: if every $t \in s$ has an open neighbourhood $s' \subseteq s$ on which $\gamma$ is a geodesic, then $\gamma$ is a geodesic on $s$ ⟦Chapter7/Minimal · isGeodesicOn_of_locally⟧, because smoothness on an open set is local ⟦Mathlib/Analysis/Calculus/ContDiff/Defs · contDiffOn_of_locally_contDiffOn⟧ and the other two conditions are pointwise. Milnor allows any interval; a geodesic on a closed interval is represented by one on an open interval containing it (§VI.6).

The velocity of a geodesic is tangent, $\gamma'(t) \in T_{\gamma(t)}N$ ⟦Chapter7/Geodesic · IsGeodesicOn.deriv_mem⟧ (the first small lemma of §VI.1), and the normality of $\gamma''$ says exactly that $P_{\gamma(t)}\gamma''(t) = 0$ ⟦Chapter7/Geodesic · IsGeodesicOn.tanProj_deriv_deriv⟧ ⟦Chapter6/Projection · tanProj_eq_zero_iff⟧. As $\frac{D}{dt} = P \circ \frac{d}{dt}$, this is Milnor's definition: a smooth curve $c : \mathbb R \to N$ is a geodesic on $\mathbb R$ if and only if $\frac{D}{dt}\frac{dc}{dt} = 0$ at every time ⟦Chapter7/Geodesic · isGeodesicOn_univ_iff_covDeriv⟧.

**Proposition (the geodesic equation, V7.3).** Let $\gamma$ be $C^\infty$ on the open set $s$ with $\gamma(s) \subseteq N$. Then $\gamma$ is a geodesic on $s$ if and only if
$$\gamma''(t) = \mathrm{II}_{\gamma(t)}\big(\gamma'(t), \gamma'(t)\big) \qquad (t \in s)$$
⟦Chapter7/Geodesic · IsGeodesicOn.deriv_deriv_eq⟧ ⟦Chapter7/Geodesic · isGeodesicOn_of_deriv_deriv_eq⟧.

*Proof.* Let $\gamma$ be a geodesic, $t \in s$, $q = \gamma(t)$, $\sigma = \sigma_q$ and $Q = Q_\sigma$. For $\tau$ near $t$, $\gamma(\tau)$ is in $N$ and in the domain of $\sigma$, so $Q(\gamma(\tau)) = P_{\gamma(\tau)}$, and $\gamma'(\tau)$ is tangent; hence
$$Q(\gamma(\tau))\,\gamma'(\tau) = \gamma'(\tau) \qquad \text{for } \tau \text{ near } t$$
⟦Chapter6/Projection · projRep_eq⟧ ⟦Chapter6/Projection · tanProj_eq_self⟧. Differentiate at $t$ with the product rule. The derivative of $\tau \mapsto Q(\gamma(\tau))$ is $D_{\gamma'(t)}$ (§VI.1), so the left side has derivative $D_{\gamma'(t)}\gamma'(t) + P_q\gamma''(t) = \mathrm{II}_q(\gamma'(t), \gamma'(t)) + P_q\gamma''(t)$, and the right side has derivative $\gamma''(t)$. By uniqueness of derivatives these agree, and $P_q\gamma''(t) = 0$. Conversely, if $\gamma'' = \mathrm{II}(\gamma', \gamma')$, then $\gamma'(t)$ is tangent (the curve lies in $N$ near $t$), and $\mathrm{II}$ of two tangent vectors is normal, so $\gamma''(t)$ is normal. $\square$

**The geodesic spray.** The vector field
$$(x, v) \longmapsto \big(v, \mathrm{II}_x(v, v)\big) \quad (x \in N), \qquad (x, v) \longmapsto (v, 0) \quad (x \notin N)$$
on $V \times V$ ⟦Chapter7/Geodesic · geodesicSpray⟧ is the geodesic spray; its values off $N$ are a placeholder and never used. The lift $t \mapsto (\gamma(t), \gamma'(t))$ of a geodesic lies in $TN$ ⟦Chapter7/Geodesic · IsGeodesicOn.mem_tangentBundleSet⟧, and a smooth curve $\gamma$ in $N$ on an open set $s$ is a geodesic if and only if its lift is an integral curve of the spray on $s$ ⟦Chapter7/Geodesic · isGeodesicOn_iff_hasDerivAt_geodesicSpray⟧. This is Milnor's first-order system (p. 56), and the proof is the geodesic equation read in both directions. As the spray involves the derivative of $P$, which exists only along $N$, the equations actually solved are a smooth extension of it to an open set of $V \times V$ (§VI.4) and its expression in a chart (§VI.5).

**Proposition (constant speed, V7.2).** If $\gamma$ is a geodesic on $s$, then $\frac{d}{dt}\|\gamma'(t)\|^2 = 0$ for $t \in s$ ⟦Chapter7/Geodesic · IsGeodesicOn.hasDerivAt_norm_sq⟧. If $s$ is preconnected (an open interval), the speed $\|\gamma'\|$ is constant on $s$ ⟦Chapter7/Geodesic · IsGeodesicOn.norm_deriv_eq⟧.

*Proof.* $\frac{d}{dt}\|\gamma'\|^2 = 2\langle\gamma'', \gamma'\rangle$, and $\gamma''$ is normal while $\gamma'$ is tangent. A function with zero derivative on an open preconnected subset of $\mathbb R$ is constant there ⟦Mathlib/Analysis/Calculus/MeanValue · IsOpen.is_const_of_deriv_eq_zero⟧; apply it to $\|\gamma'\|^2$ and take square roots. $\square$

This is Milnor's computation (p. 55). The length of a geodesic on $[a, b] \subseteq s$ is then its speed times $b - a$ (§VI.10).

**Proposition (homogeneity, V7.2).** If $\gamma$ is a geodesic on $s$, then for all real $a, b$ the curve $t \mapsto \gamma(at + b)$ is a geodesic on $\{t : at + b \in s\}$ ⟦Chapter7/Geodesic · IsGeodesicOn.comp_mul_add⟧.

*Proof.* The preimage of an open set under a continuous map is open, and smoothness and membership in $N$ are inherited. By the chain rule the velocity at $t$ is $a\gamma'(at + b)$, and near any $t$ of the preimage this holds identically, so the acceleration is $a^2\gamma''(at + b)$, a multiple of a normal vector. $\square$

Milnor states the case $b = 0$ (p. 57); shifts ($a = 1$) and reversals ($a = -1$) are used below.

### VI.3 Theorem 10.1: Milnor's facts about ordinary differential equations

Milnor's Theorem 10.1 (p. 56) gives, for $u'' = F(u, u')$ with $F$ smooth near $(u_1, v_1) \in \mathbb R^{2n}$, unique solutions for a uniform time, depending smoothly on the initial data; he passes to the system $u' = v$, $v' = F(u, v)$ and quotes Graves. The formal proof has four steps: a connectedness principle, local uniqueness by Grönwall's inequality, local existence with smooth dependence by a cut-off and the global flow of Part I (§I.18–§I.21), and the reduction to first order.

**Lemma (a connectedness principle).** Let $s \subseteq \mathbb R$ be open and preconnected, $F$ a Hausdorff space, and $f, g : \mathbb R \to F$ continuous on $s$. Suppose $f(t_0) = g(t_0)$ for some $t_0 \in s$, and that whenever $f$ and $g$ agree at a point of $s$ they agree near it. Then $f = g$ on $s$ ⟦Chapter7/ODE · eqOn_of_eventuallyEq⟧.

*Proof.* The set $u$ of times near which $f$ and $g$ agree is open ⟦Mathlib/Topology/Neighborhoods · isOpen_setOfPred_eventually_nhds⟧ and contains $t_0$. If $t \in s$ lies in the closure of $u$, then $f$ and $g$ agree at points arbitrarily close to $t$; both are continuous at $t$ and limits in a Hausdorff space are unique, so $f(t) = g(t)$, and by hypothesis $t \in u$. An open set that meets $s$ and contains every point of $s$ in its closure contains the preconnected set $s$ ⟦Mathlib/Topology/Connected/Basic · IsPreconnected.subset_of_closure_inter_subset⟧. $\square$

**Lemma (local uniqueness).** Let $E$ be a real normed space and $G : E \to E$ of class $C^1$ at $f(t_0)$. If $f$ and $g$ solve $x' = G(x)$ near $t_0$ and $f(t_0) = g(t_0)$, then $f = g$ near $t_0$ ⟦Chapter7/ODE · ode_eventuallyEq⟧.

*Proof.* A $C^1$ map is Lipschitz, with some constant $K$, on a neighbourhood $S$ of the point ⟦Mathlib/Analysis/Calculus/ContDiff/RCLike · ContDiffAt.exists_lipschitzOnWith⟧. Both solutions are continuous at $t_0$ with the common value $f(t_0) \in S$, so for some $\varepsilon > 0$ both solve the equation and stay in $S$ on $(t_0 - \varepsilon, t_0 + \varepsilon)$. Grönwall's inequality, in Mathlib's form for a field that is $K$-Lipschitz on the sets where the solutions live, gives $f = g$ on that interval ⟦Mathlib/Analysis/ODE/ExistUnique · ODE_solution_unique_of_mem_Ioo⟧. $\square$

**Lemma (uniqueness on an interval).** Let $G$ be $C^1$ on an open set $U \subseteq E$ and $s \subseteq \mathbb R$ open and preconnected. Two solutions of $x' = G(x)$ on $s$ with values in $U$ that agree at one time of $s$ agree on $s$ ⟦Chapter7/ODE · ode_eqOn⟧.

*Proof.* Solutions are continuous; where they agree, local uniqueness applies (at a point of $U$, where $G$ is $C^1$); the connectedness principle spreads the agreement over $s$. $\square$

**Proposition (local existence with smooth dependence).** Let $E$ be finite-dimensional, $U \subseteq E$ open, $G$ smooth on $U$ and $x_1 \in U$. There are a smooth map $\varphi : \mathbb R \times E \to E$ and numbers $r, \tau > 0$ such that for every $x$ with $\|x - x_1\| < r$: $\varphi(0, x) = x$, and for $|t| < \tau$, $\varphi(t, x) \in U$ and $\frac{\partial}{\partial t}\varphi(t, x) = G(\varphi(t, x))$ ⟦Chapter7/ODE · exists_localFlow⟧.

*Proof.*

1. *Cut-off.* Choose $\rho > 0$ with the ball $B(x_1, \rho) \subseteq U$ and put $R = \rho/3$. Mathlib's smooth bump function $\chi$ with inner radius $R$ and outer radius $2R$ about $x_1$ ⟦Mathlib/Analysis/Calculus/BumpFunction/Basic · ContDiffBump⟧ equals $1$ on the closed ball $\bar B(x_1, R)$ and has support in $\bar B(x_1, 2R) \subseteq U$.
2. *A global field.* $X = \chi\,G$ is smooth on all of $E$: at points of $U$ it is a product of smooth maps, and a point outside $U$ lies outside the closed support of $\chi$, near which $X$ vanishes identically. $X$ has compact support, so it is bounded, say by $M \ge 0$, and globally Lipschitz ⟦Flow/Global · IsBddLipschitz.of_contDiff⟧.
3. *Its flow.* By the flow library (Part I, §I.18–§I.21), $X$ has a global flow $\varphi = \varphi^X$ ⟦Flow/Global · flow⟧ with $\varphi(0, x) = x$ ⟦Flow/Global · IsBddLipschitz.flow_zero⟧ whose flow lines are integral curves ⟦Flow/Global · IsBddLipschitz.hasDerivAt_flow⟧, and $(t, x) \mapsto \varphi(t, x)$ is smooth ⟦Flow/Smooth · contDiff_flow_uncurry⟧.
4. *The flow lines stay where $\chi = 1$.* The flow lines are $M$-Lipschitz in time, $\|\varphi(t, x) - x\| \le M|t|$ ⟦Flow/Global · IsBddLipschitz.dist_flow_flow_le⟧. Put $r = R/2$ and $\tau = R/(2(M + 1))$. For $\|x - x_1\| < R/2$ and $|t| < \tau$ one gets $M|t| < R/2$, so $\|\varphi(t, x) - x_1\| < R$. There $\chi = 1$, so $X = G$ at $\varphi(t, x)$, which lies in $U$, and the flow line solves $x' = G(x)$. $\square$

The uniform time $\tau$, which Milnor's product $W \times (-\varepsilon, \varepsilon)$ requires, falls out of the bound on the speed.

**Theorem 10.1 (V7.4).** Let $E$ be a finite-dimensional real normed space (Milnor's $\mathbb R^n$), $U \subseteq E \times E$ open, $F : E \times E \to E$ smooth on $U$ and $z_1 \in U$.

1. (Existence and smooth dependence.) There are a neighbourhood $W$ of $z_1$, an $\varepsilon > 0$ and a map $(z, t) \mapsto u_z(t)$, smooth on $W \times (-\varepsilon, \varepsilon)$, such that for every $z = (u_0, v_0) \in W$: $u_z(0) = u_0$, $u_z'(0) = v_0$, and for $|t| < \varepsilon$, $(u_z(t), u_z'(t)) \in U$ and $u_z''(t) = F(u_z(t), u_z'(t))$ ⟦Chapter7/ODE · theorem_10_1⟧.
2. (Uniqueness.) Here $E$ may be any real normed space and $F$ need only be $C^1$ on $U$. If $(u_1, v_1)$ and $(u_2, v_2)$ satisfy $u_i' = v_i$, $v_i' = F(u_i, v_i)$ and $(u_i, v_i) \in U$ on an open preconnected $s \subseteq \mathbb R$, and $u_1(t_0) = u_2(t_0)$, $v_1(t_0) = v_2(t_0)$ for some $t_0 \in s$, then $u_1 = u_2$ on $s$ ⟦Chapter7/ODE · theorem_10_1_unique⟧.

*Proof.* Both parts pass to $G(u, v) = (v, F(u, v))$ on $U$, smooth (respectively $C^1$) where $F$ is. For (1), take $\varphi$, $r$, $\tau$ from the proposition at $z_1$, put $W = B(z_1, r)$, $\varepsilon = \tau$ and let $u_z(t)$ be the first component of $\varphi(t, z)$, a smooth function of $(z, t)$ everywhere. For $z \in W$ and $|t| < \tau$, the first component of an integral curve of $G$ has as derivative the second component ⟦Chapter7/ODE · hasDerivAt_fst_comp⟧, so $u_z' = (\varphi(\cdot, z))_2$ near $t$; hence $(u_z(t), u_z'(t)) = \varphi(t, z) \in U$, $u_z'(0) = v_0$, and the derivative of $u_z'$ is the second component of $G(\varphi(t, z))$ ⟦Chapter7/ODE · hasDerivAt_snd_comp⟧, which is $F(u_z(t), u_z'(t))$. For (2), the pairs $(u_i, v_i)$ are solutions of $x' = G(x)$ in $U$ that agree at $t_0$, so they agree on $s$ by uniqueness on an interval; take first components. $\square$

Part (2) is stronger than Milnor's uniqueness for small times: it holds on every common open interval, for $C^1$ equations on any normed space.

### VI.4 Uniqueness of geodesics

**Theorem (uniqueness of geodesics, V7.5).** (1) Let $\gamma_1$, $\gamma_2$ be geodesics on open sets $s_1$, $s_2$ containing $t_0$, with $\gamma_1(t_0) = \gamma_2(t_0)$ and $\gamma_1'(t_0) = \gamma_2'(t_0)$. Then $\gamma_1 = \gamma_2$ near $t_0$ ⟦Chapter7/Geodesic · IsGeodesicOn.eventuallyEq⟧. (2) If $\gamma_1$, $\gamma_2$ are geodesics on the same open preconnected set $s$ (an open interval) with the same position and velocity at one time of $s$, then $\gamma_1 = \gamma_2$ on $s$ ⟦Chapter7/Geodesic · IsGeodesicOn.eqOn⟧.

*Proof of (1).* $\mathrm{II}$ is defined only on $N$; the proof replaces it by an expression defined on an open set of $V \times V$.

1. Let $q = \gamma_1(t_0)$, $\sigma = \sigma_q$ and $Q = Q_\sigma$, the smooth extension of $P$ near $q$ (§VI.1). Define
$$G(x, v) = \big(v,\ dQ_x(v)\,v\big) \qquad (x, v \in V),$$
where $dQ_x(v)$ is the derivative of the operator-valued map $Q$ at $x$ in the direction $v$, an operator, applied to $v$. Since $Q$ is smooth near $q$, so is $dQ$, and $G$ is $C^1$ (indeed smooth) at $(q, \gamma_1'(t_0))$.
2. For each $i$, near $t_0$ the point $\gamma_i(t)$ lies in the domain of $\sigma$, and there the geodesic equation and $D_v = dQ(v)$ for tangent $v$ ⟦Chapter6/Projection · dN_tanProj_eq_fderiv⟧ give
$$\gamma_i''(t) = \mathrm{II}_{\gamma_i(t)}(\gamma_i'(t), \gamma_i'(t)) = dQ_{\gamma_i(t)}(\gamma_i'(t))\,\gamma_i'(t).$$
So both lifts $t \mapsto (\gamma_i(t), \gamma_i'(t))$ solve $x' = G(x)$ near $t_0$. The same chart $\sigma$ serves both curves, because the identity $D_v = dQ_\sigma(v)$ holds at every point of $N$ in the domain of $\sigma$, not only at $q$.
3. The lifts agree at $t_0$, so they agree near $t_0$ by local uniqueness; take first components. $\square$

*Proof of (2).* Apply the connectedness principle to the lifts $t \mapsto (\gamma_i(t), \gamma_i'(t))$, which are continuous on $s$ because $\gamma_i$ and $\gamma_i'$ are smooth there. If the lifts agree at $t \in s$, part (1) gives $\gamma_1 = \gamma_2$ near $t$; then also $\gamma_1' = \gamma_2'$ near $t$, so the lifts agree near $t$. $\square$

*What Milnor leaves implicit.* "The unique geodesic", and the uniqueness of $\exp_q(v)$ when defined (p. 58), need uniqueness on whole intervals, not only for small times in one chart; on an abstract manifold also the Hausdorff property. The verified edition calls this Lemma A.

### VI.5 The geodesic equation in a chart, and Lemma 10.2

The extension $Q$ of §VI.4 makes the geodesic equation an ordinary differential equation on an open set of $V \times V$, but nothing would keep its solutions in $TN$: the invariance criterion of the flow library needs a closed set, and $TN$ need not be closed in $V \times V$. So existence is solved in a chart, where solutions lie in $N$ by construction.

**The pseudo-inverse.** For a linear map $A : Y \to V$, $Y$ finite-dimensional, put $A^+ = (A^{\mathsf T}A)^{-1}A^{\mathsf T}$, where $A^{\mathsf T}$ is the transpose and $A^{\mathsf T}A$ the Gram operator ⟦Chapter7/GeodesicLocal · pinvL⟧ ⟦Chapter6/Projection · transposeL⟧ ⟦Chapter6/Projection · gramL⟧. If $A$ is injective then $A^+A = \mathrm{id}$ ⟦Chapter7/GeodesicLocal · pinvL_apply_self⟧ (the Gram operator is then injective ⟦Chapter6/Projection · gramL_injective⟧, hence invertible), and by definition $AA^+$ is the operator $A(A^{\mathsf T}A)^{-1}A^{\mathsf T}$ of §VI.1 ⟦Chapter7/GeodesicLocal · gramProj_eq_comp_pinvL⟧, the orthogonal projection onto the range of $A$. Near an injective $A$, $A \mapsto A^+$ is smooth ⟦Chapter7/GeodesicLocal · contDiffAt_pinvL⟧: the transpose and the Gram operator depend smoothly on $A$, and inversion is smooth at an invertible operator ⟦Mathlib/Analysis/Calculus/ContDiff/Operations · contDiffAt_map_inverse⟧.

**Chart facts.** Let $\sigma$ be a slice chart with parametrization $x$ on $T = T_\sigma$. Then $\sigma(x(u)) = (u, 0)$ ⟦Chapter7/GeodesicLocal · sliceChart_sliceParam⟧; differentiating, $d\sigma \circ dx = (\,\cdot\,, 0)$ ⟦Chapter7/GeodesicLocal · fderiv_sliceChart_comp_fderiv_sliceParam⟧, that is $(d\sigma\,dx_u w)_1 = w$ ⟦Chapter7/GeodesicLocal · fst_fderiv_sliceChart_fderiv_sliceParam⟧. The tangent space at $x(u)$ is the range of $dx_u$ ⟦Chapter7/GeodesicLocal · tangentSubspace_sliceParam⟧. And the chart coordinates of a tangent vector $v \in T_pN$ are $(d\sigma_p v)_1$, in the sense that $dx_{(\sigma p)_1}\big((d\sigma_p v)_1\big) = v$ ⟦Chapter7/GeodesicLocal · fderiv_sliceParam_fst_fderiv⟧: write $v = dx\,z$ and use the previous identity.

**The chart equation.** Define the Christoffel term and the chart spray
$$\Gamma(u)(w, w) = (dx_u)^+\big(d^2x_u(w, w)\big), \qquad (u, w) \longmapsto \big(w,\ -\Gamma(u)(w, w)\big)$$
⟦Chapter7/GeodesicLocal · chartAcc⟧ ⟦Chapter7/GeodesicLocal · chartSpray⟧. The term is quadratic in $w$: $\Gamma(u)(aw, aw) = a^2\,\Gamma(u)(w, w)$ ⟦Chapter7/GeodesicLocal · chartAcc_smul⟧ and $\Gamma(u)(0, 0) = 0$ ⟦Chapter7/GeodesicLocal · chartAcc_zero⟧. The spray is smooth on $T \times Z$ ⟦Chapter7/GeodesicLocal · contDiffOn_chartSpray⟧: $dx$ and $d^2x$ are smooth on $T$, and $u \mapsto (dx_u)^+$ is smooth because each $dx_u$ is injective.

$(dx_u)^+d^2x_u(w, w)$ is the coordinate vector of the tangential part of $d^2x_u(w, w)$, with components $\sum_{i,j}\Gamma^k_{ij}w^iw^j$ for the Christoffel symbols of p. 55; as no Christoffel symbols are defined formally, this is a remark, not a theorem.

**Proposition (solutions of the chart equation are geodesics, V7.3).** Let $\zeta = (u, w)$ be $C^\infty$ on an open set $s$, with $u(t) \in T$ and $\zeta'(t) = (w(t), -\Gamma(u(t))(w(t), w(t)))$ for $t \in s$. Then $t \mapsto x(u(t))$ is a geodesic on $s$ ⟦Chapter7/GeodesicLocal · isGeodesicOn_chart⟧, with velocity $dx_{u(t)}w(t)$ ⟦Chapter7/GeodesicLocal · hasDerivAt_sliceParam_chart⟧.

*Proof.* The curve lies in $N$ and is smooth as a composite. Its velocity is $dx_u u' = dx_u w$ by the chain rule, and this holds near every $t$, so its acceleration is the derivative of $t \mapsto dx_{u(t)}w(t)$:
$$d^2x_u(w, w) + dx_u w' = y - dx_u(dx_u)^+y = y - P\,y, \qquad y = d^2x_u(w, w),$$
where $dx_u(dx_u)^+$ is the orthogonal projection onto the range of $dx_u$ ⟦Chapter6/Projection · gramProj_eq_starProjection⟧, which is the tangent space at $x(u)$. So the acceleration is $y$ minus its tangential part, a normal vector. $\square$

Only this direction is stated in the chart; it is what existence needs, and uniqueness comes from §VI.4.

**A local flow of the chart spray.** For $u_0 \in T$, a *local spray* at $u_0$ ⟦Chapter7/GeodesicLocal · LocalSpray⟧ consists of a map $\varphi : \mathbb R \times (Z \times Z) \to Z \times Z$, smooth in all variables, and numbers $r, \tau > 0$, such that for every $z$ in the ball $B((u_0, 0), r)$ (for the maximum norm on $Z \times Z$): $\varphi(0, z) = z$, and for $|t| < \tau$, the first component of $\varphi(t, z)$ lies in $T$ and $t \mapsto \varphi(t, z)$ solves the chart equation. One exists ⟦Chapter7/GeodesicLocal · nonempty_localSpray⟧, by the local existence proposition of §VI.3 applied to the chart spray on the open set $T \times Z$ at $(u_0, 0)$.

**Milnor's rescaling.** Let $L$ be a local spray at $u_0$ and $c = \tau/2$ ⟦Chapter7/GeodesicLocal · LocalSpray.c⟧. Milnor obtains geodesics on $(-2, 2)$ by rescaling, $\gamma_v(t) = \gamma_{v/c}(ct)$ (pp. 56–57). Formally:
$$\mathrm{geo}(u, w)(t) = x\Big(\big(\varphi(ct, (u, w/c))\big)_1\Big)$$
⟦Chapter7/GeodesicLocal · LocalSpray.geo⟧, with chart position and velocity $\big((\varphi(ct, (u, w/c)))_1,\ c\,(\varphi(ct, (u, w/c)))_2\big)$ ⟦Chapter7/GeodesicLocal · LocalSpray.chartCurve⟧. The admissible chart data are $\mathcal G = B(u_0, r) \times B(0, cr)$ ⟦Chapter7/GeodesicLocal · LocalSpray.good⟧, an open set containing $(u_0, 0)$ ⟦Chapter7/GeodesicLocal · LocalSpray.isOpen_good⟧ ⟦Chapter7/GeodesicLocal · LocalSpray.mem_good⟧. For $(u, w) \in \mathcal G$ the rescaled datum $(u, w/c)$ lies in $B((u_0, 0), r)$ ⟦Chapter7/GeodesicLocal · LocalSpray.mem_ball_of_good⟧, and for $|t| < 2$, $|ct| < \tau$ ⟦Chapter7/GeodesicLocal · LocalSpray.mul_mem_Ioo⟧. Then:

- the rescaled chart curve solves the chart equation on $(-2, 2)$ ⟦Chapter7/GeodesicLocal · LocalSpray.hasDerivAt_chartCurve⟧. With $\xi = \varphi(ct, (u, w/c))$, the chain rule gives the derivative $\big(c\,\xi_2,\ -c^2\,\Gamma(\xi_1)(\xi_2, \xi_2)\big)$, because $\xi$ solves the chart equation; by quadratic homogeneity this is the chart spray at the rescaled point $(\xi_1, c\,\xi_2)$;
- it starts at $(u, w)$ ⟦Chapter7/GeodesicLocal · LocalSpray.chartCurve_zero⟧;
- hence $\mathrm{geo}(u, w)$ is a geodesic on $(-2, 2)$ ⟦Chapter7/GeodesicLocal · LocalSpray.isGeodesicOn_geo⟧ with $\mathrm{geo}(u, w)(0) = x(u)$ ⟦Chapter7/GeodesicLocal · LocalSpray.geo_zero⟧ and initial velocity $dx_u w$ ⟦Chapter7/GeodesicLocal · LocalSpray.hasDerivAt_geo_zero⟧;
- $(u, w, t) \mapsto \mathrm{geo}(u, w)(t)$ is smooth on $\mathcal G \times (-2, 2)$ ⟦Chapter7/GeodesicLocal · LocalSpray.contDiffOn_geo⟧, a composite of $\varphi$, linear maps and $x$, the first component staying in $T$.

**Lemma 10.2 (V7.6).** For every $q_0 \in N$ there are an open set $U \ni q_0$ of $V$, an $\varepsilon > 0$ and a map $\Theta : V \times V \times \mathbb R \to V$, smooth on $U \times B(0, \varepsilon) \times (-2, 2)$, such that for every $p \in N \cap U$ and every $v \in T_pN$ with $\|v\| < \varepsilon$, the curve $\gamma_v = \Theta(p, v, \cdot)$ is a geodesic on $(-2, 2)$ with $\gamma_v(0) = p$ and $\gamma_v'(0) = v$, and every geodesic on $(-2, 2)$ with this position and velocity at $0$ equals $\gamma_v$ on $(-2, 2)$ ⟦Chapter7/GeodesicLocal · lemma_10_2⟧.

*Proof.*

1. Let $\sigma = \sigma_{q_0}$, $u_0 = (\sigma q_0)_1 \in T$ ⟦Chapter1/ManifoldSubmanifold · toChart_apply_mem_target⟧, and $L$ a local spray at $u_0$, with $r$, $\tau$, $c$.
2. *From lengths to coordinates.* Put $C = \|d\sigma_{q_0}\| + 1$ and
$$U = \{p \in \operatorname{dom}\sigma : (\sigma p)_1 \in B(u_0, r),\ \|d\sigma_p\| < C\},$$
open because $p \mapsto ((\sigma p)_1, d\sigma_p)$ is continuous on the open domain of $\sigma$, and containing $q_0$. Put $\varepsilon = cr/C$. For $p \in U$ and $\|v\| < \varepsilon$,
$$\|(d\sigma_p v)_1\| \le \|d\sigma_p v\| \le \|d\sigma_p\|\,\|v\| < C\varepsilon = cr,$$
so the chart data $((\sigma p)_1, (d\sigma_p v)_1)$ lie in $\mathcal G$.
3. Define $\Theta(p, v, t) = \mathrm{geo}\big((\sigma p)_1, (d\sigma_p v)_1\big)(t)$. It is smooth on $U \times B(0, \varepsilon) \times (-2, 2)$, as the smooth map of the last list composed with the smooth map $(p, v, t) \mapsto (((\sigma p)_1, (d\sigma_p v)_1), t)$, which lands in $\mathcal G \times (-2, 2)$ by step 2.
4. For $p \in N \cap U$ and tangent $v$ with $\|v\| < \varepsilon$: $\Theta(p, v, \cdot)$ is a geodesic on $(-2, 2)$; its value at $0$ is $x((\sigma p)_1) = p$; its velocity at $0$ is $dx\big((d\sigma_p v)_1\big) = v$ by the chart facts. Uniqueness is the theorem of §VI.4 on the interval $(-2, 2)$. $\square$

*What Milnor leaves implicit.* To pass from the coordinate neighbourhood $W$ of Theorem 10.1 to "$p \in U$, $\|v\| < \varepsilon_1$" one must bound the coordinates of $v$ by $\|v\|$, uniformly near $p_0$: step 2. The smooth dependence of $\gamma_v(t)$ on $(p, v, t)$ is not in Milnor's statement but is used on p. 58; the smoothness of $\exp$ near the zero section rests on it.

### VI.6 The exponential map

Milnor (p. 57) puts $\exp_q(v) = \gamma(1)$ for the geodesic $\gamma : [0, 1] \to M$ with $\gamma(0) = q$ and $\frac{d\gamma}{dt}(0) = v$, if there is one, and observes $\gamma(t) = \exp_q(tv)$. The formal definition replaces $[0, 1]$, with its one-sided derivatives at the ends, by an open interval around it.

**Definition (V7.7; §0.9).** For $q, v \in V$, a curve $\gamma$ is a *geodesic from $q$ with initial velocity $v$* if for some $\delta > 0$ it is a geodesic on $(-\delta, 1 + \delta)$ with $\gamma(0) = q$ and $\gamma'(0) = v$ ⟦Chapter7/Exp · IsGeodesicFrom⟧. The *domain of $\exp$* is the set of pairs $(q, v)$ for which such a geodesic exists ⟦Chapter7/Exp · expDom⟧, and
$$\exp_q(v) = \gamma(1)$$
for one of them, chosen; off the domain $\exp_q(v) = q$, a placeholder ⟦Chapter7/Exp · exp⟧.

If $\gamma$ is a geodesic from $q$ with velocity $v$, then $(q, v)$ is in the domain ⟦Chapter7/Exp · IsGeodesicFrom.mem_expDom⟧, $q \in N$ ⟦Chapter7/Exp · IsGeodesicFrom.mem⟧ and $v \in T_qN$; and $\exp_q(v) \in N$ whenever $(q, v)$ is in the domain ⟦Chapter7/HopfRinow · exp_mem_of_mem_expDom⟧. A geodesic on any open preconnected set $s$ containing $0$ and $1$ is a geodesic from $\gamma(0)$ with initial velocity $\gamma'(0)$ ⟦Chapter7/Exp · isGeodesicFrom_of_isGeodesicOn⟧: $s$ contains balls around $0$ and $1$ and, being an interval, everything between, so it contains $(-\delta, 1 + \delta)$ for small $\delta$.

**Proposition ($\exp$ is well defined, V7.7).** Two geodesics from $q$ with initial velocity $v$ agree on an open interval containing $[0, 1]$ ⟦Chapter7/Exp · IsGeodesicFrom.eqOn⟧. Consequently $\exp_q(v) = \gamma(1)$ for *every* geodesic $\gamma$ from $q$ with initial velocity $v$ ⟦Chapter7/Exp · IsGeodesicFrom.exp_eq⟧ ⟦Chapter7/Exp · exp_eq_of_mem_expDom⟧.

*Proof.* Restrict both to $(-\delta, 1 + \delta)$ with $\delta$ the smaller of their two margins and apply uniqueness of geodesics (§VI.4) at $t = 0$. The chosen geodesic in the definition of $\exp$ is one of them. $\square$

This is Milnor's remark that $\exp_q(v)$, if defined, is uniquely defined (p. 58).

For $q \in N$ the constant curve is a geodesic from $q$ with velocity $0$ ⟦Chapter7/Exp · isGeodesicFrom_const⟧, so $(q, 0)$ is in the domain ⟦Chapter7/Exp · zero_mem_expDom⟧ and $\exp_q(0) = q$ ⟦Chapter7/Exp · exp_zero⟧.

**Proposition ($\gamma(t) = \exp_q(tv)$, V7.7).** Let $\gamma$ be a geodesic from $q$ with initial velocity $v$, on $(-\delta, 1 + \delta)$. For each $t$ in this interval, $s \mapsto \gamma(ts)$ is a geodesic from $q$ with initial velocity $tv$, and $\exp_q(tv) = \gamma(t)$ ⟦Chapter7/Exp · IsGeodesicFrom.exp_smul⟧. In particular $t \mapsto \exp_q(tv)$ is a geodesic on $(-\delta, 1 + \delta)$, equal there to $\gamma$ ⟦Chapter7/Exp · IsGeodesicFrom.isGeodesicOn_exp_smul⟧.

*Proof.* By homogeneity (§VI.2), $\eta(s) = \gamma(ts)$ is a geodesic on $\{s : ts \in (-\delta, 1 + \delta)\}$. This set is convex, hence preconnected, and contains $0$ and $1$ (the latter because $t$ is in the interval). So $\eta$ is a geodesic from $\eta(0) = q$ with initial velocity $\eta'(0) = t\gamma'(0) = tv$ (chain rule), and $\exp_q(tv) = \eta(1) = \gamma(t)$ by well-definedness. The second statement: a curve equal on an open set to a geodesic is a geodesic there. $\square$

The same argument works for any geodesic, not only near $[0, 1]$: if $\gamma$ is a geodesic on an open interval $s \ni 0$, then
$$\exp_{\gamma(0)}\big(t\,\gamma'(0)\big) = \gamma(t) \qquad (t \in s)$$
⟦Chapter7/GeodesicFlow · IsGeodesicOn.exp_smul_eq⟧ ⟦Chapter7/GeodesicFlow · IsGeodesicOn.eqOn_exp_smul⟧, the preimage of $s$ under $\sigma \mapsto t\sigma$ being again an interval containing $0$ and $1$ ⟦Chapter7/GeodesicFlow · isPreconnected_preimage_mul_add⟧. So the radial curves $t \mapsto \exp_y(tw)$ are all the geodesics there are; §VI.16 builds the geodesic flow on this observation.

*The two definitions of the domain.* A geodesic on an open interval containing $[0, 1]$ restricts to one on $[0, 1]$ in Milnor's sense, with the same value at $1$. Conversely a geodesic on $[0, 1]$ extends beyond both ends, so the two domains coincide; this is proved later, with the tools of Chapters 9 and 11 ⟦Chapter9/GeodesicVariation · exists_initial_ray⟧ ⟦Chapter11/ExpSmooth · mem_expDom_of_isGeodesicOn⟧, and nothing in this part needs it.

### VI.7 Smoothness near the zero section, and $d(\exp_q)_0 = \mathrm{id}$

Milnor (p. 58) says that, by Lemma 10.2, $(q, v) \mapsto \exp_q(v)$ is defined and differentiable on a neighbourhood of $(p, 0)$ in $TM$. For a subset of $V \times V$, "smooth" means what it means for Milnor: near each point, the restriction of a smooth map on an open set.

**Proposition (Lemma 10.2 in terms of $\exp$, V7.8).** For every $q_0 \in N$ there are an open $U \ni q_0$, an $\varepsilon > 0$ and a map $F : V \times V \to V$, smooth on $U \times B(0, \varepsilon)$, such that for every $p \in N \cap U$ and $v \in T_pN$ with $\|v\| < \varepsilon$, $(p, v)$ is in the domain of $\exp$ and $\exp_p(v) = F(p, v)$ ⟦Chapter7/Exp · exists_exp_eq⟧.

*Proof.* Take $U$, $\varepsilon$, $\Theta$ from Lemma 10.2 and $F(p, v) = \Theta(p, v, 1)$, smooth because $1 \in (-2, 2)$. The geodesic $\Theta(p, v, \cdot)$ on $(-2, 2)$ is a geodesic from $p$ with initial velocity $v$ (take $\delta = 1$), so $\exp_p(v) = \Theta(p, v, 1)$. $\square$

**Theorem ($\exp$ near the zero section, V7.8).** There is an open set $O \subseteq V \times V$ containing $(q, 0)$ for every $q \in N$ such that every point of $TN \cap O$ is in the domain of $\exp$, and near each point of $TN \cap O$, $\exp$ is the restriction to $TN$ of a smooth map on an open set of $V \times V$ ⟦Chapter7/Exp · exists_isOpen_exp⟧. Moreover $(q, v) \mapsto \exp_q(v)$ is smooth on the open subset $TN \cap O$ of the manifold $TN$ ⟦Chapter7/Exp · contMDiffOn_exp⟧.

*Proof.* Choose, for each $q_0 \in N$, the data $U(q_0)$, $\varepsilon(q_0)$, $F_{q_0}$ of the last proposition, and let $O$ be the union of the open sets $U(q_0) \times B(0, \varepsilon(q_0))$. It contains every $(q, 0)$. A point $z$ of $TN \cap O$ lies in one of these sets, so it is in the domain, and on that open set $\exp = F_{q_0}$ along $TN$. For the manifold statement: on the open neighbourhood of $z$ in $TN$ cut out by that set, $\exp$ agrees with $F_{q_0}$ composed with the inclusion $TN \to V \times V$, which is smooth ⟦Milnor/Chapter2/Submanifold · IsSliceSubmanifold.contMDiff_val⟧. $\square$

This is stronger than Milnor's statement in one respect: one open set serves the whole zero section. The smoothness of $\exp$ on its whole domain, not only near the zero section, is proved in Chapter 11 ⟦Chapter11/ExpSmooth · exists_contDiffOn_exp⟧ ⟦Chapter11/ExpSmooth · contMDiffOn_exp_expDom⟧; §VI.16 proves the continuity on the whole domain that Corollary 10.10 needs.

**Theorem ($d(\exp_q)_0 = \mathrm{id}$, V7.8).** For $q \in N$, the map $\exp_q$, regarded as a map on the vector space $T_qN$, has at $0$ the derivative the inclusion $T_qN \to V$ ⟦Chapter7/Exp · hasFDerivAt_exp_zero⟧.

*Proof.*

1. Take $U$, $\varepsilon$, $F$ from the proposition at $q_0 = q$ and let $F_q = F(q, \cdot)$, smooth near $0$. On the ball of radius $\varepsilon$ in $T_qN$, $\exp_q = F_q$.
2. *Radial directions.* Let $v \in T_qN$ with $\|v\| < \varepsilon$, and $\gamma$ a geodesic from $q$ with velocity $v$. For $|t| < 1$, $\|tv\| < \varepsilon$, so $F_q(tv) = \exp_q(tv) = \gamma(t)$ for $t$ near $0$ (§VI.6). The curve $t \mapsto F_q(tv)$ has derivative $dF_q(0)\,v$ at $0$ by the chain rule, and $\gamma$ has derivative $v$. So $dF_q(0)\,v = v$.
3. *All directions.* For $v \ne 0$ in $T_qN$, apply step 2 to $av$ with $a = \varepsilon/(2\|v\|)$ and divide by $a$, using linearity. So $dF_q(0)$ restricted to $T_qN$ is the inclusion.
4. The derivative at $0$ of $F_q$ composed with the inclusion of $T_qN$ is therefore the inclusion, and $\exp_q$ agrees with this composite near $0$. $\square$

In Milnor's computation (p. 58), the Jacobian of $(q, v) \mapsto (q, \exp_q v)$ at $(p, 0)$ has $F_*(\partial/\partial t^j) = \partial/\partial u_2^j$, which is this statement.

### VI.8 Normal radii and Lemma 10.3

**Definition (normal coordinates, V7.9).** Let $q \in N$ and $\varepsilon > 0$, and write $B_\varepsilon(q) = \{v \in T_qN : \|v\| < \varepsilon\}$. *Normal coordinates of radius $\varepsilon$ at $q$* consist of open sets $O, U \subseteq V$ and maps $F$, smooth on $O$, and $G$, smooth on $U$, such that ⟦Chapter7/NormalNbhd · NormalCoord⟧:

- for $v \in B_\varepsilon(q)$: $(q, v)$ is in the domain of $\exp$, $v \in O$, $F(v) = \exp_q(v)$, $\exp_q(v) \in U$, and $G(\exp_q v) = v$;
- for $y \in N \cap U$: $G(y) \in T_qN$, $\|G(y)\| < \varepsilon$, and $\exp_q(G(y)) = y$.

So $\exp_q$ is a bijection of $B_\varepsilon(q)$ onto the open subset $U_q = N \cap U$ of $N$, and it and its inverse are restrictions of smooth maps on open sets of $V$: Milnor's "maps diffeomorphically onto an open set $U_q$" (Lemma 10.3 (3), p. 59), made precise in his own sense of smoothness for subsets of Euclidean space. $\varepsilon$ is a *normal radius* at $q$ if such coordinates exist ⟦Chapter7/NormalNbhd · IsNormalRadius⟧. (The name is the exposition's.)

The proof of Lemma 10.3 reads $\exp$ in the chart of §VI.5 and inverts Milnor's map $(q, v) \mapsto (q, \exp_q v)$ there.

**$\exp$ in the chart.** Let $\sigma$ be a slice chart, $x$ its parametrization, $L$ a local spray at $u_0$ with constants $r$, $\tau$, $c$. Points $z$ of $B((u_0, 0), r)$ have first component in $T$ ⟦Chapter7/NormalNbhd · LocalSpray.fst_mem_target⟧, and the ball is stable under $(u, w) \mapsto (u, aw)$ for $|a| \le 1$ ⟦Chapter7/NormalNbhd · LocalSpray.mem_ball_smul⟧.

- *Homogeneity of the chart flow.* For $(u, w)$ in the ball, $|a| \le 1$ and $|s| < \tau$,
$$\varphi(s, (u, aw)) = \Big(\big(\varphi(as, (u, w))\big)_1,\ a\,\big(\varphi(as, (u, w))\big)_2\Big)$$
⟦Chapter7/NormalNbhd · LocalSpray.φ_smul⟧. Both sides solve the chart equation in $T \times Z$ on $(-\tau, \tau)$ (the right side by the chain rule and quadratic homogeneity) and agree at $s = 0$; apply uniqueness on an interval (§VI.3).
- *The chart expression of $\exp$.* $E(u, w) = \big(\varphi(c, (u, w/c))\big)_1$ ⟦Chapter7/NormalNbhd · LocalSpray.chartExp⟧ is smooth on $Z \times Z$ ⟦Chapter7/NormalNbhd · LocalSpray.contDiff_chartExp⟧, lies in $T$ for $(u, w) \in \mathcal G$ ⟦Chapter7/NormalNbhd · LocalSpray.chartExp_mem⟧, and
$$\exp\big(x(u),\ dx_u w\big) = x\big(E(u, w)\big) \qquad ((u, w) \in \mathcal G)$$
⟦Chapter7/NormalNbhd · LocalSpray.exp_eq_chartExp⟧, because $\mathrm{geo}(u, w)$ is a geodesic from $x(u)$ with initial velocity $dx_u w$ ⟦Chapter7/NormalNbhd · LocalSpray.isGeodesicFrom_geo⟧ and its value at $1$ is $x(E(u, w))$.
- $E(u, 0) = u$ for $u \in B(u_0, r)$ ⟦Chapter7/NormalNbhd · LocalSpray.chartExp_zero⟧: $(u, 0)$ is a zero of the chart spray, so the constant curve solves the chart equation, and by uniqueness the flow line through $(u, 0)$ is constant.
- For $(u_0, b) \in \mathcal G$, the curve $t \mapsto E(u_0, tb)$ has velocity $b$ at $t = 0$ ⟦Chapter7/NormalNbhd · LocalSpray.hasDerivAt_chartExp_line⟧. For $|t| < 1$ the homogeneity of the flow gives $E(u_0, tb) = (\varphi(ct, (u_0, b/c)))_1$; at $t = 0$ its derivative is $c$ times the first component of the chart spray at $(u_0, b/c)$, that is $c \cdot b/c = b$.

**Milnor's Jacobian.** Let $\Phi(z) = (z_1, E(z))$ ⟦Chapter7/NormalNbhd · LocalSpray.chartF⟧, the map $(q, v) \mapsto (q, \exp_q v)$ in the chart. Its derivative at $(u_0, 0)$ is
$$(a, b) \longmapsto (a,\ a + b),$$
an isomorphism with inverse $(a, b) \mapsto (a, b - a)$ ⟦Chapter7/NormalNbhd · LocalSpray.jacobian⟧ ⟦Chapter7/NormalNbhd · LocalSpray.hasFDerivAt_chartF⟧. *Proof.* In the direction $(a, 0)$: $E(u, 0) = u$ near $u_0$, so $dE(a, 0) = a$. In the direction $(0, b)$ with $(u_0, b) \in \mathcal G$: the chain rule along $t \mapsto (u_0, tb)$ and the velocity just computed give $dE(0, b) = b$; for arbitrary $b$ scale it into $\mathcal G$ and use linearity. Add. $\square$

These are the images of $\partial/\partial u^i$ and $\partial/\partial t^j$ in Milnor's matrix $\begin{pmatrix} I & I \\ 0 & I \end{pmatrix}$ (p. 58).

**Lemma 10.3 (V7.10).** For each $p \in N$ there are an open set $O \ni p$ of $V$ and an $\varepsilon > 0$ such that, with $W = N \cap O$:

1. for all $q_1, q_2 \in W$ there is exactly one $v \in T_{q_1}N$ with $\|v\| < \varepsilon$ and $\exp_{q_1}(v) = q_2$;
2. there are an open set $O_2 \subseteq V \times V$ and a map $G$, smooth on $O_2$, such that for all $q_1, q_2 \in W$: $(q_1, q_2) \in O_2$ and $G(q_1, q_2)$ is the vector of (1);
3. $\varepsilon$ is a normal radius at every $q \in W$

⟦Chapter7/NormalNbhd · lemma_10_3⟧. By (1), each $U_q$ of (3) contains $W$.

*Proof.* The proof is Milnor's, in the slice chart $\sigma = \sigma_p$, with $u_0 = (\sigma p)_1$, a local spray $L$ at $u_0$ and the parametrization $x$.

1. *The inverse function theorem.* $\Phi$ is smooth, and its derivative at $(u_0, 0)$ is invertible. The companion volume's inverse function theorem for manifolds ⟦Milnor/Chapter1/InverseFunction · ContMDiff.isLocalDiffeomorphAt_of_isInvertible_mfderiv⟧ gives a partial diffeomorphism $\hat\Phi$ between open subsets of $Z \times Z$, whose domain contains $(u_0, 0)$ and on which it agrees with $\Phi$; its inverse $\hat\Phi^{-1}$ is smooth on the image, and $\hat\Phi^{-1}(\Phi(z)) = z$ on the domain. Milnor says "implicit function theorem"; it is this one.
2. *The shape of $V'$.* Milnor takes $V' = \{(q, v) : q \in U',\ \|v\| < \varepsilon\}$; that such sets form a neighbourhood base needs a uniform comparison of $\|v\|$ with the coordinates of $v$, made explicit here. Let $C_2 = \|dx_{u_0}\| + 1$, and let $A$ be the set of $z$ in the domain of $\hat\Phi$ and in $\mathcal G$ with $z_1 \in T$ and $\|dx_{z_1}\| < C_2$; it is open and contains $(u_0, 0)$, so it contains a ball $B((u_0, 0), \rho)$. Let $C_1 = \|d\sigma_p\| + 1$, $\varepsilon = \rho/C_1$, and
$$S = \{z \in B((u_0, 0), \rho) : \|dx_{z_1}z_2\| < \varepsilon\},$$
the chart picture of $\{(q, v) : \|v\| < \varepsilon\}$. $S$ is open, contains $(u_0, 0)$ and lies in $A$. Its image $\Phi(S) = \hat\Phi(S)$ is open (a partial homeomorphism maps open subsets of its domain to open sets) and contains $\Phi(u_0, 0) = (u_0, u_0)$, hence a ball $B((u_0, u_0), \rho_2)$. Put $\rho' = \min(\rho, \rho_2)$ and
$$O = \{y \in \operatorname{dom}\sigma : \|(\sigma y)_1 - u_0\| < \rho',\ \|d\sigma_y\| < C_1\},$$
open (by continuity of $y \mapsto ((\sigma y)_1, d\sigma_y)$) and containing $p$.
3. *Four facts.* (K1) For $y \in O$ and $\|v\| < \varepsilon$, the chart data $((\sigma y)_1, (d\sigma_y v)_1)$ lie in $B((u_0, 0), \rho)$, since $\|(d\sigma_y v)_1\| \le \|d\sigma_y\|\,\|v\| < C_1\varepsilon = \rho$. (K2) Points of that ball are in the domain of $\hat\Phi$, in $\mathcal G$, and have first component in $T$. (K3) For $q \in N \cap O$ and $v \in T_qN$ with $\|v\| < \varepsilon$, the chart data of $(q, v)$ lie in $S$ (the condition $\|dx\,(d\sigma_q v)_1\| = \|v\| < \varepsilon$ holds by the chart facts of §VI.5), and $\exp_q(v) = x\big(E((\sigma q)_1, (d\sigma_q v)_1)\big)$ by the chart expression of $\exp$. (K4) For $q_1, q_2 \in N \cap O$, the point $((\sigma q_1)_1, (\sigma q_2)_1)$ lies within $\rho_2$ of $(u_0, u_0)$, hence in $\Phi(S)$: there is $w$ with $((\sigma q_1)_1, w) \in S$ and $\Phi((\sigma q_1)_1, w) = ((\sigma q_1)_1, (\sigma q_2)_1)$ (the first component of $\Phi$ is the identity), and then $\exp_{q_1}(dx\,w) = q_2$.
4. *Item (1).* Existence: $v = dx_{(\sigma q_1)_1}w$ with $w$ from (K4) is tangent at $q_1$ (it is in the range of $dx$), has $\|v\| < \varepsilon$ (definition of $S$), and $\exp_{q_1}(v) = q_2$. Uniqueness: if $v'$ is tangent, $\|v'\| < \varepsilon$ and $\exp_{q_1}(v') = q_2$, then by (K3) the chart data $((\sigma q_1)_1, (d\sigma_{q_1}v')_1)$ lie in $S$ and $E$ of them is $(\sigma q_2)_1$; so $\Phi$ takes the same value at these chart data and at $((\sigma q_1)_1, w)$. Applying $\hat\Phi^{-1}$, $(d\sigma_{q_1}v')_1 = w$, and $v' = dx\,w = v$ by the chart facts.
5. *Item (2).* Let $O_2$ be the set of pairs $(y_1, y_2)$ of points of the domain of $\sigma$ with $((\sigma y_1)_1, (\sigma y_2)_1)$ in $T \times Z$ and in the image of $\hat\Phi$; it is open. Put
$$G(y_1, y_2) = dx_{(\sigma y_1)_1}\Big(\big(\hat\Phi^{-1}((\sigma y_1)_1, (\sigma y_2)_1)\big)_2\Big),$$
smooth on $O_2$ as a composite of smooth maps. For $q_1, q_2 \in N \cap O$, step 3 shows $(q_1, q_2) \in O_2$ and $\hat\Phi^{-1}((\sigma q_1)_1, (\sigma q_2)_1) = ((\sigma q_1)_1, w)$, so $G(q_1, q_2)$ is the vector of item (1).
6. *Item (3).* Fix $q \in N \cap O$ and write $u_q = (\sigma q)_1$. The normal coordinates are: $O_q = \{v : (u_q, (d\sigma_q v)_1) \in B((u_0, 0), \rho)\}$, open; $F_q(v) = x\big(E(u_q, (d\sigma_q v)_1)\big)$, smooth on $O_q$ by (K2); $U_q = \{y \in \operatorname{dom}\sigma : (u_q, (\sigma y)_1) \in \Phi(S)\}$, open; and $G_q(y) = dx_{u_q}\big((\hat\Phi^{-1}(u_q, (\sigma y)_1))_2\big)$, smooth on $U_q$. The ten conditions follow from steps 3–4: vectors of $B_\varepsilon(q)$ are in the domain of $\exp$ (the geodesics $\mathrm{geo}$) and in $O_q$ (K1); $F_q = \exp_q$ there (K3); $\exp_q$ maps them into $U_q$, because $(u_q, (\sigma(\exp_q v))_1) = \Phi(u_q, (d\sigma_q v)_1)$ with the argument in $S$; $G_q \circ \exp_q = \mathrm{id}$ on $B_\varepsilon(q)$ because $\hat\Phi^{-1} \circ \Phi = \mathrm{id}$; and for $y \in N \cap U_q$, writing $(u_q, (\sigma y)_1) = \Phi(u_q, w)$ with $(u_q, w) \in S$, $G_q(y) = dx\,w$ is tangent at $q$, has norm $< \varepsilon$, and $\exp_q(G_q(y)) = x(E(u_q, w)) = x((\sigma y)_1) = y$. $\square$

*Geodesics or vectors.* Milnor's item (1) speaks of "a unique geodesic of length $< \varepsilon$", the formal item (1) of initial vectors. They agree: a geodesic from $q_1$ with initial velocity $v$, $\|v\| < \varepsilon$, ending at $q_2$ has $\exp_{q_1}(v) = q_2$, so $v$ is the vector of (1) ⟦Chapter7/NormalNbhd · lemma_10_3_geodesic⟧; the geodesic is $t \mapsto \exp_{q_1}(tv)$ on $[0, 1]$ (§VI.6), of length $\|v\|$ (§VI.10).

**Corollary.** Every point of $N$ has a normal radius ⟦Chapter7/NormalNbhd · exists_isNormalRadius⟧ (item (3) at $q = p$).

**$\exp_q$ as a partial diffeomorphism (V7.9, V7.10).** The same statement in Mathlib's language: let $\exp_q$ be regarded as a map from the vector space $T_qN$ to the manifold $N$ (with a placeholder value where $\exp_q(v) \notin N$) ⟦Chapter7/NormalNbhd · expToN⟧ ⟦Chapter7/NormalNbhd · coe_expToN⟧. If $\varepsilon$ is a normal radius at $q$, then $\exp_q$ restricts to a partial diffeomorphism from the open ball of radius $\varepsilon$ in $T_qN$ onto the open subset $\{y \in N : y \in U\}$ of $N$ ⟦Chapter7/NormalNbhd · NormalCoord.expDiffeo⟧. Its inverse is $y \mapsto$ the orthogonal projection of $G(y)$ onto $T_qN$, which is $G(y)$ itself because $G(y)$ is tangent ⟦Chapter7/NormalNbhd · NormalCoord.coe_orthogonalProjectionOnto_G⟧; $\exp_q$ takes values in $N$ on the ball ⟦Chapter7/NormalNbhd · NormalCoord.exp_mem⟧. Smoothness into the manifold $N$ uses that a map into $N$ which agrees near a point with a smooth map into $V$ is smooth into $N$ there ⟦Chapter7/NormalNbhd · contMDiffAt_of_val_eventuallyEq⟧ (read it in the slice chart at the image point), applied to $F$; the inverse is smooth because $G$ composed with the inclusion of $N$ is. Hence $\exp_q$ is a local diffeomorphism at $0$: for every $q \in N$ there are $\varepsilon > 0$ and a partial diffeomorphism with domain the $\varepsilon$-ball of $T_qN$, whose image contains $q$, equal to $\exp_q$ on that ball ⟦Chapter7/NormalNbhd · exists_expDiffeo⟧. This is what Milnor obtains on p. 58 from $d(\exp_q)_0 = \mathrm{id}$ and the inverse function theorem; formally it comes out of Lemma 10.3.

### VI.9 The Gauss lemma (Lemma 10.5)

Milnor's Lemma 10.5 (p. 60) says that in $U_q$ the geodesics through $q$ are the orthogonal trajectories of the hypersurfaces $\{\exp_q(v) : \|v\| = \text{const}\}$. His proof takes a curve $v(t)$ of unit vectors and the surface $f(r, t) = \exp_q(rv(t))$, and shows that $\langle\partial f/\partial r, \partial f/\partial t\rangle$ does not depend on $r$. The formal statement is stronger and needs no curve $v(t)$.

Fix normal coordinates $(O, U, F, G)$ of radius $\varepsilon$ at $q$ and write $D_w = dF_w$, $D^2_w = d^2F_w$ for $w \in O$. For $w \in B_\varepsilon(q)$, $F$ is smooth near $w$ ⟦Chapter7/GaussLemma · NormalCoord.contDiffAt_F⟧ ⟦Chapter7/GaussLemma · NormalCoord.hasFDerivAt_F⟧, and along a line through $w$ in a direction of $T_qN$, $F = \exp_q$ near $w$ ⟦Chapter7/GaussLemma · NormalCoord.eventually_F_eq⟧ (the points stay in the ball for small parameter).

**Lemma (radial speed).** For $u \in B_\varepsilon(q)$ and $0 \le r \le 1$, $\|D_{ru}(u)\| = \|u\|$ ⟦Chapter7/GaussLemma · NormalCoord.norm_fderiv_F_apply⟧.

*Proof.* $t \mapsto \exp_q(tu)$ is a geodesic near $[0, 1]$, with velocity $u$ at $0$ (§VI.6). Near $t = r$ it equals $t \mapsto F(tu)$, whose velocity at $r$ is $D_{ru}(u)$. By constant speed (§VI.2) the speed at $r$ is the speed at $0$. $\square$

**Lemma ($G$ inverts $F$ infinitesimally).** For $w \in B_\varepsilon(q)$ and $v \in T_qN$, $dG_{F(w)}(D_w v) = v$; in particular $D_w$ is injective on $T_qN$ ⟦Chapter7/GaussLemma · NormalCoord.fderiv_G_fderiv_F⟧ ⟦Chapter7/GaussLemma · NormalCoord.injective_fderiv_F⟧.

*Proof.* $G(F(w + sv)) = G(\exp_q(w + sv)) = w + sv$ for $s$ near $0$; differentiate at $s = 0$ with the chain rule. $\square$

**Lemma 10.5, the Gauss lemma (V7.12).** Let $\varepsilon$ be a normal radius at $q$. For $w, x \in T_qN$ with $\|w\| < \varepsilon$,
$$\big\langle d(\exp_q)_w(w),\ d(\exp_q)_w(x)\big\rangle = \langle w, x\rangle,$$
where $\exp_q$ is regarded as a map on the vector space $T_qN$ ⟦Chapter7/GaussLemma · gauss_lemma⟧. In particular, if $x \perp w$, the radial velocity $d(\exp_q)_w(w)$ is orthogonal to $d(\exp_q)_w(x)$ ⟦Chapter7/GaussLemma · gauss_lemma_orthogonal⟧.

The vectors $x \perp w$ form the tangent space at $w$ of the sphere $\{\|v\| = \|w\|\}$, so the special case is Milnor's statement; the general one holds for every $x \in T_qN$. The statement for $\exp_q$ follows from the one for $F$ ⟦Chapter7/GaussLemma · NormalCoord.inner_fderiv_F⟧, since near $w$ in $T_qN$, $\exp_q = F$ and the derivative of $\exp_q$ is $D_w$ restricted to $T_qN$.

*Proof for $F$.* The proof is Milnor's, with $f(r, s) = \exp_q(r(w + sx))$ and everything computed in $V$. Put
$$g(r) = \big\langle D_{rw}(w),\ D_{rw}(rx)\big\rangle \qquad (0 \le r \le 1),$$
which is $\langle\partial f/\partial r, \partial f/\partial s\rangle$ at $s = 0$. For $r \in [0, 1]$ the point $rw$ lies in $B_\varepsilon(q)$, so $F$ is smooth near it and $g$ is continuous on $[0, 1]$. Clearly $g(0) = 0$ and $g(1) = \langle D_w w, D_w x\rangle$. For $0 < r < 1$, the product rule gives
$$g'(r) = \big\langle D^2_{rw}(w, w),\ D_{rw}(rx)\big\rangle + \big\langle D_{rw}(w),\ D^2_{rw}(w, rx) + D_{rw}(x)\big\rangle,$$
because $r \mapsto D_{rw}(w)$ has derivative $D^2_{rw}(w, w)$ and $r \mapsto D_{rw}(rx)$ has derivative $D^2_{rw}(w, rx) + D_{rw}(x)$.

1. *The first term vanishes.* Near $t = r$, $\exp_q(tw) = F(tw)$, so the acceleration of the geodesic $t \mapsto \exp_q(tw)$ at $r$ is $D^2_{rw}(w, w)$, and it is normal to $N$ at $\exp_q(rw)$. On the other hand $D_{rw}(rx)$ is the velocity at $s = 0$ of $s \mapsto F(rw + s\,rx) = \exp_q(rw + s\,rx)$, a curve in $N$ through $\exp_q(rw)$, so it is tangent there (§VI.1). Milnor's version: $\frac{D}{\partial r}\frac{\partial f}{\partial r} = 0$ because the radial curves are geodesics.
2. *The second term is $\langle w, x\rangle$.* Consider $h(s) = \|D_{r(w + sx)}(w + sx)\|^2$. For $s$ near $0$, $w + sx \in B_\varepsilon(q)$, and the radial speed lemma gives $h(s) = \|w + sx\|^2$. Differentiate at $s = 0$: the left side gives $2\langle D_{rw}w,\ D^2_{rw}(rx, w) + D_{rw}x\rangle$, the right side $2\langle w, x\rangle$. Second derivatives of a smooth map are symmetric ⟦Mathlib/Analysis/Calculus/FDeriv/Symmetric · ContDiffAt.isSymmSndFDerivAt⟧, so $D^2_{rw}(rx, w) = D^2_{rw}(w, rx)$, and the second term equals $\langle w, x\rangle$. Milnor's version: $\langle\frac{\partial f}{\partial r}, \frac{D}{\partial r}\frac{\partial f}{\partial s}\rangle = \frac12\frac{\partial}{\partial s}\|\frac{\partial f}{\partial r}\|^2$, with his symmetry Lemma 8.7 replaced by the symmetry of second derivatives in $V$.
3. So $g' = \langle w, x\rangle$ on $(0, 1)$. By the mean value theorem ⟦Mathlib/Analysis/Calculus/Deriv/MeanValue · exists_hasDerivAt_eq_slope⟧, $g(1) - g(0) = \langle w, x\rangle$, that is $\langle D_w w, D_w x\rangle = \langle w, x\rangle$. $\square$

*What Milnor leaves implicit.* That the sets $\{\exp_q(v) : \|v\| = r\}$ are hypersurfaces with tangent vectors $\frac{d}{dt}\exp_q(r_0v(t))$ uses that $\exp_q$ is a diffeomorphism on the ball; the form proved here sidesteps the hypersurfaces entirely.

### VI.10 Paths and their lengths

Theorem 10.4 compares the geodesic with every *other piecewise smooth path*. Milnor defines these only on p. 67 (§11) and uses them from p. 59 on; the formal text defines them, and a wider class, here.

**Definitions (V7.11; §0.3).** Let $c : \mathbb R \to V$ and $a \le b$.

- The *length* of $c$ on $[a, b]$ is $L(c|[a, b]) = \int_a^b \|c'(t)\|\,dt$ ⟦Chapter7/Path · pathLength⟧, where $c'(t)$ is taken to be $0$ where $c$ is not differentiable, the convention of the formal language (§0.1); for the paths below this happens only on a null set.
- $c$ is *piecewise smooth* on $[a, b]$ if it is continuous on $[a, b]$ and there is a finite set $B$ of break points such that $c$ is $C^\infty$ (with one-sided derivatives at the ends) on every $[s, t] \subseteq [a, b]$, $s < t$, whose interior contains no point of $B$ ⟦Chapter7/Path · IsPiecewiseSmooth⟧. For Milnor's subdivision $a = t_0 < \dots < t_k = b$ take $B = \{t_i\}$.
- $c$ is *admissible* on $[a, b]$ if it is continuous on $[a, b]$, differentiable at all but countably many points of $(a, b)$, and $\|c'\|$ is integrable on $[a, b]$ ⟦Chapter7/Path · IsAdmissible⟧.

A path in $N$ is one with $c([a, b]) \subseteq N$. The lower bounds for lengths below are proved for admissible paths, a wider class than the piecewise smooth paths, stable under restriction to subintervals ⟦Chapter7/Path · IsAdmissible.mono⟧, in which the fundamental theorem of calculus holds.

**Proposition.** Piecewise smooth paths are admissible ⟦Chapter7/Path · IsPiecewiseSmooth.isAdmissible⟧.

*Proof.* Off the finite set $B$, a point $t \in (a, b)$ has a closed interval around it free of break points, on which $c$ is smooth; so $c$ is differentiable at $t$. For integrability, induct on the number of break points in the open interval: with none, $c$ is smooth on the closed piece, its one-sided derivative is continuous there and agrees with $c'$ inside, so $\|c'\|$ is integrable ⟦Chapter7/Path · IsPiecewiseSmooth.intervalIntegrable_of_contDiffOn⟧; with some, split at one of them, which leaves fewer on each side, and integrability is additive. $\square$

**Properties of length (V7.11).** For an admissible $c$ on $[a, b]$ (with $V$ complete):

- *Fundamental theorem of calculus*: $\int_a^b c' = c(b) - c(a)$ ⟦Chapter7/Path · IsAdmissible.integral_deriv⟧, from Mathlib's version with countably many exceptional points ⟦Mathlib/MeasureTheory/Integral/DivergenceTheorem · integral_eq_of_hasDerivAt_off_countable_of_le⟧. Hence $\|c(b) - c(a)\| \le L(c|[a, b])$ ⟦Chapter7/Path · IsAdmissible.norm_sub_le_pathLength⟧.
- $L \ge 0$ ⟦Chapter7/Path · IsAdmissible.pathLength_nonneg⟧; $L(c|[a, m]) + L(c|[m, b]) = L(c|[a, b])$ for $m \in [a, b]$ ⟦Chapter7/Path · IsAdmissible.pathLength_add⟧; lengths of subintervals are smaller ⟦Chapter7/Path · IsAdmissible.pathLength_le⟧.
- A path of length $0$ is constant ⟦Chapter7/Path · IsAdmissible.eq_of_pathLength_eq_zero⟧ (by the chord bound on each $[a, t]$).
- $t \mapsto L(c|[a, t])$ is continuous ⟦Chapter7/Path · IsAdmissible.continuousOn_pathLength⟧ and nondecreasing ⟦Chapter7/Path · IsAdmissible.monotoneOn_pathLength⟧ on $[a, b]$.
- If $\|c'(t)\| = k$ wherever $c$ is differentiable in $(a, b)$, then $L(c|[a, b]) = k(b - a)$ ⟦Chapter7/Path · pathLength_eq_of_norm_deriv⟧: the integrand is $k$ off a countable, hence null, set ⟦Chapter7/Path · ae_uIoc_of_forall_Ioo_diff⟧.

**Operations (V7.11).** A path smooth on an open set containing $[a, b]$ is piecewise smooth with no break ⟦Chapter7/Path · IsPiecewiseSmooth.of_contDiffOn⟧; restriction to a subinterval ⟦Chapter7/Path · IsPiecewiseSmooth.mono⟧, concatenation of $c_1$ on $[a, m]$ and $c_2$ on $[m, b]$ with $c_1(m) = c_2(m)$ (break set $B_1 \cup B_2 \cup \{m\}$) ⟦Chapter7/Path · IsPiecewiseSmooth.concat⟧, reversal $t \mapsto c(a + b - t)$ ⟦Chapter7/Path · IsPiecewiseSmooth.reverse⟧ and translation of the parameter ⟦Chapter7/Path · IsPiecewiseSmooth.translate⟧ preserve piecewise smoothness. Under concatenation lengths add ⟦Chapter7/Path · pathLength_concat⟧ (the concatenation has the derivative of $c_1$ before $m$ and of $c_2$ after, and $\{m\}$ is null); under reversal and translation they are unchanged ⟦Chapter7/Path · pathLength_reverse⟧ ⟦Chapter7/Path · pathLength_translate⟧ (substitution in the integral).

**The length of a geodesic (V7.2).** If $\gamma$ is a geodesic on an open preconnected $s \supseteq [a, b]$ and $t_0 \in s$, then $L(\gamma|[a, b]) = \|\gamma'(t_0)\|\,(b - a)$ ⟦Chapter7/Shortest · IsGeodesicOn.pathLength_eq⟧: constant speed and the last bullet.

### VI.11 Lemma 10.6, and paths that leave a normal ball

Fix normal coordinates $(O, U, F, G)$ of radius $\varepsilon$ at $q$. Then $q \in U$ ⟦Chapter7/Shortest · NormalCoord.mem_U_self⟧, $G(q) = 0$ ⟦Chapter7/Shortest · NormalCoord.G_self⟧, and $G(y) \ne 0$ for $y \in N \cap U$, $y \ne q$ ⟦Chapter7/Shortest · NormalCoord.G_ne_zero⟧ (since $y = \exp_q(G y)$ and $\exp_q(0) = q$). In Milnor's notation a point $y \ne q$ of $U_q$ is $\exp_q(r v)$ with $r = \|G(y)\| \in (0, \varepsilon)$ and $v = G(y)/r$ a unit vector.

**Lemma 10.6, pointwise.** Let $c$ lie in $N$ near $t$, be differentiable at $t$, with $c(t) \in U$ and $c(t) \ne q$. Then the radius $\rho(s) = \|G(c(s))\|$ is differentiable at $t$ with $|\rho'(t)| \le \|c'(t)\|$; and if $\rho'(t) = \|c'(t)\|$, the direction $s \mapsto G(c(s))/\|G(c(s))\|$ has derivative $0$ at $t$ ⟦Chapter7/GaussLemma · NormalCoord.hasDerivAt_radius⟧.

*Proof.* Put $w = G(c(t))$, nonzero, and $w' = dG_{c(t)}(c'(t))$, the derivative of $s \mapsto G(c(s))$ at $t$; it lies in $T_qN$, because $G(c(s)) \in T_qN$ near $t$ (the third small lemma of §VI.1). Near $t$, $F(G(c(s))) = c(s)$, so $D_w(w') = c'(t)$. The radius has derivative $\rho'(t) = \langle w, w'\rangle/\|w\|$ ⟦Chapter7/GaussLemma · hasDerivAt_norm_of_ne⟧. By the Gauss lemma,
$$\langle D_w w,\ c'(t)\rangle = \langle D_w w,\ D_w w'\rangle = \langle w, w'\rangle, \qquad \|D_w w\|^2 = \langle w, w\rangle,$$
the second by the Gauss lemma with $x = w$. The Cauchy–Schwarz inequality ⟦Mathlib/Analysis/InnerProductSpace/Basic · abs_real_inner_le_norm⟧ gives $|\langle w, w'\rangle| \le \|w\|\,\|c'(t)\|$, that is $|\rho'(t)| \le \|c'(t)\|$. If $\rho'(t) = \|c'(t)\|$, then $\langle D_w w, c'(t)\rangle = \|D_w w\|\,\|c'(t)\|$, and equality in Cauchy–Schwarz ⟦Mathlib/Analysis/InnerProductSpace/Basic · inner_eq_norm_mul_iff_real⟧ makes $c'(t) = l\,D_w w$ with $l = \|c'(t)\|/\|w\|$. Then $D_w(w' - lw) = 0$, and injectivity of $D_w$ on $T_qN$ (§VI.9) gives $w' = lw$. The derivative of $G(c)/\|G(c)\|$ at $t$ is
$$\frac{w'}{\|w\|} - \frac{\langle w, w'\rangle}{\|w\|^3}\,w = \frac{l\,w}{\|w\|} - \frac{l\,\|w\|^2}{\|w\|^3}\,w = 0. \qquad \square$$

Milnor (p. 61) splits $\frac{d\omega}{dt}$ into orthogonal radial and spherical parts. The formal proof never splits: the stronger Gauss lemma and Cauchy–Schwarz do the work. Milnor's step from $\partial f/\partial t = 0$ to $dv/dt = 0$ needs $d(\exp_q)$ injective and $r > 0$; both appear above.

**Lemma 10.6 (V7.13).** Let $c$ be admissible on $[a, b]$ with $c(t) \in N \cap U$ and $c(t) \ne q$ for $t \in [a, b]$. Then
$$L(c|[a, b]) \ \ge\ \|G(c(b))\| - \|G(c(a))\|$$
⟦Chapter7/Shortest · NormalCoord.radius_sub_le_pathLength⟧; and if equality holds, the direction $G(c(t))/\|G(c(t))\|$ is constant on $[a, b]$ ⟦Chapter7/Shortest · NormalCoord.direction_eq_of_pathLength_eq⟧.

*Proof of the inequality.* The radius $\rho$ is continuous on $[a, b]$, and off the countable exceptional set of $c$ it is differentiable with $|\rho'| \le \|c'\|$ by the pointwise lemma. So $\rho'$ is integrable (dominated by $\|c'\|$), the fundamental theorem of calculus off a countable set gives $\int_a^b \rho' = \rho(b) - \rho(a)$, and $\rho' \le |\rho'| \le \|c'\|$ almost everywhere gives $\int_a^b \rho' \le L(c|[a, b])$. $\square$

*Proof of the equality clause.* With equality, $\int_a^b(\|c'\| - \rho') = 0$ with a nonnegative integrand, so $\|c'\| = \rho'$ almost everywhere ⟦Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic · integral_eq_zero_iff_of_le_of_nonneg_ae⟧. At those points (off the countable set) the pointwise lemma gives that the direction $u = G(c)/\|G(c)\|$ has derivative $0$. So $u' = 0$ almost everywhere; $u$ is continuous and differentiable off a countable set, and the fundamental theorem of calculus on $[t, b]$ gives $u(b) - u(t) = \int_t^b u' = 0$. $\square$

The formal Lemma 10.6 is one-sided ($r(b) - r(a)$ rather than $|r(b) - r(a)|$), the case Theorem 10.4 uses; the monotone parametrization of the equality case is obtained in §VI.12.

**Normal balls.** For $0 < s$, the *open normal ball* of radius $s$ is cut out of $N$ by the open set
$$\mathrm{ball}_s = U \cap G^{-1}(B(0, s))$$
⟦Chapter7/Shortest · NormalCoord.ballSet⟧ ⟦Chapter7/Shortest · NormalCoord.isOpen_ballSet⟧ ⟦Chapter7/Shortest · NormalCoord.mem_ballSet⟧, and the *closed normal ball* is $\overline{\mathrm{ball}}_s = F\big(\bar B(0, s) \cap T_qN\big)$ ⟦Chapter7/Shortest · NormalCoord.closedBallSet⟧. For $s < \varepsilon$ the closed normal ball is compact, as the continuous image of a compact set ⟦Chapter7/Shortest · NormalCoord.isCompact_closedBallSet⟧, hence closed in $V$; and it consists of the points $y \in N \cap U$ with $\|G(y)\| \le s$ ⟦Chapter7/Shortest · NormalCoord.mem_closedBallSet⟧.

**Lemma (paths leaving a normal ball, V7.14).** Let $c$ be admissible on $[a, b]$ with $c([a, b]) \subseteq N$, $c(a) = q$, $0 < s < \varepsilon$, and $c(b) \notin \mathrm{ball}_s$. There are $a \le t_1 < t_2 \le b$ such that $c(t_1) = q$; $c(t) \in U \setminus \{q\}$ for $t_1 < t \le t_2$; $\|G(c(t))\| < s$ for $t_1 \le t < t_2$; $\|G(c(t_2))\| = s$; and $L(c|[t_1, t_2]) \ge s$ ⟦Chapter7/Shortest · NormalCoord.exists_crossing⟧.

Here $t_2$ is the first exit from the open normal ball and $t_1$ the last visit of $q$ before it. After $t_2$ the path may leave $U_q$ altogether, and that is exactly the case Milnor's proof does not discuss.

*Proof.*

1. *The first exit.* The set $S_2$ of $t \in [a, b]$ with $c(t) \notin \mathrm{ball}_s$ is closed (the preimage of a closed set under a map continuous on a closed interval) and contains $b$; let $t_2$ be its infimum, which belongs to it. Since $c(a) = q \in \mathrm{ball}_s$, $a < t_2$, and $c(t) \in \mathrm{ball}_s$ for $a \le t < t_2$.
2. *The exit point is on the sphere.* For $a \le t < t_2$, $c(t)$ is in $N$ and in $\mathrm{ball}_s$, hence in the closed normal ball. That ball is closed in $V$, and $c(t_2)$ is the limit of $c(t)$ as $t \uparrow t_2$, so $c(t_2)$ lies in it: $c(t_2) \in U$ and $\|G(c(t_2))\| \le s$. As $t_2 \in S_2$, $c(t_2) \notin \mathrm{ball}_s$, so $\|G(c(t_2))\| = s$; in particular $c(t_2) \ne q$. This is where compactness of closed normal balls, and Hausdorffness, enter.
3. *The last visit of $q$.* The set $S_1$ of $t \in [a, t_2]$ with $c(t) = q$ is closed and contains $a$; let $t_1$ be its supremum, which belongs to it, and $t_1 < t_2$ since $c(t_2) \ne q$. For $t_1 < t \le t_2$, $c(t) \ne q$, and $c(t) \in U$ (from step 1, or step 2 at $t = t_2$).
4. *The length.* Let $\eta > 0$. The radius $\|G(c(t))\|$ is continuous at $t_1$ from the right, with value $\|G(q)\| = 0$, so there is $t' \in (t_1, t_2)$ with $\|G(c(t'))\| < \eta$. On $[t', t_2]$ the path avoids $q$ and stays in $N \cap U$, so Lemma 10.6 gives $L(c|[t', t_2]) \ge s - \|G(c(t'))\| > s - \eta$, and $L(c|[t_1, t_2]) \ge L(c|[t', t_2])$. As $\eta$ was arbitrary, $L(c|[t_1, t_2]) \ge s$. $\square$

Milnor (p. 61) argues that for every $\delta > 0$ the path contains a segment joining the shells of radii $\delta$ and $r$ and lying between them, of length $\ge r - \delta$, and lets $\delta \to 0$. The formal proof replaces the shells of radius $\delta$ by the last visit of $q$ and takes the limit inside the argument. The verified edition calls this lemma Lemma C.

### VI.12 Theorem 10.4, with the sharp equality case

**Lemma (the radial geodesic).** If $\varepsilon$ is a normal radius at $q$ and $v \in B_\varepsilon(q)$, then $t \mapsto \exp_q(tv)$ is a geodesic on some $(-\delta, 1 + \delta)$ with velocity $v$ at $0$ ⟦Chapter7/Shortest · NormalCoord.radial⟧, and its length on $[0, 1]$ is $\|v\|$ ⟦Chapter7/Shortest · NormalCoord.pathLength_exp_smul⟧ (constant speed $\|v\|$, §VI.10).

**Theorem 10.4, inequality (V7.15).** Let $\varepsilon$ be a normal radius at $q$, $v \in T_qN$ with $\|v\| < \varepsilon$, and $c$ an admissible path in $N$, on any $[a, b]$, from $q$ to $\exp_q(v)$. Then $L(c|[a, b]) \ge \|v\|$ ⟦Chapter7/Shortest · NormalCoord.norm_le_pathLength⟧, whether or not $c$ stays in $U_q$.

*Proof.* For $v = 0$ there is nothing to prove. Otherwise $s = \|v\|$ satisfies $0 < s < \varepsilon$, and $c(b) = \exp_q(v)$ has $\|G(c(b))\| = \|v\| = s$, so $c(b) \notin \mathrm{ball}_s$. The lemma of §VI.11 gives $t_1 < t_2$ with $L(c|[a, b]) \ge L(c|[t_1, t_2]) \ge s$. $\square$

**Theorem 10.4, equality, sharp form (V7.16).** In the same situation, suppose $v \ne 0$ and $L(c|[a, b]) = \|v\|$. Then
$$c(t) = \exp_q\big(\rho(t)\,v\big), \qquad \rho(t) = \frac{L(c|[a, t])}{\|v\|} \qquad (a \le t \le b)$$
⟦Chapter7/Shortest · NormalCoord.eq_exp_of_pathLength_eq⟧, where $\rho$ is continuous and nondecreasing with $\rho(a) = 0$ and $\rho(b) = 1$ (§VI.10). So $c = \gamma \circ \rho$ is a monotone reparametrization of the geodesic $\gamma(t) = \exp_q(tv)$, $0 \le t \le 1$.

*Proof.* Let $s = \|v\|$ and take $t_1 < t_2$ from the crossing lemma.

1. *Splitting the length.* $L(c|[a, t_1]) + L(c|[t_1, t_2]) + L(c|[t_2, b]) = s$, the middle term is $\ge s$ and the others are $\ge 0$. So $L(c|[a, t_1]) = 0 = L(c|[t_2, b])$ and $L(c|[t_1, t_2]) = s$. Paths of length $0$ are constant: $c = q$ on $[a, t_1]$ and $c = c(b) = \exp_q(v)$ on $[t_2, b]$, so $G(c(t_2)) = v$.
2. *The middle.* Let $t_1 < t \le t_2$. The point $c(t)$ is $\exp_q(G(c(t)))$ with $G(c(t)) \in B_\varepsilon(q)$, so the inequality on $[t_1, t]$ gives $L(c|[t_1, t]) \ge \|G(c(t))\|$, and Lemma 10.6 on $[t, t_2]$ (where $c$ avoids $q$ and stays in $U$) gives $L(c|[t, t_2]) \ge s - \|G(c(t))\|$. The two lengths add up to $s$, so both inequalities are equalities: $L(c|[t_1, t]) = \|G(c(t))\|$, and Lemma 10.6 holds with equality on $[t, t_2]$. Its equality clause gives $G(c(t))/\|G(c(t))\| = v/s$, hence $G(c(t)) = (\|G(c(t))\|/s)\,v$ and $c(t) = \exp_q\big((L(c|[t_1, t])/s)\,v\big)$.
3. *All $t$.* For $t \le t_1$: $L(c|[a, t]) = 0$ and $c(t) = q = \exp_q(0)$. For $t_1 < t \le t_2$: $L(c|[a, t]) = L(c|[t_1, t])$ because the length on $[a, t_1]$ is $0$, and step 2 applies. For $t > t_2$: $L(c|[a, t]) = s$, so $\rho(t) = 1$, and $c(t) = \exp_q(v)$. $\square$

Milnor's equality clause (p. 59) is that the point sets coincide; he says a strict inequality is easily obtained when they differ (p. 61). The sharp form implies it: $c([a, b]) = \gamma([0, 1])$ ⟦Chapter7/Shortest · NormalCoord.image_eq_of_pathLength_eq⟧, because $\rho$ maps $[a, b]$ into $[0, 1]$ by monotonicity and onto it by the intermediate value theorem. Equal images are, however, too weak for Corollary 10.7: a path that runs along $\gamma$ at variable speed, or backwards and forwards, has the same image without being a geodesic.

**Theorem 10.4 (V7.15).** For each $p \in N$ there are an open set $O \ni p$ of $V$ and an $\varepsilon > 0$ such that for any $q_1, q_2 \in N \cap O$ there is $v \in T_{q_1}N$ with $\|v\| < \varepsilon$ and $\exp_{q_1}(v) = q_2$, the geodesic $\gamma(t) = \exp_{q_1}(tv)$, $0 \le t \le 1$, has length $\|v\|$, and every piecewise smooth path $c$ in $N$, on any $[a, b]$, from $q_1$ to $q_2$ satisfies $L(c|[a, b]) \ge \|v\|$, with equality only if $c([a, b]) = \gamma([0, 1])$ ⟦Chapter7/Shortest · theorem_10_4⟧.

*Proof.* Take $O$ and $\varepsilon$ from Lemma 10.3, $v$ from its item (1), and normal coordinates at $q_1$ from its item (3). The length of $\gamma$ is $\|v\|$ by the radial lemma; piecewise smooth paths are admissible, so the inequality is the one above. For equality: if $v = 0$, then $q_1 = q_2$, the path has length $0$ and is constant at $q_1 = \gamma(t)$; otherwise apply the sharp form and its corollary on images. $\square$

The formal statement is stronger than Milnor's in allowing any parameter interval and, in the two lemmas behind it, admissible paths. Milnor's proof needs the crossing lemma (V7.14), which his text does not supply.

### VI.13 Corollary 10.7: shortest paths are geodesics

**Lemma (the segment lemma).** Let $c$ be piecewise smooth on $[0, \ell]$ with $c([0, \ell]) \subseteq N$, parametrized by arc length ($\|c'(t)\| = 1$ wherever $c$ is differentiable in $(0, \ell)$), and *minimal*: $L(c|[0, \ell]) \le L(\tilde c|[a, b])$ for every piecewise smooth path $\tilde c$ in $N$, on any $[a, b]$, from $c(0)$ to $c(\ell)$. Let $O$, $\varepsilon$ satisfy items (1) and (3) of Lemma 10.3, and let $0 \le \alpha < \beta \le \ell$ with $c([\alpha, \beta]) \subseteq O$. Then $c$ agrees on $[\alpha, \beta]$ with a geodesic defined on an open set containing $[\alpha, \beta]$, namely $t \mapsto \exp_{c(\alpha)}\big(\frac{t - \alpha}{\beta - \alpha}v\big)$ for the vector $v$ of item (1) joining $c(\alpha)$ to $c(\beta)$ ⟦Chapter7/Minimal · minimal_segment⟧.

*Proof.*

1. *Arc length.* For $0 \le s \le t \le \ell$, $L(c|[s, t]) = t - s$, by the constant-speed formula of §VI.10.
2. *The geodesic segment.* Let $q_1 = c(\alpha)$, $q_2 = c(\beta)$, $v$ the vector of item (1) and normal coordinates of radius $\varepsilon$ at $q_1$ (item (3)). The radial geodesic $t \mapsto \exp_{q_1}(tv)$ lives on some $(-\delta, 1 + \delta)$, so by homogeneity $\tilde\gamma(t) = \exp_{q_1}(k(t - \alpha)v)$, $k = (\beta - \alpha)^{-1}$, is a geodesic on the preimage of $(-\delta, 1 + \delta)$ under $t \mapsto k(t - \alpha)$, an open interval containing $[\alpha, \beta]$. It runs from $\tilde\gamma(\alpha) = q_1$ to $\tilde\gamma(\beta) = \exp_{q_1}(v) = q_2$, lies in $N$ on $[\alpha, \beta]$, and has speed $k\|v\|$, hence length $\|v\|$ on $[\alpha, \beta]$.
3. *The competitor.* Let $c_2$ be $c$ on $[0, \alpha]$, $\tilde\gamma$ on $[\alpha, \beta]$ and $c$ on $[\beta, \ell]$. It is piecewise smooth (two concatenations), lies in $N$, joins $c(0)$ to $c(\ell)$, and has length $L(c|[0, \alpha]) + \|v\| + L(c|[\beta, \ell])$.
4. *Equality.* Minimality of $c$ against $c_2$ and additivity of length give $L(c|[\alpha, \beta]) \le \|v\|$; Theorem 10.4's inequality, applied to $c|[\alpha, \beta]$, gives the reverse. So $L(c|[\alpha, \beta]) = \|v\| = \beta - \alpha > 0$, and $v \ne 0$.
5. *Identification.* The sharp equality case gives, for $t \in [\alpha, \beta]$, $c(t) = \exp_{q_1}\big(\frac{L(c|[\alpha, t])}{\|v\|}v\big) = \exp_{q_1}\big(\frac{t - \alpha}{\beta - \alpha}v\big) = \tilde\gamma(t)$, by arc length. $\square$

The arc-length hypothesis is what turns the monotone reparametrization of the sharp equality case into an affine one.

**Corollary 10.7 (V7.17).** Let $c$ be a piecewise smooth path in $N$ on $[0, \ell]$, parametrized by arc length, whose length is at most that of every piecewise smooth path in $N$, on any parameter interval, from $c(0)$ to $c(\ell)$. Then $c$ is a geodesic on $(0, \ell)$ ⟦Chapter7/Minimal · corollary_10_7⟧; in particular it is smooth there, also at its break points. Moreover $c$ agrees on $[0, \ell]$ with a geodesic defined on an open interval $(-\delta, \ell + \delta)$ ⟦Chapter7/Minimal · corollary_10_7_extend⟧.

*Proof.* Let $t_0 \in (0, \ell)$. Take $O$, $\varepsilon$ from Lemma 10.3 at $c(t_0)$. By continuity of $c$ at $t_0$ there is $\eta > 0$, also at most $t_0/2$ and $(\ell - t_0)/2$, with $c([t_0 - \eta, t_0 + \eta]) \subseteq O$. The segment lemma on $[t_0 - \eta, t_0 + \eta]$ gives a geodesic equal to $c$ there; so $c$ is a geodesic on $(t_0 - \eta, t_0 + \eta)$. Being a geodesic is local (§VI.2), so $c$ is a geodesic on $(0, \ell)$.

For the extension, the case $\ell = 0$ is a constant geodesic. Otherwise the segment lemma at the endpoints, on $[0, \eta_0]$ and on $[\ell - \eta_1, \ell]$ (with $\eta_0, \eta_1$ chosen as above from Lemma 10.3 at $c(0)$ and $c(\ell)$, using continuity within $[0, \ell]$), gives geodesics $\gamma_0$, $\gamma_1$ on open sets containing these intervals, equal to $c$ there. Choose $\delta > 0$ so that $(-\delta, 0]$ lies in the domain of $\gamma_0$ and $[\ell, \ell + \delta)$ in that of $\gamma_1$, and let $g$ be $\gamma_0$ before $0$, $c$ on $[0, \ell]$ and $\gamma_1$ after $\ell$. Near any $t \in (-\delta, \ell + \delta)$, $g$ coincides with $\gamma_0$ (if $t < \eta_0$), with $c$ (if $\eta_0 \le t \le \ell - \eta_1$, inside $(0, \ell)$) or with $\gamma_1$ (if $t > \ell - \eta_1$), each a geodesic there, so $g$ is a geodesic on $(-\delta, \ell + \delta)$ by locality. $\square$

*What Milnor leaves implicit* (p. 61). Applying Theorem 10.4 to short segments needs three more things: the sharp equality case, since equal images do not make a segment a geodesic; the minimality of each segment, from the competitor of step 3; and segments with the points of $(0, \ell)$, break points included, in their interiors.

### VI.14 The distance $\rho$

Milnor (p. 62) says that the infimum of lengths "clearly" makes $M$ a metric space, compatible with its topology by Theorem 10.4. Finiteness needs connectedness, positivity needs the crossing lemma, and the topology needs small metric balls to be normal balls; Theorem 10.9 also uses the continuity of $\rho$, which the book never states.

**Definition (V7.18; §0.3).** For $p, q \in V$, let $\Lambda(p, q)$ be the set of lengths $L(c|[a, b])$, as elements of $[0, \infty]$, of the piecewise smooth paths $c$ in $N$, on any $[a, b]$, with $c(a) = p$ and $c(b) = q$ ⟦Chapter7/Distance · pathLengths⟧, and
$$\rho(p, q) = \inf \Lambda(p, q) \in [0, \infty]$$
⟦Chapter7/Distance · riemDist⟧, which is $\infty$ when no path joins $p$ to $q$, for instance when $q \notin N$ ⟦Chapter7/Distance · riemDist_eq_top_of_notMem⟧ or $q$ lies in another component of $N$.

**The axioms of an extended metric (V7.18).**

- $\rho(c(a), c(b)) \le L(c|[a, b])$ for every piecewise smooth path in $N$ ⟦Chapter7/Distance · riemDist_le_pathLength⟧.
- $\rho(p, p) = 0$ for $p \in N$ ⟦Chapter7/Distance · riemDist_self⟧: the constant path on $[0, 0]$ has length $0$.
- *Symmetry* ⟦Chapter7/Distance · riemDist_comm⟧: reversal $t \mapsto c(a + b - t)$ turns a path from $p$ to $q$ into one from $q$ to $p$ of the same length, so $\Lambda(p, q) \subseteq \Lambda(q, p)$ ⟦Chapter7/Distance · pathLengths_comm⟧, and by symmetry the two sets are equal.
- *The triangle inequality* ⟦Chapter7/Distance · riemDist_triangle⟧. Given $c_1$ from $p$ to $q$ on $[a_1, b_1]$ and $c_2$ from $q$ to $r$ on $[a_2, b_2]$, translate the parameter of $c_2$ by $d = a_2 - b_1$ so that it starts at time $b_1$, and concatenate. The result is a piecewise smooth path in $N$ from $p$ to $r$ of length $L(c_1) + L(c_2)$ (§VI.10). So $\rho(p, r) \le L(c_1) + L(c_2)$ for all such pairs, and taking infima gives $\rho(p, r) \le \rho(p, q) + \rho(q, r)$; if either set of lengths is empty the right side is $\infty$.

**Normal balls are metric balls (V7.18, V7.19).** Let $\varepsilon$ be a normal radius at $p$, with normal coordinates $(O, U, F, G)$.

- *A lower bound.* If $0 < s < \varepsilon$ and $y \notin \mathrm{ball}_s$, then $\rho(p, y) \ge s$ ⟦Chapter7/Distance · NormalCoord.ofReal_le_riemDist⟧: every piecewise smooth path from $p$ to $y$ is admissible, and the crossing lemma (§VI.11) gives a segment of length $\ge s$.
- *The radial distance.* For $v \in B_\varepsilon(p)$, $\rho(p, \exp_p v) = \|v\|$ ⟦Chapter7/Distance · NormalCoord.riemDist_exp⟧. The radial geodesic on $[0, 1]$ is a piecewise smooth path in $N$ of length $\|v\|$, which gives $\le$ ⟦Chapter7/Distance · NormalCoord.riemDist_exp_le⟧; for $v \ne 0$, $\exp_p v \notin \mathrm{ball}_{\|v\|}$ because $G(\exp_p v) = v$, and the lower bound gives $\ge$.
- *Small metric balls.* For $0 < r \le \varepsilon$, $\rho(p, y) < r$ if and only if $y \in N \cap \mathrm{ball}_r$ ⟦Chapter7/Distance · NormalCoord.riemDist_lt_iff⟧. If $\rho(p, y) < r$, then $y \in N$ (else $\rho = \infty$); and if $y$ were outside $\mathrm{ball}_r$, choosing $s$ with $\rho(p, y) < s < r$ would put $y$ outside $\mathrm{ball}_s$ and give $\rho(p, y) \ge s$. Conversely, $y \in N \cap \mathrm{ball}_r$ is $\exp_p(G y)$ with $\|G y\| < r$, at distance at most $\|G y\|$.

**Positivity (V7.18).** For $p, q \in N$, $\rho(p, q) = 0$ implies $p = q$ ⟦Chapter7/Distance · eq_of_riemDist_eq_zero⟧. *Proof.* Suppose $q \ne p$, and take a normal radius $\varepsilon$ at $p$. There is $s$ with $0 < s < \varepsilon$ and $q \notin \mathrm{ball}_s$: if $q \in U$, then $G(q) \ne 0$ and $s = \min(\|G(q)\|, \varepsilon/2)$ works; otherwise $s = \varepsilon/2$. Then $\rho(p, q) \ge s > 0$. $\square$

**The topology (V7.19).** For every $p \in N$, the metric balls $\{y : \rho(p, y) < r\}$, $r > 0$, form a basis of the neighbourhoods of $p$ in $N$, for the topology of $N$ as a subspace of $V$ ⟦Chapter7/Distance · hasBasis_nhdsWithin_riemDist⟧.

*Proof.* Take a normal radius $\varepsilon$ at $p$. A neighbourhood of $p$ in $N$ contains $N \cap O'$ for an open $O' \ni p$. $F$ is continuous at $0$ with $F(0) = p$, so $F(B(0, r_0)) \subseteq O'$ for some $r_0 > 0$; with $r = \min(r_0, \varepsilon)$, the metric ball of radius $r$ is $N \cap \mathrm{ball}_r$, whose points are $F(G y)$ with $\|G y\| < r$, so it lies in $O'$. Conversely a metric ball of radius $r$ contains $N \cap \mathrm{ball}_{\min(r, \varepsilon)}$, the trace on $N$ of an open set containing $p$. $\square$

Milnor's "follows easily from 10.4" is these two facts: small metric balls are normal balls, and small normal balls lie in any given neighbourhood of $p$. Consequently, for $p \in N$ and every $r > 0$, all points of $N$ near $p$ are at distance $< r$ from $p$ ⟦Chapter7/Metric · eventually_riemDist_lt⟧.

**$\rho$ dominates the distance of $V$ (V7.21).** $\|q - p\| \le \rho(p, q)$ for all $p, q \in V$ ⟦Chapter7/Metric · ofReal_norm_sub_le_riemDist⟧: a path is at least as long as its chord (§VI.10).

**Continuity of $\rho$ (V7.21).** The function $(x, y) \mapsto \rho(x, y) \in [0, \infty]$ is continuous on $N \times N$ ⟦Chapter7/Metric · continuousOn_riemDist⟧, in particular $y \mapsto \rho(y, q)$ is continuous on $N$ for every $q$ ⟦Chapter7/Metric · continuousOn_riemDist_left⟧ (constant $\infty$ if $q \notin N$), and $\rho$ is continuous on the product space $N \times N$ ⟦Chapter7/Metric · continuous_riemDist⟧.

*Proof.* Fix $(x, y) \in N \times N$. By the neighbourhood-basis property, for every $r > 0$ the pairs $(z_1, z_2) \in N \times N$ near $(x, y)$ have $\rho(x, z_1) < r/2$ and $\rho(y, z_2) < r/2$. For such pairs the triangle inequality gives
$$\rho(z_1, z_2) \le \rho(x, y) + r \qquad\text{and}\qquad \rho(x, y) \le \rho(z_1, z_2) + r.$$
If $\rho(x, y) < b$, choose $r$ with $\rho(x, y) + r < b$: the first inequality gives $\rho(z_1, z_2) < b$ near $(x, y)$. If $a < \rho(x, y)$, choose $r$ with $a + r < \rho(x, y)$: the second inequality excludes $\rho(z_1, z_2) \le a$ near $(x, y)$. This is continuity in the order topology of $[0, \infty]$. $\square$

**Finiteness (V7.21).** If $N$ is preconnected, $\rho(p, q) < \infty$ for all $p, q \in N$ ⟦Chapter7/Metric · riemDist_ne_top⟧. *Proof.* Let $T$ be the set of $y \in N$ at finite distance from $p$. Points near $y$ are at distance $< 1$ from $y$; so if $y \in T$ they are in $T$, and if $y \notin T$ they are not in $T$ (else $\rho(p, y) \le \rho(p, y') + \rho(y', y) < \infty$). So $T$ is open and closed in $N$, it contains $p$, and $N$ is preconnected. $\square$

This is what Milnor's standing assumption that $M$ is connected (p. 55) is for. "Connected" is preconnected in the formal statements, which also admits $N = \emptyset$.

**The metric spaces $(N, \rho)$ (V7.21).** $\rho$ restricted to $N$ satisfies the axioms of an extended metric ⟦Chapter7/Metric · riemEMetricSpace₀⟧, and the topology it defines is the topology of $N$ as a subspace of $V$ ⟦Chapter7/Metric · topology_eq_riemEMetricSpace₀⟧, by the neighbourhood-basis property. Replacing the topology of the metric structure by the (equal) subspace topology ⟦Mathlib/Topology/EMetricSpace/Defs · EMetricSpace.replaceTopology⟧ gives an extended metric space whose topology is the topology of $N$ by definition ⟦Chapter7/Metric · riemEMetricSpace⟧. For preconnected $N$, where $\rho$ is finite, it becomes a metric space with distance $\rho$ ⟦Chapter7/Metric · riemMetricSpace⟧ ⟦Chapter7/Metric · riemMetricSpace_dist⟧ ⟦Chapter7/Metric · riemMetricSpace_edist⟧, again with the topology of $N$ by definition ⟦Chapter7/Metric · riemMetricSpace_topology⟧. They are not instances, since $N$, a subset of $V$, already carries the metric of $V$.

### VI.15 Corollary 10.8

Milnor's Corollary 10.8 (p. 62): for compact $K$ there is $\delta > 0$ such that two points of $K$ at distance $< \delta$ are joined by a unique geodesic of length $< \delta$, which is minimal and depends differentiably on its endpoints. His proof covers $K$ by sets $W$ of Lemma 10.3 and takes $\delta$ so small that two points of $K$ at distance $< \delta$ lie in a common $W$.

**Definition.** For $\delta > 0$ and $y, z \in N$, say $y$ and $z$ are *$\delta$-joined* ⟦Chapter7/Distance · IsShortJoin⟧ if there is $v \in T_yN$ with $\|v\| < \delta$ and $\exp_y(v) = z$, such that: $\rho(y, z) = \|v\|$ (the geodesic $t \mapsto \exp_y(tv)$, $0 \le t \le 1$, of length $\|v\|$, is minimal); every $w \in T_yN$ with $\|w\| < \delta$ and $\exp_y(w) = z$ equals $v$; and there are an open $O_2 \ni (y, z)$ of $V \times V$ and a map $G$, smooth on $O_2$, with $G(y, z) = v$ and, for all $y', z' \in N$ with $(y', z') \in O_2$ and $\rho(y', z') < \delta$, $G(y', z') \in T_{y'}N$, $\|G(y', z')\| < \delta$ and $\exp_{y'}(G(y', z')) = z'$.

Uniqueness is stated for initial vectors, which covers geodesics as after Lemma 10.3; "depends differentiably" becomes the smooth $G$.

**Lemma (Lemma 10.3 read with the distance).** Around each $p \in N$ there are $s > 0$ and an open $\Omega \ni p$ of $V$ such that points of $N \cap \Omega$ are at distance $< s$ from $p$, and for every $0 < \delta \le s$, every $y \in N \cap \Omega$ and every $z \in N$ with $\rho(y, z) < \delta$, $y$ and $z$ are $\delta$-joined ⟦Chapter7/Distance · exists_isShortJoin⟧.

*Proof.*

1. Take $O$, $\varepsilon$ and items (1)–(3) from Lemma 10.3 at $p$, and $r > 0$ with the metric ball of radius $r$ about $p$ inside $O$ (§VI.14). Let $s = \min(r, \varepsilon)/2$ and $\Omega = \mathrm{ball}_s$ for normal coordinates of radius $\varepsilon$ at $p$; so $N \cap \Omega$ is the metric ball of radius $s$, and $2s \le r$, $s \le \varepsilon$.
2. *Both points lie in $O$.* $\rho(p, y) < s$, and $\rho(p, z) \le \rho(p, y) + \rho(y, z) < s + \delta \le 2s \le r$.
3. *The vector.* Item (1) gives the unique $v \in T_yN$ with $\|v\| < \varepsilon$ and $\exp_y(v) = z$. As $\varepsilon$ is a normal radius at $y$ (item (3)), $\rho(y, z) = \|v\|$ (§VI.14); so $\|v\| < \delta$.
4. *Uniqueness* among vectors of norm $< \delta \le \varepsilon$ is item (1).
5. *Smooth dependence.* Item (2) gives $O_2'$ and $G$; take $O_2 = O_2' \cap (O \times O)$. $G(y, z) = v$ by item (1). For $(y', z') \in O_2$ with $y', z' \in N$ and $\rho(y', z') < \delta$: $G(y', z')$ is the vector of item (1) for $(y', z')$, and $\|G(y', z')\| = \rho(y', z') < \delta$ by step 3 at $y'$. $\square$

**Corollary 10.8 (V7.20).** Let $K \subseteq N$ be compact. There is $\delta > 0$ such that any $y, z \in K$ with $\rho(y, z) < \delta$ are $\delta$-joined ⟦Chapter7/Distance · corollary_10_8⟧.

*Proof.* If $K$ is empty there is nothing to prove. Otherwise apply the lemma at each $x \in K$, obtaining $s_x$ and $\Omega_x$; finitely many $\Omega_{x_1}, \dots, \Omega_{x_k}$ cover $K$ ⟦Mathlib/Topology/Compactness/Compact · IsCompact.elim_finite_subcover⟧. Let $\delta = \min_i s_{x_i} > 0$. A point $y \in K$ lies in some $\Omega_{x_i}$, and $\delta \le s_{x_i}$, so the lemma applies to $y$ and any $z$ with $\rho(y, z) < \delta$. $\square$

Milnor's choice of $\delta$ is this Lebesgue-number argument; uniqueness "of length $< \delta$" needs $\delta \le \varepsilon$ for each set of the cover, and minimality is Theorem 10.4 through $\rho(y, z) = \|v\|$. Only $y$ needs to lie in $K$.

### VI.16 The geodesic flow, and the continuity of $\exp$ on its domain

Corollary 10.10 needs $\exp_p$ continuous on a large disk of $T_pM$, about which Lemma 10.2 says nothing. The formal proof obtains it by continuing geodesics (the verified edition's Lemma B, in a continuous form).

**The geodesic flow.** By §VI.6 every geodesic is a radial curve $t \mapsto \exp_y(tw)$. The geodesic flow is therefore read off from $\exp$:
$$\Psi_t(y, w) = \Big(\exp_y(tw),\ \tfrac{d}{dt}\exp_y(tw)\Big)$$
⟦Chapter7/GeodesicFlow · geoFlow⟧, the position and velocity at time $t$ of $s \mapsto \exp_y(sw)$; where the geodesic with initial data $(y, w)$ exists, this is its position and velocity at time $t$.

**Proposition (the local flow, uniformly).** For $x_0 \in N$ and $R > 0$ there are an open set $U \ni x_0$ of $V$, a time $\tau > 0$ and a map $\Phi$, continuous on $U \times B(0, R) \times (-\tau, \tau)$, such that for every $y \in N \cap U$ and $w \in T_yN$ with $\|w\| < R$: $t \mapsto \exp_y(tw)$ is a geodesic on $(-\tau, \tau)$ with velocity $w$ at $0$, and $\Psi_t(y, w) = \Phi(y, w, t)$ for $|t| < \tau$ ⟦Chapter7/GeodesicFlow · exists_localFlow_exp⟧.

*Proof.* Take $U$, $\varepsilon$, $\Theta$ from Lemma 10.2 at $x_0$ and rescale by homogeneity. Let $a = \varepsilon/(2R)$, so $a\|w\| < \varepsilon$ for $\|w\| < R$, and $\tau = 2a$. The map $\iota(y, w, t) = (y, aw, t/a)$ sends $U \times B(0, R) \times (-2a, 2a)$ into $U \times B(0, \varepsilon) \times (-2, 2)$, where $\Theta$ is smooth. Put
$$\Phi(y, w, t) = \Big(\Theta(\iota(y, w, t)),\ a^{-1}\,\partial_t\Theta(\iota(y, w, t))\Big),$$
continuous since $\Theta$ and its derivative are. For $y \in N \cap U$ and tangent $w$ with $\|w\| < R$, the curve $\eta(t) = \Theta(y, aw, t/a)$ is a geodesic on $(-2a, 2a)$ by homogeneity, with $\eta(0) = y$ and $\eta'(t) = a^{-1}\partial_t\Theta(\iota(y, w, t))$ by the chain rule, so $\eta'(0) = a^{-1}(aw) = w$. Every geodesic is radial, so $\exp_y(tw) = \eta(t)$ on $(-2a, 2a)$, and its position and velocity at $t$ are $\Phi(y, w, t)$. $\square$

In particular, for $y \in N$ and $w \in T_yN$, $t \mapsto \exp_y(tw)$ is a geodesic on some $(-\tau, \tau)$ with velocity $w$ at $0$ ⟦Chapter7/GeodesicFlow · exists_isGeodesicOn_exp_smul⟧ ⟦Chapter7/GeodesicFlow · hasDerivAt_exp_smul_zero⟧ (take $R = \|w\| + 1$), and $\Psi_0$ is the identity on $TN$ ⟦Chapter7/GeodesicFlow · geoFlow_zero⟧.

**Proposition (continuing a geodesic).** Suppose $t \mapsto \exp_y(tw)$ is a geodesic on an open interval $I \ni 0$, let $s \in I$ and $(y', w') = \Psi_s(y, w)$. If $t \mapsto \exp_{y'}(tw')$ is a geodesic on an open interval $J \ni 0$, then $t \mapsto \exp_y(tw)$ is a geodesic on $I \cup (s + J)$, and $\Psi_{s + t}(y, w) = \Psi_t(y', w')$ for $t \in J$ ⟦Chapter7/GeodesicFlow · isGeodesicOn_exp_smul_union⟧.

*Proof.* Let $\gamma_1(t) = \exp_y(tw)$ and $\gamma_2(t) = \exp_{y'}((t - s)w')$, a geodesic on $s + J$ by homogeneity. At time $s$ both have position $y'$ and velocity $w'$. On the open interval $I \cap (s + J)$ (an intersection of intervals), uniqueness of geodesics gives $\gamma_1 = \gamma_2$. The curve $g$ equal to $\gamma_1$ on $I$ and to $\gamma_2$ elsewhere is then a geodesic on $I \cup (s + J)$ by locality, with $g(0) = y$ and $g'(0) = w$. The union is an interval (two intervals sharing the point $s$) ⟦Mathlib/Topology/Connected/Basic · IsPreconnected.union⟧, so $g(t) = \exp_y(tw)$ on all of it because every geodesic is radial. Near $s + t$, $t \in J$, the curve $\exp_y(\cdot\,w)$ coincides with $\gamma_2$, whose position and velocity at $s + t$ are those of $\exp_{y'}(\cdot\,w')$ at $t$. $\square$

This gluing replaces the maximal geodesics that Milnor's talk of extending geodesics (pp. 58, 62) presupposes; maximal geodesics are not constructed.

**Theorem (the domain of $\exp$ is open in $TN$ and $\exp$ is continuous on it, V7.23).** Let $(p, v)$ be in the domain of $\exp$. Then every $z \in TN$ near $(p, v)$ is in the domain, and $\exp$, as a function on $TN$, is continuous at $(p, v)$ ⟦Chapter7/GeodesicFlow · eventually_mem_expDom_and_continuousWithinAt_exp⟧. In particular, if $\exp_p$ is defined on all of $T_pN$, it is continuous there ⟦Chapter7/GeodesicFlow · continuousOn_exp⟧.

*Proof.*

1. *The given geodesic.* Let $\gamma$ be a geodesic from $p$ with initial velocity $v$ on $(-\delta_0, 1 + \delta_0)$. Then $v \in T_pN$, $\exp_p(tv) = \gamma(t)$ there, so $\Psi_s(p, v) = (\gamma(s), \gamma'(s))$, and $\|\gamma'(s)\| = \|v\|$. Put $R = \|v\| + 1$.
2. *A uniform time.* For each $x \in N$ the local flow proposition gives $U_x$, $\tau_x$, $\Phi_x$ for this $R$. The arc $\gamma([0, 1])$ is compact, so finitely many $U_{x_1}, \dots, U_{x_k}$ cover it. Let $\tau_0 = \frac12\min_i\tau_{x_i}$, so $\tau_0 < \tau_{x_i}$ for each $i$.
3. *The induction statement.* For $s \in [0, 1]$ let $P(s)$ say: for all $z = (y, w) \in TN$ near $(p, v)$ (eventually in the neighbourhood filter of $(p, v)$ within $TN$), the curve $t \mapsto \exp_y(tw)$ is a geodesic on some $(-\delta, s + \delta)$; and $z \mapsto \Psi_s(z)$ is continuous within $TN$ at $(p, v)$.
4. *$P(0)$.* For $z = (y, w) \in TN$ near $(p, v)$, $y \in U_p$ and $\|w\| < R$, so $t \mapsto \exp_y(tw)$ is a geodesic on $(-\tau_p, \tau_p)$. And $\Psi_0$ is the identity on $TN$, hence continuous.
5. *The step: $P(s) \Rightarrow P(\min(s + \tau_0, 1))$ for $s \in [0, 1)$.* Let $s' = \min(s + \tau_0, 1)$ and $h = s' - s \in (0, \tau_0]$. Choose $i$ with $\gamma(s) \in U_{x_i}$. By continuity of $\Psi_s$, for $z = (y, w)$ near $(p, v)$ the point $(y', w') = \Psi_s z$ has $y' \in U_{x_i}$; also $y' \in N$, $w'$ is tangent at $y'$, and $\|w'\| = \|w\| < R$ by constant speed. So $t \mapsto \exp_{y'}(tw')$ is a geodesic on $(-\tau_{x_i}, \tau_{x_i})$ with $\Psi_t(y', w') = \Phi_{x_i}(y', w', t)$. Continuing (previous proposition), $t \mapsto \exp_y(tw)$ is a geodesic on $(-\delta, s + \delta) \cup (s - \tau_{x_i}, s + \tau_{x_i})$, which contains $(-\delta', s' + \delta')$ for $\delta' = \min(\delta, \tau_{x_i} - \tau_0)$, and
$$\Psi_{s'}(z) = \Psi_h(\Psi_s z) = \Phi_{x_i}(\Psi_s z, h).$$
The right side is continuous within $TN$ at $(p, v)$: $\Phi_{x_i}$ is continuous at $(\gamma(s), \gamma'(s), h)$, a point of its domain because $\|\gamma'(s)\| = \|v\| < R$ and $|h| < \tau_{x_i}$, and $z \mapsto (\Psi_s z, h)$ is continuous at $(p, v)$ by $P(s)$.
6. *Iteration.* By induction on $k$, $P(\min(k\tau_0, 1))$ for every natural $k$; for $k \ge 1/\tau_0$ this is $P(1)$.
7. *Conclusion.* For $z = (y, w) \in TN$ near $(p, v)$, $t \mapsto \exp_y(tw)$ is a geodesic on $(-\delta, 1 + \delta)$ starting at $y$ with velocity $w$, so $z$ is in the domain. And $\exp(z) = (\Psi_1 z)_1$ is continuous within $TN$ at $(p, v)$. For the last statement compose with $w \mapsto (p, w)$, which maps $T_pN$ into $TN$. $\square$

This is the global dependence of geodesics on their initial data. The smoothness of $\exp$ on its whole domain is proved in Chapter 11 (§VI.7); continuity is all that Corollary 10.10 uses.

### VI.17 Completeness

**Definitions (V7.22).**

- $(N, \rho)$ is *complete* if every sequence $(x_n)$ of points of $N$ that is Cauchy for $\rho$ (for every $\varepsilon > 0$, $\rho(x_m, x_n) < \varepsilon$ for all large $m, n$) converges for $\rho$ to some $y \in N$, that is $\rho(x_n, y) \to 0$ ⟦Chapter7/Metric · IsRiemComplete⟧. For preconnected $N$ this is completeness of the metric space $(N, \rho)$ in Mathlib's sense ⟦Chapter7/Metric · isRiemComplete_iff_completeSpace⟧ (a translation between the two formulations of Cauchy sequences and convergence).
- A set $X \subseteq V$ is *bounded* if $\rho(x, y) \le d$ for all $x, y \in X$ and some real $d$ ⟦Chapter7/Metric · IsRiemBounded⟧. A nonempty bounded set lies in $N$, since $\rho(x, x) = \infty$ for $x \notin N$.
- $N$ is *geodesically complete* if $\exp_q(v)$ is defined for every $q \in N$ and every $v \in T_qN$ ⟦Chapter7/GeodesicFlow · IsGeodesicallyComplete⟧ (Milnor, p. 58).

**Proposition.** If $\exp_q$ is defined on all of $T_qN$, then for every $v \in T_qN$ the curve $t \mapsto \exp_q(tv)$ is a geodesic on $\mathbb R$ ⟦Chapter7/GeodesicFlow · isGeodesicOn_univ_exp_smul⟧.

*Proof.* For $T > 0$ and $w \in T_qN$: $\exp_q(Tw)$ is defined, so there is a geodesic from $q$ with velocity $Tw$ on some $(-\delta, 1 + \delta)$, equal there to $\sigma \mapsto \exp_q(\sigma Tw)$ (§VI.6); rescaling time by $1/T$ (homogeneity), $t \mapsto \exp_q(tw)$ is a geodesic on $(-T\delta, T + T\delta)$. For $t \ge 0$ take $T = t + 1$ and $w = v$. For $t < 0$ take $T = -t + 1$ and $w = -v$, and reverse time: $\exp_q(-s(-v)) = \exp_q(sv)$. So $t \mapsto \exp_q(tv)$ is a geodesic near every $t$, hence on $\mathbb R$ by locality. $\square$

**Proposition (Milnor's two definitions agree, V7.22).** $N$ is geodesically complete if and only if every geodesic on an open preconnected nonempty $s \subseteq \mathbb R$ is the restriction to $s$ of a geodesic on $\mathbb R$ ⟦Chapter7/GeodesicFlow · isGeodesicallyComplete_iff⟧.

*Proof.* ($\Rightarrow$) Let $\gamma$ be a geodesic on $s$ and $t_0 \in s$, $q = \gamma(t_0)$, $v = \gamma'(t_0)$. By the last proposition and a shift of time, $t \mapsto \exp_q((t - t_0)v)$ is a geodesic on $\mathbb R$ with position $q$ and velocity $v$ at $t_0$; by uniqueness of geodesics on $s$ it equals $\gamma$ there. ($\Leftarrow$) For $q \in N$ and $v \in T_qN$, $t \mapsto \exp_q(tv)$ is a geodesic on some $(-\tau, \tau)$; it extends to a geodesic $\bar\gamma$ on $\mathbb R$, which on $(-1, 2)$ is a geodesic from $q$ with velocity $v$ (its value and derivative at $0$ are those of $\exp_q(tv)$). $\square$

Milnor calls the two "clearly equivalent" (p. 58). The equivalence glues geodesics, which needs uniqueness in the large.

### VI.18 Theorem 10.9 (Hopf–Rinow)

**Definition (V7.24).** A curve $\gamma$ is a *minimal geodesic on $[a, b]$*, $a \le b$, if it is a geodesic on some open set containing $[a, b]$ and $L(\gamma|[a, b]) \le L(c|[a', b'])$ for every piecewise smooth path $c$ in $N$, on any $[a', b']$, with $c(a') = \gamma(a)$ and $c(b') = \gamma(b)$ ⟦Chapter7/HopfRinow · IsMinimalGeodesic⟧ (Milnor, pp. 61–62).

**Lemma.** If $v \in T_pN$, $t \mapsto \exp_p(tv)$ is a geodesic on $\mathbb R$ and $\rho(p, \exp_p v) = \|v\|$, then $t \mapsto \exp_p(tv)$ is a minimal geodesic on $[0, 1]$, of length $\|v\|$ ⟦Chapter7/HopfRinow · isMinimalGeodesic_exp_smul⟧. *Proof.* Its speed is $\|v\|$, so its length on $[0, 1]$ is $\|v\|$; a competitor $c$ has $\|v\| = \rho(p, \exp_p v) \le L(c)$. $\square$

Milnor's proof (pp. 62–64, Diagram 10) has two steps that the formal proof isolates as lemmas.

**Step 1: the nearest point of a small sphere (V7.25).** Let $\varepsilon$ be a normal radius at $p \in N$, $0 < \delta < \varepsilon$, and $q$ with $\delta < \rho(p, q) < \infty$. There is $w \in T_pN$ with $\|w\| = \delta$ and
$$\rho(p, q) = \delta + \rho(\exp_p w, q)$$
⟦Chapter7/HopfRinow · NormalCoord.exists_riemDist_eq_add⟧: the point $p_0 = \exp_p w$ of the sphere $S$ of radius $\delta$ about $p$ is a point of $S$ nearest to $q$.

*Proof.*

1. $q \in N$, since $\rho(p, q) < \infty$; and $q \notin \mathrm{ball}_\delta$, since otherwise $\rho(p, q) < \delta$ (§VI.14). This is where $\delta < \rho(p, q)$ is needed: otherwise $q$ lies inside the shell and paths from $p$ to $q$ need not meet it.
2. $S = \exp_p\big(\{w \in T_pN : \|w\| = \delta\}\big) = F(\dots)$ is compact, as the continuous image of a compact set, and lies in $N$.
3. *Every path crosses $S$.* Let $c$ be a piecewise smooth path in $N$ from $p$ to $q$ on $[a, b]$. The crossing lemma with $s = \delta$ gives $t_1 < t_2$ with $\|G(c(t_2))\| = \delta$, so $y = c(t_2) = \exp_p(G(c(t_2))) \in S$, and $L(c|[t_1, t_2]) \ge \delta$. Then $L(c|[a, b]) \ge L(c|[t_1, t_2]) + L(c|[t_2, b]) \ge \delta + \rho(y, q)$.
4. *$S$ is nonempty*: $\rho(p, q) < \infty$, so some path from $p$ to $q$ exists (the infimum of the empty set is $\infty$), and step 3 produces a point of $S$.
5. *The nearest point.* $y \mapsto \rho(y, q)$ is continuous on $N \supseteq S$ (§VI.14), and $S$ is compact and nonempty, so it has a minimum at some $y_0 = \exp_p(w_0)$, $\|w_0\| = \delta$ ⟦Mathlib/Topology/Order/Compact · IsCompact.exists_isMinOn⟧.
6. *Equality.* $\rho(p, q) \le \rho(p, y_0) + \rho(y_0, q) = \delta + \rho(y_0, q)$, as $\rho(p, \exp_p w_0) = \|w_0\| = \delta$. Conversely, for every path length $L \in \Lambda(p, q)$, step 3 gives $y \in S$ with $\delta + \rho(y_0, q) \le \delta + \rho(y, q) \le L$; take the infimum. $\square$

**Step 2: a broken geodesic of minimal length is unbroken (V7.25).** Let $\gamma$ be a geodesic on $\mathbb R$ with $\|\gamma'(0)\| = 1$, let $0 < t_0 < t_1$, and let $\sigma$ be a geodesic on an open preconnected set containing $[t_0, t_1]$ with $\|\sigma'(t_0)\| = 1$ and $\sigma(t_0) = \gamma(t_0)$. If $\rho(\gamma(0), \sigma(t_1)) \ge t_1$, then $\sigma(t_1) = \gamma(t_1)$ ⟦Chapter7/HopfRinow · broken_geodesic_eq⟧.

*Proof.*

1. *The broken path.* Let $c = \gamma$ on $t \le t_0$ and $c = \sigma$ after. It is piecewise smooth on $[0, t_1]$ (concatenation) and lies in $N$.
2. *Unit speed.* Both pieces have constant speed $1$. At a point $t \ne t_0$ where $c$ is differentiable, $c$ agrees near $t$ with $\gamma$ or with $\sigma$. At $t = t_0$, if $c$ is differentiable there, its derivative is also its left derivative, which is that of $\gamma$, of norm $1$ (left derivatives on $(-\infty, t_0]$ are unique ⟦Mathlib/Analysis/Calculus/TangentCone/Real · uniqueDiffWithinAt_Iic⟧). So $L(c|[0, t_1]) = t_1$.
3. *Minimality.* For any piecewise smooth competitor $\tilde c$ from $c(0) = \gamma(0)$ to $c(t_1) = \sigma(t_1)$: $t_1 \le \rho(\gamma(0), \sigma(t_1)) \le L(\tilde c)$.
4. *Corollary 10.7* makes $c$ a geodesic on $(0, t_1)$. It agrees with $\gamma$ near $t_0/2$, in position and velocity, so by uniqueness of geodesics $c = \gamma$ on $(0, t_1)$, and by continuity on $[0, t_1]$ ⟦Mathlib/Topology/Separation/Hausdorff · Set.EqOn.of_subset_closure⟧. In particular $\sigma(t_1) = c(t_1) = \gamma(t_1)$. $\square$

Milnor (pp. 63–64) concludes by Corollary 10.7 that the broken geodesic is unbroken "and hence coincides with $\gamma$"; this needs unit speed on both pieces and uniqueness in the large.

**Theorem 10.9, at one point (V7.26).** Let $p \in N$ be such that $\exp_p$ is defined on all of $T_pN$. Every $q \in N$ with $\rho(p, q) < \infty$ is $\exp_p(v)$ for some $v \in T_pN$ with $\|v\| = \rho(p, q)$, and $t \mapsto \exp_p(tv)$ is a minimal geodesic on $[0, 1]$ from $p$ to $q$ ⟦Chapter7/HopfRinow · theorem_10_9⟧.

*Proof.* Let $r = \rho(p, q)$. Once a $v \in T_pN$ with $\exp_p(v) = q$ and $\|v\| = r$ is found, the lemma before Step 1 finishes the proof, $t \mapsto \exp_p(tv)$ being a geodesic on $\mathbb R$ (§VI.17).

1. *$r = 0$.* Then $p = q$ by positivity, and $v = 0$.
2. *The first sphere.* Let $r > 0$, $\varepsilon$ a normal radius at $p$ and $\delta = \min(\varepsilon, r)/2$, so that $\delta < \varepsilon$ and $\delta < r$. Step 1 gives $w_0$ with $\|w_0\| = \delta$ and $r = \delta + \rho(\exp_p w_0, q)$. Let $u = w_0/\delta$, a unit vector, and $\gamma(t) = \exp_p(tu)$, a geodesic on $\mathbb R$ of unit speed with $\gamma(0) = p$ and $\gamma(\delta) = \exp_p(w_0)$.
3. *The set of good times.* Let $A = \{t : \rho(\gamma(t), q) = r - t\}$. It is closed, because $t \mapsto \rho(\gamma(t), q)$ is continuous (§VI.14) and $t \mapsto r - t$, read in $[0, \infty]$, is continuous. By Step 1, $\delta \in A$.
4. *The inductive step.* Let $t_0 \in A$ with $\delta \le t_0 < r$, and $y > t_0$; we find a point of $A$ in $(t_0, y]$. Let $x_0 = \gamma(t_0)$, $\varepsilon'$ a normal radius at $x_0$, and $\delta' = \min(\varepsilon', r - t_0, y - t_0)/2$. Since $\rho(x_0, q) = r - t_0 > \delta'$, Step 1 at $x_0$ gives $w$ with $\|w\| = \delta'$ and $\rho(x_0, q) = \delta' + \rho(p_0', q)$ for $p_0' = \exp_{x_0}(w)$; so $\rho(p_0', q) = r - (t_0 + \delta')$, and the triangle inequality $r \le \rho(p, p_0') + \rho(p_0', q)$ gives $\rho(p, p_0') \ge t_0 + \delta'$. Let $\sigma(t) = \exp_{x_0}\big(\frac{t - t_0}{\delta'}w\big)$, the radial geodesic of the normal ball at $x_0$ rescaled to unit speed: $\sigma(t_0) = x_0 = \gamma(t_0)$, $\sigma(t_0 + \delta') = p_0'$, and $\sigma$ is a geodesic on an open interval containing $[t_0, t_0 + \delta']$. Step 2, with $t_1 = t_0 + \delta'$, gives $\gamma(t_0 + \delta') = p_0'$, hence $t_0 + \delta' \in A$; and $t_0 < t_0 + \delta' \le y$.
5. *Continuous induction.* A closed set containing $\delta$ that, with each of its points $t_0 \in [\delta, r)$, meets every interval $(t_0, y]$, contains $[\delta, r]$ ⟦Mathlib/Topology/Order/IntermediateValue · IsClosed.Icc_subset_of_forall_exists_gt⟧. So $r \in A$: $\rho(\gamma(r), q) = 0$, and $\gamma(r) = q$ by positivity.
6. Take $v = ru$: $\exp_p(v) = \gamma(r) = q$ and $\|v\| = r$. $\square$

*What Milnor leaves implicit.* Besides $\delta < \rho(p, q)$ in Step 1, the inductive step needs $\delta' < r - t_0$, else $t_0 + \delta'$ overshoots $r$; the supremum "by continuity" is the continuous induction of step 5, resting on the continuity of $\rho$. Completeness is used only at $p$: the proof uses the single geodesic $t \mapsto \exp_p(tu)$.

**Theorem 10.9, Milnor's statement (V7.26).** If $N$ is preconnected and geodesically complete, any two points $p, q \in N$ are joined by a minimal geodesic $\gamma$ on $[0, 1]$, $\gamma(0) = p$, $\gamma(1) = q$, with $\rho(p, q) = L(\gamma|[0, 1])$ ⟦Chapter7/HopfRinow · theorem_10_9'⟧. *Proof.* $\rho(p, q) < \infty$ by connectedness (§VI.14); apply the theorem at $p$; the length of $t \mapsto \exp_p(tv)$ on $[0, 1]$ is $\|v\| = \rho(p, q)$. $\square$

### VI.19 Corollary 10.10, its converse, and the Hopf–Rinow theorem

**Corollary 10.10, first part, at one point (V7.27).** Let $N$ be preconnected and $p \in N$ such that $\exp_p$ is defined on all of $T_pN$. Every bounded set $X \subseteq V$ has compact closure, and the closure lies in $N$ ⟦Chapter7/HopfRinow · isCompact_closure_of_isRiemBounded⟧.

*Proof.* The empty set is trivial. Let $x_0 \in X$ and $d$ a bound for the diameter. $X \subseteq N$, as noted in §VI.17. With $R = \rho(p, x_0) + \max(d, 0)$, finite by connectedness, every $x \in X$ has $\rho(p, x) \le \rho(p, x_0) + \rho(x_0, x) \le R$. The set
$$K = \exp_p\big(\bar B(0, R) \cap T_pN\big)$$
is compact, as the image of a compact set under $\exp_p$, which is continuous on $T_pN$ (§VI.16); and $K \subseteq N$. By Theorem 10.9 at $p$, each $x \in X$ is $\exp_p(v)$ with $\|v\| = \rho(p, x) \le R$, so $X \subseteq K$. $K$ is closed in $V$, so the closure of $X$ lies in $K$, is compact, and lies in $N$. $\square$

Milnor's proof (p. 64) is this one; it needs $\exp_p$ continuous on the whole disk, which Lemma 10.2 does not give, and $M$ connected, so that distances are finite and Theorem 10.9 applies to all of $X$.

**Corollary 10.10, second part (V7.27).** If every bounded set has compact closure contained in $N$, then $(N, \rho)$ is complete ⟦Chapter7/HopfRinow · isRiemComplete_of_forall_isCompact_closure⟧.

*Proof.* Let $(x_n)$ be $\rho$-Cauchy in $N$ and $n_0$ such that $\rho(x_m, x_n) < 1$ for $m, n \ge n_0$. The tail $X = \{x_{n_0 + k}\}$ is bounded, so its closure is compact and lies in $N$, and a subsequence of the tail converges in $V$ to some $y$ in the closure ⟦Mathlib/Topology/Sequences · IsCompact.tendsto_subseq⟧, hence $y \in N$. Convergence in $N$ implies convergence for $\rho$ ⟦Chapter7/Metric · tendsto_riemDist_of_tendsto⟧, by the neighbourhood-basis property. Finally a Cauchy sequence with a convergent subsequence converges: given $\eta > 0$, choose $n_1$ with $\rho(x_m, x_n) < \eta/2$ for $m, n \ge n_1$ and a term $x_{\varphi(k) + n_0}$ of the subsequence with index $\ge n_1$ and $\rho(x_{\varphi(k)+n_0}, y) < \eta/2$; then $\rho(x_n, y) < \eta$ for $n \ge n_1$. $\square$

**Corollary 10.10 (V7.27).** If $N$ is preconnected and geodesically complete, every bounded set has compact closure contained in $N$, and $(N, \rho)$ is complete ⟦Chapter7/HopfRinow · corollary_10_10⟧. *Proof.* If $N$ is empty, a bounded set is empty (a point $x$ would have $\rho(x, x) = \infty$), and both conclusions hold. Otherwise use the two parts at any $p \in N$. $\square$

**The converse of Corollary 10.10 (V7.28).** If $(N, \rho)$ is complete, then $N$ is geodesically complete ⟦Chapter7/GeodesicFlow · isGeodesicallyComplete_of_isRiemComplete⟧. No connectedness is assumed.

Milnor (p. 64) calls this not difficult, using Lemma 10.3, and leaves the details to Hopf and Rinow. The formal proof is the exposition's, and uses only the uniform local existence of Lemma 10.2.

*Proof.* Let $q \in N$, $v \in T_qN$ and $c(t) = \exp_q(tv)$. It suffices that $c$ is a geodesic near $[0, 1]$: then it is a geodesic from $q$ with initial velocity $v$.

1. *The set of good times.* Let $A$ be the set of $T \ge 0$ such that $c$ is a geodesic on some $(-\delta, T + \delta)$. It is downward closed in $[0, \infty)$ and contains $0$ (local existence). Suppose $1 \notin A$; then $A \subseteq [0, 1)$. Let $T_0 = \sup A$; $T_0 > 0$, since $A$ contains a small positive time.
2. *Below $T_0$.* For $0 \le t < T_0$ there is $T > t$ in $A$, so $c$ is a geodesic near $[0, T]$, of speed $\|v\|$, lying in $N$. For $0 \le t \le t' < T_0$ the restriction of $c$ to $[t, t']$ is a piecewise smooth path of length $\|v\|(t' - t)$, so $\rho(c(t), c(t')) \le \|v\|\,|t' - t|$.
3. *A Cauchy sequence.* Let $t_n = T_0 - T_0/(n + 2)$, which increases to $T_0$. By step 2, $(c(t_n))$ is $\rho$-Cauchy, and by completeness $\rho(c(t_n), x) \to 0$ for some $x \in N$.
4. *Uniform time near the limit.* The local flow proposition at $x$ with $R = \|v\| + 1$ gives $U \ni x$ and $\tau > 0$: every geodesic $t \mapsto \exp_y(tw)$ with $y \in N \cap U$, $w \in T_yN$, $\|w\| < R$ exists on $(-\tau, \tau)$. Metric balls about $x$ are neighbourhoods in $N$, so $c(t_n) \in U$ for large $n$; also $t_n > T_0 - \tau/2$ for large $n$. Fix such an $n$.
5. *Continuation.* $c$ is a geodesic on some $(-\delta, T + \delta)$ with $T > t_n$, and $\Psi_{t_n}(q, v)$ has position $c(t_n) \in N \cap U$ and velocity of norm $\|v\| < R$. So the geodesic starting there exists on $(-\tau, \tau)$, and continuing (§VI.16) makes $c$ a geodesic on $(-\delta, T + \delta) \cup (t_n - \tau, t_n + \tau)$. Since $t_n + \tau > T_0 + \tau/2$, this union contains $(-\delta', T_0 + \tau/4 + \delta')$ for $\delta' = \min(\delta, \tau/4)$. So $T_0 + \tau/4 \in A$, contradicting $T_0 = \sup A$. $\square$

**Bounded closed sets are compact.** If every bounded set has compact closure contained in $N$, then every subset of $N$ that is closed in $N$ and bounded is compact ⟦Chapter7/HopfRinow · isCompact_of_isClosed_of_isRiemBounded⟧: its closure in $V$ is compact and lies in $N$, so it equals the closure in $N$, which is the set itself.

**The Hopf–Rinow theorem (V7.29).** Let $N$ be preconnected and nonempty. The following are equivalent ⟦Chapter7/HopfRinow · hopf_rinow⟧:

1. $(N, \rho)$ is complete;
2. $N$ is geodesically complete;
3. $\exp_p$ is defined on all of $T_pN$ for some $p \in N$;
4. every bounded set has compact closure, contained in $N$.

*Proof.* (1) ⇒ (2) is the converse of Corollary 10.10; (2) ⇒ (3) because $N$ is nonempty; (3) ⇒ (4) is the first part of Corollary 10.10 at $p$; (4) ⇒ (1) is its second part. $\square$

Condition (3) is not in the book. After Corollary 10.10 and its converse Milnor speaks simply of complete Riemannian manifolds (p. 64).

**Consequences of completeness (V7.29).** If $N$ is preconnected and $(N, \rho)$ is complete, then $N$ is geodesically complete; every geodesic on an open interval is the restriction of a geodesic on $\mathbb R$; any two points $p, q$ are joined by a minimal geodesic on $[0, 1]$ whose length is $\rho(p, q)$; and every bounded subset of $N$ that is closed in $N$ is compact ⟦Chapter7/HopfRinow · hopf_rinow_of_isRiemComplete⟧. *Proof.* The converse of Corollary 10.10, the two definitions of §VI.17, Theorem 10.9, and Corollary 10.10 with the last remark. $\square$

### VI.20 Closed submanifolds and the sphere

In the embedded setting completeness has a simple sufficient condition, the source of the complete manifolds used later.

**Theorem (closed submanifolds are complete, V7.30).** If $N$ is closed in $V$, then $(N, \rho)$ is complete ⟦Chapter7/Metric · isRiemComplete_of_isClosed⟧.

*Proof.* A $\rho$-Cauchy sequence is Cauchy in $V$, because $\|x - y\| \le \rho(x, y)$ (§VI.14). $V$ is complete, so the sequence converges in $V$ ⟦Mathlib/Topology/UniformSpace/Cauchy · cauchySeq_tendsto_of_complete⟧, to a limit that lies in $N$ because $N$ is closed. Convergence in $N$ implies convergence for $\rho$. $\square$

**Corollary (V7.30).** A preconnected $N$ that is closed in $V$, in particular a preconnected compact one, has all the properties listed under "consequences of completeness": it is geodesically complete, its geodesics extend to $\mathbb R$, any two of its points are joined by a minimal geodesic whose length is their distance, and its closed bounded subsets are compact ⟦Chapter7/HopfRinow · hopf_rinow_of_isClosed⟧ ⟦Chapter7/HopfRinow · hopf_rinow_of_isCompact⟧. This covers, for instance, compact matrix groups embedded in a space of matrices.

**The round sphere (V7.30).** Let $n \ge 1$ and $S^n = \{x \in \mathbb R^{n+1} : \langle x, x\rangle - 1 = 0\}$ ⟦Milnor/Chapter5/HairyBall · sphG⟧ ⟦Milnor/Chapter5/HairyBall · Sph⟧, with its structure of a slice submanifold of $\mathbb R^{n+1}$ modelled on $\mathbb R^n$ with complement $\mathbb R^1$, from the companion volume ⟦Milnor/Chapter6/EulerSphere · sphSub⟧. Then $S^n$ is geodesically complete, and any two of its points are joined by a minimal geodesic on $[0, 1]$ whose length is their distance ⟦Chapter7/HopfRinow · sphere_hopf_rinow⟧.

*Proof.* $S^n$ is the metric sphere of radius $1$ ⟦Milnor/Chapter5/HairyBall · preimage_eq_sphere⟧, compact ⟦Milnor/Chapter6/EulerSphere · isCompact_sph⟧ and connected, because the dimension $n + 1$ of the ambient space exceeds $1$ ⟦Mathlib/Analysis/Normed/Module/Connected · isConnected_sphere⟧. Apply the corollary. $\square$

Milnor (p. 65) shows that the geodesics of $S^n$ are the great circles and discusses which arcs of them are minimal; that identification is not formalized.

### VI.21 What the formalization taught us

The hidden hypotheses of §10 are of four kinds, each recorded where it is used: uniqueness of geodesics in the large (§VI.4); uniform comparisons between tangent vectors and their coordinates, in Lemmas 10.2 and 10.3 (§VI.5, §VI.8); the crossing lemma, needed wherever a competing path may leave a normal ball, with the compactness of closed normal balls behind it (§VI.11); and two continuity statements the book uses without proof, of $\rho$ and of $\exp_p$ on large disks (§VI.14, §VI.16). Three statements needed sharpening: the equality case of Theorem 10.4 (§VI.12), the radii $\delta < \rho(p, q)$ and $\delta' < r - t_0$ in Theorem 10.9 (§VI.18), and $\delta$ below every $\varepsilon$ of the cover in Corollary 10.8 (§VI.15). And two results need less than the book uses: Theorem 10.9 needs completeness at one point only, and the converse of Corollary 10.10 only Lemma 10.2, not Lemma 10.3.

Not formalized: maximal geodesics (gluing replaces them); the remark after Lemma 10.3 that $W$ can be chosen geodesically convex (p. 59); the remarks on minimal geodesics of p. 62; the examples of pp. 65–66 beyond the completeness of the sphere; Lemma 10.6 in its two-sided form; and §10 on an abstract Riemannian manifold, which would need a Levi-Civita connection and an exponential map that Mathlib does not have, or Nash's embedding theorem.
