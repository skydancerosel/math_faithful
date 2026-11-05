## Part X. Non-conjugate points, topology and curvature (Milnor §§18–19)

In §§18–19 Milnor draws the global consequences of the index theorem and of the fundamental theorem of §17. Section 18 identifies the points conjugate to $p$ with the critical values of $\exp_p$ (Theorem 18.1). Sard's theorem then shows that almost every $q$ is conjugate to $p$ along no geodesic (Corollary 18.2), which is the hypothesis under which Theorem 17.3 describes $\Omega(M; p, q)$. Section 19 relates curvature to topology. Non-positive sectional curvature rules out conjugate points (Lemma 19.1), and this leads to the theorem of Cartan and Hadamard (19.2) and to the vanishing of the higher homotopy groups (19.3). A positive lower bound $(n-1)/r^2$ on the Ricci curvature forces conjugate points on every geodesic longer than $\pi r$ (Myers, 19.4), bounds the diameter (19.5), and leaves the path space only finitely many cells in each dimension (19.6).

Every result of this Part is proved for a slice submanifold $N$ of a finite-dimensional real inner product space $V$, modelled on $Z$, with the induced metric, as in Parts VI–IX; $n = \dim Z$ is the dimension of $N$. No statement assumes $N$ closed, compact, connected or complete unless it says so. Every Riemannian manifold is of this kind by Nash's embedding theorem, which is quoted, not proved. The formal route leaves Milnor's at five places, each explained where it occurs.

1. Milnor treats $\exp_p$ as a smooth map on all of $TM_p$, but §10 gives smoothness only near the zero section. The smooth dependence of geodesics on their initial data over a compact time interval is therefore proved first (X.2–X.4). It also removes the completeness assumption from §18.
2. Theorem 18.1 is proved with the explicit Jacobi fields $W_X(t) = t\,d(\exp_q)_{tv}(X)$. It comes with the multiplicity, which is the dimension of the kernel of $d(\exp_q)_v$.
3. Cartan–Hadamard is proved with covering spaces rather than with the path space. In non-positive curvature $\exp_p : T_pN \to N$ is a covering map, and simple connectivity makes it injective. Milnor's statements about the path space are then derived from the covering (X.17).
4. The first half of Corollary 19.3 is proved by lifting cubes through $\exp_p$. No abstract universal covering appears.
5. For Theorem 19.6 the continuity of the Ricci curvature on the unit tangent bundle, which Milnor uses, is proved. The homology of $\Omega$ is computed from the energy filtration, not from cells.

Two statements are not proved: that the fundamental group of a complete manifold of non-positive curvature has no element of finite order other than the identity (the second half of 19.3), and Theorem 19.6 when $p$ and $q$ are conjugate along some geodesic (X.20).

**Map.**

- `Chapter11/ExpSmooth`: geodesics that depend smoothly on a parameter in a normed space; $\exp$ smooth on its whole domain; $\exp_q$, its domain and its derivative; Theorem 18.1 with the multiplicity.
- `Chapter11/NonConjugate`: the conjugate locus; Corollary 18.2; the density of non-conjugate points; the complete case.
- `Chapter11/Curvature`: Lemma 19.1; index and nullity $0$; $E_{**}$ positive definite; $\exp_p$ nowhere critical.
- `Chapter11/Myers`: the Ricci tensor, its symmetry and Milnor's Assertion; a parallel frame along a geodesic; Theorem 19.4, Corollary 19.5, the unit sphere.
- `Chapter11/LongGeodesics`: test fields on pieces of $[0, 1]$; the index bound in the proof of Theorem 19.6.
- `Chapter11/ExpCovering`: the Gauss lemma on the whole domain of $\exp_p$; $\exp_p$ a local diffeomorphism; lifting curves; $\exp_p$ a covering map.
- `Chapter11/CartanHadamard`: Theorem 19.2; the first half of 19.3; one geodesic in each homotopy class; the path space in non-positive curvature.
- `Chapter11/PositiveRicci`: the continuity and the minimum of the Ricci curvature; Theorem 19.6 for non-conjugate end points.
- `Chapter11/RicciHomology`: the homology of $\Omega(N; p, q)$ is finite-dimensional in each degree under the hypotheses of 19.6.

### X.1 The setting

The objects of this Part are those of §0.3, §0.8 and §0.9 and of Parts V–IX. This section recalls them in the form in which the proofs below use them.

*The submanifold and its curvature.* $N \subseteq V$ is a slice submanifold modelled on $Z$ with complement $W$ ⟦Milnor/Chapter2/Submanifold · IsSliceSubmanifold⟧. Its tangent space $T_qN \subseteq V$ at $q \in N$ is the range of the derivative of the inclusion ⟦Chapter1/ManifoldSubmanifold · tangentSubspace⟧, of dimension $n$ ⟦Chapter9/JacobiSystem · finrank_tanAt⟧ ⟦Chapter9/JacobiSystem · tanAt_of_mem⟧. $P_q$ is the orthogonal projection of $V$ onto $T_qN$ ⟦Chapter6/Projection · tanProj⟧. Along curves the proofs use a total version $P_x$, which is the projection for $x \in N$ and $0$ for $x \notin N$ ⟦Chapter8/Energy · prj⟧; it is idempotent and self-adjoint ⟦Chapter8/Energy · prj_prj⟧ ⟦Chapter8/Energy · inner_prj_left⟧, and it fixes exactly the tangent vectors ⟦Chapter8/Energy · prj_eq_self_iff⟧. The second fundamental form is $\mathrm{II}(a, b) = (dP)_q(a)\,b$, the derivative of $q \mapsto P_q$ along $N$ ⟦Chapter6/Submanifold · secondFundForm⟧. Milnor's curvature tensor, with his sign, is
$$R(x, y)z = \mathrm{II}(y, \mathrm{II}(x, z)) - \mathrm{II}(x, \mathrm{II}(y, z))$$
⟦Chapter6/Submanifold · curvOp⟧ ⟦Chapter6/Submanifold · curvOp_apply⟧. On $T_qN$ it is a trilinear map ⟦Chapter6/Submanifold · curvTensor⟧ with the identities of Lemma 9.3 ⟦Chapter6/Submanifold · isCurvatureTensor_curvTensor⟧, and along curves it is used in a total form that agrees with it at points of $N$ ⟦Chapter8/SecondVariation · curvR⟧ ⟦Chapter8/SecondVariation · curvR_of_mem⟧.

*Geodesics and the exponential map.* A geodesic on an open set $s \subseteq \mathbb R$ is a curve $\gamma : \mathbb R \to V$, smooth on $s$, with values in $N$ there, whose acceleration is normal to $N$ ⟦Chapter7/Geodesic · IsGeodesicOn⟧. Its velocity is tangent ⟦Chapter7/Geodesic · IsGeodesicOn.deriv_mem⟧, the tangential part of its acceleration vanishes ⟦Chapter7/Geodesic · IsGeodesicOn.tanProj_deriv_deriv⟧, and on an interval its speed is constant ⟦Chapter7/Geodesic · IsGeodesicOn.norm_deriv_eq⟧. A pair $(q, v)$ lies in the domain of $\exp$ if some geodesic $\gamma$ on an interval $(-\delta, 1 + \delta)$ has $\gamma(0) = q$ and $\gamma'(0) = v$ ⟦Chapter7/Exp · IsGeodesicFrom⟧ ⟦Chapter7/Exp · expDom⟧. Then $\exp_q(v) = \gamma(1)$ ⟦Chapter7/Exp · exp⟧, whatever $\gamma$ is chosen ⟦Chapter7/Exp · IsGeodesicFrom.exp_eq⟧, and $\exp_q(v) \in N$ ⟦Chapter7/HopfRinow · exp_mem_of_mem_expDom⟧. Further, $\exp_q(0) = q$ ⟦Chapter7/Exp · exp_zero⟧, and $\exp_q$, as a map from the vector space $T_qN$ to $V$, has as derivative at $0$ the inclusion $T_qN \to V$ ⟦Chapter7/Exp · hasFDerivAt_exp_zero⟧. The curve $t \mapsto \exp_y(tw)$ has velocity $w$ at $t = 0$ ⟦Chapter7/GeodesicFlow · hasDerivAt_exp_smul_zero⟧. $N$ is *geodesically complete* if $(q, v)$ lies in the domain for every $q \in N$ and $v \in T_qN$ ⟦Chapter7/GeodesicFlow · IsGeodesicallyComplete⟧, and then every $t \mapsto \exp_q(tv)$ is a geodesic on all of $\mathbb R$ ⟦Chapter7/GeodesicFlow · isGeodesicOn_univ_exp_smul⟧. Completeness of $N$ for Milnor's distance $\rho$ ⟦Chapter7/Distance · riemDist⟧ ⟦Chapter7/Metric · IsRiemComplete⟧ implies geodesic completeness ⟦Chapter7/GeodesicFlow · isGeodesicallyComplete_of_isRiemComplete⟧, and a closed $N \subseteq V$ is complete for $\rho$ ⟦Chapter7/Metric · isRiemComplete_of_isClosed⟧.

*Curves, Jacobi fields and conjugate points.* A *smooth curve on $[0, 1]$* is a curve that is smooth on the closed interval (with one-sided derivatives at the ends) and has values in $N$ there ⟦Chapter9/JacobiSystem · IsSmoothCurveIn⟧. Its velocity $\gamma'(t)$ is taken within $[0, 1]$ ⟦Chapter9/JacobiSystem · velAlong⟧, and so is the covariant derivative $DX/dt = P_{\gamma(t)}(dX/dt)$ of a field along it ⟦Chapter9/JacobiSystem · covAlong⟧. In the interior of $[0, 1]$ the two-sided version is also used ⟦Chapter8/FirstVariation · covD⟧, with the same notation. A *Jacobi field* along $\gamma$ is a field that is smooth on $[0, 1]$, tangent to $N$, and satisfies $D^2J/dt^2 + R(V, J)V = 0$ on $(0, 1)$, where $V = d\gamma/dt$ ⟦Chapter8/Jacobi · jacobiExpr⟧ ⟦Chapter8/Jacobi · IsJacobiField⟧. Being a Jacobi field depends only on the values of $J$ on $[0, 1]$ ⟦Chapter9/JacobiSpace · IsJacobiField.congr⟧. The Jacobi fields form a vector space $\mathcal J(\gamma)$, each normalized to be constant off $[0, 1]$ ⟦Chapter9/JacobiSpace · jacobiSpace⟧. A Jacobi field is determined by $J(s)$ and $DJ/dt(s)$ at any $s \in [0, 1]$, and every pair of tangent vectors occurs ⟦Chapter9/JacobiSpace · jacEval_bijective⟧. In particular $J(s) = 0$ and $DJ/dt(s) = 0$ force $J = 0$ on $[0, 1]$ ⟦Chapter9/JacobiSystem · IsJacobiField.eqOn_zero⟧. Parameters $a \ne b$ of $[0, 1]$ are *conjugate* along $\gamma$ if some Jacobi field vanishes at $a$ and at $b$ without vanishing on all of $[0, 1]$ ⟦Chapter9/JacobiSpace · IsConjugate⟧. Their *multiplicity* is the dimension of the space of fields of $\mathcal J(\gamma)$ that vanish at $a$ and $b$ ⟦Chapter9/JacobiSpace · conjSpace⟧ ⟦Chapter9/JacobiSpace · mem_conjSpace⟧ ⟦Chapter9/JacobiSpace · conjMultiplicity⟧, and $a$, $b$ are conjugate exactly when it is positive ⟦Chapter9/JacobiSpace · isConjugate_iff⟧. As in Part VII, "$\gamma(t)$ is conjugate to $\gamma(0)$" means that the parameters $0$ and $t$ are conjugate.

*The path space and $E_{**}$.* $\Omega(N; p, q)$ is the set of piecewise smooth paths in $N$ from $p$ to $q$ ⟦Chapter8/Energy · pathSpace⟧, with energy $E(\omega) = \int_0^1 \|d\omega/dt\|^2\,dt$ ⟦Chapter8/Energy · energy⟧ and length $L(\omega)$ ⟦Chapter7/Path · pathLength⟧. An *unbroken geodesic* of $\Omega$ is a path smooth on $[0, 1]$ that is a geodesic on $(0, 1)$ ⟦Chapter8/Critical · IsUnbrokenGeodesic⟧, and such a path is a smooth curve in the sense above ⟦Chapter9/JacobiSystem · IsUnbrokenGeodesic.isSmoothCurveIn⟧. $T\Omega_\gamma$ is the space of piecewise smooth tangent fields along $\gamma$ that vanish at $0$ and $1$ ⟦Chapter8/Energy · pathTangent⟧. $E_{**}$ is a symmetric bilinear form on it ⟦Chapter8/Hessian · energyHessian⟧ ⟦Chapter8/Hessian · energyHessian_isSymm⟧, given by the integral form of the second variation formula
$$\tfrac12 E_{**}(W_1, W_2) = \int_0^1 \Big(\Big\langle \frac{DW_1}{dt}, \frac{DW_2}{dt}\Big\rangle - \langle R(V, W_1)V, W_2\rangle\Big)\,dt$$
⟦Chapter8/Hessian · energyHessian_eq_integral⟧. Its *index* is the supremum, in $\mathbb N \cup \{\infty\}$, of the dimensions of the finite-dimensional subspaces on which it is negative definite ⟦Chapter9/FormIndex · IsNegDefOn⟧ ⟦Chapter9/FormIndex · formIndex⟧, so one such subspace of dimension $k$ gives index $\ge k$ ⟦Chapter9/FormIndex · le_formIndex⟧. Its *nullity* ⟦Chapter9/JacobiSpace · hessNullity⟧ is positive exactly when $0$ and $1$ are conjugate (Theorem 14.1) ⟦Chapter9/JacobiSpace · hessNullity_pos_iff⟧, and a field $W$ with $E_{**}(W, \cdot) = 0$ is a Jacobi field ⟦Chapter8/Jacobi · theorem_14_1⟧. The index theorem 15.1 says that the index is the number of $t \in (0, 1)$ conjugate to $0$, counted with multiplicity, a finite sum ⟦Chapter9/IndexTheorem · theorem_15_1⟧. At a minimal geodesic ⟦Chapter8/Hessian · IsMinimalPath⟧ the form $E_{**}$ is positive semi-definite (Lemma 13.6) ⟦Chapter8/Hessian · lemma_13_6⟧.

*The topology of the path space.* $\Omega(N; p, q)$ carries Milnor's metric ⟦Chapter10/PathMetric · PathSp⟧. $\Omega^*(N; p, q)$ is the space of continuous paths with the compact-open topology ⟦Chapter10/FullPathSpace · pathCSet⟧ ⟦Chapter10/FullPathSpace · PathC⟧. The inclusion $\Omega \to \Omega^*$ is a homotopy equivalence, with no completeness assumed (Theorem 17.1; Part IX, §IX.18) ⟦Chapter10/FullPathTheorem · theorem_17_1⟧. Theorem 17.3 (Part IX, §IX.6) applies when $N$ is closed in $V$ and every geodesic from $p$ to $q$ is non-degenerate. It produces lists $\mathrm{geo}_0, \mathrm{geo}_1, \ldots$ of geodesics from $p$ to $q$ with three properties. Each geodesic from $p$ to $q$ agrees on $[0, 1]$ with an entry of exactly one list, and the entries of a list are distinct on $[0, 1]$. The energies increase strictly from one list to the next. $\Omega(N; p, q)$ has the homotopy type of the countable cell complex with one cell of dimension $\operatorname{index}(\gamma)$ for each entry $\gamma$, attached list by list ⟦Chapter10/FundamentalTheorem · theorem_17_3⟧. Here the index of a geodesic is taken as a natural number ⟦Chapter10/FundamentalTheorem · geodesicIndex⟧ ⟦Chapter10/FundamentalTheorem · geodesicIndex_eq⟧. "Has the homotopy type of a countable cell complex" means: homotopy equivalent to the mapping telescope of a tower of cell attachments with the given cells ⟦Appendix/MonotoneUnion · IsCountableCellComplexType⟧ (§0.5; Part XI, §XI.15).

### X.2 Radial geodesics depending smoothly on a parameter

The analytic core of §18 is a statement Milnor never formulates: geodesics depend smoothly on their initial data over a compact time interval. Part VII proved it for a parameter $u \in \mathbb R$, for Lemma 14.4 ⟦Chapter9/GeodesicVariation · raysGood_of_isGeodesicOn⟧. The smoothness of $\exp$ needs parameters in $V \times V$, so the argument is repeated with parameters in an arbitrary real normed space $E$.

*The data.* Let $U_0 \subseteq E$ be open, $u_0 \in U_0$, and let $c, w : E \to V$ be smooth on $U_0$ with $c(u) \in N$ and $P_{c(u)}w(u) = w(u)$ for $u \in U_0$. The *rays* of the family are
$$\mathrm{rays}(u, t) = \exp_{c(u)}(t\,w(u))$$
⟦Chapter11/ExpSmooth · raysE⟧. Say that the rays are *good up to $b$* if there are $\varepsilon, \eta > 0$ with the following three properties. The ball $B(u_0, \varepsilon)$ lies in $U_0$. $\mathrm{rays}$ is smooth on $B(u_0, \varepsilon) \times (-\eta, b + \eta)$. For every $u$ in the ball, $t \mapsto \mathrm{rays}(u, t)$ is a geodesic on $(-\eta, b + \eta)$ ⟦Chapter11/ExpSmooth · RaysGoodE⟧. Good up to $b$ implies good up to every $b' \le b$ ⟦Chapter11/ExpSmooth · RaysGoodE.mono⟧. The time derivative $\partial G/\partial t$ of a map $G$ on $E \times \mathbb R$ is the derivative applied to $(0, 1)$ ⟦Chapter11/ExpSmooth · partialT⟧. It is the derivative of $t \mapsto G(u, t)$ ⟦Chapter11/ExpSmooth · hasDerivAt_partialT⟧ and is smooth where $G$ is, on an open set ⟦Chapter11/ExpSmooth · contDiffOn_partialT⟧. On an open set where $\mathrm{rays}$ is smooth, the velocity of the $u$-ray at time $t$ is $\partial\,\mathrm{rays}/\partial t\,(u, t)$ ⟦Chapter11/ExpSmooth · deriv_raysE_eq⟧.

*The local flow.* For $x_1 \in N$ and $R > 0$ there are an open $U \ni x_1$ of $V$, an $h > 0$ and a map $\Phi(y, w, t)$, smooth on $U \times B_R(0) \times (-h, h)$, with the following property. For $y \in N \cap U$ and $w \in T_yN$ with $\|w\| < R$, the curve $t \mapsto \exp_y(tw)$ is a geodesic on $(-h, h)$ and equals $\Phi(y, w, t)$ there ⟦Chapter9/GeodesicVariation · exists_smooth_ray⟧. This is Lemma 10.2 with smooth dependence on the initial data ⟦Chapter7/GeodesicLocal · lemma_10_2⟧, rescaled by $\exp_y(tw) = \exp_y((t/\kappa)(\kappa w))$ so that every speed below $R$ is admitted.

**The start: the rays are good up to $0$** ⟦Chapter11/ExpSmooth · raysGoodE_zero⟧.

*The proof as formalized.* Apply the local flow at $c(u_0)$ with $R = \|w(u_0)\| + 1$. The map $u \mapsto (c(u), w(u))$ is continuous at $u_0$, so there is $\varepsilon > 0$ such that every $u \in B(u_0, \varepsilon)$ satisfies $u \in U_0$, $c(u) \in U$ and $\|w(u)\| < R$. On $B(u_0, \varepsilon) \times (-h/2, h/2)$ one then has $\mathrm{rays}(u, t) = \Phi(c(u), w(u), t)$, a composite of smooth maps, and each ray is a geodesic on $(-h, h) \supseteq (-h/2, h/2)$. Take $\eta = h/2$.

**One step** ⟦Chapter11/ExpSmooth · RaysGoodE.step⟧. Suppose the rays are good up to $b \ge 0$. Let $\Phi$ on $U_1 \times B_R(0) \times (-h, h)$ be a local flow as above, such that the base ray at time $b$ lies in $U_1$ and has speed $< R$. Then the rays are good up to $b + h/2$.

*The proof as formalized.*

1. Let $\varepsilon, \eta$ be the constants for $b$. Put $F(u) = \mathrm{rays}(u, b)$ and $G(u) = \partial\,\mathrm{rays}/\partial t\,(u, b)$, the position and the velocity of the $u$-ray at time $b$. Both are smooth on $B(u_0, \varepsilon)$, as restrictions of smooth maps to the slice $t = b$.
2. By continuity at $u_0$ there is $\varepsilon' > 0$ with $B(u_0, \varepsilon') \subseteq B(u_0, \varepsilon)$, $F(u) \in U_1$ and $\|G(u)\| < R$ for $u \in B(u_0, \varepsilon')$.
3. For such $u$, $F(u) \in N$ and $G(u) \in T_{F(u)}N$, since they are the position and velocity of a geodesic. $(F(u), G(u))$ is the geodesic flow of $(c(u), w(u))$ at time $b$ ⟦Chapter7/GeodesicFlow · geoFlow⟧ ⟦Chapter9/GeodesicVariation · geoFlow_eq_exp⟧. The local flow makes $t \mapsto \exp_{F(u)}(t\,G(u))$ a geodesic on $(-h, h)$. The gluing lemma for geodesics ⟦Chapter7/GeodesicFlow · isGeodesicOn_exp_smul_union⟧ then shows that the $u$-ray is a geodesic on $(-\eta, b + \eta) \cup (b - h, b + h)$, and that its position at time $t \in (b - h, b + h)$ is the position at time $t - b$ of the flow from $(F(u), G(u))$, that is $\Phi(F(u), G(u), t - b)$.
4. Put $\eta' = \min(\eta, h/4)$. Then $(-\eta', b + h/2 + \eta') \subseteq (-\eta, b + \eta) \cup (b - h, b + h)$, so every ray with $u \in B(u_0, \varepsilon')$ is a geodesic on the new interval.
5. Smoothness is checked near each point $(u, t)$. If $t < b + \eta$, the point lies in the old box, where $\mathrm{rays}$ is smooth. If $t \ge b + \eta$, it lies in $B(u_0, \varepsilon') \times (b - h, b + h)$, where $\mathrm{rays}(u, t) = \Phi(F(u), G(u), t - b)$ is smooth. A map smooth near every point of a set is smooth on it ⟦Mathlib/Analysis/Calculus/ContDiff/Defs · contDiffOn_of_locally_contDiffOn⟧.

**Smooth dependence over a compact interval** ⟦Chapter11/ExpSmooth · raysGoodE_of_isGeodesicOn⟧. If the base ray $t \mapsto \exp_{c(u_0)}(t\,w(u_0))$ is a geodesic on $(-\delta, B + \delta)$, with $B \ge 0$ and $\delta > 0$, then the rays are good up to $B$.

*The proof as formalized.* Let $S$ be the set of $b \in [0, B]$ up to which the rays are good. It contains $0$; let $b_0 = \sup S \in [0, B]$. The base ray $\gamma_0$ is a geodesic near $b_0$. Apply the local flow at $\gamma_0(b_0)$ with $R = \|\gamma_0'(b_0)\| + 1$, obtaining $U_1$, $h$ and $\Phi$. Since $t \mapsto (\gamma_0(t), \gamma_0'(t))$ is continuous, there is $r > 0$ such that $\gamma_0(t) \in U_1$ and $\|\gamma_0'(t)\| < R$ for $|t - b_0| < r$. Choose $s \in S$ with $s > b_0 - \min(r, h/4)$. The step at $s$ shows that the rays are good up to $s + h/2$, hence up to $\min(s + h/2, B)$, which therefore belongs to $S$ and is at most $b_0$. But $s + h/2 > b_0 + h/4 > b_0$, so the minimum is $B$, and $B \in S$. A supremum argument takes the place of a finite cover of $[0, B]$.

### X.3 The exponential map is smooth on its whole domain

Milnor applies the notion of a critical point to $\exp_p$ on all of $TM_p$ (p. 98), so he treats it as smooth there. Part VI proves smoothness of $\exp$ only near the zero section, from Lemma 10.2 (Part VI, §VI.7) ⟦Chapter7/Exp · contMDiffOn_exp⟧. This section proves it on the whole domain, without completeness.

**A smooth retraction onto $N$** ⟦Chapter11/ExpSmooth · exists_retraction⟧. Every $p \in N$ has an open neighbourhood $U$ in $V$ with a map $r$, smooth on $U$, with values in $N$ and fixing the points of $N \cap U$.

*Proof.* Take the slice chart $\sigma$ chosen at $p$ ⟦Chapter6/Projection · sliceAt⟧ and put $r(y) = \sigma^{-1}(\sigma(y)_Z, 0)$, the local parametrization of $N$ ⟦Chapter1/ManifoldSubmanifold · sliceParam⟧ applied to the $Z$-component of $\sigma(y)$. On the open set where $\sigma$ is defined and $\sigma(y)_Z$ lies in the target of the induced chart of $N$, $r$ is smooth ⟦Chapter1/ManifoldSubmanifold · contDiffOn_sliceParam⟧ and has values in $N$ ⟦Chapter1/ManifoldSubmanifold · sliceParam_mem⟧. For $y \in N$ it gives $y$ back ⟦Chapter1/ManifoldSubmanifold · sliceParam_toChart⟧.

The tangent bundle is $TN = \{(y, w) : y \in N,\ w \in T_yN\}$ ⟦Milnor/Chapter8/TangentBundle · tangentBundleSet⟧. It is a slice submanifold of $V \times V$ modelled on $Z \times Z$ ⟦Milnor/Chapter8/TangentBundle · isSliceSubmanifold_tangentBundle⟧. The domain of $\exp$ lies in $TN$, because a geodesic from $(q, v)$ has $q = \gamma(0) \in N$ and $v = \gamma'(0)$ tangent ⟦Chapter11/ExpSmooth · expDom_subset_tangentBundleSet⟧. Conversely, a point $(y, w)$ of $TN$ lies in the domain as soon as $t \mapsto \exp_y(tw)$ is a geodesic on some $(-\eta, 1 + \eta)$. The curve itself is then the required geodesic, with value $y$ and velocity $w$ at $0$ ⟦Chapter11/ExpSmooth · mem_expDom_of_isGeodesicOn⟧.

**Theorem ($\exp$ is smooth on its domain)** ⟦Chapter11/ExpSmooth · exists_contDiffOn_exp⟧. For every $(p, v)$ in the domain of $\exp$ there are an open $O \subseteq V \times V$ containing $(p, v)$ and a map $F$, smooth on $O$, such that every point $z$ of $TN \cap O$ lies in the domain and $\exp(z) = F(z)$.

*The proof as formalized.*

1. $(p, v) \in TN$. Take a retraction $r$ on $U \ni p$.
2. The parameter space is $E = V \times V$ with $U_0 = U \times V$. The data are $c(y, x) = r(y)$ and $w(y, x) = P_{r(y)}x$. The first is smooth with values in $N$. The second is smooth, because the projection along a smooth map into $N$ is smooth ⟦Chapter8/Energy · ContDiffOn.prj_comp⟧, and it is tangent at $r(y)$. On $TN \cap U_0$ the data are the identity: $r(y) = y$ for $y \in N$, and $P_y x = x$ for $x \in T_yN$.
3. The base ray $t \mapsto \exp_p(tv)$ is a geodesic on some $(-\delta, 1 + \delta)$ ⟦Chapter7/Exp · IsGeodesicFrom.isGeodesicOn_exp_smul⟧. By X.2 with $B = 1$ there are $\varepsilon, \eta > 0$ such that $\mathrm{rays}$ is smooth on $B((p, v), \varepsilon) \times (-\eta, 1 + \eta)$ and every ray from the ball is a geodesic on $(-\eta, 1 + \eta)$.
4. Take $O = B((p, v), \varepsilon)$ and $F(z) = \mathrm{rays}(z, 1)$, smooth on $O$. For $z = (y, x) \in O \cap TN$, the ray of the data is $t \mapsto \exp_y(tx)$, a geodesic on $(-\eta, 1 + \eta)$. So $z$ lies in the domain, and $\exp_y(x) = \mathrm{rays}(z, 1) = F(z)$.

Two consequences follow. The domain of $\exp$ is $O' \cap TN$ for an open $O' \subseteq V \times V$, namely the union of the sets $O$ chosen at the points of the domain ⟦Chapter11/ExpSmooth · exists_isOpen_expDom⟧. And for the manifold structure of $TN$, $\exp$ is smooth at every point of its domain ⟦Chapter11/ExpSmooth · contMDiffOn_exp_expDom⟧: near such a point it agrees, on the open set of points of $TN$ lying in $O$, with $F$ composed with the smooth inclusion $TN \to V \times V$.

### X.4 The exponential map at one point

For $q \in N$ the domain of $\exp_q$ is $\mathcal D_q = \{v \in T_qN : (q, v) \in \text{domain of } \exp\}$ ⟦Chapter11/ExpSmooth · expDomAt⟧. It contains $0$ ⟦Chapter11/ExpSmooth · zero_mem_expDomAt⟧. It is star-shaped about $0$ ⟦Chapter11/ExpSmooth · smul_mem_expDomAt⟧: if $\gamma$ is a geodesic from $q$ with velocity $v$, then for $0 \le t \le 1$ the curve $s \mapsto \gamma(ts)$ is a geodesic from $q$ with velocity $tv$ ⟦Chapter7/Exp · IsGeodesicFrom.exp_smul⟧. Near each $v \in \mathcal D_q$, $\exp_q$ is the restriction of a smooth map ⟦Chapter11/ExpSmooth · exists_contDiffAt_expAt⟧: compose the $F$ of X.3 with the affine map $y \mapsto (q, y)$, which sends $T_qN$ into $TN$, and take the preimage of $O$. Hence $\mathcal D_q$ is open in $T_qN$ ⟦Chapter11/ExpSmooth · isOpen_expDomAt⟧, and $\exp_q$ is smooth on it as a map from the vector space $T_qN$ to $V$ ⟦Chapter11/ExpSmooth · contDiffOn_expAt⟧. For $v \in \mathcal D_q$ the *radial geodesic* $\gamma_v(t) = \exp_q(tv)$ is a geodesic on some $(-\delta, 1 + \delta)$ ⟦Chapter11/ExpSmooth · isGeodesicOn_ray⟧ and a smooth curve on $[0, 1]$ ⟦Chapter11/ExpSmooth · isSmoothCurveIn_ray⟧. If $N$ is geodesically complete, $\mathcal D_q = T_qN$ ⟦Chapter11/NonConjugate · expDomAt_eq_univ⟧, which is Milnor's setting.

The derivative of $\exp_q$ at $v$ is the linear map $d(\exp_q)_v : T_qN \to V$ ⟦Chapter11/ExpSmooth · dExpAt⟧ ⟦Chapter11/ExpSmooth · dExpAt_apply⟧. This is Milnor's $\exp_*$ on $T(TM_p)_v$, with $T(TM_p)_v$ identified with $TM_p$, as he does on p. 99 when he differentiates along paths $v(u)$ in $TM_p$. $\exp_q$ is *critical* at $v$ when $d(\exp_q)_v$ is not one-to-one. Milnor's $\exp_*$ takes values in the tangent space of $M$ at $\exp v$, the formal one in $V$; whether a linear map is one-to-one does not depend on the space that receives its values.

### X.5 Theorem 18.1

Milnor's proof (pp. 98–99) has two halves. If $\exp_*X = 0$ with $X \ne 0$, a path $v(u)$ in $TM_p$ with $v(0) = v$ and $dv/du(0) = X$ gives the variation $\alpha(u, t) = \exp(t\,v(u))$ through geodesics. Its variation field is a Jacobi field that vanishes at both ends and has non-zero initial derivative. Conversely, if $\exp_*$ is non-singular at $v$, the Jacobi fields built from a basis $X_1, \ldots, X_n$ have independent values at $\exp v$, and a count of dimensions shows that no non-trivial Jacobi field vanishes at both ends. The formal proof takes the straight path $v(u) = v + uX$ and writes its variation field down.

**Definition** ⟦Chapter11/ExpSmooth · expJacobi⟧. For $q \in N$ and $v, X \in T_qN$ put
$$W_X(t) = t\,d(\exp_q)_{tv}(X) \qquad (0 \le t \le 1),$$
extended to be constant off $[0, 1]$ (the formula is applied to the point of $[0, 1]$ nearest to $t$) ⟦Chapter11/ExpSmooth · expJacobi_apply_of_mem⟧. The definition packages $X \mapsto W_X$ as a linear map from $T_qN$ to fields along $\gamma_v$. Directly from the formula, $W_X(0) = 0$ ⟦Chapter11/ExpSmooth · expJacobi_zero⟧ and $W_X(1) = d(\exp_q)_v(X)$ ⟦Chapter11/ExpSmooth · expJacobi_one⟧.

**Lemma ($W_X$ is a Jacobi field)** ⟦Chapter11/ExpSmooth · isJacobiField_expJacobi⟧. For $v \in \mathcal D_q$ and $X \in T_qN$, $W_X$ is a Jacobi field along $\gamma_v$.

*The proof as formalized.*

1. Let $g(u, t) = t(v + uX)$, a smooth map $\mathbb R^2 \to T_qN$, and $\alpha(u, t) = \exp_q(g(u, t))$, Milnor's variation. The compact set $\{0\} \times [0, 1]$ is mapped by $g$ into the open set $\mathcal D_q$, because $g(0, t) = tv$ and $\mathcal D_q$ is star-shaped. The generalized tube lemma ⟦Mathlib/Topology/Compactness/Compact · generalized_tube_lemma⟧ gives open sets $U' \ni 0$ and $T' \supseteq [0, 1]$ with $g(U' \times T') \subseteq \mathcal D_q$. Shrinking $U'$ to an interval $(-\varepsilon, \varepsilon)$ gives a box $(-\varepsilon, \varepsilon) \times [0, 1]$ on which $g$ lands in $\mathcal D_q$. Milnor does not mention this step, but without it his variation is not defined on any such box.
2. On the box $(-\varepsilon, \varepsilon) \times [0, 1]$, $\alpha$ is smooth, as a composite of $g$ with $\exp_q$, which is smooth on $\mathcal D_q$. It has values in $N$, because $\exp$ maps its domain into $N$.
3. For $|u| < \varepsilon$ the point $v + uX = g(u, 1)$ lies in $\mathcal D_q$. Its radial geodesic, which is $\alpha(u, \cdot)$, is a geodesic on an interval containing $[0, 1]$, hence on $(0, 1)$.
4. Lemma 14.3 ⟦Chapter9/JacobiVariation · lemma_14_3⟧ (Part VII) now says that $t \mapsto \partial\alpha/\partial u\,(0, t)$ is a Jacobi field along $\alpha(0, \cdot) = \gamma_v$.
5. For $t \in [0, 1]$, $u \mapsto t(v + uX)$ has derivative $tX$ at $u = 0$, and $\exp_q$ is differentiable at $tv \in \mathcal D_q$. The chain rule gives $\partial\alpha/\partial u\,(0, t) = d(\exp_q)_{tv}(tX) = W_X(t)$. A Jacobi field depends only on its values on $[0, 1]$, so $W_X$ is one.

**Lemma ($DW_X/dt\,(0) = X$)** ⟦Chapter11/ExpSmooth · covAlong_expJacobi_zero⟧. For every $v, X \in T_qN$ the covariant derivative of $W_X$ along $\gamma_v$ at $t = 0$ is $X$.

*The proof as formalized.* The domain $\mathcal D_q$ is open and contains $0$, so $\exp_q$ is smooth near $0$, and $t \mapsto d(\exp_q)_{tv}(X)$ is differentiable at $t = 0$. By the product rule, the derivative of $t \mapsto t\,d(\exp_q)_{tv}(X)$ at $0$ is $d(\exp_q)_0(X)$; the second term carries the factor $t = 0$. This is also the derivative within $[0, 1]$. Since $d(\exp_q)_0$ is the inclusion ⟦Chapter7/Exp · hasFDerivAt_exp_zero⟧, the derivative is $X$. The covariant derivative projects it by $P_{\gamma_v(0)} = P_q$, which fixes $X$.

Milnor obtains $DW/dt(0) = D/du\,v(u)$ from the symmetry lemma 8.7 and the covariant derivative along the constant curve $u \mapsto \alpha(u, 0) = p$. The formal proof needs neither, because $W_X$ is known explicitly and $d(\exp_q)_0$ is the identity.

So $W_X$ belongs to $\mathcal J(\gamma_v)$ ⟦Chapter11/ExpSmooth · expJacobi_mem_jacobiSpace⟧; it was built to be constant off $[0, 1]$. The linear map $X \mapsto W_X$ is injective ⟦Chapter11/ExpSmooth · expJacobi_injective⟧, since $X$ is recovered as $DW_X/dt(0)$.

**Lemma (every Jacobi field vanishing at $0$ is a $W_X$)** ⟦Chapter11/ExpSmooth · eq_expJacobi⟧. If $J \in \mathcal J(\gamma_v)$ and $J(0) = 0$, then $J = W_X$ with $X = DJ/dt(0)$.

*Proof.* $X = DJ/dt(0)$ is a projection onto $T_{\gamma_v(0)}N = T_qN$ ⟦Chapter8/Energy · prj_mem⟧, so $W_X$ is defined. $J$ and $W_X$ both vanish at $0$ and have covariant derivative $X$ there. The map $J \mapsto (J(0), DJ/dt(0))$ is injective on $\mathcal J(\gamma_v)$ ⟦Chapter9/JacobiSpace · jacEval_bijective⟧, which is Milnor's statement that a Jacobi field is determined by these two vectors (p. 77; Corollary 14.B of the exposition). Hence $J = W_X$.

**Theorem (the fields vanishing at both ends)** ⟦Chapter11/ExpSmooth · conjSpace_eq_map_ker⟧. For $v \in \mathcal D_q$, the fields of $\mathcal J(\gamma_v)$ vanishing at $0$ and $1$ are exactly the $W_X$ with $X \in \ker d(\exp_q)_v$.

*Proof.* If $J$ vanishes at $0$ and $1$, then $J = W_X$ by the last lemma, and $0 = J(1) = W_X(1) = d(\exp_q)_v(X)$. Conversely, for $X$ in the kernel, $W_X \in \mathcal J(\gamma_v)$, $W_X(0) = 0$ and $W_X(1) = d(\exp_q)_v(X) = 0$.

**Theorem 18.1, with the multiplicity** ⟦Chapter11/ExpSmooth · theorem_18_1_multiplicity⟧. Let $q \in N$ and $v \in \mathcal D_q$. The multiplicity of $0$ and $1$ as conjugate parameters along $\gamma_v(t) = \exp_q(tv)$ equals $\dim \ker d(\exp_q)_v$.

*Proof.* The space whose dimension is the multiplicity is the image of $\ker d(\exp_q)_v$ under the injective linear map $X \mapsto W_X$, and an injective linear map preserves dimension.

**Theorem 18.1** ⟦Chapter11/ExpSmooth · theorem_18_1⟧. Let $q \in N$ and $v \in \mathcal D_q$. Then $\exp_q(v)$ is conjugate to $q$ along $\gamma_v$, that is, the parameters $0$ and $1$ are conjugate, if and only if $\exp_q$ is critical at $v$.

*Proof.* The parameters $0 \ne 1$ of $[0, 1]$ are conjugate if and only if the multiplicity is positive ⟦Chapter9/JacobiSpace · isConjugate_iff⟧. By the previous theorem this means $\ker d(\exp_q)_v \ne 0$, that is, $d(\exp_q)_v$ is not one-to-one.

Milnor's dimension count for the converse is replaced by the bijectivity of $J \mapsto (J(0), DJ/dt(0))$, and completeness is not assumed: $v$ ranges over the open, star-shaped domain $\mathcal D_q$. The equality of the multiplicity with the nullity of $\exp_*$ is a strengthening that Milnor does not state.

### X.6 The conjugate locus and Corollary 18.2

**Definition** ⟦Chapter11/NonConjugate · conjLocus⟧. For $p \in V$, the *conjugate locus* $C(p)$ is the set of $q$ for which there is a smooth curve $\gamma$ on $[0, 1]$, a geodesic on $(0, 1)$, with $\gamma(0) = p$ and $\gamma(1) = q$, along which $0$ and $1$ are conjugate. Conjugacy depends only on $\gamma$ on $[0, 1]$ ⟦Chapter11/NonConjugate · IsConjugate.congr_curve⟧ ⟦Chapter11/NonConjugate · IsConjugate.congr_curve_iff⟧, because the Jacobi equation does ⟦Chapter9/JacobiVariation · IsJacobiField.congr_curve⟧.

Milnor states that Corollary 18.2 follows at once from 18.1 and Sard's theorem (p. 99). Three facts are hidden in this. Every geodesic from $p$ must be a radial geodesic, so that its conjugate points are critical values of $\exp_p$. $\exp_p$ must be smooth on its whole domain (X.3). And without completeness the domain must be open (X.4).

**Theorem (18.1 along any geodesic from $p$)** ⟦Chapter11/NonConjugate · theorem_18_1_of_geodesic⟧. Let $p \in N$ and let $\gamma$ be a smooth curve on $[0, 1]$, a geodesic on $(0, 1)$, with $\gamma(0) = p$. Then its initial velocity $v = \gamma'(0)$ lies in $T_pN$ and in $\mathcal D_p$, $\exp_p(v) = \gamma(1)$, and $\gamma(1)$ is conjugate to $p$ along $\gamma$ if and only if $\exp_p$ is critical at $v$.

*The proof as formalized.* A geodesic segment extends past its end points and is radial ⟦Chapter9/GeodesicVariation · exists_initial_ray⟧ (Part VII): there is $\eta > 0$ such that $t \mapsto \exp_p(tv)$ is a geodesic on $(-\eta, 1 + \eta)$ that agrees with $\gamma$ on $[0, 1]$. The velocity of a smooth curve in $N$ is tangent ⟦Chapter9/JacobiSystem · IsSmoothCurveIn.velAlong_mem⟧, so $v \in T_pN$. The ray is a geodesic on an interval containing $[0, 1]$, so $v \in \mathcal D_p$, and $\exp_p(v)$, the ray at $t = 1$, is $\gamma(1)$. Conjugacy along $\gamma$ is conjugacy along the ray, which agrees with $\gamma$ on $[0, 1]$, and Theorem 18.1 applies to the ray.

**Theorem (the conjugate locus is the set of critical values of $\exp_p$)** ⟦Chapter11/NonConjugate · conjLocus_eq⟧. For $p \in N$,
$$C(p) = \exp_p\big(\{x \in \mathcal D_p : d(\exp_p)_x \text{ is not one-to-one}\}\big).$$

*Proof.* If $q \in C(p)$ through $\gamma$, the previous theorem gives $v \in \mathcal D_p$, critical, with $\exp_p(v) = \gamma(1) = q$. Conversely, for a critical $x \in \mathcal D_p$, the radial geodesic $\gamma_x$ is a smooth curve on $[0, 1]$ and a geodesic on $(0, 1)$, running from $p$ to $\exp_p(x)$, along which $0$ and $1$ are conjugate by Theorem 18.1. If $N$ is geodesically complete, $C(p)$ is the set of critical values of $\exp_p : T_pN \to N$ ⟦Chapter11/NonConjugate · conjLocus_eq_of_complete⟧.

**Corollary 18.2** ⟦Chapter11/NonConjugate · corollary_18_2⟧. Let $p \in N$, let $\sigma$ be any slice chart of $N$, and let $\mu$ be any Haar measure on $Z$ for the Borel $\sigma$-algebra. Then the image of $C(p) \cap \operatorname{dom}\sigma$ under the chart $y \mapsto \sigma(y)_Z$ of $N$ has $\mu$-measure $0$.

The book never defines "measure zero" in a manifold. Its Sard theorem (6.1) states the conclusion in these words, but §6 applies it only to maps into $\mathbb R^n$, and §18 is the first place where the target is a manifold. The formal statement reads the phrase in every chart: almost every $q$ means every $q$ outside a set whose image in every slice chart is null for every Haar measure.

*The proof as formalized.*

1. $T = T_pN$ has dimension $n = \dim Z$, so there is a linear isomorphism $e : Z \to T$ ⟦Mathlib/Topology/Algebra/Module/FiniteDimension · ContinuousLinearEquiv.ofFinrankEq⟧.
2. Let $U' = e^{-1}(\mathcal D_p) \cap (\exp_p \circ e)^{-1}(\operatorname{dom}\sigma)$, an open subset of $Z$ by continuity. On it the map $g(z) = \sigma(\exp_p(e z))_Z$ is smooth, because the slice chart is smooth on its domain ⟦Milnor/Chapter8/TangentBundle · sliceChart_contDiffOn⟧.
3. Sard's theorem of the companion project ⟦Milnor/Chapter3/Sard · sard⟧ says that $g$ maps the set of points of $U'$ where $dg$ is not onto ⟦Milnor/Chapter3/Basic · Sard.critSet⟧ to a $\mu$-null set. It remains to show that the chart image of $C(p) \cap \operatorname{dom}\sigma$ lies in this image.
4. Let $y \in C(p) \cap \operatorname{dom}\sigma$. By the previous theorem $y = \exp_p(x)$ with $x \in \mathcal D_p$ critical. Then $z = e^{-1}x \in U'$ and $g(z) = \sigma(y)_Z$. By the chain rule $dg_z = \mathrm{pr}_Z \circ d\sigma_y \circ d(\exp_p)_x \circ e$. If $dg_z$ were onto, then, being an endomorphism of the finite-dimensional space $Z$, it would also be one-to-one. But $d(\exp_p)_x(a) = d(\exp_p)_x(b)$ gives $dg_z(e^{-1}(a - b)) = 0$, hence $a = b$, so $d(\exp_p)_x$ would be one-to-one, against the choice of $x$. So $dg_z$ is not onto and $\sigma(y)_Z \in g(\text{critical set})$.

Milnor's Sard theorem is stated for $C^1$ maps; the companion project proves it for smooth maps, which is the case here.

**Theorem (non-conjugate points are dense)** ⟦Chapter11/NonConjugate · dense_compl_conjLocus⟧. For $p \in N$, the points of $N$ not conjugate to $p$ along any geodesic are dense in $N$.

This is what §18 is for: Milnor's justification of Theorem 17.3 rests on the existence of such points. From measure zero to existence one more fact is needed: a null set has empty interior.

*The proof as formalized.* Give $Z$ its Borel $\sigma$-algebra and the Haar measure $\mu$ of a basis. Let $U$ be an open subset of $N$ containing a point $q$, and $\sigma$ the slice chart at $q$. The chart of $N$ induced by $\sigma$ is a partial homeomorphism, so the image $O$ of $U \cap \operatorname{dom}\sigma$ is open in $Z$, and it is non-empty. A non-empty open set has positive Haar measure ⟦Mathlib/MeasureTheory/Measure/OpenPos · IsOpen.measure_pos⟧, so $O$ is not contained in the null set of Corollary 18.2. A point of $O$ outside that set is the image of some $y \in U \cap \operatorname{dom}\sigma$, and $y \notin C(p)$, since otherwise its image would lie in the null set.

**Theorem (non-degeneracy off the conjugate locus)** ⟦Chapter11/NonConjugate · hessNullity_eq_zero_of_notMem_conjLocus⟧. If $q \notin C(p)$, then $E_{**}$ has nullity $0$ at every unbroken geodesic $\gamma \in \Omega(N; p, q)$.

*Proof.* A positive nullity makes $0$ and $1$ conjugate (Theorem 14.1), and $\gamma$, a smooth curve from $p$ to $q$ and a geodesic on $(0, 1)$, would put $q$ in $C(p)$.

This is the hypothesis of Theorems 16.3 and 17.3, and Part IX, §IX.6, states Theorem 17.3 in this form ⟦Chapter10/FundamentalTheorem · theorem_17_3_nonconj⟧. With the density theorem it holds for a dense set of $q$, and with Corollary 18.2 for almost every $q$.

### X.7 Lemma 19.1 and non-positive curvature

**Definition** ⟦Chapter11/Curvature · NonposCurvature⟧. $N$ has *non-positive curvature* if $\langle R(A, B)A, B\rangle \le 0$ for all $A, B \in T_qN$ and all $q \in N$, which is Milnor's hypothesis in Lemma 19.1. This says exactly that every sectional curvature is $\le 0$ ⟦Chapter11/Curvature · nonposCurvature_iff_sectionalCurvature⟧, for the sectional curvature
$$K(A, B) = \frac{\langle R(A, B)A, B\rangle}{\|A\|^2\|B\|^2 - \langle A, B\rangle^2}$$
of independent $A, B$ ⟦Chapter6/CurvatureAlgebra · sectionalCurvature⟧ (Part V, §V.8). For independent $A, B$ the denominator is positive ⟦Chapter6/CurvatureAlgebra · gram_pos⟧, so $K(A, B)$ has the sign of $\langle R(A, B)A, B\rangle$. For dependent $A, B$ the numerator vanishes ⟦Chapter6/CurvatureAlgebra · IsCurvatureTensor.inner_apply_self_eq_zero_of_not_linearIndependent⟧.

**Lemma (the derivative of $\langle DJ/dt, J\rangle$)** ⟦Chapter11/Curvature · hasDerivAt_inner_covAlong⟧. Let $\gamma$ be a smooth curve on $[0, 1]$ and $J$ a Jacobi field along it. For $t \in (0, 1)$,
$$\frac{d}{dt}\Big\langle \frac{DJ}{dt}, J\Big\rangle = \Big\|\frac{DJ}{dt}\Big\|^2 - \langle R(V, J)V, J\rangle.$$

*The proof as formalized.* On the open interval $(0, 1)$ the derivative within $[0, 1]$ is the ordinary one, so $DJ/dt = P J'$ there, a smooth function. The product rule gives
$$\frac{d}{dt}\langle PJ', J\rangle = \langle (PJ')', J\rangle + \langle PJ', J'\rangle .$$
For the first term, $J = PJ$ because $J$ is tangent, and $P$ is self-adjoint, so $\langle (PJ')', J\rangle = \langle P(PJ')', J\rangle = \langle D^2J/dt^2, J\rangle$. By the Jacobi equation this equals $-\langle R(V, J)V, J\rangle$. For the second term, $P$ is idempotent and self-adjoint, so $\langle PJ', J'\rangle = \langle PJ', PJ'\rangle = \|DJ/dt\|^2$. Milnor writes the same derivative as $\langle D^2J/dt^2, J\rangle + \|DJ/dt\|^2$.

The covariant derivative within $[0, 1]$ of a field smooth on $[0, 1]$ is continuous on $[0, 1]$, ends included ⟦Chapter11/Curvature · continuousOn_covAlong⟧, because $t \mapsto P_{\gamma(t)}$ is smooth on $[0, 1]$ ⟦Chapter9/JacobiSystem · IsSmoothCurveIn.contDiffOn_prj⟧.

**Lemma (the key step of 19.1)** ⟦Chapter11/Curvature · IsJacobiField.eqOn_zero_of_nonpos⟧. Let $N$ have non-positive curvature, let $\gamma$ be a smooth curve on $[0, 1]$ that is a geodesic on $(0, 1)$, and let $J$ be a Jacobi field along $\gamma$ with $J(a) = J(b) = 0$ for some $0 \le a < b \le 1$. Then $J = 0$ on $[0, 1]$.

*The proof as formalized.*

1. Let $g = \langle DJ/dt, J\rangle$. For $t \in (a, b) \subseteq (0, 1)$, $V(t)$ is the velocity of a geodesic, so it is tangent, and $J(t)$ is tangent. The hypothesis gives $\langle R(V, J)V, J\rangle \le 0$, and the last lemma gives $g'(t) \ge \|DJ/dt(t)\|^2 \ge 0$.
2. $g$ is continuous on $[a, b]$, by the continuity of $DJ/dt$ and of $J$, and its derivative inside is $\ge 0$, so it is monotone there ⟦Mathlib/Analysis/Calculus/Deriv/MeanValue · monotoneOn_of_deriv_nonneg⟧. As $g(a) = g(b) = 0$, $g$ vanishes on $[a, b]$.
3. On $(a, b)$, $g$ is locally constant, so $g' = 0$ and $\|DJ/dt\|^2 \le g' = 0$. Hence $DJ/dt = 0$ on $(a, b)$.
4. At $a$: the interval $(a, b)$ is non-empty and accumulates at $a$, and $DJ/dt$ is continuous at $a$. Its limit from the right is therefore both $DJ/dt(a)$ and $0$, so $DJ/dt(a) = 0$.
5. $J(a) = 0$ and $DJ/dt(a) = 0$, so $J = 0$ on $[0, 1]$ ⟦Chapter9/JacobiSystem · IsJacobiField.eqOn_zero⟧.

Milnor observes that $g$ is strictly increasing where $DJ/dt \ne 0$; only the inequality $g' \ge \|DJ/dt\|^2$ is used here. He takes $J(0) = J(t_0) = 0$. Step 4, which passes from $DJ/dt = 0$ on the open interval to the end point, is left implicit in his proof.

**Lemma 19.1** ⟦Chapter11/Curvature · lemma_19_1⟧. If $N$ has non-positive curvature, then along a smooth curve on $[0, 1]$ that is a geodesic on $(0, 1)$, no two parameters $a, b$ are conjugate.

*Proof.* Conjugacy would give a Jacobi field vanishing at $a \ne b$ but not on all of $[0, 1]$. Ordering $a$ and $b$, the key step makes it vanish on $[0, 1]$.

The lemma is local along each geodesic: it needs neither completeness nor compactness. Its consequences for the index form are the first steps of Milnor's proof of 19.2.

**Theorem (index and nullity $0$)** ⟦Chapter11/Curvature · formIndex_eq_zero_of_nonpos⟧. In non-positive curvature every unbroken geodesic $\gamma \in \Omega(N; p, q)$ has index $0$ and nullity $0$.

*Proof.* By the index theorem the index is $\sum_{t \in (0, 1)}$ (multiplicity of $0$ and $t$). Each multiplicity is $0$, since a positive one would make $0$ and $t$ conjugate, against Lemma 19.1. So the sum is $0$. A positive nullity would make $0$ and $1$ conjugate (Theorem 14.1).

**Theorem ($E_{**}$ is positive definite)** ⟦Chapter11/Curvature · energyHessian_pos_of_nonpos⟧. In non-positive curvature, $E_{**}(X, X) > 0$ for every $X \in T\Omega_\gamma$ that does not vanish identically on $[0, 1]$, at every unbroken geodesic $\gamma \in \Omega(N; p, q)$.

*The proof as formalized.* By the integral form, $E_{**}(Y, Y) = 2\int_0^1 (\|DY/dt\|^2 - \langle R(V, Y)V, Y\rangle)\,dt$. The curvature term is $\le 0$ at every $t \in (0, 1)$ by hypothesis, since $Y(t)$ and $V(t)$ are tangent, and it vanishes at $t = 0, 1$, where $Y = 0$. So $E_{**}$ is positive semi-definite. If $E_{**}(X, X) = 0$, then $X$ lies in the kernel of $E_{**}$, by the Cauchy–Schwarz inequality for symmetric semi-definite forms ⟦Mathlib/LinearAlgebra/SesquilinearForm/Basic · apply_apply_same_eq_zero_iff⟧. That is, $E_{**}(X, \cdot) = 0$, so $X$ is a Jacobi field (Theorem 14.1). It vanishes at $0$ and $1$ and not everywhere on $[0, 1]$, so $0$ and $1$ would be conjugate, against Lemma 19.1. Milnor does not state this positivity.

**Theorem ($\exp_p$ is nowhere critical)** ⟦Chapter11/Curvature · injective_dExpAt_of_nonpos⟧. In non-positive curvature, $d(\exp_p)_v$ is one-to-one for every $p \in N$ and every $v \in \mathcal D_p$.

*Proof.* Otherwise Theorem 18.1 makes $0$ and $1$ conjugate along $\gamma_v$, against Lemma 19.1. This is the last step of Milnor's proof of 19.2 (p. 103).

### X.8 The Ricci tensor and Milnor's Assertion

**Definition** ⟦Chapter11/Myers · ricci⟧. The *Ricci tensor* at $q \in N$ is the bilinear form on $T_qN$
$$K(U_1, U_2) = \operatorname{trace}\big(W \mapsto R(U_1, W)U_2\big),$$
the trace of a linear map of $T_qN$. This is Milnor's definition (p. 104) taken literally. In an orthonormal basis $E_1, \ldots, E_n$ of $T_qN$,
$$K(U_1, U_2) = \sum_i \langle R(U_1, E_i)U_2, E_i\rangle$$
⟦Chapter11/Myers · ricci_eq_sum⟧, because the trace of a linear map $T$ is $\sum_i\langle E_i, TE_i\rangle$ ⟦Mathlib/Analysis/InnerProductSpace/Trace · LinearMap.trace_eq_sum_inner⟧.

**Symmetry** ⟦Chapter11/Myers · ricci_comm⟧. $K(U_1, U_2) = K(U_2, U_1)$. Milnor says this follows easily from 9.3. The formal proof computes in an orthonormal basis and uses, term by term, the pair symmetry $\langle R(X, Y)Z, W\rangle = \langle R(Z, W)X, Y\rangle$ of Lemma 9.3 (4) ⟦Chapter6/CurvatureAlgebra · IsCurvatureTensor.inner_comm_pairs⟧, which holds for the curvature tensor of $N$ ⟦Chapter6/Submanifold · isCurvatureTensor_curvTensor⟧. With $X = U_1$, $Y = W = E_i$ and $Z = U_2$ it gives $\langle R(U_1, E_i)U_2, E_i\rangle = \langle R(U_2, E_i)U_1, E_i\rangle$.

**Milnor's Assertion** ⟦Chapter11/Myers · ricci_eq_sum_erase⟧. For an orthonormal basis $(b_i)$ of $T_qN$ and an index $i_0$,
$$K(b_{i_0}, b_{i_0}) = \sum_{i \ne i_0} \langle R(b_{i_0}, b_i)b_{i_0}, b_i\rangle,$$
the sum of the sectional curvatures of the planes spanned by $b_{i_0}$ and the other $b_i$.

*Proof.* As Milnor says, the term $i = i_0$ of the sum in the basis vanishes, because $R(x, x) = 0$ ⟦Chapter11/Myers · curvOp_self⟧: $R(x, x)$ is a difference of two equal compositions of second fundamental forms.

The hypothesis of Myers' theorem is the bound $K(U, U) \ge (n - 1)/r^2$ for every unit vector $U \in T_qN$ and every $q \in N$, with $n = \dim Z$ ⟦Chapter11/Myers · RicciLowerBound⟧.

### X.9 Myers' theorem (Theorem 19.4)

Milnor's proof (pp. 104–105) runs as follows. Take parallel fields $P_1, \ldots, P_n$ along the geodesic $\gamma : [0, 1] \to M$ of length $L$, orthonormal at one point and hence everywhere, with $P_n$ pointing along $\gamma$, so that $V = LP_n$. Put $W_i(t) = \sin(\pi t)P_i(t)$, compute $\tfrac12 E_{**}(W_i, W_i)$, and sum over $i < n$. The sum is $\int_0^1 \sin^2(\pi t)\big((n - 1)\pi^2 - L^2K(P_n, P_n)\big)\,dt$, which is negative when $L > \pi r$. Some $E_{**}(W_i, W_i)$ is then negative, so the index is positive and the index theorem produces a conjugate point. The formal proof follows this outline. It first has to make the parallel frame available. Parallel transport (Part V, §V.19) is built for smooth curves defined on all of $\mathbb R$ ⟦Chapter6/Parallel · IsParallel⟧ ⟦Chapter6/Parallel · parallelField⟧ ⟦Chapter6/Parallel · parallelField_spec⟧, so $\gamma$ is extended beyond $[0, 1]$ first.

**A smooth clamp** ⟦Chapter11/Myers · exists_smooth_clamp⟧. For $a > 0$ there is a smooth $\varphi : \mathbb R \to [-a, 1 + a]$ with $\varphi(t) = t$ on $[0, 1]$, namely
$$\varphi(t) = t + (1 + a - t)\,\tau\Big(\frac{t - 1}{a}\Big) + (-a - t)\,\tau\Big(\frac{-t}{a}\Big),$$
where $\tau$ is Mathlib's smooth transition function: $0$ on $(-\infty, 0]$, $1$ on $[1, \infty)$, with values in $[0, 1]$ ⟦Mathlib/Analysis/SpecialFunctions/SmoothTransition · Real.smoothTransition⟧. On $[0, 1]$ both $\tau$-terms vanish. For $t \le 0$ only the last term can be non-zero; it moves $t$ towards $-a$ by a fraction $\tau \in [0, 1]$ of the distance, and $\varphi(t) = -a$ for $t \le -a$. The case $t \ge 1$ is symmetric. The formal proof checks these inequalities case by case.

**Extension of a geodesic segment** ⟦Chapter11/Myers · exists_smooth_extension⟧. Let $\gamma \in \Omega(N; p, q)$ be an unbroken geodesic of length $L$. There are a smooth curve $c : \mathbb R \to N$ with $c = \gamma$ on $[0, 1]$ and a smooth field $V_f$ along $c$, tangent to $N$, with $V_f = \gamma'$ on $(0, 1)$ and $\|V_f(t)\| = L$ for all $t$, such that $L^{-1}V_f$ is parallel along $c$.

*The proof as formalized.*

1. The radial geodesic $\mathrm{ray}(t) = \exp_{\gamma(0)}(t\gamma'(0))$ is a geodesic on some $(-\eta, 1 + \eta)$ that agrees with $\gamma$ on $[0, 1]$ ⟦Chapter9/GeodesicVariation · exists_initial_ray⟧.
2. $L = \|\mathrm{ray}'(0)\|$. The length of a geodesic on an interval is its constant speed times the length of the interval ⟦Chapter7/Shortest · IsGeodesicOn.pathLength_eq⟧, and $\gamma' = \mathrm{ray}'$ on $(0, 1)$. By constancy of the speed, $\|\mathrm{ray}'(t)\| = L$ on $(-\eta, 1 + \eta)$.
3. Let $\varphi$ be the clamp for $a = \eta/2$, with values in $(-\eta, 1 + \eta)$. Put $c = \mathrm{ray} \circ \varphi$ and $V_f(t) = \mathrm{ray}'(\varphi(t))$. Both are smooth, $c = \gamma$ on $[0, 1]$, $V_f = \gamma'$ on $(0, 1)$, $\|V_f\| = L$, and $V_f(t)$ is tangent at $c(t)$.
4. $L^{-1}V_f$ is parallel along $c$. Its derivative is $L^{-1}\varphi'(t)\,\mathrm{ray}''(\varphi(t))$, and the acceleration of a geodesic has no tangential part ⟦Chapter7/Geodesic · IsGeodesicOn.tanProj_deriv_deriv⟧, so the covariant derivative vanishes. Outside $[0, 1]$ the curve $c$ runs along the geodesic at a varying speed and is in general not a geodesic, but $V_f$ is still parallel along it.

**A parallel frame** ⟦Chapter11/Myers · exists_parallel_frame⟧. Let $\gamma \in \Omega(N; p, q)$ be an unbroken geodesic of length $L > 0$. Take $c$ and $V_f$ as above. Then there are a finite index set $I$, a subset $s \subseteq I$ with $|s| + 1 = n$, and parallel fields $P_i$ along $c$ with $\|P_i(t)\| = 1$, such that for every $r$ with the Ricci bound and every $t$,
$$\sum_{i \in s} \langle R(V_f, P_i)V_f, P_i\rangle(t) \ \ge\ L^2\,\frac{|s|}{r^2}.$$

*The proof as formalized.*

1. $e_0 = L^{-1}V_f(0)$ is a unit vector of $T_{c(0)}N$. Extend $\{e_0\}$ to an orthonormal basis $b$ of $T_{c(0)}N$ ⟦Mathlib/Analysis/InnerProductSpace/PiL2 · Orthonormal.exists_orthonormalBasis_extension⟧, indexed by a finite set $I \ni e_0$; let $i_0$ be the index of $e_0$.
2. Let $P_i$ be the parallel field along $c$ with $P_i(0) = b_i$. Two parallel fields with the same value at one time coincide ⟦Chapter6/Parallel · IsParallel.eq⟧, so $P_{i_0} = L^{-1}V_f$ and $V_f = LP_{i_0}$. This uses that $V_f$ itself is parallel, which Milnor's identity $V = LP_n$ takes for granted.
3. At each $t$, $(P_i(t))_i$ is the image of $b$ under parallel transport from $c(0)$ to $c(t)$, a linear isometry onto $T_{c(t)}N$ ⟦Chapter6/Parallel · parallelTransport⟧ ⟦Chapter6/Parallel · parallelTransport_apply⟧. So it is an orthonormal basis of $T_{c(t)}N$, and $\|P_i(t)\| = 1$. This is why Milnor's frame, orthonormal at one point, is orthonormal everywhere. The Assertion needs it, since the trace is computed in the basis $(P_i(t))$.
4. Let $s = I \setminus \{i_0\}$. Then $|s| + 1 = |I| = \dim T_{c(0)}N = n$.
5. At time $t$, apply the Ricci bound to the unit vector $P_{i_0}(t)$ and the Assertion in the basis $(P_i(t))$: $\sum_{i \in s}\langle R(P_{i_0}, P_i)P_{i_0}, P_i\rangle = K(P_{i_0}, P_{i_0}) \ge (n - 1)/r^2 = |s|/r^2$. Since $V_f = LP_{i_0}$, each term $\langle R(V_f, P_i)V_f, P_i\rangle$ equals $L^2\langle R(P_{i_0}, P_i)P_{i_0}, P_i\rangle$ by linearity ⟦Chapter6/Submanifold · curvOp_smul_left⟧. Multiply by $L^2$.

For smooth $c$ and smooth tangent fields $V_f$, $P$ along it, the function $t \mapsto \langle R(V_f, P)V_f, P\rangle$ is continuous ⟦Chapter11/Myers · continuous_inner_curvR⟧, because $R$ depends smoothly on smooth data ⟦Chapter8/Jacobi · contDiffAt_curvR⟧. So the integrals below exist. Two integrals are needed: $\int_0^1 \sin^2(\pi t)\,dt = \int_0^1 \cos^2(\pi t)\,dt = \tfrac12$ ⟦Chapter11/Myers · integral_sin_sq_pi_mul⟧ ⟦Chapter11/Myers · integral_cos_sq_pi_mul⟧, by the substitution $x = \pi t$ and the primitives of $\sin^2$ and $\cos^2$ ⟦Mathlib/Analysis/SpecialFunctions/Integrals/Basic · integral_sin_sq⟧ ⟦Mathlib/Analysis/SpecialFunctions/Integrals/Basic · integral_cos_sq⟧.

**The test fields** ⟦Chapter11/Myers · energyHessian_sin_parallel⟧. Let $\gamma \in \Omega(N; p, q)$ agree on $[0, 1]$ with a smooth curve $c : \mathbb R \to N$. Let $P$ be parallel along $c$ with $\|P\| = 1$, and let $V_f$ be a field with $V_f = \gamma'$ on $(0, 1)$. Then $W(t) = \sin(\pi t)P(t)$ lies in $T\Omega_\gamma$ and
$$\tfrac12 E_{**}(W, W) = \int_0^1 \big(\pi^2\cos^2(\pi t) - \sin^2(\pi t)\,\langle R(V_f, P)V_f, P\rangle\big)\,dt .$$

*The proof as formalized.* $W$ is smooth, hence piecewise smooth. It is tangent along $\gamma$ on $[0, 1]$, because there $P(t) \in T_{c(t)}N = T_{\gamma(t)}N$. It vanishes at $0$ and $1$, because $\sin 0 = \sin\pi = 0$. In the integral form of $E_{**}$ take $t \in (0, 1)$. Then $W'(t) = \sin(\pi t)P'(t) + \pi\cos(\pi t)P(t)$. The projection kills $P'(t)$, $P$ being parallel, and fixes $P(t)$, so $DW/dt = \pi\cos(\pi t)P(t)$ and $\|DW/dt\|^2 = \pi^2\cos^2(\pi t)$. The curvature term is $\sin^2(\pi t)\langle R(V_f, P)V_f, P\rangle$ by linearity ⟦Chapter6/Submanifold · curvOp_smul_right⟧.

Milnor uses the form $-\int\langle W, D^2W/dt^2 + R(V, W)V\rangle$ of $\tfrac12 E_{**}$ and obtains $\pi^2\sin^2(\pi t)$ where the integral form used here gives $\pi^2\cos^2(\pi t)$. Both integrate to $\pi^2/2$, so nothing else changes.

**The key estimate** ⟦Chapter11/Myers · exists_energyHessian_neg⟧. Let $n \ge 2$, $r > 0$, and let the Ricci curvature satisfy $K(U, U) \ge (n - 1)/r^2$ for all unit vectors $U$. If $\gamma \in \Omega(N; p, q)$ is an unbroken geodesic with $L(\gamma) > \pi r$, there is $X \in T\Omega_\gamma$ with $E_{**}(X, X) < 0$.

*The proof as formalized.*

1. $L > \pi r > 0$, so the parallel frame exists. Let $W_i = \sin(\pi t)P_i$ for $i \in s$ and $k_i(t) = \langle R(V_f, P_i)V_f, P_i\rangle(t)$.
2. By the test-field formula, $\sum_{i \in s} E_{**}(W_i, W_i) = 2\int_0^1 \sum_{i \in s} f_i$ with $f_i = \pi^2\cos^2(\pi t) - \sin^2(\pi t)k_i(t)$. The $f_i$ are continuous, so the sum passes under the integral.
3. Pointwise, $\sum_i f_i = |s|\pi^2\cos^2(\pi t) - \sin^2(\pi t)\sum_i k_i \le |s|\pi^2\cos^2(\pi t) - |s|(L^2/r^2)\sin^2(\pi t) = g(t)$, by the frame estimate and $\sin^2 \ge 0$.
4. $\int_0^1 g = |s|(\pi^2 - L^2/r^2)/2$. Here $|s| = n - 1 \ge 1$, and $\pi^2 < L^2/r^2$ because $L > \pi r > 0$. So the sum of the $E_{**}(W_i, W_i)$ is negative, and one of its terms is negative.

**Theorem 19.4 (Myers)** ⟦Chapter11/Myers · theorem_19_4⟧. Let $n \ge 2$, $r > 0$, and $K(U, U) \ge (n - 1)/r^2$ for every unit vector $U$ at every point of $N$. Then every unbroken geodesic $\gamma \in \Omega(N; p, q)$ of length $> \pi r$ has a parameter $t \in (0, 1)$ conjugate to $0$, and it is not minimal: some path of $\Omega(N; p, q)$ is shorter.

*The proof as formalized.* Take $X$ with $E_{**}(X, X) < 0$; then $X \ne 0$. On the line spanned by $X$, $E_{**}(aX, aX) = a^2E_{**}(X, X) < 0$ for $a \ne 0$, so $E_{**}$ is negative definite there and the index is at least $1$. By the index theorem, the index is the sum over $t \in (0, 1)$ of the multiplicities of $0$ and $t$. If no $t$ were conjugate to $0$, every multiplicity would be $0$ and so would the index. At a minimal geodesic $E_{**}$ is positive semi-definite (Lemma 13.6), which $E_{**}(X, X) < 0$ excludes. Milnor argues instead with a variation along $W_i$ that decreases the energy; Lemma 13.6 packages the same argument.

*A hidden hypothesis: $n \ge 2$.* For $n = 1$ the Ricci tensor vanishes, the sum in the Assertion being empty, and the hypothesis $0 \ge 0$ holds for every $r$. But a segment of a line of length $> \pi r$ has no conjugate points and is minimal. The formal statement assumes $n \ge 2$, and the proof uses it at step 4 of the key estimate.

### X.10 Corollary 19.5 and the sphere

A *minimal geodesic* in Milnor's sense (p. 61) is the restriction to $[0, 1]$ of a geodesic on an open set containing $[0, 1]$, whose length is at most that of every piecewise smooth path in $N$ with the same end points ⟦Chapter7/HopfRinow · IsMinimalGeodesic⟧. Such a $\gamma$ is an unbroken geodesic of $\Omega(N; \gamma(0), \gamma(1))$ of minimal length ⟦Chapter11/Myers · IsMinimalGeodesic.isMinimalPath⟧: being smooth on a neighbourhood of $[0, 1]$, it is piecewise smooth, and the comparison paths are the same.

**Corollary 19.5** ⟦Chapter11/Myers · corollary_19_5⟧. Let $N$ be connected and complete for $\rho$, let $r > 0$ with $(n - 1)/r^2 > 0$, and let $K(U, U) \ge (n - 1)/r^2$ for all unit vectors $U$. Then $\rho(p, q) \le \pi r$ for all $p, q \in N$, and $N$ is compact.

*The proof as formalized.* $(n - 1)/r^2 > 0$ forces $n \ge 2$. The Hopf–Rinow theorem for connected complete $N$ ⟦Chapter7/HopfRinow · hopf_rinow_of_isRiemComplete⟧ (Part VI, §VI.19) gives two things. First, any $p, q$ are joined by a minimal geodesic $\gamma$ on $[0, 1]$ with $\rho(p, q) = L(\gamma)$. Second, closed $\rho$-bounded subsets of $N$ are compact. If $L(\gamma) > \pi r$, Theorem 19.4 says that $\gamma$ is not minimal in $\Omega$, against the first point; so $\rho(p, q) \le \pi r$. Then $N$, closed in itself, is $\rho$-bounded ⟦Chapter7/Metric · IsRiemBounded⟧, hence compact. Connectedness is a hidden hypothesis, needed for minimal geodesics to exist; it is Milnor's standing assumption.

**The unit sphere.** Let $S^n \subseteq \mathbb R^{n+1}$ be the unit sphere, a level set ⟦Milnor/Chapter5/HairyBall · Sph⟧ and a slice submanifold ⟦Milnor/Chapter6/EulerSphere · sphSub⟧. Its curvature is $R(x, y)z = \langle x, z\rangle y - \langle y, z\rangle x$ for tangent $x, y, z$ ⟦Chapter6/SphereCurvature · curvOp_sph⟧ (Part V, §V.21, from the Gauss equation). So $K(U, U) = (n - 1)\|U\|^2$ ⟦Chapter11/Myers · ricci_sph⟧: in an orthonormal basis $(b_i)$ of $T_qS^n$ the terms are $\langle R(U, b_i)U, b_i\rangle = \|U\|^2 - \langle U, b_i\rangle^2$, and their sum is $n\|U\|^2 - \|U\|^2$ by Parseval's identity, since $T_qS^n$ has dimension $n$. Hence the Ricci bound holds with $r = 1$ ⟦Chapter11/Myers · ricciLowerBound_sph⟧. For $n \ge 2$, every unbroken geodesic of $\Omega(S^n; p, q)$ of length $> \pi$ has a parameter in $(0, 1)$ conjugate to $0$ and is not minimal, and $\rho(p, q) \le \pi$ for all $p, q$ ⟦Chapter11/Myers · sphere_myers⟧. This is Theorem 19.4 with $r = 1$, and Corollary 19.5. $S^n$ is connected, a sphere in a space of dimension $n + 1 \ge 2$ ⟦Mathlib/Analysis/Normed/Module/Connected · isConnected_sphere⟧. It is complete because it is compact ⟦Milnor/Chapter6/EulerSphere · isCompact_sph⟧, hence closed in $\mathbb R^{n+1}$. Milnor's sphere of radius $r$ and his remark that the result is best possible are not formalized.

### X.11 Long geodesics have large index

In the proof of 19.6 (p. 106) Milnor shows that a geodesic of length $> k\pi r$ has index $\ge k$. Arguing as for 19.4, he finds, for each $i = 1, \ldots, k$, a field $X_i$ that vanishes outside $((i-1)/k, i/k)$ and has $E_{**}(X_i, X_i) < 0$, and he calls the orthogonality $E_{**}(X_i, X_j) = 0$, $i \ne j$, clear. The formal proof constructs these fields on an arbitrary piece $[a, b] \subseteq [0, 1]$.

*Integrals over pieces.* Let $0 \le a \le b \le 1$. If $G = 0$ on $(0, a)$ and on $(b, 1)$, and $G = F$ on $(a, b)$ with $F$ continuous, then $\int_0^1 G = \int_a^b F$ ⟦Chapter11/LongGeodesics · integral_eq_of_eqOn_pieces⟧: split the integral at $a$ and $b$, and use that integrals over an interval only see the integrand on its interior. If $\kappa(b - a) = \pi$, then $\int_a^b \sin^2(\kappa(t - a))\,dt = \int_a^b \cos^2(\kappa(t - a))\,dt = (b - a)/2$ ⟦Chapter11/LongGeodesics · integral_sin_sq_shift⟧ ⟦Chapter11/LongGeodesics · integral_cos_sq_shift⟧.

**Definition (the field on a piece)** ⟦Chapter11/LongGeodesics · sinBump⟧. For $a < b$, $\kappa = \pi/(b - a)$ and a field $P$, put
$$X(t) = \sin\big(\kappa(\max(a, \min(t, b)) - a)\big)\,P(t).$$
The clamp makes continuity evident. On $[a, b]$, $X(t) = \sin(\kappa(t - a))P(t)$ ⟦Chapter11/LongGeodesics · sinBump_of_mem⟧. For $t \le a$, $X(t) = \sin(0)P(t) = 0$ ⟦Chapter11/LongGeodesics · sinBump_of_le⟧. For $t \ge b$, $X(t) = \sin(\pi)P(t) = 0$ ⟦Chapter11/LongGeodesics · sinBump_of_ge⟧. So $X$ vanishes on a neighbourhood of every $t \notin [a, b]$ ⟦Chapter11/LongGeodesics · sinBump_eventually_zero⟧, and near every $t \in (a, b)$ it agrees with the smooth function $\sin(\kappa(t - a))P(t)$ ⟦Chapter11/LongGeodesics · sinBump_eventuallyEq⟧. Off $[a, b]$ both $X$ and $DX/dt$ vanish ⟦Chapter11/LongGeodesics · covD_sinBump_of_notMem⟧, and $R(x, 0) = 0$ ⟦Chapter11/LongGeodesics · curvOp_zero_right⟧.

**Lemma** ⟦Chapter11/LongGeodesics · sinBump_mem_pathTangent⟧. Let $\gamma = c$ on $[0, 1]$ for a smooth $c : \mathbb R \to N$, let $P$ be parallel along $c$, and let $0 \le a < b \le 1$. Then the field $X$ on $[a, b]$ lies in $T\Omega_\gamma$.

*Proof.* $X$ is continuous. It is piecewise smooth with break points $\{a, b\}$: on an interval whose interior contains neither $a$ nor $b$, it is either identically $0$ (left of $a$ or right of $b$) or equal to the smooth function $\sin(\kappa(t - a))P(t)$. It is tangent, as $P$ is, and it vanishes at $0 \le a$ and at $1 \ge b$.

**Lemma (the energy of a field on a piece)** ⟦Chapter11/LongGeodesics · energyHessian_sinBump⟧. With $P$ parallel of norm $1$, and $V_f$ smooth, tangent and equal to $\gamma'$ on $(0, 1)$,
$$\tfrac12 E_{**}(X, X) = \int_a^b \big(\kappa^2\cos^2(\kappa(t - a)) - \sin^2(\kappa(t - a))\,\langle R(V_f, P)V_f, P\rangle\big)\,dt .$$

*Proof.* In the integral form, the integrand vanishes on $(0, a)$ and $(b, 1)$, where $X$ and $DX/dt$ vanish. On $(a, b)$ it is computed as for the test fields of X.9, with $\kappa$ in place of $\pi$: $DX/dt = \kappa\cos(\kappa(t - a))P$.

**Lemma (orthogonality)** ⟦Chapter11/LongGeodesics · energyHessian_sinBump_disjoint⟧. For fields $X$ on $[a, b]$ and $X'$ on $[a', b']$, built from parallel $P$, $P'$, with $b \le a'$: $E_{**}(X, X') = 0$.

*Proof.* The integrand $\langle DX/dt, DX'/dt\rangle - \langle R(V, X)V, X'\rangle$ vanishes on $(0, a)$ and on $(b, 1)$, where $X$ and $DX/dt$ vanish. It also vanishes on $(a, b)$, where $t < b \le a'$, so that $X'$ and $DX'/dt$ vanish. Only the common end point, a null set, is left. The integral form has no jump terms at the break points, which is why Milnor can treat the orthogonality as evident.

**Lemma (a negative field on each long piece)** ⟦Chapter11/LongGeodesics · exists_sinBump_neg⟧. Let $n \ge 2$, $r > 0$, and let $c, V_f, (P_i)_{i \in s}$ be a parallel frame with the estimate of X.9. If $0 \le a < b \le 1$ and $L(b - a) > \pi r$, then the field on $[a, b]$ built from some $P_i$, $i \in s$, has $E_{**}(X_i, X_i) < 0$.

*Proof.* As in X.9, $\sum_{i \in s} \tfrac12 E_{**}(X_i, X_i)$ is at most
$$|s|\Big(\kappa^2\,\frac{b - a}{2} - \frac{L^2}{r^2}\,\frac{b - a}{2}\Big) = |s|\,\frac{b - a}{2}\,\Big(\kappa^2 - \frac{L^2}{r^2}\Big),$$
which is negative because $|s| \ge 1$ and $\kappa = \pi/(b - a) < L/r$.

**Theorem (the index bound of 19.6)** ⟦Chapter11/LongGeodesics · theorem_19_6_index⟧. Let $n \ge 2$, $r > 0$, $K(U, U) \ge (n - 1)/r^2$ for every unit vector $U$, and let $\gamma \in \Omega(N; p, q)$ be an unbroken geodesic with $L(\gamma) > k\pi r$, $k \in \mathbb N$. Then the index of $E_{**}$ at $\gamma$ is at least $k$.

*The proof as formalized.*

1. For $k = 0$ there is nothing to prove. Otherwise $L > 0$; take the parallel frame of X.9.
2. The pieces $[i/k, (i + 1)/k]$, $i = 0, \ldots, k - 1$, have length $1/k$, and $L/k > \pi r$. For each $i$ the last lemma gives an index $j(i) \in s$ such that the field $Y_i$ on the $i$-th piece built from $P_{j(i)}$ has $E_{**}(Y_i, Y_i) < 0$.
3. For $i < i'$ the pieces satisfy $(i + 1)/k \le i'/k$, so $E_{**}(Y_i, Y_{i'}) = 0$ by orthogonality, and by symmetry also for $i > i'$.
4. Let $\Phi : \mathbb R^k \to T\Omega_\gamma$, $\Phi(x) = \sum_i x_iY_i$. Expanding bilinearly, the cross terms vanish and $E_{**}(\Phi x, \Phi x) = \sum_i x_i^2 E_{**}(Y_i, Y_i)$. For $x \ne 0$, some $x_{i_0} \ne 0$ contributes a negative term and the others contribute terms $\le 0$, so $E_{**}(\Phi x, \Phi x) < 0$.
5. Hence $\Phi$ is injective, since $\Phi x = 0$ gives $E_{**}(\Phi x, \Phi x) = 0$, and $E_{**}$ is negative definite on its $k$-dimensional range. The index is at least $k$.

That the $X_i$ span a $k$-dimensional space, which Milnor takes as evident, is a consequence here, not an extra observation: the fields are non-zero with disjoint supports, and step 4 gives both their independence and the negativity.

Two reformulations follow. A geodesic of index $< k$ has length $\le k\pi r$ ⟦Chapter11/LongGeodesics · pathLength_le_of_formIndex_lt⟧, the form used in the proof of 19.6. And with the index theorem, a geodesic of length $> k\pi r$ has at least $k$ parameters in $(0, 1)$ conjugate to $0$, counted with multiplicity ⟦Chapter11/LongGeodesics · le_finsum_conjMultiplicity_of_ricci⟧.

### X.12 The Gauss lemma on the whole domain, and $\exp_p$ as a local diffeomorphism

Milnor proves Theorem 19.2 through the path space (pp. 102–103). There are no conjugate points, so by 17.3 $\Omega(M; p, q)$ has the homotopy type of a discrete set with one point for each geodesic. $\Omega$ is connected because $M$ is simply connected, so there is exactly one geodesic from $p$ to $q$. Then $\exp_p$ is one-to-one and onto, and non-critical by 18.1, hence a diffeomorphism. For a manifold that is not simply connected he passes to the universal covering, and asserts without proof that it inherits a complete metric of curvature $\le 0$ (p. 103). The formal proof takes the standard covering-space route instead, in four steps.

1. $\exp_p$ is a local diffeomorphism, by Lemma 19.1, Theorem 18.1 and the inverse function theorem (this section).
2. Curves in $N$ lift through $\exp_p$, by the completeness of $N$ and the Gauss lemma, which keeps lifts bounded (X.13).
3. Hence $\exp_p$ is a covering map (X.14).
4. If $N$ is simply connected, a covering $\exp_p$ is injective (X.15).

The space $T_pN$ with the map $\exp_p$ is then Milnor's universal covering, and the metric pulled back to it is never introduced.

$\exp_p$ is smooth at every point of its domain ⟦Chapter11/ExpCovering · contDiffAt_expAt⟧. Radial geodesics have constant speed ⟦Chapter11/ExpCovering · norm_fderiv_expAt_apply⟧: for $u \in \mathcal D_p$ and $0 \le r \le 1$, $\|d(\exp_p)_{ru}(u)\| = \|u\|$. The left side is the velocity at $t = r$ of $t \mapsto \exp_p(tu)$, by the chain rule. The speed of a geodesic is constant, and at $t = 0$ it is $\|u\|$.

**The Gauss lemma on the whole domain** ⟦Chapter11/ExpCovering · gauss_lemma_expDomAt⟧. For $w \in \mathcal D_p$ and $x \in T_pN$,
$$\big\langle d(\exp_p)_w(w),\ d(\exp_p)_w(x)\big\rangle = \langle w, x\rangle .$$
Milnor states the Gauss lemma only inside a normal neighbourhood (Lemma 10.5 ⟦Chapter7/GaussLemma · gauss_lemma⟧; Part VI, §VI.9). The covering argument needs it on the whole domain, and his completeness claim for the universal cover rests on it.

*The proof as formalized.* Write $D_y$ for $d(\exp_p)_y$ and $D^2_y$ for the second derivative; $\exp_p$ is smooth on the open set $\mathcal D_p$, which contains the segment $\{rw : 0 \le r \le 1\}$. Let $g(r) = \langle D_{rw}(w), D_{rw}(rx)\rangle$. Then $g$ is continuous on $[0, 1]$, $g(0) = 0$, and $g(1)$ is the left side. It suffices to show $g'(r) = \langle w, x\rangle$ on $(0, 1)$, because the mean value theorem ⟦Mathlib/Analysis/Calculus/Deriv/MeanValue · exists_hasDerivAt_eq_slope⟧ then gives $g(1) - g(0) = \langle w, x\rangle$. By the product rule,
$$g'(r) = \big\langle D^2_{rw}(w)(w),\ D_{rw}(rx)\big\rangle + \big\langle D_{rw}(w),\ D^2_{rw}(w)(rx) + D_{rw}(x)\big\rangle .$$

1. *The first term vanishes.* $D^2_{rw}(w)(w)$ is the acceleration at $t = r$ of the radial geodesic $t \mapsto \exp_p(tw)$, so it is normal to $N$ at $\exp_p(rw)$. $D_{rw}(rx)$ is the velocity at $s = 0$ of $s \mapsto \exp_p(rw + s\,rx)$. For small $s$ this curve stays in the open domain, hence in $N$, so its velocity is tangent ⟦Chapter7/Geodesic · hasDerivAt_mem_tangentSubspace⟧. A normal vector and a tangent vector are orthogonal.
2. *The second term is $\langle w, x\rangle$.* For $s$ near $0$, $w + sx \in \mathcal D_p$, and the constant speed of its ray gives $\|D_{r(w + sx)}(w + sx)\|^2 = \|w + sx\|^2$. Differentiating at $s = 0$ yields $2\langle D_{rw}(w), D^2_{rw}(rx)(w) + D_{rw}(x)\rangle = 2\langle w, x\rangle$. The second derivative of a $C^2$ map is symmetric ⟦Mathlib/Analysis/Calculus/FDeriv/Symmetric · ContDiffAt.isSymmSndFDerivAt⟧, so $D^2_{rw}(rx)(w) = D^2_{rw}(w)(rx)$, which turns this identity into the claim.

This is Milnor's computation for Lemma 10.5, $\langle \partial f/\partial r, \partial f/\partial s\rangle$ with $f$ the radial map, carried out along the whole segment. With $x = w$ it gives $\|d(\exp_p)_w(w)\| = \|w\|$ ⟦Chapter11/ExpCovering · norm_fderiv_expAt_self⟧.

*$\exp_p$ as a map into $N$.* $\exp_p$ is regarded as a map $T_pN \to N$ ⟦Chapter7/NormalNbhd · expToN⟧, with the default value $p$ where $\exp_p(v) \notin N$, which never happens on the domain ⟦Chapter11/ExpCovering · coe_expToN_of_mem⟧. It is smooth, for the manifold structure of $N$, at every point of the domain ⟦Chapter11/ExpCovering · contMDiffAt_expToN⟧: a map into $N$ is smooth at a point if its composite with the inclusion agrees near that point with a smooth map into $V$ ⟦Chapter7/NormalNbhd · contMDiffAt_of_val_eventuallyEq⟧.

**Lemma ($\exp_p$ is a local diffeomorphism at non-critical points)** ⟦Chapter11/ExpCovering · isLocalDiffeomorphAt_expToN⟧. If $v \in \mathcal D_p$ and $d(\exp_p)_v$ is one-to-one, then $\exp_p : T_pN \to N$ is a local diffeomorphism at $v$.

*The proof as formalized.* Apply the inverse function theorem between manifolds of the companion project ⟦Milnor/Chapter1/InverseFunction · isLocalDiffeomorphAt_of_isInvertible_mfderiv⟧. Its first hypothesis, smoothness at every point near $v$, holds because $\mathcal D_p$ is open. Its second is the invertibility of the manifold derivative $A : T_pN \to Z$ of $\exp_p$ at $v$. Near $v$, the inclusion of $N$ composed with $\exp_p$ is the map $\exp_p : T_pN \to V$. By the chain rule, the derivative of the inclusion composed with $A$ is $d(\exp_p)_v$, which is one-to-one, so $A$ is one-to-one. As $\dim T_pN = \dim Z$, $A$ is bijective ⟦Mathlib/LinearAlgebra/FiniteDimensional/Lemmas · LinearMap.injective_iff_surjective_of_finrank_eq_finrank⟧, hence invertible. This is Milnor's step from non-critical to locally diffeomorphic.

If $N$ is geodesically complete and $d(\exp_p)_v$ is one-to-one for every $v \in T_pN$, then $\exp_p : T_pN \to N$ is a local diffeomorphism ⟦Chapter11/ExpCovering · isLocalDiffeomorph_expToN⟧. In non-positive curvature the second hypothesis always holds (X.7) ⟦Chapter11/CartanHadamard · injective_dExpAt_of_nonpos'⟧.

### X.13 Lifting curves through $\exp_p$

In this section and the next, $N$ is geodesically complete and $d(\exp_p)_v$ is one-to-one for every $v \in T_pN$. Then $\exp_p$ is continuous on $T_pN$ ⟦Chapter11/ExpCovering · continuous_expAt⟧.

**Lemma (the derivative of a lift)** ⟦Chapter11/ExpCovering · hasDerivAt_expLift⟧. Let $c : \mathbb R \to V$ be smooth with values in $N$, and let $\Gamma : \mathbb R \to T_pN$ be continuous at $t_0$ with $\exp_p(\Gamma(t)) = c(t)$ for $t$ near $t_0$. Then $\Gamma$ is differentiable at $t_0$, and $d(\exp_p)_{\Gamma(t_0)}(\Gamma'(t_0)) = c'(t_0)$.

*Proof.* Let $\Phi$ be a local diffeomorphism of $\exp_p$ at $\Gamma(t_0)$. For $t$ near $t_0$, $\Gamma(t)$ lies in the source of $\Phi$, by continuity, and $\Phi(\Gamma(t)) = c(t)$. So $\Gamma(t) = \Phi^{-1}(c(t))$ near $t_0$. The curve $c$ is smooth as a map into $N$ ⟦Milnor/Chapter2/Corestrict · contMDiff_codRestrict⟧, so $\Phi^{-1} \circ c$ is smooth at $t_0$, and $\Gamma$ is differentiable there. The chain rule for $\exp_p \circ \Gamma = c$ and the uniqueness of derivatives give the formula.

**Lemma (lifts do not escape to infinity)** ⟦Chapter11/ExpCovering · norm_expLift_le⟧. Let $c$ be as above with $\|c'(t)\| \le \Lambda$ on $[0, T]$, and let $\Gamma$ be continuous on $[0, T]$ with $\exp_p \circ \Gamma = c$ there. Then $\|\Gamma(t)\| \le \|\Gamma(0)\| + 1 + \Lambda t$ on $[0, T]$.

*The proof as formalized.* Let $\psi = \sqrt{\|\Gamma\|^2 + 1}$, which is differentiable wherever $\Gamma$ is, unlike $\|\Gamma\|$ at $0$. On $(0, T)$, by the last lemma, $\psi' = \langle \Gamma, \Gamma'\rangle/\psi$. The Gauss lemma with $w = \Gamma$ and $x = \Gamma'$ gives
$$\langle \Gamma, \Gamma'\rangle = \big\langle d(\exp_p)_\Gamma(\Gamma),\ d(\exp_p)_\Gamma(\Gamma')\big\rangle = \big\langle d(\exp_p)_\Gamma(\Gamma),\ c'\big\rangle \le \|\Gamma\|\,\|c'\| \le \|\Gamma\|\,\Lambda \le \psi\Lambda ,$$
using $\|d(\exp_p)_\Gamma(\Gamma)\| = \|\Gamma\|$. So $\psi' \le \Lambda$. The mean value inequality ⟦Mathlib/Analysis/Calculus/Deriv/MeanValue · Convex.image_sub_le_mul_sub_of_deriv_le⟧ gives $\psi(t) \le \psi(0) + \Lambda t$. Finally $\psi(0) \le \|\Gamma(0)\| + 1$ and $\|\Gamma(t)\| \le \psi(t)$.

The radial part of the velocity of a lift is at most the speed of the curve below it. This inequality is the whole content of Milnor's claim that the pulled-back metric is complete, and it is all that the proof below uses.

**Theorem (curves lift)** ⟦Chapter11/ExpCovering · exists_expLift⟧. Let $c : \mathbb R \to V$ be smooth with values in $N$, and $v_0 \in T_pN$ with $\exp_p(v_0) = c(0)$. Then there is $\Gamma$, continuous on $[0, 1]$, with $\Gamma(0) = v_0$ and $\exp_p(\Gamma(t)) = c(t)$ for $t \in [0, 1]$.

*The proof as formalized.*

1. Let $\Lambda$ bound $\|c'\|$ on the compact interval $[0, 1]$. Let $S$ be the set of $T \in [0, 1]$ such that a lift from $v_0$ exists on $[0, T]$. The constant $v_0$ shows $0 \in S$. Let $T_0 = \sup S$, and choose $u_m \in S$ with $u_m \to T_0$ ⟦Mathlib/Topology/Order/IsLUB · exists_seq_tendsto_sSup⟧, with lifts $\Gamma_m$ on $[0, u_m]$.
2. By the last lemma all $\Gamma_m(u_m)$ lie in the closed ball of radius $\|v_0\| + 1 + \Lambda$. In the finite-dimensional space $T_pN$ a subsequence $\Gamma_{m_k}(u_{m_k})$ converges to some $w$ ⟦Mathlib/Topology/MetricSpace/Sequences · tendsto_subseq_of_bounded⟧. By continuity of $\exp_p$ and of $c$, $\exp_p(w) = c(T_0)$.
3. Let $\Phi$ be a local diffeomorphism of $\exp_p$ at $w$. Then $c(T_0)$ lies in its target, and there is $\eta > 0$ with $c(t)$ in the target for $|t - T_0| < \eta$. Choose $k$ so large that $\Gamma_{m_k}(u_{m_k})$ lies in the source of $\Phi$ and $a := u_{m_k} > T_0 - \eta$.
4. Let $T_1 = \min(1, T_0 + \eta/2) \ge a$. Define $\Gamma$ to be $\Gamma_{m_k}$ on $[0, a]$ and $\Phi^{-1} \circ c$ on $(a, T_1]$. It lifts $c$, since $\exp_p \circ \Phi^{-1} = \mathrm{id}$ on the target. It is continuous on $[0, T_1]$: at the junction, $\Gamma_{m_k}(a)$ lies in the source of $\Phi$ and lies over $c(a)$, so $\Phi^{-1}(c(a)) = \Gamma_{m_k}(a)$.
5. So $T_1 \in S$ and $T_1 \le T_0$. As $T_0 + \eta/2 > T_0$, the minimum must be $1$. Hence $1 \in S$.

**Theorem (lifts are unique)** ⟦Chapter11/ExpCovering · expLift_unique⟧. Two lifts of the same curve that are continuous on $[0, 1]$ and agree at one time agree on $[0, 1]$.

*Proof.* $\exp_p$ is a local homeomorphism, hence locally injective, and $T_pN$ is Hausdorff, so $\exp_p$ is a separated map ⟦Mathlib/Topology/SeparatedMap · T2Space.isSeparatedMap⟧. For such a map, two continuous maps on a preconnected set whose composites agree, and which agree at one point, agree everywhere ⟦Mathlib/Topology/SeparatedMap · IsSeparatedMap.eqOn_of_comp_eqOn⟧.

### X.14 $\exp_p$ is a covering map

**Theorem** ⟦Chapter11/ExpCovering · isCoveringMap_expToN⟧. If $N$ is geodesically complete and $\exp_p$ is nowhere critical, then $f = \exp_p : T_pN \to N$ is a covering map ⟦Mathlib/Topology/Covering/Basic · IsCoveringMap⟧: every point of $N$ has an evenly covered open neighbourhood, with a discrete fibre ⟦Mathlib/Topology/Covering/Basic · IsEvenlyCovered⟧.

*The proof as formalized.* Fix $q \in N$.

1. *A normal ball and its radial geodesics.* Take normal coordinates at $q$ ⟦Chapter7/NormalNbhd · exists_isNormalRadius⟧ ⟦Chapter7/NormalNbhd · IsNormalRadius⟧ ⟦Chapter7/NormalNbhd · NormalCoord⟧ (Part VI, §VI.8). They give an $\varepsilon > 0$ and an open $U \subseteq V$ such that $\exp_q$ maps the $\varepsilon$-ball of $T_qN$ bijectively onto $B = N \cap U$, with a smooth inverse $G$. For $y \in B$ let $\ell(y) = G(y) \in T_qN$, which is continuous in $y$, and let $\rho_y(t) = \exp_q(t\,\ell(y))$. This is a geodesic on $\mathbb R$, by completeness, from $\rho_y(0) = q$ to $\rho_y(1) = y$.
2. *The sections.* For $e$ in the fibre $f^{-1}(q)$ and $y \in B$, let $\Gamma_{e, y}$ be the lift of $\rho_y$ from $e$ (X.13). The map $(t, y) \mapsto \Gamma_{e, y}(t)$ on $[0, 1] \times B$ lifts the continuous map $(t, y) \mapsto \rho_y(t)$. It is continuous at $t = 0$, where it is the constant $e$, and continuous in $t$ for each $y$. By the homotopy lifting lemma for local homeomorphisms that are separated maps ⟦Mathlib/Topology/Homotopy/Lifting · IsLocalHomeomorph.continuous_lift⟧, it is jointly continuous. So the section $\mathrm{sec}_e(y) = \Gamma_{e, y}(1)$ is continuous, and $f(\mathrm{sec}_e(y)) = y$.
3. *Every point over $B$ lies on a section.* Let $f(v) = z \in B$. Lift the reversed geodesic $t \mapsto \rho_z(1 - t)$ from $v$. Its end point $e$ lies over $\rho_z(0) = q$. Reversed, this lift is a lift of $\rho_z$ from $e$, so by uniqueness it is $\Gamma_{e, z}$. Hence $\mathrm{sec}_e(z) = v$.
4. *The fibre is discrete*, because $f$ is locally injective and constant on it ⟦Mathlib/Topology/SeparatedMap · discreteTopology_iff_locallyInjective⟧. If the fibre is empty, step 3 shows that nothing lies over $B$, and $B$ is evenly covered with empty fibre ⟦Mathlib/Topology/Covering/Basic · IsEvenlyCovered.of_preimage_eq_empty⟧.
5. *The sheets.* Let $U_e = \mathrm{sec}_e(B)$. The sheets have the following properties.
   - $U_e$ is open. Given $z_0 \in B$, let $\phi$ be a local diffeomorphism of $f$ at $\mathrm{sec}_e(z_0)$. Consider the points $y$ of the source of $\phi$ such that $f(y) = z$ for some $z$ with $\mathrm{sec}_e(z)$ in the source of $\phi$. They form an open neighbourhood of $\mathrm{sec}_e(z_0)$. Each such $y$ satisfies $f(y) = f(\mathrm{sec}_e(z))$ with both points in the source of $\phi$, where $f$ is injective, so $y = \mathrm{sec}_e(z) \in U_e$.
   - $f$ is injective on $U_e$, because $f \circ \mathrm{sec}_e = \mathrm{id}$, and $f$ maps $U_e$ onto $B$.
   - The sheets are pairwise disjoint. If $\mathrm{sec}_{e_1}(z_1) = \mathrm{sec}_{e_2}(z_2)$, applying $f$ gives $z_1 = z_2 = z$. The lifts $\Gamma_{e_1, z}$ and $\Gamma_{e_2, z}$ of $\rho_z$ then agree at $t = 1$, hence everywhere by uniqueness, and at $t = 0$ this says $e_1 = e_2$.
   - The sheets cover $f^{-1}(B)$, by step 3.
   - A subset $W \subseteq B$ is open if and only if $f^{-1}(W) \cap U_e$ is open. One direction is continuity. For the other, $W = f(f^{-1}(W) \cap U_e)$, and a local homeomorphism is an open map.
6. These are the hypotheses of Mathlib's construction of a trivialization with discrete fibre over an open set ⟦Mathlib/Topology/Covering/Basic · IsOpen.trivializationDiscrete⟧, so $q$ is evenly covered ⟦Mathlib/Topology/Covering/Basic · IsEvenlyCovered.of_trivialization⟧.

**Corollary** ⟦Chapter11/CartanHadamard · isCoveringMap_expToN_of_nonpos⟧. If $N$ is geodesically complete and has non-positive curvature, then $\exp_p : T_pN \to N$ is a covering map for every $p \in N$.

$T_pN$ is a vector space, hence contractible, so this covering is the universal covering of Milnor's p. 103. No abstract covering space and no metric on it are needed.

### X.15 Theorem 19.2 (Cartan–Hadamard)

**Lemma (injectivity)** ⟦Chapter11/CartanHadamard · injective_expToN_of_simplyConnected⟧. If $\exp_p$ is a covering map and $N$ is simply connected, then $\exp_p$ is one-to-one.

*Proof.* Let $f = \exp_p$ and suppose $f(v_1) = f(v_2)$. The segment $s(t) = v_1 + t(v_2 - v_1)$ projects to a loop $f \circ s$ at $f(v_1)$. In a simply connected space this loop is homotopic, relative to its end points, to the constant loop ⟦Mathlib/AlgebraicTopology/FundamentalGroupoid/SimplyConnected · SimplyConnectedSpace.paths_homotopic⟧. Lifts from $v_1$ of paths homotopic relative to the end points end at the same point ⟦Mathlib/Topology/Homotopy/Lifting · IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel⟧. The lift of $f \circ s$ from $v_1$ is $s$ itself, by the uniqueness of lifts ⟦Mathlib/Topology/Homotopy/Lifting · IsCoveringMap.eq_liftPath_iff'⟧, and the lift of the constant loop is constant ⟦Mathlib/Topology/Homotopy/Lifting · IsCoveringMap.liftPath_const⟧. So $v_2 = s(1) = v_1$.

**Lemma (surjectivity)** ⟦Chapter11/CartanHadamard · surjective_expToN⟧. If $N$ is connected and geodesically complete, $\exp_p$ is onto. This is the Hopf–Rinow theorem 10.9 ⟦Chapter7/HopfRinow · theorem_10_9⟧ (Part VI, §VI.18): $\rho(p, q) < \infty$ in a connected $N$ ⟦Chapter7/Metric · riemDist_ne_top⟧, and 10.9 gives $v$ with $\exp_p(v) = q$.

Two facts about geodesics from $p$ are used. If $N$ is geodesically complete, every radial geodesic $t \mapsto \exp_p(tv)$ is an unbroken geodesic of $\Omega(N; p, \exp_p(v))$ ⟦Chapter11/CartanHadamard · ray_mem_pathSpace⟧. Conversely, every unbroken geodesic $\gamma \in \Omega(N; p, q)$ is radial ⟦Chapter11/CartanHadamard · exists_eqOn_ray⟧: it agrees on $[0, 1]$ with $t \mapsto \exp_p(tv)$ for its initial velocity $v$, and $\exp_p(v) = q$ (X.6). A simply connected space is connected ⟦Chapter11/CartanHadamard · isPreconnected_of_simplyConnected⟧, and a closed $N \subseteq V$ is geodesically complete ⟦Chapter11/CartanHadamard · isGeodesicallyComplete_of_isClosed⟧.

**The diffeomorphism** ⟦Chapter11/CartanHadamard · expDiffeomorph⟧ ⟦Chapter11/CartanHadamard · coe_expDiffeomorph⟧. If $N$ is geodesically complete, simply connected and of non-positive curvature, then $\exp_p : T_pN \to N$ is a diffeomorphism ⟦Mathlib/Geometry/Manifold/Diffeomorph · Diffeomorph⟧. It is a local diffeomorphism (X.12) and bijective (the two lemmas), and a bijective local diffeomorphism is a diffeomorphism ⟦Mathlib/Geometry/Manifold/LocalDiffeomorph · IsLocalDiffeomorph.diffeomorphOfBijective⟧, since its inverse agrees near each point with a smooth local inverse.

**Theorem 19.2 (Cartan)** ⟦Chapter11/CartanHadamard · theorem_19_2⟧. Let $N$ be geodesically complete (for instance closed in $V$), simply connected, with $\langle R(A, B)A, B\rangle \le 0$ everywhere. Then any two points $p, q$ of $N$ are joined by an unbroken geodesic $\gamma \in \Omega(N; p, q)$, which is unique: every unbroken geodesic of $\Omega(N; p, q)$ agrees with it on $[0, 1]$. And $N$ is diffeomorphic to $\mathbb R^n$.

*The proof as formalized.*

1. Let $v$ be the preimage of $q$ under the diffeomorphism $\exp_p$. The radial geodesic of $v$ is an unbroken geodesic from $p$ to $q$.
2. Any unbroken geodesic $\gamma'$ from $p$ to $q$ is the radial geodesic of some $v'$ with $\exp_p(v') = q$. Injectivity gives $v' = v$, so $\gamma'$ agrees with the radial geodesic of $v$ on $[0, 1]$.
3. $N$ is non-empty, which is part of being simply connected. For $p \in N$, $T_pN$ is linearly isomorphic to $\mathbb R^n$, since both have dimension $n$. Composing this isomorphism with $\exp_p$ gives a diffeomorphism $\mathbb R^n \to N$.

*The order of the argument is reversed.* Milnor derives the uniqueness of geodesics from the path space and then the injectivity of $\exp_p$. This route needs Theorem 17.1 to identify the components of $\Omega$ with the homotopy classes of paths, a step he does not state. The formal proof derives injectivity from the covering, uniqueness from injectivity, and Milnor's statements about the path space afterwards (X.17). Both routes rest on Lemma 19.1. In place of 17.1, the covering route needs the bound on lifts of X.13.

### X.16 Corollary 19.3: the higher homotopy groups

Milnor's proof of the first half of 19.3 is one line: $\pi_i(M) = \pi_i(\tilde M) = 0$ for $i > 1$, as $\tilde M \cong \mathbb R^n$ is contractible. The formal proof lifts the maps that define $\pi_i$ (§0.7) directly. In this section $i$ is the dimension of a cube $I^i$, and $k, l$ index its coordinates.

The cube $I^i$ is contractible, by the straight-line contraction $(s, y) \mapsto (1 - s)y$ to the corner $0$ ⟦Chapter11/CartanHadamard · contractibleSpace_cube⟧ ⟦Mathlib/Topology/Homotopy/Contractible · contractible_iff_id_nullhomotopic⟧. Its faces $\{y : y_k = a\}$ are preconnected ⟦Chapter11/CartanHadamard · isPreconnected_cube_face⟧, being products of intervals and a point.

**Lemma** ⟦Chapter11/CartanHadamard · genLoop_homotopic_const⟧. Let $N$ be geodesically complete with non-positive curvature, $i \ge 2$, $x \in N$, and let $\gamma : I^i \to N$ be continuous and send the boundary of the cube ⟦Mathlib/Topology/Homotopy/HomotopyGroup · Cube.boundary⟧ to $x$, that is, a generalized loop ⟦Mathlib/Topology/Homotopy/HomotopyGroup · GenLoop⟧. Then $\gamma$ is homotopic to the constant map relative to the boundary ⟦Mathlib/Topology/Homotopy/HomotopyGroup · GenLoop.Homotopic⟧.

*The proof as formalized.*

1. $f = \exp_x$ is a covering map with $f(0) = x$. The cube is contractible, hence simply connected, and locally path connected. The corner $0$ of the cube lies on its boundary, so $\gamma(0) = x = f(0)$. Hence $\gamma$ lifts to a continuous $F : I^i \to T_xN$ with $F(0) = 0$ ⟦Mathlib/Topology/Homotopy/Lifting · IsCoveringMap.existsUnique_continuousMap_lifts⟧.
2. On each face $\{y_k = a\}$ with $a \in \{0, 1\}$, $f \circ F = \gamma$ is constant, equal to $x$. The face is preconnected and the fibre over $x$ is discrete, so $F$ is constant on the face ⟦Mathlib/Topology/Covering/Basic · IsCoveringMap.constOn_of_comp⟧.
3. Let $y$ lie on the face $\{y_k = a\}$, and let $z$ be the point with $z_k = y_k$ and all other coordinates $0$. Then $F(y) = F(z)$, as both lie on that face. Because $i \ge 2$ there is $l \ne k$, and $z$ and $0$ both lie on the face $\{y_l = 0\}$, so $F(z) = F(0) = 0$. Hence $F = 0$ on the boundary of the cube.
4. $H(s, y) = f((1 - s)F(y))$ is a homotopy from $f \circ F = \gamma$ to the constant $f(0) = x$. For $y$ on the boundary, $H(s, y) = f(0) = x$ for every $s$.

Step 3 is where $i \ge 2$ enters: the boundary of the cube is connected only then. For $i = 1$ the boundary $\{0, 1\}$ is not connected, and the argument stops, as the statement does.

**Corollary 19.3, first half** ⟦Chapter11/CartanHadamard · corollary_19_3⟧. If $N$ is geodesically complete with non-positive curvature, then $\pi_i(N, x) = 0$ ⟦Mathlib/Topology/Homotopy/HomotopyGroup · HomotopyGroup.Pi⟧ for every $i > 1$ and every $x \in N$.

*Proof.* Every class is represented by a generalized loop, and by the lemma every generalized loop is homotopic, relative to the boundary, to the constant loop. So any two classes coincide.

### X.17 Homotopy classes of paths and the path space

Two further statements of Milnor's concern a complete $M$ of non-positive curvature. On p. 102: $\Omega(M; p, q)$ has the homotopy type of a $0$-dimensional complex with one vertex for each geodesic. On p. 103: each homotopy class of paths from $p$ to $q$ contains exactly one geodesic. Both follow from the covering. A path $\gamma \in \Omega(N; p, q)$ is regarded as a continuous path in $N$ from $p$ to $q$ ⟦Chapter11/CartanHadamard · pathOfMem⟧.

**Theorem (one geodesic in each homotopy class)** ⟦Chapter11/CartanHadamard · homotopy_class_unique_geodesic⟧. Let $N$ be geodesically complete with non-positive curvature, $p, q \in N$, and $c$ a continuous path from $p$ to $q$ in $N$. Then some unbroken geodesic $\gamma \in \Omega(N; p, q)$ is homotopic to $c$ relative to the end points. Two unbroken geodesics of $\Omega(N; p, q)$ that are both homotopic to $c$ relative to the end points agree on $[0, 1]$.

*The proof as formalized.* Let $f = \exp_p$, a covering map with $f(0) = p$.

1. *Existence.* Let $\Gamma$ be the lift of $c$ from $0$ ⟦Mathlib/Topology/Homotopy/Lifting · IsCoveringMap.liftPath⟧ and $v = \Gamma(1)$, so that $f(v) = q$. The radial geodesic of $v$ is an unbroken geodesic of $\Omega(N; p, q)$. The segment $t \mapsto tv$ and $\Gamma$ are paths in $T_pN$ from $0$ to $v$. $T_pN$ is contractible, hence simply connected, so the two paths are homotopic relative to the end points. Such homotopies in $T_pN$ correspond exactly to homotopies of the projected paths in $N$ ⟦Mathlib/Topology/Homotopy/Lifting · IsCoveringMap.homotopicRel_iff_comp⟧. The projections are the radial geodesic of $v$ and $c$.
2. *Uniqueness.* Let $\gamma$, $\gamma'$ be two such geodesics. Both are radial, of vectors $v$ and $v'$ (X.15), and their lifts from $0$ are the segments to $v$ and to $v'$, by the uniqueness of lifts. $\gamma$ and $\gamma'$ are homotopic relative to the end points, through $c$, so their lifts from $0$ end at the same point. Hence $v = v'$ and $\gamma = \gamma'$ on $[0, 1]$.

Milnor obtains this by applying 19.2 to the universal covering with the lifted metric. Here the covering is $\exp_p$ itself.

**The path space through Theorem 17.3** ⟦Chapter11/CartanHadamard · omega_cells_of_nonpos⟧. Let $N$ be closed in $V$, of non-positive curvature, and $p, q \in N$. Then $\Omega(N; p, q)$ has the homotopy type of a countable cell complex all of whose cells are $0$-cells, one for each geodesic from $p$ to $q$.

*Proof.* Every geodesic from $p$ to $q$ has nullity $0$ and index $0$ (X.7). So Theorem 17.3 applies, and its cells, which have the dimensions of the indices, all have dimension $0$ ⟦Chapter10/FundamentalTheorem · geodesicIndex_eq⟧. This is the first step of Milnor's proof of 19.2.

**One cell** ⟦Chapter11/CartanHadamard · omega_single_cell⟧. If moreover $N$ is simply connected, the complex has exactly one cell.

*Proof.* Let $\gamma_0$ be the unique geodesic of Theorem 19.2 from $p$ to $q$, and let $n_0$ be the list of Theorem 17.3 in which it occurs. Every entry of every list is a geodesic from $p$ to $q$, so it agrees with $\gamma_0$ on $[0, 1]$. An entry of a list $m \ne n_0$ would therefore agree on $[0, 1]$ with an entry of list $n_0$, which Theorem 17.3 excludes, so the other lists are empty. Two entries of list $n_0$ would agree on $[0, 1]$, which is also excluded. So list $n_0$ has exactly one entry, giving one $0$-cell at stage $n_0$ and none elsewhere.

What remains of Milnor's sentence is that a complex with only $0$-cells is a discrete set. For the formal cell complexes, which are mapping telescopes, this is not formalized. The homotopy type is computed directly from the covering instead.

**Theorem ($\Omega^*$ and a fibre of $\exp_p$)** ⟦Chapter11/CartanHadamard · nonempty_homotopyEquiv_pathC_fiber⟧. Let $N$ be geodesically complete with non-positive curvature, and $p, q \in N$. Then $\Omega^*(N; p, q)$ is homotopy equivalent ⟦Mathlib/Topology/Homotopy/Equiv · ContinuousMap.HomotopyEquiv⟧ to the fibre $f^{-1}(q)$ of $f = \exp_p$.

*The proof as formalized.*

1. The evaluation $H(t, \gamma) = \gamma(t)$ is continuous on $[0, 1] \times \Omega^*$, and $H(0, \gamma) = p = f(0)$. The homotopy lifting property of coverings ⟦Mathlib/Topology/Homotopy/Lifting · IsCoveringMap.liftHomotopy⟧ gives a continuous $\tilde H : [0, 1] \times \Omega^* \to T_pN$ with $f \circ \tilde H = H$ and $\tilde H(0, \gamma) = 0$. Thus $\tilde H(\cdot, \gamma)$ is the lift of $\gamma$ from $0$.
2. $\mathrm{end}(\gamma) = \tilde H(1, \gamma)$ is a continuous map $\Omega^* \to f^{-1}(q)$.
3. The fibre is discrete ⟦Mathlib/Topology/Covering/Basic · IsEvenlyCovered.discreteTopology_fiber⟧, so $\mathrm{geo}(v) = (t \mapsto f(tv))$, a path from $p$ to $q$, depends continuously on $v$.
4. $\mathrm{end} \circ \mathrm{geo} = \mathrm{id}$. The lift of $t \mapsto f(tv)$ from $0$ is $t \mapsto tv$, by the uniqueness of lifts ⟦Mathlib/Topology/Covering/Basic · IsCoveringMap.eq_of_comp_eq⟧, and it ends at $v$.
5. $\mathrm{geo} \circ \mathrm{end} \simeq \mathrm{id}$, through
$$G(s, \gamma)(t) = f\big((1 - s)\tilde H(t, \gamma) + s\,t\,\tilde H(1, \gamma)\big),$$
the straight-line homotopy in $T_pN$ from the lift of $\gamma$ to the segment with the same end points, projected by $f$. At $s = 0$ it is $\gamma$; at $s = 1$ it is $\mathrm{geo}(\mathrm{end}(\gamma))$. For every $s$ it runs from $f(0) = p$ to $f(\tilde H(1, \gamma)) = q$, so it stays in $\Omega^*$.

The points of the fibre are the geodesics from $p$ to $q$ ⟦Chapter11/CartanHadamard · geodesic_iff_mem_fiber⟧, for complete $N$. For $v$ in the fibre, the radial geodesic of $v$ is an unbroken geodesic of $\Omega(N; p, q)$. Every unbroken geodesic of $\Omega(N; p, q)$ agrees on $[0, 1]$ with the radial geodesic of a point of the fibre. And two points of the fibre whose radial geodesics agree on $[0, 1]$ are equal, since both are the velocity at $0$ within $[0, 1]$, which is unique.

**Theorem (the path space has the homotopy type of a discrete set)** ⟦Chapter11/CartanHadamard · omega_homotopyEquiv_fiber⟧. Let $N$ be geodesically complete with non-positive curvature, and $p, q \in N$. The fibre of $\exp_p$ over $q$ is discrete and countable, and $\Omega(N; p, q)$ is homotopy equivalent to it.

*Proof.* $\Omega \simeq \Omega^*$ by Theorem 17.1, composed with the last theorem. The fibre is a discrete subspace of the separable space $T_pN$, hence countable ⟦Mathlib/Topology/Bases · TopologicalSpace.separableSpace_iff_countable⟧.

Together with the description of the fibre, this is Milnor's statement on p. 102, for every geodesically complete $N$ of non-positive curvature, closed in $V$ or not, and for all $p, q$.

**Contractibility.** If $D : T \to N$ is a homeomorphism from a real normed space with $D(0) = p$, then $\Omega^*(N; p, q)$ is contractible ⟦Chapter11/CartanHadamard · contractibleSpace_pathC⟧ ⟦Mathlib/Topology/Homotopy/Contractible · ContractibleSpace⟧. The homotopy
$$H(s, \gamma)(t) = D\big((1 - s)D^{-1}(\gamma(t)) + s\,t\,D^{-1}(q)\big)$$
contracts it onto $\gamma_0(t) = D(t\,D^{-1}(q))$. At $t = 0$ its value is $D(0) = p$, and at $t = 1$ it is $D(D^{-1}(q)) = q$. With $D = \exp_p$ (X.15) and Theorem 17.1 this gives **Theorem 19.2 for the path space** ⟦Chapter11/CartanHadamard · contractibleSpace_pathSp⟧: if $N$ is geodesically complete, simply connected and of non-positive curvature, $\Omega(N; p, q)$ is contractible. It has the homotopy type of a point, as Milnor's proof asserts.

### X.18 Theorem 19.6 for non-conjugate end points

Milnor's proof (p. 106) has four steps. The continuous function $K(U, U)$ on the compact space of unit vectors takes a minimum $(n - 1)/r^2 > 0$. A geodesic of length $> k\pi r$ has index $\ge k$ (X.11). If $p$ and $q$ are not conjugate along any geodesic, Theorem 16.3 leaves only finitely many geodesics of length $\le k\pi r$, hence only finitely many of index $< k$. Theorem 17.3 then finishes the proof. The formal proof supplies the continuity of $K(U, U)$, which Milnor does not discuss: the Ricci tensor is a trace over the moving subspace $T_qN$.

*The Ricci curvature as a trace on $V$.* For $q \in N$ and $u \in V$ let $\mathrm{Ric}_{q, u}$ be the linear map $W \mapsto R(P_qu, P_qW)P_qu$ of $V$ ⟦Chapter11/PositiveRicci · ricciMap⟧ ⟦Chapter11/PositiveRicci · ricciMap_apply⟧. For $U \in T_qN$, $K(U, U) = \operatorname{tr}_V \mathrm{Ric}_{q, U}$ ⟦Chapter11/PositiveRicci · ricci_eq_trace_ricciMap⟧. Indeed $\mathrm{Ric}_{q, U} = \iota \circ A \circ \pi$, where $A$ is $W \mapsto R(U, W)U$ on $T_qN$, $\iota$ the inclusion and $\pi$ the orthogonal projection onto $T_qN$. A trace does not change when the factors of a composite are cycled ⟦Mathlib/LinearAlgebra/Trace · LinearMap.trace_comp_comm'⟧, and $\pi \circ \iota = \mathrm{id}$, so the trace is $\operatorname{tr} A$.

**Lemma (continuity)** ⟦Chapter11/PositiveRicci · continuous_trace_ricciMap⟧. $(q, u) \mapsto \operatorname{tr}_V \mathrm{Ric}_{q, u}$ is continuous on $N \times V$.

*The proof as formalized.* Near $q_0$, take the slice chart $\sigma$ at $q_0$ and the smooth map $Q$, defined on an open subset of $V$, that agrees with $q \mapsto P_q$ on $N$ ⟦Chapter6/Projection · projRep⟧ ⟦Chapter6/Projection · projRep_eq⟧ ⟦Chapter6/Projection · contDiffAt_projRep⟧. For tangent $a$, $\mathrm{II}(a, b) = dQ(a)\,b$ ⟦Chapter6/Projection · dN_tanProj_eq_fderiv⟧. Fix an orthonormal basis $(e_i)$ of $V$. Near $(q_0, u_0)$ the trace is
$$\sum_i \Big\langle e_i,\ dQ_q(Q_qe_i)\big(dQ_q(Q_qu)(Q_qu)\big) - dQ_q(Q_qu)\big(dQ_q(Q_qe_i)(Q_qu)\big)\Big\rangle ,$$
which is continuous in $(q, u)$ because $Q$ and $dQ$ are.

**Lemma (the minimum)** ⟦Chapter11/PositiveRicci · exists_ricciLowerBound⟧. If $N$ is compact, $n \ge 2$, and $K(U, U) > 0$ for every non-zero tangent vector $U$, there is $r > 0$ with $K(U, U) \ge (n - 1)/r^2$ for every unit tangent vector $U$.

*The proof as formalized.* The unit tangent bundle $\{(q, u) \in N \times V : P_qu = u,\ \|u\| = 1\}$ is closed, because $q \mapsto P_q$ is continuous ⟦Chapter6/Projection · contMDiff_tanProj⟧. It lies in the compact set $N \times S$, $S$ the unit sphere of $V$, so it is compact; this is Milnor's compact space of unit vectors. If it is empty, any $r$ will do. Otherwise the continuous trace attains a minimum $m$ on it ⟦Mathlib/Topology/Order/Compact · IsCompact.exists_isMinOn⟧, at a unit tangent vector, so $m > 0$. Put $r = \sqrt{(n - 1)/m}$; then $(n - 1)/r^2 = m \le K(U, U)$.

*Energy and index.* The energy of an unbroken geodesic is the square of its length ⟦Chapter11/PositiveRicci · energy_eq_pathLength_sq_of_geodesic⟧: its speed is constant, which is the case of equality in $L^2 \le E$ ⟦Chapter8/Energy · pathLength_sq_eq_energy_iff⟧. Hence, under the Ricci bound, a geodesic of index $\le d$ has energy $\le ((d + 1)\pi r)^2$ ⟦Chapter11/PositiveRicci · energy_le_of_geodesicIndex_le⟧: its index is $< d + 1$, so its length is $\le (d + 1)\pi r$ (X.11).

**Theorem 19.6, under a Ricci bound** ⟦Chapter11/PositiveRicci · theorem_19_6_of_ricciLowerBound⟧. Let $N$ be closed in $V$, $n \ge 2$, $r > 0$ with $K(U, U) \ge (n - 1)/r^2$ for all unit vectors, and $p, q \in N$ with $q \notin C(p)$. Then $\Omega(N; p, q)$ has the homotopy type of a countable cell complex in which, for each $d$, only finitely many stages contain a cell of dimension $d$. Each stage is a finite list, so there are only finitely many cells of each dimension.

*The proof as formalized.*

1. As $q \notin C(p)$, every geodesic from $p$ to $q$ has nullity $0$ (X.6). Theorem 17.3 gives the lists $\mathrm{geo}_m$, the cells of stage $m$ having the dimensions of the indices of its entries, and the energies increasing strictly from one list to the next.
2. Fix $d$ and put $e_d = ((d + 1)\pi r)^2$. For each stage $m$ containing a cell of dimension $d$, choose an entry $g(m)$ of $\mathrm{geo}_m$ of index $d$. Then $E(g(m)) \le e_d$.
3. $m \mapsto E(g(m))$ is injective on these stages, because energies increase strictly across lists. Its values lie in the set of energies $\le e_d$ of geodesics from $p$ to $q$, which is finite by Theorem 16.3 ⟦Chapter10/FundamentalTheorem · finite_geodesicEnergies⟧ (Part VIII, §VIII.14). So there are finitely many such stages.

**Theorem 19.6** ⟦Chapter11/PositiveRicci · theorem_19_6⟧. Let $N$ be compact, $n \ge 2$, with positive definite Ricci tensor, and $p, q \in N$ with $q \notin C(p)$. Then $\Omega(N; p, q)$ has the homotopy type of a countable cell complex with only finitely many cells in each dimension.

*Proof.* A compact $N$ is closed in $V$, and the last two lemmas give $r$.

Three things differ from the book. Milnor's CW-complex is here a countable cell complex in the sense of §0.5, a mapping telescope (Part XI, §XI.15). Its identification with the union of its stages with the weak topology is Example 2 of the Appendix (Part XI, §XI.7), which needs Whitehead's theorem and is not formalized. The end points are assumed not conjugate along any geodesic, which is all that Milnor's proof covers, although his statement is for all $p, q$ (X.20). And $n \ge 2$ is assumed. It makes $(n - 1)/r^2$ positive and provides a field perpendicular to $\gamma$; in dimension $1$ the Ricci tensor vanishes, so it cannot be positive definite there anyway.

### X.19 The homology of the path space

With cellular homology, Theorem 19.6 would make $H_i(\Omega; \Bbbk)$ finite-dimensional at once, and Milnor computes the homology of $\Omega S^n$ from its cells in this way on p. 96. The formal cell complexes have attaching maps that need not be cellular, so cellular homology is not available. The homology is computed instead from the filtration of $\Omega$ by the sublevel sets $\Omega^a = \{E \le a\}$ ⟦Chapter2/Crossing · sublevel⟧ of the energy, a continuous function on $\Omega$ ⟦Chapter10/FundamentalTheorem · PathSp.energyC⟧, as in Milnor's §§3 and 5 (Parts II and IV), carried over to the path space in Part IX. Homology is singular homology (§0.6) with coefficients in a field $\Bbbk$, of spaces ⟦Homology/MorseHomologyBasic · spaceHomology⟧ and of pairs of subsets ⟦Homology/TripleFiltration · subsetHomology⟧; $\Bbbk$ is taken in the same universe as $V$, a formal condition without mathematical content. Let $\mathcal E(a, b)$ be the set of energies in $(a, b)$ of geodesics from $p$ to $q$ ⟦Chapter11/RicciHomology · slabEnergies⟧.

**Theorem (the homology of a slab)** ⟦Chapter11/RicciHomology · slab_homology⟧. Let $N$ be closed in $V$, $p, q \in N$, every geodesic from $p$ to $q$ non-degenerate, and let $a \le b$ be levels that are not energies of geodesics. Then for every $j$, $H_j(\Omega^b, \Omega^a; \Bbbk)$ is finite-dimensional, and it is $0$ if no geodesic with energy in $(a, b)$ has index $j$.

*The proof as formalized.* By strong induction on the number $m$ of elements of $\mathcal E(a, b)$, which is finite by Theorem 16.3.

1. *At most one energy.* This is the slab computation of Part IX, §IX.9 ⟦Chapter10/PathHomology · BrokenSetup.finrank_subsetHomology_Omega⟧. A setup of broken geodesics ⟦Chapter10/Broken · BrokenSetup⟧ at level $\max(b, 0) + 1$ ⟦Chapter10/Broken · exists_brokenSetup_uniform⟧, available because closed $\rho$-balls of a closed $N$ are compact ⟦Chapter10/Broken · isCompact_closedRiemBall_of_isClosed⟧, transports the slab to the energy on a finite-dimensional manifold of broken geodesics. There $H_j(\Omega^b, \Omega^a; \Bbbk)$ is finite-dimensional, of dimension the number of geodesics with energy in $(a, b)$ and index $j$. If none has index $j$, the dimension is $0$.
2. *At least two energies.* Let $e_1 < e_2$ be the two smallest elements of $\mathcal E(a, b)$ and $c = (e_1 + e_2)/2$. The level $c$ is not an energy, since every other energy in $(a, b)$ is $\ge e_2 > c$. The slab $(a, c)$ contains exactly the energy $e_1$ and the slab $(c, b)$ the other $m - 1$, so the induction hypothesis applies to both. The triple $\Omega^a \subseteq \Omega^c \subseteq \Omega^b$ has an exact sequence ⟦Homology/TripleFiltration · subsetTripleLongExactSeq⟧, containing $H_j(\Omega^c, \Omega^a) \to H_j(\Omega^b, \Omega^a) \to H_j(\Omega^b, \Omega^c)$. The middle term is finite-dimensional when the outer terms are ⟦Chapter3/Inequalities · finiteDimensional_middle⟧, and $0$ when they are ⟦Chapter10/SublevelHomology · LongExactSeq.subsingleton_B⟧. A hypothesis that no geodesic in $(a, b)$ has index $j$ passes to both halves.

**Theorem (finite-dimensional homology)** ⟦Chapter11/RicciHomology · finiteDimensional_spaceHomology_omega⟧. Let $N$ be closed in $V$, $n \ge 2$, $r > 0$ with $K(U, U) \ge (n - 1)/r^2$ for all unit vectors, and $p, q \in N$ with $q \notin C(p)$. Then $H_i(\Omega(N; p, q); \Bbbk)$ is finite-dimensional for every $i$ and every field $\Bbbk$.

*The proof as formalized.*

1. *Levels.* For $k \ge 1$ choose $a_k \in (k - 1, k)$ that is not the energy of a geodesic from $p$ to $q$; there are only finitely many such energies $\le k$. Put $a_0 = -1$. The levels $a_k$ increase, are never energies of geodesics, and satisfy $a_k \ge k - 1$. Let $A_k = \Omega^{a_k}$. Every compact subset of $\Omega$ lies in some $A_k$, because the energy is continuous and bounded on it ⟦Chapter10/SublevelHomology · exists_subset_sublevel_of_isCompact⟧.
2. *High slabs have no homology in degrees $i$ and $i + 1$.* Choose $k_0 > ((i + 2)\pi r)^2 + 1$, so that $a_{k_0} > ((i + 2)\pi r)^2$. For $k \ge k_0$, every geodesic with energy in $(a_k, a_{k+1})$ has energy $> ((i + 2)\pi r)^2$. Its index is therefore $\ge i + 2$, since an index $\le i + 1$ would bound the energy by $((i + 2)\pi r)^2$ (X.18). By the slab theorem the slab has zero homology in degrees $i$ and $i + 1$.
3. *Passage to $\Omega$.* Hence $H_i(A_{k_0}, \emptyset) \cong H_i(\Omega)$ ⟦Chapter10/SublevelHomology · spaceHomologyEquivOfSteps⟧. This is the argument of Part IX, §IX.8: singular chains have compact support, and steps with no homology in degrees $i$ and $i + 1$ change nothing in degree $i$.
4. *The bottom.* Energies are $\ge 0 > -1$ ⟦Chapter10/PathMetric · PathSp.energy_nonneg_of_le⟧, so $A_0 = \emptyset$. Thus $H_i(A_{k_0}, \emptyset)$ is $H_i(A_{k_0}, A_0)$ ⟦Homology/TripleFiltration · finiteDimensional_subsetHomology_congr⟧, which is finite-dimensional by the slab theorem.

Under Milnor's hypotheses of 19.6 ($N$ compact, $n \ge 2$, positive definite Ricci tensor, $q \notin C(p)$) the same conclusion holds ⟦Chapter11/RicciHomology · finiteDimensional_spaceHomology_omega_of_compact⟧, with $r$ from the minimum of X.18.

### X.20 What is not done

- **The second half of Corollary 19.3**: in a complete $N$ of non-positive curvature, $\pi_1(N)$ has no element of finite order other than the identity. Milnor's proof uses the cohomology of groups. For $M$ with contractible universal covering, $H^k(M)$ is the cohomology of $\pi_1(M)$ (he cites Hu), and a finite cyclic group has non-zero cohomology in arbitrarily high degrees. As `Chapter11/CartanHadamard` records, neither is available to the formalization.
- **Theorem 19.6 when $p$ and $q$ are conjugate along some geodesic.** Milnor states 19.6 for all $p, q$, but his proof treats only non-conjugate end points. The general case needs a $q'$ not conjugate to $p$, which the density theorem of X.6 provides, and a homotopy equivalence $\Omega(N; p, q) \simeq \Omega(N; p, q')$ obtained by changing the end point through Theorem 17.1 (Lemma 17.D of the exposition). That lemma is not formalized. The same restriction applies to the finiteness of the homology in X.19.
- **Cell complexes and spaces.** That a mapping telescope with only $0$-cells is homotopy equivalent to a discrete space is not formalized; X.17 obtains the discreteness from the covering instead. Milnor's CW-complexes are the formal telescopes only up to Example 2 of the Appendix (Part XI, §XI.7), which needs Whitehead's theorem.
- **The finiteness of $\pi_1$ under positive Ricci curvature** (p. 105, after 19.5). It needs the universal covering of $N$ with the lifted metric, to which 19.5 would apply. The covering of X.14 needs $\exp_p$ to be nowhere critical, which fails in positive curvature.
- **Side remarks of §19**: the sectional curvature as the Gaussian curvature of the image under $\exp_p$ of a plane (p. 100); the optics paragraph and the examples of pp. 101–102; the sphere of radius $r$ and the claim that 19.4 is best possible (p. 105); the remarks of pp. 106–107 on complete non-compact manifolds, on $S^m \times S^k$ and on Synge's theorem.
- **Abstract Riemannian manifolds**: everything is proved for submanifolds of a Euclidean space with the induced metric; Nash's theorem is quoted.

The module docstrings of `Chapter11/Curvature`, `Chapter11/Myers` and `Chapter11/LongGeodesics` still list Theorem 19.2, Corollary 19.3 and the rest of Theorem 19.6 as not done. They predate the four later files, as `DocstringErrata.md` records in its one open row. This Part follows the proofs, not those notes.

### What the formalization taught us

- **§18 needs no completeness**, but it needs $\exp$ to be smooth on its whole domain, which §10 does not provide. The smooth dependence of geodesics on their initial data over a compact interval supplies it ⟦Chapter11/ExpSmooth · raysGoodE_of_isGeodesicOn⟧ ⟦Chapter11/ExpSmooth · exists_contDiffOn_exp⟧.
- **Theorem 18.1 is a statement about multiplicities** ⟦Chapter11/ExpSmooth · theorem_18_1_multiplicity⟧. The explicit fields $t\,d(\exp_q)_{tv}(X)$ replace both the symmetry lemma and the dimension count ⟦Chapter11/ExpSmooth · covAlong_expJacobi_zero⟧.
- **Corollary 18.2 is not immediate.** Milnor's one-line derivation hides the radiality of geodesics from $p$ ⟦Chapter11/NonConjugate · theorem_18_1_of_geodesic⟧, an undefined notion of measure zero in a manifold ⟦Chapter11/NonConjugate · corollary_18_2⟧, and the step from measure zero to existence ⟦Chapter11/NonConjugate · dense_compl_conjLocus⟧.
- **Hidden hypotheses**: $n \ge 2$ in Myers' theorem ⟦Chapter11/Myers · theorem_19_4⟧; connectedness in Corollary 19.5 ⟦Chapter11/Myers · corollary_19_5⟧; the parallelism of the velocity field in the frame of 19.4 ⟦Chapter11/Myers · exists_parallel_frame⟧; the continuity of the Ricci curvature on the unit tangent bundle in 19.6 ⟦Chapter11/PositiveRicci · continuous_trace_ricciMap⟧; and, in $\pi_i(M) = \pi_i(\tilde M)$, the connectedness of the boundary of the cube, true only for $i \ge 2$ ⟦Chapter11/CartanHadamard · genLoop_homotopic_const⟧.
- **The completeness of the universal covering** is one inequality: lifts through $\exp_p$ grow no faster than the length of the curve below them ⟦Chapter11/ExpCovering · norm_expLift_le⟧. It rests on the Gauss lemma on the whole domain of $\exp_p$ ⟦Chapter11/ExpCovering · gauss_lemma_expDomAt⟧.
- **Cartan–Hadamard needs no path space**: the covering gives the theorem ⟦Chapter11/CartanHadamard · theorem_19_2⟧, and Milnor's path-space statements follow from it ⟦Chapter11/CartanHadamard · omega_homotopyEquiv_fiber⟧. On the way, $E_{**}$ turns out to be positive definite in non-positive curvature ⟦Chapter11/Curvature · energyHessian_pos_of_nonpos⟧.
- **The homology of $\Omega$ under positive Ricci curvature** comes from the energy filtration and the index bound, without cellular homology ⟦Chapter11/RicciHomology · finiteDimensional_spaceHomology_omega⟧.
