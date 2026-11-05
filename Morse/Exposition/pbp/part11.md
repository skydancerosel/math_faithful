## Part XI. The Appendix: the homotopy type of a monotone union

Milnor's Appendix (pp. 149–153) gives another way to finish the proof of Theorem 17.3. The path space $\Omega$ is the union of its increasing sublevel sets $\Omega^{a_0} \subseteq \Omega^{a_1} \subseteq \cdots$, each of which has the homotopy type of a CW-complex. The question is when this information about the pieces determines the homotopy type of the union. Milnor's tool is the *telescope* $X_\Sigma \subseteq X \times \mathbb R$, which stacks the pieces $X_n \times [n, n+1]$ on top of one another. His main result, Theorem A, says that a map which is a homotopy equivalence piece by piece is a homotopy equivalence, provided both spaces are *homotopy direct limits* of their pieces. This part retells the formal proofs of the whole Appendix except Example 2 and a remark that is stated without proof. The setting is arbitrary topological spaces, with no separation axiom anywhere except in Example 1. Theorem A is proved twice: once by Milnor's own proof, with his two cases, his explicit homotopies and a possible misprint corrected, and once exactly as he states it.

The formal route departs from the book in five places, each explained where it occurs.

- **Closedness.** Every map Milnor writes on a telescope is given strip by strip. Pasting such pieces is guaranteed to give a continuous map when the strips $X_n \times [n, n+1]$ are closed in $X_\Sigma$, as they are when the $X_n$ are closed in $X$, and in general they are not (§XI.4). Milnor never says so. The formal Case 1 assumes the $X_n$ closed, and the hypothesis is not an artifact of the formal proof: without it, Milnor's homotopy inverse $g$ can be discontinuous (§XI.10). His proof of Theorem A as a whole needs only the $Y_n$ closed, because Case 2 applies Case 1 only to truncations of telescopes, which are always closed (§XI.11). Theorem A as Milnor states it, with no closedness at all, follows by running the same proof on *mapping telescopes*, where a map given block by block is always continuous (§§XI.12–11.13).
- **A silent lemma.** Case 2 ends by passing from the telescope of the truncations $X^n_\Sigma$ back to $X_\Sigma$. This needs $X_\Sigma$ to be the homotopy direct limit of its truncations, which Milnor does not mention. It is Lemma 2.2 (§XI.6).
- **A possible misprint.** The third line of Milnor's homotopy $h_u$ has $(4-3t)u$ where $(4t-3)u$ is meant (§XI.10).
- **Sublevel sets need no paracompactness.** Milnor's application rests on Example 1, which needs $\Omega$ paracompact. For the sublevel sets of a continuous function the formal proof needs neither paracompactness nor Hausdorffness (§XI.7), and this is the form Theorem 17.3 uses (§XI.15).
- **CW-complexes become mapping telescopes.** Example 2, that a CW-complex is the homotopy direct limit of its subcomplexes, rests on Whitehead's theorem, which Mathlib does not have. So the Corollary and the topological part of Theorem 17.3 conclude with a homotopy equivalence to the mapping telescope of a tower of iterated adjunction spaces, which stands for a countable CW-complex (§§XI.14–11.15).

The Appendix serves Part IX twice. Theorem 17.1 uses Theorem A for open, not closed, pieces of path spaces, so it needs the version without closedness. Theorem 17.3 uses the countable cell complexes of §XI.15.

**Map.**

- `Appendix/Telescope` (630 lines): homotopy equivalences as a property of a map; the telescope, its strips, (T1); the projection and homotopy direct limits; (T3) and maps given strip by strip; the induced map $f_\Sigma$ and the reduction to it; truncations and (T2); Lemmas 2.1 and 2.2.
- `Appendix/Examples` (239 lines): Example 1; sublevel sets; Example 3.
- `Appendix/TheoremA` (765 lines): reparametrizations of the strips; Milnor's maps $h_1$, their inverse $g$ and the homotopies $H_u$, $K_u$; Case 1; Case 2; Theorem A with closed $Y_i$.
- `Appendix/MappingTelescope` (517 lines): mapping telescopes, their truncations, and (T2) for them.
- `Appendix/MonotoneUnion` (569 lines): the comparison with mapping telescopes; Theorem A without closedness; monotone unions and the Corollary; cell towers and the topological part of Theorem 17.3.

The names (T1)–(T3), Lemma 2.1 and Lemma 2.2 are those of the retelling (`Exposition/Appendix.md`, §§1–2). Milnor gives these facts no names, and most of them he uses without stating them.

### XI.1 Conventions: homotopy equivalences, restrictions, clamps

Spaces are arbitrary topological spaces and maps are continuous. A subset carries the subspace topology, and a point of a subset $S \subseteq X$ is a point of $X$ together with a proof that it lies in $S$. $I$ is the interval $[0,1]$. A sequence $X_0, X_1, \dots$ of subsets is *increasing* when $X_0 \subseteq X_1 \subseteq \cdots$. Formally this is a monotone map from $\mathbb N$ to the subsets of $X$. Milnor's sequences are always increasing, and the statements below say when they assume it.

*Homotopies.* A homotopy from $f_0$ to $f_1 : X \to Y$ is Mathlib's: a continuous $F : I \times X \to Y$, time first, with $F(0, \cdot) = f_0$ and $F(1, \cdot) = f_1$ ⟦Mathlib/Topology/Homotopy/Basic · ContinuousMap.Homotopy⟧. *Homotopic* means that a homotopy exists ⟦Mathlib/Topology/Homotopy/Basic · ContinuousMap.Homotopic⟧; this is an equivalence relation, compatible with composition on either side. A homotopy of maps into a subset takes its values in that subset. So "$f_n \simeq \mathrm{id}$ in $X_n$" means a homotopy through maps $X_n \to X_n$.

*Homotopy equivalences.* A map $f : X \to Y$ is a **homotopy equivalence** if some $g : Y \to X$ has $gf \simeq \mathrm{id}_X$ and $fg \simeq \mathrm{id}_Y$ ⟦Appendix/Telescope · IsHomotopyEquiv⟧ (§0.4). This is a property of the map. Mathlib's homotopy equivalence is instead a structure that carries both maps $f$, $g$ and the two facts $gf \simeq \mathrm{id}$, $fg \simeq \mathrm{id}$ ⟦Mathlib/Topology/Homotopy/Equiv · ContinuousMap.HomotopyEquiv⟧. The two notions convert into each other ⟦Appendix/Telescope · IsHomotopyEquiv.of_homotopyEquiv⟧ ⟦Appendix/Telescope · IsHomotopyEquiv.exists_homotopyEquiv⟧. Two spaces are *homotopy equivalent* when such a structure exists between them, as it does whenever some map between them is a homotopy equivalence ⟦Appendix/Telescope · IsHomotopyEquiv.nonempty⟧. Milnor uses four closure properties without comment, and a fifth is his Assertion of p. 22. Each has a short proof:

1. identities and homeomorphisms are homotopy equivalences ⟦Appendix/Telescope · IsHomotopyEquiv.id⟧ ⟦Appendix/Telescope · IsHomotopyEquiv.of_homeomorph⟧;
2. a composite of homotopy equivalences is one, with the composite of the inverses as inverse ⟦Appendix/Telescope · IsHomotopyEquiv.comp⟧;
3. a map homotopic to a homotopy equivalence is one, with the same inverse: if $gf \simeq \mathrm{id}$, $fg \simeq \mathrm{id}$ and $f \simeq f'$, then $gf' \simeq gf \simeq \mathrm{id}$ and $f'g \simeq fg \simeq \mathrm{id}$ ⟦Appendix/Telescope · IsHomotopyEquiv.of_homotopic⟧;
4. a homotopy inverse is itself a homotopy equivalence ⟦Appendix/Telescope · IsHomotopyEquiv.of_inverse⟧;
5. **Milnor's Assertion** (p. 22, Part II): a map $F$ with a left homotopy inverse $L$ ($LF \simeq \mathrm{id}$) and a right homotopy inverse $R$ ($FR \simeq \mathrm{id}$) is a homotopy equivalence. The proof: $L \simeq L(FR) = (LF)R \simeq R$, so $RF \simeq LF \simeq \mathrm{id}$, and $R$ is a two-sided homotopy inverse ⟦Chapter2/Attaching · homotopic_of_leftInv_rightInv⟧ ⟦Appendix/Telescope · IsHomotopyEquiv.of_leftInv_rightInv⟧. Case 2 ends with it (p. 153).

*Restrictions.* If $f : X \to Y$ carries $S \subseteq X$ into $T \subseteq Y$, then $f| : S \to T$ is its restriction ⟦Appendix/Telescope · restrictTo⟧. When $f$ carries each $X_n$ into $Y_n$, $f_n$ denotes the restriction $X_n \to Y_n$, as in Milnor.

*Clamps.* Milnor defines maps by formulas on pieces: $(x, n+2t)$ for $0 \le t \le \frac12$, another formula for $\frac12 \le t \le 1$. The formal text writes each piece as a map on the whole strip by clamping its parameter to $[0,1]$:
$$\operatorname{clamp}(s) = \min(1, \max(0, s))$$
⟦Chapter2/Attaching · clampI⟧ ⟦Mathlib/Order/Interval/Set/ProjIcc · Set.projIcc⟧. It is continuous and is the identity on $[0,1]$ ⟦Appendix/Telescope · clampI_coe⟧. It sends $s \le 0$ to $0$ and $s \ge 1$ to $1$ ⟦Appendix/Telescope · clampI_of_le_zero⟧ ⟦Appendix/Telescope · clampI_of_one_le⟧. A map defined by cases, "$F(q)$ if $a(q) \le b(q)$, $G(q)$ otherwise", is continuous when $a$, $b$, $F$ and $G$ are continuous on the whole domain and $F = G$ wherever $a = b$ ⟦Mathlib/Topology/Order/OrderClosed · Continuous.if_le⟧. Clamping is what makes each branch continuous on the whole domain. So this lemma reduces the continuity of Milnor's piecewise formulas to their agreement at the break points, which is what Milnor checks when he says that a map is well defined. On the range where a branch is actually used its clamp does nothing, and the formulas below are written without clamps.

Some statements ask that certain spaces lie in the same *universe*, a size bound on types; the condition has no mathematical content and is not mentioned again.

### XI.2 The telescope and its strips

**Definition (the telescope; Milnor p. 149).** For subsets $X_0, X_1, \dots$ of a space $X$,
$$X_\Sigma = X_0 \times [0,1] \,\cup\, X_1 \times [1,2] \,\cup\, X_2 \times [2,3] \,\cup \cdots \;\subseteq\; X \times \mathbb R,$$
with the subspace topology of $X \times \mathbb R$ ⟦Appendix/Telescope · telescope⟧ ⟦Appendix/Telescope · mem_telescope⟧.

This is exactly Milnor's definition, including his choice of topology. Every point $(x, \tau)$ of $X_\Sigma$ has $\tau \ge 0$ ⟦Appendix/Telescope · nonneg_of_mem_telescope⟧, and $\tau$ is called its *level*.

**(T1) The telescope of an increasing sequence.** If $X_0 \subseteq X_1 \subseteq \cdots$, then $(x, \tau) \in X_\Sigma$ if and only if $x \in X_n$ for some integer $0 \le n \le \tau$ ⟦Appendix/Telescope · mem_telescope_iff⟧.

*Proof.* One direction is the definition. Conversely, let $x \in X_n$ with $n \le \tau$, and let $m = \lfloor \tau \rfloor$. Then $m \ge n$, so $x \in X_m$ by monotonicity, and $m \le \tau < m+1$ puts $(x, \tau)$ on $X_m \times [m, m+1]$. $\square$

Two consequences are used constantly. *Upward closure:* if $(x, \tau) \in X_\Sigma$ and $\tau' \ge \tau$, then $(x, \tau') \in X_\Sigma$, so a homotopy that only raises levels stays in the telescope ⟦Appendix/Telescope · mem_telescope_of_le⟧. *The level determines the piece:* a point of $X_\Sigma$ at a level $\tau < n + 1$ lies over $X_n$, because (T1) gives $x \in X_m$ with $m \le \tau < n+1$, so $m \le n$ ⟦Appendix/Telescope · mem_of_mem_telescope⟧. Together they say that, for $\tau \ge 0$, $(x, \tau) \in X_\Sigma$ exactly when $x \in X_{\lfloor \tau \rfloor}$. Milnor uses all of this without comment.

*The strips as maps.* Let $i_n : X_n \to X_{n+1}$ be the inclusion ⟦Appendix/Telescope · up⟧, and let
$$\sigma_n : X_n \times I \to X_\Sigma, \qquad \sigma_n(x, t) = (x, n + t),$$
be the $n$-th strip ⟦Appendix/Telescope · stripMap⟧. Milnor writes $(x, n+t)$ for this point, and so does this part. The top of each strip is the bottom of the next: $\sigma_n(x, 1) = \sigma_{n+1}(i_n x, 0)$ ⟦Appendix/Telescope · stripMap_one⟧. Every point lies on a strip ⟦Appendix/Telescope · exists_stripMap⟧. For an increasing sequence it lies on a canonical one with $t < 1$, namely $n = \lfloor \tau \rfloor$ and $t = \tau - \lfloor \tau \rfloor$ ⟦Appendix/Telescope · exists_stripMap_lt_one⟧, and a point at an integer level $m$ is $\sigma_m(x, 0)$ ⟦Appendix/Telescope · eq_stripMap_of_level⟧; both facts use (T1) to place $x$ in $X_n$. Two functions on $X_\Sigma$ that agree on every strip are equal ⟦Appendix/Telescope · telescope_ext⟧ ⟦Appendix/Telescope · telescope_ext'⟧. Every identity between maps of telescopes in this part is proved this way, by evaluating both sides at $(x, n+t)$, as Milnor does.

### XI.3 Homotopy direct limits and the reduction to $f_\Sigma$

**Definition (Milnor p. 149).** The *projection* is $p : X_\Sigma \to X$, $p(x, \tau) = x$ ⟦Appendix/Telescope · telescopeProj⟧. $X$ is the **homotopy direct limit** of $\{X_i\}$ when $p$ is a homotopy equivalence ⟦Appendix/Telescope · IsHomotopyDirectLimit⟧.

Neither Milnor's definition nor the formal one asks that the $X_i$ cover $X$. The sufficient condition of Lemma 2.1 below forces it, and nothing in this part needs it separately.

*The induced map.* Let $f : X \to Y$ carry each $X_n$ into $Y_n$. Then $f_\Sigma(x, \tau) = (f(x), \tau)$ maps $X_\Sigma$ into $Y_\Sigma$, because $(f(x), \tau)$ lies on the same strip as $(x, \tau)$ ⟦Appendix/Telescope · mem_telescope_map⟧ ⟦Appendix/Telescope · telescopeMap⟧. On the strips, $f_\Sigma(x, n+t) = (f_n(x), n+t)$ ⟦Appendix/Telescope · telescopeMap_stripMap⟧, and $p_Y f_\Sigma = f p_X$ holds by definition ⟦Appendix/Telescope · telescopeProj_comp_telescopeMap⟧. Since $f_\Sigma$ is the restriction of $f \times \mathrm{id}_{\mathbb R}$, it is continuous without any pasting. This matters in §XI.11.

**Theorem (the reduction; Milnor p. 150).** Let $X$ and $Y$ be the homotopy direct limits of $\{X_i\}$ and $\{Y_i\}$, and let $f$ carry each $X_n$ into $Y_n$. If $f_\Sigma$ is a homotopy equivalence, so is $f$. ⟦Appendix/Telescope · IsHomotopyEquiv.of_telescopeMap⟧

Milnor dismisses this step in a single sentence. The formal statement assumes neither monotonicity nor closedness.

*Proof.* Let $s$ be a homotopy inverse of $p_X$, so $s p_X \simeq \mathrm{id}$ and $p_X s \simeq \mathrm{id}$. Then $s$ is itself a homotopy equivalence ⟦Appendix/Telescope · IsHomotopyEquiv.of_inverse⟧, and $p_Y f_\Sigma s$ is a composite of three homotopy equivalences ⟦Appendix/Telescope · IsHomotopyEquiv.comp⟧. But
$$p_Y f_\Sigma s = f p_X s \simeq f,$$
the equality by $p_Y f_\Sigma = f p_X$ and the homotopy by $p_X s \simeq \mathrm{id}$. A map homotopic to a homotopy equivalence is one ⟦Appendix/Telescope · IsHomotopyEquiv.of_homotopic⟧. $\square$

The same three lines close the proof of Theorem A without closedness (§XI.13), with mapping telescopes in place of telescopes.

### XI.4 Pasting along the strips: (T3) and the hypothesis it needs

Every map and every homotopy that Milnor writes on a telescope is given by formulas in $(x, n+t)$, strip by strip, and he never says why the result is continuous. The reason is the following lemma, and the lemma has a hypothesis.

**Theorem (T3).** Let every $X_n$ be closed in $X$, and let $P$ be any space. A function $F : P \times X_\Sigma \to Z$ is continuous as soon as, for every $n$, the function $(q, x, t) \mapsto F(q, (x, n+t))$ is continuous on $P \times X_n \times I$. ⟦Appendix/Telescope · continuous_of_stripMap⟧

*Proof as formalized.* Let $S_n = \{(q, (x, \tau)) : x \in X_n,\ n \le \tau \le n+1\}$, the $n$-th strip times $P$.

1. The $S_n$ cover $P \times X_\Sigma$, by the definition of $X_\Sigma$.
2. Each $S_n$ is closed. It is the preimage of $X_n$ under the continuous coordinate $x$, intersected with two closed inequalities in the coordinate $\tau$. This is the one place where the closedness of $X_n$ is used.
3. The family is locally finite. The open neighbourhood $\{|\tau - \tau_0| < 1\}$ of a point at level $\tau_0$ meets $S_n$ only if $n \le \tau < \tau_0 + 1$, so only for the finitely many $n < \lceil \tau_0 + 1 \rceil$.
4. $F$ is continuous on each $S_n$. The map $S_n \to P \times X_n \times I$, $(q, (x, \tau)) \mapsto (q, x, \tau - n)$, is continuous, and on $S_n$ the function $F$ is the given continuous function composed with it, since $(x, n + (\tau - n)) = (x, \tau)$.

A function continuous on each member of a locally finite cover by closed sets is continuous ⟦Mathlib/Topology/LocallyFinite · LocallyFinite.continuous⟧. $\square$

*Why closedness is needed.* Without it a strip need not be closed in $X_\Sigma$. In $X = [0,1]$ take $X_0 = (0,1]$ and $X_1 = [0,1]$. The point $(0, 1)$ lies in $X_\Sigma$, on the strip $X_1 \times [1,2]$. It is the limit of the points $(\frac1k, 1 - \frac1k)$ of the strip $X_0 \times [0,1]$, which does not contain it. So a function that is continuous on each strip is free to do anything on $X_0 \times [0,1]$ near $(0,1)$, whatever its value at $(0,1)$. §XI.10 shows that Milnor's map $g$ does exactly this for a suitable choice of homotopy.

*Maps given strip by strip.* The formal text builds all of Milnor's maps through one construction. Let $\Phi_n : P \times X_n \times I \to Z$ be continuous maps that agree at the integer levels:
$$\Phi_{n+1}(q, i_n x, 0) = \Phi_n(q, x, 1).$$
Define $F(q, (x, \tau)) = \Phi_{\lfloor \tau \rfloor}(q, x, \tau - \lfloor \tau \rfloor)$, using the canonical strip. Here $x \in X_{\lfloor\tau\rfloor}$ by (T1), and $\tau - \lfloor\tau\rfloor \in [0,1)$ ⟦Appendix/Telescope · telescopeLiftFun⟧ ⟦Appendix/Telescope · mem_floor⟧ ⟦Appendix/Telescope · fract_mem⟧. Then $F(q, (x, n+t)) = \Phi_n(q, x, t)$ for every $n$ and every $t \in I$ ⟦Appendix/Telescope · telescopeLiftFun_stripMap⟧. For $t < 1$ the floor of $n+t$ is $n$. For $t = 1$ it is $n+1$, and the compatibility condition gives the value. So $F$ is continuous on every strip, and (T3) makes it continuous ⟦Appendix/Telescope · telescopeLift⟧ ⟦Appendix/Telescope · telescopeLift_stripMap⟧.

With $P$ a point this gives maps $X_\Sigma \to Z$ ⟦Appendix/Telescope · telescopeDesc⟧ ⟦Appendix/Telescope · telescopeDesc_stripMap⟧. With $P = I$ it gives homotopies, whose two ends are checked strip by strip ⟦Appendix/Telescope · telescopeHomotopy⟧. All three constructions call (T3), so all three need the $X_n$ closed. Every map of Case 1, the reparametrizations of §XI.8 and Milnor's map $G$ of Case 2 are built with them. These constructions are the only way that closedness hypotheses enter this part.

### XI.5 Truncations: (T2)

**Definition (Milnor p. 152).** The $n$-th truncation is $X^n_\Sigma = \{(x, \tau) \in X_\Sigma : \tau \le n\}$ ⟦Appendix/Telescope · truncation⟧. For an increasing sequence it is $X_0 \times [0,1] \cup \dots \cup X_{n-1} \times [n-1, n] \cup X_n \times \{n\}$.

Whatever the $X_i$, $X^n_\Sigma$ is closed in $X_\Sigma$, being cut out by $\tau \le n$ ⟦Appendix/Telescope · isClosed_truncation⟧, and $X^0_\Sigma \subseteq X^1_\Sigma \subseteq \cdots$ ⟦Appendix/Telescope · monotone_truncation⟧. The first of these facts is what saves Case 2.

For an increasing sequence, let $\iota_n : X_n \to X^n_\Sigma$, $\iota_n(x) = (x, n)$ ⟦Appendix/Telescope · stripMap_zero_mem_truncation⟧ ⟦Appendix/Telescope · truncIncl⟧. Let $r_n : X^n_\Sigma \to X_n$, $r_n(x, \tau) = x$, which lands in $X_n$ by (T1) since $\tau \le n < n+1$ ⟦Appendix/Telescope · truncProj⟧. Both are restrictions of continuous maps of $X \times \mathbb R$, and $r_n \iota_n = \mathrm{id}$ by definition ⟦Appendix/Telescope · truncProj_comp_truncIncl⟧.

**Theorem (T2).** For an increasing sequence, $\iota_n r_n \simeq \mathrm{id}$ in $X^n_\Sigma$. Hence $\iota_n : X_n \to X^n_\Sigma$ and $r_n$ are homotopy equivalences. ⟦Appendix/Telescope · truncIncl_comp_truncProj⟧ ⟦Appendix/Telescope · isHomotopyEquiv_truncIncl⟧ ⟦Appendix/Telescope · isHomotopyEquiv_truncProj⟧

Milnor states without proof that $X^n_\Sigma$ contains $X_n \times \{n\}$ as a deformation retract (p. 152).

*Proof.* Put $D(s, (x, \tau)) = (x, (1-s)n + s\tau)$. As $\tau \le n$, the new level lies between $\tau$ and $n$. It is at least $\tau$, so $D$ stays in $X_\Sigma$ by upward closure, and it is at most $n$, so $D$ stays in $X^n_\Sigma$. $D(0, \cdot) = \iota_n r_n$ and $D(1, \cdot) = \mathrm{id}$, and $D$ is continuous as a formula in the coordinates. $\square$

No closedness is needed: the deformation is a single formula on all of $X^n_\Sigma$, not a map pasted from strips. $D$ also fixes $X_n \times \{n\}$, so it is a deformation retraction, as Milnor says. The formal statement records only what is used later, the homotopy.

**Lemma (levels).** Let $X_0 \subseteq X_1 \subseteq \cdots$, and let $F : X_\Sigma \to Z$ and $\ell : Z \to \mathbb R$ be functions. Suppose that $F$ sends the $n$-th strip to points with $\ell \le n+1$ and its bottom $X_n \times \{n\}$ to points with $\ell \le n$. Then $F$ sends $X^m_\Sigma$ to points with $\ell \le m$, for every $m$. ⟦Appendix/Telescope · level_le_of_stripMap⟧

*Proof.* Write a point of $X^m_\Sigma$ as $(x, n+t)$ on its canonical strip, with $t < 1$ and $n + t \le m$. If $t = 0$, then $\ell \le n \le m$. If $t > 0$, then $n < m$, so $n + 1 \le m$ as both are integers, and $\ell \le n + 1 \le m$. $\square$

In Case 2, $\ell$ is the level and $F$ is $Gf_\Sigma$ or $f_\Sigma G$. Milnor asserts without argument that these maps carry each truncation into itself, and this lemma is the proof.

### XI.6 Lemma 2.1 and Lemma 2.2: when the graph of a function is a deformation retract

**Lemma 2.1.** Let $X_0 \subseteq X_1 \subseteq \cdots \subseteq X$. Let $f : X \to \mathbb R$ be continuous with $f \ge 0$ and $f(x) \ge n + 1$ whenever $x \notin X_n$. Then $X$ is the homotopy direct limit of $\{X_i\}$. ⟦Appendix/Telescope · isHomotopyDirectLimit_of_level⟧

This is the mechanism of Milnor's Example 1, where he asserts without argument that the image of $x \mapsto (x, f(x))$ is a deformation retract of $X_\Sigma$ (p. 149). Once $f$ is given, it needs neither paracompactness nor closedness.

*Proof as formalized.*

1. *The graph lies in $X_\Sigma$.* Let $m = \lfloor f(x) \rfloor$. If $x \notin X_m$, then $f(x) \ge m+1 > f(x)$, which is absurd. So $x \in X_m$ with $m \le f(x)$, and $(x, f(x)) \in X_\Sigma$ by (T1).
2. *A section.* $\sigma_f(x) = (x, f(x))$ is continuous, and $p\sigma_f = \mathrm{id}_X$ by definition.
3. *The deformation.* Put $D_f(s, (x, \tau)) = (x, (1-s)f(x) + s\tau)$. It stays in $X_\Sigma$. If $\tau \le f(x)$, the new level is at least $\tau$, and upward closure applies to $(x, \tau)$. If $\tau \ge f(x)$, it is at least $f(x)$, and upward closure applies to $(x, f(x))$, which lies in $X_\Sigma$ by step 1. $D_f(0, \cdot) = \sigma_f p$ and $D_f(1, \cdot) = \mathrm{id}$, so $\sigma_f p \simeq \mathrm{id}$.

So $p$ is a homotopy equivalence with homotopy inverse $\sigma_f$. $\square$

Each $D_f(s, \cdot)$ fixes the graph of $f$, so the graph is a deformation retract, as Milnor says; the formal proof needs only the two homotopies. The hypothesis forces $\bigcup_n X_n = X$, since a point outside every $X_n$ would have $f(x) \ge n+1$ for all $n$.

Lemma 2.1 does most of the work of this part. Example 1, its form for sublevel sets, Lemma 2.2 and the corresponding fact for mapping telescopes all reduce to it, each by writing down a suitable $f$ (§§XI.7 and 11.12). So does the version of Example 1 pulled back along a map, which Part IX uses for Theorem 17.1 (§XI.13).

**Lemma 2.2.** For any sequence $X_0, X_1, \dots$ of subsets of $X$, increasing or not, closed or not, the telescope $X_\Sigma$ is the homotopy direct limit of its truncations $\{X^n_\Sigma\}$. ⟦Appendix/Telescope · isHomotopyDirectLimit_truncation⟧

*Proof.* Apply Lemma 2.1 to the space $X_\Sigma$, the increasing sequence $X^0_\Sigma \subseteq X^1_\Sigma \subseteq \cdots$, and $f(x, \tau) = \tau + 1 \ge 1$. A point outside $X^n_\Sigma$ has $\tau > n$, hence $f > n + 1$. $\square$

The telescope of the truncations is a telescope of a telescope: a subspace of $X_\Sigma \times \mathbb R$, whose points are pairs $((x, \tau), \tau')$ with $\tau \le \lfloor \tau' \rfloor$. Milnor needs Lemma 2.2 at the end of Case 2 and does not mention it (§XI.11). Example 1 would give it only if $X_\Sigma$ were paracompact, and nothing guarantees that.

### XI.7 Milnor's three examples

**Example 1 (Milnor p. 149).** Let $X$ be paracompact and Hausdorff, and let $X_0 \subseteq X_1 \subseteq \cdots$ be subsets such that every point of $X$ lies in the interior of some $X_n$. Then $X$ is the homotopy direct limit of $\{X_i\}$. ⟦Appendix/Examples · example1⟧

*Hidden hypothesis: Hausdorff.* Milnor says only paracompact. Mathlib's partitions of unity subordinate to an open cover need a space that is normal as well as paracompact ⟦Mathlib/Topology/PartitionOfUnity · PartitionOfUnity.exists_isSubordinate⟧ ⟦Mathlib/Topology/Compactness/Paracompact · ParacompactSpace⟧. A paracompact Hausdorff space is normal by Dieudonné's theorem, which Mathlib provides as an instance. So the formal statement reads paracompactness with the Hausdorff axiom included, as Bourbaki and Dugundji do.

*Proof as formalized.* Milnor's sentence, that a partition of unity gives the function, becomes the following.

1. The interiors $\operatorname{int} X_n$ form an open cover of $X$. Take a partition of unity $\{\beta_n\}$ subordinate to it: $\beta_n \ge 0$, the supports are locally finite, the support of $\beta_n$ lies in $\operatorname{int} X_n$, and $\sum_n \beta_n = 1$.
2. Put $f = \sum_n n\,\beta_n$. It is a locally finite sum, hence continuous ⟦Mathlib/Topology/PartitionOfUnity · PartitionOfUnity.continuous_finsum_smul⟧, and $f \ge 0$.
3. Let $x \notin X_i$. For $j \le i$, $\beta_j(x) = 0$: otherwise $x$ lies in the support of $\beta_j$, hence in $X_j \subseteq X_i$. The sums are finite at $x$, so
$$i + 1 = \sum_j \beta_j(x)(i+1) \le \sum_j \beta_j(x)\, j = f(x),$$
term by term: for $j \le i$ both terms vanish, and for $j > i$ one has $i + 1 \le j$.
4. Lemma 2.1 concludes. $\square$

**Sublevel sets.** Let $E : X \to \mathbb R$ be continuous, on any space $X$, and let $a_0 \le a_1 \le \cdots$ with $a_n \to \infty$. Then $X$ is the homotopy direct limit of the sublevel sets $X^{a_n} = \{E \le a_n\}$ (§0.4). ⟦Appendix/Examples · isHomotopyDirectLimit_sublevel⟧ ⟦Chapter2/Crossing · sublevel⟧

*Deviation (stronger).* No paracompactness, no Hausdorffness and no interiors are needed. This is the situation of Theorem 17.3, where Milnor's application (p. 150) appeals to Example 1 and hence to the paracompactness of the path space; here a function is written down directly.

*Proof as formalized.*

1. For each $j$ let $\theta_j(x) = \operatorname{clamp}(E(x) - a_j + 1)$. It is continuous, with values in $[0,1]$; it is $0$ where $E \le a_j - 1$ and $1$ where $E \ge a_j$.
2. *The supports are locally finite.* Given $x_0$, choose $N$ with $a_j \ge E(x_0) + 2$ for all $j \ge N$, which is possible as $a$ is increasing and tends to $\infty$. On the open neighbourhood $\{E < E(x_0) + 1\}$ of $x_0$, every $j \ge N$ has $E - a_j + 1 < 0$, so $\theta_j = 0$. Only the $\theta_j$ with $j < N$ can be nonzero near $x_0$.
3. So $f = \sum_j \theta_j$ is locally a finite sum of continuous functions, hence continuous ⟦Mathlib/Topology/Algebra/Monoid · continuous_finprod⟧ (in its additive form), and $f \ge 0$.
4. Let $x \notin X^{a_i}$. Then $E(x) > a_i \ge a_j$ for every $j \le i$, so $E(x) - a_j + 1 > 1$ and $\theta_j(x) = 1$. The remaining terms are $\ge 0$, so $f(x) \ge i + 1$.
5. The sublevel sets increase with $a_n$ ⟦Chapter2/Crossing · sublevel_mono⟧, and Lemma 2.1 concludes. $\square$

**Example 2 (Milnor p. 149) is not formalized.** It says that a CW-complex is the homotopy direct limit of an increasing sequence of subcomplexes with union the whole complex. Milnor's proof is that $p$ induces isomorphisms of all homotopy groups, so that Whitehead's theorem applies. That needs Whitehead's theorem, the fact that compact subsets of a CW-complex lie in finite subcomplexes, and the CW topology of $X \times \mathbb R$. None of them is in Mathlib. This one gap shapes the end of the Appendix. Wherever Milnor takes a union $K = \bigcup K_i$ of complexes with the weak topology, the formal text takes a mapping telescope of the $K_i$ instead (§§XI.12–11.15).

**Example 3 (Milnor p. 150).** Let $X_n = \{0\} \cup [\frac1{n+1}, 1] \subseteq [0,1]$ ⟦Appendix/Examples · example3Set⟧. Milnor writes $[0] \cup [1/i, 1]$, indexing from $1$. These sets are closed ⟦Appendix/Examples · isClosed_example3Set⟧ and increasing ⟦Appendix/Examples · monotone_example3Set⟧. Their union is $[0,1]$, since every $x > 0$ exceeds some $\frac1{n+1}$ ⟦Appendix/Examples · iUnion_example3Set⟧. Then $[0,1]$ is **not** the homotopy direct limit of $\{X_n\}$. ⟦Appendix/Examples · example3⟧

Milnor gives no proof.

*Proof as formalized.* Suppose that $p : X_\Sigma \to [0,1]$ has a homotopy inverse $s$, and let $\Lambda$ be a homotopy from $sp$ to the identity of $X_\Sigma$. Only this half of the hypothesis will be used. Let $C = \{(x, \tau) \in X_\Sigma : x = 0\}$, the ray $\{0\} \times [0, \infty)$.

1. *$C$ is open and closed in $X_\Sigma$.* It is closed as the preimage of $0$. For openness, let $(0, \tau_0) \in C$ and consider the open set
$$W = \{(x, \tau) \in X_\Sigma : x < \tfrac1{\tau_0 + 2},\ \tau < \tau_0 + 1\},$$
which contains $(0, \tau_0)$. Suppose a point $(x, \tau)$ of $W$ had $x \ne 0$. It would lie on some strip $n$, with $n \le \tau$ and $x \ge \frac1{n+1}$. Then $\frac1{n+1} < \frac1{\tau_0 + 2}$ gives $n > \tau_0 + 1 > \tau \ge n$, which is absurd. So $W \subseteq C$. In words: below the level $\tau_0 + 1$, every point of the telescope off the ray has first coordinate at least $\frac1{\tau_0+2}$.
2. *Paths cannot leave $C$.* For a path $\gamma : I \to X_\Sigma$, the set $\gamma^{-1}(C)$ is open and closed in the connected interval, hence empty or everything ⟦Mathlib/Topology/Connected/Clopen · isClopen_iff⟧. So $\gamma(0) \in C$ if and only if $\gamma(1) \in C$.
3. *Three paths.* The path $u \mapsto \Lambda(u, (0, 0))$ runs from $sp(0,0) = s(0)$ to $(0,0)$. The map $s$ itself is a path from $s(0)$ to $s(1)$, its domain being $[0,1]$. The path $u \mapsto \Lambda(u, (1, 0))$ runs from $s(1)$ to $(1, 0)$. As $(0, 0) \in C$, step 2 gives $s(0) \in C$, then $s(1) \in C$, then $(1, 0) \in C$, which is false. $\square$

The proof shows more than the statement: $p$ has no left homotopy inverse at all. The point $0$ lies in every $X_n$ but in the interior of none, so the hypothesis of Example 1 fails at a single point, and the telescope separates that point from the rest.

### XI.8 Theorem A, and reparametrizing the strips

**Theorem A (Milnor p. 150).** Let $X$ be the homotopy direct limit of $X_0 \subseteq X_1 \subseteq \cdots$ and $Y$ that of $Y_0 \subseteq Y_1 \subseteq \cdots$. Let $f : X \to Y$ carry each $X_i$ into $Y_i$ by a homotopy equivalence $f_i : X_i \to Y_i$. Then $f$ is a homotopy equivalence.

The formal text proves it twice. The first version assumes the $Y_i$ closed and follows Milnor's proof ⟦Appendix/TheoremA · theoremA⟧ (§XI.11). The second is exactly Milnor's statement ⟦Appendix/MonotoneUnion · theoremA_general⟧ (§XI.13). Milnor's proof has three steps:

1. the reduction to $f_\Sigma$ (§XI.3);
2. Case 1, where $X = Y$, $X_i = Y_i$ and each $f_i$ is homotopic to the identity (§§XI.9–11.10);
3. Case 2, the general case, which builds a homotopy inverse $G$ of $f_\Sigma$ and applies Case 1 to $Gf_\Sigma$ and $f_\Sigma G$ (§XI.11).

In this section and in §§XI.9–11.10, $X_0 \subseteq X_1 \subseteq \cdots$ are **closed** in $X$, so that (T3) is available.

*Reparametrizing the strips.* Twice Milnor declares two maps homotopic without argument when they differ by a change of speed inside the strips (pp. 151 and 152). Let $\rho : I \to I$ be continuous with $\rho(0) = 0$ and $\rho(1) = 1$, and put
$$R_\rho(x, n+t) = (x, n + \rho(t)).$$
It is pasted from the strips: at an integer level both neighbouring formulas give $(x, n+1)$, because $\rho$ fixes $0$ and $1$ ⟦Appendix/TheoremA · reparam⟧ ⟦Appendix/TheoremA · reparam_stripMap⟧.

**Lemma.** $R_\rho \simeq \mathrm{id}$. ⟦Appendix/TheoremA · reparam_homotopic⟧

*Proof.* Take the straight-line homotopy $(s, (x, n+t)) \mapsto (x, n + (1-s)\rho(t) + st)$. It stays inside each strip, since a convex combination of two numbers in $[0,1]$ lies in $[0,1]$. It agrees at the integer levels for every $s$, since both $\rho$ and the identity fix $0$ and $1$. It is $R_\rho$ at $s = 0$ and the identity at $s = 1$, and it is assembled strip by strip as in §XI.4. $\square$

The case that is used is $R_c(x, n+t) = (x, n + \min(ct, 1))$ for $c \ge 1$, from $\rho(t) = \operatorname{clamp}(ct)$ ⟦Appendix/TheoremA · scaleI⟧ ⟦Appendix/TheoremA · scaleMap⟧ ⟦Appendix/TheoremA · scaleMap_stripMap⟧ ⟦Appendix/TheoremA · scaleMap_homotopic⟧. Milnor's $h_0$ is $f_\Sigma R_2$ (§XI.10), and his homotopies $H_u$ end at $R_4$ (§XI.9).

### XI.9 Milnor's maps $h_1$, their inverse $g$, and the homotopies $H_u$ and $K_u$

Milnor's proof of Case 1 deforms $f_\Sigma$ to a map $h_1$ with two properties. He then shows that *any* map with these two properties is a homotopy equivalence (p. 151). The formal text isolates the class of such maps.

**Definition (Milnor maps).** A map $\psi : X_\Sigma \to X_\Sigma$ is a *Milnor map* if

- (low) $\psi(x, n+t) = (x, n+2t)$ for $0 \le t \le \frac12$, and
- (high) $\psi(x, n+t)$ has level $n+1$ for $\frac12 \le t \le 1$. ⟦Appendix/TheoremA · IsMilnorMap⟧

In the second condition Milnor asks that $h_1(x, n+t) \in X_{n+1} \times \{n+1\}$. Asking only for the level is the same, since a point of $X_\Sigma$ at level $n+1$ lies over $X_{n+1}$ by (T1).

*Elementary properties.* A Milnor map fixes every point at an integer level: such a point is $(x, m + 0)$, and (low) at $t = 0$ returns it ⟦Appendix/TheoremA · IsMilnorMap.fix⟧. Milnor uses this without saying so when he computes $h_1 g$. It follows that $\psi(\psi(x, n+t)) = \psi(x, n+t)$ for $t \ge \frac12$, the inner value being at level $n+1$ ⟦Appendix/TheoremA · IsMilnorMap.fix_high⟧. It also follows that $\psi(x, n+1) = (x, n+1)$ ⟦Appendix/TheoremA · IsMilnorMap.apply_one⟧, and (low) gives $\psi(x, n+\frac12) = (x, n+1)$. The formal text packages the last two facts as $\psi(x, n + \frac12 + \frac\mu2) = (x, n+1)$ for $\mu \in \{0, 1\}$ ⟦Appendix/TheoremA · IsMilnorMap.apply_half_or_one⟧.

So for each $x \in X_n$ the path $s \mapsto \psi(x, n + s)$, $\frac12 \le s \le 1$, is a **loop** at $(x, n+1)$. Every homotopy below shrinks this loop. It is convenient to parametrize the loop by $\mu \in [0,1]$, with $s = \frac12 + \frac\mu2$.

**Milnor's inverse $g$ (p. 151).**
$$g(x, n+t) = \begin{cases} (x, n+2t) & 0 \le t \le \frac12, \\ \psi(x, n + \frac32 - t) & \frac12 \le t \le 1. \end{cases}$$
⟦Appendix/TheoremA · milnorInvStrip⟧ ⟦Appendix/TheoremA · milnorInv⟧

At $t = \frac12$ both lines give $(x, n+1)$, because $\psi(x, n+1) = (x, n+1)$. Between strips, the top of strip $n$ gives $\psi(x, n + \frac12) = (x, n+1)$ and the bottom of strip $n+1$ gives $(x, n+1)$. This is Milnor's remark that $g$ is well defined because $h_1$ takes the value $(x, n+1)$ at both $n + \frac12$ and $n + 1$. The map is pasted from the strips by (T3).

$g$ is a Milnor map itself ⟦Appendix/TheoremA · milnorInv_low⟧ ⟦Appendix/TheoremA · milnorInv_high⟧ ⟦Appendix/TheoremA · milnorInv_isMilnorMap⟧. Property (low) is its first line. For (high): at $t = \frac12$ the first line has level $n+1$, and for $t > \frac12$ the value $\psi(x, n + \frac32 - t)$ has level $n+1$ because $\frac32 - t \ge \frac12$. In particular $g$ also fixes the integer levels.

*The two composites.* Using only these facts,
$$\psi g(x, n+t) = \begin{cases} (x, n+4t) & t \le \frac14, \\ \psi(x, n+2t) & \frac14 \le t \le \frac12, \\ \psi(x, n+\frac32 - t) & \frac12 \le t \le 1, \end{cases} \qquad g\psi(x, n+t) = \begin{cases} (x, n+4t) & t \le \frac14, \\ \psi(x, n+\frac32 - 2t) & \frac14 \le t \le \frac12, \\ \psi(x, n+t) & \frac12 \le t \le 1. \end{cases}$$
For $\psi g$: if $t \le \frac12$, $g$ gives $(x, n+2t)$, to which $\psi$ applies (low) when $2t \le \frac12$; if $t \ge \frac12$, $g$ gives a point at level $n+1$, which $\psi$ fixes. For $g\psi$: if $t \le \frac14$ both maps act by (low); if $\frac14 \le t \le \frac12$, $\psi$ gives $(x, n+2t)$ with $2t \ge \frac12$, and $g(x, n+2t) = \psi(x, n + \frac32 - 2t)$; if $t \ge \frac12$, $\psi$ gives a point at level $n+1$, which $g$ fixes. On $[\frac14, 1]$, $\psi g$ runs along the loop forwards, $\mu$ going from $0$ to $1$, and then backwards. $g\psi$ runs backwards and then forwards.

**The loop homotopies.** For a continuous function $\mu(u, t)$, define on each strip
$$L^\mu_u(x, n+t) = \begin{cases} (x, n+4t) & t \le \frac14, \\ \psi\big(x, n + \frac12 + \frac12\mu(u, t)\big) & t \ge \frac14. \end{cases}$$
⟦Appendix/TheoremA · loopFun⟧

This is continuous on each strip times $I$ when the two lines agree at $t = \frac14$, where the first gives $(x, n+1)$. By the packaged property above, that holds when $\mu(u, \frac14) \in \{0, 1\}$ ⟦Appendix/TheoremA · continuous_loopFun⟧. The strips fit together when $\mu(u, 1) \in \{0, 1\}$, since then the top of strip $n$ is $(x, n+1)$, the bottom of strip $n+1$. (T3) then makes $(u, z) \mapsto L^\mu_u(z)$ a homotopy ⟦Appendix/TheoremA · loopHomotopy⟧. If $\mu(1, t) \in \{0, 1\}$ for $\frac14 < t \le 1$, the end $L^\mu_1$ is $R_4$, since every point with $t \ge \frac14$ goes to $(x, n+1)$ ⟦Appendix/TheoremA · loopFun_one⟧. Milnor's two homotopies are two choices of $\mu$.

*Milnor's $H_u$.* Take $\mu_H(u, t) = \min(4t - 1,\ 1 - u,\ 2 - 2t)$ ⟦Appendix/TheoremA · muH⟧ ⟦Appendix/TheoremA · continuous_muH⟧.

- At $u = 0$ it is $4t - 1$ on $[\frac14, \frac12]$ and $2 - 2t$ on $[\frac12, 1]$ ⟦Appendix/TheoremA · muH_zero_low⟧ ⟦Appendix/TheoremA · muH_zero_high⟧. Then $\frac12 + \frac12\mu_H$ is $2t$, respectively $\frac32 - t$, and $L^{\mu_H}_0 = \psi g$.
- At $u = 1$ it vanishes on $[\frac14, 1]$ ⟦Appendix/TheoremA · muH_one⟧, so $L^{\mu_H}_1 = R_4$.
- It vanishes at $t = \frac14$ and at $t = 1$ for every $u$ ⟦Appendix/TheoremA · muH_quarter⟧ ⟦Appendix/TheoremA · muH_end⟧.

Hence there is a homotopy $\psi g \simeq R_4$ ⟦Appendix/TheoremA · milnorH⟧.

This is Milnor's $H_u$ of p. 151, written as one formula. Milnor's parameter runs over $[0, \frac12]$. With $u_M = u/2$, the cap $\mu \le 1 - u$ means $s \le 1 - u_M$: his homotopy cuts the excursion along the loop at the point $\psi(x, n + 1 - u_M)$. The minimum switches from $4t - 1$ to $1 - u$ at $t = \frac{1 - u_M}2$, and from $1 - u$ to $2 - 2t$ at $t = \frac12 + u_M$; these are exactly his break points. His end $H_{1/2}$ is $R_4$, which he declares homotopic to the identity without argument; the lemma of §XI.8 is the proof.

*The analogous homotopy $K_u$.* For $g\psi$, Milnor says only that an analogous argument applies (p. 152). The formal text takes $\mu_K(u, t) = \max(2 - 4t,\ 2t - 1,\ u)$ ⟦Appendix/TheoremA · muK⟧ ⟦Appendix/TheoremA · continuous_muK⟧.

- At $u = 0$ it is $2 - 4t$ on $[\frac14, \frac12]$ and $2t - 1$ on $[\frac12, 1]$ ⟦Appendix/TheoremA · muK_zero_low⟧ ⟦Appendix/TheoremA · muK_zero_high⟧. Then $\frac12 + \frac12\mu_K$ is $\frac32 - 2t$, respectively $t$, so $L^{\mu_K}_0 = g\psi$.
- At $u = 1$ it is $1$ on $[\frac14, 1]$ ⟦Appendix/TheoremA · muK_one⟧, so $L^{\mu_K}_1 = R_4$, as $\psi(x, n+1) = (x, n+1)$.
- It equals $1$ at $t = \frac14$ and at $t = 1$ for every $u$ ⟦Appendix/TheoremA · muK_quarter⟧ ⟦Appendix/TheoremA · muK_end⟧.

Hence there is a homotopy $g\psi \simeq R_4$ ⟦Appendix/TheoremA · milnorK⟧. Where $H_u$ caps the loop from above, $K_u$ cuts it from below: the part of the loop with $\mu < u$ is never visited, and at $u = 1$ nothing of the loop remains.

**Theorem (Milnor's maps are homotopy equivalences; pp. 151–152).** For closed $X_n$, every Milnor map $\psi$ is a homotopy equivalence, with homotopy inverse $g$. ⟦Appendix/TheoremA · isHomotopyEquiv_of_milnorMap⟧

*Proof.* $g\psi \simeq R_4 \simeq \mathrm{id}$ and $\psi g \simeq R_4 \simeq \mathrm{id}$, by the two loop homotopies and §XI.8. $\square$

The formal proofs that the loop homotopies start at $\psi g$ and at $g\psi$ are the case analyses displayed above for the two composites, over the three ranges $t \le \frac14$, $\frac14 < t \le \frac12$ and $t > \frac12$.

### XI.10 Case 1

**Theorem (Case 1; Milnor pp. 150–152).** Let $X_0 \subseteq X_1 \subseteq \cdots$ be closed in $X$. Let $\varphi : X \to X$ carry each $X_n$ into itself by a map $\varphi_n$ that is homotopic, in $X_n$, to the identity of $X_n$. Then $\varphi_\Sigma : X_\Sigma \to X_\Sigma$ is a homotopy equivalence. ⟦Appendix/TheoremA · theoremA_case1⟧

Milnor's Case 1 assumes $X_i = Y_i$; the formal statement takes $Y = X$ and a self-map $\varphi$. It does not assume that $X$ is a homotopy direct limit.

Choose homotopies $h^n_u : X_n \to X_n$, $0 \le u \le 1$, with $h^n_0 = \varphi_n$ and $h^n_1 = \mathrm{id}$. The formal proof picks one for each $n$ from the hypothesis.

**Milnor's $h_u$, corrected.** On the $n$-th strip,
$$h_u(x, n+t) = \begin{cases} (h^n_u(x),\ n + 2t) & 0 \le t \le \frac12, \\ (h^n_{(3-4t)u}(x),\ n+1) & \frac12 \le t \le \frac34, \\ (h^{n+1}_{(4t-3)u}(x),\ n+1) & \frac34 \le t \le 1. \end{cases}$$
⟦Appendix/TheoremA · case1Fun⟧

*The misprint.* Milnor prints the third line as $h^{n+1}_{(4-3t)u}$ (p. 151). At $t = 1$ the printed index happens to give the right value $u$. At $t = \frac34$, however, it gives $h^{n+1}_{7u/4}$, which is not even defined for $u > \frac47$, while continuity at $t = \frac34$ requires $h^{n+1}_0$ there. The correct index $(4t-3)u$ runs from $0$ at $t = \frac34$ to $u$ at $t = 1$. The second line, $h^n_{(3-4t)u}$, is printed correctly.

Read along the strip, $h_u$ first rises to the top of the strip while applying $h^n_u$. It then runs the homotopy $h^n$ back from time $u$ to time $0$, arriving at $\varphi(x)$. Finally it runs the next homotopy $h^{n+1}$ forward from time $0$ to time $u$, arriving at the value from which the next strip starts.

*Continuity on a strip* ⟦Appendix/TheoremA · continuous_case1Fun⟧. At $t = \frac12$, the first line gives $(h^n_u x, n+1)$ as a point at the top of strip $n$. The second line gives the same point, since $(3 - 2)u = u$, as a point at the bottom of strip $n+1$. They are equal by the gluing of strips. At $t = \frac34$ both indices are $0$. Since $h^n_0 = \varphi_n$ and $h^{n+1}_0 = \varphi_{n+1}$, both lines give $(\varphi(x), n+1)$; here one uses that $\varphi_{n+1}$ and $\varphi_n$ are restrictions of the same $\varphi$. The clamps make each line continuous on $I \times X_n \times I$, and the case-splitting lemma of §XI.1 does the rest.

*Compatibility between strips* ⟦Appendix/TheoremA · case1Fun_compat⟧. At the top of strip $n$ the third line gives $(h^{n+1}_u x, n+1)$, as $(4 - 3)u = u$. At the bottom of strip $n+1$ the first line gives the same point.

By (T3) with $P = I$, $(u, z) \mapsto h_u(z)$ is continuous on $I \times X_\Sigma$ ⟦Appendix/TheoremA · case1Family⟧ ⟦Appendix/TheoremA · case1Map⟧ ⟦Appendix/TheoremA · case1Map_stripMap⟧. So $h_0 \simeq h_1$.

**$h_0 = \varphi_\Sigma R_2$** ⟦Appendix/TheoremA · case1Map_zero⟧. At $u = 0$ all three indices are $0$, and $h^n_0 = \varphi_n$. So
$$h_0(x, n+t) = (\varphi(x), n + \min(2t, 1)) = \varphi_\Sigma(x, n + \min(2t, 1)) = \varphi_\Sigma R_2(x, n+t).$$
As $R_2 \simeq \mathrm{id}$, $h_0 \simeq \varphi_\Sigma$. Milnor takes this homotopy as evident (p. 151).

**$h_1$ is a Milnor map** ⟦Appendix/TheoremA · case1Map_one⟧. At $u = 1$ the first line is $(h^n_1 x, n+2t) = (x, n+2t)$, which is (low). For $t \ge \frac12$ every line is at level $n+1$, which is (high).

*Proof of Case 1.* $\varphi_\Sigma \simeq h_0 \simeq h_1$, and $h_1$ is a homotopy equivalence by §XI.9. A map homotopic to a homotopy equivalence is one. $\square$

*Why Case 1 needs closed sets.* All of its maps are pasted from strips of $X_\Sigma$: $h_u$, $g$, $H_u$, $K_u$, $R_2$ and $R_4$. Without closedness the construction itself can fail, not only its formal proof. The retelling gives an example, which is not formalized. Let $X = [0,1]$, $X_0 = (0,1]$, $X_n = X$ for $n \ge 1$ and $\varphi = \mathrm{id}$. Take $h^n_u = \mathrm{id}$ for $n \ge 1$, and for $h^0_u$ a homotopy from the identity of $(0,1]$ to itself that, at the time $u = 1 - \frac x2$, pushes the point $x$ all the way to $1$:
$$h^0_u(x) = x + (1-x)\max\Big(0,\ 1 - \frac{|u - 1 + x/2|}{x/2}\Big).$$
For $t = 1 - \frac x8$, Milnor's $g$ gives
$$g(x, t) = h_1(x, \tfrac12 + \tfrac x8) = (h^0_{1 - x/2}(x), 1) = (1, 1).$$
But $(x, 1 - \frac x8) \to (0, 1)$ as $x \to 0$, and $g(0, 1) = (0, 1)$. So $g$ is discontinuous at $(0,1)$: the strip $X_0 \times [0,1]$ is not closed, exactly as in §XI.4. (The formal text does not ask whether the conclusion of Case 1 survives without closedness: below, Case 1 is applied only to truncations, which are closed.)

*The Remark (p. 150).* Milnor observes that under the hypotheses of Case 1 one might expect $\varphi_\Sigma$ to be homotopic to the identity, and says without an example that it need not be. **This is not formalized.** The retelling gives a counterexample built from a phantom map. The map goes from the telescope of $S^1 \xrightarrow{z^2} S^1 \xrightarrow{z^2} \cdots$ to $\mathbb{CP}^\infty$; it is null-homotopic on every finite stage but detected by the second cohomology of the telescope. The example needs cellular cohomology and $\mathbb{CP}^\infty$, which are not available. What is formalized is the positive statement, that $\varphi_\Sigma$ is a homotopy equivalence.

### XI.11 Case 2, and Theorem A with closed $Y_i$

The heart of Case 2 is a statement about self-maps of a single telescope, which the formal text isolates.

**Theorem (self-maps that preserve the truncations).** Let $X_0 \subseteq X_1 \subseteq \cdots$ be any increasing sequence in $X$, closed or not. Let $F : X_\Sigma \to X_\Sigma$ carry each truncation $X^m_\Sigma$ into itself, and suppose that $F(x, m) = (e_m(x), m)$ for maps $e_m : X_m \to X_m$ homotopic to the identity. Then $F$ is a homotopy equivalence. ⟦Appendix/TheoremA · isHomotopyEquiv_of_truncation⟧

*Proof as formalized.* Apply the reduction of §XI.3 with the space $X_\Sigma$ in place of $X$, its sequence of truncations $\{X^m_\Sigma\}$ on both sides, and the self-map $F$. Both sides are homotopy direct limits by Lemma 2.2. So it suffices that the induced map $F_\Sigma$ of the telescope of the truncations, a subspace of $X_\Sigma \times \mathbb R$, is a homotopy equivalence. That is Case 1 for the space $X_\Sigma$, the closed sets $X^m_\Sigma$ (§XI.5) and the self-map $F$. Case 1 asks that each restriction $F_m : X^m_\Sigma \to X^m_\Sigma$ be homotopic to the identity. With $\iota = \iota_m$ and $r = r_m$ the maps of (T2),
$$F_m \simeq F_m\,\iota\, r = \iota\, e_m\, r \simeq \iota\, r \simeq \mathrm{id}.$$
The first homotopy is $\iota r \simeq \mathrm{id}$ (T2); the equality is the hypothesis $F(x, m) = (e_m x, m)$; the second homotopy is $e_m \simeq \mathrm{id}$; the last is (T2) again. $\square$

This is the step that Milnor compresses into one sentence (p. 152). He says there that $X^n_\Sigma$ deformation retracts onto $X_n \times \{n\}$, that $Gf_\Sigma$ restricted there is $g_n f_n$ and hence homotopic to the identity, and that Case 1 therefore applies to the sequence $\{X^n_\Sigma\}$. Two things are left implicit. First, Case 1 concludes that the induced map of the telescope of $\{X^n_\Sigma\}$ is a homotopy equivalence; to come back to $Gf_\Sigma$ itself one needs $X_\Sigma$ to be the homotopy direct limit of its truncations, which is Lemma 2.2. Second, Case 1 needs closed sets, and the truncations are closed whatever the $X_n$ are.

**Milnor's map $G$.** Now let $f : X \to Y$ carry each $X_n$ into $Y_n$ by a homotopy equivalence $f_n$, and choose homotopy inverses $g_n : Y_n \to X_n$. Let $i_n : X_n \to X_{n+1}$ and $j_n : Y_n \to Y_{n+1}$ be the inclusions.

*The squares commute up to homotopy* ⟦Appendix/TheoremA · homotopic_square⟧:
$$i_n g_n \simeq g_{n+1} f_{n+1}\, i_n g_n = g_{n+1}\, j_n f_n\, g_n \simeq g_{n+1} j_n.$$
The steps use $g_{n+1} f_{n+1} \simeq \mathrm{id}$, then $f_{n+1} i_n = j_n f_n$ (both are restrictions of $f$), then $f_n g_n \simeq \mathrm{id}$. This is Milnor's computation (p. 152). Choose homotopies $k^n_u : Y_n \to X_{n+1}$ with $k^n_0 = i_n g_n$ and $k^n_1 = g_{n+1} j_n$; these are Milnor's $h^n_u$, renamed to avoid a clash with Case 1. Define on the strips of $Y_\Sigma$
$$G(y, n+t) = \begin{cases} (g_n(y),\ n + 2t) & 0 \le t \le \frac12, \\ (k^n_{2t-1}(y),\ n+1) & \frac12 \le t \le 1. \end{cases}$$
⟦Appendix/TheoremA · case2InvStrip⟧ ⟦Appendix/TheoremA · case2Inv⟧ ⟦Appendix/TheoremA · case2Inv_stripMap⟧

At $t = \frac12$ both lines give $(g_n y, n+1)$, as $k^n_0 = i_n g_n$. At the top of the strip the second line gives $(g_{n+1} y, n+1)$, as $k^n_1 = g_{n+1} j_n$, and this is the bottom of the next strip. $G$ is pasted from the strips of $Y_\Sigma$, so it needs the $Y_n$ closed. It has two properties ⟦Appendix/TheoremA · case2Inv_level⟧ ⟦Appendix/TheoremA · case2Inv_zero⟧: it carries the $n$-th strip of $Y_\Sigma$ to levels $\le n+1$, and $G(y, n) = (g_n(y), n)$. From here on the formal proof forgets the formula for $G$ and uses only these two properties.

**Theorem (Case 2: $f_\Sigma$ is a homotopy equivalence).** Let $X_0 \subseteq X_1 \subseteq \cdots$ in $X$ and $Y_0 \subseteq Y_1 \subseteq \cdots$ in $Y$, with the $Y_n$ closed. Let $f : X \to Y$ carry each $X_n$ into $Y_n$ by a homotopy equivalence. Then $f_\Sigma : X_\Sigma \to Y_\Sigma$ is a homotopy equivalence. ⟦Appendix/TheoremA · theoremA_telescope⟧

*Deviation.* This is narrower than Milnor's Case 2 by the closedness of the $Y_n$. It is stronger in two ways: there is no homotopy direct limit hypothesis, and no closedness of the $X_n$.

*Proof as formalized.*

1. *$Gf_\Sigma$ is a homotopy equivalence.* $f_\Sigma$ carries the $n$-th strip of $X_\Sigma$ to the $n$-th strip of $Y_\Sigma$, and $G$ carries that to levels $\le n+1$. The bottom point $(x, n)$ goes to $G(f(x), n) = (g_n f_n x, n)$, at level $n$. By the lemma on levels (§XI.5), $Gf_\Sigma$ carries each $X^m_\Sigma$ into itself ⟦Appendix/Telescope · level_le_of_stripMap⟧. Moreover $Gf_\Sigma(x, m) = (g_m f_m(x), m)$ with $g_m f_m \simeq \mathrm{id}$. The theorem above applies, with $e_m = g_m f_m$.
2. *$f_\Sigma G$ is a homotopy equivalence*, in the same way on $Y_\Sigma$. $G$ carries strip $n$ to levels $\le n+1$, and $f_\Sigma$ preserves levels. Moreover $f_\Sigma G(y, m) = (f_m g_m(y), m)$ with $f_m g_m \simeq \mathrm{id}$.
3. Let $k_1$ be a homotopy inverse of $Gf_\Sigma$. Then $(k_1 G) f_\Sigma \simeq \mathrm{id}$, so $k_1 G$ is a left homotopy inverse of $f_\Sigma$. Let $k_2$ be a homotopy inverse of $f_\Sigma G$. Then $f_\Sigma (G k_2) \simeq \mathrm{id}$, so $G k_2$ is a right homotopy inverse. By Milnor's Assertion (§XI.1), $f_\Sigma$ is a homotopy equivalence ⟦Appendix/Telescope · IsHomotopyEquiv.of_leftInv_rightInv⟧. $\square$

**Theorem A, by Milnor's proof.** Let $X$ be the homotopy direct limit of $X_0 \subseteq X_1 \subseteq \cdots$ and $Y$ that of $Y_0 \subseteq Y_1 \subseteq \cdots$, with the $Y_i$ closed in $Y$. Let $f : X \to Y$ carry each $X_i$ into $Y_i$ by a homotopy equivalence. Then $f$ is a homotopy equivalence. ⟦Appendix/TheoremA · theoremA⟧

*Proof.* Case 2 and the reduction of §XI.3. $\square$

*Why only the $Y_i$ need to be closed.* Follow the pasting. In Case 2 the only map pasted from the strips of a telescope of the original sets is $G$, on $Y_\Sigma$. Case 1 is used only for the truncations of $X_\Sigma$ and of $Y_\Sigma$, which are closed in any case. $f_\Sigma$ is not pasted at all, and (T2), Lemma 2.2 and the lemma on levels need nothing. So the one closedness hypothesis of Milnor's proof concerns the target sets. In his application they are subcomplexes $K_i$ of a CW-complex, hence closed. In Theorem 17.1, however, Part IX applies Theorem A to open subsets of path spaces, and there the hypothesis has to go.

### XI.12 The mapping telescope

Two things make the formal text replace Milnor's telescope by a mapping telescope. The first is closedness. In $X_\Sigma$ a map given strip by strip is known to be continuous only when the strips are closed (§XI.4), while the mapping telescope carries the topology in which every such map is continuous. The second is that the complexes $K_i$ of Theorem 17.3 and of the Corollary are not subspaces of one space in this project. Attaching a cell is a pushout in the category of topological spaces ⟦Chapter2/Attaching · AttachCell⟧. It comes with a map $K \to K \cup e^\lambda$ ⟦Chapter2/Attaching · cellInl⟧ rather than an inclusion of subsets, so a sequence of complexes is a sequence of spaces and maps.

*Sequences.* A sequence $K_0 \xrightarrow{c_0} K_1 \xrightarrow{c_1} K_2 \to \cdots$ is a functor from $\mathbb N$ to topological spaces. For $m \le n$ write $c_{m,n} : K_m \to K_n$ for the composite ⟦Appendix/MappingTelescope · tmap⟧, so that $c_{n,n} = \mathrm{id}$ and $c_{m,n}c_{l,m} = c_{l,n}$ ⟦Appendix/MappingTelescope · tmap_refl⟧ ⟦Appendix/MappingTelescope · tmap_tmap⟧. Thus $c_n = c_{n,n+1}$.

**Definition (the mapping telescope).** $\operatorname{Tel}(K)$ is the disjoint union of the blocks $K_n \times I$, each with the product topology, divided by the relation $(k, 1)_n \sim (c_n k, 0)_{n+1}$, with the quotient topology ⟦Appendix/MappingTelescope · MapTelRel⟧ ⟦Appendix/MappingTelescope · MappingTelescope⟧.

Write $[k, t]_n$ for the class of $(k, t)$ in the $n$-th block ⟦Appendix/MappingTelescope · MappingTelescope.mk⟧. So $[k, 1]_n = [c_n k, 0]_{n+1}$ ⟦Appendix/MappingTelescope · MappingTelescope.mk_one⟧, every point has this form ⟦Appendix/MappingTelescope · MappingTelescope.exists_mk⟧, and $(k, t) \mapsto [k, t]_n$ is continuous ⟦Appendix/MappingTelescope · MappingTelescope.isQuotientMap_quotMk⟧ ⟦Appendix/MappingTelescope · MappingTelescope.continuous_mk⟧. The mapping telescope is not in the book; the retelling uses it to prove the Corollary.

*Maps out of the mapping telescope, block by block.* Let $\Phi_n : K_n \times I \to Z$ be continuous with $\Phi_{n+1}(c_n k, 0) = \Phi_n(k, 1)$. Then $[k, t]_n \mapsto \Phi_n(k, t)$ is a well-defined continuous map $\operatorname{Tel}(K) \to Z$ ⟦Appendix/MappingTelescope · MappingTelescope.desc⟧ ⟦Appendix/MappingTelescope · MappingTelescope.desc_mk⟧. The $\Phi_n$ together are continuous on the disjoint union ⟦Mathlib/Topology/Constructions · continuous_sigma⟧ and respect the relation, so they descend to the quotient ⟦Mathlib/Topology/Constructions · continuous_quot_lift⟧. There is no hypothesis: this is (T3) without closedness.

*With a parameter.* Let $P$ be a locally compact space and $\Phi_n : P \times K_n \times I \to Z$ continuous and compatible in the same way. Then $(q, [k, t]_n) \mapsto \Phi_n(q, k, t)$ is continuous on $P \times \operatorname{Tel}(K)$ ⟦Appendix/MappingTelescope · MappingTelescope.lift⟧ ⟦Appendix/MappingTelescope · MappingTelescope.lift_mk⟧. The formal proof goes through the exponential law. Each $\Phi_n$ curries to a continuous map $K_n \times I \to C(P, Z)$, the space of maps with the compact-open topology ⟦Mathlib/Topology/CompactOpen · ContinuousMap.curry⟧. These are compatible, so they descend to a continuous map $\operatorname{Tel}(K) \to C(P, Z)$. Uncurrying it gives a continuous map on $\operatorname{Tel}(K) \times P$, because $P$ is locally compact ⟦Mathlib/Topology/CompactOpen · ContinuousMap.uncurry⟧. This is J. H. C. Whitehead's lemma that the product of a quotient map with a locally compact space is a quotient map, in the form the formal proof uses. With $P = I$ it gives homotopies, block by block ⟦Appendix/MappingTelescope · MappingTelescope.homotopy⟧. Two maps that agree on every block are equal ⟦Appendix/MappingTelescope · MappingTelescope.ext⟧.

*Levels and truncations.* The level $\ell[k, t]_n = n + t$ is well defined, as $(n+1) + 0 = n + 1$; it is continuous and $\ge 0$ ⟦Appendix/MappingTelescope · MappingTelescope.level⟧ ⟦Appendix/MappingTelescope · MappingTelescope.level_mk⟧ ⟦Appendix/MappingTelescope · MappingTelescope.level_nonneg⟧. The truncations $\operatorname{Tel}^n(K) = \{\ell \le n\}$ are closed and increasing ⟦Appendix/MappingTelescope · MappingTelescope.trunc⟧ ⟦Appendix/MappingTelescope · MappingTelescope.isClosed_trunc⟧ ⟦Appendix/MappingTelescope · MappingTelescope.monotone_trunc⟧. $\operatorname{Tel}(K)$ is the homotopy direct limit of $\{\operatorname{Tel}^n(K)\}$, by Lemma 2.1 with $f = \ell + 1$ ⟦Appendix/MappingTelescope · MappingTelescope.isHomotopyDirectLimit_trunc⟧.

**Theorem ((T2) for mapping telescopes).** The map $\kappa_n : K_n \to \operatorname{Tel}^n(K)$, $\kappa_n(k) = [k, 0]_n$, is a homotopy equivalence. ⟦Appendix/MappingTelescope · MappingTelescope.mk_zero_mem_trunc⟧ ⟦Appendix/MappingTelescope · MappingTelescope.levelIncl⟧ ⟦Appendix/MappingTelescope · MappingTelescope.isHomotopyEquiv_levelIncl⟧

In $X_\Sigma$ this was a one-line deformation, because every point has a coordinate $x$ that does not change as the level rises. A mapping telescope has no such coordinate. A point $[k, t]_m$ of $\operatorname{Tel}^n(K)$ must be pushed up through the blocks $m, m+1, \dots, n$, and its first coordinate changes on the way, from $k$ to $c_m k$, to $c_{m+1}c_m k$, and so on. The formal proof takes four steps.

*1. Trajectories.* For $k \in K_m$ and a height $s \in [0, d+1]$, the point at height $s$ above $[k, 0]_m$ along the maps $c$ is
$$\operatorname{traj}_d(m, k, s) = \begin{cases} [k, s]_m & s \le 1, \\ \operatorname{traj}_{d-1}(m+1, c_m k, s - 1) & s > 1, \end{cases}$$
with $\operatorname{traj}_0(m, k, s) = [k, \operatorname{clamp}(s)]_m$ ⟦Appendix/MappingTelescope · MappingTelescope.traj⟧ ⟦Appendix/MappingTelescope · MappingTelescope.traj_of_le_one⟧ ⟦Appendix/MappingTelescope · MappingTelescope.traj_zero_right⟧. It is continuous in $(k, s)$, by induction on $d$; the two cases agree at $s = 1$ because $[k, 1]_m = [c_m k, 0]_{m+1}$ ⟦Appendix/MappingTelescope · MappingTelescope.continuous_traj⟧. Its level is $m + s$ for $0 \le s \le d+1$ ⟦Appendix/MappingTelescope · MappingTelescope.level_traj⟧.

*2. The push.* On the block $m$ put
$$\operatorname{push}_n(s, [k, t]_m) = \operatorname{traj}_{d}\big(m, k,\ t + s\max(0,\, n - m - t)\big), \qquad d = \max(n - m, 0)$$
⟦Appendix/MappingTelescope · MappingTelescope.pushFun⟧. For a point at level $m + t \le n$, the height rises linearly from $t$ at $s = 0$ to $n - m$ at $s = 1$, that is, to level $n$. A point at level $\ge n$ does not move. Each block formula is continuous ⟦Appendix/MappingTelescope · MappingTelescope.continuous_pushFun⟧, and the formulas agree at the gluing ⟦Appendix/MappingTelescope · MappingTelescope.pushFun_compat⟧. For $m < n$: the trajectory of $k$ from height $1$ in block $m$ is the trajectory of $c_m k$ from height $0$ in block $m+1$. If $s\max(0, n-m-1) = 0$, both are the point $[k,1]_m = [c_m k, 0]_{m+1}$; otherwise the recursion steps into the next block. For $m \ge n$, both sides are the point itself. By the parameter version of block-by-block maps, $\operatorname{push}_n : I \times \operatorname{Tel}(K) \to \operatorname{Tel}(K)$ is continuous ⟦Appendix/MappingTelescope · MappingTelescope.push⟧. It starts at the identity ⟦Appendix/MappingTelescope · MappingTelescope.push_zero⟧ and fixes each $[k, 0]_n$ ⟦Appendix/MappingTelescope · MappingTelescope.push_bottom⟧. On $\operatorname{Tel}^n(K)$ it moves levels by $\ell(\operatorname{push}_n(s, z)) = \ell(z) + s(n - \ell(z))$ ⟦Appendix/MappingTelescope · MappingTelescope.level_push⟧. So it keeps $\operatorname{Tel}^n(K)$ in itself ⟦Appendix/MappingTelescope · MappingTelescope.push_mem_trunc⟧ and ends at level $n$ ⟦Appendix/MappingTelescope · MappingTelescope.level_push_one⟧.

*3. Reading off the point at level $n$.* Every point at level exactly $n$ is $[k, 0]_n$ for some $k$ ⟦Appendix/MappingTelescope · MappingTelescope.exists_mk_zero_of_level⟧. Indeed, if it is $[k, t]_m$ with $m + t = n$, then either $t = 1$, and it is $[c_m k, 0]_{m+1}$ with $m + 1 = n$; or $t < 1$, and then $m = n$ and $t = 0$. The $k$ is unique. Consider the function that sends $[k, t]_m$ to $c_{m,n}(k)$ when $m + t = n$, and to nothing otherwise. It respects the gluing, because $c_{m+1,n}c_m = c_{m,n}$, so it is defined on the mapping telescope ⟦Appendix/MappingTelescope · MappingTelescope.atLevel⟧. At $[k, 0]_n$ it returns $k$ ⟦Appendix/MappingTelescope · MappingTelescope.atLevel_mk_zero⟧, so $\kappa_n$ is injective ⟦Appendix/MappingTelescope · MappingTelescope.mk_zero_injective⟧.

*4. $\kappa_n$ is an embedding* ⟦Appendix/MappingTelescope · MappingTelescope.isInducing_mk_zero⟧: every open $V \subseteq K_n$ is $\kappa_n^{-1}(W)$ for an open $W \subseteq \operatorname{Tel}(K)$. Let $S$ be the set of points $(k', t)$ of the blocks $m \le n$ with $|m + t - n| < \frac12$ and $c_{m,n}(k') \in V$. In each block $S$ is open: it is an open condition on $t$ intersected with the preimage of $V$ under the continuous $c_{m,n}$, and it is empty for $m > n$. It is saturated for the gluing. A top point $(k, 1)_m$ within $\frac12$ of level $n$ has $m + 1 = n$, and then it lies in $S$ exactly when $(c_m k, 0)_{m+1}$ does, as $c_{m+1,n} c_m = c_{m,n}$. So $S$ is the preimage of an open set $W$ of the quotient. At level exactly $n$ the condition defining $S$ reads $k \in V$, so $\kappa_n^{-1}(W) = V$.

*Proof of the theorem.* Using step 3, define $q_n : \operatorname{Tel}^n(K) \to K_n$ by $[q_n(z), 0]_n = \operatorname{push}_n(1, z)$ ⟦Appendix/MappingTelescope · MappingTelescope.push_one_eq⟧ ⟦Appendix/MappingTelescope · MappingTelescope.levelRetract⟧ ⟦Appendix/MappingTelescope · MappingTelescope.mk_levelRetract⟧. It is continuous because $\kappa_n q_n = \operatorname{push}_n(1, \cdot)$ is continuous and $\kappa_n$ is an embedding ⟦Mathlib/Topology/Maps/Basic · IsInducing.continuous_iff⟧. Next, $q_n \kappa_n = \mathrm{id}$, by injectivity and because $\operatorname{push}_n$ fixes $[k, 0]_n$ ⟦Appendix/MappingTelescope · MappingTelescope.levelRetract_levelIncl⟧ ⟦Appendix/MappingTelescope · MappingTelescope.levelRetract_comp_levelIncl⟧. Finally, $s \mapsto \operatorname{push}_n(s, \cdot)$ is a homotopy in $\operatorname{Tel}^n(K)$ from the identity to $\kappa_n q_n$ ⟦Appendix/MappingTelescope · MappingTelescope.levelIncl_comp_levelRetract⟧. So $\kappa_n$ and $q_n$ are homotopy equivalences ⟦Appendix/MappingTelescope · MappingTelescope.isHomotopyEquiv_levelRetract⟧. $\square$

In $X_\Sigma$ the retraction $r_n$ was simply $(x, \tau) \mapsto x$. Here the $K_n$ are not subspaces of a common space, so the retraction has to be read off at level $n$, and the embedding is what makes it continuous. Part XII uses the same push to compute the homotopy groups of mapping telescopes ⟦Homotopy/Telescope · bijective_homotopyGroupMap_telescopeIncl⟧.

### XI.13 Theorem A with no closedness

**The mapping telescope of the inclusions.** For an increasing sequence $X_0 \subseteq X_1 \subseteq \cdots$, the inclusions form a sequence of spaces and maps ⟦Appendix/MonotoneUnion · subspaceFunctor⟧. Write $T_X$ for its mapping telescope and $T^m_X$ for its truncations, with the maps $\kappa^X_m$ and $q^X_m$ of §XI.12. The comparison map
$$c_X : T_X \to X_\Sigma, \qquad [x, t]_n \mapsto (x, n+t),$$
is continuous block by block, the gluing being respected because $\sigma_n(x, 1) = \sigma_{n+1}(x, 0)$ ⟦Appendix/MonotoneUnion · telescopeComparison⟧ ⟦Appendix/MonotoneUnion · telescopeComparison_mk⟧. It is a bijection, an elementary check that the formal text never needs. Through it, $T_X$ is the set $X_\Sigma$ with the finest topology in which every strip $X_n \times I \to X_\Sigma$ is continuous.

**Theorem.** For closed $X_n$, $c_X$ is a homeomorphism. ⟦Appendix/MonotoneUnion · telescopeComparisonHomeomorph⟧

*Proof.* The inverse $(x, n+t) \mapsto [x, t]_n$ is given strip by strip, compatibly because $[x, 1]_n = [x, 0]_{n+1}$, and it is continuous by (T3). The two composites are the identity, as one checks on blocks and on strips. $\square$

So for closed sets the mapping telescope of the inclusions *is* Milnor's telescope, and (T3) says exactly that the subspace topology of $X_\Sigma$ is then the colimit topology of the strips. For arbitrary sets the two topologies may differ, but not up to homotopy.

**Theorem.** For any increasing sequence, $c_X$ is a homotopy equivalence. ⟦Appendix/MonotoneUnion · isHomotopyEquiv_telescopeComparison⟧

*Proof.* Apply Theorem A of §XI.11, the version with closed targets. The source is the space $T_X$ with its truncations $T^m_X$. The target is the space $X_\Sigma$ with its truncations $X^m_\Sigma$, which are closed. The map is $c_X$. Both spaces are homotopy direct limits of their truncations (§XI.12 and Lemma 2.2), and $c_X$ carries $T^m_X$ into $X^m_\Sigma$ because it preserves levels. It remains to see that each restriction $R_m : T^m_X \to X^m_\Sigma$ is a homotopy equivalence. Now $R_m \kappa^X_m = \iota_m$, as both send $x$ to $(x, m)$, so
$$R_m \simeq R_m\, \kappa^X_m\, q^X_m = \iota_m\, q^X_m,$$
using $\kappa^X_m q^X_m \simeq \mathrm{id}$. And $\iota_m q^X_m$ is a composite of homotopy equivalences, by (T2) for both telescopes. $\square$

Consequently, if $X$ is the homotopy direct limit of $\{X_n\}$, then $\pi_X = p\,c_X : T_X \to X$, $[x, t]_n \mapsto x$, is a homotopy equivalence ⟦Appendix/MonotoneUnion · telescopeProj'⟧ ⟦Appendix/MonotoneUnion · isHomotopyEquiv_telescopeProj'⟧.

*The induced map.* Let $f$ carry each $X_n$ into $Y_n$. Then $\Phi_f[x, t]_n = [f(x), t]_n$ is a continuous map $T_X \to T_Y$, built block by block with no hypothesis ⟦Appendix/MonotoneUnion · mappingTelescopeMap⟧ ⟦Appendix/MonotoneUnion · mappingTelescopeMap_mk⟧. It preserves levels, hence the truncations ⟦Appendix/MonotoneUnion · mapsTo_mappingTelescopeMap⟧.

**Theorem A, as Milnor states it.** Let $X$ be the homotopy direct limit of $X_0 \subseteq X_1 \subseteq \cdots$ and $Y$ that of $Y_0 \subseteq Y_1 \subseteq \cdots$, arbitrary subsets. Let $f : X \to Y$ carry each $X_i$ into $Y_i$ by a homotopy equivalence. Then $f$ is a homotopy equivalence. ⟦Appendix/MonotoneUnion · theoremA_general⟧

*Proof as formalized.*

1. *$\Phi_f$ is a homotopy equivalence.* Apply Theorem A with closed targets to $T_X$ with its truncations $T^m_X$, to $T_Y$ with its truncations $T^m_Y$, which are closed, and to $\Phi_f$. Both spaces are homotopy direct limits of their truncations. The restriction $R_m : T^m_X \to T^m_Y$ satisfies $R_m \kappa^X_m = \kappa^Y_m f_m$, so
$$R_m \simeq R_m\, \kappa^X_m\, q^X_m = \kappa^Y_m\, f_m\, q^X_m,$$
a composite of three homotopy equivalences.
2. *Commutation.* $f\,\pi_X = \pi_Y\,\Phi_f$, since both send $[x, t]_n$ to $f(x)$; this is checked block by block.
3. *Conclusion*, as in §XI.3. Let $s$ be a homotopy inverse of $\pi_X$. Then $\pi_Y \Phi_f s$ is a composite of homotopy equivalences, and it equals $f \pi_X s \simeq f$. $\square$

*Where the closedness went.* Milnor's proof is run with the truncations $T^m_X \subseteq T_X$ and $T^m_Y \subseteq T_Y$ in the roles of his $X_i \subseteq X$ and $Y_i \subseteq Y$. Inside it, Case 2 pastes $G$ on the telescope of the closed sets $T^m_Y$, and Case 1 works with truncations of telescopes; nothing else is pasted. The closedness that Milnor's proof needs is thus a property of the subspace topology on $X_\Sigma$, not of the theorem.

*Where it is used.* In Part IX, Theorem 17.1 says that the inclusion of the piecewise smooth paths $\Omega$ into all continuous paths $\Omega^*$ is a homotopy equivalence. It is proved by Theorem A for open sets: the sets $Y_k \subseteq \Omega^*$ of paths whose dyadic pieces of level $k$ lie in good balls, and their preimages $X_k \subseteq \Omega$. $\Omega^*$ is metric, hence paracompact, so it is the homotopy direct limit of the $Y_k$ by Example 1. In the formal model $\Omega$ is not Hausdorff (its paths are functions on $\mathbb R$, and the metric sees only $[0,1]$), so for $\Omega$ Example 1 is pulled back along the inclusion instead ⟦Chapter10/FullPathSpace · isHomotopyDirectLimit_preimage⟧. The $X_k$ and $Y_k$ are open, not closed, so the version without closedness is the one applied ⟦Chapter10/FullPathTheorem · JoinSystem.isHomotopyEquiv_toPathC⟧ ⟦Chapter10/FullPathTheorem · theorem_17_1⟧.

### XI.14 Monotone unions and the Corollary

**Theorem (subspace form).** Let $X$ be the homotopy direct limit of $X_0 \subseteq X_1 \subseteq \cdots$. Let $Y_0 \subseteq Y_1 \subseteq \cdots$ be closed in $Y$, and let $f : X \to Y$ carry each $X_i$ into $Y_i$ by a homotopy equivalence. Then $X$ is homotopy equivalent to $Y_\Sigma$. ⟦Appendix/MonotoneUnion · nonempty_homotopyEquiv_telescope⟧

*Proof.* $p : X_\Sigma \to X$ is a homotopy equivalence by hypothesis, and so is $f_\Sigma : X_\Sigma \to Y_\Sigma$ by Case 2 (§XI.11). Compose an inverse of the first with the second. $\square$

Here $Y$ need not be a homotopy direct limit, since the conclusion names $Y_\Sigma$, not $Y$. By (T3) the topology of $Y_\Sigma$ is the colimit topology of the strips (§XI.13), so it depends only on the topologies of the $Y_i$. If $Y$ is a CW-complex and the $Y_i$ are subcomplexes, then $Y_\Sigma \simeq Y$ is Example 2, which is not formalized. That is why the telescope, not $Y$, appears in the conclusion.

**Lemma (squares of inverses).** Suppose $ja \simeq a'i$, and $b$, $b'$ satisfy $ab \simeq \mathrm{id}$ and $b'a' \simeq \mathrm{id}$. Then $ib \simeq b'j$, because
$$ib \simeq b'a'\,ib \simeq b'\,j\,ab \simeq b'j.$$
⟦Appendix/MonotoneUnion · homotopic_inverse_square⟧

This is the computation of Milnor's square in Case 2, made abstract.

**Theorem (mapping telescope form).** Let $X$ be the homotopy direct limit of $X_0 \subseteq X_1 \subseteq \cdots$, closed or not. Let $K_0 \xrightarrow{c_0} K_1 \xrightarrow{c_1} \cdots$ be any sequence of spaces and maps, and let $g_n : X_n \to K_n$ be homotopy equivalences with $c_n g_n \simeq g_{n+1} i_n$ on $X_n$. Then $X$ is homotopy equivalent to $\operatorname{Tel}(K)$. ⟦Appendix/MonotoneUnion · nonempty_homotopyEquiv_mappingTelescope⟧

*Deviation (stronger).* In Milnor's application the ladder commutes strictly, and his $K_i$ are subcomplexes of one complex. Here the squares need only commute up to homotopy, and the $K_n$ are arbitrary spaces.

*Proof as formalized.*

1. Choose homotopy inverses $g'_n$ of $g_n$. By the lemma on squares, $i_n g'_n \simeq g'_{n+1} c_n : K_n \to X_{n+1}$; choose homotopies $k^n_u$ from $i_n g'_n$ to $g'_{n+1} c_n$.
2. Define $\Psi : \operatorname{Tel}(K) \to X_\Sigma$ block by block, as Milnor defined $G$:
$$\Psi[k, t]_n = \begin{cases} (g'_n(k),\ n + 2t) & 0 \le t \le \frac12, \\ (k^n_{2t-1}(k),\ n+1) & \frac12 \le t \le 1. \end{cases}$$
⟦Appendix/MonotoneUnion · compareStrip⟧ ⟦Appendix/MonotoneUnion · compareMap⟧ ⟦Appendix/MonotoneUnion · compareMap_mk⟧ The checks at $t = \frac12$ and at $t = 1$ are those for $G$, with $c_n$ in place of $j_n$. Since $\Psi$ is defined out of a mapping telescope, it is continuous with no closedness at all.
3. $\Psi[k, 0]_n = (g'_n(k), n)$ ⟦Appendix/MonotoneUnion · compareMap_mk_zero⟧, and $\Psi$ carries $\operatorname{Tel}^m(K)$ into $X^m_\Sigma$ ⟦Appendix/MonotoneUnion · compareMap_mapsTo⟧. A point $[k, t]_n$ of $\operatorname{Tel}^m(K)$ with $t = 0$ goes to level $n \le m$. If $t > 0$, then $n < m$, so $n + 1 \le m$, and $\Psi$ lands at a level $\le n+1$.
4. $\Psi$ is a homotopy equivalence ⟦Appendix/MonotoneUnion · isHomotopyEquiv_compareMap⟧. This is Theorem A with closed targets, for $\operatorname{Tel}(K)$ with its truncations and $X_\Sigma$ with its closed truncations; both spaces are homotopy direct limits of their truncations. The restriction $R_m : \operatorname{Tel}^m(K) \to X^m_\Sigma$ satisfies $R_m \kappa_m = \iota_m g'_m$, so $R_m \simeq \iota_m g'_m q_m$, a composite of homotopy equivalences.
5. So $X \simeq X_\Sigma \simeq \operatorname{Tel}(K)$, the first by hypothesis. $\square$

The direction of $\Psi$ is chosen so that it starts from the mapping telescope, where pasting is free. The closedness that $G$ needed in Case 2 is then never needed. In particular no closedness of the $X_n$ is assumed, here or in the Corollary.

**The Corollary (Milnor p. 153).** If $X$ is the homotopy direct limit of $\{X_i\}$ and each $X_i$ has the homotopy type of a CW-complex, then so does $X$. Milnor gives no proof, remarking only that it is not hard. The formal statements replace the CW-complexes in two ways.

**Theorem (the Corollary, in the telescope model).** Let $X$ be the homotopy direct limit of $X_0 \subseteq X_1 \subseteq \cdots$, and let $e_n : X_n \to K_n$ be homotopy equivalences, with homotopy inverses $e'_n$. With the maps $c_n = e_{n+1}\, i_n\, e'_n : K_n \to K_{n+1}$, $X$ is homotopy equivalent to the mapping telescope of $K_0 \to K_1 \to \cdots$. ⟦Appendix/MonotoneUnion · corollary_appendix⟧ ⟦Mathlib/CategoryTheory/Functor/OfSequence · Functor.ofSequence⟧

*Proof.* $c_n e_n = e_{n+1} i_n e'_n e_n \simeq e_{n+1} i_n$, as $e'_n e_n \simeq \mathrm{id}$. The mapping telescope form applies with $g_n = e_n$. $\square$

**Theorem (the Corollary for finite cell complexes).** If each $X_n$ has the homotopy type of a finite iterated adjunction space with cells $\mathrm{cells}_n$ (§0.5) ⟦Chapter2/CWType · IsFiniteCellComplexType⟧ ⟦Chapter2/CWType · IsCellAttachment⟧, then $X$ is homotopy equivalent to the mapping telescope of a sequence of such spaces. ⟦Appendix/MonotoneUnion · corollary_cellComplex⟧

*Proof.* Choose the spaces and the homotopy equivalences, and apply the previous theorem. $\square$

*What is not proved* is that the mapping telescope is itself a CW-complex. That needs cellular approximation, to replace the $c_n$ by cellular maps, and the CW structure of the mapping telescope of cellular maps. Neither is in Mathlib, and the retelling's proof of the Corollary uses both. The formal Corollary therefore ends with a mapping telescope.

### XI.15 Cell towers and the topological part of Theorem 17.3

The countable CW-complexes of Theorem 17.3 are built by attaching cells, finitely many at each stage. The formal model keeps the stages and the maps between them, and takes their mapping telescope for the union.

**Definition (relative cell attachment).** $K$ is obtained from $L$ by attaching cells of dimensions $(\lambda_1, \dots, \lambda_k)$, with map $j : L \to K$, if it is obtained by attaching a $\lambda_1$-cell to $L$, then a $\lambda_2$-cell to the result, and so on, each along an arbitrary continuous map of its boundary sphere into the space built so far. The map $j$ is the composite of the maps $K' \to K' \cup e^\lambda$ ⟦Appendix/MonotoneUnion · IsRelCellAttachment⟧.

If $L$ is a finite iterated adjunction space with cells $c$, and $K$ is obtained from $L$ by attaching cells $c'$, then $K$ is a finite iterated adjunction space with cells $c$ followed by $c'$ ⟦Appendix/MonotoneUnion · IsCellAttachment.of_rel⟧. The proof is by induction on the attachments. With no cells there is nothing to do. With one more cell, attach it to the space that has cells $c$ followed by the earlier part of $c'$.

**Definition (cell towers).** A *cell tower* with cells $\mathrm{cells}_0, \mathrm{cells}_1, \dots$ (finite lists of dimensions) is a sequence $K_0 \to K_1 \to \cdots$ with two properties. $K_0$ is a finite iterated adjunction space with cells $\mathrm{cells}_0$. Each $K_{n+1}$ is obtained from $K_n$ by attaching the cells $\mathrm{cells}_{n+1}$, and the map $K_n \to K_{n+1}$ is the attachment map ⟦Appendix/MonotoneUnion · CellTower⟧.

Each stage $K_n$ is then a finite iterated adjunction space with the cells $\mathrm{cells}_0, \dots, \mathrm{cells}_n$, in this order ⟦Appendix/MonotoneUnion · CellTower.isCellAttachment⟧, by induction on $n$ with the previous lemma. A tower can be given by its stages and maps, which is how an inductive construction produces it ⟦Appendix/MonotoneUnion · CellTower.ofSequence⟧ ⟦Appendix/MonotoneUnion · CellTower.tmap_ofSequence⟧.

**Definition (§0.5).** $X$ *has the homotopy type of a countable cell complex* with cells $\mathrm{cells}_0, \mathrm{cells}_1, \dots$ if it is homotopy equivalent to the mapping telescope of some cell tower with these cells ⟦Appendix/MonotoneUnion · IsCountableCellComplexType⟧. The property passes to homotopy equivalent spaces ⟦Appendix/MonotoneUnion · IsCountableCellComplexType.of_homotopyEquiv⟧.

*Deviation (narrower).* This is weaker than having the homotopy type of a CW-complex in two ways. The attaching maps need not be cellular. And the mapping telescope of the tower stands for the union of its stages with the weak topology, to which it is homotopy equivalent by Example 2, which is not formalized.

**Theorem (towers).** Let $X$ be the homotopy direct limit of $X_0 \subseteq X_1 \subseteq \cdots$. Let $g_n : X_n \to K_n$ be homotopy equivalences to the stages of a cell tower with $c_n g_n \simeq g_{n+1} i_n$. Then $X$ has the homotopy type of the countable cell complex. ⟦Appendix/MonotoneUnion · isCountableCellComplexType_of_tower⟧

*Proof.* The mapping telescope form of §XI.14. $\square$

**Theorem 17.3, the topological part (Milnor p. 150).** Let $E : X \to \mathbb R$ be continuous and $a_0 \le a_1 \le \cdots$ with $a_n \to \infty$. Let $g_n : X^{a_n} \to K_n$ be homotopy equivalences from the sublevel sets $X^{a_n} = \{E \le a_n\}$ to the stages of a cell tower, each extending the previous one: $c_n g_n = g_{n+1}$ on $X^{a_n}$. Then $X$ has the homotopy type of the countable cell complex with cells $\mathrm{cells}_0, \mathrm{cells}_1, \dots$. ⟦Appendix/MonotoneUnion · isCountableCellComplexType_of_sublevel⟧

*Proof.* The sublevel sets increase, and $X$ is their homotopy direct limit by §XI.7, with no paracompactness. Equal maps are homotopic, so the squares commute up to homotopy. The previous theorem applies. $\square$

The variant with the tower given by its stages and maps is the form that an inductive construction produces ⟦Appendix/MonotoneUnion · isCountableCellComplexType_of_sublevel'⟧.

*Comparison with Milnor's alternative step* (p. 150). Milnor has homotopy equivalences $\Omega^{a_i} \to K_i$ that form a strictly commutative ladder with the inclusions. He takes the union map $\Omega \to K = \bigcup K_i$ and applies Theorem A with Examples 1 and 2. The formal proof differs at three points.

- The hypotheses Milnor leaves implicit are stated: $a_i \to \infty$, so that the sublevel sets exhaust $X$; $E$ continuous; and each map extending the previous one, without which no union map exists.
- No union map is formed, since $K = \bigcup K_i$ with its weak topology is not available. The homotopy equivalence $X \simeq \operatorname{Tel}(K)$ is built in the other direction, from homotopy inverses, by Milnor's map $G$ of Case 2.
- Example 1 is replaced by its sublevel form of §XI.7.

*Where it is used.* In Part IX, Theorem 17.3 is proved with towers that commute only up to homotopy, through the theorem on towers above ⟦Chapter10/RelativeCells · isCountableCellComplexType_of_rel⟧ ⟦Chapter10/RelativeCells · isCountableCellComplexType_of_relSublevel⟧ ⟦Chapter10/FundamentalTheorem · theorem_17_3⟧. So even the strict extension property is not needed there.

### XI.16 What the formalization taught us

- **Pasting needs closed strips.** Every map Milnor defines on a telescope is given strip by strip, and it is continuous when the $X_n$ are closed (T3) ⟦Appendix/Telescope · continuous_of_stripMap⟧. Case 1 as written needs them ⟦Appendix/TheoremA · theoremA_case1⟧, and otherwise his $g$ can be discontinuous.
- **Milnor's proof of Theorem A needs only the $Y_i$ closed.** Case 2 applies Case 1 only to truncations of telescopes, which are always closed ⟦Appendix/Telescope · isClosed_truncation⟧, and it pastes only $G$ on a telescope of the original sets ⟦Appendix/TheoremA · theoremA_telescope⟧.
- **Theorem A is true as Milnor states it.** Run on mapping telescopes, where pasting is automatic, his proof needs no closedness at all ⟦Appendix/MonotoneUnion · theoremA_general⟧. Theorem 17.1 needs exactly this, for open pieces ⟦Chapter10/FullPathTheorem · JoinSystem.isHomotopyEquiv_toPathC⟧.
- **A silent lemma.** Case 2 returns from the telescope of the truncations to $X_\Sigma$ through Lemma 2.2, which holds with no hypothesis at all ⟦Appendix/Telescope · isHomotopyDirectLimit_truncation⟧.
- **A possible misprint.** The third line of $h_u$ is $h^{n+1}_{(4t-3)u}$, not $h^{n+1}_{(4-3t)u}$ ⟦Appendix/TheoremA · case1Fun⟧.
- **Evident steps become formulas.** $h_0 = f_\Sigma R_2$ ⟦Appendix/TheoremA · case1Map_zero⟧. Milnor's $H_u$ and the analogous $K_u$ are single formulas with $\mu = \min(4t-1, 1-u, 2-2t)$ and $\mu = \max(2-4t, 2t-1, u)$ ⟦Appendix/TheoremA · milnorH⟧ ⟦Appendix/TheoremA · milnorK⟧. The computation of $h_1 g$ uses that $h_1$ fixes the integer levels ⟦Appendix/TheoremA · IsMilnorMap.fix⟧. That $Gf_\Sigma$ preserves the truncations is a lemma about levels ⟦Appendix/Telescope · level_le_of_stripMap⟧.
- **Paracompactness is not needed for sublevel sets** ⟦Appendix/Examples · isHomotopyDirectLimit_sublevel⟧, and Example 1 needs the Hausdorff axiom as well as paracompactness ⟦Appendix/Examples · example1⟧.
- **Example 3 has a short proof** once one sees that the ray over $0$ is open and closed in the telescope ⟦Appendix/Examples · example3⟧.
- **CW-complexes become mapping telescopes.** Without Whitehead's theorem, Example 2 is out of reach, so the Corollary and Theorem 17.3 conclude with a mapping telescope of iterated adjunction spaces ⟦Appendix/MonotoneUnion · corollary_cellComplex⟧ ⟦Appendix/MonotoneUnion · isCountableCellComplexType_of_sublevel⟧. The squares need only commute up to homotopy ⟦Appendix/MonotoneUnion · nonempty_homotopyEquiv_mappingTelescope⟧.
- **(T2) is harder for mapping telescopes.** Points must be pushed up through the blocks, and the continuity of the retraction rests on $k \mapsto [k, 0]_n$ being an embedding ⟦Appendix/MappingTelescope · MappingTelescope.isInducing_mk_zero⟧.
