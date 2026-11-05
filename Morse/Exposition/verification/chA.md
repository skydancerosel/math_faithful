## Appendix (Milnor pp. 149–153): partly verified

Milnor's Appendix gives an alternative final step for the proof of Theorem 17.3. For subspaces
$X_0 \subseteq X_1 \subseteq \cdots$ of a space $X$ it defines the telescope $X_\Sigma \subseteq X
\times \mathbb R$ and calls $X$ the homotopy direct limit of $\{X_i\}$ if the projection
$X_\Sigma \to X$ is a homotopy equivalence (p. 149). Examples 1–3 (pp. 149–150) give two sufficient
conditions (the interiors of the $X_i$ cover a paracompact $X$; the $X_i$ are subcomplexes of a
CW-complex) and a counterexample. Theorem A (p. 150) says that a map of homotopy direct limits that
carries each $X_i$ into $Y_i$ by a homotopy equivalence is a homotopy equivalence; it is proved by
reduction to the map of telescopes, in two cases (pp. 150–153), and gives the final step of 17.3.
The Corollary (p. 153) says that a homotopy direct limit of spaces of the homotopy type of
CW-complexes has that homotopy type. Verified, for arbitrary topological spaces: telescopes,
homotopy direct limits, and the facts Milnor uses about them without comment ((T1)–(T3) and Lemmas
2.1–2.2 of the exposition); Examples 1 and 3; Milnor's proof of Theorem A in both cases, with the
misprint $(4 - 3t)u$ corrected to $(4t - 3)u$; **Theorem A exactly as Milnor states it, with no
closedness hypothesis** (VA.15); the Corollary, with a mapping telescope in place of a CW-complex;
and the topological part of Theorem 17.3, for a space exhausted by sublevel sets of a continuous
function. The proof departs from Milnor's in one respect. **Milnor's maps are defined strip by
strip**, which makes them continuous only when the sets are closed (T3): Case 1 as written needs
the $X_i$ closed; Case 2 applies Case 1 only to truncations of telescopes, which are always closed,
and pastes only one map, $G$, on the telescope of the $Y_i$, so his proof of Theorem A needs only
the $Y_i$ closed (VA.12); and the same proof run on mapping
telescopes, where pasting is automatic, needs no closedness at all (VA.15). **Not verified:**
Example 2 (Whitehead's theorem), a counterexample for the Remark, and the CW structure of
mapping telescopes (cellular approximation), so that "CW-complex" becomes a mapping telescope of
iterated adjunction spaces (the list at the end). Lean: `Morse/Appendix/` — `Telescope.lean` (630
lines), `Examples.lean` (239), `TheoremA.lean` (765), `MappingTelescope.lean` (517),
`MonotoneUnion.lean` (569).

**Conventions.** Spaces are arbitrary topological spaces, with no separation axiom unless one is
stated; maps are continuous; subsets carry the subspace topology; $I = [0, 1]$. Sequences are
indexed from $0$. A sequence of subsets $X_0, X_1, \dots$ of $X$ is *monotone* if
$X_0 \subseteq X_1 \subseteq \cdots$; Milnor's sequences always are, and most statements below
assume it. Homotopies of maps into a subset take values in that subset.

**VA.1 (homotopy equivalences; `Morse.IsHomotopyEquiv`, `Morse.IsHomotopyEquiv.comp`,
`Morse.IsHomotopyEquiv.of_homotopic`, `Morse.IsHomotopyEquiv.of_inverse`,
`Morse.IsHomotopyEquiv.of_leftInv_rightInv`, `Morse.restrictTo`).** A map $f : X \to Y$ is a
*homotopy equivalence* if there is a map $g : Y \to X$ with $gf \simeq \mathrm{id}_X$ and
$fg \simeq \mathrm{id}_Y$. A composite of homotopy equivalences is one; a map homotopic to a
homotopy equivalence is one; a homotopy inverse is one; and a map with a left homotopy inverse and
a right homotopy inverse is a homotopy equivalence. If $f$ carries $A \subseteq X$ into
$B \subseteq Y$, $f|A : A \to B$ is its restriction. *Book:* p. 22, Assertion: if a map $F$ has a
left homotopy inverse $L$ and a right homotopy inverse $R$, then $F$ is a homotopy equivalence;
p. 153 refers to it ("compare page 22"). *Hidden hypotheses:* none. *Deviation (not in the
book):* the closure properties, used throughout without comment.

**VA.2 (the telescope and homotopy direct limits; `Morse.telescope`, `Morse.mem_telescope_iff`,
`Morse.mem_telescope_of_le`, `Morse.stripMap`, `Morse.telescopeProj`,
`Morse.IsHomotopyDirectLimit`).** For subsets $X_0, X_1, \dots$ of $X$, the *telescope* is
$X_\Sigma = \bigcup_n X_n \times [n, n + 1] \subseteq X \times \mathbb R$, with the subspace
topology; the $n$-th *strip* is the map $X_n \times [0, 1] \to X_\Sigma$, $(x, t) \mapsto
(x, n + t)$; $p : X_\Sigma \to X$ is $p(x, \tau) = x$; and $X$ is the *homotopy direct limit* of
$\{X_i\}$ if $p$ is a homotopy equivalence. **(T1)** For a monotone sequence, $(x, \tau) \in
X_\Sigma$ iff $x \in X_n$ for some integer $n \ge 0$ with $n \le \tau$; so $(x, \tau) \in X_\Sigma$
and $\tau' \ge \tau$ give $(x, \tau') \in X_\Sigma$. *Book:* p. 149: for subspaces $X_0 \subset X_1
\subset \cdots$, the infinite union $X_\Sigma = X_0 \times [0, 1] \cup X_1 \times [1, 2] \cup
\cdots$, "to be topologized as a subset of $X \times \mathbb R$"; Definition: $X$ is the homotopy
direct limit of $\{X_i\}$ if $p : X_\Sigma \to X$, $p(x, \tau) = x$, is a homotopy equivalence.
*Hidden hypotheses:* none. *Deviation (not in the book):* (T1), used without comment.

**VA.3 ((T3) pasting along the strips; `Morse.continuous_of_stripMap`, `Morse.telescopeLift`,
`Morse.telescopeDesc`, `Morse.telescopeHomotopy`).** If every $X_n$ is closed in $X$, then for every
space $P$ a function $F$ on $P \times X_\Sigma$ is continuous as soon as each $(p, x, t) \mapsto
F(p, (x, n + t))$ is continuous on $P \times X_n \times [0, 1]$. Hence, for a monotone sequence of
closed sets, maps $\Phi_n : P \times X_n \times [0, 1] \to Z$ with $\Phi_{n+1}(p, x, 0) =
\Phi_n(p, x, 1)$ define a continuous map $P \times X_\Sigma \to Z$, $(p, (x, n + t)) \mapsto
\Phi_n(p, x, t)$; in particular maps $X_\Sigma \to Z$, and homotopies between them, may be given
strip by strip. *Book:* every map and homotopy on a telescope in the proof of Theorem A
(pp. 151–153) is given strip by strip, by formulas in $(x, n + t)$, $0 \le t \le 1$. *Hidden
hypotheses:* closedness of the $X_n$, which Milnor never states; then the strips are closed in
$X_\Sigma$ and form a locally finite family. *Deviation (not in the book):* stated and proved as a
lemma.

**VA.4 (the map of telescopes, and "clearly sufficient"; `Morse.telescopeMap`,
`Morse.telescopeProj_comp_telescopeMap`, `Morse.IsHomotopyEquiv.of_telescopeMap`).** If $f : X \to Y$
carries each $X_n$ into $Y_n$, then $f_\Sigma(x, \tau) = (f(x), \tau)$ is a map $X_\Sigma \to
Y_\Sigma$ with $p_Yf_\Sigma = fp_X$. If $X$ and $Y$ are the homotopy direct limits of $\{X_i\}$ and
$\{Y_i\}$ and $f_\Sigma$ is a homotopy equivalence, then so is $f$. *Book:* p. 150: define
$f_\Sigma(x, t) = (f(x), t)$; "it is clearly sufficient to prove that $f_\Sigma$ is a homotopy
equivalence". *Hidden hypotheses:* none; neither closedness nor monotonicity is needed. *Proof:*
$f \simeq fp_Xs = p_Yf_\Sigma s$ for a homotopy inverse $s$ of $p_X$.

**VA.5 ((T2) truncations; `Morse.truncation`, `Morse.isClosed_truncation`,
`Morse.monotone_truncation`, `Morse.truncIncl`, `Morse.truncProj`, `Morse.isHomotopyEquiv_truncIncl`,
`Morse.isHomotopyEquiv_truncProj`, `Morse.level_le_of_stripMap`).** The truncation $X^n_\Sigma =
\{(x, \tau) \in X_\Sigma : \tau \le n\}$ is closed in $X_\Sigma$, and $X^0_\Sigma \subseteq
X^1_\Sigma \subseteq \cdots$, whatever the $X_i$. For a monotone sequence, $x \mapsto (x, n)$ is a
homotopy equivalence $X_n \to X^n_\Sigma$ with homotopy inverse $(x, \tau) \mapsto x$, the homotopy
raising $\tau$ to $n$; and a function $F$ on $X_\Sigma$ that sends the $n$-th strip to levels
$\le n + 1$ and $X_n \times \{n\}$ to levels $\le n$ sends each $X^m_\Sigma$ to levels $\le m$.
*Book:* p. 152: $X^n_\Sigma = X_0 \times [0, 1] \cup \dots \cup X_{n-1} \times [n - 1, n] \cup X_n
\times [n]$, which "contains $X_n \times [n]$ as deformation retract"; $Gf_\Sigma$ carries
$X^n_\Sigma$ into itself. *Hidden hypotheses:* none; no closedness. *Deviation (not in the book):*
proofs of the two facts Milnor states.

**VA.6 (Lemmas 2.1 and 2.2 of the exposition; `Morse.isHomotopyDirectLimit_of_level`,
`Morse.isHomotopyDirectLimit_truncation`).** (i) For a monotone sequence, if $f : X \to \mathbb R$
is continuous, $f \ge 0$, and $f(x) \ge n + 1$ whenever $x \notin X_n$, then $X$ is the homotopy
direct limit of $\{X_i\}$. (ii) For any sequence, $X_\Sigma$ is the homotopy direct limit of its
truncations $\{X^n_\Sigma\}$. *Book:* p. 149, in Example 1: $x \mapsto (x, f(x))$ maps $X$
homeomorphically onto a subset of $X_\Sigma$ "which is clearly a deformation retract"; (ii) is used
without mention at the end of Case 2 (p. 153). *Hidden hypotheses:* (ii), for Case 2 (VA.11).
*Deviation (not in the book):* (i) needs no paracompactness once $f$ is given. *Proof:* (i) the
homotopy $(x, (1 - s)f(x) + s\tau)$ stays in $X_\Sigma$ by (T1); (ii) is (i) with
$f(x, \tau) = \tau + 1$.

**VA.7 (Example 1, and sublevel sets; `Morse.example1`, `Morse.isHomotopyDirectLimit_sublevel`).**
(i) Let $X$ be paracompact and Hausdorff, and $X_0 \subseteq X_1 \subseteq \cdots$ with every point
of $X$ in the interior of some $X_i$. Then $X$ is the homotopy direct limit of $\{X_i\}$. (ii) Let
$E : X \to \mathbb R$ be continuous, on any space $X$, and $a_0 \le a_1 \le \cdots$ with
$a_i \to \infty$. Then $X$ is the homotopy direct limit of the sublevel sets
$\{x : E(x) \le a_i\}$. *Book:* p. 149, Example 1: if each point of $X$ lies in the interior of
some $X_i$ and $X$ is paracompact, a partition of unity gives $f : X \to \mathbb R$ with
$f(x) \ge i + 1$ for $x \notin X_i$ and $f \ge 0$, and $X$ is a homotopy direct limit. *Hidden
hypotheses:* Hausdorff: Mathlib's partitions of unity need a normal space, and Milnor's
"paracompact" is read with the Hausdorff axiom. *Deviation (stronger):* (ii) needs no
paracompactness; it covers the sublevel sets of the energy in Theorem 17.3, where Milnor uses
Example 1 and the paracompactness of a metric space. *Proof:* (i) $f = \sum_ii\,\varphi_i$ for a
partition of unity $\{\varphi_i\}$ subordinate to $\{\operatorname{int}X_i\}$, then VA.6 (i);
(ii) $f = \sum_j\min(1, \max(0, E - a_j + 1))$, locally a finite sum.

**VA.8 (Example 3; `Morse.example3Set`, `Morse.monotone_example3Set`, `Morse.isClosed_example3Set`,
`Morse.iUnion_example3Set`, `Morse.example3`).** Let $X_n = \{0\} \cup [\frac1{n+1}, 1] \subseteq
[0, 1]$. The $X_n$ are closed and increasing, with union $[0, 1]$, and $[0, 1]$ is not the homotopy
direct limit of $\{X_n\}$. *Book:* p. 150, Example 3: the unit interval $[0, 1]$ is not the
homotopy direct limit of the sequence of closed subsets $[0] \cup [1/i, 1]$; no proof. *Hidden
hypotheses:* none. *Deviation (restated):* indexed from $0$. *Proof:* $\{0\} \times [0, \infty)$ is
open and closed in $X_\Sigma$, so $X_\Sigma$ is not connected, while a homotopy inverse $s$ of $p$
would join $(0, 0)$ to $s(0)$, $s(0)$ to $s(1)$ and $s(1)$ to $(1, 0)$ by paths.

**VA.9 (Milnor's maps $h_1$ and their inverse $g$; `Morse.reparam`, `Morse.reparam_homotopic`,
`Morse.scaleMap`, `Morse.IsMilnorMap`, `Morse.IsMilnorMap.fix`, `Morse.milnorInv`,
`Morse.loopFun`, `Morse.milnorH`, `Morse.milnorK`, `Morse.isHomotopyEquiv_of_milnorMap`).** Let
$X_0 \subseteq X_1 \subseteq \cdots$ be closed in $X$. (i) For a map $\rho : I \to I$ with
$\rho(0) = 0$ and $\rho(1) = 1$, $(x, n + t) \mapsto (x, n + \rho(t))$ is homotopic to the
identity of $X_\Sigma$; in particular so is $R_c(x, n + t) = (x, n + \min(ct, 1))$, $c \ge 1$.
(ii) Let $\psi : X_\Sigma \to X_\Sigma$ be a map with $\psi(x, n + t) = (x, n + 2t)$ for
$t \le \frac12$ and $\psi(x, n + t)$ at level $n + 1$ for $t \ge \frac12$. Then $\psi$ fixes the
points at integer levels, and it is a homotopy equivalence, with homotopy inverse Milnor's $g$:
$g(x, n + t) = (x, n + 2t)$ for $t \le \frac12$ and $\psi(x, n + \frac32 - t)$ for
$t \ge \frac12$. *Book:* p. 151: any map $h_1$ with $h_1(x, n + t) = (x, n + 2t)$ for
$t \le \frac12$ and $h_1(x, n + t) \in X_{n+1} \times [n + 1]$ for $t \ge \frac12$ is a homotopy
equivalence, with homotopy inverse $g$, well defined since $h_1(x, n + \frac12) = h_1(x, n + 1) =
(x, n + 1)$; $h_1g \simeq \mathrm{id}$ by a homotopy $H_u$, $0 \le u \le \frac12$, ending at
$H_{1/2}(x, n + t) = (x, n + \min(4t, 1))$, "clearly" homotopic to the identity; p. 152:
$gh_1 \simeq \mathrm{id}$ "by a completely analogous argument". *Hidden hypotheses:* the $X_n$
closed (VA.3); the formula for $h_1g$ uses that $h_1$ fixes the integer levels. *Proof:* with $u$
rescaled to $[0, 1]$, Milnor's $H_u$ is the single formula $(x, n + 4t)$ for $t \le \frac14$ and
$\psi(x, n + \frac12 + \frac\mu2)$ for $t \ge \frac14$, $\mu = \min(4t - 1, 1 - u, 2 - 2t)$; the
analogous homotopy for $g\psi$ takes $\mu = \max(2 - 4t, 2t - 1, u)$; both end at $R_4$, homotopic to
the identity by (i).

**VA.10 (Case 1 of Theorem A; `Morse.case1Fun`, `Morse.case1Family`, `Morse.case1Map_zero`,
`Morse.case1Map_one`, `Morse.theoremA_case1`).** Let $X_0 \subseteq X_1 \subseteq \cdots$ be closed
in $X$, and $\varphi : X \to X$ a map carrying each $X_n$ into itself by a map $\varphi_n$
homotopic, in $X_n$, to the identity of $X_n$. Then $\varphi_\Sigma$ is a homotopy equivalence. The
steps: with homotopies $h^n_u$ from $\varphi_n$ to the identity, $h_u(x, n + t)$ is
$(h^n_u(x), n + 2t)$ for $t \le \frac12$, $(h^n_{(3-4t)u}(x), n + 1)$ for $\frac12 \le t \le \frac34$
and $(h^{n+1}_{(4t-3)u}(x), n + 1)$ for $\frac34 \le t \le 1$; $(u, z) \mapsto h_u(z)$ is
continuous; $h_0 = \varphi_\Sigma \circ R_2$; and $h_1$ is a map as in VA.9 (ii). *Book:*
pp. 150–152, Case 1: $X_i = Y_i$ and each $f_i : X_i \to Y_i$ homotopic to the identity; the third
line of $h_u$ is printed $h^{n+1}_{(4-3t)u}$; "taking $u = 0$ this defines a map $h_0$ which is
clearly homotopic to $f_\Sigma$". *Hidden hypotheses:* the $X_n$ closed, for the continuity of
$h_u$ and of $g$ (VA.3); without it Milnor's $g$ can be discontinuous (the exposition's example:
$X = [0, 1]$, $X_0 = (0, 1]$). This part does not use that $X$ is a homotopy direct limit.
*Deviation (value differs):* the third line is $h^{n+1}_{(4t-3)u}$; the printed $(4 - 3t)u$ is a
misprint, giving $h^{n+1}_{7u/4}$ at $t = \frac34$ where continuity needs $h^{n+1}_0$. *Proof:*
Milnor's, with $h_0 \simeq \varphi_\Sigma$ by VA.9 (i).

**VA.11 (Case 2: $f_\Sigma$ is a homotopy equivalence; `Morse.isHomotopyEquiv_of_truncation`,
`Morse.homotopic_square`, `Morse.case2Inv`, `Morse.case2Inv_level`, `Morse.theoremA_telescope`).**
(i) Let $X_0 \subseteq X_1 \subseteq \cdots$ be a monotone sequence, closed or not, and
$F : X_\Sigma \to X_\Sigma$ a map carrying each truncation $X^m_\Sigma$ into itself, with
$F(x, m) = (e_m(x), m)$ for maps $e_m : X_m \to X_m$ homotopic to the identity. Then $F$ is a
homotopy equivalence. (ii) Let $X_0 \subseteq X_1 \subseteq \cdots$ in $X$ and $Y_0 \subseteq Y_1
\subseteq \cdots$ in $Y$, the $Y_n$ closed, and let $f : X \to Y$ carry each $X_n$ into $Y_n$ by a
homotopy equivalence $f_n$. Then $f_\Sigma : X_\Sigma \to Y_\Sigma$ is a homotopy equivalence.
*Book:* pp. 152–153, Case 2: "now let $X$ and $Y$ be arbitrary"; with homotopy inverses $g_n$ of the
$f_n$, $i_ng_n \simeq g_{n+1}f_{n+1}i_ng_n = g_{n+1}j_nf_ng_n \simeq g_{n+1}j_n$; with a homotopy
$h^n_u$ from $i_ng_n$ to $g_{n+1}j_n$, $G(y, n + t) = (g_n(y), n + 2t)$ for $t \le \frac12$ and
$(h^n_{2t-1}(y), n + 1)$ for $t \ge \frac12$; $Gf_\Sigma$ carries $X^n_\Sigma$ into itself by a
map homotopic to the identity, so "we can apply Case 1 to the sequence $\{X^n_\Sigma\}$, and
conclude that $Gf_\Sigma$ is a homotopy equivalence"; similarly $f_\Sigma G$; so $f_\Sigma$ has a
left and a right homotopy inverse (VA.1). *Hidden hypotheses:* the $Y_n$ closed, for the continuity
of $G$ (VA.3); the return from Case 1, which is about the induced map of the telescope of
$\{X^n_\Sigma\}$, to $Gf_\Sigma$ itself needs $X_\Sigma$ to be the homotopy direct limit of its
truncations (VA.6 (ii)); that $Gf_\Sigma$ on $X^m_\Sigma$ is homotopic to the identity is the chain
$\varphi \simeq \varphi\iota r = \iota(g_mf_m)r \simeq \iota r \simeq \mathrm{id}$, with $\iota$, $r$
the maps of (T2) (VA.5). *Deviation (narrower):* the $Y_n$ closed, where Milnor's Case 2 has no
hypothesis. *Deviation (stronger):* no homotopy direct limit hypothesis, and no closedness of the
$X_n$: Case 1 is applied only to the truncations $X^m_\Sigma$ and $Y^m_\Sigma$, which are always
closed (VA.5).

**VA.12 (Theorem A, by Milnor's proof; `Morse.theoremA`).** Let $X$ be the homotopy direct limit of
$X_0 \subseteq X_1 \subseteq \cdots$ and $Y$ that of $Y_0 \subseteq Y_1 \subseteq \cdots$, the $Y_i$
closed in $Y$, and let $f : X \to Y$ carry each $X_i$ into $Y_i$ by a homotopy equivalence
$f_i = f|X_i : X_i \to Y_i$. Then $f$ is a homotopy equivalence. *Book:* p. 150, Theorem A, with no
closedness hypothesis. *Hidden hypotheses:* Milnor's proof needs the $Y_i$ closed (VA.11), and
only these. *Deviation (narrower):* the $Y_i$ closed; this is removed in VA.15. *Proof:* VA.11 (ii)
and VA.4.

**VA.13 (the mapping telescope; `Morse.MapTelRel`, `Morse.MappingTelescope`,
`Morse.MappingTelescope.mk`, `Morse.MappingTelescope.mk_one`, `Morse.MappingTelescope.desc`,
`Morse.MappingTelescope.lift`, `Morse.MappingTelescope.homotopy`, `Morse.MappingTelescope.level`,
`Morse.MappingTelescope.trunc`, `Morse.MappingTelescope.isClosed_trunc`,
`Morse.MappingTelescope.isHomotopyDirectLimit_trunc`, `Morse.MappingTelescope.push`,
`Morse.MappingTelescope.mk_zero_injective`, `Morse.MappingTelescope.isInducing_mk_zero`,
`Morse.MappingTelescope.levelIncl`, `Morse.MappingTelescope.levelRetract`,
`Morse.MappingTelescope.isHomotopyEquiv_levelIncl`).** For a
sequence of spaces and maps $K_0 \xrightarrow{c_0} K_1 \xrightarrow{c_1} \cdots$, the *mapping
telescope* $T$ is the quotient of the disjoint union of the blocks $K_n \times [0, 1]$ by
$(k, 1)_n \sim (c_n(k), 0)_{n+1}$, with the quotient topology; $(k, t)_n$ is at level $n + t$, a
continuous function on $T$. Maps out of $T$, and out of $P \times T$ for a locally compact $P$ (for
homotopies, $P = I$), may be given block by block, compatibly with the gluing, with no closedness
condition. The truncations $T_n = \{\text{level} \le n\}$ are closed and increasing, and $T$ is the
homotopy direct limit of $\{T_n\}$; $k \mapsto (k, 0)_n$ is an embedding $K_n \to T$ and a homotopy
equivalence $K_n \to T_n$. *Book:* not in the book; the exposition's proof of the Corollary uses it.
*Hidden hypotheses:* none. *Deviation (not in the book):* the device that removes the closedness
hypotheses (VA.15) and replaces a union of complexes that are not subspaces of one space (VA.16,
VA.17). *Proof:* the product of a quotient map with a locally compact space is a quotient map; the
homotopy inverse of $K_n \to T_n$ reads off the point reached by pushing each point of $T_n$ up to
level $n$ along the maps $c_m$, and is continuous because $K_n \to T$ is an embedding; $T$ is a
homotopy direct limit by VA.6 (i) with $f = \text{level} + 1$.

**VA.14 (the mapping telescope of the inclusions; `Morse.subspaceFunctor`,
`Morse.telescopeComparison`, `Morse.telescopeComparisonHomeomorph`,
`Morse.isHomotopyEquiv_telescopeComparison`, `Morse.telescopeProj'`,
`Morse.isHomotopyEquiv_telescopeProj'`).** Let $X_0 \subseteq X_1 \subseteq \cdots$ be subsets of
$X$, not necessarily closed, and $T$ the mapping telescope of the inclusions. The map $T \to
X_\Sigma$, $(x, t)_n \mapsto (x, n + t)$, is a homotopy equivalence, and a homeomorphism when the
$X_n$ are closed. If $X$ is the homotopy direct limit of $\{X_i\}$, the map $T \to X$,
$(x, t)_n \mapsto x$, is a homotopy equivalence. *Book:* not in the book. *Hidden hypotheses:*
none. *Deviation (not in the book).* *Proof:* the map carries $T_m$ into $X^m_\Sigma$ by a map
homotopic to the composite of the homotopy equivalences $T_m \to X_m \to X^m_\Sigma$ (VA.13,
VA.5), so VA.12 applies to the closed truncations, with VA.6 (ii) and VA.13; the inverse of the
homeomorphism is given strip by strip (VA.3).

**VA.15 (Theorem A with no closedness hypothesis; `Morse.mappingTelescopeMap`,
`Morse.mapsTo_mappingTelescopeMap`, `Morse.theoremA_general`).** Let $X$ be the homotopy direct
limit of $X_0 \subseteq X_1 \subseteq \cdots$ and $Y$ that of $Y_0 \subseteq Y_1 \subseteq \cdots$,
arbitrary subsets, and let $f : X \to Y$ carry each $X_i$ into $Y_i$ by a homotopy equivalence
$f_i = f|X_i : X_i \to Y_i$. Then $f$ is a homotopy equivalence. *Book:* p. 150, Theorem A: suppose
that $X$ is the homotopy direct limit of $\{X_i\}$ and $Y$ the homotopy direct limit of $\{Y_i\}$,
and let $f : X \to Y$ be a map which carries each $X_i$ into $Y_i$ by a homotopy equivalence; then
$f$ itself is a homotopy equivalence. *Hidden hypotheses:* none. *Proof:* departs from Milnor's in
the space on which his proof is run. The map $(x, t)_n \mapsto (f(x), t)_n$ of the mapping
telescopes of the inclusions carries the $m$-th truncation into the $m$-th by a map homotopic to
the composite of homotopy equivalences $T_m \to X_m \xrightarrow{f_m} Y_m \to T_m$ (VA.13), and
the truncations are closed, so VA.12 (Milnor's proof, Cases 1 and 2) makes it a homotopy
equivalence; the mapping telescopes are homotopy equivalent to $X$ and $Y$ by maps commuting with
$f$ (VA.14).

**VA.16 (monotone unions, and the final step of Theorem 17.3; `Morse.nonempty_homotopyEquiv_telescope`,
`Morse.homotopic_inverse_square`, `Morse.compareMap`, `Morse.compareMap_mapsTo`,
`Morse.isHomotopyEquiv_compareMap`, `Morse.nonempty_homotopyEquiv_mappingTelescope`).** (i) If $X$
is the homotopy direct limit of $X_0 \subseteq X_1 \subseteq \cdots$, the $Y_i \subseteq Y$ are
closed and increasing, and $f : X \to Y$ carries each $X_i$ into $Y_i$ by a homotopy equivalence,
then $X$ is homotopy equivalent to the telescope $Y_\Sigma$. (ii) If $X$ is the homotopy direct
limit of $X_0 \subseteq X_1 \subseteq \cdots$ (closed or not), $K_0 \xrightarrow{c_0} K_1
\xrightarrow{c_1} \cdots$ is a sequence of spaces and maps, and $g_n : X_n \to K_n$ are homotopy
equivalences with $c_ng_n \simeq g_{n+1}$ on $X_n$, then $X$ is homotopy equivalent to the mapping
telescope of the $K_n$. *Book:* p. 150: in the proof of Theorem 17.3 homotopy equivalences
$\Omega^{a_i} \to K_i$ form a commutative diagram with $K_0 \subset K_1 \subset \cdots$; since
$\Omega = \bigcup\Omega^{a_i}$ and $K = \bigcup K_i$ are homotopy direct limits (Examples 1 and 2),
the limit mapping $\Omega \to K$ is a homotopy equivalence. *Hidden hypotheses:* the limit mapping
exists only because each map extends the previous one; $K$ is the homotopy direct limit of
$\{K_i\}$ by Example 2, which is not verified. *Deviation (restated):* the conclusion is a homotopy
equivalence with $Y_\Sigma$, or with the mapping telescope of the $K_n$, which stands for the union
$K$ with the weak topology; the two are homotopy equivalent by Example 2 (Whitehead's theorem).
*Deviation (stronger):* in (ii) the squares need only commute up to homotopy, and the $K_n$ need
not be subspaces of one space. *Proof:* (ii) Milnor's map $G$ of Case 2, built from homotopy
inverses of the $g_n$ and defined from the mapping telescope of the $K_n$ to $X_\Sigma$, where it is
continuous block by block, is a homotopy equivalence by VA.12 for the closed truncations.

**VA.17 (the Corollary; `Morse.corollary_appendix`, `Morse.corollary_cellComplex`).** (i) If $X$ is
the homotopy direct limit of $X_0 \subseteq X_1 \subseteq \cdots$ and the $X_n$ are homotopy
equivalent to spaces $K_n$, then there are maps $K_0 \to K_1 \to \cdots$ (in the proof
$e_{n+1}\iota_ne_n'$, with $e_n : X_n \to K_n$ a homotopy equivalence, $e_n'$ a homotopy inverse
and $\iota_n$ the inclusion) such that $X$ is homotopy equivalent to their mapping telescope.
(ii) If each $X_n$ has the homotopy type of a finite cell complex with cells $\mathrm{cells}_n$
(V2.11), $X$ is homotopy equivalent to the mapping telescope of a sequence of iterated adjunction
spaces $K_n$ with these cells. No closedness of the $X_n$ is assumed. *Book:* p. 153, Corollary: if
$X$ is the homotopy direct limit of $\{X_i\}$ and each $X_i$ has the homotopy type of a
CW-complex, then $X$ itself has the homotopy type of a CW-complex; "the proof is not difficult".
*Hidden hypotheses:* that a telescope of CW-complexes is a CW-complex needs cellular maps (cellular
approximation) and the CW structure of mapping telescopes. *Deviation (narrower):* the conclusion
is a mapping telescope of the $K_n$, not a CW-complex; for finite complexes, iterated adjunction
spaces (V2.11) replace CW-complexes. *Proof:* VA.16 (ii).

**VA.18 (countable cell complexes; `Morse.IsRelCellAttachment`, `Morse.IsCellAttachment.of_rel`,
`Morse.CellTower`, `Morse.CellTower.isCellAttachment`, `Morse.CellTower.ofSequence`,
`Morse.IsCountableCellComplexType`, `Morse.IsCountableCellComplexType.of_homotopyEquiv`).** A space
$K$ is obtained from $L$ by attaching cells of dimensions $(\lambda_1, \dots, \lambda_k)$ if it is
obtained by attaching a $\lambda_1$-cell to $L$, then a $\lambda_2$-cell, and so on, each along an
arbitrary map of its boundary sphere into the space built so far (V1.2); the map $L \to K$ is the
composite of the inclusions. A *cell tower* with cells $\mathrm{cells}_0, \mathrm{cells}_1, \dots$
(finite lists of dimensions) is a sequence $K_0 \to K_1 \to \cdots$ in which $K_0$ is an iterated
adjunction space with cells $\mathrm{cells}_0$ (V2.11) and $K_{n+1}$ is obtained from $K_n$ by
attaching the cells $\mathrm{cells}_{n+1}$, the map $K_n \to K_{n+1}$ being the inclusion; each
$K_n$ is then an iterated adjunction space with the cells $\mathrm{cells}_0, \dots,
\mathrm{cells}_n$. A space $X$ *has the homotopy type of a countable cell complex* with cells
$\mathrm{cells}_0, \mathrm{cells}_1, \dots$ if it is homotopy equivalent to the mapping telescope
(VA.13) of such a tower; this is invariant under homotopy equivalence. *Book:* p. 149: each
$\Omega^{a_i}$ has the homotopy type of "a certain CW-complex", and so should the union; p. 150:
$K = \bigcup K_i$. *Hidden hypotheses:* none. *Deviation (narrower):* weaker than a CW-complex: the
attaching maps need not be cellular (V2.11), and the mapping telescope of the tower stands for the
union of the $K_n$ with the weak topology, to which it is homotopy equivalent by Example 2, not
verified.

**VA.19 (the topological part of Theorem 17.3; `Morse.isCountableCellComplexType_of_tower`,
`Morse.isCountableCellComplexType_of_sublevel`, `Morse.isCountableCellComplexType_of_sublevel'`).**
(i) If $X$ is the homotopy direct limit of $X_0 \subseteq X_1 \subseteq \cdots$ and $g_n : X_n \to
K_n$ are homotopy equivalences to the stages of a cell tower with $c_ng_n \simeq g_{n+1}$ on $X_n$,
then $X$ has the homotopy type of the countable cell complex. (ii) Let $E : X \to \mathbb R$ be
continuous, $a_0 \le a_1 \le \cdots$ with $a_n \to \infty$, and $g_n : \{E \le a_n\} \to K_n$
homotopy equivalences to the stages of a cell tower (given as a tower, or by its stages $K_n$ and
the inclusions $c_n : K_n \to K_{n+1}$ attaching the cells $\mathrm{cells}_{n+1}$) with
$c_ng_n = g_{n+1}$ on $\{E \le a_n\}$. Then $X$ has the homotopy type of the countable cell complex
with cells $\mathrm{cells}_0, \mathrm{cells}_1, \dots$. *Book:* p. 150, the alternative final step
of Theorem 17.3 (VA.16). *Hidden hypotheses:* $a_i \to \infty$, so that the sublevel sets exhaust
$X$; each $g_{n+1}$ extends $g_n$, for the limit map. *Deviation (stronger):* no paracompactness
(VA.7 (ii)). *Deviation (restated):* "CW-complex" in the sense of VA.18. *Proof:* VA.16 (ii), with
VA.7 (ii) in (ii).

### What is not verified in this chapter

- **Example 2** (p. 149): a CW-complex is the homotopy direct limit of subcomplexes with union $X$.
  It needs Whitehead's theorem, the fact that compact subsets of a CW-complex lie in finite
  subcomplexes, and the CW topology of products (Lemma 2.3 and Facts (a)–(c) of the exposition),
  none of which is in Mathlib. Hence the mapping telescope of a cell tower is not compared with the
  union of its stages in the weak topology (VA.16, VA.18).
- **The Remark** (p. 150): that under the hypotheses of Case 1 $f_\Sigma$ need not be homotopic to
  the identity ("counterexamples can be given"). The exposition's phantom-map counterexample needs
  cellular cohomology and $\mathbb{CP}^\infty$; it is not formalized.
- **The CW structure of mapping telescopes**: the Corollary's conclusion that $X$ has the homotopy
  type of a CW-complex needs cellular approximation, to make the maps $K_n \to K_{n+1}$ cellular, and
  the CW structure of the mapping telescope of cellular maps; neither is in Mathlib, so the
  conclusion is a mapping telescope (VA.17).
- **The application to the path space** (p. 150) is not part of this chapter: the sublevel sets
  $\Omega^{a_i}$, Milnor's metric and the tower of complexes are verified in Chapter 10, where VA.19
  gives Theorem 17.3 (V10.20–V10.22) and the homology of $\Omega(S^n; p, q)$ is computed level by
  level (V10.25–V10.26).

### Sign-off items

1. (VA.1) A homotopy equivalence is a map with a two-sided homotopy inverse; a map with a left and
   a right homotopy inverse is one.
2. (VA.2) The telescope is $X_\Sigma = \bigcup_nX_n \times [n, n + 1] \subseteq X \times \mathbb R$,
   and $X$ is the homotopy direct limit of $\{X_i\}$ when $(x, \tau) \mapsto x$ is a homotopy
   equivalence; raising $\tau$ stays in $X_\Sigma$.
3. (VA.3) If the $X_n$ are closed, a map on $X_\Sigma$ (or $P \times X_\Sigma$) continuous on each
   strip is continuous.
4. (VA.4) If $f_\Sigma$ is a homotopy equivalence between homotopy direct limits, so is $f$.
5. (VA.5) $X_n \to X^n_\Sigma$, $x \mapsto (x, n)$, is a homotopy equivalence, with no closedness.
6. (VA.6) A function $f \ge 0$ with $f \ge n + 1$ off $X_n$ makes $X$ a homotopy direct limit, and
   $X_\Sigma$ is always the homotopy direct limit of its truncations.
7. (VA.7) Example 1 holds for paracompact Hausdorff $X$; sublevel sets $\{E \le a_i\}$ of a
   continuous $E$ with $a_i \to \infty$ need no paracompactness.
8. (VA.8) Example 3: $[0, 1]$ is not the homotopy direct limit of $\{0\} \cup [\frac1{n+1}, 1]$.
9. (VA.9) For closed $X_n$, Milnor's maps $h_1$ are homotopy equivalences with inverse $g$.
10. (VA.10) Case 1: for closed $X_n$ and $\varphi_n \simeq \mathrm{id}$, $\varphi_\Sigma$ is a
    homotopy equivalence; the third line of $h_u$ is $h^{n+1}_{(4t-3)u}$.
11. (VA.11) Case 2: if the $Y_n$ are closed and every $f_n$ is a homotopy equivalence, $f_\Sigma$ is
    a homotopy equivalence; the $X_n$ need not be closed.
12. (VA.12) Theorem A by Milnor's proof, with the $Y_i$ closed.
13. (VA.13) The mapping telescope of $K_0 \to K_1 \to \cdots$ is the homotopy direct limit of its
    closed truncations, each homotopy equivalent to the corresponding $K_n$.
14. (VA.14) The mapping telescope of the inclusions $X_n \subseteq X_{n+1}$ is homotopy equivalent
    to $X_\Sigma$, and to $X$ when $X$ is the homotopy direct limit.
15. (VA.15) Theorem A holds exactly as Milnor states it, with no closedness hypothesis.
16. (VA.16) A homotopy direct limit of the $X_n$ is homotopy equivalent to the mapping telescope of
    any sequence $K_n$ with compatible homotopy equivalences $X_n \to K_n$.
17. (VA.17) The Corollary, with the mapping telescope of the $K_n$ in place of a CW-complex.
18. (VA.18) A countable cell complex is the mapping telescope of a tower of cell attachments.
19. (VA.19) A space exhausted by sublevel sets homotopy equivalent to the compatible stages of a
    cell tower has the homotopy type of the countable cell complex.
