## Part XII. Homotopy groups, cells and fibre bundles

Milnor's Part IV rests on facts of homotopy theory that he quotes rather than proves. Theorem 22.1 turns a lower bound $\lambda_0$ on the indices of the non-minimal geodesics into the statement that the space $\Omega^d$ of minimal geodesics carries the low homotopy groups of the path space: $\Omega$ has the homotopy type of $\Omega^d$ with cells of dimension $\ge \lambda_0$ attached, and attaching such cells changes no $\pi_i$ with $i \le \lambda_0 - 2$ (p. 118). Bott periodicity (§§23–24) passes between path spaces, loop spaces and the manifold itself, $\pi_i\Omega \cong \pi_{i+1}M$, and compares the homotopy groups of unitary groups, spheres, Stiefel and Grassmann manifolds through the exact homotopy sequences of fibre bundles, with $\pi_iS^n = 0$ for $i < n$ as input. Mathlib defines the homotopy groups $\pi_n(X, x)$ and their group structure, but not the maps that continuous maps induce on them, nor what is built on those: change of basepoint, invariance under homotopy equivalence, cellular approximation, Serre fibrations and their exact homotopy sequence. The vanishing of $\pi_iS^n$ for $i < n$ is on its list of things to do. This part retells the formal proofs of all of these, from the twelve files of `Morse/Homotopy/` that do not concern particular bundles. The bundles themselves (coset maps of unitary groups, Stiefel and Grassmann manifolds) are Part XIII's.

The setting is arbitrary topological spaces, with a Hausdorff hypothesis only where a cell is embedded in an ambient space. The formal route departs from the textbook one (Hatcher, *Algebraic Topology*, Sections 4.1–4.2) in six places, each explained where it occurs.

- **No relative homotopy groups.** Milnor states Theorem 22.1 as $\pi_i(\Omega, \Omega^d) = 0$ for $i < \lambda_0$ and reads off the inclusion from the exact sequence of the pair. Mathlib has no relative homotopy groups. The formal text uses the *compression* form of the vanishing and proves surjectivity and injectivity of the induced maps directly from it (§XII.2). This treats $i = 0$ and $i = 1$, where the terms are not abelian groups or not groups at all, with the same argument as every other degree, at every basepoint.
- **The push-off by smooth approximation.** The key step of cellular approximation, pushing a map of a cube off the centre of a cell of larger dimension (Hatcher, Lemma 4.10), is proved with the Stone–Weierstrass theorem for smooth maps of the companion project and the fact that a $C^1$ map from a space of smaller dimension misses a dense set (§XII.5). No simplicial approximation is used.
- **No separation axiom on the space to which a cell is attached.** A continuous "probe" on $Y \cup_\varphi e^n$ measures how deep a point lies in the cell and reads off its coordinate (§XII.6), and the radial deformation of the punctured cell onto its boundary is replaced by a radial *expansion* of a small ball, defined on the whole cell (§XII.7).
- **Countable complexes are mapping telescopes**, as in Part XI, and their homotopy groups are computed by compactness (§§XII.9–12.10). The deformation of a truncation of the telescope moves the basepoint, so change of basepoint (§XII.3) is needed even for this.
- **Fibre bundles as a property of a map.** Local triviality is a property of an arbitrary map $p : E \to B$ (§XII.13), so that it applies to maps between spaces built independently. Locally trivial maps are Serre fibrations by Hatcher's subdivision argument, with an explicit order on the boxes and an explicit retraction of a box onto the faces where the lift is already known (§XII.14).
- **Exactness as pointed sets, at every place.** The exact sequence is proved at the fibre, the total space and the base for every finite index set, $\pi_0$ included (§XII.16). Exactness of pointed sets gives only trivial kernels, so the injectivity statements used in §23 need two further arguments (§XII.17).

The results are stated for Mathlib's homotopy groups $\pi_N(X, x)$, indexed by an arbitrary finite set $N$; for $N = \{0, \dots, n-1\}$ they are statements about $\pi_n$.

**Map.**

- `Homotopy/Basic` (169 lines): induced maps; compressions; surjectivity and injectivity from compressions.
- `Homotopy/ChangeOfBase` (498 lines): the frame construction; change of basepoint; free homotopies; homotopy equivalences; homotopy-commutative squares.
- `Homotopy/PushOff` (184 lines): the push-off lemma in the coordinates of a cell.
- `Homotopy/CellAttach` (729 lines): the point-set topology of $Y \cup_\varphi e^n$; the push-off and the radial push there; cells and homotopy groups; other pushout squares and embedded cells.
- `Homotopy/Telescope` (327 lines): exhaustions by compact sets; increasing unions; mapping telescopes; cell towers.
- `Homotopy/RelCells` (177 lines): relative cell complexes, with finitely and countably many cells; the form of Theorem 22.1.
- `Homotopy/LoopSpace` (416 lines): reindexing cubes; $\pi_M(\Omega X) \cong \pi_{M+1}(X)$, as groups; path spaces with different end points.
- `Homotopy/Fibration` (317 lines): locally trivial maps; the open box; Serre fibrations; the absolute lifting property.
- `Homotopy/HomotopyLifting` (694 lines): the retraction onto faces of a cube; the grid; one box; the order of the boxes; locally trivial maps are Serre fibrations.
- `Homotopy/ExactSequence` (587 lines): boundary lifts; the boundary map; exactness at the three places.
- `Homotopy/ExactSequenceIso` (425 lines): homomorphisms; injectivity; bijectivity; two out of three; the forms with $\pi_i$.
- `Homotopy/Spheres` (174 lines): contractible spaces; $\pi_iS^n = 0$ for $i < n$.

### XII.1 Conventions: cubes, generalized loops and the extra coordinate

Spaces are topological spaces, maps are continuous, and $I = [0,1]$. Homotopies are Mathlib's, with time first, and a homotopy *relative to* $S$ fixes every point of $S$ at all times (§0.4) ⟦Mathlib/Topology/Homotopy/Basic · ContinuousMap.Homotopy⟧ ⟦Mathlib/Topology/Homotopy/Basic · ContinuousMap.HomotopyRel⟧ ⟦Mathlib/Topology/Homotopy/Basic · ContinuousMap.HomotopicRel⟧. Such homotopies compose with maps on the left ⟦Mathlib/Topology/Homotopy/Basic · ContinuousMap.HomotopyRel.compContinuousMap⟧ and can be concatenated ⟦Mathlib/Topology/Homotopy/Basic · ContinuousMap.HomotopyRel.trans⟧, and all their stages agree on $S$ ⟦Mathlib/Topology/Homotopy/Basic · ContinuousMap.HomotopyRel.eq_fst⟧ ⟦Mathlib/Topology/Homotopy/Basic · ContinuousMap.HomotopyRel.fst_eq_snd⟧.

*Cubes.* Mathlib indexes cubes by an arbitrary type $N$. The cube $I^N$ is the space of functions $N \to I$ with the product topology, and its boundary $\partial I^N$ is the set of points with some coordinate equal to $0$ or $1$ ⟦Mathlib/Topology/Homotopy/HomotopyGroup · Cube.boundary⟧. For $N = \{0, \dots, n-1\}$ this is the usual cube; for $N = \emptyset$ it is a point with empty boundary. Most statements assume $N$ finite, with $|N|$ elements.

*Generalized loops and homotopy groups* (§0.7). A generalized loop at $x \in X$ is a continuous $\gamma : I^N \to X$ equal to $x$ on $\partial I^N$ ⟦Mathlib/Topology/Homotopy/HomotopyGroup · GenLoop⟧ ⟦Mathlib/Topology/Homotopy/HomotopyGroup · GenLoop.boundary⟧. They form a space $\Omega^N(X, x)$, which contains the constant loop ⟦Mathlib/Topology/Homotopy/HomotopyGroup · GenLoop.const⟧. Two are equivalent when they are homotopic relative to $\partial I^N$ ⟦Mathlib/Topology/Homotopy/HomotopyGroup · GenLoop.Homotopic⟧. The set of classes $[\gamma]$ is $\pi_N(X, x)$ ⟦Mathlib/Topology/Homotopy/HomotopyGroup · HomotopyGroup⟧, and $\pi_n(X, x) = \pi_{\{0, \dots, n-1\}}(X, x)$ ⟦Mathlib/Topology/Homotopy/HomotopyGroup · HomotopyGroup.Pi⟧. The class of the constant loop is written $0$, or $1$ where the group is written multiplicatively. For $N = \emptyset$ a generalized loop is a point of $X$ and a homotopy relative to $\emptyset$ is a path, so $\pi_\emptyset(X, x)$ is the set $\pi_0(X)$ of path components, whatever $x$ is ⟦Mathlib/Topology/Homotopy/HomotopyGroup · HomotopyGroup.pi0EquivZerothHomotopy⟧. "$\pi_N(X, x)$ is trivial" means that it has at most one element.

*The group structure.* For nonempty $N$, $\pi_N(X, x)$ is a group ⟦Mathlib/Topology/Homotopy/HomotopyGroup · HomotopyGroup.group⟧, abelian when $|N| \ge 2$ ⟦Mathlib/Topology/Homotopy/HomotopyGroup · HomotopyGroup.commGroup⟧, and the fundamental group when $|N| = 1$ ⟦Mathlib/Topology/Homotopy/HomotopyGroup · HomotopyGroup.pi1EquivFundamentalGroup⟧. Products are concatenations along a coordinate $i \in N$. The loop $\operatorname{trans}_i(f, g)$ is $f$ on $\{t_i \le \frac12\}$ and $g$ on $\{t_i \ge \frac12\}$, each rescaled in the coordinate $i$ ⟦Mathlib/Topology/Homotopy/HomotopyGroup · GenLoop.transAt⟧, and $\operatorname{symm}_i f$ is $f$ with $t_i$ replaced by $1 - t_i$ ⟦Mathlib/Topology/Homotopy/HomotopyGroup · GenLoop.symmAt⟧. The class of $\operatorname{trans}_i(f, g)$ does not depend on $i$ ⟦Mathlib/Topology/Homotopy/HomotopyGroup · HomotopyGroup.transAt_indep⟧. One convention of Mathlib matters below: the product $[p]\cdot[q]$ is the class of $\operatorname{trans}_i(q, p)$, so the *second* factor runs first ⟦Mathlib/Topology/Homotopy/HomotopyGroup · HomotopyGroup.mul_spec⟧. Further $[p]^{-1} = [\operatorname{symm}_i p]$ ⟦Mathlib/Topology/Homotopy/HomotopyGroup · HomotopyGroup.inv_spec⟧, and the identity is the class of the constant loop ⟦Mathlib/Topology/Homotopy/HomotopyGroup · HomotopyGroup.one_def⟧.

*The extra coordinate.* Write $N^+$ for $N$ with one new element $\star$ adjoined (formally `Option N`, with $\star$ = `none`). Then $|N^+| = |N| + 1$, and $\pi_{N^+}$ is the homotopy group one degree above $\pi_N$. A point of $I^{N^+}$ is a pair $(t, z)$: its $\star$-coordinate $t \in I$ and the point $z \in I^N$ of its other coordinates ⟦Homotopy/LoopSpace · optionPoint⟧ ⟦Homotopy/ExactSequence · optionTail⟧ ⟦Homotopy/LoopSpace · optionPoint_eta⟧. The correspondence is continuous both ways ⟦Homotopy/LoopSpace · continuous_optionPoint⟧ ⟦Homotopy/ExactSequence · continuous_optionTail⟧. The point $(t, z)$ lies on $\partial I^{N^+}$ exactly when $t \in \{0, 1\}$ or $z \in \partial I^N$ ⟦Homotopy/ExactSequence · mem_boundary_option_iff⟧ ⟦Homotopy/LoopSpace · optionPoint_mem_boundary_of_left⟧ ⟦Homotopy/LoopSpace · optionPoint_mem_boundary_of_right⟧. The extra coordinate is the loop parameter in §XII.12 and the time of a lifting problem in §§XII.15–12.17. Reindexing along a bijection $M \cong N$ identifies $\pi_M$ with $\pi_N$ (§XII.12), so $\pi_{\{0, \dots, n\}}$ and $\pi_{\{0, \dots, n-1\}^+}$ are the same group.

*Paths.* A path from $x$ to $y$ is Mathlib's ⟦Mathlib/Topology/Path · Path⟧, with reversal $\gamma^{-1}$ and concatenation $\gamma\cdot\omega$ ⟦Mathlib/Topology/Path · Path.symm⟧ ⟦Mathlib/Topology/Path · Path.trans⟧. Formulas below evaluate paths at real numbers outside $[0,1]$. This means the extension of $\gamma$ to $\mathbb R$ that is constant on $(-\infty, 0]$ and on $[1, \infty)$ ⟦Mathlib/Topology/Path · Path.extend⟧. A homotopy $H$ from $f$ to $g$ moves each point $x$ along the path $t \mapsto H(t, x)$ from $f(x)$ to $g(x)$ ⟦Mathlib/Topology/Homotopy/Path · ContinuousMap.Homotopy.evalAt⟧.

*Clamps and cases.* As in Part XI (§XI.1), $\operatorname{clamp}(s) = \min(1, \max(0, s))$ ⟦Mathlib/Order/Interval/Set/ProjIcc · Set.projIcc⟧. A map defined by one formula on $\{a \le b\}$ and another on $\{a \ge b\}$ is continuous when both formulas are continuous everywhere and agree on $\{a = b\}$ ⟦Mathlib/Topology/Order/OrderClosed · Continuous.if_le⟧. Nearly every homotopy of this part is built this way, and the formulas are written without the clamps on the range where they do nothing. $\bar s = 1 - s$ is the reversal of $I$ ⟦Mathlib/Topology/UnitInterval · unitInterval.symm⟧.

Statements about adjunction spaces ask that the spaces involved lie in one universe, as in Part II. The condition has no mathematical content and is not mentioned again.

### XII.2 Induced maps and the compression criteria

**Definition (induced maps).** A map $f : X \to Y$ carries a generalized loop $\gamma$ at $x$ to the generalized loop $f \circ \gamma$ at $f(x)$ ⟦Homotopy/Basic · genLoopMap⟧ ⟦Homotopy/Basic · genLoopMap_apply⟧, and a homotopy $H$ relative to $\partial I^N$ to the homotopy $f \circ H$, again relative to $\partial I^N$ ⟦Homotopy/Basic · genLoopMap_homotopic⟧. So it induces
$$f_* : \pi_N(X, x) \to \pi_N(Y, f(x)), \qquad f_*[\gamma] = [f \circ \gamma]$$
⟦Homotopy/Basic · homotopyGroupMap⟧ ⟦Homotopy/Basic · homotopyGroupMap_mk⟧.

It is functorial, $(g \circ f)_* = g_* \circ f_*$ and $\mathrm{id}_* = \mathrm{id}$, as one sees on representatives ⟦Homotopy/Basic · homotopyGroupMap_comp⟧ ⟦Homotopy/Basic · homotopyGroupMap_id⟧, and it sends the class of the constant loop to the class of the constant loop ⟦Homotopy/ExactSequence · homotopyGroupMap_const⟧. It is defined as a map of sets, for every $N$, so that one notion covers $\pi_0$, $\pi_1$ and the higher groups. For nonempty $N$ it is a homomorphism (§XII.17), and a bijective $f_*$ is then an isomorphism of groups.

**Definition (compressions).** Let $j : Y \to X$ be a map and $P$ a space. $j$ *compresses maps from $P$* if every map $f : P \to X$ is homotopic, relative to $f^{-1}(j(Y))$, to a map with values in $j(Y)$ ⟦Homotopy/Basic · Compresses⟧.

The relative clause says that the points of $P$ already mapped into $j(Y)$ stay where they are. This is Hatcher's compression criterion for $\pi_i(X, A) = 0$, with the cube replaced by an arbitrary space $P$. It is what the push-off argument produces for $X = Y \cup e^\lambda$ and $P$ of dimension $< \lambda$ (§XII.7).

Two small facts are used throughout. A homotopy relative to $S$ is a homotopy relative to every $T \subseteq S$ ⟦Homotopy/Basic · homotopyRelMono⟧. And when $j$ is an embedding, a map $g : P \to X$ with values in $j(Y)$ factors as $g = j \circ g'$ with $g'$ continuous ⟦Homotopy/Basic · exists_lift_of_isEmbedding⟧. The preimage $g'(p)$ of $g(p)$ is unique, and $g'$ is continuous because $Y$ carries the topology induced by $j$ ⟦Mathlib/Topology/Maps/Basic · IsInducing.continuous_iff⟧.

**Theorem (compression gives surjectivity).** Let $j : Y \to X$ be an embedding that compresses maps from the cube $I^N$. Then $j_* : \pi_N(Y, y) \to \pi_N(X, j(y))$ is onto for every $y \in Y$. ⟦Homotopy/Basic · surjective_homotopyGroupMap_of_compresses⟧

*The proof as formalized.*

1. Let $\gamma$ be a generalized loop in $X$ at $j(y)$. Compress it: there are $g : I^N \to X$ with values in $j(Y)$ and a homotopy $F$ from $\gamma$ to $g$ relative to $\gamma^{-1}(j(Y))$. Write $g = j \circ g'$.
2. $\partial I^N \subseteq \gamma^{-1}(j(Y))$, because $\gamma = j(y)$ there. So $F$ fixes the boundary, and for $z \in \partial I^N$, $j(g'(z)) = g(z) = \gamma(z) = j(y)$, whence $g'(z) = y$ by injectivity. Thus $g'$ is a generalized loop in $Y$ at $y$.
3. $j \circ g' = g$, and $F$ run backwards is a homotopy from $g$ to $\gamma$ relative to the boundary. So $j_*[g'] = [\gamma]$. $\square$

**Theorem (compression gives injectivity).** Let $j : Y \to X$ be an embedding that compresses maps from the cylinder $I \times I^N$. Then $j_* : \pi_N(Y, y) \to \pi_N(X, j(y))$ is one-to-one for every $y \in Y$. ⟦Homotopy/Basic · injective_homotopyGroupMap_of_compresses⟧

*The proof as formalized.*

1. Let $\alpha, \alpha'$ be generalized loops in $Y$ at $y$ with $j_*[\alpha] = j_*[\alpha']$, and let $F : I \times I^N \to X$ be a homotopy from $j \circ \alpha$ to $j \circ \alpha'$ relative to $\partial I^N$.
2. Compress $F$ itself, as a map of the cylinder: there is $g = j \circ g'$ with a homotopy from $F$ to $g$ that fixes every point where $F$ lands in $j(Y)$. At those points $g = F$.
3. $F$ lands in $j(Y)$ on the bottom, the top and the sides of the cylinder: $F(0, z) = j(\alpha(z))$, $F(1, z) = j(\alpha'(z))$, and $F(s, z) = j(\alpha(z))$ for $z \in \partial I^N$. There $g = F$, and injectivity of $j$ gives $g'(0, z) = \alpha(z)$, $g'(1, z) = \alpha'(z)$ and $g'(s, z) = \alpha(z)$ on the sides.
4. So $g'$ is a homotopy in $Y$ from $\alpha$ to $\alpha'$ relative to $\partial I^N$, and $[\alpha] = [\alpha']$. $\square$

Neither proof uses a group structure, a finiteness hypothesis on $N$, or any property of $X$. For $N = \emptyset$ they say that $j$ is onto on path components when it compresses points, and one-to-one when it compresses paths. Milnor passes from $\pi_i(\Omega, \Omega^d) = 0$ to the isomorphism $\pi_i\Omega^d \cong \pi_i\Omega$, $i \le \lambda_0 - 2$, through the exact sequence of the pair (p. 118), which for $i = 0$ needs a separate argument because the terms are not groups (the retelling, `Exposition/Chapter13.md`, records this). The two criteria replace both the relative groups and the exact sequence, uniformly in $i$.

### XII.3 The frame construction and the change of basepoint

A map that is only *freely* homotopic to another, the basepoint being allowed to move, does not induce the same map on homotopy groups: the two differ by a change of basepoint. Mathlib has no change of basepoint for higher homotopy groups. The formal text builds one, with a single device that also produces all the homotopies of this section and the next. In this section, and in every later statement that goes through a change of basepoint, $N$ is finite, because the device uses the largest of the coordinates.

*The sup-distance from the centre.* For $y \in I^N$ let
$$d(y) = \max_{j \in N} \big|y_j - \tfrac12\big| \in [0, \tfrac12],$$
the sup norm of $y - (\frac12, \dots, \frac12)$ ⟦Homotopy/ChangeOfBase · cubeDist⟧. It is continuous ⟦Homotopy/ChangeOfBase · continuous_cubeDist⟧, bounds every $|y_j - \frac12|$ ⟦Homotopy/ChangeOfBase · abs_le_cubeDist⟧, is at most $\frac12$ ⟦Homotopy/ChangeOfBase · cubeDist_le_half⟧ and equals $\frac12$ on $\partial I^N$ ⟦Homotopy/ChangeOfBase · cubeDist_of_mem_boundary⟧. It vanishes when $N$ is empty ⟦Homotopy/ChangeOfBase · cubeDist_of_isEmpty⟧, and otherwise the maximum is attained at some coordinate ⟦Homotopy/ChangeOfBase · exists_abs_eq_cubeDist⟧.

*Rescaling.* For $r > 0$ the map
$$\rho_r(y)_j = \operatorname{clamp}\Big(\frac{y_j - \frac12}{2r} + \frac12\Big)$$
stretches the cube $\{d \le r\}$ of radius $r$ about the centre affinely onto $I^N$ ⟦Homotopy/ChangeOfBase · cubeScale⟧, and depends continuously on $y$ and on $r$ when $r$ is a positive continuous function of a parameter ⟦Homotopy/ChangeOfBase · continuous_cubeScale⟧. On $\{d \le r\}$ the clamp does nothing ⟦Homotopy/ChangeOfBase · coe_cubeScale⟧, and there $d(\rho_r(y)) = d(y)/2r$ ⟦Homotopy/ChangeOfBase · cubeDist_cubeScale⟧. The level set $\{d = r\}$ goes to $\partial I^N$: a coordinate with $|y_j - \frac12| = r$ goes to $0$ or $1$, and such a coordinate exists because $N$ is nonempty when $d(y) = r > 0$ ⟦Homotopy/ChangeOfBase · cubeScale_mem_boundary⟧. Finally $\rho_{1/2}$ is the identity ⟦Homotopy/ChangeOfBase · cubeScale_half⟧, and $\rho_r \circ \rho_{r'} = \rho_{2rr'}$ on $\{d \le 2rr'\}$ when $r \le \frac12$ ⟦Homotopy/ChangeOfBase · cubeScale_cubeScale⟧.

**Definition (frames).** Let $r$ be a function of a parameter $q$ with $0 < r(q) \le \frac12$, and let $\mathrm{in}(q, y)$, $y \in I^N$, and $\mathrm{out}(q, \delta)$, $\delta \in \mathbb R$, take values in $Y$. The frame is
$$\operatorname{Fr}(q, y) = \begin{cases} \mathrm{in}\big(q, \rho_{r(q)}(y)\big) & d(y) \le r(q), \\ \mathrm{out}\big(q, d(y)\big) & d(y) \ge r(q), \end{cases}$$
⟦Homotopy/ChangeOfBase · frame⟧ ⟦Homotopy/ChangeOfBase · frame_apply⟧. It is the map $\mathrm{in}(q, \cdot)$ shrunk into the cube of radius $r(q)$ about the centre, surrounded on the "annulus" $\{r(q) \le d \le \frac12\}$ by a map that is constant on each level set of $d$.

It is continuous when $r$, $\mathrm{in}$ and $\mathrm{out}$ are, provided $\mathrm{in}(q, y) = \mathrm{out}(q, r(q))$ for $y \in \partial I^N$ ⟦Homotopy/ChangeOfBase · continuous_frame⟧. Indeed on $\{d = r\}$ the point $\rho_r(y)$ lies on $\partial I^N$, so the two formulas agree there. Under the same compatibility the frame equals $\mathrm{out}(q, \frac12)$ on $\partial I^N$ ⟦Homotopy/ChangeOfBase · frame_of_mem_boundary⟧. If $d(y) = \frac12 \le r(q)$, then $r(q) = \frac12$, $\rho_{1/2}$ is the identity and $\mathrm{in}(q, y) = \mathrm{out}(q, \frac12)$; otherwise the second formula applies directly. Hence:

**Lemma (a frame with a parameter in $I$ is a homotopy).** If $\mathrm{out}(s, \frac12) = y_1$ for all $s \in I$, and the frames at $s = 0$ and $s = 1$ are generalized loops $\alpha$ and $\beta$ at $y_1$, then the frame is a homotopy from $\alpha$ to $\beta$ relative to $\partial I^N$. ⟦Homotopy/ChangeOfBase · homotopic_of_frame⟧

**Definition (change of basepoint).** For a path $\gamma$ from $y_0$ to $y_1$ and a generalized loop $\alpha$ at $y_0$, let $\gamma_\#\alpha$ be the frame with $r = \frac14$, inner part $\alpha$ and outer part $\delta \mapsto \gamma(4\delta - 1)$:
$$\gamma_\#\alpha(y) = \begin{cases} \alpha\big(\rho_{1/4}(y)\big) & d(y) \le \frac14, \\ \gamma\big(4d(y) - 1\big) & d(y) \ge \frac14. \end{cases}$$
⟦Homotopy/ChangeOfBase · changeBase⟧ ⟦Homotopy/ChangeOfBase · changeBase_apply⟧

The two formulas agree at $d = \frac14$, because $\alpha = y_0 = \gamma(0)$ on $\partial I^N$ ⟦Homotopy/ChangeOfBase · continuous_changeBaseOuter⟧, and on $\partial I^N$ the value is $\gamma(1) = y_1$. So $\gamma_\#\alpha$ is a generalized loop at $y_1$: the loop $\alpha$ shrunk into the middle of the cube, with the path $\gamma$ running radially from its boundary out to $\partial I^N$. A homotopy $F$ relative to $\partial I^N$ from $\alpha$ to $\alpha'$ gives the frame with inner part $F(s, \cdot)$, a homotopy from $\gamma_\#\alpha$ to $\gamma_\#\alpha'$ ⟦Homotopy/ChangeOfBase · changeBase_homotopic⟧. So $\gamma_\#$ is defined on classes ⟦Homotopy/ChangeOfBase · changeBaseMap⟧ ⟦Homotopy/ChangeOfBase · changeBaseMap_mk⟧.

**Lemma (changing back).** $(\gamma^{-1})_\#(\gamma_\#\alpha) \simeq \alpha$ relative to $\partial I^N$. ⟦Homotopy/ChangeOfBase · changeBase_symm_changeBase⟧

*The proof as formalized.* First the composite, by the rules for $\rho$. On $\{d \le \frac18\}$ it is $\alpha(\rho_{1/4}\rho_{1/4}(y)) = \alpha(\rho_{1/8}(y))$. On $\{\frac18 \le d \le \frac14\}$ it is $\gamma(8d - 1)$, since $d(\rho_{1/4}(y)) = 2d(y)$. On $\{d \ge \frac14\}$ it is $\gamma^{-1}(4d - 1) = \gamma(2 - 4d)$. So the composite runs out along $\gamma$ and back again on an annulus. The homotopy is the frame with
$$r(s) = \frac{1 + 3s}{8}, \qquad \mathrm{in} = \alpha, \qquad \mathrm{out}(s, \delta) = \gamma\big(\min(8(\delta - r(s)),\ 2 - 4\delta)\big).$$
At $s = 0$ it is the composite, case by case: the minimum is $8d - 1$ for $\frac18 \le d \le \frac14$, and $2 - 4d$ for $d \ge \frac14$. At $s = 1$, $r = \frac12 \ge d(y)$ for every $y$, and the frame is $\alpha \circ \rho_{1/2} = \alpha$. Compatibility holds because $\mathrm{out}(s, r(s)) = \gamma(\min(0, 2 - 4r(s))) = \gamma(0) = y_0$, and the boundary value is $\mathrm{out}(s, \frac12) = \gamma(0) = y_0$ because $8(\frac12 - r(s)) \ge 0$. As $s$ grows the inner cube grows, and the excursion along $\gamma$ shrinks to nothing. $\square$

**Theorem (change of basepoint is a bijection).** For a path $\gamma$ from $y_0$ to $y_1$, $\gamma_\# : \pi_N(Y, y_0) \to \pi_N(Y, y_1)$ is a bijection, with inverse $(\gamma^{-1})_\#$. ⟦Homotopy/ChangeOfBase · changeBaseMap_symm_comp⟧ ⟦Homotopy/ChangeOfBase · changeBaseEquiv⟧

One composite is the identity by the lemma, and the other by the lemma for $\gamma^{-1}$, since $(\gamma^{-1})^{-1} = \gamma$.

### XII.4 Free homotopies and homotopy equivalences

**Theorem (a free homotopy changes the induced map by a change of basepoint).** Let $H$ be a homotopy from $f$ to $g : X \to Y$, let $x_0 \in X$, and let $\omega(t) = H(t, x_0)$, a path from $f(x_0)$ to $g(x_0)$. Then $g_* = \omega_\# \circ f_*$ on $\pi_N(X, x_0)$. ⟦Homotopy/ChangeOfBase · changeBase_genLoopMap_homotopic⟧ ⟦Homotopy/ChangeOfBase · homotopyGroupMap_eq_changeBaseMap⟧

*The proof as formalized.* For a generalized loop $\alpha$ at $x_0$ take the frame with
$$r(s) = \frac{1 + s}{4}, \qquad \mathrm{in}(s, y) = H(s, \alpha(y)), \qquad \mathrm{out}(s, \delta) = \omega(4\delta - 1).$$
Compatibility: on $\partial I^N$, $\mathrm{in}(s, y) = H(s, x_0) = \omega(s)$, and $\mathrm{out}(s, r(s)) = \omega(1 + s - 1) = \omega(s)$. Boundary value: $\mathrm{out}(s, \frac12) = \omega(1) = g(x_0)$. At $s = 0$ the frame is $\omega_\#(f \circ \alpha)$ by definition. At $s = 1$ the inner cube has radius $\frac12$, the annulus has disappeared, and the frame is $H(1, \alpha(\rho_{1/2}(y))) = g(\alpha(y))$. So the frame is a homotopy from $\omega_\#(f\circ\alpha)$ to $g\circ\alpha$ relative to $\partial I^N$. $\square$

Since $\omega_\#$ is a bijection, homotopic maps have bijective, one-to-one or onto induced maps together, at every basepoint ⟦Homotopy/ChangeOfBase · bijective_homotopyGroupMap_iff⟧ ⟦Homotopy/ChangeOfBase · injective_homotopyGroupMap_iff⟧ ⟦Homotopy/ChangeOfBase · surjective_homotopyGroupMap_iff⟧.

**Theorem (homotopy equivalences).** A homotopy equivalence $e : X \to Y$ (§0.4) induces a bijection $e_* : \pi_N(X, x_0) \to \pi_N(Y, e(x_0))$ for every $x_0 \in X$. ⟦Homotopy/ChangeOfBase · bijective_homotopyGroupMap_of_homotopyEquiv⟧ ⟦Homotopy/ChangeOfBase · homotopyGroupEquivOfHomotopyEquiv⟧

*The proof as formalized.* Let $e'$ be the homotopy inverse. The difficulty is the basepoint: $e' \circ e$ is homotopic to the identity, but $e'(e(x_0))$ need not be $x_0$, so $e'_*$ at $e(x_0)$ is not literally an inverse of $e_*$ at $x_0$.

1. $e' \circ e \simeq \mathrm{id}_X$, so $(e'\circ e)_* = e'_* \circ e_*$ is a bijection at $x_0$, by the previous theorem and $\mathrm{id}_* = \mathrm{id}$.
2. $e \circ e' \simeq \mathrm{id}_Y$, so $(e\circ e')_* = e_* \circ e'_*$ is a bijection at $e(x_0)$. Here $e_*$ is taken at $e'(e(x_0))$.
3. By 2, $e'_*$ at $e(x_0)$ is one-to-one, being the first map of a one-to-one composite. By 1 it is onto, being the last map of an onto composite. So it is a bijection, and $e_* = (e'_*)^{-1} \circ (e'_* \circ e_*)$ is a bijection at $x_0$. $\square$

A homeomorphism is a homotopy equivalence ⟦Mathlib/Topology/Homotopy/Equiv · Homeomorph.toHomotopyEquiv⟧ and so induces bijections ⟦Homotopy/CellAttach · bijective_homotopyGroupMap_homeomorph⟧. The theorem also holds for maps that are homotopy equivalences in the sense of the Appendix (Part XI, §XI.1), which are Mathlib homotopy equivalences ⟦Appendix/Telescope · IsHomotopyEquiv.exists_homotopyEquiv⟧ ⟦Homotopy/RelCells · bijective_homotopyGroupMap_of_isHomotopyEquiv⟧.

**Theorem (transfer along homotopy-commutative squares).** Let $\iota : A \to X$ and $j : B \to K$ be maps, and $a : A \to B$ and $e : X \to K$ homotopy equivalences with $e \circ \iota \simeq j \circ a$. Then $\iota_*$ is bijective (one-to-one, onto) on $\pi_N$ at $x_0 \in A$ if and only if $j_*$ is at $a(x_0)$. ⟦Homotopy/ChangeOfBase · bijective_homotopyGroupMap_iff_of_square⟧ ⟦Homotopy/ChangeOfBase · injective_homotopyGroupMap_iff_of_square⟧ ⟦Homotopy/ChangeOfBase · surjective_homotopyGroupMap_iff_of_square⟧

*Proof.* Compose $\iota_*$ on the left with the bijection $e_*$ at $\iota(x_0)$, and $j_*$ on the right with the bijection $a_*$ at $x_0$; neither changes bijectivity. By functoriality the composites are $(e \circ \iota)_*$ and $(j \circ a)_*$, which are bijective together because the two maps are homotopic. $\square$

The square need only commute up to a free homotopy, and this is exactly how relative cell complexes are defined (Part IX, §IX.2). The theorem is what lets the cell theorems below, proved for adjunction spaces, apply to spaces that only have their homotopy type.

### XII.5 The push-off lemma in coordinates

The key step of cellular approximation is Hatcher's Lemma 4.10: a map from a space of dimension $i$ into a space with a cell of dimension $\lambda > i$ can be deformed, without moving the part mapped far from the centre of the cell, so as to miss a whole ball about the centre. Hatcher proves it by simplicial approximation on a subdivision of the domain. The formal proof uses smoothness instead. It is possible because every domain that occurs, a cube or a cube times $I$, embeds in a vector space of smaller dimension than the cell. This section does the work in the coordinates of the cell; §XII.7 transports it to an attached cell.

*The cut-off.* Let
$$\beta(\delta) = \max\big(0, \min(1, 3 - 4\delta)\big),$$
so that $\beta = 1$ on $(-\infty, \frac12]$, $\beta = 0$ on $[\frac34, \infty)$, $\beta$ is linear in between, continuous, and takes values in $[0, 1]$ ⟦Homotopy/PushOff · pushCutoff⟧ ⟦Homotopy/PushOff · continuous_pushCutoff⟧ ⟦Homotopy/PushOff · pushCutoff_nonneg⟧ ⟦Homotopy/PushOff · pushCutoff_le_one⟧ ⟦Homotopy/PushOff · pushCutoff_of_le⟧ ⟦Homotopy/PushOff · pushCutoff_of_ge⟧.

**Lemma (smooth approximation through an injection).** Let $P$ be compact, $\iota : P \to V$ a continuous injection into a finite-dimensional real normed space, $C \subseteq P$ closed, $h : P \to E$ continuous on $C$ with $E$ finite-dimensional, and $\delta > 0$. Then there is a smooth $Q : V \to E$ with $\|Q(\iota(p)) - h(p)\| < \delta$ for all $p \in C$. ⟦Homotopy/PushOff · exists_contDiff_near⟧

*The proof as formalized.* If $P$ is empty there is nothing to prove. Otherwise $\iota$ is a continuous injection of a compact space into a Hausdorff space, hence a closed embedding ⟦Mathlib/Topology/Separation/Hausdorff · Continuous.isClosedEmbedding⟧, and $\iota(C)$ is compact. A left inverse $\iota^{-1}$ of $\iota$ is continuous on $\iota(C)$, because $\iota$ is an embedding, and maps $\iota(C)$ into $C$. So $h \circ \iota^{-1}$ is continuous on the compact set $\iota(C) \subseteq V$, and the Stone–Weierstrass theorem for smooth maps of the companion project gives a smooth $Q$ within $\delta$ of it on $\iota(C)$ ⟦Milnor/Chapter8/Approx · Problems.exists_contDiff_approx_of_isCompact⟧. (That theorem approximates each coordinate of a map in a basis of $E$ by the restriction of a smooth function; these restrictions form an algebra that separates points, because linear functionals do ⟦Mathlib/Topology/ContinuousMap/StoneWeierstrass · ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints⟧.) Evaluating at $\iota(p)$ for $p \in C$ gives the claim. $\square$

**Theorem (the push-off lemma in coordinates).** Let $P$ be compact with a continuous injection $\iota : P \to V$, where $V$ and $E$ are finite-dimensional real normed spaces with $\dim V < \dim E$. Let $W \subseteq P$, and let $h : P \to E$ be continuous on $W$ with $\|h(p)\| < 1$ for $p \in W$, such that $C = \{p \in W : \|h(p)\| \le \frac34\}$ is closed in $P$. Then there are a map $H : I \times P \to E$, continuous on $I \times W$, and $\varepsilon > 0$ such that:

1. $H(0, p) = h(p)$ for all $p$;
2. $H(t, p) = h(p)$ for all $t$ whenever $\|h(p)\| \ge \frac34$;
3. $\|H(t, p)\| < 1$ for $p \in W$;
4. $\|H(1, p)\| \ge \varepsilon$ for $p \in W$.

⟦Homotopy/PushOff · exists_pushOff⟧

In the application $E = \mathbb R^\lambda$ is the cell, $W$ is the set of points mapped into the open cell, and $h$ is the coordinate in the cell. The homotopy moves nothing that lies outside the ball of radius $\frac34$, stays in the open cell, and ends missing the ball of radius $\varepsilon$. The set $W$ need not be open; closedness of $C$ is all that is used.

*The proof as formalized.*

1. *Approximation.* By the lemma, with $\delta = \frac18$, there is a smooth $Q : V \to E$ with $\|Q(\iota(p)) - h(p)\| < \frac18$ on $C$.
2. *A missed point.* Since $\dim V < \dim E$, the complement of the range of the $C^1$ map $Q$ is dense ⟦Mathlib/Topology/MetricSpace/HausdorffDimension · ContDiff.dense_compl_range_of_finrank_lt_finrank⟧. Mathlib proves this through Hausdorff dimension: the range of a $C^1$ map on $V$ has Hausdorff dimension at most $\dim V$ ⟦Mathlib/Topology/MetricSpace/HausdorffDimension · ContDiff.dimH_range_le⟧, smaller than that of any open subset of $E$. It is the easiest case of Sard's theorem, every point being critical. So some $p_0$ with $\|p_0\| < \frac18$ is not a value of $Q$.
3. *A ball missing the image.* $Q(\iota(P))$ is compact, hence closed, and does not contain $p_0$. So there is $\varepsilon_0 > 0$ with $\|Q(\iota(p)) - p_0\| \ge \varepsilon_0$ for every $p \in P$.
4. *The homotopy.* Put
$$H(t, p) = h(p) + t\,\beta(\|h(p)\|)\,\big(Q(\iota(p)) - p_0 - h(p)\big), \qquad \varepsilon = \min(\varepsilon_0, \tfrac14).$$
It is continuous on $I \times W$, since $h$ is continuous there and $\beta$, $Q$, $\iota$ are continuous. Clearly $H(0, \cdot) = h$, and $\beta(\|h(p)\|) = 0$ when $\|h(p)\| \ge \frac34$, which is clause 2.
5. *It stays in the open ball over $W$.* If $\|h(p)\| \ge \frac34$ then $H(t, p) = h(p)$ has norm $< 1$. Otherwise $p \in C$, and
$$\|Q(\iota(p)) - p_0 - h(p)\| \le \|Q(\iota(p)) - h(p)\| + \|p_0\| < \tfrac18 + \tfrac18 = \tfrac14.$$
The coefficient $t\beta$ lies in $[0, 1]$, so $\|H(t, p)\| < \frac34 + \frac14 = 1$.
6. *It misses the ball of radius $\varepsilon$ at $t = 1$.* If $\|h(p)\| \le \frac12$, then $\beta = 1$ and $H(1, p) = Q(\iota(p)) - p_0$, of norm $\ge \varepsilon_0 \ge \varepsilon$. If $\|h(p)\| \ge \frac34$, then $H(1, p) = h(p)$, of norm $\ge \frac34 > \varepsilon$. In between, the correction $\beta(\cdots)(Q(\iota(p)) - p_0 - h(p))$ has norm $< \frac14$ by step 5, so $\|H(1, p)\| > \frac12 - \frac14 = \frac14 \ge \varepsilon$. $\square$

The translation by $-p_0$ is the whole trick: $Q$ approximates $h$ near the centre, and subtracting a point not in the range of $Q$ moves the hole of $Q \circ \iota$ to the centre of the cell.

### XII.6 The point-set topology of $Y \cup_\varphi e^n$

Recall from §0.5 and Part II: for a space $Y$ and a map $\varphi : S^{n-1} \to Y$, the space $X = Y \cup_\varphi e^n$ is the pushout, in the category of topological spaces, of $\varphi$ and the inclusion $S^{n-1} \to D^n$ ⟦Chapter2/Attaching · AttachCell⟧. It comes with the inclusion $Y \to X$ and the characteristic map $D^n \to X$ ⟦Chapter2/Attaching · cellInl⟧ ⟦Chapter2/Attaching · cellInr⟧, and a map out of $X$ is a pair of maps on $Y$ and on $D^n$ that agree along $\varphi$ ⟦Chapter2/Attaching · cellDesc⟧. Here $D^n$ and $S^{n-1}$ are the closed unit ball and the unit sphere of $\mathbb R^n$ ⟦Mathlib/Topology/Category/TopCat/Sphere · TopCat.disk⟧ ⟦Mathlib/Topology/Category/TopCat/Sphere · TopCat.diskBoundary⟧ ⟦Mathlib/Topology/Category/TopCat/Sphere · TopCat.diskBoundaryInclusion⟧. A point of $D^n$ is a vector $z$ with $\|z\| \le 1$ ⟦Chapter2/Attaching · diskPt⟧ ⟦Chapter2/Attaching · dvec⟧ ⟦Chapter2/Attaching · norm_dvec_le⟧, called "the point $z$ of the cell" when viewed in $X$. For $u \in S^{n-1}$ the points $\varphi(u)$ of $Y$ and $u$ of the cell coincide in $X$ ⟦Chapter2/Attaching · cellInl_apply_eq⟧. Nothing is assumed about $Y$: it need not be Hausdorff, or even $T_1$. Everything the push-off needs is extracted from the pushout itself.

*The underlying set.* The forgetful functor to sets preserves pushouts, so the set underlying $X$ is the pushout of the underlying sets ⟦Homotopy/CellAttach · isPushout_forget⟧. Since $S^{n-1} \to D^n$ is injective ⟦Homotopy/CellAttach · injective_diskBoundaryInclusion⟧, Mathlib's description of pushouts of sets gives three facts. Every point of $X$ comes from $Y$ or from $D^n$ ⟦Homotopy/CellAttach · exists_eq_cellInl_or_cellInr⟧ ⟦Mathlib/CategoryTheory/Limits/Types/Pushouts · Types.eq_or_eq_of_isPushout⟧. The inclusion $Y \to X$ is injective ⟦Homotopy/CellAttach · cellInl_injective⟧ ⟦Mathlib/CategoryTheory/Limits/Types/Pushouts · Types.pushoutCocone_inr_injective_of_isColimit⟧. And the point $z$ of the cell equals the point $y$ of $Y$ exactly when $z \in S^{n-1}$ and $\varphi(z) = y$ ⟦Homotopy/CellAttach · cellInr_eq_cellInl_iff⟧ ⟦Mathlib/CategoryTheory/Limits/Types/Pushouts · CategoryTheory.Limits.Types.pushoutCocone_inl_eq_inr_iff_of_isColimit⟧.

*The topology.* A set $S \subseteq X$ is closed if and only if its preimages in $Y$ and in $D^n$ are closed ⟦Homotopy/CellAttach · isClosed_attachCell_iff⟧. A colimit carries the final topology for the maps from the objects of the diagram ⟦Mathlib/Topology/Category/TopCat/Limits/Basic · TopCat.isClosed_iff_of_isColimit⟧; the third object $S^{n-1}$ adds no condition, since its preimage is the preimage under $\varphi$ of the preimage in $Y$.

**Lemma.** The inclusion $Y \to X$ is a closed embedding. ⟦Homotopy/CellAttach · isClosedEmbedding_cellInl⟧

*Proof.* A continuous injective closed map is a closed embedding ⟦Mathlib/Topology/Maps/Basic · IsClosedEmbedding.of_continuous_injective_isClosedMap⟧. Let $C \subseteq Y$ be closed. The preimage of its image in $Y$ is $C$, by injectivity. The preimage in $D^n$ is the image of $\varphi^{-1}(C)$ under $S^{n-1} \to D^n$, by the description of the identifications. This is the image of a compact set, a closed subset of the compact sphere, so it is compact, hence closed in the Hausdorff ball. $\square$

*The probe.* Define $\Pi : X \to \mathbb R^n \times \mathbb R$ by
$$\Pi = (0, 0) \text{ on } Y, \qquad \Pi(z) = \big((1 - \|z\|)\,z,\ 1 - \|z\|\big) \text{ at the point } z \text{ of the cell}$$
⟦Homotopy/CellAttach · cellProbe⟧ ⟦Homotopy/CellAttach · cellProbe_inl⟧ ⟦Homotopy/CellAttach · cellProbe_inr⟧. The two formulas agree along $\varphi$, as $\|z\| = 1$ on $S^{n-1}$, so $\Pi$ is continuous by the universal property. Its second coordinate is the **height** $\eta$ ⟦Homotopy/CellAttach · cellHeight⟧, continuous ⟦Homotopy/CellAttach · continuous_cellHeight⟧, equal to $0$ on $Y$ and to $1 - \|z\|$ at the point $z$ of the cell ⟦Homotopy/CellAttach · cellHeight_inl⟧ ⟦Homotopy/CellAttach · cellHeight_inr⟧, and never negative ⟦Homotopy/CellAttach · cellHeight_nonneg⟧. The **coordinate** is $\zeta = (\text{first coordinate of } \Pi)/\eta$ ⟦Homotopy/CellAttach · cellCoord⟧, which by the formal convention $0^{-1} = 0$ is $0$ on $Y$. It is continuous on the open cell $\{\eta > 0\}$ ⟦Homotopy/CellAttach · continuousOn_cellCoord⟧, and equals $z$ at the point $z$ of the cell when $\|z\| < 1$ ⟦Homotopy/CellAttach · cellCoord_inr⟧.

Four facts follow.

- $Y$ is exactly the zero set of $\eta$ ⟦Homotopy/CellAttach · mem_range_cellInl_iff⟧: the point $z$ of the cell has height $0$ only if $\|z\| = 1$, and then it lies in $Y$ ⟦Homotopy/CellAttach · cellInr_mem_range_of_norm_eq_one⟧.
- A point of positive height is the point $z$ of the cell for some $\|z\| < 1$ ⟦Homotopy/CellAttach · exists_cellInr_of_cellHeight_pos⟧, and there $\|\zeta\| = 1 - \eta$ ⟦Homotopy/CellAttach · norm_cellCoord⟧.
- So the open cell $\{\eta > 0\}$ is open, its coordinate $\zeta$ is continuous on it, and for $r < 1$ the closed ball $\{\|\zeta\| \le r\}$ of the cell is the closed set $\{\eta \ge 1 - r\}$.
- The characteristic map extends to all of $\mathbb R^n$. Let $c(z) = z/\max(1, \|z\|)$ be the radial retraction of $\mathbb R^n$ onto its closed unit ball ⟦Homotopy/CellAttach · clampBall⟧, continuous ⟦Homotopy/CellAttach · continuous_clampBall⟧, with $\|c(z)\| = \min(1, \|z\|)$ ⟦Homotopy/CellAttach · norm_clampBall⟧ ⟦Homotopy/CellAttach · norm_clampBall_le⟧ and $c(z) = z$ on the ball ⟦Homotopy/CellAttach · clampBall_of_norm_le⟧. Let $\chi(z)$ be the point $c(z)$ of the cell ⟦Homotopy/CellAttach · cellChar⟧. Then $\chi$ is continuous ⟦Homotopy/CellAttach · continuous_cellChar⟧ and is the point $z$ of the cell when $\|z\| \le 1$ ⟦Homotopy/CellAttach · cellChar_of_norm_le⟧. It inverts the coordinate: $\chi(\zeta(x)) = x$ when $\eta(x) > 0$ ⟦Homotopy/CellAttach · cellChar_cellCoord⟧, and $\zeta(\chi(z)) = z$, $\eta(\chi(z)) = 1 - \|z\|$ for $\|z\| < 1$ ⟦Homotopy/CellAttach · cellCoord_cellChar⟧ ⟦Homotopy/CellAttach · cellHeight_cellChar⟧.

The usual proof that the open cell is open and homeomorphic to the open ball works in the quotient topology directly. The probe replaces it by two continuous functions, and with them the continuity of every map below is a matter of continuous functions on open sets.

### XII.7 The push-off and the radial push in $Y \cup_\varphi e^n$

*The radial push of the ball.* For $0 < \varepsilon \le 1$ and $t \in I$ let
$$R_t(z) = c\big((1 + t(\varepsilon^{-1} - 1))\,z\big)$$
⟦Homotopy/CellAttach · radialPush⟧, continuous in $(t, z)$ ⟦Homotopy/CellAttach · continuous_radialPush⟧, with values in the closed ball ⟦Homotopy/CellAttach · norm_radialPush_le⟧. $R_0$ is the identity of the ball ⟦Homotopy/CellAttach · radialPush_zero⟧. Every $R_t$ fixes the unit sphere, because the factor $1 + t(\varepsilon^{-1} - 1)$ is at least $1$ and the clamp divides it out again ⟦Homotopy/CellAttach · radialPush_of_norm_eq_one⟧. And $R_1(z) = c(z/\varepsilon)$ lies on the unit sphere whenever $\|z\| \ge \varepsilon$ ⟦Homotopy/CellAttach · norm_radialPush_one⟧.

*The radial push of $X$.* On the cell, $z \mapsto (t \mapsto \text{the point } R_t(z) \text{ of the cell})$ is a continuous map from $D^n$ to the space of paths in $X$ ⟦Homotopy/CellAttach · radialDisk⟧ ⟦Mathlib/Topology/CompactOpen · ContinuousMap.curry⟧. On $Y$ take the constant paths. The two agree along $\varphi$, because $R_t$ fixes the sphere ⟦Homotopy/CellAttach · radialDisk_compat⟧. The universal property gives a continuous map from $X$ to the space of paths in $X$, and uncurrying it, which is legitimate because $I$ is locally compact ⟦Mathlib/Topology/CompactOpen · ContinuousMap.uncurry⟧, gives a homotopy $\mathcal R : I \times X \to X$ ⟦Homotopy/CellAttach · cellRadial⟧. This is the same use of the exponential law as for homotopies out of an adjunction space (§0.5) ⟦Chapter2/Attaching · cellHomotopy⟧. Its properties:

- $\mathcal R_t$ is the identity on $Y$ for every $t$ ⟦Homotopy/CellAttach · cellRadial_inl⟧ ⟦Homotopy/CellAttach · cellRadial_of_mem_range⟧, and is $R_t$ on the cell ⟦Homotopy/CellAttach · cellRadial_inr⟧;
- $\mathcal R_0$ is the identity of $X$ ⟦Homotopy/CellAttach · cellRadial_zero⟧;
- $\mathcal R_1$ maps into $Y$ every point $x$ such that $\eta(x) > 0$ implies $\|\zeta(x)\| \ge \varepsilon$ ⟦Homotopy/CellAttach · cellRadial_one_mem⟧. A point of $Y$ stays in $Y$. A point $z$ of the cell with $\|z\| < 1$ has positive height, hence $\|z\| \ge \varepsilon$, and goes to the sphere, which lies in $Y$. A point with $\|z\| = 1$ is fixed and already lies in $Y$.

Hatcher's proof finishes by projecting radially from a point of the open cell that the deformed map misses, a deformation of the punctured cell onto its boundary sphere that is undefined at the puncture. The formal proof never removes a point: $\mathcal R$ is defined on all of $X$, and it expands the small ball $\{\|z\| < \varepsilon\}$ over the whole cell. It is enough that the map to be pushed avoids that ball, and the push-off provides a ball, not just a point, because its image is compact.

A homotopy relative to $S$ can be given by its values: a continuous $F$ on $I \times P$ with the right ends that fixes $S$ ⟦Homotopy/CellAttach · homotopyRelOfFun⟧.

**Theorem (the push-off lemma; Hatcher, Lemma 4.10).** Let $P$ be compact with a continuous injection $\iota : P \to V$ into a finite-dimensional real vector space with $\dim V < n$. Every map $f : P \to X = Y \cup_\varphi e^n$ is homotopic, relative to $\{p : \eta(f(p)) < \frac14\}$, to a map $g$ that misses a ball of the cell: for some $\varepsilon > 0$, $\|\zeta(g(p))\| \ge \varepsilon$ whenever $\eta(g(p)) > 0$. ⟦Homotopy/CellAttach · exists_homotopicRel_avoid_ball⟧

The set $\{\eta(f(p)) < \frac14\}$ consists of the points that $f$ maps into $Y$ or outside the closed ball of radius $\frac34$ of the cell.

*The proof as formalized.*

1. *Coordinates.* Let $W = \{p : \eta(f(p)) > 0\}$, an open set, and $h = \zeta \circ f$, continuous on $W$ with $\|h\| = 1 - \eta \circ f < 1$ there. The set $\{p \in W : \|h(p)\| \le \frac34\}$ equals $\{p : \eta(f(p)) \ge \frac14\}$, which is closed.
2. *The push-off in coordinates* (§XII.5), with $E = \mathbb R^n$, gives $H$ and $\varepsilon$.
3. *Back in $X$.* Put $F(t, p) = \chi(H(t, p))$ if $\eta(f(p)) > 0$, and $F(t, p) = f(p)$ otherwise.
4. *$F$ fixes $\{\eta \circ f < \frac14\}$.* For height $0$ this is the definition. For $0 < \eta(f(p)) < \frac14$, $\|h(p)\| = 1 - \eta(f(p)) > \frac34$, so $H(t, p) = h(p)$ and $F(t, p) = \chi(\zeta(f(p))) = f(p)$.
5. *$F$ is continuous.* Near a point $(t, p)$ with $\eta(f(p)) > 0$, $F$ agrees with $\chi \circ H$ on the open set $\{\eta \circ f > 0\}$, and $\chi\circ H$ is continuous at $(t,p)$ because $H$ is continuous on the neighbourhood $I \times W$. Near a point with $\eta(f(p)) = 0$, $F$ agrees with $(t, p) \mapsto f(p)$ on the open set $\{\eta \circ f < \frac14\}$, by step 4.
6. *The ends.* $F(0, p) = f(p)$, since $H(0, p) = h(p)$ and $\chi(\zeta(f(p))) = f(p)$ at positive height. Let $g = F(1, \cdot)$. By steps 4 and 5, $F$ is a homotopy from $f$ to $g$ relative to $\{\eta \circ f < \frac14\}$.
7. *$g$ misses the ball.* If $\eta(g(p)) > 0$, then $\eta(f(p)) > 0$, for otherwise $g(p) = f(p)$ would have height $0$. So $g(p) = \chi(H(1, p))$ with $\|H(1, p)\| < 1$, hence $\zeta(g(p)) = H(1, p)$, of norm $\ge \varepsilon$. $\square$

**Theorem (the radial push into $Y$).** Let $g : P \to X$ and $\varepsilon > 0$ be such that $\|\zeta(g(p))\| \ge \varepsilon$ whenever $\eta(g(p)) > 0$. Then $g$ is homotopic, relative to $g^{-1}(Y)$, to a map into $Y$. ⟦Homotopy/CellAttach · exists_homotopicRel_into_range⟧

*Proof.* Let $\varepsilon' = \min(\varepsilon, \frac14)$, which lies in $(0, 1]$ as the radial push requires, and take $(t, p) \mapsto \mathcal R_t(g(p))$ for $\varepsilon'$. It starts at $g$, fixes the points mapped into $Y$, and at $t = 1$ lands in $Y$ because $\|\zeta(g(p))\| \ge \varepsilon \ge \varepsilon'$ at positive height. $\square$

**Theorem (compression into $Y$).** Let $P$ be compact with a continuous injection into a finite-dimensional real vector space $V$ with $\dim V < n$. Then the inclusion $Y \to Y \cup_\varphi e^n$ compresses maps from $P$: every $f : P \to Y \cup_\varphi e^n$ is homotopic, relative to $f^{-1}(Y)$, to a map into $Y$. ⟦Homotopy/CellAttach · compresses_cellInl⟧

*The proof as formalized.* The push-off gives $F$ from $f$ to $g$, relative to $\{\eta \circ f < \frac14\}$. This set contains $f^{-1}(Y)$, where $\eta = 0$, so $F$ is also relative to $f^{-1}(Y)$. The radial push gives $G$ from $g$ to a map into $Y$, relative to $g^{-1}(Y)$. This set contains $f^{-1}(Y)$, because $F$ fixes those points and so $g = f$ there. The concatenation of $F$ and $G$ is relative to $f^{-1}(Y)$ ⟦Homotopy/Basic · homotopyRelMono⟧ ⟦Mathlib/Topology/Homotopy/Basic · ContinuousMap.HomotopyRel.trans⟧. $\square$

### XII.8 Attaching cells does not change the low homotopy groups

The cube and the cylinder embed in vector spaces of their own dimension: $I^N \to \mathbb R^N$ ⟦Homotopy/CellAttach · cubeEmb⟧ ⟦Homotopy/CellAttach · continuous_cubeEmb⟧ ⟦Homotopy/CellAttach · injective_cubeEmb⟧ and $I \times I^N \to \mathbb R \times \mathbb R^N$ ⟦Homotopy/CellAttach · cylEmb⟧ ⟦Homotopy/CellAttach · continuous_cylEmb⟧ ⟦Homotopy/CellAttach · injective_cylEmb⟧, of dimensions $|N|$ and $|N| + 1$. So the inclusion $Y \to Y \cup_\varphi e^n$ compresses maps from $I^N$ when $|N| < n$, and from $I \times I^N$ when $|N| + 1 < n$ ⟦Homotopy/CellAttach · compresses_cellInl_cube⟧ ⟦Homotopy/CellAttach · compresses_cellInl_cyl⟧.

**Theorem (one cell).** Let $N$ be finite, $Y$ any space, $\varphi : S^{n-1} \to Y$ and $y \in Y$. The inclusion $Y \to Y \cup_\varphi e^n$ induces a map $\pi_N(Y, y) \to \pi_N(Y \cup_\varphi e^n, y)$ that is

- onto if $|N| < n$ ⟦Homotopy/CellAttach · surjective_homotopyGroupMap_cellInl⟧,
- one-to-one if $|N| + 1 < n$ ⟦Homotopy/CellAttach · injective_homotopyGroupMap_cellInl⟧,
- bijective if $|N| + 2 \le n$ ⟦Homotopy/CellAttach · bijective_homotopyGroupMap_cellInl⟧.

In Milnor's terms: attaching a $\lambda$-cell induces isomorphisms on $\pi_i$ for $i \le \lambda - 2$ and epimorphisms for $i = \lambda - 1$.

*Proof.* The inclusion is a closed embedding (§XII.6), in particular an embedding, and the compression criteria of §XII.2 apply with the two compressions above. $\square$

**Theorem (finitely many cells).** Let $K$ be obtained from $L$ by attaching cells of dimensions $c_1, \dots, c_k$ one at a time, each along an arbitrary map, with $j : L \to K$ the composite of the inclusions (§0.5; Part IX, §IX.2) ⟦Appendix/MonotoneUnion · IsRelCellAttachment⟧. If all $c_i \ge |N| + 2$, then $j_*$ is bijective on $\pi_N$ at every $x \in L$; if all $c_i > |N|$, it is onto. ⟦Homotopy/CellAttach · bijective_homotopyGroupMap_of_isRelCellAttachment⟧ ⟦Homotopy/CellAttach · surjective_homotopyGroupMap_of_isRelCellAttachment⟧

*Proof.* Induction on the attachment. With no cells $j$ is the identity, and $\mathrm{id}_* = \mathrm{id}$. If $K = K_1 \cup_\psi e^c$ and $j$ is $j_1 : L \to K_1$ followed by the inclusion, then $j_*$ is $(j_1)_*$ followed by the map of the one-cell theorem at the basepoint $j_1(x)$, a composite of bijections (surjections). $\square$

*Other pushout squares.* Suppose $j : A \to Q$ and $\chi : D^n \to Q$ form a pushout square with some $\psi : S^{n-1} \to A$ and the inclusion $S^{n-1} \to D^n$ ⟦Mathlib/CategoryTheory/Limits/Shapes/Pullback/IsPullback/Defs · CategoryTheory.IsPushout⟧. Then $Q$ is canonically homeomorphic to $A \cup_\psi e^n$, with $j$ corresponding to the inclusion ⟦Mathlib/CategoryTheory/Limits/Shapes/Pullback/IsPullback/Defs · CategoryTheory.IsPushout.isoPushout⟧. Compressions are transported along homeomorphisms of the target ⟦Homotopy/CellAttach · Compresses.comp_homeomorph⟧, so $j$ compresses maps from every compact $P$ that embeds in dimension $< n$ ⟦Homotopy/CellAttach · compresses_of_isPushout⟧. On homotopy groups the inclusion of $A$ into $A \cup_\psi e^n$ is $j_*$ followed by the bijection induced by the homeomorphism, so $j_*$ is bijective for $|N| + 2 \le n$ and onto for $|N| < n$ ⟦Homotopy/CellAttach · bijective_homotopyGroupMap_of_isPushout⟧ ⟦Homotopy/CellAttach · surjective_homotopyGroupMap_of_isPushout⟧.

**Theorem (an embedded cell).** Let $M$ be a Hausdorff space, $A \subseteq M$ closed, and $\chi : \mathbb R^n \to M$ continuous and injective on the closed unit ball $D^n$, with $\chi(z) \in A$ exactly when $\|z\| = 1$, for $z \in D^n$. Then:

- every map from a compact $P$ that embeds continuously in dimension $< n$ into $A \cup \chi(D^n)$ is homotopic, relative to the preimage of $A$, to a map into $A$ ⟦Homotopy/CellAttach · compresses_union_cell⟧;
- the inclusion $A \to A \cup \chi(D^n)$ is bijective on $\pi_N$ for $|N| + 2 \le n$ and onto for $|N| < n$, at every basepoint $a \in A$ ⟦Homotopy/CellAttach · bijective_homotopyGroupMap_union_cell⟧ ⟦Homotopy/CellAttach · surjective_homotopyGroupMap_union_cell⟧.

*Proof.* Lemma D in a Hausdorff space (Part II, §II.11) makes $A \cup \chi(D^n)$ the pushout of $\chi|S^{n-1} : S^{n-1} \to A$ and $S^{n-1} \to D^n$, with the inclusion of $A$ as one side of the square ⟦Chapter2/CellPatch · exists_isPushout_union_cell_of_t2⟧. Then the results for pushout squares apply. $\square$

This is the form in which Theorem 3.2 and Remark 3.3 produce cells (Part II), and the form used for spheres in §XII.18. The Hausdorff hypothesis and the closedness of $A$ are those of Lemma D; they make the cell a closed set on which $\chi$ is a homeomorphism.

### XII.9 Compact sets lie in a finite stage

Milnor's countable complexes are increasing unions, and their homotopy groups are computed by compactness: a map from a cube, or a homotopy on a cylinder, has compact image, and a compact set lies in a finite stage. The formal statements take this as a hypothesis on the stages, so that it applies equally to sublevel sets and to truncations of telescopes.

**Lemma.** If $A_0 \subseteq A_1 \subseteq \cdots \subseteq X$ and every point of $X$ has some $A_n$ as a neighbourhood, then every compact $K \subseteq X$ lies in some $A_n$. ⟦Homotopy/Telescope · exists_subset_of_isCompact⟧

*Proof.* The interiors of the $A_n$ form an increasing open cover of $K$, so finitely many of them, hence one, cover it ⟦Mathlib/Topology/Compactness/Compact · IsCompact.elim_directed_cover⟧. $\square$

For a map $f : Y \to X$ with values in a subset $S$, its corestriction is the same map as a map $Y \to S$ ⟦Homotopy/Telescope · corestrict⟧, and the inclusion of $S$ is a continuous map $S \to X$ ⟦Homotopy/Telescope · valC⟧.

**Theorem (compactness).** Let $A_0, A_1, \dots$ be subsets of $X$ such that every compact subset of $X$ lies in some $A_n$, and let $\iota : Y \to X$ be a map with values in every $A_n$. If for every $n$ the corestriction $\iota_n : Y \to A_n$ is onto (one-to-one, bijective) on $\pi_N$ at $y_0$, then so is $\iota$. ⟦Homotopy/Telescope · surjective_homotopyGroupMap_of_exhaustion⟧ ⟦Homotopy/Telescope · injective_homotopyGroupMap_of_exhaustion⟧ ⟦Homotopy/Telescope · bijective_homotopyGroupMap_of_exhaustion⟧

*The proof as formalized.* $\iota$ is $\iota_n$ followed by the inclusion of $A_n$, so $\iota_* = (\text{inclusion})_* \circ (\iota_n)_*$.

- *Onto.* Let $\gamma$ be a generalized loop in $X$ at $\iota(y_0)$. Its image is compact, so it lies in some $A_n$, and $\gamma$ is a generalized loop in $A_n$ at $\iota_n(y_0)$. Choose $[\alpha]$ with $(\iota_n)_*[\alpha] = [\gamma \text{ in } A_n]$. The inclusion carries $[\gamma \text{ in } A_n]$ to $[\gamma]$, so $\iota_*[\alpha] = [\gamma]$.
- *One-to-one.* Let $F$ be a homotopy relative to $\partial I^N$ in $X$ from $\iota\circ\alpha$ to $\iota\circ\alpha'$. Its image $F(I \times I^N)$ is compact, so it lies in some $A_n$, and $F$ is a homotopy in $A_n$ from $\iota_n\circ\alpha$ to $\iota_n\circ\alpha'$, still relative to $\partial I^N$. Since $(\iota_n)_*$ is one-to-one, $[\alpha] = [\alpha']$. $\square$

No finiteness of $N$ and no group structure is involved. The hypothesis that $\iota$ lands in every $A_n$ is satisfied in practice by maps into $A_0$, the $A_n$ being increasing.

**Theorem (increasing unions).** Let $A_0 \subseteq A_1 \subseteq \cdots \subseteq X$ be such that every compact subset of $X$ lies in some $A_n$. If every inclusion $A_n \to A_{n+1}$ is bijective (onto) on $\pi_N$ at every basepoint, then so is the inclusion $A_0 \to X$. ⟦Homotopy/Telescope · bijective_homotopyGroupMap_valC_of_step⟧ ⟦Homotopy/Telescope · surjective_homotopyGroupMap_valC_of_step⟧

*Proof.* By the compactness theorem it suffices that each corestriction $A_0 \to A_n$ is bijective (onto). It is the identity for $n = 0$, and for $n + 1$ it is the corestriction to $A_n$ followed by the inclusion $A_n \to A_{n+1}$; induction on $n$. $\square$

### XII.10 Mapping telescopes and countable cell complexes

The countable complexes of the project are mapping telescopes of towers of iterated adjunction spaces (Part IX, §IX.4; Part XI, §XI.15). Recall from Part XI (§XI.12) the mapping telescope $\operatorname{Tel}(K)$ of $K_0 \to K_1 \to \cdots$ ⟦Appendix/MappingTelescope · MappingTelescope⟧, the maps $c_{m,n} : K_m \to K_n$ of the sequence ⟦Appendix/MappingTelescope · tmap⟧ with $c_{n,n} = \mathrm{id}$ and $c_{m,n}c_{l,m} = c_{l,n}$ ⟦Appendix/MappingTelescope · tmap_refl⟧ ⟦Appendix/MappingTelescope · tmap_tmap⟧, its points $[k, t]_n$ with $[k, 1]_n = [c_n k, 0]_{n+1}$ ⟦Appendix/MappingTelescope · MappingTelescope.mk⟧ ⟦Appendix/MappingTelescope · MappingTelescope.mk_one⟧, the level $\ell[k, t]_n = n + t$ ⟦Appendix/MappingTelescope · MappingTelescope.level⟧, the truncations $\operatorname{Tel}^n(K) = \{\ell \le n\}$ ⟦Appendix/MappingTelescope · MappingTelescope.trunc⟧, the push $\operatorname{push}_n$, which deforms $\operatorname{Tel}^n(K)$ within itself up to level $n$ along the trajectories of the maps ⟦Appendix/MappingTelescope · MappingTelescope.traj⟧ ⟦Appendix/MappingTelescope · MappingTelescope.pushFun⟧ ⟦Appendix/MappingTelescope · MappingTelescope.push⟧ ⟦Appendix/MappingTelescope · MappingTelescope.push_mk⟧, and (T2): $\kappa_n : K_n \to \operatorname{Tel}^n(K)$, $k \mapsto [k, 0]_n$, is a homotopy equivalence ⟦Appendix/MappingTelescope · MappingTelescope.levelIncl⟧ ⟦Appendix/MappingTelescope · MappingTelescope.isHomotopyEquiv_levelIncl⟧.

Let $\kappa : K_0 \to \operatorname{Tel}(K)$, $k \mapsto [k, 0]_0$, be the inclusion of the bottom ⟦Homotopy/Telescope · telescopeIncl⟧. Its values have level $0$, so they lie in every truncation ⟦Homotopy/Telescope · telescopeIncl_mem_trunc⟧.

**Lemma (pushing the bottom of a block).** For $m \le n$ and $k \in K_m$, $\operatorname{push}_n(1, [k, 0]_m) = [c_{m,n}k, 0]_n$. ⟦Homotopy/Telescope · push_one_mk_zero⟧

*Proof.* At time $1$ the push moves a point $[k, t]_m$ of level $\le n$ to height $t + \max(0, n - m - t)$ along the trajectory of $k$, here to height $n - m$. The trajectory of $k$ reaches height $d$ at $[c_{m, m+d}k, 0]_{m+d}$ ⟦Homotopy/Telescope · traj_self⟧, by induction on $d$. For $d = 0$ this is the starting point ⟦Appendix/MappingTelescope · MappingTelescope.traj_zero_right⟧. For $d = 1$ it is the top $[k, 1]_m = [c_mk, 0]_{m+1}$ of the block. For $d \ge 2$ the trajectory steps into the next block and continues from $c_mk$, and $c_{m+1, m+d}\,c_m = c_{m, m+d}$. $\square$

**Lemma.** The corestriction $K_0 \to \operatorname{Tel}^n(K)$ of $\kappa$ is homotopic, as a map into $\operatorname{Tel}^n(K)$, to $\kappa_n \circ c_{0,n}$. ⟦Homotopy/Telescope · homotopic_corestrict_telescopeIncl⟧

*Proof.* The homotopy is $(s, k) \mapsto \operatorname{push}_n(s, [k, 0]_0)$. It stays in $\operatorname{Tel}^n(K)$ ⟦Appendix/MappingTelescope · MappingTelescope.push_mem_trunc⟧, starts at $[k, 0]_0$ ⟦Appendix/MappingTelescope · MappingTelescope.push_zero⟧, and ends at $[c_{0,n}k, 0]_n$ by the previous lemma. $\square$

This homotopy moves the basepoint: $[x_0, 0]_0$ travels up to $[c_{0,n}x_0, 0]_n$. It is a free homotopy, and the comparison of the induced maps goes through the change of basepoint of §XII.4.

**Theorem (mapping telescopes).** Let $N$ be finite. If every composite $c_{0,n} : K_0 \to K_n$ is bijective (onto) on $\pi_N$ at $x_0$, so is $\kappa : K_0 \to \operatorname{Tel}(K)$. ⟦Homotopy/Telescope · bijective_homotopyGroupMap_telescopeIncl⟧ ⟦Homotopy/Telescope · surjective_homotopyGroupMap_telescopeIncl⟧

*The proof as formalized.*

1. Every compact subset of $\operatorname{Tel}(K)$ lies in a truncation: the continuous level is bounded on it ⟦Mathlib/Topology/Order/Compact · IsCompact.bddAbove_image⟧, say by $n$.
2. By the compactness theorem of §XII.9 it suffices that each corestriction $K_0 \to \operatorname{Tel}^n(K)$ is bijective (onto) at $x_0$.
3. That map is freely homotopic to $\kappa_n \circ c_{0,n}$, so the two are bijective (onto) together (§XII.4).
4. $\kappa_n$ is a homotopy equivalence, so $(\kappa_n)_*$ is bijective at $c_{0,n}(x_0)$ (§XII.4), and $(\kappa_n \circ c_{0,n})_* = (\kappa_n)_* \circ (c_{0,n})_*$ is bijective (onto) by hypothesis. $\square$

If every step $c_n : K_n \to K_{n+1}$ is bijective (onto) on $\pi_N$ at every basepoint, so is every composite $c_{0,n}$, by induction, since $c_{0,n+1} = c_n \circ c_{0,n}$ ⟦Homotopy/Telescope · bijective_homotopyGroupMap_tmap_of_step⟧ ⟦Homotopy/Telescope · surjective_homotopyGroupMap_tmap_of_step⟧.

**Theorem (countable cell complexes).** Let $T$ be a cell tower ⟦Appendix/MonotoneUnion · CellTower⟧: $K_0$ is an iterated adjunction space and each $K_{n+1}$ is obtained from $K_n$ by attaching finitely many cells, the map $K_n \to K_{n+1}$ being the composite inclusion (Part IX, §IX.4). If every cell attached after $K_0$ has dimension $\ge |N| + 2$ (resp. $> |N|$), then the inclusion $\kappa : K_0 \to \operatorname{Tel}(K)$ is bijective (onto) on $\pi_N$ at every basepoint. ⟦Homotopy/Telescope · bijective_homotopyGroupMap_of_cellTower⟧ ⟦Homotopy/Telescope · surjective_homotopyGroupMap_of_cellTower⟧

*Proof.* Each step is a relative cell attachment with cells of the required dimension, hence bijective (onto) at every basepoint by the theorem on finitely many cells (§XII.8). So are the composites, and then $\kappa$ by the previous theorem. $\square$

Milnor's statement concerns a countable CW-complex $K = \bigcup K_i$ with the weak topology. The mapping telescope stands for it, as everywhere in the project; the comparison of the two is Example 2 of the Appendix, which rests on Whitehead's theorem and is not formalized (Part XI, §§XI.14–11.15).

### XII.11 Relative cell complexes: the form of Theorem 22.1

Recall from Part IX (§IX.2) that $\iota : A \to X$ *has the homotopy type of the inclusion of $A$ with cells $(c_1, \dots, c_k)$ attached* if there are a relative cell attachment $j : A \to K$ with these cells and a homotopy equivalence $e : X \to K$ with $e \circ \iota \simeq j$ ⟦Chapter10/RelativeCells · IsRelCellComplexType⟧. This is the form in which the relative Theorem 3.5 describes a step $M^{a_n} \subseteq M^{a_{n+1}}$ of a filtration by sublevel sets.

**Theorem (relative cell complexes, finitely many cells).** Let $A$ and $X$ be spaces and suppose $\iota : A \to X$ has the homotopy type of the inclusion of $A$ with cells $(c_1, \dots, c_k)$ attached. If all $c_i \ge |N| + 2$ (resp. $> |N|$), then $\iota_* : \pi_N(A, a) \to \pi_N(X, \iota(a))$ is bijective (onto) for every $a \in A$. ⟦Homotopy/RelCells · bijective_homotopyGroupMap_of_isRelCellComplexType⟧ ⟦Homotopy/RelCells · surjective_homotopyGroupMap_of_isRelCellComplexType⟧

*Proof.* Take the data $j : A \to K$ and $e : X \to K$. The square with the identity of $A$ on the left, $e \circ \iota \simeq j \circ \mathrm{id}_A$, is a homotopy-commutative square of homotopy equivalences, so $\iota_*$ is bijective at $a$ if and only if $j_*$ is (§XII.4). $j_*$ is bijective by the theorem on finitely many cells (§XII.8). $\square$

**Theorem (countably many cells).** Let $B_0 \subseteq B_1 \subseteq \cdots \subseteq X$ be such that every compact subset of $X$ lies in some $B_n$, and suppose each inclusion $B_n \to B_{n+1}$ ⟦Chapter10/RelativeCells · inclC⟧ has the homotopy type of a relative cell complex with cells of dimension $\ge |N| + 2$ (resp. $> |N|$). Then $B_0 \to X$ is bijective (onto) on $\pi_N$ at every basepoint. ⟦Homotopy/RelCells · bijective_homotopyGroupMap_of_seq⟧ ⟦Homotopy/RelCells · surjective_homotopyGroupMap_of_seq⟧

*Proof.* Each step is bijective (onto) at every basepoint by the previous theorem; the theorem on increasing unions (§XII.9) finishes. $\square$

Sublevel sets satisfy the compactness hypothesis: if $E : X \to \mathbb R$ is continuous and $a_n \to \infty$, every compact $K \subseteq X$ lies in some $\{E \le a_n\}$, because $E$ is bounded on $K$ ⟦Homotopy/RelCells · exists_subset_sublevel⟧.

**Theorem (the setting of Theorem 22.1).** Let $E : X \to \mathbb R$ be continuous and $a_0 \le a_1 \le \cdots$ a sequence tending to $\infty$. Suppose each inclusion $X^{a_n} \to X^{a_{n+1}}$ of sublevel sets (§0.4) ⟦Chapter2/Crossing · sublevel⟧ ⟦Chapter2/Crossing · sublevel_mono⟧ has the homotopy type of a relative cell complex with cells of dimension $\ge |N| + 2$ (resp. $> |N|$). Then $X^{a_0} \to X$ is bijective (onto) on $\pi_N$ at every basepoint. ⟦Homotopy/RelCells · bijective_homotopyGroupMap_sublevel⟧ ⟦Homotopy/RelCells · surjective_homotopyGroupMap_sublevel⟧

With $X = \Omega$, $E$ the energy, $a_0 = d$ and all cells of dimension $\ge \lambda_0$, this is the conclusion Milnor draws on p. 118: $\pi_i\Omega^d \to \pi_i\Omega$ is bijective for $i \le \lambda_0 - 2$. It is also onto for $i = \lambda_0 - 1$, which Milnor does not state and the retelling (`Exposition/Chapter13.md`) records beside his statement. The hypothesis, a relative cell structure on every step of the energy filtration with cells of dimension at least $\lambda_0$, is the geometric content of Theorem 22.1. Providing it for $\Omega$ is not part of this library, which supplies the step from cells to homotopy groups.

**Theorem (countable complexes up to homotopy).** Let $T$ be a cell tower whose cells attached after $K_0$ have dimension $\ge |N| + 2$ (resp. $> |N|$). Let $\iota : A \to Z$ be a map, and $a : A \to K_0$ and $e : Z \to \operatorname{Tel}(K)$ homotopy equivalences with $e \circ \iota \simeq \kappa \circ a$. Then $\iota_*$ is bijective (onto) on $\pi_N$ at every basepoint. ⟦Homotopy/RelCells · bijective_homotopyGroupMap_of_telescope⟧ ⟦Homotopy/RelCells · surjective_homotopyGroupMap_of_telescope⟧

*Proof.* Transfer along the square (§XII.4), and apply the theorem on countable cell complexes (§XII.10). $\square$

This is the form that matches the conclusion of Theorem 17.3 as formalized, where a space is homotopy equivalent to the mapping telescope of a cell tower ⟦Appendix/MonotoneUnion · IsCountableCellComplexType⟧.

### XII.12 Loop spaces and path spaces

*Reindexing.* A bijection $e : M \to N$ identifies $I^M$ with $I^N$, and carries generalized loops on $I^M$ to generalized loops on $I^N$ ⟦Mathlib/Topology/Homotopy/HomotopyGroup · GenLoop.congr⟧. It carries homotopies relative to the boundary to such homotopies, because a point of $I^N$ with a boundary coordinate $n$ corresponds to a point of $I^M$ with the boundary coordinate $e^{-1}(n)$ ⟦Homotopy/LoopSpace · genLoop_homotopic_congr⟧, and reindexing back undoes it ⟦Homotopy/LoopSpace · genLoop_congr_symm_congr⟧. So $\pi_M(X, x) \cong \pi_N(X, x)$ ⟦Homotopy/LoopSpace · homotopyGroupCongr⟧. Concatenation along $m$ becomes concatenation along $e(m)$ ⟦Homotopy/LoopSpace · genLoop_congr_transAt⟧, so for nonempty $M$ this is an isomorphism of groups ⟦Homotopy/LoopSpace · homotopyGroupCongrMulEquiv⟧.

*The loop space.* $\Omega X$ is the space of loops at $x$, Mathlib's paths from $x$ to $x$ with the compact-open topology ⟦Mathlib/Topology/Homotopy/HomotopyGroup · LoopSpace⟧, based at the constant loop ⟦Mathlib/Topology/Path · Path.refl⟧. A generalized loop $\gamma$ on $I^M$ in $\Omega X$ assigns to each $z \in I^M$ a loop $\gamma(z)$ at $x$, the constant loop when $z \in \partial I^M$.

*Uncurrying.* Put $\hat\gamma(t, z) = \gamma(z)(t)$ on $I^{M^+}$ ⟦Homotopy/LoopSpace · loopUncurry⟧. It is continuous because evaluation of paths is, and it is a generalized loop at $x$: for $t \in \{0, 1\}$ the value is an end point of a loop at $x$, and for $z \in \partial I^M$ the loop $\gamma(z)$ is constant. Conversely, a generalized loop $\beta$ on $I^{M^+}$ gives for each $z$ the loop $t \mapsto \beta(t, z)$ ⟦Homotopy/LoopSpace · loopCurryPath⟧. These loops depend continuously on $z$, because a family of paths is continuous exactly when the map of two variables is ⟦Homotopy/LoopSpace · continuous_loopCurryPath⟧ ⟦Mathlib/Topology/Path · Path.continuous_uncurry_iff⟧, and they are constant for $z \in \partial I^M$; this is a generalized loop in $\Omega X$ ⟦Homotopy/LoopSpace · loopCurry⟧. The two constructions are inverse ⟦Homotopy/LoopSpace · loopCurry_loopUncurry⟧ ⟦Homotopy/LoopSpace · loopUncurry_loopCurry⟧. The same uncurrying, applied to a homotopy $F(s, z)$ relative to $\partial I^M$, gives the homotopy $(s, (t, z)) \mapsto F(s, z)(t)$ relative to $\partial I^{M^+}$, and conversely ⟦Homotopy/LoopSpace · loopUncurry_homotopic⟧ ⟦Homotopy/LoopSpace · loopCurry_homotopic⟧.

**Theorem.** For every index set $M$, uncurrying is a bijection $\pi_M(\Omega X, \text{const}) \cong \pi_{M^+}(X, x)$. In particular $\pi_i(\Omega X) \cong \pi_{i+1}(X)$ for every $i \ge 0$. ⟦Homotopy/LoopSpace · homotopyGroupLoopEquiv⟧ ⟦Homotopy/LoopSpace · homotopyGroupPiLoopEquiv⟧

The second statement reindexes $\{0, \dots, i\}$ as $\{0, \dots, i-1\}^+$ ⟦Mathlib/Logic/Equiv/Fin/Basic · finSuccEquiv⟧.

**Theorem (as groups).** For nonempty $M$ the bijection is an isomorphism of groups; in particular $\pi_{i+1}(\Omega X) \cong \pi_{i+2}(X)$ as groups. ⟦Homotopy/LoopSpace · homotopyGroupLoopMulEquiv⟧ ⟦Homotopy/LoopSpace · homotopyGroupPiLoopMulEquiv⟧

*Proof.* Uncurrying carries concatenation along a coordinate $m \in M$ of the family of loops to concatenation along the same coordinate $m$ of $I^{M^+}$, because changing the coordinate $m$ of $(t, z)$ does not touch $t$ ⟦Homotopy/LoopSpace · update_some_comp⟧ ⟦Homotopy/LoopSpace · loopUncurry_transAt⟧. By Mathlib's description of products, $[p]\cdot[q] = [\operatorname{trans}_m(q, p)]$ on both sides, so products correspond. $\square$

*Path spaces.* Milnor's $\Omega(M; p, q)$ has two different end points, and §§21–24 pass freely between it and the loop space (`Exposition/Findings.md` records that the proof of Theorem 21.7 treats $\Omega(G; p, q)$ and needs a lemma to change the end points). The formal statement is a homotopy equivalence, and it needs a homotopy that depends continuously on the path.

**Lemma (cancelling a path, continuously).** For a path $\omega$ from $b$ to $c$, the map $\gamma \mapsto (\gamma\cdot\omega)\cdot\omega^{-1}$ of the space of paths from $a$ to $b$ to itself is homotopic to the identity. ⟦Homotopy/LoopSpace · homotopic_trans_trans_symm⟧

*The proof as formalized.* At time $s$, with $u(s) = (1 + 3s)/4$, let
$$\theta_s(\gamma)(t) = \begin{cases} \gamma\big(t/u(s)\big) & t \le u(s), \\ \omega\big(\min(4(t - u(s)),\ 2 - 2t)\big) & t \ge u(s). \end{cases}$$
⟦Homotopy/LoopSpace · cancelFamily⟧ It runs through $\gamma$ on $[0, u(s)]$, then out along $\omega$ and back to its start. The two formulas agree at $t = u(s)$, both giving $b$, and $\theta_s(\gamma)$ ends at $b$: for $u(s) < 1$ the second formula gives $\omega(\min(4(1 - u(s)), 0)) = \omega(0)$. The map $(s, \gamma) \mapsto \theta_s(\gamma)$ is continuous ⟦Homotopy/LoopSpace · continuous_cancelFamily⟧. At $s = 1$, $u = 1$ and $\theta_1(\gamma) = \gamma$ ⟦Homotopy/LoopSpace · cancelFamily_one⟧. At $s = 0$, $u = \frac14$, and $\theta_0(\gamma)$ is $\gamma(4t)$ on $[0, \frac14]$, $\omega(4t - 1)$ on $[\frac14, \frac12]$ (the minimum is $4t - 1 \le 1 \le 2 - 2t$ there), and $\omega(2 - 2t)$ on $[\frac12, 1]$. This is $(\gamma\cdot\omega)\cdot\omega^{-1}$, since Mathlib's concatenation runs its first path at double speed ⟦Homotopy/LoopSpace · cancelFamily_zero⟧. $\square$

**Theorem (changing the end point).** For a path $\omega$ from $b$ to $c$, $\gamma \mapsto \gamma\cdot\omega$ is a homotopy equivalence from the space of paths from $a$ to $b$ to the space of paths from $a$ to $c$, with homotopy inverse $\delta \mapsto \delta\cdot\omega^{-1}$. If $X$ is path-connected, the space of paths from $p$ to $q$ is homotopy equivalent to the loop space at $p$. ⟦Homotopy/LoopSpace · pathTransHomotopyEquiv⟧ ⟦Homotopy/LoopSpace · pathHomotopyEquivLoop⟧

*Proof.* One composite is the lemma for $\omega$, the other the lemma for $\omega^{-1}$, as $(\omega^{-1})^{-1} = \omega$. For path-connected $X$ take for $\omega$ a chosen path from $q$ to $p$ ⟦Mathlib/Topology/Connected/PathConnected · PathConnectedSpace.somePath⟧. $\square$

With §XII.4, the homotopy groups of $\Omega(X; p, q)$ at a path $\gamma$ are those of the loop space at the loop $\gamma\cdot\omega$; at the constant loop, the loop space has the homotopy groups of $X$ shifted by one degree. These are the pieces from which Milnor's identification $\pi_i\Omega(M; p, q) \cong \pi_{i+1}M$ (p. 118, and throughout §§23–24) is assembled. Note that the shift is stated at the constant loop only; the formal text says nothing about the other path components of $\Omega X$ beyond what change of basepoint gives inside a component.

### XII.13 Locally trivial maps and Serre fibrations

In §§23–24 Milnor quotes the exact homotopy sequence of a fibre bundle from Steenrod. The formal text sets up the two notions it rests on, local triviality and the homotopy lifting property, and then proves the sequence (§§XII.15–12.17).

**Definition (local triviality).** Let $p : E \to B$ be any function and $F$ a space. $p$ is *locally trivial with fibre $F$* if every $b \in B$ has an open neighbourhood $U$ with a homeomorphism $\varphi : p^{-1}(U) \to U \times F$ whose first component is $p$ ⟦Homotopy/Fibration · IsLocallyTrivial⟧.

Mathlib's fibre bundles are a structure on a total space assembled from the fibres ⟦Mathlib/Topology/FiberBundle/Basic · FiberBundle⟧. Here local triviality is a property of a given map, so that it applies directly to maps between spaces constructed independently, such as a unitary group mapping onto a sphere (Part XIII). Continuity of $p$ is not part of the definition, because the lifting argument uses only the homeomorphisms over the sets $U$.

The definition is checked in the expected cases and is invariant in the expected ways. A map covered by Mathlib's local trivializations is locally trivial ⟦Homotopy/Fibration · isLocallyTrivial_of_trivializations⟧ ⟦Mathlib/Topology/FiberBundle/Trivialization · Trivialization⟧. In particular the projection of a Mathlib fibre bundle is ⟦Homotopy/Fibration · isLocallyTrivial_proj⟧, and so is the projection $B \times F \to B$, with $U = B$ ⟦Homotopy/Fibration · isLocallyTrivial_fst⟧. If $p$ is locally trivial and $h : E' \to E$ is a homeomorphism, $p \circ h$ is locally trivial, with the trivializations restricted along $h$ ⟦Homotopy/Fibration · IsLocallyTrivial.comp_homeomorph⟧. A homeomorphism of the fibre changes nothing ⟦Homotopy/Fibration · IsLocallyTrivial.congr_fiber⟧.

*The fibres.* A point of the fibre $p^{-1}(b)$ lies in $p^{-1}(U)$ for any $U \ni b$ ⟦Homotopy/Fibration · mem_preimage_of_mem_fiber⟧, and a trivialization over $U$ gives a homeomorphism $p^{-1}(b) \to F$: $x \mapsto \operatorname{pr}_F\varphi(x)$, with inverse $f \mapsto \varphi^{-1}(b, f)$ ⟦Homotopy/Fibration · fiberHomeomorphOfTriv⟧. So every fibre of a locally trivial map is homeomorphic to $F$ ⟦Homotopy/Fibration · IsLocallyTrivial.nonempty_fiberHomeomorph⟧ ⟦Homotopy/Fibration · IsLocallyTrivial.fiberHomeomorph⟧.

**Definition (the open box).** $J^N = I^N \times \{0\} \cup \partial I^N \times I \subseteq I^N \times I$ ⟦Homotopy/Fibration · openBox⟧ ⟦Homotopy/Fibration · mem_openBox⟧ ⟦Homotopy/Fibration · mk_zero_mem_openBox⟧ ⟦Homotopy/Fibration · mk_mem_openBox_of_mem_boundary⟧, the boundary of the cylinder without its top face (Hatcher's notation).

**Definition (Serre fibrations).** $p : E \to B$ is a *Serre fibration* if for every $n$, every map $H : I^n \times I \to B$ and every $g : I^n \times I \to E$ that is continuous on $J^n$ with $p \circ g = H$ on $J^n$, there is a map $G : I^n \times I \to E$ with $p \circ G = H$ everywhere and $G = g$ on $J^n$ ⟦Homotopy/Fibration · IsSerreFibration⟧.

This is the homotopy lifting property for cubes in its *relative* form: the lift is prescribed on the whole open box, not only on the bottom. That is the form the boundary map needs, since it lifts a cube relative to the part of its boundary that goes to the basepoint (§XII.15). In the uses, $g$ is given by a formula on the whole cylinder that is right only on $J^n$, which is why only continuity on $J^n$ and agreement with $H$ there are asked.

The definition quantifies over the cubes $I^n$, $n \in \mathbb N$, so that it stays in one universe. It extends to cubes indexed by any finite set $N$ ⟦Homotopy/Fibration · IsSerreFibration.exists_lift⟧: choose a bijection $N \cong \{0, \dots, n-1\}$, reindex the cube by it ⟦Homotopy/Fibration · cubeCongr⟧ ⟦Homotopy/Fibration · cubeCongr_apply⟧, which preserves boundaries ⟦Homotopy/Fibration · cubeCongr_mem_boundary_iff⟧ and hence open boxes, solve the reindexed problem, and reindex back.

**Theorem (the absolute homotopy lifting property).** Let $p$ be a Serre fibration and $N$ finite. Every homotopy $H : I^N \times I \to B$ lifts to $E$ with any prescribed lift $g_0$ of $H(\cdot, 0)$ at time $0$: there is $G$ with $p \circ G = H$ and $G(\cdot, 0) = g_0$. ⟦Homotopy/Fibration · IsSerreFibration.exists_lift_of_bot⟧

*The proof as formalized.* The relative property for $(I^N \times I, J^N)$ gives the absolute one for $(I^N \times I, I^N \times \{0\})$ through a map of pairs with a section.

1. Let $\phi(x, t) = \big(\rho_{1/4}(x),\ t \cdot \operatorname{clamp}(2 - 4d(x))\big)$ ⟦Homotopy/Fibration · boxFold⟧ ⟦Homotopy/Fibration · continuous_boxFold⟧, with $\rho$ and $d$ as in §XII.3. The cube of radius $\frac14$ about the centre is stretched onto $I^N$, and time is scaled by a factor that is $1$ on that cube and $0$ on $\partial I^N$. So $\phi$ maps $J^N$ into $I^N \times \{0\}$ ⟦Homotopy/Fibration · boxFold_snd_of_mem_openBox⟧.
2. Let $\psi(x, t) = (\frac x2 + \frac14, t)$, shrinking the cube by half about its centre ⟦Homotopy/Fibration · cubeShrink⟧ ⟦Homotopy/Fibration · continuous_cubeShrink⟧. Then $d(\frac x2 + \frac14) = d(x)/2 \le \frac14$ ⟦Homotopy/Fibration · cubeDist_cubeShrink⟧, so $\rho_{1/4}(\frac x2 + \frac14) = x$ ⟦Homotopy/Fibration · cubeScale_cubeShrink⟧ and the time factor is $\operatorname{clamp}(2 - 2d(x)) = 1$. Hence $\phi \circ \psi = \mathrm{id}$ ⟦Homotopy/Fibration · boxFold_shrink⟧.
3. Lift $H \circ \phi$ relative to $J^N$ with the prescribed values $g(z) = g_0(\phi(z)_1)$, the first component. On $J^N$, $\phi(z) = (\phi(z)_1, 0)$, so $p(g(z)) = H(\phi(z)_1, 0) = H(\phi(z))$. Let $G'$ be the lift.
4. $G = G' \circ \psi$ lifts $H$, since $p \circ G' \circ \psi = H \circ \phi \circ \psi = H$. At time $0$, $\psi(x, 0)$ lies on the bottom of $J^N$, so $G(x, 0) = g(\psi(x, 0)) = g_0(x)$. $\square$

### XII.14 Homotopy lifting for locally trivial maps

**Theorem (Hatcher, Proposition 4.48).** A locally trivial map is a Serre fibration. In particular the projection of a Mathlib fibre bundle is a Serre fibration. ⟦Homotopy/HomotopyLifting · IsLocallyTrivial.isSerreFibration⟧ ⟦Homotopy/HomotopyLifting · isSerreFibration_proj⟧

The proof subdivides the cylinder into small boxes, each mapped into a set over which $p$ is trivial, and lifts box by box. Two things need care, and the textbook passes over both: the order in which the boxes are lifted, and the shape of the part of each box where the lift is already known. The formal proof first puts the time coordinate on the same footing as the others, so that one statement about cubes covers every stage.

*The statement proved.* Identify $I^n \times I$ with the cube $I^{N^+}$ for $N = \{0, \dots, n-1\}$, time becoming the coordinate $\star$ ⟦Homotopy/HomotopyLifting · optionCubeHomeo⟧. For a finite $N$ and $D \subseteq N$, let $\mathcal F_D \subseteq I^N$ be the union of the faces $\{w_c = 0\}$ for all $c \in N$ and the faces $\{w_c = 1\}$ for $c \in D$ ⟦Homotopy/HomotopyLifting · cubeFaces⟧, a closed set ⟦Homotopy/HomotopyLifting · isClosed_cubeFaces⟧. Under the identification, the open box $J^n$ is exactly $\mathcal F_D$ for $D = \{c \ne \star\}$ ⟦Homotopy/HomotopyLifting · optionCubeHomeo_mem_cubeFaces_iff⟧: the bottom is the face $\{w_\star = 0\}$, and the sides are the faces $\{w_c = 0\}$ and $\{w_c = 1\}$ for $c \ne \star$.

**Theorem (lifting relative to faces).** Let $p : E \to B$ be locally trivial with fibre $F$, $N$ finite, and $D \subseteq N$ with some $c_0 \notin D$. Let $H : I^N \to B$ be a map and $g$ a lift of $H$ given and continuous on $\mathcal F_D$. Then there is a map $G : I^N \to E$ with $p \circ G = H$ and $G = g$ on $\mathcal F_D$. ⟦Homotopy/HomotopyLifting · IsLocallyTrivial.exists_lift_cubeFaces⟧

The coordinate $c_0 \notin D$ is needed. For $D = N$ the faces form the whole boundary of the cube; with $B$ a point and $E$ that boundary, the statement would make the boundary a retract of the cube. (This remark is not formalized.) Applied with $c_0 = \star$, the theorem is the Serre property ⟦Homotopy/HomotopyLifting · IsLocallyTrivial.isSerreFibration⟧.

*The retraction onto faces.* For $u \in I^N$ and $c \in N$ put
$$\tau_c(u) = \begin{cases} 4\,|u_c - \frac12| & c \in D, \\ 2 - u_c & c \notin D, \end{cases} \qquad M(u) = \max_c \tau_c(u)$$
⟦Homotopy/HomotopyLifting · faceWeight⟧ ⟦Homotopy/HomotopyLifting · faceWeight_of_mem⟧ ⟦Homotopy/HomotopyLifting · faceWeight_of_notMem⟧ ⟦Homotopy/HomotopyLifting · faceMax⟧. Each weight lies in $[0, 2]$ and depends continuously on $u$ ⟦Homotopy/HomotopyLifting · faceWeight_nonneg⟧ ⟦Homotopy/HomotopyLifting · faceWeight_le_two⟧ ⟦Homotopy/HomotopyLifting · continuous_faceWeight⟧. $M$ is the sup norm of the vector of weights, so it is continuous, bounds every weight and is attained ⟦Homotopy/HomotopyLifting · continuous_faceMax⟧ ⟦Homotopy/HomotopyLifting · faceWeight_le_faceMax⟧ ⟦Homotopy/HomotopyLifting · exists_faceWeight_eq_faceMax⟧, and $M \le 2$ ⟦Homotopy/HomotopyLifting · faceMax_le_two⟧. Because $c_0 \notin D$, $M(u) \ge \tau_{c_0}(u) = 2 - u_{c_0} \ge 1$ ⟦Homotopy/HomotopyLifting · one_le_faceMax⟧. On $\mathcal F_D$, $M = 2$: a coordinate with $u_c = 0$ has weight $2$ in both cases, and one with $c \in D$, $u_c = 1$ has weight $4 \cdot \frac12 = 2$ ⟦Homotopy/HomotopyLifting · faceMax_of_mem⟧. Let $P$ be the point with $P_c = \frac12$ for $c \in D$ and $P_c = 2$ for $c \notin D$, outside the cube when $D \ne N$, and let
$$r_D(u) = \operatorname{clamp}\Big(P + \frac{2}{M(u)}\,(u - P)\Big),$$
coordinatewise ⟦Homotopy/HomotopyLifting · faceRetract⟧: radial projection from $P$. It is continuous because $M \ge 1$ ⟦Homotopy/HomotopyLifting · continuous_faceRetract⟧.

**Lemma.** $r_D$ maps $I^N$ into $\mathcal F_D$ and is the identity on $\mathcal F_D$. ⟦Homotopy/HomotopyLifting · faceRetract_mem⟧ ⟦Homotopy/HomotopyLifting · faceRetract_of_mem⟧

*Proof.* Choose $c$ with $\tau_c(u) = M(u)$. If $c \in D$, then $|u_c - \frac12| = M/4 > 0$ and $\frac2M(u_c - \frac12) = \pm\frac12$, so the coordinate $c$ of $r_D(u)$ is $\operatorname{clamp}(1) = 1$ or $\operatorname{clamp}(0) = 0$: the point lies on a face $\{w_c = 1\}$ with $c \in D$ or on a face $\{w_c = 0\}$. If $c \notin D$, then $2 - u_c = M$, so $\frac2M(2 - u_c) = 2$ and the coordinate $c$ is $\operatorname{clamp}(2 - 2) = 0$. On $\mathcal F_D$, $M = 2$ and the formula returns $u$. $\square$

*The grid.* For $m \ge 1$ and $\kappa : N \to \{0, \dots, m-1\}$ let $B_\kappa = \prod_c [\kappa_c/m, (\kappa_c + 1)/m]$ ⟦Homotopy/HomotopyLifting · gridBox⟧, a closed box ⟦Homotopy/HomotopyLifting · isClosed_gridBox⟧, parametrized by $e_\kappa(u) = (\kappa + u)/m$ ⟦Homotopy/HomotopyLifting · gridEmb⟧ ⟦Homotopy/HomotopyLifting · coe_gridEmb⟧ ⟦Homotopy/HomotopyLifting · natCast_add_one_le⟧ ⟦Homotopy/HomotopyLifting · continuous_gridEmb⟧ ⟦Homotopy/HomotopyLifting · gridEmb_mem⟧. The inverse on the box is $e_\kappa^{-1}(w) = \operatorname{clamp}(mw - \kappa)$ ⟦Homotopy/HomotopyLifting · gridCoord⟧ ⟦Homotopy/HomotopyLifting · continuous_gridCoord⟧ ⟦Homotopy/HomotopyLifting · coe_gridCoord_of_mem⟧ ⟦Homotopy/HomotopyLifting · gridEmb_gridCoord⟧ ⟦Homotopy/HomotopyLifting · gridCoord_gridEmb⟧. Every point $w$ lies in a box, with $\kappa_c = \min(m - 1, \lfloor m w_c \rfloor)$ ⟦Homotopy/HomotopyLifting · exists_mem_gridBox⟧.

**Lemma (subdivision).** For every open cover of $I^N$ there is $m \ge 1$ such that every box of the grid of mesh $\frac1m$ lies in a member of the cover. ⟦Homotopy/HomotopyLifting · exists_gridBox_subset⟧

*Proof.* The cube is compact; let $\delta$ be a Lebesgue number of the cover for the sup metric ⟦Mathlib/Topology/MetricSpace/Pseudo/Lemmas · lebesgue_number_lemma_of_metric⟧, and $m$ with $\frac1m < \delta$. Every point of $B_\kappa$ is within $\frac1m$ of the corner $e_\kappa(0)$ in every coordinate, so $B_\kappa$ lies in the ball of radius $\delta$ about that corner, hence in a member of the cover. $\square$

*Lifting over one box.* Let $\varphi : p^{-1}(U) \to U \times F$ be a trivialization over $U$. Moving a point $x \in p^{-1}(U)$ into the fibre over $b \in U$ while keeping its $F$-coordinate gives
$$\mu_b(x) = \varphi^{-1}\big(b, \operatorname{pr}_F\varphi(x)\big)$$
⟦Homotopy/HomotopyLifting · fiberMove⟧. It lies over $b$ ⟦Homotopy/HomotopyLifting · fiberMove_proj⟧, is $x$ itself when $b = p(x)$ ⟦Homotopy/HomotopyLifting · fiberMove_self⟧, and depends continuously on $(b, x)$ ⟦Homotopy/HomotopyLifting · continuous_fiberMove⟧.

**Lemma (one box).** Let $\varphi : p^{-1}(U) \to U \times F$ be a trivialization, $H : I^N \to B$ with $H(B_\kappa) \subseteq U$, and $A \subseteq I^N$ closed. Suppose that $A$ meets the box exactly in the image of a set of faces: $e_\kappa^{-1}(w) \in \mathcal F_{D'}$ for $w \in B_\kappa \cap A$, and $e_\kappa(\mathcal F_{D'}) \subseteq A$, for some $D'$ missing a coordinate $c_0$. Let $G'$ be continuous on $A$ with $p \circ G' = H$ on $A$. Then $G'$ extends to $G$, continuous on $A \cup B_\kappa$, with $p \circ G = H$ there. ⟦Homotopy/HomotopyLifting · exists_lift_union_gridBox⟧

*The proof as formalized.*

1. *The retraction of the box.* $r(w) = e_\kappa\big(r_{D'}(e_\kappa^{-1}(w))\big)$ is continuous, takes values in $A$ (they lie in $e_\kappa(\mathcal F_{D'})$) and in $B_\kappa$, and is the identity on $B_\kappa \cap A$, by the lemma on $r_{D'}$ and $e_\kappa e_\kappa^{-1} = \mathrm{id}$ on the box.
2. *A continuous candidate.* $G' \circ r$ is continuous on the whole cube, $G'$ being continuous on $A$, and its values lie over $H(r(w)) \in U$, so in $p^{-1}(U)$.
3. *The new lift.* On the box put $L(w) = \mu_{H(w)}\big(G'(r(w))\big)$: the point of $G'(r(w))$'s $F$-coordinate in the fibre over $H(w)$. It is continuous and lies over $H(w)$. On $B_\kappa \cap A$, $r(w) = w$ and $p(G'(w)) = H(w)$, so $L(w) = \mu_{p(G'(w))}(G'(w)) = G'(w)$.
4. *Pasting.* Let $G = L$ on $B_\kappa$ and $G = G'$ elsewhere. By step 3, $G = G'$ on $A$. So $G$ is continuous on the closed set $A$ and on the closed set $B_\kappa$, hence on their union ⟦Mathlib/Topology/ContinuousOn · ContinuousOn.union_of_isClosed⟧, and it lifts $H$ on both. $\square$

*The order of the boxes.* After the boxes with indices in a finite set $S$ have been lifted, the lift is known on
$$\Lambda(S) = \mathcal F_D \cup \bigcup_{\kappa \in S} B_\kappa$$
⟦Homotopy/HomotopyLifting · liftedPart⟧, a closed set ⟦Homotopy/HomotopyLifting · isClosed_liftedPart⟧, and $\Lambda(S) = \Lambda(S \setminus \{\kappa\}) \cup B_\kappa$ for $\kappa \in S$ ⟦Homotopy/HomotopyLifting · liftedPart_insert⟧. The boxes are added along the pointwise order of the indices, so that $S$ is always a *lower set*: with $\kappa$, it contains every $\kappa' \le \kappa$. When the box $B_\kappa$ is added, $\kappa$ maximal in $S$, the prescribed part of the box consists of its lower faces and of those upper faces that lie on the top faces $\{w_c = 1\}$, $c \in D$, of the cube. In the coordinates of the box these are the faces $\mathcal F_{D'}$ with
$$D' = \{c \in D : \kappa_c = m - 1\}$$
⟦Homotopy/HomotopyLifting · upperFaces⟧, which misses $c_0$ because $D$ does. Two lemmas make this precise.

**Lemma (the known part of the new box).** Let $\kappa$ be maximal in $S$ and $w \in B_\kappa \cap \Lambda(S \setminus \{\kappa\})$. Then $e_\kappa^{-1}(w) \in \mathcal F_{D'}$. ⟦Homotopy/HomotopyLifting · gridCoord_mem_cubeFaces⟧

*Proof.* If $w$ lies on a face of $\mathcal F_D$ with $w_c = 0$, then $\kappa_c = 0$, since $w \in B_\kappa$ forces $\kappa_c/m \le 0$; so the coordinate $c$ of $e_\kappa^{-1}(w)$ is $0$. If $w_c = 1$ with $c \in D$, then $(\kappa_c + 1)/m \ge 1$ forces $\kappa_c = m - 1$, so $c \in D'$ and the coordinate is $m - \kappa_c = 1$. If $w \in B_{\kappa'}$ with $\kappa' \in S$, $\kappa' \ne \kappa$, then $\kappa \not\le \kappa'$, for otherwise maximality would give $\kappa' = \kappa$. So $\kappa'_c < \kappa_c$ for some $c$, and $w_c \le (\kappa'_c + 1)/m \le \kappa_c/m \le w_c$: the point lies on the lower face $c$ of $B_\kappa$, where the box coordinate is $0$. $\square$

**Lemma (the prescribed faces are known).** Let $S$ be a lower set and $\kappa \in S$. Then $e_\kappa(\mathcal F_{D'}) \subseteq \Lambda(S \setminus \{\kappa\})$. ⟦Homotopy/HomotopyLifting · gridEmb_mem_of_mem_cubeFaces⟧

*Proof.* Let $u \in \mathcal F_{D'}$ and $w = e_\kappa(u)$. If $u_c = 0$ and $\kappa_c = 0$, then $w_c = 0$ and $w \in \mathcal F_D$. If $u_c = 0$ and $\kappa_c > 0$, let $\kappa'$ be $\kappa$ with $\kappa_c$ lowered by one. Then $\kappa' \le \kappa$, so $\kappa' \in S$ as $S$ is a lower set, and $\kappa' \ne \kappa$; and $w$ lies in $B_{\kappa'}$, its coordinate $c$ being $\kappa_c/m = (\kappa'_c + 1)/m$. If $u_c = 1$ with $c \in D'$, then $w_c = (\kappa_c + 1)/m = 1$ with $c \in D$, so $w \in \mathcal F_D$. $\square$

*Proof of the theorem on lifting relative to faces.*

1. For each $b \in B$ choose an open $U_b \ni b$ with a trivialization. By subdivision there is $m$ such that $H$ maps each box $B_\kappa$ into some $U_{b(\kappa)}$.
2. *Claim:* for every lower set $S$ of indices there is $G$, continuous on $\Lambda(S)$, lifting $H$ there and equal to $g$ on $\mathcal F_D$. The proof is a strong induction on $S$, removing one element at a time ⟦Mathlib/Data/Finset/Card · Finset.eraseInduction⟧.
3. For $S = \emptyset$, $\Lambda(\emptyset) = \mathcal F_D$ and $G = g$.
4. For nonempty $S$ choose a maximal $\kappa \in S$ ⟦Mathlib/Order/Preorder/Finite · Finset.exists_maximal⟧. Then $S \setminus \{\kappa\}$ is again a lower set: if $a \le a'$ with $a' \in S \setminus \{\kappa\}$, then $a \in S$, and $a = \kappa$ would give $\kappa \le a'$, hence $a' = \kappa$ by maximality. The induction hypothesis gives $G'$ on $A = \Lambda(S \setminus \{\kappa\})$. The two lemmas are the hypotheses of the one-box lemma with $D' = \{c \in D : \kappa_c = m - 1\}$, which gives $G$ on $A \cup B_\kappa = \Lambda(S)$. It equals $G' = g$ on $\mathcal F_D \subseteq A$.
5. The set of all indices is a lower set, and $\Lambda$ of it is the whole cube, since every point lies in a box. The resulting $G$ is continuous on $I^N$. $\square$

*Proof that locally trivial maps are Serre fibrations.* Transport the lifting problem on $I^n \times I$ to $I^{N^+}$, $N = \{0, \dots, n-1\}$, by the homeomorphism, which carries $J^n$ onto $\mathcal F_D$ with $D = \{c \ne \star\}$, apply the theorem with $c_0 = \star$, and transport back ⟦Homotopy/HomotopyLifting · IsLocallyTrivial.isSerreFibration⟧. $\square$

The induction along lower sets is what makes the textbook's "lift box by box" correct. In a careless order, a box could be reached after boxes above it in some coordinate, and the part of it where the lift is already known would not be a set of faces onto which the box retracts.

### XII.15 The boundary map

*The setting* of this section and the next two: $p : E \to B$ is a continuous Serre fibration, $e_0 \in E$, and $F = p^{-1}(p(e_0))$ is the fibre through $e_0$, a subspace of $E$ ⟦Homotopy/ExactSequence · fiber⟧, based at $e_0$ ⟦Homotopy/ExactSequence · fiberPt⟧, with inclusion $i : F \to E$ ⟦Homotopy/ExactSequence · fiberIncl⟧ ⟦Homotopy/ExactSequence · fiberIncl_apply⟧ and $p = p(e_0)$ on $F$ ⟦Homotopy/ExactSequence · proj_fiber⟧. $N$ is finite, possibly empty. The group $\pi_{n+1}(B)$ is $\pi_{N^+}(B, p(e_0))$, and its extra coordinate $\star$ is the *time* of the lifting problems. A generalized loop $\alpha$ on $I^{N^+}$ gives the map $(z, t) \mapsto \alpha(t, z)$ of $I^N \times I$ ⟦Homotopy/ExactSequence · cubeOfLoop⟧, which sends the open box $J^N$ to $p(e_0)$, because $(0, z)$ and $(t, z)$ with $z \in \partial I^N$ lie on $\partial I^{N^+}$. Simplification rules for points $(t, z)$ are recorded once ⟦Homotopy/ExactSequence · optionPoint_none⟧ ⟦Homotopy/ExactSequence · optionPoint_some⟧ ⟦Homotopy/ExactSequence · optionTail_optionPoint⟧ ⟦Homotopy/ExactSequence · optionPoint_optionTail⟧ ⟦Homotopy/ExactSequence · update_none_eq_optionPoint⟧ ⟦Homotopy/ExactSequence · update_some_optionPoint⟧, as are the clamps of numbers $\le 0$ and $\ge 1$ ⟦Homotopy/ExactSequence · projIcc_eq_zero⟧ ⟦Homotopy/ExactSequence · projIcc_eq_one⟧.

**Definition (boundary lifts).** A map $G : I^N \times I \to E$ is a *boundary lift* of $\alpha$ if
$$p(G(z, t)) = \alpha(t, z), \qquad G(z, 0) = e_0, \qquad G(z, t) = e_0 \text{ for } z \in \partial I^N$$
⟦Homotopy/ExactSequence · IsBoundaryLift⟧. Its *top face* $z \mapsto G(z, 1)$ lies in $F$, because $\alpha(1, z) = p(e_0)$ ⟦Homotopy/ExactSequence · IsBoundaryLift.mem_fiber⟧, and is $e_0$ on $\partial I^N$. So it is a generalized loop in $F$ at $e_0$ ⟦Homotopy/ExactSequence · topFace⟧ ⟦Homotopy/ExactSequence · coe_topFace⟧.

A generalized loop $\beta$ on $I^{N^+}$ in $E$ at $e_0$, read as the map $(z, t) \mapsto \beta(t, z)$, is a boundary lift of $p \circ \beta$ ⟦Homotopy/ExactSequence · isBoundaryLift_genLoopMap⟧, with constant top face. Boundary lifts always exist ⟦Homotopy/ExactSequence · exists_isBoundaryLift⟧: lift $(z, t) \mapsto \alpha(t, z)$ relative to $J^N$ with the constant $e_0$ prescribed there, which lies over $p(e_0) = \alpha(t, z)$ on $J^N$ ⟦Homotopy/Fibration · IsSerreFibration.exists_lift⟧.

**Theorem (homotopic loops have homotopic boundaries).** Let $\alpha \simeq \alpha'$ relative to $\partial I^{N^+}$, and let $G$, $G'$ be boundary lifts of $\alpha$, $\alpha'$. Then their top faces are homotopic in $F$ relative to $\partial I^N$. ⟦Homotopy/ExactSequence · homotopic_topFace⟧

*The proof as formalized.* Let $K(s, (t, z))$ be the homotopy from $\alpha$ to $\alpha'$; it equals $p(e_0)$ on $\partial I^{N^+}$ for every $s$. Lift it, as one lifting problem on the cube $I^{N^+}$ of the variables $(s, z)$, the homotopy parameter $s$ taking the place of $\star$, times the time $t$:

1. The map to lift is $(s, z, t) \mapsto K(s, (t, z))$.
2. The prescribed lift on the open box is
$$g(s, z, t) = \begin{cases} G\big(z, \operatorname{clamp}(t - 2s)\big) & s \le \frac12, \\ G'\big(z, \operatorname{clamp}(t - 2 + 2s)\big) & s \ge \frac12, \end{cases}$$
continuous because both formulas give $e_0$ at $s = \frac12$, where both clamps vanish.
3. It lies over $K$ on the open box. At $t = 0$ both clamps vanish, so $g = e_0$, over $K(s, (0, z)) = p(e_0)$. At $s = 0$, $g = G(z, t)$, over $\alpha(t, z) = K(0, (t, z))$. At $s = 1$, $g = G'(z, t)$, over $\alpha'(t, z)$. For $z \in \partial I^N$, $g = e_0$ by the side conditions, over $K(s, (t, z)) = p(e_0)$.
4. Let $L$ be the lift. Its top $(s, z) \mapsto L(s, z, 1)$ lies in $F$, since $K(s, (1, z)) = p(e_0)$. On the open box $L = g$, so at $s = 0$ it is $G(z, 1)$, at $s = 1$ it is $G'(z, \operatorname{clamp}(1)) = G'(z, 1)$, and for $z \in \partial I^N$ it is $e_0$. This is the required homotopy of top faces. $\square$

**Definition (the boundary map).** $\partial : \pi_{N^+}(B, p(e_0)) \to \pi_N(F, e_0)$ sends $[\alpha]$ to the class of the top face of a chosen boundary lift of $\alpha$ ⟦Homotopy/ExactSequence · boundaryLoop⟧ ⟦Homotopy/ExactSequence · boundaryMap⟧. By the theorem it is well defined, and $\partial[\alpha]$ is the class of the top face of *any* boundary lift of $\alpha$ ⟦Homotopy/ExactSequence · boundaryMap_mk⟧, the case $\alpha' = \alpha$ ⟦Mathlib/Topology/Homotopy/HomotopyGroup · GenLoop.Homotopic.refl⟧.

Textbook proofs of exactness glue a homotopy of the top face onto a lift and reparametrize the cube. The formal proof does such gluing once, inside a lifting problem, in the following lemma, and never reparametrizes cubes afterwards.

**Lemma (changing the top face).** Let $G$ be a boundary lift of $\alpha$ whose top face is homotopic in $F$, relative to $\partial I^N$, to $\gamma$. Then some boundary lift $G'$ of the same $\alpha$ has top face exactly $\gamma$. ⟦Homotopy/ExactSequence · exists_isBoundaryLift_topFace_eq⟧

*The proof as formalized.* Let $\Gamma$ be the homotopy in $F$ from the top face of $G$ to $\gamma$.

1. *A path for each $z$.* For $r \in \mathbb R$ let $P(z, r) = G(z, \operatorname{clamp} r)$ for $r \le 1$ and $P(z, r) = \Gamma(\operatorname{clamp}(r - 1), z)$ for $r \ge 1$: the path $G(z, \cdot)$ followed by the path $\Gamma(\cdot, z)$ in $F$. It is continuous, since both give $G(z, 1)$ at $r = 1$. It satisfies $P(z, 0) = e_0$; $P(z, r) = e_0$ for $z \in \partial I^N$, because $\Gamma$ is relative to $\partial I^N$; $p(P(z, r)) = \alpha(\operatorname{clamp} r, z)$ for $r \le 1$; and $P(z, r) \in F$ for $r > 1$.
2. *The lifting problem.* On the cube $I^{N^+}$ of the variables $(t, z)$, with a new time $s$, lift the constant homotopy $(t, z, s) \mapsto \alpha(t, z)$, prescribing on the open box $g(t, z, s) = P(z, t(1 + s))$.
3. *It lies over $\alpha$ on the open box.* At $s = 0$, $g = P(z, t) = G(z, t)$, over $\alpha(t, z)$. On $\partial I^{N^+}$, $\alpha = p(e_0)$, and $g$ lies over it: if $t(1+s) > 1$, $P$ is in $F$; otherwise $p(g) = \alpha(\operatorname{clamp}(t(1+s)), z)$, and this is $p(e_0)$ because $t = 0$, or $t = 1$ and then $s = 0$, or $z \in \partial I^N$.
4. *The new lift.* Let $L$ be the lift and $G'(z, t) = L(t, z, 1)$. It lies over $\alpha(t, z)$. On the open box $L = g$, so $G'(z, 0) = P(z, 0) = e_0$, $G'(z, t) = P(z, 2t) = e_0$ for $z \in \partial I^N$, and the top face is $G'(z, 1) = P(z, 2) = \Gamma(1, z) = \gamma(z)$. $\square$

At $s = 1$ the prescribed values run through $G(z, \cdot)$ at double speed and then through the homotopy $\Gamma$: the lift of the constant homotopy of $\alpha$ moves $G$ to a lift that has absorbed $\Gamma$.

### XII.16 Exactness at every place

**Theorem (the exact homotopy sequence).** In the setting of §XII.15, consider
$$\pi_{N^+}(B, p(e_0)) \xrightarrow{\ \partial\ } \pi_N(F, e_0) \xrightarrow{\ i_*\ } \pi_N(E, e_0) \xrightarrow{\ p_*\ } \pi_N(B, p(e_0)).$$
At each of the three middle places the kernel, the preimage of the class of the constant loop, is the image:

- at $\pi_N(F)$: $i_*c = 0$ if and only if $c$ is in the image of $\partial$ ⟦Homotopy/ExactSequence · exact_fiber⟧;
- at $\pi_N(E)$: $p_*c = 0$ if and only if $c$ is in the image of $i_*$ ⟦Homotopy/ExactSequence · exact_total⟧;
- at $\pi_{N^+}(B)$: $\partial c = 0$ if and only if $c$ is in the image of $p_*$ ⟦Homotopy/ExactSequence · exact_base⟧.

As $N$ runs over $\emptyset, \{0\}, \{0, 1\}, \dots$ this is exactness of the whole sequence
$$\cdots \to \pi_{n+1}B \to \pi_nF \to \pi_nE \to \pi_nB \to \pi_{n-1}F \to \cdots \to \pi_0F \to \pi_0E \to \pi_0B,$$
as pointed sets, including its end, $N = \emptyset$, where the terms are sets of path components. This is the sequence Milnor quotes from Steenrod for §§23–24.

*Exactness at the fibre.*

- *An element of the image of $\partial$ dies in $E$.* Let $G$ be a boundary lift of $\alpha$, so $\partial[\alpha]$ is the class of its top face. Run $G$ backwards in time: $(s, z) \mapsto G(z, 1 - s)$ is a homotopy in $E$ from the top face to $G(z, 0) = e_0$, relative to $\partial I^N$, where $G = e_0$ throughout.
- *An element that dies in $E$ is in the image.* Let $\gamma$ be a generalized loop in $F$ and $\Lambda$ a homotopy in $E$, relative to $\partial I^N$, from $i\circ\gamma$ to the constant loop. Put $\alpha(t, z) = p(\Lambda(1 - t, z))$. It is a generalized loop in $B$ at $p(e_0)$: at $t = 0$ it is $p(e_0)$; at $t = 1$ it is $p(\gamma(z)) = p(e_0)$ because $\gamma$ lies in $F$; on $z \in \partial I^N$ it is $p(e_0)$. Then $G(z, t) = \Lambda(1 - t, z)$ is a boundary lift of $\alpha$, by construction, and its top face is $\Lambda(0, z) = \gamma(z)$. So $\partial[\alpha] = [\gamma]$. $\square$

*Exactness at the total space.*

- *The composite is trivial*: $p \circ i$ is constant, so $p_* i_*$ sends everything to the constant class ⟦Homotopy/ExactSequence · homotopyGroupMap_proj_fiberIncl⟧.
- *An element that dies in $B$ comes from $F$.* Let $\beta$ be a generalized loop in $E$ and $\Theta$ a homotopy in $B$, relative to $\partial I^N$, from $p\circ\beta$ to the constant loop. Lift $(z, t) \mapsto \Theta(t, z)$ relative to $J^N$, prescribing $\beta(z)$ there; this lies over $\Theta(0, z) = p(\beta(z))$ at $t = 0$, and over $\Theta(t, z) = p(\beta(z))$ for $z \in \partial I^N$. Let $L$ be the lift. Its top $\gamma(z) = L(z, 1)$ lies in $F$, since $\Theta(1, z) = p(e_0)$, and equals $\beta(z) = e_0$ for $z \in \partial I^N$; so $\gamma$ is a generalized loop in $F$. Running $L$ backwards in time, $(s, z) \mapsto L(z, 1 - s)$ is a homotopy in $E$ from $i\circ\gamma$ to $L(z, 0) = \beta(z)$, relative to $\partial I^N$, where $L = \beta = e_0$. So $[\beta] = i_*[\gamma]$. $\square$

*Exactness at the base.*

- *The composite is trivial.* For a generalized loop $\beta$ in $E$, $\beta$ itself is a boundary lift of $p\circ\beta$, and its top face $\beta(1, z) = e_0$ is constant. So $\partial p_*[\beta] = 0$.
- *An element with trivial boundary comes from $E$.* Let $\partial[\alpha] = 0$, and let $G$ be a boundary lift of $\alpha$. Its top face is homotopic in $F$ to the constant loop, so by the lemma on changing the top face some boundary lift $G'$ of $\alpha$ has constant top face $e_0$. Then $\beta(t, z) = G'(z, t)$ is a generalized loop in $E$ at $e_0$: it is $e_0$ at $t = 0$ (bottom), at $t = 1$ (constant top face) and for $z \in \partial I^N$ (sides). And $p\circ\beta = \alpha$. So $[\alpha] = p_*[\beta]$. $\square$

### XII.17 Homomorphisms, injectivity, and the two forms used in §23

*Induced maps are homomorphisms.* A map $f$ commutes with concatenation along any coordinate, $f \circ \operatorname{trans}_i(\gamma, \gamma') = \operatorname{trans}_i(f\circ\gamma, f\circ\gamma')$, both being given by the same case distinction ⟦Homotopy/ExactSequenceIso · genLoopMap_transAt⟧. So for nonempty $N$, $f_*([\gamma][\gamma']) = f_*[\gamma]\,f_*[\gamma']$ ⟦Homotopy/ExactSequenceIso · homotopyGroupMap_mul⟧, and $f_*$ is a group homomorphism ⟦Homotopy/ExactSequenceIso · homotopyGroupHom⟧.

**Theorem (the boundary map is a homomorphism).** For nonempty $N$, $\partial : \pi_{N^+}(B) \to \pi_N(F)$ is a group homomorphism. ⟦Homotopy/ExactSequenceIso · boundaryMap_mul⟧ ⟦Homotopy/ExactSequenceIso · boundaryHom⟧

*The proof as formalized.* Let $a = [\alpha]$, $b = [\alpha']$, with boundary lifts $G$, $G'$, and choose a coordinate $j \in N$. By Mathlib's description of products, taken along the coordinate $j$ of $N^+$, $ab = [\operatorname{trans}_j(\alpha', \alpha)]$. Put the two lifts side by side in the coordinate $j$:
$$GG(z, t) = \begin{cases} G'\big(z \text{ with } z_j \mapsto 2z_j,\ t\big) & z_j \le \frac12, \\ G\big(z \text{ with } z_j \mapsto 2z_j - 1,\ t\big) & z_j \ge \frac12. \end{cases}$$
At $z_j = \frac12$ both formulas give $e_0$, by the side conditions, so $GG$ is continuous. It is a boundary lift of $\operatorname{trans}_j(\alpha', \alpha)$. It lies over it, since concatenation along $j$ does not touch the time coordinate. It is $e_0$ at $t = 0$. And it is $e_0$ for $z \in \partial I^N$: if the boundary coordinate is $j$, the rescaled point is on the boundary of the corresponding lift; otherwise the rescaled point keeps that boundary coordinate. Its top face is $\operatorname{trans}_j$ of the top faces of $G'$ and $G$, whose class is $\partial a\,\partial b$ by the same description of products. The identity goes to the identity because $\partial$ kills the image of $p_*$, which contains the constant class (§XII.16). $\square$

*Injectivity.* Exactness of pointed sets says only that the kernel is trivial, and in the low degrees, $\partial : \pi_1(B) \to \pi_0(F)$ and $i_* : \pi_0(F) \to \pi_0(E)$, the targets are not groups, so a trivial kernel does not give injectivity. Two arguments valid in every degree supply it.

**Lemma.** If $\partial a = \partial b$, then $b^{-1}a$ lies in the image of $p_* : \pi_{N^+}(E) \to \pi_{N^+}(B)$. ⟦Homotopy/ExactSequenceIso · exists_homotopyGroupMap_eq_inv_mul⟧

This holds for every finite $N$, including $N = \emptyset$, since $\pi_{N^+}$ is always a group.

*The proof as formalized.* Let $a = [\alpha]$ and $b = [\alpha']$ with boundary lifts $G$ and $G_1$. Since $\partial a = \partial b$, the top faces of $G_1$ and $G$ are homotopic in $F$, and the lemma on changing the top face gives a boundary lift $G'$ of $\alpha'$ with the same top face as $G$. Follow $G$ by $G'$ run backwards in time:
$$\beta(t, z) = \begin{cases} G(z, 2t) & t \le \frac12, \\ G'(z, 2 - 2t) & t \ge \frac12. \end{cases}$$
The formulas agree at $t = \frac12$ because the top faces agree, and $\beta$ is $e_0$ at $t = 0$, at $t = 1$ and on $z \in \partial I^N$, so it is a generalized loop in $E$ at $e_0$. Its projection $p \circ \beta$ is, on the nose, $\operatorname{trans}_\star(\alpha, \operatorname{symm}_\star\alpha')$. By Mathlib's conventions this represents $[\operatorname{symm}_\star\alpha']\cdot[\alpha] = b^{-1}a$ ⟦Mathlib/Topology/Homotopy/HomotopyGroup · HomotopyGroup.inv_spec⟧ ⟦Mathlib/Topology/Homotopy/HomotopyGroup · HomotopyGroup.mul_spec⟧. $\square$

Hence, if $\pi_{N^+}(E, e_0)$ is trivial, $\partial$ is one-to-one: $b^{-1}a = p_*(c) = p_*(1) = 1$ ⟦Homotopy/ExactSequenceIso · injective_boundaryMap⟧.

**Theorem.** If $\pi_{N^+}(B, p(e_0))$ is trivial, $i_* : \pi_N(F) \to \pi_N(E)$ is one-to-one. ⟦Homotopy/ExactSequenceIso · injective_homotopyGroupMap_fiberIncl⟧

*The proof as formalized.* Let $\gamma, \gamma'$ be generalized loops in $F$ and $\Lambda$ a homotopy in $E$ from $i\circ\gamma$ to $i\circ\gamma'$ relative to $\partial I^N$.

1. Its projection $\delta(t, z) = p(\Lambda(t, z))$ is a generalized loop on $I^{N^+}$ in $B$ at $p(e_0)$: at $t = 0$ and $t = 1$ it is $p$ of a point of $F$, and on $z \in \partial I^N$ it is $p(e_0)$.
2. $\pi_{N^+}(B)$ is trivial, so there is a homotopy $Q$ from $\delta$ to the constant loop relative to $\partial I^{N^+}$.
3. Lift $(t, z, s) \mapsto Q(s, (t, z))$ on $I^{N^+} \times I$, prescribing $\Lambda(t, z)$ on the open box. It lies over $Q$ there: at $s = 0$, $Q = \delta = p \circ \Lambda$, and on $\partial I^{N^+}$, $Q(s, \cdot) = \delta$.
4. The lift $R$ ends, at $s = 1$, over the constant loop, so $(t, z) \mapsto R(t, z, 1)$ lies in $F$. On $\partial I^{N^+}$ it equals $\Lambda$: at $t = 0$ it is $\gamma(z)$, at $t = 1$ it is $\gamma'(z)$, and for $z \in \partial I^N$ it is $e_0$. So it is a homotopy in $F$ from $\gamma$ to $\gamma'$ relative to $\partial I^N$. $\square$

*Surjectivity and bijectivity.* If $\pi_N(E)$ is trivial, every $c \in \pi_N(F)$ has $i_*c = 0$, so $\partial$ is onto by exactness at the fibre ⟦Homotopy/ExactSequenceIso · surjective_boundaryMap⟧. If $\pi_N(B)$ is trivial, $i_*$ is onto by exactness at the total space ⟦Homotopy/ExactSequenceIso · surjective_homotopyGroupMap_fiberIncl⟧. Together with injectivity:

- $\partial : \pi_{N^+}(B) \to \pi_N(F)$ is bijective when $\pi_{N^+}(E)$ and $\pi_N(E)$ are trivial ⟦Homotopy/ExactSequenceIso · bijective_boundaryMap⟧;
- $i_* : \pi_N(F) \to \pi_N(E)$ is bijective when $\pi_{N^+}(B)$ and $\pi_N(B)$ are trivial ⟦Homotopy/ExactSequenceIso · bijective_homotopyGroupMap_fiberIncl⟧.

*Two out of three.* If two of the groups vanish in the right degrees, so does the third. If $\pi_N(F)$ and $\pi_N(B)$ are trivial, so is $\pi_N(E)$, because $i_*$ is onto ⟦Homotopy/ExactSequenceIso · subsingleton_homotopyGroup_total⟧. If $\pi_{N^+}(E)$ and $\pi_N(F)$ are trivial, so is $\pi_{N^+}(B)$: every $c$ has $\partial c = 0$, so $c = p_*(c')$ with $c'$ the constant class, and $p_*$ preserves it ⟦Homotopy/ExactSequenceIso · subsingleton_homotopyGroup_base⟧. If $\pi_{N^+}(B)$ and $\pi_N(E)$ are trivial, so is $\pi_N(F)$, because $i_*$ is one-to-one ⟦Homotopy/ExactSequenceIso · subsingleton_homotopyGroup_fiber⟧.

*The forms with $\pi_i$.* Reindexing turns $\pi_{\{0, \dots, j-1\}^+}$ into $\pi_{j+1}$, so a vanishing $\pi_{j+1}$ gives a vanishing $\pi_{\{0,\dots,j-1\}^+}$ ⟦Homotopy/ExactSequenceIso · subsingleton_homotopyGroup_option⟧, and the boundary map becomes $\partial : \pi_{j+1}(B, p(e_0)) \to \pi_j(F, e_0)$ ⟦Homotopy/ExactSequenceIso · boundaryMapPi⟧. The two forms that Milnor's §23 uses follow.

**Theorem (a).** If $\pi_i(E, e_0)$ is trivial for all $i \le k$, then $\partial : \pi_{j+1}(B) \to \pi_j(F)$ is bijective for $j + 1 \le k$ and onto for $j \le k$. ⟦Homotopy/ExactSequenceIso · bijective_boundaryMapPi_of_le⟧ ⟦Homotopy/ExactSequenceIso · surjective_boundaryMapPi_of_le⟧ ⟦Homotopy/ExactSequenceIso · boundaryEquivPi⟧

So $\pi_i(B) \cong \pi_{i-1}(F)$ for $1 \le i \le k$, and $\pi_{k+1}(B) \to \pi_k(F)$ is onto. Bijectivity for $j + 1 \le k$ uses the vanishing of $\pi_{j+1}(E)$ and $\pi_j(E)$; surjectivity uses $\pi_j(E)$ only.

**Theorem (b).** If $\pi_i(B, p(e_0))$ is trivial for all $i \le k$, then $i_* : \pi_i(F) \to \pi_i(E)$ is bijective for $i + 1 \le k$ and onto for $i \le k$. ⟦Homotopy/ExactSequenceIso · bijective_homotopyGroupMap_fiberIncl_of_le⟧ ⟦Homotopy/ExactSequenceIso · surjective_homotopyGroupMap_fiberIncl_of_le⟧

The two-out-of-three statements have $\pi_i$ forms as well ⟦Homotopy/ExactSequenceIso · subsingleton_pi_base⟧ ⟦Homotopy/ExactSequenceIso · subsingleton_pi_fiber⟧.

In §23 (pp. 128–129) the stability of $\pi_iU(m)$ is form (b) for the bundle $U(m) \to U(m+1) \to S^{2m+1}$: the base has $\pi_iS^{2m+1} = 0$ for $i \le 2m$ (§XII.18), so $\pi_iU(m) \to \pi_iU(m+1)$ is bijective for $i \le 2m - 1$ and onto for $i = 2m$. And $\pi_iG_m(\mathbb C^{2m}) \cong \pi_{i-1}U(m)$ for $1 \le i \le 2m$ is form (a) for the bundle $U(m) \to V \to G_m(\mathbb C^{2m})$ of the Stiefel manifold over the Grassmannian, once $\pi_iV = 0$ for $i \le 2m$. The bundles, and their local triviality, are Part XIII's. Both forms are proved in every degree, so they also hold where they concern $\pi_0$ or $\pi_1$, at the low end of the sequence, where exactness of pointed sets alone would not give injectivity.

### XII.18 The homotopy groups of spheres below the dimension

$\pi_iS^n = 0$ for $i < n$ is on Mathlib's list of things to do. It feeds the exact sequences of the bundles $U(m) \to U(m+1) \to S^{2m+1}$ in §§23–24. The formal proof is the cell theorem of §XII.8 applied to the two hemispheres, the same decomposition that computes the homology of spheres in Part IV.

**Lemma (contractible spaces).** If $X$ is contractible ⟦Mathlib/Topology/Homotopy/Contractible · ContractibleSpace⟧ and $N$ finite, $\pi_N(X, x)$ is trivial for every $x$. ⟦Homotopy/Spheres · subsingleton_homotopyGroup_of_contractible⟧

*Proof.* $X$ is homotopy equivalent to a point ⟦Mathlib/Topology/Homotopy/Contractible · ContractibleSpace.hequiv_unit⟧. A point has exactly one generalized loop, so its homotopy groups are trivial. The homotopy equivalence induces a bijection (§XII.4), in particular an injection into a trivial set. $\square$

**Lemma (basepoints).** If $x$ and $y$ are joined by a path ⟦Mathlib/Topology/Connected/PathConnected · Joined⟧ and $\pi_N(X, y)$ is trivial, so is $\pi_N(X, x)$. ⟦Homotopy/Spheres · subsingleton_homotopyGroup_of_joined⟧

*Proof.* Change of basepoint along a path from $x$ to $y$ ⟦Mathlib/Topology/Connected/PathConnected · Joined.somePath⟧ is a bijection (§XII.3). $\square$

*The hemispheres.* For $s = \pm 1$ and $z$ in the closed unit ball of $\mathbb R^n$ let
$$h_s(z) = \big(z,\ s\sqrt{1 - \|z\|^2}\big) \in \mathbb R^{n+1}$$
⟦Homology/Spheres · hemisphere⟧, continuous and injective, since it keeps the first $n$ coordinates ⟦Homology/Spheres · continuous_hemisphere⟧ ⟦Homology/Spheres · hemisphere_injective⟧, with values in the unit sphere ⟦Homology/Spheres · hemisphere_mem_sphere⟧. The sphere $S^n$ is the union of the lower hemisphere $D_- = h_{-1}(D^n)$ and the upper hemisphere $D_+ = h_1(D^n)$ ⟦Homology/Spheres · sphere_eq_union_hemisphere⟧ ⟦Homotopy/Spheres · lowerHemisphere_union⟧: a point $x$ of the sphere is $h_s(z)$ with $z$ its first $n$ coordinates and $s$ the sign of its last one. A point $h_1(z)$ of the upper hemisphere lies in the lower one exactly when $\|z\| = 1$, on the equator ⟦Homology/Spheres · hemisphere_one_mem_iff⟧. So $D_+$ is an $n$-cell embedded in the Hausdorff space $\mathbb R^{n+1}$, meeting $D_-$ exactly along its boundary.

$D_-$ is closed, being a compact image ⟦Homotopy/Spheres · lowerHemisphere⟧ ⟦Homotopy/Spheres · isClosed_lowerHemisphere⟧. It is contractible ⟦Homotopy/Spheres · contractibleSpace_lowerHemisphere⟧: $h_{-1}$ restricted to the closed ball is a continuous injection of a compact space into a Hausdorff space, hence a homeomorphism onto $D_-$, and the closed ball is convex and nonempty, hence contractible ⟦Mathlib/Analysis/Convex/Contractible · Convex.contractibleSpace⟧ ⟦Mathlib/Topology/Homotopy/Contractible · Homeomorph.contractibleSpace⟧. The south pole $h_{-1}(0) = -e_{n+1}$ lies in $D_-$ ⟦Homotopy/Spheres · southPole⟧.

**Theorem.** $\pi_N(S^n, x)$ is trivial for $|N| < n$ and every $x \in S^n$, where $S^n$ is the unit sphere of $\mathbb R^{n+1}$. In particular $\pi_iS^n = 0$ for $i < n$. ⟦Homotopy/Spheres · subsingleton_homotopyGroup_sphere⟧ ⟦Homotopy/Spheres · subsingleton_pi_sphere⟧

*The proof as formalized.*

1. *At the south pole* ⟦Homotopy/Spheres · subsingleton_homotopyGroup_sphere_southPole⟧. By the theorem on embedded cells (§XII.8), with $M = \mathbb R^{n+1}$, $A = D_-$ and $\chi = h_1$, the inclusion $D_- \to D_- \cup D_+$ is onto on $\pi_N$ at the south pole, as $|N| < n$. The source is trivial, $D_-$ being contractible, so the target is trivial. The equality $D_- \cup D_+ = S^n$ is a homeomorphism of subspaces, which induces bijections (§XII.4), so $\pi_N(S^n, -e_{n+1})$ is trivial.
2. *At every point.* $|N| < n$ forces $n \ge 1$, so $\mathbb R^{n+1}$ has dimension at least $2$ and its unit sphere is path-connected ⟦Mathlib/Analysis/Normed/Module/Connected · isPathConnected_sphere⟧. Every $x \in S^n$ is joined to the south pole, and the lemma on basepoints finishes. $\square$

The theorem transfers to other models of the sphere. A linear isometry carries unit sphere to unit sphere homeomorphically ⟦Homotopy/Spheres · sphereHomeomorph⟧, and every real inner product space of dimension $n + 1$ is isometric to $\mathbb R^{n+1}$ through an orthonormal basis ⟦Mathlib/Analysis/InnerProductSpace/PiL2 · stdOrthonormalBasis⟧. So $\pi_i$ of its unit sphere vanishes for $i < n$ ⟦Homotopy/Spheres · subsingleton_pi_sphere_of_finrank⟧. The unit sphere of $\mathbb C^m$, of real dimension $2m = (2m - 1) + 1$, is $S^{2m-1}$, and $\pi_i S^{2m-1} = 0$ for $i < 2m - 1$ ⟦Homotopy/Spheres · subsingleton_pi_sphere_complex⟧. This is the form the unitary groups use: $U(m+1)$ acts on the unit sphere of $\mathbb C^{m+1}$, and $\pi_iS^{2m+1} = 0$ for $i \le 2m$.

The retelling of §23 (`Exposition/Chapter14.md`) quotes this fact from the companion volume (Problem 5 of its Chapter 8: a map of a manifold of smaller dimension into a sphere is homotopic to a constant), and adds that a free null-homotopy suffices because $\pi_1$ acts on $\pi_i$ fixing the zero element. The formal proof needs neither the passage from free to based homotopies nor smooth manifolds as domains: the compression of §XII.7 is already relative to the boundary of the cube. The decomposition into hemispheres is the one Part IV uses for the homology of spheres ⟦Homology/Spheres · sphereRelIso⟧.

### XII.19 What the formalization taught us

- **Compression replaces relative homotopy groups.** Mathlib has no relative homotopy groups and no exact sequence of a pair. Compressing cubes gives surjectivity and compressing cylinders gives injectivity ⟦Homotopy/Basic · surjective_homotopyGroupMap_of_compresses⟧ ⟦Homotopy/Basic · injective_homotopyGroupMap_of_compresses⟧, for every index set and at every basepoint. Milnor's step from $\pi_i(\Omega, \Omega^d) = 0$ to $\pi_i\Omega^d \cong \pi_i\Omega$ becomes a direct proof, with $\pi_0$ and $\pi_1$ treated like the rest and the surjectivity at $\lambda_0 - 1$ stated ⟦Homotopy/RelCells · bijective_homotopyGroupMap_sublevel⟧ ⟦Homotopy/RelCells · surjective_homotopyGroupMap_sublevel⟧.
- **Homotopy invariance needs change of basepoint.** Homotopic maps induce the same map on homotopy groups only up to a change of basepoint ⟦Homotopy/ChangeOfBase · homotopyGroupMap_eq_changeBaseMap⟧, and even the invariance under homotopy equivalence has to manage basepoints that do not return ⟦Homotopy/ChangeOfBase · bijective_homotopyGroupMap_of_homotopyEquiv⟧. One construction, the frame, gives all the homotopies ⟦Homotopy/ChangeOfBase · homotopic_of_frame⟧. The mapping telescope needs it too, because the push to the top of a truncation moves the basepoint ⟦Homotopy/Telescope · homotopic_corestrict_telescopeIncl⟧.
- **Cellular approximation without simplices.** The push-off lemma follows from smooth approximation and the null image of a smooth map from a smaller dimension ⟦Homotopy/PushOff · exists_pushOff⟧, because the domains that matter embed in vector spaces of their own dimension ⟦Homotopy/CellAttach · compresses_cellInl_cube⟧ ⟦Homotopy/CellAttach · compresses_cellInl_cyl⟧.
- **The attached-to space needs no separation axiom.** The probe, with its height and coordinate, makes the open cell open and its coordinate continuous for any $Y$ ⟦Homotopy/CellAttach · cellProbe⟧ ⟦Homotopy/CellAttach · isClosedEmbedding_cellInl⟧. The radial push needs no puncture ⟦Homotopy/CellAttach · cellRadial⟧. Hausdorffness enters only for cells embedded in an ambient space, through Lemma D ⟦Homotopy/CellAttach · bijective_homotopyGroupMap_union_cell⟧.
- **Countable complexes by compactness.** A compact set lies in a finite stage, of a filtration ⟦Homotopy/Telescope · bijective_homotopyGroupMap_of_exhaustion⟧ or of a mapping telescope ⟦Homotopy/Telescope · bijective_homotopyGroupMap_telescopeIncl⟧, and the homotopy-commutative squares of Part IX are exactly what the transfer theorem needs ⟦Homotopy/ChangeOfBase · bijective_homotopyGroupMap_iff_of_square⟧.
- **Fibre bundles as a property.** Local triviality of a map, not a bundle structure on a sigma type ⟦Homotopy/Fibration · IsLocallyTrivial⟧; Serre fibrations lift relative to the open box ⟦Homotopy/Fibration · IsSerreFibration⟧, and the absolute property follows by a map of pairs ⟦Homotopy/Fibration · IsSerreFibration.exists_lift_of_bot⟧.
- **"Lift box by box" needs an order and a retraction.** The boxes are added along lower sets of indices, so that the known part of each new box is a union of faces missing one coordinate, onto which it retracts radially ⟦Homotopy/HomotopyLifting · gridCoord_mem_cubeFaces⟧ ⟦Homotopy/HomotopyLifting · gridEmb_mem_of_mem_cubeFaces⟧ ⟦Homotopy/HomotopyLifting · faceRetract_mem⟧. Without the missing coordinate the statement is false.
- **Exactness of pointed sets is not injectivity.** The sequence is exact at every place, $\pi_0$ included ⟦Homotopy/ExactSequence · exact_fiber⟧ ⟦Homotopy/ExactSequence · exact_total⟧ ⟦Homotopy/ExactSequence · exact_base⟧, but the forms Milnor uses need injectivity, which takes two extra arguments ⟦Homotopy/ExactSequenceIso · exists_homotopyGroupMap_eq_inv_mul⟧ ⟦Homotopy/ExactSequenceIso · injective_homotopyGroupMap_fiberIncl⟧. One lemma, changing the top face of a boundary lift inside a lifting problem, replaces every reparametrization of cubes ⟦Homotopy/ExactSequence · exists_isBoundaryLift_topFace_eq⟧.
- **Mathlib's order of multiplication shows.** $[p]\cdot[q]$ is $q$ followed by $p$, so the lift built from $\alpha$ and $\alpha'$ represents $b^{-1}a$ rather than $ab^{-1}$ ⟦Mathlib/Topology/Homotopy/HomotopyGroup · HomotopyGroup.mul_spec⟧, and the side-by-side lifts of the homomorphism property are put down in the order $G'$, $G$ ⟦Homotopy/ExactSequenceIso · boundaryMap_mul⟧.
- **$\pi_iS^n = 0$ is a cell theorem.** The sphere is a contractible hemisphere with a cell attached ⟦Homotopy/Spheres · subsingleton_homotopyGroup_sphere_southPole⟧; no manifold structure on the domain is needed, and no passage from free to based homotopies.
