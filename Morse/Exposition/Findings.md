# Findings: gaps, hidden hypotheses and possible misprints in Milnor's *Morse Theory*

Collected while writing the exposition and the Lean files. Each item names where it was found.
These feed the formalization plan and, later, the verified edition and the comparison edition.

**About the scan.** The PDF is an Acrobat "Paper Capture" scan, which redraws recognised text
in substitute fonts and can silently drop glyphs or parts of displays. On p. 55 the geodesic
equation shows only its `Γ`-term, set right of centre where `d²u^k/dt² + Σ` is missing. A formula
that seems to lack a `Σ`, `½` or `∫` is therefore treated as a defect of the scan unless the
printed text itself clearly reads that way; such items are marked *(scan?)* below.

## §2 (Chapter 1; Lean `Morse/Chapter1/`)

- p. 9, example (d): the critical set of `f(x, y) = x²` is the `y`-axis, not the `x`-axis as
  printed. (Checked against the scan; found by the Lean formalization.)
- p. 1, (1) is printed "`a < 0 < f(p)`"; it should be `a < 0 = f(p)` *(scan?)*. p. 3: the statements
  "`a < f(point) < b`" need `[a, b]` free of other critical values. The torus must stand upright with
  `r < R`: lying flat, its height function has degenerate critical circles. That `p, q, r, s` are the
  only critical points, with the stated normal forms, is asserted without checking (all verified in
  `Morse/Chapter3/Torus.lean`).
- p. 8, Corollary 2.3 is stated without proof; it needs only that `f` is `C²` at `p`
  (`Morse.IsNondegenerateCriticalPoint.exists_nhds_isCriticalPoint_eq`).

## §§1–3 (Chapters 1–2)

- Manifolds must be Hausdorff (unique integral curves, smoothness of `F`, disjoint Morse charts)
  and second countable (a metric, bump functions); Milnor's manifolds are tacitly both.
- Lemma 2.4: defining `φ_t = φ_{ε₀/2}^k ∘ φ_r` needs a check that the result does not depend on how
  `t` is split.
- Morse lemma: the induction must keep the remaining block non-singular; when every diagonal entry
  vanishes, a substitution `u_r = w_r + w_l` is needed first.
- Theorem 3.1: `φ_{b−a}(M^a) = M^b` needs that each trajectory crosses `a ≤ f ≤ b` at most once.
- Theorem 3.2: "k-cell" for "λ-cell" *(scan?: the same scan renders λ as "A")*; the function `μ`
  is never constructed; the bound is `∂F/∂η ≥ 1`, not `> 1` *(scan?: the p. 17 display drops "∂F")*; identifying `M^{c−ε} ∪ e^λ` with the abstract attached space needs a lemma.
- Remark 3.4 ("easily") needs: if `A` is a strong deformation retract of `X` and `B ⊇ A` is a
  retract of `X`, then `A` is a strong deformation retract of `B`.
- Lemmas 3.6–3.7 need `[0,1] ×` (quotient map) to be a quotient map.
- From the Lean proof of 3.2–3.5 on submanifolds: Theorem 3.2 on a manifold silently uses
  Hausdorffness; Lemma 3.7 needs the formula for `k` from the *proof* of 3.6, not only its statement;
  "`M^a` vacuous" (proof of 3.5) needs the minimum of `f` to be a critical point; Remark 3.3 needs
  disjoint Morse charts. Cells attached in non-decreasing dimension form a CW complex only if each
  attaching map lands in the lower-dimensional cells (hence Milnor's appeal to cellular
  approximation).
- From the Lean proof of 3.2: `F` is smooth only because the ellipsoid where `μ` acts is compact,
  hence closed; "`r_t` = identity outside `U`" is continuous only because `r_t` moves points of the
  ellipsoid within it; Case 2 of `r_t` reads `0/0` at `ξ = ε, η = 0`; three lemmas (the two parts of
  "Lemma A" and the pushout identification "Lemma D" of the exposition) are used without being
  stated; possible misprints "`f(q) ≥ c − e`" and "Remark 2.4" *(scan?)*.
- Theorem 3.5: the non-compact case needs patched flows; the infinite case needs Whitehead's
  theorem and the fact that manifolds have the homotopy type of CW complexes.

## §§4–6 (Chapters 3–4)

- From the Lean proof of §5 in singular homology: p. 29 assumes distinct critical values; its first
  "=" needs homotopy equivalences of pairs, and moving the bottom of the pair needs the exact sequence
  of a triple; the step called excision is not literally excision; `M^{a₀} = ∅` and `M^{a_k} = M` rely
  on the minimum and maximum being critical values; finiteness of `R_λ` is a consequence, not an
  assumption; that `χ` is the same over every field, and the homeomorphism invariance used to pass to
  an embedded copy, are never stated.
- Morse inequalities: the choice of the `a_i` assumes distinct critical values; the fix is one
  critical value per slab (using Remark 3.3).
- Excision: `(M ∪ e, M) → (e, ė)` is not a literal excision; it needs a thickened subspace,
  deformation retracts and the five lemma.
- Subadditive functions need a domain closed under triples (pairs with finite-dimensional
  homology).
- §4, three critical points: needs compactness and non-degeneracy, and Poincaré duality only mod 2
  (`ℝP²` is non-orientable), plus a parity argument.
- Reeb's theorem: the proof gives only a homeomorphism (Alexander's trick); Remark 1 needs Brown's
  monotone-union theorem.
- From the Lean proof of Reeb's theorem: that the minimum has index `0` and the maximum index `n`
  is used without comment; minimum `≠` maximum needs `n ≥ 1` (in dimension `0` the function can be
  constant); "`ε` small" must put the whole sublevel set inside the Morse chart, which needs
  compactness and a unique minimum; Theorem 3.1 as stated does not say that the level `f⁻¹(ε)` goes
  onto `f⁻¹(1 − ε)` (only its proof gives it); the "easy" gluing needs Alexander's trick, the pasting
  lemma, and compact-to-Hausdorff.
- Integral homology of `ℂPⁿ`: Corollary 5.4 gives only Betti numbers over fields; a lacunary
  argument is needed.
- §6, possible misprints: `K₁ … K_n` should be `K₁ … K_k`; "rank" should be "nullity"; normal frames exist only
  locally; `t = 0` must be excluded; "`≥ 1/t`" should be "`> 1/t`".
- Corollaries 6.7–6.8 need Hausdorff, second-countable manifolds and a closed embedding; the
  derivative bounds need fixed charts; Application 2 needs `f` to be a Morse function.

## §§16–19 (Chapters 10–11)

- **Theorem 17.1 (p. 94): "Clearly `h` is continuous" does not hold as we read it** — confirmed by an independent
  review against the scan, by numerical checks, and now in Lean (`Morse.milnor_h_not_continuous`). `h(ω)` agrees with `ω` at `0, A(ω), …, kA(ω)`
  and `1`, where `A` depends continuously on `ω` and `k` is the largest integer in `1/A(ω)`. When
  `1/A(ω)` crosses an integer a last interval of length near `0` appears; for a continuous path
  that is not Lipschitz at its end (e.g. `M = ℝ`, `ω_λ(t) = λ((1−t)^{1/3} − (1−t))`) the energy of
  the geodesic on that interval blows up (`E(h(ω_λ))` = 0.44 at `λ*`, then 9.7, 20.7, 44.2, 94.9
  for `λ/λ* − 1 = 10⁻³, …, 10⁻⁶`), while `ω_λ → ω_λ*` uniformly. Since `√E` is 1-Lipschitz for
  Milnor's metric `d`, `h` is not continuous into `(Ω, d)`. The theorem is true; the exposition
  proves it by a modified argument, with dyadic subdivisions, convex balls and Theorem A of the Appendix applied
  to closed truncations of the telescopes. §19.6 needs the full 17.1, not only a weak form.
- §16, p. 91 (possible misprint, in the printed text): the condition defining `B^a` should read
  `Σ ρ²/Δt ≤ a`; the exponent printed as `c` should be `2` (a missing `Σ` is probably a defect of
  the scan *(scan?)*). From the Lean proof of §16: Theorem 16.3 needs `a` not to be the energy of a
  geodesic; closedness of `B^a` needs the distances to be finite; Lemma 15.4 is used with segments
  free of conjugate points (normal radius `≥ ε`); "`r_u` fixes `B`" needs uniqueness of short
  geodesics; the "easily verified" continuity of `r_u` needs the two formulas to agree at `u = t_i`
  and uniform energy bounds on short intervals for the speed term; continuity of `E` needs
  Minkowski's inequality; continuity of
  `r_u` needs `L²` control of the speed on short intervals; Lemma 15.4 is used with the subdivision
  properties of §15; 16.3 needs a regular level `a′ > a` and a reparametrized `E′`.
- **The modified proof of 17.1 is now machine-checked** (`Morse.theorem_17_1`): dyadic subdivisions
  kept fixed, Theorem A of the Appendix on open pieces via telescopes. It also needs good balls to be
  convex, one smooth minimal-geodesic map on each whole ball, `d` to control velocities in `L²`, and
  care with `Ω` not being Hausdorff; no completeness is needed.
- From the Lean proof of 17.3: the strict "`g_{i+1}` extends `g_i`" is not needed (towers commuting
  up to homotopy suffice); a relative Theorem 3.5 is needed; Milnor switches between loops and paths;
  for the sphere, the list of geodesics must be shown complete, with multiplicities and
  non-conjugacy checked.
- 17.3: the `a_i` must tend to `∞`, with at most one critical value per interval; compatible maps
  need nested subdivisions.
- 17.4, 19.6: loop spaces and arbitrary endpoints need an endpoint-change lemma and 17.1. 17.5 needs
  completeness (`ℝⁿ⁺¹ ∖ 0` is a counterexample).
- From the Lean proofs of §§18–19: 18.1 treats `exp_p` as smooth on all of its domain, while §10
  gives smoothness only near the zero section (proved here); "measure zero in `M`" is never defined;
  18.2's "follows immediately" also needs every geodesic from `p` to be radial and the domain of
  `exp` to be open; density from measure zero needs that null sets have empty interior; in 19.4,
  parallel frames along the geodesic need `V` parallel (constant speed). In 19.6 Milnor does justify
  that `K(U, U)` attains a minimum (the unit tangent bundle is compact, p. 106; an earlier version
  of this item said otherwise); only the compactness of the unit tangent bundle is left implicit.
- From the Lean proof of 19.2–19.6: "it is clear" that the universal cover is complete needs the
  Gauss lemma on the whole domain of `exp_p` (Milnor states it only in a normal neighbourhood);
  "`πᵢ(M) = πᵢ(M̃)`" uses that the boundary of the cube is connected for `i ≥ 2`; in 19.6 the
  continuity of `K(U, U)` (a trace over the moving subspace `T_qN`) is unproved, `n ≥ 2` is needed
  and not stated, and the proof covers only non-conjugate endpoints.
- 19.4 needs `n ≥ 2`. (The `½`, `Σ` and `∫` missing from its displays in the scan are dropped
  glyphs: blank gaps sit where they belong. Withdrawn as misprints.) 19.2 silently uses
  17.1 to get `π₀` of the path space.

## §5 and §6 Application 2 (Lean `Morse/Chapter3/EulerChar*.lean`)

- §6, Application 2 (pp. 36–37) is the Poincaré–Hopf proof of `Σ(−1)^λ C_λ = χ`: its "any
  differentiable function" must be a Morse function, and "critical points of `X`" means zeros of `X`.
- It states without proof that `(−1)^λ` is the index of `grad f` at a critical point of index `λ`;
  this needs a metric and `sgn det = (−1)^index` (spectral theorem and Sylvester's law). The Hessian
  of `F|N` is not the restriction of the Hessian of `F`; replacing `F` by `F ∘ r` (`r` the
  nearest-point retraction) repairs this.
- p. 29: "isolated" is redundant for non-degenerate critical points, and "`± C_n`" silently takes
  `n = dim M`. p. 25 (Reeb): the indices `0` at the minimum and `n` at the maximum are used without
  comment.

## §6 (Lean `Morse/Chapter4/`)

- Numbering in the book: Milnor's 6.3 is about principal curvatures, 6.5 is the statement about
  `L_p`, and 6.8 is a corollary.
- p. 35: "rank of the upper-left block" should be its nullity (the ranks differ by `n − k`). Normal
  frames `w_α` exist only locally; the cases `t = 0` and `p = q` are implicit.
- p. 38: "`≥ 1/t`" should be "`> 1/t`"; equality is excluded only by non-degeneracy. Principal
  curvatures are defined in coordinates with `g = I`, with no argument that such coordinates exist
  or that the result does not depend on them.
- Corollary 6.7 needs Hausdorff, second countable and a closed embedding. Corollary 6.8's hypothesis
  that `f` is bounded is unnecessary: perturbing by `⟨a, β(x)⟩` with `β` a diffeomorphism of `ℝⁿ`
  onto the open unit ball works for every `f`.

## §§20–22 (Chapters 12–13)

- 21.5: `G` must be connected (`SO(3) × ℤ` is a counterexample).
- 21.7, finiteness: the "§19.4" argument needs trivial centre, from 21.6, hence simple
  connectivity; the proof treats `Ω(G; p, q)`, not the loop space, and changing endpoints needs a
  lemma. The remarks after 21.7: Remark 1 fails for `G = {e}`; Remark 2 needs `G` connected and
  simply connected.
- 20.1: the proof uses `γ(−t)`, so completeness must come first. 20.5 is a statement about
  parameter values on any interval, not about points.
- 22.5: `M⁰` compact is implicit; `g` must be defined on an open set where `f` is bounded; "homotopy
  type with cells attached" must be relative to the lower level with regular levels; Hanner's
  theorem is needed (or a tubular neighbourhood, if `Ω^d` is smooth).
- 22.1: `i = 0, 1` need direct handling; Lemma 22.4 must allow degenerate critical points, since
  non-minimal antipodal geodesics are degenerate.

## §§23–24 (Chapters 14–15)

- Page ranges: §23 runs pp. 124–132 and §24 pp. 133–148 (checked against the scan).
- Minimal geodesics are matched with the Grassmannian only as a set; a homeomorphism needs a
  compactness argument.
- Why `SU(2m)` and not `U(2m)`: in `U(n)` the non-minimal geodesic with `k = (3, 1, …, 1)` has index
  `0`, so the hypothesis of Theorem 22.1 fails there.
- Periodicity is an abstract isomorphism in each degree; `ΩU ≃ ℤ × BU` needs colimits and CW
  homotopy types (Milnor 1959), quoted.
- Lemma 24.4 needs `Ω_{l+1}(n) ≠ ∅` and the convention `J₀ = I`; the "only if" halves of Assertions
  1–2 hold only for small `A`.
- The curvature computation on `Ω_k(n)` silently uses the Gauss equation for totally geodesic
  submanifolds.
- Lemma 24.8 is only sketched for `k ≤ 8`, so Theorem 24.5 holds as proved only for `k ≤ 7`, which
  suffices for periodicity.
- The case `k ≡ 2 (mod 4)` needs Theorem 22.1 one component at a time, `n/2` even, stability of the
  integer labelling components, and the general bound `|a_h| ≥ 3` where Milnor gives one example
  ("… equal to −3"; checked on review: an example in clear prose, not a misprint).
- p. 148 (checked against the scan): the chain bounds `Σ(a_h − a_j − 2)` strictly from below by
  `Σ_{a_h > 0}(a_h − (−3) − 3) = p`; the `−3` in place of `−2` is a deliberate weakening that makes the
  inequality strict, which then needs at least one positive `a_h`. Only the example `a_h = −3` is
  treated.
- From the Lean proofs: p. 131, the count of conjugate points needs `k_i − k_j` even, an exchange of
  the two sums, and a reason the eigenvectors span; p. 135, the eigenvalues used are those of
  `K_{πA} = π² K_A`, not of `K_A`; p. 143, "follows from 24.6" needs cyclic vectors and that the
  central element acts as `±1` on a minimal space.
- The chain needs `J₃`, `J₇` in the middle components and an explicit stabilizing block in `ℝ¹⁶`
  (given in the exposition by Kronecker products).

## §2 p. 10, Lemma 2.4 (Lean `Morse/Flow/`)

- Smooth dependence of the flow on the initial point is quoted as well known; Mathlib has only
  Lipschitz dependence. Proved here via the inverse function theorem in `C([0,1], E)`.
- Uniqueness of the 1-parameter group generated by a field is implicit in the text; it uses that
  uniqueness of integral curves is global in time.

## §5 (Chapter 3; Lean `Morse/Chapter3/Inequalities.lean`)

- Numbering: subadditivity of `S_λ` is Lemma 5.3; Theorem 5.2 is the weak inequalities.
- The instantiation with singular homology needs relative homology, the exact sequence of a
  triple and excision (`H_*(M^b, M^a) ≅ H_*(e^λ, ∂e^λ)`), none of which Mathlib has yet.

## §7 (Chapter 5)

- Assertion 2 (p. 40) reads the focal points off the eigenvalues of `Q′` in the coordinate inner
  product; they are eigenvalues relative to `g_ij`. A shorter route avoids focal points: the
  Andreotti–Frankel identity `H(JX, JX) = 4g(X, X) − H(X, X)`.
- 7.2 proves that the dimension is at most `k`, not exactly `k`; 7.3 and 7.4 need `V` of pure
  dimension `k` (a counterexample is in the exposition).
- The neighbourhood of `V ∩ P` (p. 42) must deform with `V ∩ P` fixed; triangulability is quoted.
- p. 41: the form of Lefschetz duality used is never named (a proof of 7.3 without duality is in
  the exposition).
- `f = 1/L_p` is infinite at `p` when `p ∈ V`; Theorems 3.1–3.2 are run on `V` away from `V ∩ P`.

## §§8–9 (Chapter 6)

- Locality of connections and the tensor property (by bump functions) are used silently; patching
  across charts is needed in 8.1, 8.2, 8.6; 8.6 needs a converse of 8.3 that is not stated.
- A possible misprint on p. 49 (see the exposition).
- From the Lean proofs (submanifolds of `ℝᴷ`): Lemma 8.2, "linear, hence defined for all `t`": the
  natural equation `X′ = P′X` has no a priori bound; solving `X′ = (P′P − PP′)X` instead preserves
  norms, and a second uniqueness argument keeps the solution tangent. Lemma 8.6, "one can verify":
  symmetry of the connection is the symmetry of the second fundamental form, which Part II never
  mentions. Lemma 9.1, "similar computations": the `Z` case is a different computation. Lemma 9.3
  (2)–(3) assume extensions with vanishing brackets. Lemma 8.3 needs parallel orthonormal frames.
  Lemmas 8.7 and 9.2 need `DV/∂x` jointly smooth.
- Milnor's curvature tensor `R` is the negative of the standard (Kobayashi–Nomizu) one
  (`Morse.milnorCurvature_eq_neg`); Mathlib v4.33.1 has connections and torsion but no curvature
  tensor, Levi-Civita connection or parallel transport. Sectional curvature only appears on
  p. 100; that it does not depend on the basis of the plane and that it determines `R` are never
  stated.
- §7: "the linear terms vanish" (p. 40) needs real orthogonality to a complex subspace to imply
  Hermitian orthogonality; the focal-point count needs `p`, `q` non-focal and the case `p = q`.
- §9: the signs on the faces of the octahedron (proof of 9.3 (4)) are left to the reader.

## §10 (Chapter 7)

- Hausdorffness is needed for uniqueness of geodesics beyond one chart and for compact normal balls
  to be closed.
- ~~The printed geodesic equation omits the term `d²u^k/dt²`.~~ Withdrawn on review: a defect of
  the scan (the display is off-centre by the width of the missing part), not a misprint.
- Theorem 10.4: competing paths may leave the normal ball (a shell-crossing lemma is needed); the
  equality case "same image" is too weak for Corollary 10.7, which needs `ω = γ ∘` (a monotone
  reparametrization).
- `ρ` is a metric: positivity needs a separate lemma, and the topology needs "small metric balls
  are normal balls".
- Corollary 10.8 needs a finite subcover and `δ ≤ min ε`; the Hopf–Rinow argument also needs
  `δ < ρ(p, q)`. Corollary 10.10 needs `exp` continuous on all of `TM_p` (global flow theorem).
- From the Lean proofs (submanifolds of `ℝᴷ`): "the unique geodesic" needs uniqueness beyond one
  chart; Lemma 10.2 needs a uniform bound of chart coordinates by `‖v‖` and never states smooth
  dependence; in 10.3 it is the inverse (not the implicit) function theorem, and the sets `V′` must
  form a neighbourhood base; equality in 10.6 needs `d exp` injective; 10.7 needs minimality of
  segments and break points inside segments.
- From the Lean proof of Hopf–Rinow: the continuity of `ρ` is used without proof; the proof needs
  `δ < ρ(p, q)` and `δ′ < r − t₀` where only `δ < ε` is stated; the point of `S` nearest to `q` needs
  `S` nonempty and `ρ` continuous; "coincides with `γ`" needs unit speed at the break and uniqueness of
  geodesics in the large; 10.10 needs `exp_p` continuous on the whole disk; the converse needs only
  Lemma 10.2, not 10.3 as cited; completeness at a single point suffices; "Cauchy ⇒ convergent" is
  left unstated.
- Supplied, not proved in the book: the converse of 10.10, the convexity remark, the `U(n)`
  footnote (a bi-invariant metric only).

## Appendix

- Theorem A and closedness (settled by the Lean proof): Case 1 of Milnor's proof, as written, needs
  the `X_i` closed (pasting); Case 2 applies Case 1 only to truncations of the telescope, which are
  always closed, so his proof of Theorem A needs only the `Y_i` closed; and Theorem A holds exactly
  as Milnor states it, with no closedness at all, by running his proof on mapping telescopes
  (`Morse.theoremA_general`). The exposition's earlier claim that the `X_i` and `Y_i` must be closed
  is too strong.
- Possible misprint: `(4 − 3t)u` should be `(4t − 3)u` (confirmed on review: at `t = 3/4` the printed
  formula gives `7u/4`, not `0`).
- The application cites "Theorem 17.2"; it is Corollary 17.2 (p. 95).
- Case 2 silently uses that the telescope is the homotopy limit of its truncations.
- The application in 17.3 needs `a_i → ∞`, `E` continuous, and `f_{i+1}` extending `f_i`.

## §§11–15 (Chapters 8–9)

- The "tangent space" `TΩ_ω` of the path space is formal: `Ω` is given no manifold structure. Every
  statement must be read through variations, or `Ω` must be replaced by Palais's `H¹` Hilbert
  manifold.
- Variations built from the exponential map need a uniform `ε` from compactness (Lemma 11.A of the
  exposition), and in 14.4 the openness of the domain of `exp`. Completeness of `M` is never needed.
- Formula (12.2′) is used at every `u`, not only at `u = 0`: §13 differentiates it. The reference
  to "Lemma 8.5" should be to Lemma 8.7 (confirmed against the scan: 8.5 is the definition of a
  symmetric connection, p. 48; the interchange of `D/∂t` and `D/∂u` is Lemma 8.7, p. 50).
- Lemma 14.4 (p. 81): the variation through minimal geodesics needs `γ|[0, δ]` to be *the* minimal
  geodesic from `γ(0)` to `γ(δ)`, which Milnor does not argue. It follows from his choice of `U`
  (unique minimal geodesics depending differentiably on the endpoints): if `γ|[0, s]` stopped being
  minimal, `γ(s)` would be a cut point, hence conjugate (excluded by the differentiable dependence)
  or joined by a second minimal geodesic (excluded by uniqueness). The exposition supplies the
  argument. The Lean proof (`Morse.lemma_14_4`) avoids the issue altogether: it builds the variation
  from the initial data, `α(u, t) = exp_{c(u)}(t w(u))` with `c(u) = exp_{γ(0)}(u J(0))`, so it needs
  no minimality and no restriction to a short segment. (This replaces an earlier
  item, withdrawn on review, that claimed a missing length bound.)
- Remark 14.2 needs `γ` non-constant; Example 2 needs Remark 14.2 for the upper bound `n − 1`.
- The continuity of `H_τ` (used in the proof of the index theorem, unproved in the book) needs
  non-conjugacy on the segment.
- From the Lean proofs of §§11–14.1: symmetric mixed partials are needed on the edges of the strips
  of a variation; the test fields of 12.3 and 14.1 need Lemma 11.A and care at break points; the
  "uniqueness theorem" step of 12.3 needs a derivative-extension argument at break points; the
  symmetry in 13.4 tacitly needs `E ∘ ᾱ` of class `C²`; bilinearity in `W₁` needs one-sided
  linearity; in 14.1 "fit together" needs linear ODE theory.
- From the Lean proof of §§14–15: "defined throughout `γ`" needs global existence for linear ODEs;
  Remark 14.2 fails for a constant geodesic and needs `n ≥ 1`; in Lemma 14.4 the compactness step is
  smooth dependence on initial data over a compact interval, and identifying the extended field with
  `J` needs uniqueness of Jacobi fields, not stated; "`H_τ` evidently continuous" needs non-conjugacy
  and a perturbation lemma; Lemma 15.4 rests on an abstract index lemma rather than a
  "straightforward" proof.
- Theorem 15.1 needs the finiteness of the set of conjugate points before the index `λ` can be
  assembled from the nullities.
