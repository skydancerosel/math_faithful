# Compactness first: a roadmap for formalizing the compactness theorems of geometric analysis and symplectic topology

*A planning document, written for a research group or a lab with the compute to run large
formalization efforts and looking for a target that matters. It argues that the compactness
theorems of geometric analysis, and the frameworks built to tame them in symplectic and contact
topology, are that target; takes inventory of what they are and what they need; and proposes an
order of attack along two tracks. Statements about the current contents of the Lean library Mathlib
are as of the author's knowledge in September 2026 and should be re-checked against the library
before work begins.*

---

## 1. Why compactness

Nearly every existence theorem in geometric analysis has the same shape. One wants a solution of a
nonlinear partial differential equation: a harmonic map, a minimal surface, a Yang–Mills connection,
a metric of constant scalar curvature, a periodic orbit of a Hamiltonian system, a pseudoholomorphic
curve, a solution of a nonlinear Schrödinger or wave equation. One writes down an energy whose
critical points are the solutions, takes a sequence of approximate critical points (a minimizing
sequence, a Palais–Smale sequence, a sequence of solutions with bounded energy), and asks whether it
converges. In the natural function spaces it does *not* converge in general, and the theorems that
say exactly *how* it fails are the compactness theorems:

* The sequence may **concentrate**: its energy collects at points, and after rescaling one sees a
  nontrivial solution on the whole space, a *bubble*. Sacks–Uhlenbeck for harmonic maps (1981),
  Brezis–Coron's "how to blow bubbles" (1985), Struwe's global compactness for the Yamabe-type
  functional (1984), Uhlenbeck's compactness for Yang–Mills (1982), the bubble trees of Gromov
  compactness (1985).
* The sequence may **vanish** or **split**: spread out, or separate into pieces that drift apart.
  Lions's concentration-compactness principle (1984–85) classifies this; the profile decompositions
  of Gérard (1998) and Bahouri–Gérard (1999) make it quantitative.
* In variational problems the failure of compactness itself has a **Morse theory**: the lost
  sequences behave like critical points that are not there, and their topology is computable. This
  is Bahri's theory of *critical points at infinity* (1989), which with Coron (1988) proved that a
  domain with nontrivial topology carries a solution of the critical-exponent equation that has no
  positive solution on a ball, and which Bahri and Lions (1992) tied to Morse indices of Palais–Smale
  sequences. The same viewpoint drives Bahri's variational approach to periodic orbits of contact
  forms and to the Weinstein conjecture.
* In symplectic and contact geometry, **Hofer's compactness** for finite-energy pseudoholomorphic
  planes in a symplectization (1993) turned the Weinstein conjecture in dimension three into a
  bubbling-off analysis; Hofer, Wysocki and Zehnder then described the asymptotics of such curves
  near punctures (1995–2000), and Bourgeois, Eliashberg, Hofer, Wysocki and Zehnder proved the
  **SFT compactness theorem** (2003): sequences of finite-energy curves converge to *holomorphic
  buildings*, stacked levels joined along Reeb orbits. This is the compactness theorem behind
  contact homology and symplectic field theory.
* The compact moduli spaces produced by Gromov and SFT compactness are not manifolds, and the
  invariants built from them need a *virtual fundamental cycle*. The frameworks for this, Fukaya–
  Oh–Ohta–Ono's Kuranishi structures, McDuff–Wehrheim's Kuranishi atlases, Pardon's implicit
  atlases, and Hofer–Wysocki–Zehnder's **polyfold theory**, are thousands of pages of analysis whose
  purpose is precisely to put a smooth, Fredholm structure on a compactified moduli space so that
  compactness and transversality can be used together. The correctness of these foundations was
  publicly debated in the 2010s; it was settled, but by argument and re-exposition, not by anything
  a machine has checked.
* In the geometric setting the *domain itself* may degenerate: Cheeger–Gromov compactness for
  Riemannian manifolds, Hamilton's version for Ricci flows (1995), Perelman's no-local-collapsing;
  and in geometric measure theory Federer–Fleming's compactness for integral currents (1960) and
  Allard's regularity (1972) are what make minimal surfaces exist.

These theorems are what make the subjects work: knowing the *only* ways convergence can fail, one
rules them out by an energy estimate, a topological argument, or a virtual count, and the solution
or the invariant exists. Yamabe (Aubin, Schoen), Bahri–Coron, Sacks–Uhlenbeck, Donaldson theory,
Floer homology, Gromov–Witten theory, contact homology, the Weinstein conjecture (Hofer in dimension
three for overtwisted and $S^3$-like cases, Taubes in general), Perelman's geometrization, the
Kenig–Merle theory of critical dispersive equations, all run through a compactness theorem.

At the time of writing, none of these theorems is formalized, in Lean or in any other proof
assistant, and the infrastructure they rest on (Sobolev spaces, elliptic regularity, analysis on
Riemannian manifolds, the sc-calculus) is largely absent from Mathlib. The headline results recently
announced with machine-checked proofs sit in other parts of analysis. This document is a case that
compactness is the right next place to build, and a plan for doing it.

Three reasons this is the right target rather than a single famous theorem. First, *leverage*: one
compactness theorem is a dependency of dozens of existence theorems. Second, *honesty of
statement*: compactness theorems have clean, checkable statements which a human mathematician can
verify without reading the proof; that is what a large automated effort needs from its human
collaborators, and it is the part that does not need compute. Third, *unfinished verification*: the
symplectic foundations in particular are long, were contested, and are relied upon by a whole field;
a machine-checked polyfold theory would be a genuine service, not a demonstration.

---

## 2. The tally

Each entry gives: the statement in one or two sentences, the source, what it needs, what needs it,
the state of the Lean library Mathlib as far as the author knows (marked *check*), notes for the
formalizer, and a size: **S** comparable to Sard's theorem in the accompanying Milnor project (one
working session with an agent, about 1,500 lines including missing infrastructure), **M** a few such
units, **L** months for a team with agents, **XL** a multi-year library effort. Entries are grouped
in blocks A–G; the dependency graph in §3 uses the labels.

### A. Functional-analytic core

**T1. Arzelà–Ascoli.** A subset of $C(K, Y)$, $K$ compact, is precompact iff it is pointwise
precompact and equicontinuous. *Mathlib:* present (`BoundedContinuousFunction.arzela_ascoli`).
*Needed by:* every compactness argument that passes to $C^k$ convergence on compact sets. **Done.**

**T2. Banach–Alaoglu and weak sequential compactness.** The closed unit ball of the dual of a
normed space is weak-* compact; in a reflexive space, bounded sequences have weakly convergent
subsequences; in a Hilbert space this is elementary. *Mathlib:* Banach–Alaoglu present
(`WeakDual.isCompact_polar`); the sequential statement for Hilbert spaces should be checked and, if
missing, is S. *Needed by:* T8, S6, every minimizing-sequence argument. **Done / S.**

**T2′. Gromov–Hausdorff precompactness.** A family of compact metric spaces with a uniform bound
on the number of $\varepsilon$-balls needed to cover, for each $\varepsilon$, is precompact in the
Gromov–Hausdorff metric. *Source:* Gromov (1981). *Mathlib:* the Gromov–Hausdorff space and its
completeness are present (`GromovHausdorff`), including a total-boundedness criterion (*check* the
exact form). *Needed by:* T14, Cheeger–Colding theory. *Note:* this is the one deep compactness
theorem of the subject that is essentially already formalized; it should be advertised as such.
**Done.**

**D1. Distributions, weak derivatives, mollifiers, cutoffs.** Test functions, the distributional
derivative, convolution with an approximate identity converging in $L^p$, smooth bump functions with
prescribed support. *Mathlib:* Schwartz space, smooth bump functions and convolution are present;
general distributions on open sets are partial (*check*). *Needed by:* T3 and everything after.
*Note:* decide once whether $W^{k,p}$ is built on distributions or on the closure of smooth
functions; the two are equivalent (Meyers–Serrin) but the proof of equivalence is itself an M-sized
task. **S–M.**

**T3. Sobolev spaces $W^{k,p}(\Omega)$.** Definition via weak derivatives; completeness; density of
$C^\infty_c$ in $W^{k,p}(\mathbb R^n)$ and of $C^\infty(\bar\Omega)$ for Lipschitz $\Omega$;
extension operator for Lipschitz domains; trace theorem; the homogeneous space $\dot H^1$.
*Source:* any of Adams–Fournier, Evans, Brezis. *Mathlib:* absent as a theory (*check* for recent
work). *Needed by:* T4–T14, V1–V4, P1–P3, F4. *Notes:* work over $L^p$ equivalence classes; state
for open subsets of a finite-dimensional inner product space, not $\mathbb R^n$; the extension and
trace theorems are the expensive parts and are not needed for the $\mathbb R^n$ theory, so they can
be deferred to after T8. **M (for $\mathbb R^n$), L (with domains).**

**T4. Sobolev, Gagliardo–Nirenberg, Morrey, Hardy–Littlewood–Sobolev inequalities.**
$\|u\|_{L^{p^*}} \le C\|\nabla u\|_{L^p}$ for $p < n$, $p^* = np/(n-p)$; Hölder continuity for
$p > n$; sharp constants (Aubin, Talenti 1976; Lieb 1983 for HLS). *Needed by:* T5, T9, T10, V2.
*Notes:* the Gagliardo trick (integrate along lines, then Hölder) formalizes cleanly; the sharp
constant and the classification of extremals (the bubbles $U(x) = (1 + |x|^2)^{-(n-2)/2}$ up to
scaling and translation) are a separate M task needed by T10 and V2. **M.**

**T5. Rellich–Kondrachov.** For bounded Lipschitz $\Omega$ and $q < p^*$, the inclusion
$W^{1,p}(\Omega) \to L^q(\Omega)$ is compact. *Needs:* T3, T4, and the Kolmogorov–Riesz–Fréchet
criterion: a bounded subset of $L^p(\mathbb R^n)$ is precompact iff it is tight and
$\sup_f \|f(\cdot + h) - f\|_p \to 0$ as $h \to 0$. *Needed by:* T8–T14, V1–V3. *Note:* prove
Kolmogorov–Riesz first as a standalone theorem; it is reusable and S. **M.**

**E2. Fredholm theory and the implicit function theorem in Banach spaces.** Fredholm operators,
index, stability under small and compact perturbations, the $C^k$ implicit function theorem, the
Sard–Smale theorem (regular values of Fredholm maps of index $d$ are generic). *Mathlib:* the
Banach IFT is present; Fredholm operators and Sard–Smale are absent (*check*). *Needed by:* V1, F3,
S6, and every transversality argument. *Note:* Sard–Smale needs Sard's theorem, which the Milnor
project has. **S–M.**

**E1. Elliptic regularity.** Interior and boundary $L^p$ estimates for the Laplacian
(Calderón–Zygmund), Schauder estimates, $\varepsilon$-regularity for the equations in T10–T12, S1
($\|\nabla u\|_{L^2}$ small on a disc implies $C^k$ bounds inside). *Needed by:* T10–T14, SW,
S1–S7. *Notes:* the single largest infrastructure item in Track I; nothing geometric can be
completed without it; the Calderón–Zygmund theory needs singular integrals, which Mathlib does not
have. Start with the $L^2$ theory (energy estimates, difference quotients) which suffices for
$\varepsilon$-regularity of harmonic maps and $J$-curves in two dimensions, and defer $L^p$. **L.**

### B. Variational methods and critical points at infinity

**V1. Palais–Smale condition, deformation lemma, mountain pass and linking theorems.** If $J$ is
$C^1$ on a Banach space, satisfies (PS)$_c$, and has a mountain-pass geometry, then $c$ is a critical
value. *Sources:* Palais–Smale (1964), Ambrosetti–Rabinowitz (1973), Rabinowitz's CBMS notes
(1986); Ekeland's variational principle (1974) as the alternative route. *Needs:* E2, pseudo-gradient
vector fields and their flows (ODE in Banach spaces, in Mathlib). *Needed by:* T10, V2–V4, S2.
*Note:* Ekeland's principle is a pure metric-space theorem and is S on its own. **M.**

**T6. Lions's concentration-compactness lemma I.** Let $\mu_k$ be probability measures on
$\mathbb R^n$. Then, along a subsequence, exactly one of: *compactness* (there are $y_k$ with
$\mu_k(B(y_k, R)) \ge 1 - \varepsilon$ for $R = R(\varepsilon)$), *vanishing*
($\sup_y \mu_k(B(y,R)) \to 0$ for every $R$), or *dichotomy* (there is $\alpha \in (0,1)$ and
$\mu_k \approx \mu_k^1 + \mu_k^2$ with masses $\alpha$, $1 - \alpha$ and supports drifting apart).
*Source:* Lions, Ann. IHP 1 (1984), Part 1, Lemma I.1. *Needs:* measure theory only. *Needed by:*
T8, and conceptually everything in block B. *Note:* the proof is a diagonal argument on the
concentration functions $Q_k(R) = \sup_y \mu_k(B(y,R))$; the formal statement must fix which
subsequence and which cutoffs, which is exactly where textbook versions are loose. **S.**

**T7. Brezis–Lieb lemma.** If $u_k \to u$ a.e. and $\sup_k \|u_k\|_p < \infty$ then
$\|u_k\|_p^p - \|u_k - u\|_p^p \to \|u\|_p^p$. *Source:* Brezis–Lieb, Proc. AMS 88 (1983). *Needs:*
$L^p$, Fatou, dominated convergence. *Needed by:* T8, T9, T10. **S.**

**T8. Lions's concentration-compactness II (locally compact case).** For translation-invariant
minimization problems $I_\lambda = \inf\{E(u) : \int |u|^q = \lambda\}$, every minimizing sequence is
relatively compact up to translation iff the strict subadditivity $I_\lambda < I_\alpha +
I_{\lambda-\alpha}$ holds for all $0 < \alpha < \lambda$. *Source:* Lions (1984), Parts 1 and 2.
*Needs:* T5, T6, T7. *Needed by:* existence of ground states for nonlinear Schrödinger and
Choquard equations, the Thomas–Fermi and Hartree problems. **M.**

**T8′. The limit case: Lions's Rev. Mat. Iberoam. papers (1985).** Concentration-compactness for
critical-exponent problems, with the measure-theoretic lemma: if $u_k \rightharpoonup u$ in
$\dot H^1$, $|\nabla u_k|^2 \rightharpoonup \mu$, $|u_k|^{2^*} \rightharpoonup \nu$, then
$\nu = |u|^{2^*} + \sum_j \nu_j \delta_{x_j}$, $\mu \ge |\nabla u|^2 + \sum_j \mu_j\delta_{x_j}$,
with $\nu_j^{2/2^*} \le S^{-1}\mu_j$. *Needs:* T4 (sharp constant), T7. *Needed by:* T10, V2. **M.**

**T9. Profile decomposition.** Every bounded sequence in $\dot H^1(\mathbb R^n)$ has a subsequence
$u_k = \sum_{j \le J} \lambda_{j,k}^{-(n-2)/2}\,\phi_j\bigl((x - x_{j,k})/\lambda_{j,k}\bigr) +
r_k^J$ with pairwise orthogonal scales/centres and $\limsup_k \|r_k^J\|_{L^{2^*}} \to 0$ as
$J \to \infty$, together with the Pythagorean expansion of the $\dot H^1$ norm. *Sources:* Gérard,
ESAIM COCV 3 (1998); Bahouri–Gérard, Amer. J. Math. 121 (1999) for the wave equation; Keraani for
Strichartz norms. *Needs:* T3, T4, T7. *Needed by:* T10, P2, P3. *Note:* prove by induction on the
energy defect; the orthogonality of scales is a clean lemma about sequences of pairs
$(\lambda, x)$. **M–L.**

**T10. Struwe's global compactness; Brezis–Coron.** Every Palais–Smale sequence for
$E(u) = \tfrac12\int |\nabla u|^2 - \tfrac1{2^*}\int |u|^{2^*}$ on a bounded domain is, up to a
subsequence, a solution plus finitely many bubbles (rescaled solutions on $\mathbb R^n$) with
energies adding up. Brezis–Coron: the analogous statement for $H$-systems (constant mean curvature
surfaces), the first "bubbling" theorem stated as such. *Sources:* Struwe, Math. Z. 187 (1984);
Brezis–Coron, CPAM 37 (1984), CMP 92 (1985); Brezis–Nirenberg, CPAM 36 (1983) for the subcritical
perturbation. *Needs:* T5, T8′, T9, E1, the Pohozaev identity, the classification of positive
solutions on $\mathbb R^n$ (Gidas–Ni–Nirenberg, Caffarelli–Gidas–Spruck; itself an M–L task via
the moving plane method). *Needed by:* V2, V3, and every "energy quantization" argument. **L.**

**V2. Bahri–Coron: critical points at infinity.** If a bounded domain $\Omega \subseteq \mathbb R^n$
has $H_d(\Omega; \mathbb Z/2) \ne 0$ for some $d \ge 1$, then $-\Delta u = u^{(n+2)/(n-2)}$, $u > 0$,
$u|_{\partial\Omega} = 0$ has a solution. The proof studies the sublevel sets of $E$ on the unit
sphere of $\dot H^1_0$, shows via T10 that the only obstruction to compactness is the "critical
points at infinity" (configurations of bubbles at points of $\Omega$), computes their contribution
to the topology of the level sets by an explicit expansion of $E$ and its gradient near such
configurations (the *Morse lemma at infinity*), and derives a contradiction from the topology of
$\Omega$. *Sources:* Bahri–Coron, CPAM 41 (1988); Coron, CRAS 299 (1984) for domains with a small
hole; Bahri, *Critical points at infinity in some variational problems*, Pitman 182 (1989), for the
general theory; Rey, JFA 89 (1990) for the role of the Green function. *Needs:* T10, V1, T4 with
sharp constants and the explicit bubbles, singular homology of the domain and of level sets (Mathlib
has singular homology only in nascent form; *check*), the expansion estimates. *Needed by:* V3, the
Bahri–Coron scalar curvature theorem on $S^3$ (JFA 95, 1991), Bahri's contact form theory. *Notes:*
this is the flagship of Track I because it is exactly the kind of proof a machine should check: long
explicit expansions with error terms whose constants depend on the configuration, and a topological
argument that must be stated precisely. Plan the algebraic-topology input separately. **L.**

**V3. Bahri–Lions: Morse indices of Palais–Smale sequences.** For superlinear subcritical problems
$-\Delta u = f(u)$, bounds on the Morse index of a sequence of solutions give $L^\infty$ bounds,
hence compactness; conversely the Morse index of critical points obtained by min-max is controlled.
*Sources:* Bahri–Lions, CPAM 45 (1992); Bahri–Lions, Ann. IHP 14 (1997) for unbounded domains.
*Needs:* T10-type blow-up analysis, spectral theory of Schrödinger operators (Mathlib has the
spectral theorem for compact self-adjoint operators; *check* for unbounded operators), Liouville
theorems. **M–L.**

**V4. Bahri's variational theory of contact forms; Bahri–Rabinowitz.** The action functional on
the space of Legendrian-type curves, its critical points (Reeb periodic orbits) and its critical
points at infinity (pseudo-orbits); Bahri–Rabinowitz on periodic solutions of Hamiltonian systems of
three-body type via critical points at infinity. *Sources:* Bahri, *Pseudo-orbits of contact forms*
(1988); *Flow lines and algebraic invariants in contact form geometry* (2003); Bahri–Rabinowitz,
Ann. IHP 8 (1991). *Needs:* V1, Hilbert manifolds of loops, ODE, contact geometry (absent). *Note:*
this is where Track I meets Track II from the variational side; it is the road not taken by most
of the field after Hofer 1993, and precisely for that reason it is under-verified. **L.**

**V5. Compactness of the Yamabe problem (Schoen's conjecture).** The set of solutions of the Yamabe
equation on a compact manifold not conformally equivalent to the sphere is compact in $C^2$, for
$n \le 24$; false for $n \ge 25$. *Sources:* Schoen (1991) conjecture and the locally conformally
flat case; Li–Zhu (1999) $n = 3$; Druet (2004) $n \le 5$; Marques (2005) $n \le 7$; Li–Zhang
(2005–07) $n \le 11$; Khuri–Marques–Schoen, JDG 81 (2009) $n \le 24$; Brendle, JAMS 21 (2008)
counterexamples $n \ge 52$; Brendle–Marques, JDG 81 (2009) $25 \le n \le 51$. *Needs:* T10-type
blow-up analysis on manifolds (G1, E1), the positive mass theorem (itself XL), Weyl tensor
expansions. *Note:* the cleanest example of a compactness statement whose truth depends on the
dimension in a nontrivial way; the counterexamples are explicit and would be a striking
formalization target on their own (they are finite-dimensional calculus). **XL (theorem), L
(counterexamples).**

### C. Dispersive equations

**P1. Strichartz estimates and critical local well-posedness.** $\|e^{it\Delta}f\|_{L^q_tL^r_x} \le
C\|f\|_{L^2}$ for admissible $(q,r)$; local existence for energy-critical NLS in $\dot H^1$.
*Sources:* Strichartz (1977), Ginibre–Velo, Keel–Tao (1998). *Needs:* Fourier transform on
$L^2$ (Mathlib has the Fourier transform on Schwartz space and $L^2$ Plancherel; *check*), the
$TT^*$ argument, dispersive estimate. **M.**

**P2. Kenig–Merle: concentration-compactness and rigidity.** For the focusing energy-critical NLS in
dimensions $3, 4, 5$, radial data with energy below the ground state's scatter; proof: if not, a
minimal-energy blow-up solution exists whose orbit is precompact modulo scaling (by T9 and
P1), and a localized virial identity shows no such solution exists. *Sources:* Kenig–Merle, Invent.
Math. 166 (2006); Acta Math. 201 (2008) for the wave equation. *Needs:* T9, P1, the virial identity.
*Needed by:* the whole "induction on energy" and "minimal counterexample" method (Bourgain 1999;
Colliander–Keel–Staffilani–Takaoka–Tao 2008; Killip–Visan). *Note:* the structure (extract a
minimal almost-periodic counterexample, then exclude it) is the same as V2's and S2's; a
formalization of the extraction step would serve all three. **L.**

**P3. Merle–Raphaël: blow-up for the $L^2$-critical NLS.** Solutions slightly above the ground-state
mass with negative energy blow up with the log-log rate, and the blow-up profile is the ground state.
*Sources:* Merle–Raphaël, Ann. Math. 161 (2005) and the series 2003–2006. *Needs:* P1, modulation
theory, the spectral property of the linearized operator (checked numerically in the original;
later proved rigorously in low dimensions). *Note:* included because it is the paradigm for the
recent blow-up results; the numerically verified spectral input is a natural thing to
formalize with interval arithmetic. **L–XL.**

### D. Geometric analysis and gauge theory

**G1. Analysis on Riemannian manifolds.** Riemannian metrics, volume, Levi-Civita connection,
Laplace–Beltrami, Sobolev spaces on compact manifolds, elliptic regularity there, harmonic
coordinates (Jost–Karcher 1982; Anderson 1990). *Mathlib:* smooth manifolds, vector bundles and
connections are present; Riemannian metrics are recent and partial; no Laplacian (*check*). *Needed
by:* T11–T14, V5, S1–S7. **L.**

**T11. Sacks–Uhlenbeck; bubble trees; energy identity.** A sequence of harmonic maps (or
$\alpha$-harmonic approximations) from a closed surface with bounded energy has a subsequence
converging in $C^\infty$ away from finitely many points, where bubbles (harmonic spheres) form; the
energy is conserved in the limit (Ding–Tian 1995; Parker 1996 bubble tree with necks). Existence of
minimizing harmonic spheres in a manifold with nontrivial $\pi_2$. *Sources:* Sacks–Uhlenbeck, Ann.
Math. 113 (1981); Parker, JDG 44 (1996); Ding–Tian, CAG 3 (1995); Schoen–Uhlenbeck, JDG 17 (1982)
for regularity in higher dimensions; Hélein (1990) for regularity in two dimensions; Rivière,
Invent. Math. 168 (2007) for conservation laws. *Needs:* E1 ($\varepsilon$-regularity, removable
singularities), G1, T5. *Needed by:* S1 (same analysis with the Cauchy–Riemann operator replacing
the harmonic map operator). **L.**

**G2. Principal bundles, connections, curvature, gauge transformations, characteristic classes.**
*Mathlib:* vector bundles yes, principal bundles and gauge groups no (*check*). **M–L.**

**T12. Uhlenbeck compactness; Coulomb gauge; removable singularities.** Connections on a bundle
over a compact $n$-manifold with $\|F_A\|_{L^p} \le C$, $p > n/2$, have a subsequence which, after
gauge transformations, converges weakly in $W^{1,p}$; a connection with small $L^{n/2}$ curvature on
a ball admits a Coulomb gauge with $W^{1,p}$ control; a finite-energy Yang–Mills connection on a
punctured 4-ball extends. *Sources:* Uhlenbeck, CMP 83 (1982), two papers; Sedlacek (1982) for the
weak compactness with bubbling; Wehrheim's book *Uhlenbeck Compactness* (2004) for a complete
exposition, which is the text to formalize. *Needs:* E1, G2, T4. *Needed by:* Donaldson theory,
Taubes' gluing, Floer's instanton homology. **L–XL.**

**T12′. Tian's compactness for Yang–Mills in higher dimensions.** Sequences of Yang–Mills
connections with bounded energy on an $n$-manifold, $n \ge 5$, converge away from a closed set of
codimension at least four which is rectifiable. *Source:* Tian, Ann. Math. 151 (2000). *Needs:*
T12, GMT. **XL.**

**SW. Seiberg–Witten compactness.** For a closed 4-manifold with a spin$^c$ structure, the moduli
space of solutions of the Seiberg–Witten equations is compact; the proof is an a priori $C^0$ bound
on the spinor from the maximum principle and the Weitzenböck formula, followed by elliptic
bootstrapping. *Sources:* Witten (1994); Kronheimer–Mrowka (1994); Morgan's book (1996). *Needs:*
G2, spinors and Dirac operators, E1 (light: $L^2$ theory and bootstrapping suffice). *Needed by:*
S7, Seiberg–Witten invariants. *Note:* the cheapest compactness theorem in gauge theory and the
best first geometric target in block D after T11; no bubbling analysis at all. **M–L.**

**GMT. Federer–Fleming compactness; Allard regularity.** Integral $k$-currents in $\mathbb R^n$ with
bounded mass and boundary mass form a compact set in the flat norm topology (Federer–Fleming 1960;
the closure theorem). A stationary integral varifold whose density is close to one in a ball is a
$C^{1,\alpha}$ graph there (Allard 1972). *Needs:* Hausdorff measures (in Mathlib), rectifiable
sets, the deformation theorem, area and coarea formulas (absent). *Needed by:* existence of
minimal surfaces (Plateau's problem), Almgren–Pitts min-max, De Lellis–Spadaro regularity theory.
**L–XL.**

**GMT′. Compactness for minimal surfaces.** Choi–Schoen (1985): embedded minimal surfaces of fixed
genus in a 3-manifold with positive Ricci curvature form a compact set in $C^k$. Colding–Minicozzi:
compactness for embedded minimal disks without area bounds. *Needs:* GMT, G1, E1. **L.**

**T14. Cheeger–Gromov and Hamilton compactness.** Riemannian $n$-manifolds with $|\mathrm{Rm}| \le
K$, injectivity radius $\ge i_0$ and diameter $\le D$ subconverge in $C^{1,\alpha}$ to a $C^{1,\alpha}$
manifold, up to diffeomorphism (Cheeger 1970; Gromov 1981; Greene–Wu, Peters 1987 for the $C^{1,\alpha}$
statement via harmonic coordinates, Anderson 1990); with bounds on all derivatives of curvature,
smooth convergence, and Hamilton's version (1995) for sequences of Ricci flows. Cheeger–Colding
(1997–2000): structure of limits under Ricci lower bounds alone. *Needs:* G1 (harmonic radius),
E1, T2′. *Needed by:* Perelman's work, Ricci flow with surgery, the study of Ricci limit spaces.
**XL.**

### E. Symplectic and contact topology

**S1. Gromov compactness.** A sequence of $J_k$-holomorphic maps from closed Riemann surfaces of
fixed genus to a compact symplectic manifold with $J_k \to J$ and bounded energy has a subsequence
converging, in the Gromov topology, to a stable $J$-holomorphic map (a nodal curve with a map,
with finite automorphism group). *Sources:* Gromov, Invent. Math. 82 (1985); Ye, Trans. AMS 342
(1994); Parker–Wolfson, JGA 3 (1993); Hummel, *Gromov's compactness theorem for pseudo-holomorphic
curves* (1997); McDuff–Salamon, *$J$-holomorphic curves and symplectic topology*, Ch. 4–5 (2004).
*Needs:* T11-type $\varepsilon$-regularity and removable singularities for the Cauchy–Riemann
operator, the monotonicity lemma, the Deligne–Mumford compactification of the moduli of stable
curves (algebraic geometry or hyperbolic geometry input, absent), G1. *Needed by:* S2, S4–S6, F4,
F5, every Gromov–Witten or Floer-type invariant. *Notes:* the waist of Track II. Formalize
McDuff–Salamon's exposition, which separates the analysis (Chapter 4) from the bookkeeping of
nodal curves (Chapter 5). The genus-zero case needs no Deligne–Mumford theory beyond trees of
spheres and should be done first. **XL (L for genus zero).**

**S1′. Gromov's nonsqueezing theorem.** A symplectic embedding $B^{2n}(r) \to B^2(R) \times
\mathbb R^{2n-2}$ exists only if $r \le R$. *Proof:* S1 in genus zero on $S^2 \times T^{2n-2}$ plus
the monotonicity lemma. *Note:* the natural first application of S1 with a headline statement. **L
(given S1 genus zero).**

**S2. Hofer: finite-energy planes and the Weinstein conjecture in dimension three.** For a
contact form on a closed 3-manifold with an overtwisted contact structure, or with $\pi_2 \ne 0$,
or on $S^3$, the Reeb vector field has a periodic orbit. *Proof:* study $J$-holomorphic planes in
the symplectization $\mathbb R \times M$ with finite Hofer energy; show by a bubbling-off analysis
that a family of holomorphic discs with boundary on an overtwisted disc (Bishop family) must break,
producing a finite-energy plane; show that a finite-energy plane is asymptotic to a periodic Reeb
orbit. *Source:* Hofer, Invent. Math. 114 (1993). *Needs:* S1-type analysis on non-compact domains
with the energy identity for the symplectization, V1-type geometry for the Bishop family, contact
geometry, the asymptotic analysis of S3 (in its first form). *Needed by:* S3, S4, S7. *Note:* the
compactness-plus-bubbling structure is identical to T10 and P2; the new ingredient is the
non-compact target and the energy that controls it. **L–XL.**

**S3. Hofer–Wysocki–Zehnder asymptotics; finite-energy foliations.** A finite-energy
$J$-holomorphic half-cylinder in a symplectization converges exponentially to a Reeb orbit, with
leading term an eigenfunction of the asymptotic operator $-J_0\partial_t - S(t)$; consequences for
the intersection theory of such curves; existence of finite-energy foliations of $S^3$ and of global
surfaces of section for dynamically convex Reeb flows. *Sources:* HWZ, Ann. IHP 13 (1996); GAFA 5
(1995); Ann. Math. 148 (1998) for strictly convex energy surfaces; Ann. Math. 157 (2003) for finite
energy foliations; Siefring (2008–11) for relative asymptotics. *Needs:* S2, spectral theory of the
asymptotic operator (unbounded self-adjoint on $L^2(S^1)$; *check* Mathlib). *Needed by:* S4, S7,
embedded contact homology. **L.**

**S4. SFT compactness.** Let $(W, \omega)$ be a symplectic cobordism with cylindrical ends and $J$
cylindrical at infinity. A sequence of finite-energy punctured $J$-holomorphic curves of bounded
energy and bounded genus has a subsequence converging to a *holomorphic building*: finitely many
levels, each a nodal punctured curve in $W$ or in a symplectization of an end, matched along Reeb
orbits at the punctures, with the total energy and topology controlled. *Source:* Bourgeois–
Eliashberg–Hofer–Wysocki–Zehnder, Geom. Topol. 7 (2003); Cieliebak–Mohnke, JSG 3 (2005) for the
compactness in the Deligne–Mumford setting with the Reeb dynamics not Morse–Bott. *Needs:* S1
(with punctures), S2, S3, Deligne–Mumford with marked points and the hyperbolic-geometry
description of degenerations (thick–thin decomposition), the "level structure" bookkeeping.
*Needed by:* contact homology, SFT (Eliashberg–Givental–Hofer 2000), F4 for SFT. *Notes:* the
summit of the compactness track; the statement itself is a page long and its precise formulation
(the topology on the space of buildings) is one of the things a blueprint must settle. **XL.**

**S5. Hofer–Zehnder capacity; energy–capacity inequality.** Definition of $c_{HZ}$ via Hamiltonians
with no fast periodic orbits; $c_{HZ}(B^{2n}(r)) = \pi r^2$; the displacement energy bounds the
capacity. *Sources:* Hofer–Zehnder (1990, book 1994); Hofer's displacement energy (1990); Lalonde–
McDuff (1995) via S1. *Needs:* V1-type variational theory for the action functional (the original
proof) or S1 (the holomorphic proof). **L.**

**S6. Floer compactness and gluing.** Solutions of the Floer equation $\partial_s u + J(\partial_t u -
X_H(u)) = 0$ on the cylinder with bounded energy converge, modulo $s$-translation, to broken
trajectories; gluing produces a trajectory from a broken one; the boundary of the one-dimensional
moduli space is the set of once-broken trajectories, giving $\partial^2 = 0$. *Sources:* Floer, CMP
118 (1988), JDG 28 (1988), CMP 120 (1989); Hofer–Salamon (1995); Salamon's Park City lectures
(1999); Audin–Damian's book (2014), the most complete exposition and the one to formalize. *Needs:*
S1-type analysis on cylinders, E1, E2 (Fredholm theory of the linearized operator, spectral flow),
transversality (Floer–Hofer–Salamon 1995). *Needed by:* Floer homology, the Arnold conjecture (in the
monotone/semipositive case). **L–XL.**

**S7. Taubes: the Weinstein conjecture in dimension three.** Every contact form on a closed
3-manifold has a periodic Reeb orbit. *Proof:* solutions of the Seiberg–Witten equations with a
large parameter $r$ exist by Kronheimer–Mrowka's nonvanishing of monopole Floer homology, and as
$r \to \infty$ the spinor's zero set concentrates on a union of Reeb orbits. *Source:* Taubes, Geom.
Topol. 11 (2007). *Needs:* SW, S3-type asymptotic analysis, monopole Floer homology (Kronheimer–
Mrowka's book, XL). **XL.**

### F. Foundations of moduli spaces

**F1. sc-calculus.** An sc-Banach space is a Banach space $E = E_0$ with a decreasing sequence of
Banach subspaces $E_0 \supseteq E_1 \supseteq \cdots$, each inclusion $E_{m+1} \to E_m$ compact and
$E_\infty = \bigcap E_m$ dense in each $E_m$. A map $f : U \to F$ between open subsets of sc-Banach
spaces is sc$^0$ if it maps $U_m := U \cap E_m$ continuously to $F_m$ for all $m$; sc$^1$ if for
each $x \in U_1$ there is a bounded linear $Df(x) : E_0 \to F_0$ with $\|f(x+h) - f(x) -
Df(x)h\|_{F_0} = o(\|h\|_{E_1})$, and the tangent map $Tf : TU \to TF$, $Tf(x, h) = (f(x), Df(x)h)$
on $TU = U_1 \oplus E_0$ (the shifted scale) is sc$^0$; sc$^\infty$ by iteration. Theorems: the
sc-chain rule; sc-smooth maps that are classically smooth level-wise; the basic examples (shift
maps, action of reparametrization on $W^{k,p}$ scales). *Sources:* HWZ, JEMS 9 (2007), §2; HWZ,
*Polyfold and Fredholm Theory* (2021), Ch. 1; Fabert–Fish–Golovko–Wehrheim, *Polyfolds: a first and
second look* (EMS Surv. 2016), the friendliest entry point. *Needs:* Banach spaces, compact
operators (in Mathlib). *Needed by:* F2–F4. *Notes:* the ideal opening target of Track II: no
geometry, definitions are the content, the chain rule's proof is genuinely delicate (it uses the
compactness of the inclusions and the shift of levels), and the classical counterexamples (the
reparametrization action is not $C^1$ on a single Banach space but is sc-smooth on a scale) can be
formalized as sanity checks. **S–M.**

**F2. sc-retractions, splicings, M-polyfolds.** An sc-smooth retraction $r : U \to U$ ($r \circ r
= r$) has image $O = r(U)$, a *local model*; the tangent space $T_xO = \operatorname{im} Dr(x)$ can
change dimension from point to point; sc-smoothness of maps between local models is well defined
(independent of the retraction); M-polyfolds are spaces locally modelled on such $O$, with
boundary and corners; splicings as the standard way to build retractions from a family of
projections (the gluing profile). *Sources:* HWZ (2007) §3–4; HWZ, *sc-smoothness, retractions and
new models for smooth spaces*, DCDS 28 (2010); the 2021 book Ch. 2. *Needs:* F1. *Needed by:* F3,
F4. *Note:* the independence of the smooth structure from the retraction is the key theorem and
the natural second milestone. **M–L.**

**F3. Polyfold Fredholm theory.** Strong bundles over M-polyfolds; sc-Fredholm sections (defined via
a filled-in local normal form: after a change of coordinates, the section is a classical Fredholm
map plus a "contraction germ"); the sc-implicit function theorem (a regular sc-Fredholm section has
a solution set that is a finite-dimensional manifold with boundary and corners, of the expected
dimension); properness and compactness of solution sets; the perturbation theorem (for a proper
sc-Fredholm section with compact zero set there exist sc$^+$-multisection perturbations making the
section transverse, with the perturbed zero set a compact weighted branched orbifold, unique up to
cobordism); orientations. *Sources:* HWZ, GAFA 19 (2009) (implicit function theorems); Geom. Topol.
13 (2009) (Fredholm functors, polyfolds); *Integration theory on the zero sets of polyfold Fredholm
sections*, Math. Ann. 346 (2010); the 2021 book Parts II–III. *Needs:* F1, F2, E2, Sard–Smale,
orbifold-type quotients (ep-groupoids). *Needed by:* F4 and its applications: the Arnold conjecture
in full generality via polyfolds (Filippenko–Wehrheim 2022), Gromov–Witten invariants for general
symplectic manifolds. *Notes:* this is the body of theory whose independent verification the field
would most welcome; it is long (the book is about 1,000 pages), uniform in style, and its
difficulties are of bookkeeping and estimates rather than of ideas, which is the profile a machine
handles best. **L–XL.**

**F4. Polyfolds of Gromov–Witten theory and of SFT.** The space of stable maps of a given genus and
homology class into a compact symplectic manifold carries the structure of an M-polyfold (more
precisely, an ep-groupoid) built from splicings that implement gluing at nodes with an exponential
gluing profile; the Cauchy–Riemann operator is an sc-Fredholm section of a strong bundle over it;
its zero set is the compact Gromov–Witten moduli space; F3 then gives the virtual fundamental class
and the Gromov–Witten invariants. For SFT, the same with holomorphic buildings. *Sources:* HWZ,
*Applications of polyfold theory I: the polyfolds of Gromov–Witten theory*, Mem. AMS 248 (2017);
Fish–Hofer, *Lectures on polyfolds and symplectic field theory* (2018) and the sequence of papers
towards the SFT polyfolds. *Needs:* F3, S1 (resp. S4), Deligne–Mumford. **XL.**

**F5. The alternative frameworks.** *Kuranishi structures* (Fukaya–Ono, Topology 38, 1999; FOOO,
*Lagrangian intersection Floer theory*, AMS/IP 2009; FOOO, *Kuranishi structures and virtual
fundamental chains*, Springer 2020): finite-dimensional charts $(V, E, \Gamma, s, \psi)$ with an
obstruction bundle, coordinate changes, and a virtual fundamental chain built from multisections.
*Kuranishi atlases* (McDuff–Wehrheim, Geom. Topol. 21 (2017), two papers): a reformulation designed
to expose and repair the topological difficulties in the original approach. *Implicit atlases*
(Pardon, Geom. Topol. 20 (2016); Pardon, Geom. Topol. 23 (2019) for contact homology): a homological
formulation in which the virtual fundamental class is constructed sheaf-theoretically from local
finite-dimensional reductions, avoiding the need for a global smooth structure. Also Li–Tian, Liu–
Tian, Ruan, Siebert (1996–99) for the semipositive-free virtual cycle, and Ionel–Parker's relative
theory. *Needs:* S1 and gluing analysis; algebraic topology (Čech cohomology, Steenrod homology).
*Notes:* the history of these frameworks (1996–2020), including the public debate over the
completeness of the early proofs and the decade of re-exposition that followed, is the strongest
argument in this document for machine verification: the community settled the question by
consensus, and a checked version of any one of these frameworks would replace consensus with
certainty. Pardon's is the most algebraic and may be the easiest to formalize once S1 and gluing
are in place; polyfolds are the one whose first half (F1–F3) can begin today. **L–XL each.**

### G. A count

Fifty-odd entries: 3 already in Mathlib (T1, T2, T2′), 6 of size S or S–M (D1, E2, T6, T7, F1, and
Ekeland's principle inside V1), 13 of size M or M–L, 16 of size L or L–XL, and the rest XL. The
S-sized entries are exactly the two beginnings recommended in §4: the measure-theoretic
concentration-compactness lemma and the sc-calculus.

---

## 3. The dependency graph

<div id="roadmap-graph"></div>

The graph shows the main entries of the tally (not every primed variant). It has two waists. In the analytic track, **T3 (Sobolev spaces) and T5 (Rellich–Kondrachov)**
are on the path to everything above them, and **E1 (elliptic regularity)** is on the path to
everything geometric. In the symplectic track, **S1 (Gromov compactness)** is on the path to
everything in blocks E and F except the sc-calculus itself, while **F1–F2 (sc-calculus and
M-polyfolds)** depend on nothing but Banach space theory and can be started on day one.

---

## 4. Order of attack: two tracks

### Track I: analysis

**Milestone 0 (weeks): the measure-theoretic core.** Formalize T6 and T7. Both are short, both
are used everywhere, and both can be stated and proved with what Mathlib has. Lions's lemma I is a
theorem about sequences of probability measures on $\mathbb R^n$ with the concentration function
$Q_k(R) = \sup_y \mu_k(B(y,R))$; its proof is a diagonal argument and a splitting by a cutoff,
exactly what a proof assistant handles well and humans get wrong in the details. Success is a first
machine-checked concentration-compactness statement, and a calibration of cost.

**Milestone 1 (months): Sobolev spaces on $\mathbb R^n$ and bounded domains.** T3, T4, T5, and the
Banach-space Fredholm and implicit function theory E2 (much of which is a matter of bundling what
Mathlib has). Design decisions to make once and early:

* Functions versus equivalence classes: Mathlib's $L^p$ spaces are quotients; define weak
  derivatives on the quotient via the distributional pairing and $W^{k,p}$ as a subtype of $L^p$.
* Domains: begin with $\mathbb R^n$ and open sets; prove extension for Lipschitz domains later.
* Rellich–Kondrachov via the Kolmogorov–Riesz–Fréchet criterion for compactness in $L^p$, a
  reusable theorem in its own right.

**Milestone 2 (months): variational compactness.** V1 (mountain pass with the deformation lemma),
T8, then T9. These need only Milestone 1 and are the theorems most often called "well known" and
least often written down in full.

**Milestone 3 (a year): elliptic regularity and the first bubbling theorems.** E1 for the
semilinear equation $-\Delta u = |u|^{2^*-2}u$, then T10 (Struwe; Brezis–Coron). This is the first
theorem a geometer recognizes as geometric analysis. **Then V2, Bahri–Coron.** It is the natural
first target in the critical-points-at-infinity line because it is a complete, celebrated theorem
whose proof is an explicit computation of the topology of the set of bubble configurations, and the
gluing and expansion estimates it needs are exactly the kind of long, error-prone analysis where a
machine check has value. V3 (Bahri–Lions) follows with the same tools plus spectral theory.

**Milestone 4 (years): manifolds and gauge theory.** G1, then T11 (Sacks–Uhlenbeck), then G2 and
**SW before T12**: Seiberg–Witten compactness is a maximum-principle argument and is the cheapest
compactness theorem in gauge theory, while Uhlenbeck's needs the full Coulomb gauge machinery. T14
and GMT are separate branches.

### Track II: symplectic and contact topology

**Milestone S0 (weeks to months): the sc-calculus.** F1 needs nothing but Banach spaces:
sc-Banach spaces are decreasing scales $E_0 \supseteq E_1 \supseteq \cdots$ with compact inclusions;
sc-continuity, sc$^1$ and sc-smoothness are definitions; the sc-chain rule is the first theorem, and
it is a theorem with a subtle proof (the tangent map lives on the shifted scale). This is a
perfect first formalization target: it is the foundation of a large theory, its definitions are the
content, it is short, and it has never been checked by machine. It also provides a calibration of
how well agents handle Hofer–Wysocki–Zehnder's style of argument before committing to F3.

**Milestone S1 (months): sc-retractions and M-polyfolds.** F2. The key results are that
sc-smooth retractions have well-defined tangent spaces (which vary in dimension), that the models
are stable under sc-diffeomorphism, and the basic splicing constructions. Still no geometry: this
is functional analysis with a new smoothness notion.

**Milestone S2 (a year or more): polyfold Fredholm theory.** F3: strong bundles, sc-Fredholm
sections, the sc-implicit function theorem, and the perturbation theorem. This is the heart of the
2021 book. Formalizing it would settle, by a means everyone accepts, a body of foundations that
the field relies on and that only a handful of people have read in full. It is also where the
machine's advantages are largest: the arguments are long, uniform, and combinatorially intricate
(boundary and corner strata, the "gluing profile"), and not conceptually deep in the way S1 is.

**Milestone S3 (years): the geometric input.** S1 (Gromov compactness) first, then F4 for
Gromov–Witten theory (HWZ 2017), which is the first place where compactness (S1) and the Fredholm
theory (F3) meet and produce an invariant. Then S2 and S3 (Hofer's finite-energy planes and the
HWZ asymptotics), which are the entry to the contact world, and S4 (SFT compactness) as the summit
of the compactness track. S6 (Floer) can run in parallel once S1-type analysis on cylinders exists.

**On the alternative frameworks (F5).** Kuranishi structures and implicit atlases are as
legitimate as polyfolds, and a lab whose interest is Lagrangian Floer theory rather than SFT should
weigh Fukaya–Oh–Ohta–Ono's or Pardon's route. Pardon's implicit atlases are the most algebraic and
may formalize most cleanly once S1 and gluing are in hand; polyfolds have the advantage that their
first half (F1–F3) needs no geometry at all and can begin today. In any case the analytic core
(S1 and gluing) is shared, and it is the expensive part.

---

## 5. How to run it

**Statements first, checked by a human, then proofs by agents.** The lesson of the Milnor project
that accompanies this document: the theorem statements were the bottleneck and the proofs were
not. The human mathematician's job is to write, in ordinary language, exactly what each theorem
says, including the hypotheses that textbooks omit (which subsequence, which topology, which
normalization, which gluing profile); the formal statement is then written and read back in prose
for sign-off; only then are proofs generated. A Lean blueprint (a dependency graph of statements
with informal proofs) is the right artefact, and it is what a lab without compute can produce and a
lab with compute cannot produce without a mathematician.

**State over abstract spaces, not $\mathbb R^n$ with coordinates.** Sard's theorem in the Milnor
project was stated for arbitrary finite-dimensional normed spaces and Haar measures because the
induction passes to hyperplanes. Sobolev theory and the sc-calculus present the same choice; the
sc-calculus in particular is *defined* over abstract Banach scales and should stay there.

**Choose the proof that formalizes, not the proof in the textbook.** Milnor's cube counting for
Sard's Step 3 became "Hölder maps divide Hausdorff dimension", which Mathlib had. Expect the same:
Kolmogorov–Riesz instead of diagonal extraction; Brezis–Lieb from Fatou and uniform integrability;
profile decompositions by induction on the energy defect; for Gromov compactness, Hummel's or
McDuff–Salamon's exposition rather than the original.

**Expect the work to be in the infrastructure.** Two thirds of the Milnor project's lines were
infrastructure Mathlib lacked. For Track I it is Sobolev spaces and elliptic regularity; for Track II
it is Riemann surfaces with their degenerations and the analysis of the Cauchy–Riemann operator on
punctured surfaces. Plan, budget, and publish these as library contributions in their own right.

**What is not worth doing first.** Cheeger–Gromov, SFT compactness, Uhlenbeck compactness and the
polyfolds of SFT are the most famous entries and the worst places to start: each needs a large body
of geometry that does not yet exist in any library. A group that begins at the top will spend its
first years on preliminaries. A group that begins at the bottom (T6, T7, F1) will have checked
theorems in weeks, a checked bubbling theorem and a checked sc-calculus within a year, and will
have built, along the way, what everyone else needs.

---

## 6. What the mathematician can do without compute

1. Write the blueprint for Milestones 0–1 and S0–S1: precise statements of T3–T7 and F1–F2 with
   all hypotheses, informal proofs chosen for formalizability, and the dependency graph.
2. Decide the design questions of §4 (quotients versus functions; domains; the compactness
   criterion; the definition of sc-smoothness to adopt from the several equivalent ones in the
   literature) and record the reasons.
3. Write the prose statements a formalizer will be asked to match, in the format used in the
   chapters of this project: a theorem, a list of what is silently assumed, and what it is for.
4. Pick the headline theorem each track should deliver first with a physical or geometric meaning:
   for Track I, Bahri–Coron or the existence of a ground state for a nonlinear Schrödinger equation;
   for Track II, the polyfold Fredholm theory itself, whose verification the field would welcome.

That is a document of perhaps eighty pages. It is the part of the project that requires a
mathematician and not a machine, and it is what the labs do not have.

---

## 7. Selected references

Bahri, *Critical points at infinity in some variational problems* (1989). Bahri–Coron, CPAM 41
(1988). Bahri–Lions, CPAM 45 (1992). Bahri–Rabinowitz, Ann. IHP 8 (1991). Bahri, *Flow lines and
algebraic invariants in contact form geometry* (2003). Lions, Ann. IHP 1 (1984), Rev. Mat. Iberoam.
1 (1985). Struwe, Math. Z. 187 (1984). Brezis–Coron, CPAM 37 (1984) and CMP 92 (1985). Sacks–
Uhlenbeck, Ann. Math. 113 (1981). Uhlenbeck, CMP 83 (1982), two papers. Gérard, ESAIM COCV 3 (1998).
Bahouri–Gérard, Amer. J. Math. 121 (1999). Kenig–Merle, Invent. Math. 166 (2006). Gromov, Invent.
Math. 82 (1985). Hofer, Invent. Math. 114 (1993). Hofer–Wysocki–Zehnder, Ann. IHP 13 (1996), GAFA 5
(1995), and sequels. Bourgeois–Eliashberg–Hofer–Wysocki–Zehnder, Geom. Topol. 7 (2003).
Hofer–Wysocki–Zehnder, JEMS 9 (2007), GAFA 19 (2009), Geom. Topol. 13 (2009); *Polyfold and Fredholm
Theory*, Springer (2021); *Applications of polyfold theory I*, Mem. AMS (2017). Fish–Hofer, *Lectures
on polyfolds and symplectic field theory* (2018). Fukaya–Oh–Ohta–Ono, *Lagrangian intersection Floer
theory* (2009), *Kuranishi structures and virtual fundamental chains* (2020). McDuff–Wehrheim,
Geom. Topol. 21 (2017). Pardon, Geom. Topol. 20 (2016). Taubes, Geom. Topol. 11 (2007). Hofer–
Zehnder, *Symplectic invariants and Hamiltonian dynamics* (1994). Federer–Fleming, Ann. Math. 72
(1960). Allard, Ann. Math. 95 (1972). Hamilton, Amer. J. Math. 117 (1995).
