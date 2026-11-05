### Milnor.IsSliceSubmanifold  (Milnor.Chapter2.Submanifold)
{E : Type u_1} →
  [inst : NormedAddCommGroup E] →
    [inst_1 : NormedSpace ℝ E] →
      {H : Type u_2} →
        [inst_2 : TopologicalSpace H] →
          ModelWithCorners ℝ E H →
            {M : Type u_3} →
              [inst : TopologicalSpace M] →
                [ChartedSpace H M] →
                  (Z : Type u_4) →
                    [inst : NormedAddCommGroup Z] →
                      [NormedSpace ℝ Z] →
                        (W : Type u_5) → [inst : NormedAddCommGroup W] → [NormedSpace ℝ W] → Set M → Prop
`S` is a submanifold modelled on `Z` if every point of `S` lies in the domain of a slice
chart.


### Milnor.SliceChart  (Milnor.Chapter2.Submanifold)
{E : Type u_1} →
  [inst : NormedAddCommGroup E] →
    [inst_1 : NormedSpace ℝ E] →
      {H : Type u_2} →
        [inst_2 : TopologicalSpace H] →
          ModelWithCorners ℝ E H →
            {M : Type u_3} →
              [inst : TopologicalSpace M] →
                [ChartedSpace H M] →
                  (Z : Type u_4) →
                    [inst : NormedAddCommGroup Z] →
                      [NormedSpace ℝ Z] →
                        (W : Type u_5) →
                          [inst : NormedAddCommGroup W] → [NormedSpace ℝ W] → Set M → Type (max (max u_3 u_4) u_5)
A **slice chart** for `S ⊆ M`: a diffeomorphism `φ` from an open subset of `M` onto an open
subset of `Z × W` such that, on its domain, `S` corresponds exactly to `Z × {0}`. It comes with a
base point `x₀ ∈ S` in its domain.


### Milnor.Sphere.Sph  (Milnor.Chapter5.HairyBall)
(n : ℕ) → Set (EuclideanSpace ℝ (Fin (n + 1)))
The unit sphere `Sⁿ ⊆ ℝⁿ⁺¹`, as a set.


### Milnor.Sphere.sphG  (Milnor.Chapter5.HairyBall)
{n : ℕ} → EuclideanSpace ℝ (Fin (n + 1)) → ℝ
The defining function of the unit sphere.


### Milnor.mfd  (Milnor.Chapter5.Orient)
{E : Type u_1} →
  [inst : NormedAddCommGroup E] →
    [inst_1 : NormedSpace ℝ E] →
      {H : Type u_2} →
        [inst_2 : TopologicalSpace H] →
          {M : Type u_3} →
            [inst_3 : TopologicalSpace M] →
              [ChartedSpace H M] →
                {F : Type u_4} →
                  [inst_5 : NormedAddCommGroup F] →
                    [inst_6 : NormedSpace ℝ F] →
                      {G : Type u_5} →
                        [inst_7 : TopologicalSpace G] →
                          {N : Type u_6} →
                            [inst_8 : TopologicalSpace N] →
                              [ChartedSpace G N] →
                                ModelWithCorners ℝ E H → ModelWithCorners ℝ F G → (M → N) → M → E →L[ℝ] F
`mfderiv I J f x`, typed as a linear map between the model spaces.


### Morse.MapTelRel  (Morse.Appendix.MappingTelescope)
(F : CategoryTheory.Functor ℕ TopCat) →
  (n : ℕ) × ↑(F.obj n) × ↑unitInterval → (n : ℕ) × ↑(F.obj n) × ↑unitInterval → Prop
The gluing relation of the mapping telescope: the top `(k, 1)` of the `n`-th block is the
bottom `(c_n(k), 0)` of the next one.


### Morse.MappingTelescope  (Morse.Appendix.MappingTelescope)
CategoryTheory.Functor ℕ TopCat → Type u
**The mapping telescope** of `F₀ → F₁ → F₂ → ⋯`: `⨆_n F_n × [0, 1]` with `(k, 1)_n` glued to
`(c_n(k), 0)_{n+1}`, with the quotient topology.


### Morse.tmap  (Morse.Appendix.MappingTelescope)
(F : CategoryTheory.Functor ℕ TopCat) → {m n : ℕ} → m ≤ n → C(↑(F.obj m), ↑(F.obj n))
The maps of the sequence: `F(m ≤ n) : F_m → F_n`.


### Morse.CellTower  (Morse.Appendix.MonotoneUnion)
(ℕ → List ℕ) → Type (u + 1)
**A countable cell complex, given by its finite stages** (the Lean model of the countable
CW-complexes of Theorem 17.3): `K₀` is an iterated adjunction space with cells `cells 0`, and
`K_{n+1}` is obtained from `K_n` by attaching the cells `cells (n + 1)`, the map `K_n → K_{n+1}`
being the inclusion.


### Morse.IsCountableCellComplexType  (Morse.Appendix.MonotoneUnion)
(X : Type u) → [TopologicalSpace X] → (ℕ → List ℕ) → Prop
**`X` has the homotopy type of a countable cell complex with cells `cells 0, cells 1, …`**
(attached in this order): `X` is homotopy equivalent to the mapping telescope of a cell tower with
these cells. The telescope stands for the union of the stages with the weak topology; the two are
homotopy equivalent by Example 2 of the Appendix (Whitehead's theorem), which is not formalized.


### Morse.IsRelCellAttachment  (Morse.Appendix.MonotoneUnion)
(L K : TopCat) → (L ⟶ K) → List ℕ → Prop
**Relative iterated adjunction spaces.** `IsRelCellAttachment L K j cells`: `K` is obtained
from `L` by attaching cells of the dimensions listed in `cells`, one at a time and in this order,
each along an arbitrary continuous map, and `j : L → K` is the composite of the inclusions
`K' → K' ∪_φ e^λ` (`Morse.cellInl`).


### Morse.IsHomotopyEquiv  (Morse.Appendix.Telescope)
{X : Type u_1} → {Y : Type u_2} → [inst : TopologicalSpace X] → [inst_1 : TopologicalSpace Y] → C(X, Y) → Prop
**`f` is a homotopy equivalence**: it has a homotopy inverse `g`, with `g ∘ f ≃ id` and
`f ∘ g ≃ id` (Milnor, p. 12). Mathlib's `ContinuousMap.HomotopyEquiv` is the corresponding
structure.


### Morse.IsCriticalPointM  (Morse.Chapter1.Manifold)
(E : Type u_1) →
  [inst : NormedAddCommGroup E] →
    [NormedSpace ℝ E] → {M : Type u_2} → [inst_2 : TopologicalSpace M] → [ChartedSpace E M] → (M → ℝ) → M → Prop
**Critical point** (Milnor, p. 4): `p` is a critical point of `f` if `f_* : TM_p → TR_{f(p)}`
is zero.


### Morse.IsNondegenerateCriticalPointM  (Morse.Chapter1.Manifold)
(E : Type u_1) →
  [inst : NormedAddCommGroup E] →
    [NormedSpace ℝ E] → {M : Type u_2} → [inst_2 : TopologicalSpace M] → [ChartedSpace E M] → (M → ℝ) → M → Prop
**Non-degenerate critical point** (Milnor, p. 4).


### Morse.hessianM  (Morse.Chapter1.Manifold)
(E : Type u_1) →
  [inst : NormedAddCommGroup E] →
    [inst_1 : NormedSpace ℝ E] →
      {M : Type u_2} → [inst_2 : TopologicalSpace M] → [ChartedSpace E M] → (M → ℝ) → M → E →L[ℝ] E →L[ℝ] ℝ
**The Hessian** `f_**` of `f` at `p` (Milnor, pp. 4–5), as a continuous bilinear form on
`TM_p = TangentSpace 𝓘(ℝ, E) p = E`: the second derivative of the local representative
`Morse.localRep E f p` at the image of `p` in the preferred chart.  It is chart independent at
critical points (`Morse.IsSmoothCoord.hessian_comp_symm`).


### Morse.indexM  (Morse.Chapter1.Manifold)
(E : Type u_1) →
  [inst : NormedAddCommGroup E] →
    [NormedSpace ℝ E] → {M : Type u_2} → [inst_2 : TopologicalSpace M] → [ChartedSpace E M] → (M → ℝ) → M → ℕ
**The index of `f` at `p`** (Milnor, p. 5): the index of the Hessian `f_**` on `TM_p`.


### Morse.localRep  (Morse.Chapter1.Manifold)
(E : Type u_1) →
  [inst : NormedAddCommGroup E] →
    [NormedSpace ℝ E] → {M : Type u_2} → [inst_2 : TopologicalSpace M] → [ChartedSpace E M] → (M → ℝ) → M → E → ℝ
**The local representative** of `f : M → ℝ` at `p`: `f` read in the preferred chart at `p`,
`f ∘ (extChartAt 𝓘(ℝ, E) p)⁻¹`, a function on `E` which is meaningful on the target of the chart
(an open neighbourhood of `extChartAt 𝓘(ℝ, E) p p`).


### Morse.tangentSubspace  (Morse.Chapter1.ManifoldSubmanifold)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : NormedSpace ℝ V] →
      {Z : Type u_2} →
        [inst_2 : NormedAddCommGroup Z] →
          [inst_3 : NormedSpace ℝ Z] →
            {W : Type u_3} →
              [inst_4 : NormedAddCommGroup W] →
                [inst_5 : NormedSpace ℝ W] →
                  {N : Set V} → Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N → ↑N → Submodule ℝ V
**The tangent space `T_qN` as a linear subspace of the ambient space** `V`: the range of the
derivative of the inclusion `N → V` at `q`.


### Morse.IsCriticalPoint  (Morse.Chapter1.Nondegenerate)
{E : Type u_1} → [inst : NormedAddCommGroup E] → [NormedSpace ℝ E] → (E → ℝ) → E → Prop
**Critical point** (Milnor, p. 4): `p` is a critical point of `f : E → ℝ` if `f` is
differentiable at `p` with derivative `0`.


### Morse.IsNondegenerate  (Morse.Chapter1.Nondegenerate)
{E : Type u_1} → [inst : NormedAddCommGroup E] → [inst_1 : NormedSpace ℝ E] → (E →L[ℝ] E →L[ℝ] ℝ) → Prop
**Non-degenerate** bilinear functional: nullity `0`, i.e. trivial null space.


### Morse.hessian  (Morse.Chapter1.Nondegenerate)
{E : Type u_1} → [inst : NormedAddCommGroup E] → [inst_1 : NormedSpace ℝ E] → (E → ℝ) → E → E →L[ℝ] E →L[ℝ] ℝ
**The Hessian** (Milnor, pp. 4–5): the second derivative `d²f_p`, as a continuous bilinear
form, `hessian f p v w = d(x ↦ df_x(w))_p(v)`.


### Morse.index  (Morse.Chapter1.Nondegenerate)
{E : Type u_1} → [inst : NormedAddCommGroup E] → [inst_1 : NormedSpace ℝ E] → (E →L[ℝ] E →L[ℝ] ℝ) → ℕ
**Index** (Milnor, p. 5): the maximal dimension of a subspace on which `H` is negative
definite.  This is Mathlib's `sigNeg` of the quadratic form `v ↦ H(v, v)`; see
`Morse.index_isGreatest` for the characterization in Milnor's words.


### Morse.nullSpace  (Morse.Chapter1.Nondegenerate)
{E : Type u_1} → [inst : NormedAddCommGroup E] → [inst_1 : NormedSpace ℝ E] → (E →L[ℝ] E →L[ℝ] ℝ) → Submodule ℝ E
**Null space** (Milnor, p. 5): the subspace of all `v` with `H(v, w) = 0` for every `w`.


### Morse.quadForm  (Morse.Chapter1.Nondegenerate)
{E : Type u_1} → [inst : NormedAddCommGroup E] → [inst_1 : NormedSpace ℝ E] → (E →L[ℝ] E →L[ℝ] ℝ) → QuadraticForm ℝ E
The quadratic form `v ↦ H(v, v)` of a continuous bilinear form.


### Morse.closedRiemBall  (Morse.Chapter10.Broken)
{V : Type u_1} → [inst : NormedAddCommGroup V] → [InnerProductSpace ℝ V] → Set V → V → ℝ → Set V
**The ball** `S = {x ∈ N : ρ(p, x) ≤ r}` (Milnor p. 89, with `r = √c`).


### Morse.PathC  (Morse.Chapter10.FullPathSpace)
{V : Type u_1} → [NormedAddCommGroup V] → Set V → V → V → Type u_1
`Ω*` as a type.


### Morse.PathSp.toC  (Morse.Chapter10.FullPathSpace)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] → {N : Set V} → {p q : V} → Morse.PathSp N p q → C(↑unitInterval, V)
The underlying continuous path `[0, 1] → V` of a piecewise smooth path.


### Morse.PathSp.toPathC  (Morse.Chapter10.FullPathSpace)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] → {N : Set V} → {p q : V} → Morse.PathSp N p q → Morse.PathC N p q
**The inclusion `i : Ω → Ω*`** (Milnor p. 93).


### Morse.pathCSet  (Morse.Chapter10.FullPathSpace)
{V : Type u_1} → [inst : NormedAddCommGroup V] → Set V → V → V → Set C(↑unitInterval, V)
**Milnor's `Ω* = Ω*(M; p, q)`** (p. 93): the continuous paths `[0, 1] → N` from `p` to `q`,
as a subspace of `C([0, 1], V)` with the compact-open (= uniform) topology.


### Morse.pathIncl  (Morse.Chapter10.FullPathTheorem)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      [FiniteDimensional ℝ V] → {N : Set V} → (p q : V) → C(Morse.PathSp N p q, Morse.PathC N p q)
**The inclusion `i : Ω → Ω*`** as a continuous map (Milnor p. 93).


### Morse.geodesicIndex  (Morse.Chapter10.FundamentalTheorem)
{V : Type u} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      [FiniteDimensional ℝ V] →
        {Z : Type u_1} →
          [inst_3 : NormedAddCommGroup Z] →
            [inst_4 : NormedSpace ℝ Z] →
              [FiniteDimensional ℝ Z] →
                {W : Type u_2} →
                  [inst_6 : NormedAddCommGroup W] →
                    [inst_7 : NormedSpace ℝ W] →
                      [FiniteDimensional ℝ W] →
                        {N : Set V} → Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N → V → V → (ℝ → V) → ℕ
**The index of a geodesic** `γ ∈ Ω(N; p, q)`, as a natural number: the index of `E_**` at `γ`
(finite for a geodesic, by Theorem 15.1; `0` if `γ ∉ Ω`).


### Morse.oneCellEach  (Morse.Chapter10.PathHomology)
(ℕ → ℕ) → ℕ → List ℕ
The cells of a path space with one geodesic of index `d k` in the `k`-th window: no cell at
stage `0`, one cell of dimension `d k` at stage `k + 1`.


### Morse.PathSp  (Morse.Chapter10.PathMetric)
{V : Type u_1} → [inst : NormedAddCommGroup V] → [InnerProductSpace ℝ V] → Set V → V → V → Type u_1
**Milnor's path space** `Ω(N; p, q)` (p. 67), as a type carrying Milnor's metric `d`
(p. 88).  A path is a function `ℝ → V` in `Morse.pathSpace N p q`; its values off `[0, 1]` play
no role.


### Morse.PathSp.l2Dist  (Morse.Chapter10.PathMetric)
{V : Type u_1} → [inst : NormedAddCommGroup V] → [InnerProductSpace ℝ V] → (ℝ → V) → (ℝ → V) → ℝ
The `L²` part of Milnor's metric: `(∫₀¹ (‖γ'‖ − ‖γ''‖)²)^{1/2}`.


### Morse.PathSp.speed  (Morse.Chapter10.PathMetric)
{V : Type u_1} → [inst : NormedAddCommGroup V] → [InnerProductSpace ℝ V] → (ℝ → V) → ℝ → ℝ
The speed `ds/dt = ‖γ'(t)‖`.


### Morse.PathSp.supDist  (Morse.Chapter10.PathMetric)
{V : Type u_1} → [inst : NormedAddCommGroup V] → [InnerProductSpace ℝ V] → Set V → (ℝ → V) → (ℝ → V) → ENNReal
The uniform part of Milnor's metric: `max_{t ∈ [0, 1]} ρ(γ(t), γ'(t))`.


### Morse.NonposCurvature  (Morse.Chapter11.Curvature)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      [FiniteDimensional ℝ V] →
        {Z : Type u_2} →
          [inst_3 : NormedAddCommGroup Z] →
            [inst_4 : NormedSpace ℝ Z] →
              {W : Type u_3} →
                [inst_5 : NormedAddCommGroup W] →
                  [inst_6 : NormedSpace ℝ W] →
                    {N : Set V} → Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N → Prop
**Milnor's curvature hypothesis of Lemma 19.1** (p. 100): `⟨R(A, B)A, B⟩ ≤ 0` for all
`A, B ∈ T_qN` and all `q ∈ N`, i.e. every sectional curvature is `≤ 0`
(`Morse.nonposCurvature_iff_sectionalCurvature`).


### Morse.dExpAt  (Morse.Chapter11.ExpSmooth)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      {Z : Type u_2} →
        [inst_2 : NormedAddCommGroup Z] →
          [inst_3 : NormedSpace ℝ Z] →
            {W : Type u_3} →
              [inst_4 : NormedAddCommGroup W] →
                [inst_5 : NormedSpace ℝ W] →
                  {N : Set V} →
                    (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) →
                      (q : ↑N) → ↥(Morse.tangentSubspace hN q) → ↥(Morse.tangentSubspace hN q) →ₗ[ℝ] V
**`d(exp_q)_v`**: the derivative at `v` of `exp_q : T_qN → V`, as a linear map (Milnor's
`exp_* : T(TM_p)_v → TM_{exp v}`, with `T(TM_p)_v` identified with `TM_p`).


### Morse.expDomAt  (Morse.Chapter11.ExpSmooth)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      {Z : Type u_2} →
        [inst_2 : NormedAddCommGroup Z] →
          [inst_3 : NormedSpace ℝ Z] →
            {W : Type u_3} →
              [inst_4 : NormedAddCommGroup W] →
                [inst_5 : NormedSpace ℝ W] →
                  {N : Set V} →
                    (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) →
                      (q : ↑N) → Set ↥(Morse.tangentSubspace hN q)
**The domain of `exp_q`** in `T_qN`: the `v` for which the geodesic `t ↦ exp_q(tv)` exists on an
open interval containing `[0, 1]` (all of `T_qN` when `N` is complete).


### Morse.RicciLowerBound  (Morse.Chapter11.Myers)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      [FiniteDimensional ℝ V] →
        {Z : Type u_2} →
          [inst_3 : NormedAddCommGroup Z] →
            [inst_4 : NormedSpace ℝ Z] →
              [FiniteDimensional ℝ Z] →
                {W : Type u_3} →
                  [inst_6 : NormedAddCommGroup W] →
                    [inst_7 : NormedSpace ℝ W] →
                      {N : Set V} → Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N → ℝ → Prop
**Milnor's hypothesis of Theorem 19.4** (p. 104): `K(U, U) ≥ (n − 1)/r²` for every unit
vector `U` at every point of `N`, `n = dim N`.


### Morse.ricci  (Morse.Chapter11.Myers)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      [FiniteDimensional ℝ V] →
        {Z : Type u_2} →
          [inst_3 : NormedAddCommGroup Z] →
            [inst_4 : NormedSpace ℝ Z] →
              [FiniteDimensional ℝ Z] →
                {W : Type u_3} →
                  [inst_6 : NormedAddCommGroup W] →
                    [inst_7 : NormedSpace ℝ W] →
                      {N : Set V} →
                        (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) →
                          (q : ↑N) → ↥(Morse.tangentSubspace hN q) → ↥(Morse.tangentSubspace hN q) → ℝ
**The Ricci tensor** at `q` (Milnor p. 104): the bilinear pairing `K(U₁, U₂)` on `T_qN`, the
trace of the linear map `W ↦ R(U₁, W)U₂` of `T_qN`.


### Morse.conjLocus  (Morse.Chapter11.NonConjugate)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      [FiniteDimensional ℝ V] →
        {Z : Type u_2} →
          [inst_3 : NormedAddCommGroup Z] →
            [inst_4 : NormedSpace ℝ Z] →
              {W : Type u_3} →
                [inst_5 : NormedAddCommGroup W] →
                  [inst_6 : NormedSpace ℝ W] →
                    {N : Set V} → Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N → V → Set V
**The points conjugate to `p` along some geodesic** (Milnor p. 99): the `q` for which there is
a geodesic `γ : [0, 1] → N` from `p` to `q` along which `0` and `1` are conjugate.


### Morse.hermitian  (Morse.Chapter12.MatrixGroups)
(𝕜 : Type u_1) → [inst : RCLike 𝕜] → (ι : Type u_2) → Submodule ℝ (Matrix ι ι 𝕜)
The Hermitian matrices `Aᴴ = A`, a real subspace of `Mₙ(𝕜)`.


### Morse.specialSkewHermitian  (Morse.Chapter12.MatrixGroups)
(ι : Type u_2) → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → LieSubalgebra ℝ (Matrix ι ι ℂ)
**`𝔰𝔲(n)`**: the skew-Hermitian matrices of trace `0` (Milnor p. 126, his `𝔤'`).


### Morse.grassmannian  (Morse.Chapter12.SUMinimal)
(ι : Type u_2) → [Fintype ι] → [DecidableEq ι] → ℕ → Set (Matrix ι ι ℂ)
**The Grassmannian `G_m(ℂⁿ)`**, as the Hermitian projections of trace `m` (the orthogonal
projections onto the `m`-dimensional subspaces).


### Morse.lemma_23_1  (Morse.Chapter12.SUMinimal)
{ι : Type u_1} →
  [inst : Fintype ι] →
    [inst_1 : DecidableEq ι] → {m : ℕ} → Fintype.card ι = 2 * m → ↑(Morse.minVel ι) ≃ₜ ↑(Morse.grassmannian ι m)
**Lemma 23.1** (Milnor p. 127): in `SU(2m)`, the set of initial velocities of the minimal
geodesics from `I` to `−I` is homeomorphic to the Grassmannian of `m`-planes in `ℂ^{2m}` (as
Hermitian projections of trace `m`), by `A ↦ ½(I − (i/π)A)` (the projection onto
`Eigen(iπ)`), with inverse `P ↦ iπ(2P − I)`.


### Morse.minVel  (Morse.Chapter12.SUMinimal)
(ι : Type u_2) → [Fintype ι] → [DecidableEq ι] → Set (Matrix ι ι ℂ)
**The initial velocities of the minimal geodesics from `I` to `−I`**: the `A ∈ 𝔰𝔲(n)` with
`A² = −π²I` (Milnor p. 127).


### Morse.PushesInto  (Morse.Chapter13.Compression)
(P : Type u_1) → [TopologicalSpace P] → {T : Type u_2} → [TopologicalSpace T] → Set T → Set T → Prop
**`A` pushes maps from `P` out of `X`**: every map `h : P → T` with values in `X` is
homotopic, relative to `h⁻¹(A)`, to a map with values in `A`.


### Morse.minPaths  (Morse.Chapter13.Theorem22)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] → [inst_1 : InnerProductSpace ℝ V] → (N : Set V) → (p q : V) → Set (Morse.PathSp N p q)
**`Ω^d`: the paths of least energy** from `p` to `q` (Milnor's space of minimal geodesics,
p. 118).


### Morse.minPathsIncl  (Morse.Chapter13.Theorem22)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] → (N : Set V) → (p q : V) → C(↑(Morse.minPaths N p q), Morse.PathSp N p q)
The inclusion `Ω^d → Ω`.


### Morse.suDiag  (Morse.Chapter14.SUMatrices)
{ι : Type u_1} → [DecidableEq ι] → (ι → ℤ) → Matrix ι ι ℂ
Milnor's velocity `A = diag(iπk_1, …, iπk_n)` (p. 130).


### Morse.AttachCell  (Morse.Chapter2.Attaching)
{n : ℕ} → {X : TopCat} → (TopCat.diskBoundary n ⟶ X) → TopCat
`X ∪_φ e^n`.


### Morse.cellInl  (Morse.Chapter2.Attaching)
{n : ℕ} → {X : TopCat} → (φ : TopCat.diskBoundary n ⟶ X) → X ⟶ Morse.AttachCell φ
The inclusion `X → X ∪_φ e^n`.


### Morse.cellInr  (Morse.Chapter2.Attaching)
{n : ℕ} → {X : TopCat} → (φ : TopCat.diskBoundary n ⟶ X) → TopCat.disk n ⟶ Morse.AttachCell φ
The characteristic map `D^n → X ∪_φ e^n` of the cell.


### Morse.IsCellAttachment  (Morse.Chapter2.CWType)
TopCat → List ℕ → Prop
**Iterated adjunction spaces.** `IsCellAttachment K cells`: the space `K` is obtained from the
empty space by attaching cells of the dimensions listed in `cells`, one at a time and in the order
of the list, each along an arbitrary continuous map of its boundary sphere into the space built so
far (the attaching space being the pushout `Morse.AttachCell φ` in `TopCat`).


### Morse.IsFiniteCellComplexType  (Morse.Chapter2.CWType)
(X : Type u) → [TopologicalSpace X] → List ℕ → Prop
**`X` has the homotopy type of a finite cell complex with cells of dimensions `cells`**: it is
homotopy equivalent to a space obtained from the empty space by attaching cells of these dimensions
one at a time, in this order, along arbitrary continuous attaching maps (`Morse.IsCellAttachment`).
See the module docstring for the comparison with CW-complexes.


### Morse.IsStrongDeformationRetract  (Morse.Chapter2.Crossing)
{X : Type u_1} → [TopologicalSpace X] → Set X → Prop
**Strong deformation retract.** `A ⊆ X` is a strong deformation retract of `X` if there are a
continuous map `r : X → X` with values in `A` and a homotopy from the identity of `X` to `r` which
fixes `A` pointwise at all times (Mathlib's `ContinuousMap.HomotopyRel`). In Milnor's notation
(p. 13) the homotopy is `(t, x) ↦ r_t(x)`, `0 ≤ t ≤ 1`, with `r_0 = id`, `r_1 = r`,
`r_1(X) ⊆ A`, and `r_t = id` on `A`. Since `r` agrees with the identity on `A`, it is a retraction
onto `A`.


### Morse.sublevel  (Morse.Chapter2.Crossing)
{T : Type u_1} → (T → ℝ) → ℝ → Set T
Milnor's `M^c = f⁻¹(-∞, c] = {p ∈ M : f(p) ≤ c}` (p. 12).


### Morse.Torus.height  (Morse.Chapter3.Torus)
ℝ → ℝ → EuclideanSpace ℝ (Fin 3) → ℝ
**Milnor's height function** `f`: the height `x₁ + R + r` above the plane
`V = {x₁ = −(R + r)}`, which touches the torus at `p` (Diagram 1).


### Morse.torus  (Morse.Chapter3.TorusSurface)
ℝ → ℝ → Set (EuclideanSpace ℝ (Fin 3))
**The torus of Diagram 1** (Milnor, p. 1): the torus of revolution about the `x₃`-axis with
core radius `R` and tube radius `r`, `{x ∈ ℝ³ : (√(x₁² + x₂²) − R)² + x₃² = r²}`.  (The
coordinates `x₁, x₂, x₃` are `x 0, x 1, x 2`.)  It is a smooth surface when `0 < r < R`
(`Morse.isSliceSubmanifold_torus`).


### Morse.dN  (Morse.Chapter6.Projection)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      {Z : Type u_2} →
        [inst_2 : NormedAddCommGroup Z] →
          [inst_3 : NormedSpace ℝ Z] →
            {W : Type u_3} →
              [inst_4 : NormedAddCommGroup W] →
                [inst_5 : NormedSpace ℝ W] →
                  {N : Set V} →
                    Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N →
                      {E : Type u_4} →
                        [inst_6 : NormedAddCommGroup E] → [inst_7 : NormedSpace ℝ E] → (↑N → E) → ↑N → V →L[ℝ] E
**The derivative of `F : N → E` at `q` on ambient tangent vectors**: for `v ∈ T_qN`,
`dN F q v = dF_q(v)` (Mathlib's `mfderiv` at `q`, applied to the chart coordinates of `v`).  On
vectors not tangent to `N` its value depends on the chart and has no meaning.


### Morse.sliceAt  (Morse.Chapter6.Projection)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      {Z : Type u_2} →
        [inst_2 : NormedAddCommGroup Z] →
          [inst_3 : NormedSpace ℝ Z] →
            {W : Type u_3} →
              [inst_4 : NormedAddCommGroup W] →
                [inst_5 : NormedSpace ℝ W] →
                  {N : Set V} →
                    Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N →
                      ↑N → Milnor.SliceChart (modelWithCornersSelf ℝ V) Z W N
The slice chart of `N` chosen at `q`; its induced chart is the chart `chartAt Z q` of the
manifold structure of `N`.


### Morse.tanCoord  (Morse.Chapter6.Projection)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      {Z : Type u_2} →
        [inst_2 : NormedAddCommGroup Z] →
          [inst_3 : NormedSpace ℝ Z] →
            {W : Type u_3} →
              [inst_4 : NormedAddCommGroup W] →
                [inst_5 : NormedSpace ℝ W] →
                  {N : Set V} → Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N → ↑N → V →L[ℝ] Z
**The chart coordinates of an ambient vector** at `q`: `v ↦ (dσ_q v)₁`, `σ` the slice chart
chosen at `q`.  On `T_qN` it inverts the derivative of the inclusion
(`Morse.tanCoord_mfderiv_val`, `Morse.mfderiv_val_tanCoord`).


### Morse.tanProj  (Morse.Chapter6.Projection)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      {Z : Type u_2} →
        [inst_2 : NormedAddCommGroup Z] →
          [inst_3 : NormedSpace ℝ Z] →
            {W : Type u_3} →
              [inst_4 : NormedAddCommGroup W] →
                [inst_5 : NormedSpace ℝ W] →
                  {N : Set V} →
                    Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N →
                      [FiniteDimensional ℝ V] → ↑N → V →L[ℝ] V
**The orthogonal projection `P_q` of `V` onto the tangent space `T_qN`.**


### Morse.curvOp  (Morse.Chapter6.Submanifold)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      [FiniteDimensional ℝ V] →
        {Z : Type u_2} →
          [inst_3 : NormedAddCommGroup Z] →
            [inst_4 : NormedSpace ℝ Z] →
              {W : Type u_3} →
                [inst_5 : NormedAddCommGroup W] →
                  [inst_6 : NormedSpace ℝ W] →
                    {N : Set V} → Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N → ↑N → V → V → V →L[ℝ] V
The curvature at `q` in terms of the derivative `D = dN P q` of the projection:
`R_q(x, y) = D_y ∘ D_x − D_x ∘ D_y` (`Morse.curvature_eq`).


### Morse.curvTensor  (Morse.Chapter6.Submanifold)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      [FiniteDimensional ℝ V] →
        {Z : Type u_2} →
          [inst_3 : NormedAddCommGroup Z] →
            [inst_4 : NormedSpace ℝ Z] →
              {W : Type u_3} →
                [inst_5 : NormedAddCommGroup W] →
                  [inst_6 : NormedSpace ℝ W] →
                    {N : Set V} →
                      (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) →
                        [FiniteDimensional ℝ Z] →
                          (q : ↑N) →
                            ↥(Morse.tangentSubspace hN q) →ₗ[ℝ]
                              ↥(Morse.tangentSubspace hN q) →ₗ[ℝ]
                                ↥(Morse.tangentSubspace hN q) →ₗ[ℝ] ↥(Morse.tangentSubspace hN q)
**The curvature tensor of `N` at `q`** (Lemma 9.1, p. 51), as a trilinear map
`T_qN × T_qN × T_qN → T_qN`: `(x, y, z) ↦ R(x, y)z = II(y, II(x, z)) − II(x, II(y, z))`.


### Morse.IsShortJoin  (Morse.Chapter7.Distance)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      {Z : Type u_2} →
        [inst_2 : NormedAddCommGroup Z] →
          [inst_3 : NormedSpace ℝ Z] →
            {W : Type u_3} →
              [inst_4 : NormedAddCommGroup W] →
                [inst_5 : NormedSpace ℝ W] →
                  {N : Set V} → Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N → ℝ → ↑N → ↑N → Prop
The conclusion of Corollary 10.8 for two points `y, z` and a bound `δ`: `y` and `z` are joined
by a geodesic `t ↦ exp_y(tv)`, `0 ≤ t ≤ 1`, of length `‖v‖ < δ`; it is minimal
(`ρ(y, z) = ‖v‖`); it is the only geodesic from `y` to `z` of length `< δ`; and `v` depends
smoothly on the endpoints (it is the restriction of a smooth map `G` near `(y, z)`, on pairs at
distance `< δ`).


### Morse.pathLengths  (Morse.Chapter7.Distance)
{V : Type u_1} → [inst : NormedAddCommGroup V] → [InnerProductSpace ℝ V] → {N : Set V} → V → V → Set ENNReal
The lengths of the piecewise smooth paths in `N` from `p` to `q`, as extended reals.


### Morse.riemDist  (Morse.Chapter7.Distance)
{V : Type u_1} → [inst : NormedAddCommGroup V] → [InnerProductSpace ℝ V] → {N : Set V} → V → V → ENNReal
**The distance** `ρ(p, q)` (Milnor, p. 62): the greatest lower bound of the lengths of
piecewise smooth paths in `N` joining `p` to `q` (`∞` if there is none).


### Morse.IsGeodesicFrom  (Morse.Chapter7.Exp)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      {Z : Type u_2} →
        [inst_2 : NormedAddCommGroup Z] →
          [inst_3 : NormedSpace ℝ Z] →
            {W : Type u_3} →
              [inst_4 : NormedAddCommGroup W] →
                [inst_5 : NormedSpace ℝ W] →
                  {N : Set V} → Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N → (ℝ → V) → V → V → Prop
`γ` is a geodesic through `q` with initial velocity `v`, defined on an open interval
`(-δ, 1 + δ)` containing `[0, 1]`.


### Morse.exp  (Morse.Chapter7.Exp)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      {Z : Type u_2} →
        [inst_2 : NormedAddCommGroup Z] →
          [inst_3 : NormedSpace ℝ Z] →
            {W : Type u_3} →
              [inst_4 : NormedAddCommGroup W] →
                [inst_5 : NormedSpace ℝ W] →
                  {N : Set V} → Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N → V → V → V
**The exponential map** (Milnor, p. 57): `exp_q(v) = γ(1)` for the geodesic `γ` with
`γ(0) = q`, `γ'(0) = v` (`Morse.IsGeodesicFrom.exp_eq`); `q` if there is none.


### Morse.expDom  (Morse.Chapter7.Exp)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      {Z : Type u_2} →
        [inst_2 : NormedAddCommGroup Z] →
          [inst_3 : NormedSpace ℝ Z] →
            {W : Type u_3} →
              [inst_4 : NormedAddCommGroup W] →
                [inst_5 : NormedSpace ℝ W] →
                  {N : Set V} → Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N → Set (V × V)
**The domain of the exponential map**: the `(q, v)` for which there is a geodesic `γ` on an
open interval containing `[0, 1]` with `γ(0) = q`, `γ'(0) = v`.


### Morse.IsGeodesicOn  (Morse.Chapter7.Geodesic)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      {Z : Type u_2} →
        [inst_2 : NormedAddCommGroup Z] →
          [inst_3 : NormedSpace ℝ Z] →
            {W : Type u_3} →
              [inst_4 : NormedAddCommGroup W] →
                [inst_5 : NormedSpace ℝ W] →
                  {N : Set V} → Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N → (ℝ → V) → Set ℝ → Prop
**A geodesic of `N`** (Milnor, p. 55) on an open set `s ⊆ ℝ` (in practice an open interval):
a curve `γ : ℝ → V`, smooth on `s`, with values in `N` on `s`, whose acceleration `γ''(t)` is
normal to `N` at `γ(t)` for every `t ∈ s`.  For the induced metric this is Milnor's
`D/dt (dγ/dt) = 0` (`Morse.isGeodesicOn_univ_iff_covDeriv`), since `D/dt = P ∘ d/dt`.


### Morse.IsGeodesicallyComplete  (Morse.Chapter7.GeodesicFlow)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      {Z : Type u_2} →
        [inst_2 : NormedAddCommGroup Z] →
          [inst_3 : NormedSpace ℝ Z] →
            {W : Type u_3} →
              [inst_4 : NormedAddCommGroup W] →
                [inst_5 : NormedSpace ℝ W] →
                  {N : Set V} → Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N → Prop
**Geodesic completeness** (Milnor, p. 58): `exp_q(v)` is defined for every `q ∈ N` and every
`v ∈ T_qN`.  Equivalently (p. 62), every geodesic extends to all of `ℝ`
(`Morse.isGeodesicallyComplete_iff`).


### Morse.IsMinimalGeodesic  (Morse.Chapter7.HopfRinow)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      {Z : Type u_2} →
        [inst_2 : NormedAddCommGroup Z] →
          [inst_3 : NormedSpace ℝ Z] →
            {W : Type u_3} →
              [inst_4 : NormedAddCommGroup W] →
                [inst_5 : NormedSpace ℝ W] →
                  {N : Set V} → Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N → (ℝ → V) → ℝ → ℝ → Prop
**A minimal geodesic** (Milnor, p. 61) on `[a, b]`: the restriction of a geodesic on an open
set containing `[a, b]`, whose length is at most the length of every piecewise smooth path in `N`
with the same endpoints.


### Morse.IsRiemBounded  (Morse.Chapter7.Metric)
{V : Type u_1} → [inst : NormedAddCommGroup V] → [InnerProductSpace ℝ V] → Set V → Set V → Prop
**A `ρ`-bounded set** (Milnor, p. 64): a set of finite diameter for `ρ`.  (Such a set lies in
`N`, as `ρ(x, x) = ∞` for `x ∉ N`.)


### Morse.IsRiemComplete  (Morse.Chapter7.Metric)
{V : Type u_1} → [inst : NormedAddCommGroup V] → [InnerProductSpace ℝ V] → Set V → Prop
**`(N, ρ)` is a complete metric space** (Milnor, p. 64): every `ρ`-Cauchy sequence of points of
`N` converges, for `ρ`, to a point of `N`.


### Morse.IsNormalRadius  (Morse.Chapter7.NormalNbhd)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      {Z : Type u_2} →
        [inst_2 : NormedAddCommGroup Z] →
          [inst_3 : NormedSpace ℝ Z] →
            {W : Type u_3} →
              [inst_4 : NormedAddCommGroup W] →
                [inst_5 : NormedSpace ℝ W] →
                  {N : Set V} → Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N → ↑N → ℝ → Prop
**`ε` is a normal radius at `q`** (the exposition's term): `exp_q` maps the open `ε`-ball of
`T_qN` diffeomorphically onto an open subset of `N`.


### Morse.NormalCoord  (Morse.Chapter7.NormalNbhd)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      {Z : Type u_2} →
        [inst_2 : NormedAddCommGroup Z] →
          [inst_3 : NormedSpace ℝ Z] →
            {W : Type u_3} →
              [inst_4 : NormedAddCommGroup W] →
                [inst_5 : NormedSpace ℝ W] →
                  {N : Set V} → Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N → ↑N → ℝ → Type u_1
**Normal coordinates of radius `ε` at `q`**: `exp_q` maps the ball
`B_ε(q) = {v ∈ T_qN : ‖v‖ < ε}` diffeomorphically onto the open subset `N ∩ U` of `N`.  Precisely:
`exp_q` is defined on `B_ε(q)` and is there the restriction of the smooth map `F` on the open set
`O ⊆ V`; it is a bijection of `B_ε(q)` onto `N ∩ U`, `U` open in `V`, whose inverse is the
restriction of the smooth map `G` on `U`.


### Morse.IsPiecewiseSmooth  (Morse.Chapter7.Path)
{V : Type u_1} → [inst : NormedAddCommGroup V] → [NormedSpace ℝ V] → (ℝ → V) → ℝ → ℝ → Prop
**A piecewise smooth path** on `[a, b]` (Milnor, pp. 59, 67): `c` is continuous on `[a, b]`,
and there is a finite set `B` of break points such that `c` is smooth (`C^∞`, with one-sided
derivatives at the ends) on every closed subinterval `[s, t] ⊆ [a, b]` with no point of `B` in
`(s, t)`.  (For Milnor's subdivision `a = t₀ < ⋯ < t_k = b`, take `B = {t_i}`.)


### Morse.pathLength  (Morse.Chapter7.Path)
{V : Type u_1} → [inst : NormedAddCommGroup V] → [NormedSpace ℝ V] → (ℝ → V) → ℝ → ℝ → ℝ
**The length** `∫ₐᵇ ‖c'(t)‖ dt` of a path `c` on `[a, b]`.


### Morse.IsCriticalPath  (Morse.Chapter8.Critical)
{V : Type u_1} → [inst : NormedAddCommGroup V] → [InnerProductSpace ℝ V] → Set V → (ℝ → V) → Prop
**A critical path of the energy** (Milnor p. 69): for every variation `ᾱ` of `ω`, the
derivative `dE(ᾱ(u))/du` at `u = 0` exists and is zero.


### Morse.IsUnbrokenGeodesic  (Morse.Chapter8.Critical)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      {Z : Type u_2} →
        [inst_2 : NormedAddCommGroup Z] →
          [inst_3 : NormedSpace ℝ Z] →
            {W : Type u_3} →
              [inst_4 : NormedAddCommGroup W] →
                [inst_5 : NormedSpace ℝ W] →
                  {N : Set V} → Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N → (ℝ → V) → Prop
**An (unbroken) geodesic** in `Ω` (Milnor p. 73): `C^∞` on the whole closed interval `[0, 1]`
(one-sided derivatives at the ends), with zero acceleration.


### Morse.IsVariation  (Morse.Chapter8.Energy)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [InnerProductSpace ℝ V] →
      Set V → {P : Type u_4} → [inst : NormedAddCommGroup P] → [NormedSpace ℝ P] → Set P → (P → ℝ → V) → Finset ℝ → Prop
**A variation with fixed end points** (Milnor p. 68), with parameters in an open set `U ∋ 0`
of a normed space `P`: Milnor's `(-ε, ε)` for `P = ℝ`, a neighbourhood of `0 ∈ ℝ²` for the
2-parameter variations of §13.  `α u t ∈ N` for `u ∈ U`, `t ∈ [0, 1]`; the end points `α u 0`,
`α u 1` do not depend on `u`; and `(u, t) ↦ α u t` is smooth on each closed strip `U × [s, t]`
whose interior contains no point of the finite set `B` of break points (Milnor: smooth on each
strip `(-ε, ε) × [t_{i-1}, t_i]` of a subdivision).  It is a variation *of `α 0`*.


### Morse.energy  (Morse.Chapter8.Energy)
{E : Type u_4} → [inst : NormedAddCommGroup E] → [NormedSpace ℝ E] → (ℝ → E) → ℝ → ℝ → ℝ
**The energy** of a path from `a` to `b` (Milnor p. 70): `E_a^b(ω) = ∫ₐᵇ ‖dω/dt‖² dt`.
Milnor's `E` is `energy ω 0 1`.  (The norm is the norm of `V`, i.e. the induced metric.)


### Morse.jump  (Morse.Chapter8.Energy)
{E : Type u_1} → [inst : NormedAddCommGroup E] → [NormedSpace ℝ E] → (ℝ → E) → ℝ → E
**The jump of the derivative** `Δ_t f = f'(t⁺) - f'(t⁻)` at `t` (Milnor p. 71, for the
velocity), from the one-sided derivatives `derivWithin f (Ici t) t` and
`derivWithin f (Iic t) t`.  It vanishes where `f` is differentiable (`Morse.jump_eq_zero`).


### Morse.pathSpace  (Morse.Chapter8.Energy)
{V : Type u_1} → [inst : NormedAddCommGroup V] → [InnerProductSpace ℝ V] → Set V → V → V → Set (ℝ → V)
**Milnor's path space** `Ω(N; p, q)` (p. 67): the piecewise smooth paths `ω : [0, 1] → N` from
`p` to `q` (`Morse.IsPiecewiseSmooth`, Chapter 7).  A path is represented by a function `ℝ → V`;
its values off `[0, 1]` play no role.


### Morse.pathTangent  (Morse.Chapter8.Energy)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      [FiniteDimensional ℝ V] →
        {Z : Type u_2} →
          [inst_3 : NormedAddCommGroup Z] →
            [inst_4 : NormedSpace ℝ Z] →
              {W : Type u_3} →
                [inst_5 : NormedAddCommGroup W] →
                  [inst_6 : NormedSpace ℝ W] →
                    {N : Set V} →
                      Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N → (ℝ → V) → Submodule ℝ (ℝ → V)
**Milnor's "tangent space" `TΩ_ω`** (p. 67), as a vector space of functions: the piecewise
smooth vector fields `W` along `ω` (tangent: `P_{ω(t)} W(t) = W(t)` for `t ∈ [0, 1]`) which vanish
at `t = 0` and `t = 1`.  `Ω` itself carries no manifold structure here, as in Milnor's §§11–15;
this vector space is a definition, and its relation with `Ω` is made through variations
(`Morse.IsVariation.varField_mem`, and Lemma 11.A, `Morse.exists_variation`).


### Morse.prj  (Morse.Chapter8.Energy)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      [FiniteDimensional ℝ V] →
        {Z : Type u_2} →
          [inst_3 : NormedAddCommGroup Z] →
            [inst_4 : NormedSpace ℝ Z] →
              {W : Type u_3} →
                [inst_5 : NormedAddCommGroup W] →
                  [inst_6 : NormedSpace ℝ W] →
                    {N : Set V} → Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N → V → V →L[ℝ] V
**The tangent projection at a point `x` of `V`**: `P_x = Morse.tanProj hN ⟨x, _⟩` (orthogonal
projection onto `T_xN`) for `x ∈ N`, and `0` off `N`.  Paths lie in `N` only for `t ∈ [0, 1]`, and
a total function of `x` is convenient in integrands.


### Morse.covD  (Morse.Chapter8.FirstVariation)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      [FiniteDimensional ℝ V] →
        {Z : Type u_2} →
          [inst_3 : NormedAddCommGroup Z] →
            [inst_4 : NormedSpace ℝ Z] →
              {W : Type u_3} →
                [inst_5 : NormedAddCommGroup W] →
                  [inst_6 : NormedSpace ℝ W] →
                    {N : Set V} → Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N → (ℝ → V) → (ℝ → V) → ℝ → V
**The covariant derivative of a vector field `X` along a path `ω`** (Milnor p. 46, for the
induced metric; `Morse.covDeriv` of Chapter 6): `DX/dt = P_{ω(t)}(X'(t))`, meaningful at the
points where `X` is differentiable.


### Morse.IsMinimalPath  (Morse.Chapter8.Hessian)
{V : Type u_1} → [inst : NormedAddCommGroup V] → [InnerProductSpace ℝ V] → Set V → (ℝ → V) → V → V → Prop
A path of `Ω(N; p, q)` whose length is at most that of every path of `Ω(N; p, q)` (Milnor's
minimal geodesics, p. 61, when it is a geodesic).


### Morse.energyHessian  (Morse.Chapter8.Hessian)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      [inst_2 : FiniteDimensional ℝ V] →
        {Z : Type u_2} →
          [inst_3 : NormedAddCommGroup Z] →
            [inst_4 : NormedSpace ℝ Z] →
              [FiniteDimensional ℝ Z] →
                {W : Type u_3} →
                  [inst_6 : NormedAddCommGroup W] →
                    [inst_7 : NormedSpace ℝ W] →
                      [FiniteDimensional ℝ W] →
                        {N : Set V} →
                          (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) →
                            {γ : ℝ → V} →
                              {p q : V} → γ ∈ Morse.pathSpace N p q → LinearMap.BilinForm ℝ ↥(Morse.pathTangent hN γ)
**Milnor's Hessian** `E_** : TΩ_γ × TΩ_γ → ℝ` (p. 74), as a bilinear form on the vector space
`TΩ_γ` (`Morse.pathTangent`), defined by the right side of Theorem 13.1 (times 2):
`E_**(W₁, W₂) = 2 secondVariation γ W₁ W₂`.  That this is Milnor's `∂²E/∂u₁∂u₂ (0, 0)` for every
2-parameter variation with variation fields `W₁, W₂` is Theorem 13.1 (`Morse.second_variation`,
`Morse.hasDerivAt_hessian`); that every pair `(W₁, W₂)` arises is Lemma 11.A
(`Morse.exists_variation_two`).  Bilinearity (Corollary 13.4) comes from the integral form,
Proposition 13.A (`Morse.secondVariation_eq_hessForm`); only `γ ∈ Ω` is needed for it.


### Morse.IsJacobiField  (Morse.Chapter8.Jacobi)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      [FiniteDimensional ℝ V] →
        {Z : Type u_2} →
          [inst_3 : NormedAddCommGroup Z] →
            [inst_4 : NormedSpace ℝ Z] →
              {W : Type u_3} →
                [inst_5 : NormedAddCommGroup W] →
                  [inst_6 : NormedSpace ℝ W] →
                    {N : Set V} → Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N → (ℝ → V) → (ℝ → V) → Prop
**A Jacobi field along `γ`** on `[0, 1]` (Milnor p. 77): a smooth vector field along `γ`
(`C^∞` on `[0, 1]`, with one-sided derivatives at the ends, and tangent to `N`) satisfying the
Jacobi equation `D²J/dt² + R(V, J)V = 0` (on `(0, 1)`, hence on `[0, 1]` by continuity).


### Morse.jacobiExpr  (Morse.Chapter8.Jacobi)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      [FiniteDimensional ℝ V] →
        {Z : Type u_2} →
          [inst_3 : NormedAddCommGroup Z] →
            [inst_4 : NormedSpace ℝ Z] →
              {W : Type u_3} →
                [inst_5 : NormedAddCommGroup W] →
                  [inst_6 : NormedSpace ℝ W] →
                    {N : Set V} → Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N → (ℝ → V) → (ℝ → V) → ℝ → V
**The Jacobi operator** `D²J/dt² + R(V, J)V` along `γ` (Milnor p. 77), `V = dγ/dt`.


### Morse.curvR  (Morse.Chapter8.SecondVariation)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      [FiniteDimensional ℝ V] →
        {Z : Type u_2} →
          [inst_3 : NormedAddCommGroup Z] →
            [inst_4 : NormedSpace ℝ Z] →
              {W : Type u_3} →
                [inst_5 : NormedAddCommGroup W] →
                  [inst_6 : NormedSpace ℝ W] →
                    {N : Set V} → Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N → V → V → V → V → V
**Milnor's curvature tensor at a point `x` of `V`** (`0` off `N`): `R(a, b)c` is
`Morse.curvOp hN x a b c = II(b, II(a, c)) − II(a, II(b, c))` of Chapter 6, i.e. Milnor's
`R(X, Y)Z = −∇_X∇_Y Z + ∇_Y∇_X Z + ∇_{[X,Y]} Z` (p. 51), the sign for which Lemma 9.2 reads
`D/∂y D/∂x V − D/∂x D/∂y V = R(∂s/∂x, ∂s/∂y)V` and the unit sphere has curvature `+1`.


### Morse.secondVariation  (Morse.Chapter8.SecondVariation)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      [FiniteDimensional ℝ V] →
        {Z : Type u_2} →
          [inst_3 : NormedAddCommGroup Z] →
            [inst_4 : NormedSpace ℝ Z] →
              {W : Type u_3} →
                [inst_5 : NormedAddCommGroup W] →
                  [inst_6 : NormedSpace ℝ W] →
                    {N : Set V} →
                      Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N → (ℝ → V) → (ℝ → V) → (ℝ → V) → ℝ
**The second variation** (half of Milnor's `E_**`) at the path `γ`, Milnor's right side of
Theorem 13.1: `−Σ_t ⟨W₂(t), Δ_t DW₁/dt⟩ − ∫₀¹ ⟨W₂, D²W₁/dt² + R(V, W₁)V⟩ dt`, with
`D/dt = Morse.covD`, `V = dγ/dt`, `R = Morse.curvR`, and `Δ_t DW₁/dt = P_{γ(t)}(Δ_t W₁')` the jump
of the covariant derivative (`DW₁/dt(t^±) = P W₁'(t^±)`), the sum over the finitely many
`t ∈ (0, 1)` at which it is not zero.


### Morse.IsBrokenJacobi  (Morse.Chapter9.BrokenJacobi)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      [FiniteDimensional ℝ V] →
        {Z : Type u_2} →
          [inst_3 : NormedAddCommGroup Z] →
            [inst_4 : NormedSpace ℝ Z] →
              [FiniteDimensional ℝ Z] →
                {W : Type u_3} →
                  [inst_6 : NormedAddCommGroup W] →
                    [inst_7 : NormedSpace ℝ W] →
                      [FiniteDimensional ℝ W] →
                        {N : Set V} →
                          (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) →
                            (γ : ℝ → V) → Morse.IsSmoothCurveIn hN γ → Finset ℝ → ℝ → (ℝ → V) → Prop
**A broken Jacobi field on `[0, τ]`** for the division points `B`: on every piece it agrees
with a Jacobi field along `γ`.


### Morse.IsFine  (Morse.Chapter9.BrokenJacobi)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      [FiniteDimensional ℝ V] →
        {Z : Type u_2} →
          [inst_3 : NormedAddCommGroup Z] →
            [inst_4 : NormedSpace ℝ Z] →
              [FiniteDimensional ℝ Z] →
                {W : Type u_3} →
                  [inst_6 : NormedAddCommGroup W] →
                    [inst_7 : NormedSpace ℝ W] →
                      [FiniteDimensional ℝ W] →
                        {N : Set V} →
                          (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) →
                            (γ : ℝ → V) → Morse.IsSmoothCurveIn hN γ → Finset ℝ → ℝ → Prop
**A fine subdivision of `[0, τ]`** (Milnor p. 83, "sufficiently fine"): the interior division
points `B ⊆ (0, τ)` cut `[0, τ]` into pieces of length at most `h₀ = Morse.fineMesh`.


### Morse.brokenSpace  (Morse.Chapter9.BrokenJacobi)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      [inst_2 : FiniteDimensional ℝ V] →
        {Z : Type u_2} →
          [inst_3 : NormedAddCommGroup Z] →
            [inst_4 : NormedSpace ℝ Z] →
              [FiniteDimensional ℝ Z] →
                {W : Type u_3} →
                  [inst_6 : NormedAddCommGroup W] →
                    [inst_7 : NormedSpace ℝ W] →
                      [FiniteDimensional ℝ W] →
                        {N : Set V} →
                          {hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N} →
                            {γ : ℝ → V} →
                              Morse.IsSmoothCurveIn hN γ → Finset ℝ → ℝ → Submodule ℝ ↥(Morse.pathTangent hN γ)
**The broken Jacobi fields** `TΩ_γ(t₀, …, t_k)` along `γ|[0, τ]` (Milnor p. 83), as fields of
`TΩ_γ` vanishing outside `[0, τ]`.


### Morse.fieldsUpTo  (Morse.Chapter9.BrokenJacobi)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      [inst_2 : FiniteDimensional ℝ V] →
        {Z : Type u_2} →
          [inst_3 : NormedAddCommGroup Z] →
            [inst_4 : NormedSpace ℝ Z] →
              {W : Type u_3} →
                [inst_5 : NormedAddCommGroup W] →
                  [inst_6 : NormedSpace ℝ W] →
                    {N : Set V} →
                      (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) →
                        (γ : ℝ → V) → ℝ → Submodule ℝ ↥(Morse.pathTangent hN γ)
**The fields along `γ|[0, τ]`** vanishing at the ends, extended by `0`: the elements of
`TΩ_γ` vanishing outside `[0, τ]`.


### Morse.IsNegDefOn  (Morse.Chapter9.FormIndex)
{M : Type u_1} → [inst : AddCommGroup M] → [inst_1 : _root_.Module ℝ M] → LinearMap.BilinForm ℝ M → Submodule ℝ M → Prop
`B` is **negative definite** on the subspace `S`.


### Morse.formIndex  (Morse.Chapter9.FormIndex)
{M : Type u_1} → [inst : AddCommGroup M] → [inst_1 : _root_.Module ℝ M] → LinearMap.BilinForm ℝ M → ℕ∞
**The index** of a bilinear form (Milnor pp. 5, 83): the supremum, in `ℕ∞`, of the dimensions
of the finite dimensional subspaces on which `B` is negative definite.


### Morse.fineMesh  (Morse.Chapter9.IndexForm)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      [FiniteDimensional ℝ V] →
        {Z : Type u_2} →
          [inst_3 : NormedAddCommGroup Z] →
            [inst_4 : NormedSpace ℝ Z] →
              [FiniteDimensional ℝ Z] →
                {W : Type u_3} →
                  [inst_6 : NormedAddCommGroup W] →
                    [inst_7 : NormedSpace ℝ W] →
                      [FiniteDimensional ℝ W] →
                        {N : Set V} →
                          (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) →
                            (γ : ℝ → V) → Morse.IsSmoothCurveIn hN γ → ℝ
**The mesh of a fine subdivision**: pieces of length `≤ h₀ = 1 / (jacBound + 1)`.


### Morse.jacBound  (Morse.Chapter9.IndexForm)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      [FiniteDimensional ℝ V] →
        {Z : Type u_2} →
          [inst_3 : NormedAddCommGroup Z] →
            [inst_4 : NormedSpace ℝ Z] →
              [FiniteDimensional ℝ Z] →
                {W : Type u_3} →
                  [inst_6 : NormedAddCommGroup W] →
                    [inst_7 : NormedSpace ℝ W] →
                      [FiniteDimensional ℝ W] →
                        {N : Set V} →
                          (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) →
                            (γ : ℝ → V) → Morse.IsSmoothCurveIn hN γ → ℝ
A bound for `‖P'‖² + ‖R(V, P ·)V‖` along `γ`.


### Morse.IsConjugate  (Morse.Chapter9.JacobiSpace)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      [FiniteDimensional ℝ V] →
        {Z : Type u_2} →
          [inst_3 : NormedAddCommGroup Z] →
            [inst_4 : NormedSpace ℝ Z] →
              {W : Type u_3} →
                [inst_5 : NormedAddCommGroup W] →
                  [inst_6 : NormedSpace ℝ W] →
                    {N : Set V} → Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N → (ℝ → V) → ℝ → ℝ → Prop
**Conjugate parameter values** (Milnor p. 77, with the footnote): `a ≠ b` in `[0, 1]` are
conjugate along `γ` if a nonzero Jacobi field along `γ` vanishes at `t = a` and `t = b`.


### Morse.conjMultiplicity  (Morse.Chapter9.JacobiSpace)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      [FiniteDimensional ℝ V] →
        {Z : Type u_2} →
          [inst_3 : NormedAddCommGroup Z] →
            [inst_4 : NormedSpace ℝ Z] →
              [FiniteDimensional ℝ Z] →
                {W : Type u_3} →
                  [inst_6 : NormedAddCommGroup W] →
                    [inst_7 : NormedSpace ℝ W] →
                      [FiniteDimensional ℝ W] →
                        {N : Set V} →
                          (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) →
                            (γ : ℝ → V) → Morse.IsSmoothCurveIn hN γ → ℝ → ℝ → ℕ
**The multiplicity** of `a` and `b` as conjugate parameter values (Milnor p. 77): the
dimension of the space of Jacobi fields vanishing at `a` and `b` (`0` if they are not
conjugate).


### Morse.conjSpace  (Morse.Chapter9.JacobiSpace)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      [FiniteDimensional ℝ V] →
        {Z : Type u_2} →
          [inst_3 : NormedAddCommGroup Z] →
            [inst_4 : NormedSpace ℝ Z] →
              [FiniteDimensional ℝ Z] →
                {W : Type u_3} →
                  [inst_6 : NormedAddCommGroup W] →
                    [inst_7 : NormedSpace ℝ W] →
                      [FiniteDimensional ℝ W] →
                        {N : Set V} →
                          (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) →
                            (γ : ℝ → V) → Morse.IsSmoothCurveIn hN γ → ℝ → ℝ → Submodule ℝ (ℝ → V)
The space of Jacobi fields vanishing at `a` and `b`.


### Morse.hessNullSpace  (Morse.Chapter9.JacobiSpace)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      [FiniteDimensional ℝ V] →
        {Z : Type u_2} →
          [inst_3 : NormedAddCommGroup Z] →
            [inst_4 : NormedSpace ℝ Z] →
              [FiniteDimensional ℝ Z] →
                {W : Type u_3} →
                  [inst_6 : NormedAddCommGroup W] →
                    [inst_7 : NormedSpace ℝ W] →
                      [FiniteDimensional ℝ W] →
                        {N : Set V} →
                          Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N →
                            {γ : ℝ → V} → {p q : V} → γ ∈ Morse.pathSpace N p q → Submodule ℝ (ℝ → V)
**The null space of `E_**`** (Milnor p. 77), as a space of fields along `γ|[0, 1]`: the image
of the null space of `Morse.energyHessian` under restriction to `[0, 1]`.  (An element of
`TΩ_γ = Morse.pathTangent hN γ` is a function on `ℝ` whose values off `[0, 1]` play no role, and
`E_**` vanishes identically on the fields that vanish on `[0, 1]`.)


### Morse.hessNullity  (Morse.Chapter9.JacobiSpace)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      [FiniteDimensional ℝ V] →
        {Z : Type u_2} →
          [inst_3 : NormedAddCommGroup Z] →
            [inst_4 : NormedSpace ℝ Z] →
              [FiniteDimensional ℝ Z] →
                {W : Type u_3} →
                  [inst_6 : NormedAddCommGroup W] →
                    [inst_7 : NormedSpace ℝ W] →
                      [FiniteDimensional ℝ W] →
                        {N : Set V} →
                          Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N →
                            {γ : ℝ → V} → {p q : V} → γ ∈ Morse.pathSpace N p q → ℕ
**The nullity of `E_**`** (Milnor p. 77): the dimension of its null space.


### Morse.jacobiSpace  (Morse.Chapter9.JacobiSpace)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      [FiniteDimensional ℝ V] →
        {Z : Type u_2} →
          [inst_3 : NormedAddCommGroup Z] →
            [inst_4 : NormedSpace ℝ Z] →
              [FiniteDimensional ℝ Z] →
                {W : Type u_3} →
                  [inst_6 : NormedAddCommGroup W] →
                    [inst_7 : NormedSpace ℝ W] →
                      [FiniteDimensional ℝ W] →
                        {N : Set V} →
                          (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) →
                            (γ : ℝ → V) → Morse.IsSmoothCurveIn hN γ → Submodule ℝ (ℝ → V)
**The vector space `𝒥(γ)` of Jacobi fields along `γ`** (Milnor p. 77), each normalized to be
constant outside `[0, 1]`.


### Morse.restrictIcc  (Morse.Chapter9.JacobiSpace)
(V : Type u_1) → [inst : NormedAddCommGroup V] → [inst_1 : InnerProductSpace ℝ V] → (ℝ → V) →ₗ[ℝ] ℝ → V
Restriction of a function to `[0, 1]`, extended as a constant: `X ↦ X ∘ projIcc`.


### Morse.IsSmoothCurveIn  (Morse.Chapter9.JacobiSystem)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      {Z : Type u_2} →
        [inst_2 : NormedAddCommGroup Z] →
          [inst_3 : NormedSpace ℝ Z] →
            {W : Type u_3} →
              [inst_4 : NormedAddCommGroup W] →
                [inst_5 : NormedSpace ℝ W] →
                  {N : Set V} → Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N → (ℝ → V) → Prop
**A smooth curve in `N` on `[0, 1]`**: `C^∞` on the closed interval (one-sided derivatives at
the ends), with values in `N` there.  (Milnor's `γ : [0, 1] → M`; values off `[0, 1]` play no
role.)


### Morse.curvAlong  (Morse.Chapter9.JacobiSystem)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      [FiniteDimensional ℝ V] →
        {Z : Type u_2} →
          [inst_3 : NormedAddCommGroup Z] →
            [inst_4 : NormedSpace ℝ Z] →
              {W : Type u_3} →
                [inst_5 : NormedAddCommGroup W] →
                  [inst_6 : NormedSpace ℝ W] →
                    {N : Set V} → Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N → (ℝ → V) → ℝ → V →L[ℝ] V
**The curvature coefficient** `K(t)v = R(V, P(t)v)V` of the Jacobi equation.


### Morse.curvMid  (Morse.Chapter9.JacobiSystem)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      [FiniteDimensional ℝ V] →
        {Z : Type u_2} →
          [inst_3 : NormedAddCommGroup Z] →
            [inst_4 : NormedSpace ℝ Z] →
              {W : Type u_3} →
                [inst_5 : NormedAddCommGroup W] →
                  [inst_6 : NormedSpace ℝ W] →
                    {N : Set V} → Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N → ↑N → V → V →L[ℝ] V
The map `b ↦ R(a, b)a = II(b, II(a, a)) − II(a, II(b, a))` at `q ∈ N`, as a continuous linear
map.


### Morse.dpAlong  (Morse.Chapter9.JacobiSystem)
{V : Type u_1} →
  [inst : NormedAddCommGroup V] →
    [inst_1 : InnerProductSpace ℝ V] →
      [FiniteDimensional ℝ V] →
        {Z : Type u_2} →
          [inst_3 : NormedAddCommGroup Z] →
            [inst_4 : NormedSpace ℝ Z] →
              {W : Type u_3} →
                [inst_5 : NormedAddCommGroup W] →
                  [inst_6 : NormedSpace ℝ W] →
                    {N : Set V} → Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N → (ℝ → V) → ℝ → V →L[ℝ] V
`P'(t)`, the derivative within `[0, 1]` of the tangent projection `P(t) = P_{γ(t)}`.


### Morse.velAlong  (Morse.Chapter9.JacobiSystem)
{V : Type u_1} → [inst : NormedAddCommGroup V] → [InnerProductSpace ℝ V] → (ℝ → V) → ℝ → V
The velocity `V(t) = dγ/dt`, computed within `[0, 1]`.


### Morse.Generates  (Morse.Flow.Smooth)
{E : Type u} → [inst : NormedAddCommGroup E] → [NormedSpace ℝ E] → (E → E) → (ℝ → E → E) → Prop
Milnor's definition (p. 10): the vector field `X` **generates** `φ` if
`X_q = lim_{h → 0} (φ_h(q) − q)/h` for every `q` (in `E`, a tangent vector is a vector and
Milnor's `X_q(f)` is the derivative of `f` along it).


### Morse.IsOneParameterGroup  (Morse.Flow.Smooth)
{E : Type u} → [inst : NormedAddCommGroup E] → [NormedSpace ℝ E] → (ℝ → E → E) → Prop
Milnor's definition (pp. 9–10): a **1-parameter group of diffeomorphisms** of `E` is a `C^∞`
map `φ : ℝ × E → E` such that each `φ_t` is a diffeomorphism of `E` onto itself and
`φ_{t+s} = φ_t ∘ φ_s`.


### Morse.Homotopy.genLoopMap  (Morse.Homotopy.Basic)
{N : Type u_1} →
  {X : Type u_2} →
    {Y : Type u_3} →
      [inst : TopologicalSpace X] →
        [inst_1 : TopologicalSpace Y] → (f : C(X, Y)) → {x : X} → ↑(GenLoop N X x) → ↑(GenLoop N Y (f x))
The image `f ∘ γ` of a generalized loop `γ` at `x` under `f : X → Y`, a generalized loop at
`f x`.


### Morse.Homotopy.homotopyGroupMap  (Morse.Homotopy.Basic)
{N : Type u_1} →
  {X : Type u_2} →
    {Y : Type u_3} →
      [inst : TopologicalSpace X] →
        [inst_1 : TopologicalSpace Y] → (f : C(X, Y)) → (x : X) → HomotopyGroup N X x → HomotopyGroup N Y (f x)
**The map induced on homotopy groups**: `f_* : π_N(X, x) → π_N(Y, f x)`, `[γ] ↦ [f ∘ γ]`.


