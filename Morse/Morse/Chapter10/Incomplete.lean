import Morse.Chapter11.NonConjugate
import Morse.Chapter9.IndexTheorem

/-!
Milnor, *Morse Theory*, §17, pp. 95–97: completeness cannot be dropped from Corollary 17.5 (nor
from Theorem 17.3).  The counterexample is `ℝⁿ⁺¹ ∖ {0}` with the flat metric, that is, the metric
induced from `ℝⁿ⁺¹`, of which it is a submanifold of codimension `0`.

# An incomplete manifold with the homotopy type of `Sⁿ`

## Milnor's text, paraphrased

* **Theorem 17.3** (p. 95): if `M` is complete and `p, q ∈ M` are not conjugate along any
  geodesic, then `Ω(M; p, q)` has the homotopy type of a countable CW-complex with one cell of
  dimension `λ` for each geodesic from `p` to `q` of index `λ`.
* **Corollary 17.5** (pp. 96–97): if `M` has the homotopy type of the sphere `Sⁿ`, `n > 2`, then
  any two points of `M` which are not conjugate along any geodesic are joined by infinitely many
  geodesics; the proof gives at least one of index `k(n − 1)` for each `k ≥ 0`.  *Proof*: the
  homology of `Ω(M; p, q)`, which is that of the loop space of `Sⁿ` (Corollary 17.4), is non-zero
  in each dimension `k(n − 1)`, and by Theorem 17.3 each of these dimensions needs a cell, that
  is, a geodesic of that index.  Completeness of `M` is not among the hypotheses of 17.5.

## In the embedded setting

* `Morse.isSliceSubmanifold_of_isOpen`: an open subset `O` of a normed space `V` is a slice
  submanifold of `V` **of codimension `0`**, modelled on `V` itself (one global chart
  `x ↦ (x, 0) ∈ V × W`, `W` zero-dimensional); `Morse.tangentSubspace_of_isOpen`: its tangent
  spaces are all of `V`.
* For a slice submanifold `N ⊆ V` all of whose tangent spaces are `V` (the hypothesis
  `htop : ∀ q : N, tangentSubspace hN q = ⊤`), with the induced metric:
  - `Morse.tanProj_eq_id_of_top`, `Morse.secondFundForm_eq_zero_of_top`,
    `Morse.curvR_eq_zero_of_top`: **the metric is flat**: `P = 1`, `II = dP = 0`, `R = 0`;
  - `Morse.IsGeodesicOn.deriv_deriv_eq_zero_of_top`, `Morse.IsGeodesicOn.eq_add_smul_of_top`,
    `Morse.IsUnbrokenGeodesic.eqOn_segment_of_top`: **geodesics are straight**: `γ'' = 0`, and a
    geodesic from `p` to `q` is the segment `t ↦ p + t (q − p)` on `[0, 1]`;
  - `Morse.IsJacobiField.eqOn_affine_of_top`: Jacobi fields are affine (`J'' = 0`), hence
    `Morse.not_isConjugate_of_top`, `Morse.notMem_conjLocus_of_top`: **there are no conjugate
    points**, and (Theorems 15.1 and 14.1) `Morse.formIndex_energyHessian_eq_zero_of_top`,
    `Morse.hessNullity_eq_zero_of_top`: every geodesic has index `0` and nullity `0`;
  - `Morse.unique_geodesic_of_top`: if the segment `[p, q]` lies in `N`, it is a geodesic in
    `Ω(N; p, q)`, and **every geodesic in `Ω(N; p, q)` agrees with it on `[0, 1]`**.
* `Morse.puncturedSub n`: `N = ℝⁿ⁺¹ ∖ {0}` as a slice submanifold of `ℝⁿ⁺¹`;
  `Morse.tangentSubspace_puncturedSub`, `Morse.curvR_puncturedSub`,
  `Morse.notMem_conjLocus_puncturedSub`, `Morse.formIndex_energyHessian_puncturedSub`,
  `Morse.eqOn_segment_puncturedSub`, `Morse.unique_geodesic_puncturedSub`: the above for `N`.
* `Morse.neg_notMem_expDom_puncturedSub`, `Morse.not_isGeodesicallyComplete_puncturedSub`:
  **`N` is not complete**: `exp_q(−q)` is undefined, the geodesic from `q` with initial velocity
  `−q` runs into the origin at time `1`; `Morse.not_isClosed_punctured`: `N` is not closed in
  `ℝⁿ⁺¹`.
* `Morse.isPathConnected_punctured`: `N` is path-connected for `n ≥ 1`.
* `Morse.puncturedHomotopyEquiv n`: **`N` has the homotopy type of `Sⁿ`**
  (`Milnor.Sphere.Sph n`): the radial projection `x ↦ x / ‖x‖` and the inclusion, with the
  straight-line homotopy from `x / ‖x‖` to `x`.
* `Morse.remark_17_5_completeness`: the counterexample, packaged.

## What Milnor leaves implicit

* **Completeness** (see Exposition/Chapter10.md, §6, the box "A hidden hypothesis" after
  Corollary 17.5): Milnor's statement of 17.5 omits completeness, which Theorem 17.3 needs, and it
  cannot be dropped.  `N = ℝⁿ⁺¹ ∖ {0}` with the flat metric is connected (`n ≥ 1`), has the
  homotopy type of `Sⁿ` and no conjugate points, and two points whose segment misses the origin
  are joined by exactly one geodesic, of index `0`.  For `n ≥ 3` this contradicts the conclusion
  of 17.5.  For `n ≥ 1` it contradicts that of 17.3, which would make `Ω(N; p, q)` a single
  `0`-cell up to homotopy, whereas `Ω(N; p, q)` has the homotopy type of the loop space of `Sⁿ`,
  which is not contractible.  That last comparison is not formalized here (it needs the homotopy
  invariance of path spaces and some homotopy theory of `ΩSⁿ`); what is proved is that every
  hypothesis of the formalized Theorem 17.3 (`Morse.theorem_17_3_nonconj`) holds for `N`, except
  closedness of `N` in the ambient space, which there stands for completeness.
* **Which completeness.**  `N` is neither closed in `ℝⁿ⁺¹` (the hypothesis of the formalized
  Theorem 17.3) nor geodesically complete (`Morse.IsGeodesicallyComplete`, Milnor p. 58): the
  radial geodesic `t ↦ (1 − t) q` reaches the missing origin at `t = 1`.
* **Geodesics are counted by their values on `[0, 1]`**: paths are functions on `ℝ`, so "exactly
  one geodesic" means that every geodesic in `Ω(N; p, q)` agrees with the segment on `[0, 1]`.
* **Flatness in the embedded setting**: the curvature of `N ⊆ V` is computed from the second
  fundamental form `II = dP` (`Morse.curvOp`); for a submanifold of codimension `0` the tangent
  projection `P` is the identity, so `II = 0` and `R = 0`.  The geodesic equation becomes
  `γ'' = 0` and the Jacobi equation `J'' = 0`, and a Jacobi field vanishing at two parameter
  values vanishes identically.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

/-! ### Open subsets of a normed space -/

section OpenSubset

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [Subsingleton W]

variable (V W) in
/-- The global diffeomorphism `x ↦ (x, 0)` of `V` onto `V × W`, for `W` zero-dimensional. -/
def zeroGraph : PartialDiffeomorph 𝓘(ℝ, V) 𝓘(ℝ, V × W) V (V × W) ∞ where
  toFun x := (x, 0)
  invFun z := z.1
  source := univ
  target := univ
  map_source' _ _ := trivial
  map_target' _ _ := trivial
  left_inv' _ _ := rfl
  right_inv' z _ := Prod.ext rfl (Subsingleton.elim _ _)
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := by
    rw [contMDiffOn_iff_contDiffOn]
    exact (contDiff_id.prodMk contDiff_const).contDiffOn
  contMDiffOn_invFun := by
    rw [contMDiffOn_iff_contDiffOn]
    exact contDiff_fst.contDiffOn

/-- **The slice chart of an open set** `O ⊆ V`: `x ↦ (x, 0)` restricted to `O`, with base point
`x₀ ∈ O`.  All of its domain lies in `O`, so the slice condition is automatic. -/
def openSliceChart {O : Set V} (hO : IsOpen O) {x₀ : V} (hx₀ : x₀ ∈ O) :
    Milnor.SliceChart 𝓘(ℝ, V) V W O where
  φ := (zeroGraph V W).restrOpen O hO
  x₀ := x₀
  x₀_mem := hx₀
  x₀_source := ⟨trivial, hx₀⟩
  slice _ hp := ⟨fun _ => Subsingleton.elim _ _, fun _ => hp.2⟩

variable (W) in
/-- **An open subset of a normed space `V` is a slice submanifold of codimension `0`**, modelled
on `V` itself, with any zero-dimensional complement model `W`. -/
theorem isSliceSubmanifold_of_isOpen {O : Set V} (hO : IsOpen O) :
    Milnor.IsSliceSubmanifold 𝓘(ℝ, V) V W O :=
  fun _ hp => ⟨openSliceChart hO hp, ⟨trivial, hp⟩⟩

/-- The parametrization of the chart of an open set is the identity. -/
theorem sliceParam_openSliceChart {O : Set V} (hO : IsOpen O) {x₀ : V} (hx₀ : x₀ ∈ O) :
    sliceParam (openSliceChart (W := W) hO hx₀) = id := rfl

/-- **The tangent spaces of an open subset `O ⊆ V` are all of `V`**, for any slice submanifold
structure on `O` modelled on `V` (computed in the chart `Morse.openSliceChart`). -/
theorem tangentSubspace_of_isOpen {O : Set V} (hO : IsOpen O)
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) V W O) (q : O) :
    tangentSubspace hN q = ⊤ := by
  rw [tangentSubspace_eq_range_fderiv_sliceParam hN (openSliceChart hO q.2) ⟨trivial, q.2⟩,
    sliceParam_openSliceChart, fderiv_id]
  exact LinearMap.range_id

end OpenSubset

/-! ### Calculus: vanishing second derivative -/

section Affine

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **A function with vanishing second derivative on an open preconnected set `s ⊆ ℝ` is affine
there**: `f(t) = f(t₀) + (t − t₀) f'(t₀)`. -/
theorem eq_add_smul_of_hasDerivAt {f f' : ℝ → F} {s : Set ℝ} (hs : IsOpen s)
    (hs' : IsPreconnected s) (hf : ∀ t ∈ s, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ s, HasDerivAt f' 0 t) {t₀ t : ℝ} (ht₀ : t₀ ∈ s) (ht : t ∈ s) :
    f t = f t₀ + (t - t₀) • f' t₀ := by
  have hc : ∀ x ∈ s, f' x = f' t₀ := fun x hx =>
    hs.is_const_of_deriv_eq_zero hs'
      (fun y hy => (hf' y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (hf' y hy).deriv) hx ht₀
  have hg : ∀ x ∈ s, HasDerivAt (fun y => f y - (y - t₀) • f' t₀) 0 x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => (y - t₀) • f' t₀) ((1 : ℝ) • f' t₀) x :=
      ((hasDerivAt_id x).sub_const t₀).smul_const (f' t₀)
    have h2 := (hf x hx).sub h1
    rwa [one_smul, hc x hx, sub_self] at h2
  have := hs.is_const_of_deriv_eq_zero hs' (f := fun y => f y - (y - t₀) • f' t₀)
    (fun y hy => (hg y hy).differentiableAt.differentiableWithinAt) (fun y hy => (hg y hy).deriv)
    ht ht₀
  simp only [sub_self, zero_smul, sub_zero] at this
  rw [← this]
  abel

/-- **A function continuous on `[0, 1]` with vanishing second derivative on `(0, 1)` is affine on
`[0, 1]`**: `f(t) = f(0) + t (f(1) − f(0))`. -/
theorem eqOn_affine_of_hasDerivAt {f f' : ℝ → F} (hc : ContinuousOn f (Icc 0 1))
    (hf : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt f' 0 t) :
    EqOn f (fun t => f 0 + t • (f 1 - f 0)) (Icc 0 1) := by
  have hh : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  set g : ℝ → F := fun t => f (1 / 2) + (t - 1 / 2) • f' (1 / 2)
  have h1 : EqOn f g (Icc 0 1) := by
    refine EqOn.of_subset_closure (s := Ioo 0 1) (fun t ht => eq_add_smul_of_hasDerivAt
      isOpen_Ioo isPreconnected_Ioo hf hf' hh ht) hc ?_ Ioo_subset_Icc_self ?_
    · exact (continuous_const.add ((continuous_id.sub continuous_const).smul
        continuous_const)).continuousOn
    · rw [closure_Ioo zero_ne_one]
  intro t ht
  rw [h1 ht, h1 ⟨le_rfl, zero_le_one⟩, h1 ⟨zero_le_one, le_rfl⟩]
  simp only [g]
  module

end Affine

/-! ### Flat submanifolds of codimension zero -/

section Flat

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- If every tangent space of `N` is all of `V`, the tangent projection is the identity. -/
theorem tanProj_eq_id_of_top (htop : ∀ q : N, tangentSubspace hN q = ⊤) (q : N) :
    tanProj hN q = ContinuousLinearMap.id ℝ V :=
  ContinuousLinearMap.ext fun _ => tanProj_eq_self hN (by rw [htop q]; trivial)

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- The tangent projection `P_x` at a point `x ∈ N` is the identity. -/
theorem prj_eq_id_of_top (htop : ∀ q : N, tangentSubspace hN q = ⊤) {x : V} (hx : x ∈ N) :
    prj hN x = ContinuousLinearMap.id ℝ V := by
  rw [prj_of_mem hN hx, tanProj_eq_id_of_top htop]

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **The second fundamental form of a submanifold of codimension `0` vanishes**: `II = dP` and
`P = 1` is constant. -/
theorem secondFundForm_eq_zero_of_top (htop : ∀ q : N, tangentSubspace hN q = ⊤) (q : N)
    (v w : V) : secondFundForm hN q v w = 0 := by
  have h : tanProj hN = fun _ => ContinuousLinearMap.id ℝ V :=
    funext (tanProj_eq_id_of_top htop)
  rw [secondFundForm, h, dN_const]
  rfl

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **A submanifold of codimension `0` is flat**: its curvature tensor
`R(a, b)c = II(b, II(a, c)) − II(a, II(b, c))` vanishes. -/
theorem curvR_eq_zero_of_top (htop : ∀ q : N, tangentSubspace hN q = ⊤) (x a b c : V) :
    curvR hN x a b c = 0 := by
  by_cases hx : x ∈ N
  · rw [curvR_of_mem hN hx, curvOp_apply, secondFundForm_eq_zero_of_top htop,
      secondFundForm_eq_zero_of_top htop, sub_zero]
  · rw [curvR, dif_neg hx]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **Geodesics of a submanifold of codimension `0` have zero acceleration**: `γ''` is normal to
`T_{γ(t)}N = V`. -/
theorem IsGeodesicOn.deriv_deriv_eq_zero_of_top (htop : ∀ q : N, tangentSubspace hN q = ⊤)
    {γ : ℝ → V} {s : Set ℝ} (h : IsGeodesicOn hN γ s) {t : ℝ} (ht : t ∈ s) :
    deriv (deriv γ) t = 0 := by
  have := h.normal t ht
  rwa [htop, Submodule.top_orthogonal_eq_bot, Submodule.mem_bot] at this

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **Geodesics of a submanifold of codimension `0` are straight lines**: on a preconnected open
set, `γ(t) = γ(t₀) + (t − t₀) γ'(t₀)`. -/
theorem IsGeodesicOn.eq_add_smul_of_top (htop : ∀ q : N, tangentSubspace hN q = ⊤)
    {γ : ℝ → V} {s : Set ℝ} (h : IsGeodesicOn hN γ s) (hs : IsPreconnected s) {t₀ t : ℝ}
    (ht₀ : t₀ ∈ s) (ht : t ∈ s) : γ t = γ t₀ + (t - t₀) • deriv γ t₀ :=
  eq_add_smul_of_hasDerivAt h.isOpen hs (fun _ hx => h.hasDerivAt hx)
    (fun x hx => by
      have := h.hasDerivAt_deriv hx
      rwa [h.deriv_deriv_eq_zero_of_top htop hx] at this) ht₀ ht

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **A geodesic from `p` to `q` in a submanifold of codimension `0` is the segment**
`t ↦ p + t (q − p)` on `[0, 1]`. -/
theorem IsUnbrokenGeodesic.eqOn_segment_of_top (htop : ∀ q : N, tangentSubspace hN q = ⊤)
    {γ : ℝ → V} {p q : V} (hγ : γ ∈ pathSpace N p q) (hgeo : IsUnbrokenGeodesic hN γ) :
    EqOn γ (fun t => p + t • (q - p)) (Icc 0 1) := by
  have h := eqOn_affine_of_hasDerivAt hgeo.1.continuousOn (fun _ ht => hgeo.2.hasDerivAt ht)
    (fun t ht => by
      have := hgeo.2.hasDerivAt_deriv ht
      rwa [hgeo.2.deriv_deriv_eq_zero_of_top htop ht] at this)
  rwa [hγ.2.2.1, hγ.2.2.2] at h

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- In a submanifold of codimension `0` the Jacobi equation is `J'' = 0` (`D/dt = d/dt` and
`R = 0`), along any curve lying in `N` on `(0, 1)`. -/
theorem IsJacobiField.deriv_deriv_eq_zero_of_top (htop : ∀ q : N, tangentSubspace hN q = ⊤)
    {γ J : ℝ → V} (hγ : ∀ t ∈ Ioo (0 : ℝ) 1, γ t ∈ N) (hJ : IsJacobiField hN γ J) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) : deriv (deriv J) t = 0 := by
  have hev : covD hN γ J =ᶠ[𝓝 t] deriv J := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    rw [covD, prj_eq_id_of_top htop (hγ s hs), ContinuousLinearMap.id_apply]
  have := hJ.eq t ht
  rwa [jacobiExpr, curvR_eq_zero_of_top htop, add_zero, covD, prj_eq_id_of_top htop (hγ t ht),
    ContinuousLinearMap.id_apply, hev.deriv_eq] at this

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **Jacobi fields in a submanifold of codimension `0` are affine** on `[0, 1]`:
`J(t) = J(0) + t (J(1) − J(0))`. -/
theorem IsJacobiField.eqOn_affine_of_top (htop : ∀ q : N, tangentSubspace hN q = ⊤)
    {γ J : ℝ → V} (hγ : ∀ t ∈ Ioo (0 : ℝ) 1, γ t ∈ N) (hJ : IsJacobiField hN γ J) :
    EqOn J (fun t => J 0 + t • (J 1 - J 0)) (Icc 0 1) := by
  have hJs : ContDiffOn ℝ ∞ J (Ioo 0 1) := hJ.contDiffOn.mono Ioo_subset_Icc_self
  have hJ' : ContDiffOn ℝ ∞ (deriv J) (Ioo 0 1) := hJs.deriv_of_isOpen isOpen_Ioo (by simp)
  refine eqOn_affine_of_hasDerivAt hJ.contDiffOn.continuousOn (f' := deriv J) (fun t ht => ?_)
    (fun t ht => ?_)
  · exact ((hJs.contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt (by simp)).hasDerivAt
  · have := ((hJ'.contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt (by simp)).hasDerivAt
    rwa [hJ.deriv_deriv_eq_zero_of_top htop hγ ht] at this

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **A submanifold of codimension `0` has no conjugate points**: along any curve lying in `N` on
`(0, 1)`, no two parameter values are conjugate (an affine Jacobi field vanishing at two
parameter values vanishes on `[0, 1]`). -/
theorem not_isConjugate_of_top (htop : ∀ q : N, tangentSubspace hN q = ⊤)
    {γ : ℝ → V} (hγ : ∀ t ∈ Ioo (0 : ℝ) 1, γ t ∈ N) (a b : ℝ) : ¬ IsConjugate hN γ a b := by
  rintro ⟨ha, hb, hab, J, hJ, hJa, hJb, t, ht, hJt⟩
  have h := hJ.eqOn_affine_of_top htop hγ
  have h1 : J 0 + a • (J 1 - J 0) = 0 := (h ha).symm.trans hJa
  have h2 : J 0 + b • (J 1 - J 0) = 0 := (h hb).symm.trans hJb
  have h3 : (b - a) • (J 1 - J 0) = 0 := by
    rw [sub_smul]
    calc b • (J 1 - J 0) - a • (J 1 - J 0)
        = (J 0 + b • (J 1 - J 0)) - (J 0 + a • (J 1 - J 0)) := by abel
      _ = 0 := by rw [h1, h2, sub_zero]
  have h4 : J 1 - J 0 = 0 := (smul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 (Ne.symm hab))
  rw [h4, smul_zero, add_zero] at h1
  have h5 : J t = J 0 + t • (J 1 - J 0) := h ht
  rw [h4, smul_zero, add_zero, h1] at h5
  exact hJt h5

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **In a submanifold of codimension `0` no two points are conjugate along any geodesic**: the
conjugate locus of every point is empty. -/
theorem notMem_conjLocus_of_top (htop : ∀ q : N, tangentSubspace hN q = ⊤) (p q : V) :
    q ∉ conjLocus hN p := by
  rintro ⟨γ, hc, -, -, -, hconj⟩
  exact not_isConjugate_of_top htop (fun t ht => hc.mem t (Ioo_subset_Icc_self ht)) 0 1 hconj

end Flat

/-! ### Straight segments -/

section SegmentCalc

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The segment `t ↦ p + t (q − p)` is smooth. -/
theorem contDiff_segment (p q : V) : ContDiff ℝ ∞ (fun t : ℝ => p + t • (q - p)) :=
  contDiff_const.add (contDiff_id.smul contDiff_const)

/-- The velocity of the segment `t ↦ p + t (q − p)` is `q − p`. -/
theorem deriv_segment (p q : V) : deriv (fun t : ℝ => p + t • (q - p)) = fun _ => q - p := by
  funext s
  simpa using (((hasDerivAt_id s).smul_const (q - p)).const_add p).deriv

end SegmentCalc

section Segment

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

omit [FiniteDimensional ℝ V] in
/-- A segment lying in `N` is a path in `Ω(N; p, q)`. -/
theorem segment_mem_pathSpace {p q : V} (hseg : ∀ t ∈ Icc (0 : ℝ) 1, p + t • (q - p) ∈ N) :
    (fun t : ℝ => p + t • (q - p)) ∈ pathSpace N p q :=
  ⟨IsPiecewiseSmooth.of_contDiffOn (contDiff_segment p q).contDiffOn zero_le_one (subset_univ _),
    hseg, by simp, by simp⟩

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **A segment lying in `N` is a geodesic** of `N` (its acceleration `0` is normal to `N`). -/
theorem isUnbrokenGeodesic_segment {p q : V}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, p + t • (q - p) ∈ N) :
    IsUnbrokenGeodesic hN (fun t : ℝ => p + t • (q - p)) := by
  refine ⟨(contDiff_segment p q).contDiffOn, isOpen_Ioo,
    fun t ht => hseg t (Ioo_subset_Icc_self ht), (contDiff_segment p q).contDiffOn, fun t _ => ?_⟩
  rw [deriv_segment, deriv_const]
  exact Submodule.zero_mem _

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **Exactly one geodesic**: in a submanifold `N` of codimension `0`, if the segment `[p, q]`
lies in `N`, it is a geodesic in `Ω(N; p, q)`, and every geodesic in `Ω(N; p, q)` agrees with it
on `[0, 1]`. -/
theorem unique_geodesic_of_top (htop : ∀ q : N, tangentSubspace hN q = ⊤) {p q : V}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, p + t • (q - p) ∈ N) :
    (fun t : ℝ => p + t • (q - p)) ∈ pathSpace N p q ∧
      IsUnbrokenGeodesic hN (fun t : ℝ => p + t • (q - p)) ∧
      ∀ γ ∈ pathSpace N p q, IsUnbrokenGeodesic hN γ →
        EqOn γ (fun t => p + t • (q - p)) (Icc 0 1) :=
  ⟨segment_mem_pathSpace hseg, isUnbrokenGeodesic_segment hseg,
    fun _ hγ hgeo => hgeo.eqOn_segment_of_top htop hγ⟩

/-- **Every geodesic of a submanifold of codimension `0` has index `0`** (Theorem 15.1: there are
no conjugate points). -/
theorem formIndex_energyHessian_eq_zero_of_top (htop : ∀ q : N, tangentSubspace hN q = ⊤)
    {γ : ℝ → V} {p q : V} (hγ : γ ∈ pathSpace N p q) (hgeo : IsUnbrokenGeodesic hN γ) :
    formIndex (energyHessian hN hγ) = 0 := by
  have hγN : ∀ t ∈ Ioo (0 : ℝ) 1, γ t ∈ N := fun t ht => hγ.2.1 t (Ioo_subset_Icc_self ht)
  rw [(theorem_15_1 hN hγ hgeo).2, finsum_mem_eq_zero_of_forall_eq_zero fun t ht => ?_,
    Nat.cast_zero]
  by_contra h
  exact not_isConjugate_of_top htop hγN 0 t ((isConjugate_iff (hgeo.isSmoothCurveIn hN hγ)).2
    ⟨⟨le_rfl, zero_le_one⟩, Ioo_subset_Icc_self ht, ht.1.ne, Nat.pos_of_ne_zero h⟩)

/-- **Every geodesic of a submanifold of codimension `0` is non-degenerate** (Theorem 14.1: its
end points are not conjugate). -/
theorem hessNullity_eq_zero_of_top (htop : ∀ q : N, tangentSubspace hN q = ⊤)
    {γ : ℝ → V} {p q : V} (hγ : γ ∈ pathSpace N p q) (hgeo : IsUnbrokenGeodesic hN γ) :
    hessNullity hN hγ = 0 :=
  hessNullity_eq_zero_of_notMem_conjLocus (notMem_conjLocus_of_top htop p q) hγ hgeo

end Segment

/-! ### The punctured space `ℝⁿ⁺¹ ∖ {0}` -/

section Punctured

open Milnor.Sphere

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin (n + 1))

variable (n) in
/-- **`ℝⁿ⁺¹ ∖ {0}` is a slice submanifold of `ℝⁿ⁺¹`** of codimension `0`, modelled on `ℝⁿ⁺¹`
itself (complement model `ℝ⁰`); with the induced metric it is flat. -/
theorem puncturedSub :
    Milnor.IsSliceSubmanifold 𝓘(ℝ, 𝔼) 𝔼 (EuclideanSpace ℝ (Fin 0)) ({0}ᶜ : Set 𝔼) :=
  isSliceSubmanifold_of_isOpen _ isOpen_compl_singleton

/-- The tangent spaces of `ℝⁿ⁺¹ ∖ {0}` are all of `ℝⁿ⁺¹`. -/
theorem tangentSubspace_puncturedSub (q : ({0}ᶜ : Set 𝔼)) :
    tangentSubspace (puncturedSub n) q = ⊤ :=
  tangentSubspace_of_isOpen isOpen_compl_singleton _ q

/-- **`ℝⁿ⁺¹ ∖ {0}` is flat**: its curvature tensor vanishes. -/
theorem curvR_puncturedSub (x a b c : 𝔼) : curvR (puncturedSub n) x a b c = 0 :=
  curvR_eq_zero_of_top tangentSubspace_puncturedSub x a b c

/-- **No two points of `ℝⁿ⁺¹ ∖ {0}` are conjugate along any geodesic.** -/
theorem notMem_conjLocus_puncturedSub (p q : 𝔼) : q ∉ conjLocus (puncturedSub n) p :=
  notMem_conjLocus_of_top tangentSubspace_puncturedSub p q

/-- **Every geodesic of `ℝⁿ⁺¹ ∖ {0}` has index `0`** (Theorem 15.1). -/
theorem formIndex_energyHessian_puncturedSub {γ : ℝ → 𝔼} {p q : 𝔼}
    (hγ : γ ∈ pathSpace ({0}ᶜ : Set 𝔼) p q) (hgeo : IsUnbrokenGeodesic (puncturedSub n) γ) :
    formIndex (energyHessian (puncturedSub n) hγ) = 0 :=
  formIndex_energyHessian_eq_zero_of_top tangentSubspace_puncturedSub hγ hgeo

/-- **A geodesic of `ℝⁿ⁺¹ ∖ {0}` from `p` to `q` is the segment** `t ↦ p + t (q − p)` on
`[0, 1]`. -/
theorem eqOn_segment_puncturedSub {γ : ℝ → 𝔼} {p q : 𝔼}
    (hγ : γ ∈ pathSpace ({0}ᶜ : Set 𝔼) p q) (hgeo : IsUnbrokenGeodesic (puncturedSub n) γ) :
    EqOn γ (fun t => p + t • (q - p)) (Icc 0 1) :=
  hgeo.eqOn_segment_of_top tangentSubspace_puncturedSub hγ

/-- **Exactly one geodesic**: if the segment `[p, q]` misses the origin, it is a geodesic of
`ℝⁿ⁺¹ ∖ {0}` from `p` to `q`, and every geodesic in `Ω(ℝⁿ⁺¹ ∖ {0}; p, q)` agrees with it on
`[0, 1]`. -/
theorem unique_geodesic_puncturedSub {p q : 𝔼}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, p + t • (q - p) ≠ 0) :
    (fun t : ℝ => p + t • (q - p)) ∈ pathSpace ({0}ᶜ : Set 𝔼) p q ∧
      IsUnbrokenGeodesic (puncturedSub n) (fun t : ℝ => p + t • (q - p)) ∧
      ∀ γ ∈ pathSpace ({0}ᶜ : Set 𝔼) p q, IsUnbrokenGeodesic (puncturedSub n) γ →
        EqOn γ (fun t => p + t • (q - p)) (Icc 0 1) :=
  unique_geodesic_of_top tangentSubspace_puncturedSub hseg

/-- **`exp_q(−q)` is undefined in `ℝⁿ⁺¹ ∖ {0}`**: a geodesic with `γ(0) = q`, `γ'(0) = −q` is
`t ↦ (1 − t) q`, which reaches the origin at `t = 1`. -/
theorem neg_notMem_expDom_puncturedSub (q : 𝔼) : (q, -q) ∉ expDom (puncturedSub n) := by
  rintro ⟨γ, δ, hδ, hgeo, h0, hd0⟩
  have h0' : (0 : ℝ) ∈ Ioo (-δ) (1 + δ) := ⟨by linarith, by linarith⟩
  have h1 : (1 : ℝ) ∈ Ioo (-δ) (1 + δ) := ⟨by linarith, by linarith⟩
  have h := hgeo.eq_add_smul_of_top tangentSubspace_puncturedSub isPreconnected_Ioo h0' h1
  rw [h0, hd0, sub_zero, one_smul, add_neg_cancel] at h
  exact hgeo.mem 1 h1 h

/-- The first basis vector of `ℝⁿ⁺¹` is non-zero. -/
theorem euclideanSpace_single_ne_zero : (EuclideanSpace.single 0 1 : 𝔼) ≠ 0 := by
  intro h
  have := congrArg (fun x : 𝔼 => x 0) h
  simp at this

/-- **`ℝⁿ⁺¹ ∖ {0}` is not geodesically complete** (Milnor p. 58). -/
theorem not_isGeodesicallyComplete_puncturedSub :
    ¬ IsGeodesicallyComplete (puncturedSub n) := fun hc =>
  neg_notMem_expDom_puncturedSub _ (hc ⟨_, euclideanSpace_single_ne_zero⟩ _
    (by rw [tangentSubspace_puncturedSub]; trivial))

variable (n) in
/-- **`ℝⁿ⁺¹ ∖ {0}` is not closed in `ℝⁿ⁺¹`.** -/
theorem not_isClosed_punctured : ¬ IsClosed ({0}ᶜ : Set 𝔼) :=
  isClosed_compl_iff.not.2 (not_isOpen_singleton 0)

/-- **`ℝⁿ⁺¹ ∖ {0}` is path-connected** for `n ≥ 1`. -/
theorem isPathConnected_punctured (hn : 1 ≤ n) : IsPathConnected ({0}ᶜ : Set 𝔼) := by
  refine isPathConnected_compl_singleton_of_one_lt_rank ?_ 0
  rw [← finrank_eq_rank, finrank_euclideanSpace_fin]
  exact_mod_cast (by omega : 1 < n + 1)

variable (n) in
/-- The radial projection `x ↦ x / ‖x‖` of `ℝⁿ⁺¹ ∖ {0}` onto `Sⁿ`. -/
def radialProj : C(({0}ᶜ : Set 𝔼), Sph n) where
  toFun x := ⟨‖(x : 𝔼)‖⁻¹ • (x : 𝔼), mem_iff_norm.2 (by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 x.2)])⟩
  continuous_toFun := ((continuous_subtype_val.norm.inv₀ fun x => norm_ne_zero_iff.2 x.2).smul
    continuous_subtype_val).subtype_mk _

/-- The points of `Sⁿ` are non-zero. -/
theorem ne_zero_of_mem_sph {x : 𝔼} (hx : x ∈ Sph n) : x ≠ 0 := by
  intro h
  have := mem_iff_norm.1 hx
  rw [h, norm_zero] at this
  exact zero_ne_one this

variable (n) in
/-- The inclusion `Sⁿ → ℝⁿ⁺¹ ∖ {0}`. -/
def sphIncl : C(Sph n, ({0}ᶜ : Set 𝔼)) where
  toFun x := ⟨x, ne_zero_of_mem_sph x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The coefficient of the straight-line homotopy from `x / ‖x‖` to `x` is positive. -/
theorem radialCoeff_pos (t : unitInterval) {x : 𝔼} (hx : x ≠ 0) :
    0 < (1 - (t : ℝ)) * ‖x‖⁻¹ + t := by
  have h1 : 0 ≤ 1 - (t : ℝ) := by linarith [t.2.2]
  have h2 : 0 < ‖x‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hx)
  rcases (t.2.1 : (0 : ℝ) ≤ t).eq_or_lt with h | h
  · rw [← h, sub_zero, one_mul, add_zero]
    exact h2
  · exact add_pos_of_nonneg_of_pos (mul_nonneg h1 h2.le) h

variable (n) in
/-- **`ℝⁿ⁺¹ ∖ {0}` has the homotopy type of `Sⁿ`**: the radial projection and the inclusion are
inverse homotopy equivalences (the straight-line homotopy `((1 − t)/‖x‖ + t) x` from `x / ‖x‖`
to `x` stays away from the origin). -/
def puncturedHomotopyEquiv : ContinuousMap.HomotopyEquiv ({0}ᶜ : Set 𝔼) (Sph n) where
  toFun := radialProj n
  invFun := sphIncl n
  left_inv := ⟨{
    toFun := fun x => ⟨((1 - (x.1 : ℝ)) * ‖(x.2 : 𝔼)‖⁻¹ + x.1) • (x.2 : 𝔼),
      smul_ne_zero (radialCoeff_pos x.1 x.2.2).ne' x.2.2⟩
    continuous_toFun := by
      refine Continuous.subtype_mk ?_ _
      have h1 : Continuous fun x : unitInterval × ({0}ᶜ : Set 𝔼) => (x.2 : 𝔼) :=
        continuous_subtype_val.comp continuous_snd
      have h2 : Continuous fun x : unitInterval × ({0}ᶜ : Set 𝔼) => (x.1 : ℝ) :=
        continuous_subtype_val.comp continuous_fst
      have h3 : Continuous fun x : unitInterval × ({0}ᶜ : Set 𝔼) => ‖(x.2 : 𝔼)‖⁻¹ :=
        h1.norm.inv₀ fun x => norm_ne_zero_iff.2 x.2.2
      exact (((continuous_const.sub h2).mul h3).add h2).smul h1
    map_zero_left := fun x => by
      ext1
      simp [radialProj, sphIncl]
    map_one_left := fun x => by
      ext1
      simp }⟩
  right_inv := by
    have : (radialProj n).comp (sphIncl n) = ContinuousMap.id _ := by
      ext x : 2
      simp [radialProj, sphIncl, mem_iff_norm.1 x.2]
    rw [this]

variable (n) in
/-- **Completeness cannot be dropped from Corollary 17.5** (Milnor pp. 96–97; Exposition,
Chapter 10, §6, "A hidden hypothesis").  For `n ≥ 1`, `N = ℝⁿ⁺¹ ∖ {0}` with the flat metric:

* has the homotopy type of the sphere `Sⁿ`, and is path-connected;
* is neither closed in `ℝⁿ⁺¹` nor geodesically complete;
* has no conjugate points: no `q` is conjugate to any `p` along any geodesic;
* has points `p ≠ q` joined by exactly one geodesic: every geodesic in `Ω(N; p, q)` agrees on
  `[0, 1]` with the segment.

So for `n ≥ 3` the conclusion of 17.5 (infinitely many geodesics, one of index `k(n − 1)` for
each `k`) fails.  For `n ≥ 1` the conclusion of Theorem 17.3 fails as well: the unique geodesic
has index `0` (`Morse.formIndex_energyHessian_puncturedSub`), so 17.3 would make `Ω(N; p, q)`
a single point up to homotopy, whereas `Ω(N; p, q) ≃ Ω(Sⁿ)` is not contractible (this last fact
is not formalized).  The hypothesis `n ≥ 1` is used only for connectedness. -/
theorem remark_17_5_completeness (hn : 1 ≤ n) :
    Nonempty (ContinuousMap.HomotopyEquiv ({0}ᶜ : Set 𝔼) (Sph n)) ∧
    IsPathConnected ({0}ᶜ : Set 𝔼) ∧ ¬ IsClosed ({0}ᶜ : Set 𝔼) ∧
    ¬ IsGeodesicallyComplete (puncturedSub n) ∧
    (∀ p q : 𝔼, q ∉ conjLocus (puncturedSub n) p) ∧
    ∃ p q : 𝔼, p ≠ 0 ∧ q ≠ 0 ∧ p ≠ q ∧
      ∃ γ ∈ pathSpace ({0}ᶜ : Set 𝔼) p q, IsUnbrokenGeodesic (puncturedSub n) γ ∧
        ∀ γ' ∈ pathSpace ({0}ᶜ : Set 𝔼) p q, IsUnbrokenGeodesic (puncturedSub n) γ' →
          EqOn γ' γ (Icc 0 1) := by
  refine ⟨⟨puncturedHomotopyEquiv n⟩, isPathConnected_punctured hn, not_isClosed_punctured n,
    not_isGeodesicallyComplete_puncturedSub, notMem_conjLocus_puncturedSub, ?_⟩
  set e : 𝔼 := EuclideanSpace.single 0 1
  have he : e ≠ 0 := euclideanSpace_single_ne_zero
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, e + t • ((2 : ℝ) • e - e) ≠ 0 := by
    intro t ht h
    have h' : (1 + t) • e = 0 := by rw [← h]; module
    exact he ((smul_eq_zero.1 h').resolve_left (by linarith [ht.1]))
  obtain ⟨h1, h2, h3⟩ := unique_geodesic_puncturedSub hseg
  refine ⟨e, (2 : ℝ) • e, he, smul_ne_zero two_ne_zero he, fun h => he ?_, _, h1, h2, h3⟩
  rw [two_smul] at h
  exact left_eq_add.1 h

end Punctured

end Morse
