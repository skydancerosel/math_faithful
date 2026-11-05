import Morse.Chapter11.ExpCovering
import Morse.Chapter10.FundamentalTheorem
import Morse.Chapter10.FullPathTheorem

/-!
Milnor, *Morse Theory*, §19, pp. 102–103: **Theorem 19.2** (Cartan–Hadamard), the paragraph on
non-simply-connected manifolds, and the first part of **Corollary 19.3**, for a submanifold
`N ⊆ ℝᴷ` with the induced metric, complete (closed in `ℝᴷ`).

# The theorem of Cartan and Hadamard

## Milnor's text, paraphrased

* **Theorem 19.2** (Cartan, p. 102): if `M` is simply connected and complete, with sectional
  curvature `⟨R(A, B)A, B⟩ ≤ 0` everywhere, then any two points of `M` are joined by a unique
  geodesic, and `M` is diffeomorphic to `ℝⁿ`.  Proof (pp. 102–103): there are no conjugate
  points (19.1), so every geodesic from `p` to `q` has index `0`, and by 17.3 `Ω(M; p, q)` has the
  homotopy type of a `0`-dimensional CW complex with one vertex for each geodesic.  As `M` is
  simply connected, `Ω(M; p, q)` is connected, and a connected `0`-dimensional complex is a point:
  there is exactly one geodesic from `p` to `q`.  So `exp_p` is one-one and onto; by 18.1 it is
  non-critical, hence a local diffeomorphism, hence a diffeomorphism.
* (p. 103) If `M` is complete with curvature `≤ 0` but not simply connected, the universal
  covering `M̃` inherits a complete metric of curvature `≤ 0`, and each homotopy class of paths
  from `p` to `q` contains precisely one geodesic.
* **Corollary 19.3** (p. 103): if `M` is complete with curvature `≤ 0`, then `πᵢ(M) = 0` for
  `i > 1`, and `π₁(M)` has no element of finite order other than the identity.  Proof:
  `πᵢ(M) = πᵢ(M̃) = 0` for `i > 1` since `M̃` is contractible; `Hᵏ(M)` is the cohomology of the
  group `π₁(M)` (Hu), so a non-trivial finite cyclic subgroup `G` would give a covering `M̂` with
  `Hᵏ(G) = Hᵏ(M̂) = 0` for `k > n`, while the cohomology of a finite cyclic group is non-trivial
  in arbitrarily high dimensions.

## In the embedded setting

* `Morse.isCoveringMap_expToN_of_nonpos`: in curvature `≤ 0`, **`exp_p : T_pN → N` is a covering
  map** (`Morse.isCoveringMap_expToN` with Lemma 19.1).
* `Morse.injective_expToN_of_simplyConnected`, `Morse.surjective_expToN`,
  `Morse.expDiffeomorph`: **for simply connected `N`, `exp_p` is a diffeomorphism** `T_pN ≅ N`
  (Mathlib's `Diffeomorph`, for the manifold structure of `N`).
* `Morse.theorem_19_2`: **Theorem 19.2**: if `N` is complete (`Morse.IsGeodesicallyComplete`,
  e.g. `N` closed in `V`), simply connected (`SimplyConnectedSpace N`) and of curvature `≤ 0`
  (`Morse.NonposCurvature`), any two points are joined by a geodesic `γ ∈ Ω(N; p, q)`, unique on
  `[0, 1]`, and `N` is diffeomorphic to `ℝⁿ`, `n = dim N`.
* `Morse.homotopy_class_unique_geodesic`: **each homotopy class of paths from `p` to `q` contains
  exactly one geodesic** (p. 103), for complete `N` of curvature `≤ 0`.
* `Morse.corollary_19_3`: **Corollary 19.3, first part**: `πᵢ(N) = 0` for `i > 1` at every base
  point (Mathlib's `HomotopyGroup.Pi`); `Morse.genLoop_homotopic_const`: every generalized loop
  `Iⁱ → N`, `i ≥ 2`, is null-homotopic relative to the boundary of the cube.
* `Morse.omega_cells_of_nonpos`: **Milnor's description of the path space**: for `N` closed with
  curvature `≤ 0` and any `p, q ∈ N`, `Ω(N; p, q)` has the homotopy type of a countable cell
  complex all of whose cells are `0`-cells, one for each geodesic from `p` to `q` (Theorem 17.3
  with all indices `0`); `Morse.omega_single_cell`: for simply connected `N` it has exactly one
  cell.
* `Morse.omega_homotopyEquiv_fiber`: **`Ω(N; p, q)` has the homotopy type of a countable discrete
  set**, the fibre of `exp_p` over `q`, whose points are the geodesics from `p` to `q`
  (`Morse.geodesic_iff_mem_fiber`); through Theorem 17.1 from `Ω*` (continuous paths), which is
  homotopy equivalent to the fibre by lifting paths through the covering
  (`Morse.nonempty_homotopyEquiv_pathC_fiber`).  `Morse.contractibleSpace_pathSp`: **for simply
  connected `N`, `Ω(N; p, q)` is contractible**, the homotopy type of a point, as Milnor's proof
  asserts (`Ω*` contracts onto a geodesic through the diffeomorphism `exp_p`,
  `Morse.contractibleSpace_pathC`).

## What Milnor leaves implicit

* **The order of the argument is reversed here.**  Milnor deduces the uniqueness of geodesics
  from the connectedness of `Ω(M; p, q)`, which needs Theorem 17.1 to identify the components of
  `Ω` with the homotopy classes of paths (the exposition's remark), and the components of the cell
  complex of 17.3 with its vertices.  Here the covering `exp_p` gives the uniqueness (in a simply
  connected `N` the image of a segment of `T_pN` with both ends over one point is a null-homotopic
  loop, whose lift is closed), and then the cell complex of 17.3 has exactly one cell.  Both
  routes rest on Lemma 19.1; the covering route needs, instead of 17.1, the completeness of the
  metric pulled back to `T_pN` (`Morse.norm_expLift_le`).
* **"Hence a global diffeomorphism"**: a bijective local diffeomorphism is a diffeomorphism
  (Mathlib's `IsLocalDiffeomorph.diffeomorphOfBijective`).  That `exp_p` is onto is the
  Hopf–Rinow theorem (10.9), which needs `M` connected (part of "simply connected").
* **`M ≅ ℝⁿ`**: `T_pN` is an `n`-dimensional real vector space.
* **The universal covering** of p. 103 and Corollary 19.3 is `exp_p : T_pN → N` itself; no
  abstract covering space and no metric on it are needed.
* **"Clearly `πᵢ(M) = πᵢ(M̃)`"**: a map of a cube `Iⁱ` lifts through the covering because the
  cube is simply connected (contractible) and locally path connected; the lift is constant on the
  boundary of the cube because the fibre is discrete and the boundary is connected for `i ≥ 2`
  (each face is connected, and the faces `yᵢ = a` and `yⱼ = 0` meet when `i ≠ j`).  For `i = 1`
  the boundary `{0, 1}` is not connected, which is where the argument (and the statement) stops.
* **"`Ω(M; p, q)` has the homotopy type of a `0`-dimensional complex, one vertex for each
  geodesic"**: here the homotopy type is computed without 17.3: lifting a path from `p` to `q`
  from `0 ∈ T_pN` and taking the end point is a homotopy equivalence of `Ω*` with the fibre of
  `exp_p` over `q` (a path is homotopic, relative to its end points, to the geodesic whose lift is
  the segment to the same end point), and `Ω ≃ Ω*` by Theorem 17.1.
* **"Each homotopy class contains precisely one geodesic"**: every geodesic from `p` is radial
  (`Morse.theorem_18_1_of_geodesic`), so the geodesics from `p` are the images of the segments from
  `0` in `T_pN`, which are their lifts; homotopic paths have lifts from `0` with the same end
  point, and two paths of `T_pN` with the same end points are homotopic.

## Not done here

* **The second part of Corollary 19.3** (`π₁(N)` has no non-trivial element of finite order):
  Milnor's proof uses the cohomology of groups (`Hᵏ(M) ≅ Hᵏ(π₁(M))` for `M` with contractible
  universal covering, Hu) and the cohomology of finite cyclic groups, which are not available.
* **The cell complex of 17.3 with only `0`-cells as a discrete space**: the cell complexes of
  Theorem 17.3 are mapping telescopes of finite stages (`Morse.IsCountableCellComplexType`); that
  such a telescope with only `0`-cells is homotopy equivalent to a discrete space is not
  formalized.  (The homotopy type of `Ω` itself is obtained directly from the covering,
  `Morse.omega_homotopyEquiv_fiber`.)
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace unitInterval

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

/-! ### `exp_p` in non-positive curvature -/

/-- In non-positive curvature `exp_p` is nowhere critical, on all of `T_pN` when `N` is complete
(Lemma 19.1 with Theorem 18.1). -/
theorem injective_dExpAt_of_nonpos' (hc : IsGeodesicallyComplete hN) (hK : NonposCurvature hN)
    (p : N) (v : tangentSubspace hN p) : Injective (dExpAt hN p v) :=
  injective_dExpAt_of_nonpos hK (hc p v v.2)

/-- **`exp_p` is a covering map in non-positive curvature**. -/
theorem isCoveringMap_expToN_of_nonpos (hc : IsGeodesicallyComplete hN)
    (hK : NonposCurvature hN) (p : N) : IsCoveringMap (expToN hN p) :=
  isCoveringMap_expToN hc (injective_dExpAt_of_nonpos' hc hK p)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **In a simply connected `N`, a covering `exp_p` is one-to-one**: the image of the segment
from `v₁` to `v₂` is a loop, null-homotopic, so its lift from `v₁` ends at `v₁`. -/
theorem injective_expToN_of_simplyConnected {p : N} (hcov : IsCoveringMap (expToN hN p))
    (hsc : SimplyConnectedSpace N) : Injective (expToN hN p) := by
  intro v₁ v₂ h
  set f := expToN hN p with hf_def
  let seg : C(I, tangentSubspace hN p) :=
    ⟨fun t => v₁ + (t : ℝ) • (v₂ - v₁), by fun_prop⟩
  let γ : C(I, N) := (⟨f, hcov.continuous⟩ : C(tangentSubspace hN p, N)).comp seg
  have hγ0 : γ 0 = f v₁ := by simp [γ, seg]
  have hγ1 : γ 1 = f v₁ := by simp [γ, seg, h]
  let γp : Path (f v₁) (f v₁) := ⟨γ, hγ0, hγ1⟩
  have hhom : γ.HomotopicRel (ContinuousMap.const I (f v₁)) {0, 1} :=
    SimplyConnectedSpace.paths_homotopic γp (Path.refl _)
  have h1 := hcov.liftPath_apply_one_eq_of_homotopicRel hhom v₁ hγ0 rfl
  have hseg : seg = hcov.liftPath γ v₁ hγ0 :=
    (hcov.eq_liftPath_iff' hγ0).2 ⟨rfl, by simp [seg]⟩
  rw [← hseg, hcov.liftPath_const rfl] at h1
  simpa [seg] using h1.symm

/-! ### Theorem 19.2 -/

/-- **`exp_p` is onto** when `N` is connected and complete (the Hopf–Rinow theorem, 10.9). -/
theorem surjective_expToN (hc : IsGeodesicallyComplete hN) (hconn : IsPreconnected N) (p : N) :
    Surjective (expToN hN p) := by
  intro q
  obtain ⟨v, hv, hexp, -⟩ := theorem_10_9 (hc p) (riemDist_ne_top hN hconn p.2 q.2)
  exact ⟨⟨v, hv⟩, Subtype.ext ((coe_expToN_of_mem (hc p v hv)).trans hexp)⟩

/-- The radial geodesic `t ↦ exp_p(tv)`, `0 ≤ t ≤ 1`, is an unbroken geodesic in
`Ω(N; p, exp_p(v))`. -/
theorem ray_mem_pathSpace (hc : IsGeodesicallyComplete hN) {p : N} (v : tangentSubspace hN p) :
    (fun t : ℝ => exp hN p (t • (v : V))) ∈ pathSpace N p (exp hN p v) ∧
      IsUnbrokenGeodesic hN (fun t : ℝ => exp hN p (t • (v : V))) := by
  have hgeo := isGeodesicOn_univ_exp_smul (hc p) v.2
  refine ⟨⟨IsPiecewiseSmooth.of_contDiffOn hgeo.contDiffOn zero_le_one (subset_univ _),
    fun t _ => hgeo.mem t (mem_univ t), by simp [exp_zero p.2], by simp⟩,
    hgeo.contDiffOn.mono (subset_univ _), hgeo.mono isOpen_Ioo (subset_univ _)⟩

/-- **Every geodesic from `p` is radial**: a geodesic `γ ∈ Ω(N; p, q)` is `t ↦ exp_p(tv)` on
`[0, 1]` for some `v ∈ T_pN` with `exp_p(v) = q`. -/
theorem exists_eqOn_ray {p : N} {q : V} {γ : ℝ → V}
    (hγ : γ ∈ pathSpace N p q) (hgeo : IsUnbrokenGeodesic hN γ) :
    ∃ v : tangentSubspace hN p, exp hN p v = q ∧
      EqOn γ (fun t : ℝ => exp hN p (t • (v : V))) (Icc 0 1) := by
  have hcs := hgeo.isSmoothCurveIn hN hγ
  obtain ⟨v, hv, -, hexp, -⟩ := theorem_18_1_of_geodesic hcs hgeo.2 hγ.2.2.1
  obtain ⟨η, -, -, hray⟩ := exists_initial_ray hcs hgeo.2
  refine ⟨v, hexp.trans hγ.2.2.2, fun t ht => ?_⟩
  rw [← hray t ht, hγ.2.2.1, hv]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z]
  [FiniteDimensional ℝ W] in
/-- A simply connected `N` is connected. -/
theorem isPreconnected_of_simplyConnected (hsc : SimplyConnectedSpace N) : IsPreconnected N :=
  isPreconnected_iff_preconnectedSpace.2 inferInstance

/-- A closed `N ⊆ V` is (geodesically) complete (`Morse.isRiemComplete_of_isClosed` and the
converse of Corollary 10.10). -/
theorem isGeodesicallyComplete_of_isClosed (hcl : IsClosed N) : IsGeodesicallyComplete hN :=
  isGeodesicallyComplete_of_isRiemComplete (isRiemComplete_of_isClosed hN hcl)

/-- **`exp_p` is a diffeomorphism** `T_pN ≅ N` when `N` is simply connected and complete with
curvature `≤ 0` (the last step of Milnor's proof of Theorem 19.2: a bijective local
diffeomorphism). -/
def expDiffeomorph (hc : IsGeodesicallyComplete hN) (hK : NonposCurvature hN)
    (hsc : SimplyConnectedSpace N) (p : N) :
    letI := hN.chartedSpace
    Diffeomorph 𝓘(ℝ, tangentSubspace hN p) 𝓘(ℝ, Z) (tangentSubspace hN p) N ∞ :=
  letI := hN.chartedSpace
  (isLocalDiffeomorph_expToN hc (injective_dExpAt_of_nonpos' hc hK p)).diffeomorphOfBijective
    ⟨injective_expToN_of_simplyConnected (isCoveringMap_expToN_of_nonpos hc hK p) hsc,
      surjective_expToN hc (isPreconnected_of_simplyConnected hsc) p⟩

theorem coe_expDiffeomorph (hc : IsGeodesicallyComplete hN) (hK : NonposCurvature hN)
    (hsc : SimplyConnectedSpace N) (p : N) :
    letI := hN.chartedSpace
    ⇑(expDiffeomorph hc hK hsc p) = expToN hN p := rfl

/-- **Theorem 19.2 (Cartan)** (Milnor p. 102): if `N` is simply connected and complete and all
sectional curvatures are `≤ 0`, then any two points of `N` are joined by a unique geodesic
`γ : [0, 1] → N`, and `N` is diffeomorphic to `ℝⁿ`, `n = dim N`.  (A closed `N ⊆ V` is complete:
`Morse.isGeodesicallyComplete_of_isClosed`.) -/
theorem theorem_19_2 (hc : IsGeodesicallyComplete hN) (hsc : SimplyConnectedSpace N)
    (hK : NonposCurvature hN) :
    (∀ p q : N, ∃ γ : ℝ → V, γ ∈ pathSpace N p q ∧ IsUnbrokenGeodesic hN γ ∧
      ∀ γ' ∈ pathSpace N p q, IsUnbrokenGeodesic hN γ' → EqOn γ' γ (Icc 0 1)) ∧
    (letI := hN.chartedSpace
     Nonempty (Diffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ Z))) 𝓘(ℝ, Z)
       (EuclideanSpace ℝ (Fin (finrank ℝ Z))) N ∞)) := by
  let _ := hN.chartedSpace
  refine ⟨fun p q => ?_, ?_⟩
  · set D := expDiffeomorph hc hK hsc p
    set v := D.symm q with hv_def
    have hvq : exp hN p v = q := by
      have h1 : expToN hN p v = q := D.apply_symm_apply q
      rw [← h1, coe_expToN_of_mem (hc p _ v.2)]
    obtain ⟨hmem, hgeo⟩ := ray_mem_pathSpace hc v
    rw [hvq] at hmem
    refine ⟨_, hmem, hgeo, fun γ' hγ' hgeo' => ?_⟩
    obtain ⟨v', hv'q, heq⟩ := exists_eqOn_ray hγ' hgeo'
    have hvv : v' = v := by
      apply injective_expToN_of_simplyConnected (isCoveringMap_expToN_of_nonpos hc hK p) hsc
      apply Subtype.ext
      rw [coe_expToN_of_mem (hc p _ v'.2), coe_expToN_of_mem (hc p _ v.2), hv'q, hvq]
    rw [hvv] at heq
    exact heq
  · obtain ⟨p⟩ : Nonempty N := inferInstance
    have hdim : finrank ℝ (EuclideanSpace ℝ (Fin (finrank ℝ Z))) =
        finrank ℝ (tangentSubspace hN p) := by
      rw [finrank_euclideanSpace_fin, ← tanAt_of_mem hN p.2, finrank_tanAt hN p.2]
    let e := ContinuousLinearEquiv.ofFinrankEq hdim
    let D₁ : Diffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ Z)))
        𝓘(ℝ, tangentSubspace hN p) (EuclideanSpace ℝ (Fin (finrank ℝ Z)))
        (tangentSubspace hN p) ∞ :=
      { toEquiv := e.toEquiv
        contMDiff_toFun := e.contDiff.contMDiff
        contMDiff_invFun := e.symm.contDiff.contMDiff }
    exact ⟨D₁.trans (expDiffeomorph hc hK hsc p)⟩

/-! ### Corollary 19.3: the higher homotopy groups vanish -/

/-- The cube `Iⁿ` is contractible (the straight-line contraction to the corner `0`). -/
theorem contractibleSpace_cube (n : ℕ) : ContractibleSpace (Fin n → I) := by
  rw [contractible_iff_id_nullhomotopic]
  refine ⟨fun _ => 0, ⟨?_⟩⟩
  exact
    { toFun := fun x i => σ x.1 * x.2 i
      continuous_toFun := by fun_prop
      map_zero_left := fun y => by funext i; simp
      map_one_left := fun y => by funext i; simp }

/-- The faces `{y | y i = a}` of the cube are preconnected. -/
theorem isPreconnected_cube_face {n : ℕ} (i : Fin n) (a : I) :
    IsPreconnected {y : Fin n → I | y i = a} := by
  have e : {y : Fin n → I | y i = a} = Set.pi univ (fun k => if k = i then {a} else univ) := by
    ext y
    constructor
    · intro h k _
      by_cases hk : k = i
      · subst hk
        simpa using h
      · simp [hk]
    · intro h
      simpa using h i (mem_univ i)
  rw [e]
  exact isPreconnected_univ_pi fun k => by
    split_ifs
    exacts [isPreconnected_singleton, isPreconnected_univ]

/-- **The generalized loops of dimension `n ≥ 2` in a complete `N` of curvature `≤ 0` are
null-homotopic** (relative to the boundary of the cube): lift the loop through the covering
`exp_x : T_xN → N` from `0`; the lift is `0` on the boundary of the cube (the boundary is
connected for `n ≥ 2` and lies over `x`, whose fibre is discrete), so the straight-line contraction
of the lift to `0` projects to a homotopy relative to the boundary. -/
theorem genLoop_homotopic_const (hc : IsGeodesicallyComplete hN) (hK : NonposCurvature hN)
    {n : ℕ} (hn : 2 ≤ n) (x : N) (γ : GenLoop (Fin n) N x) :
    GenLoop.Homotopic γ GenLoop.const := by
  have cov := isCoveringMap_expToN_of_nonpos hc hK x
  set f := expToN hN x with hf_def
  have hf0 : f 0 = x := Subtype.ext ((coe_expToN_of_mem (hc x _ (0 : tangentSubspace hN x).2)).trans
    (by simp [exp_zero x.2]))
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  have : ContractibleSpace (Fin n → I) := contractibleSpace_cube n
  have : LocallyPathConnectedSpace I := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  have hbd0 : (0 : Fin n → I) ∈ Cube.boundary (Fin n) := by
    obtain ⟨i⟩ : Nonempty (Fin n) := inferInstance
    exact ⟨i, Or.inl rfl⟩
  have h0 : f 0 = γ.1 0 := by rw [hf0]; exact (γ.2 0 hbd0).symm
  obtain ⟨F, ⟨hF0, hFl⟩, -⟩ := cov.existsUnique_continuousMap_lifts γ.1 0 0 h0
  -- `F` vanishes on the boundary of the cube
  have hFγ : ∀ y, f (F y) = γ.1 y := fun y => congrFun hFl y
  have hface : ∀ (i : Fin n) (a : I), (a = 0 ∨ a = 1) → ∀ y z : Fin n → I, y i = a → z i = a →
      F y = F z := by
    intro i a ha y z hy hz
    refine cov.constOn_of_comp (isPreconnected_cube_face i a) F.continuous.continuousOn
      (fun y hy z hz => ?_) hy hz
    rw [hFγ, hFγ, γ.2 y ⟨i, hy ▸ ha⟩, γ.2 z ⟨i, hz ▸ ha⟩]
  have hFb : ∀ y ∈ Cube.boundary (Fin n), F y = 0 := by
    rintro y ⟨i, hi⟩
    obtain ⟨j, hj⟩ := exists_ne i
    set z : Fin n → I := Function.update (fun _ => 0) i (y i) with hz_def
    have h1 : F y = F z := hface i (y i) hi y z rfl (by simp [hz_def])
    have h2 : F z = F 0 := hface j 0 (Or.inl rfl) z 0 (by simp [hz_def, hj]) rfl
    rw [h1, h2, hF0]
  -- the straight-line homotopy to `0`, projected by `exp_x`
  refine ⟨{ toFun := fun st => f ((σ st.1 : ℝ) • F st.2)
            continuous_toFun := cov.continuous.comp (by fun_prop)
            map_zero_left := fun y => by simp [hFγ]
            map_one_left := fun y => by simp [hf0]
            prop' := fun t y hy => by simp [hFb y hy, hf0, γ.2 y hy] }⟩

/-- **Corollary 19.3, first part** (Milnor p. 103): if `N` is complete with all sectional
curvatures `≤ 0`, then `πᵢ(N) = 0` for `i > 1` (at every base point). -/
theorem corollary_19_3 (hc : IsGeodesicallyComplete hN) (hK : NonposCurvature hN) {i : ℕ}
    (hi : 1 < i) (x : N) : Subsingleton (HomotopyGroup.Pi i N x) := by
  refine ⟨fun a b => ?_⟩
  induction a using Quotient.inductionOn with | h γ₁ => ?_
  induction b using Quotient.inductionOn with | h γ₂ => ?_
  exact Quotient.sound ((genLoop_homotopic_const hc hK hi x γ₁).trans
    (genLoop_homotopic_const hc hK hi x γ₂).symm)

/-! ### The path space -/

/-- **The path space in non-positive curvature** (the first step of Milnor's proof of 19.2,
p. 102): if `N` is closed in `V` (complete) with all sectional curvatures `≤ 0`, then for all
`p, q ∈ N` every geodesic from `p` to `q` has index `0` and is non-degenerate, so by Theorem 17.3
`Ω(N; p, q)` has the homotopy type of a countable cell complex all of whose cells are `0`-cells,
one for each geodesic from `p` to `q`. -/
theorem omega_cells_of_nonpos (hcl : IsClosed N) (hK : NonposCurvature hN) {p q : V}
    (hp : p ∈ N) (hq : q ∈ N) :
    ∃ geo : ℕ → List (ℝ → V),
      (∀ n, ∀ γ ∈ geo n, γ ∈ pathSpace N p q ∧ IsUnbrokenGeodesic hN γ) ∧
      (∀ γ ∈ pathSpace N p q, IsUnbrokenGeodesic hN γ → ∃ n, ∃ γ' ∈ geo n, EqOn γ' γ (Icc 0 1)) ∧
      (∀ n n', ∀ γ ∈ geo n, ∀ γ' ∈ geo n', EqOn γ γ' (Icc 0 1) → n = n') ∧
      (∀ n, (geo n).Pairwise fun γ γ' => ¬ EqOn γ γ' (Icc 0 1)) ∧
      IsCountableCellComplexType (PathSp N p q) fun n => (geo n).map fun _ => 0 := by
  obtain ⟨geo, hgeo, hall, hex, hpw, -, -, hcell⟩ := theorem_17_3 hcl hp hq
    fun γ hγ hg => (formIndex_eq_zero_of_nonpos hK hγ hg).2
  refine ⟨geo, hgeo, hall, hex, hpw, ?_⟩
  have e : (fun n => (geo n).map (geodesicIndex hN p q)) = fun n => (geo n).map fun _ => 0 := by
    funext n
    refine List.map_congr_left fun γ hγ => ?_
    have h := geodesicIndex_eq (hgeo n γ hγ).1 (hgeo n γ hγ).2
    rw [(formIndex_eq_zero_of_nonpos hK (hgeo n γ hγ).1 (hgeo n γ hγ).2).1] at h
    exact_mod_cast h
  rwa [← e]

/-- **`Ω*` has the homotopy type of the fibre of `exp_p` over `q`** (a discrete set), for `N`
complete with curvature `≤ 0`: a path from `p` to `q` is sent to the end point of its lift from
`0`; a point `v` of the fibre to the geodesic `t ↦ exp_p(tv)`; and a path is homotopic to the
geodesic of the end point of its lift by projecting the straight-line homotopy between the lift
and the segment from `0` to `v`. -/
theorem nonempty_homotopyEquiv_pathC_fiber (hc : IsGeodesicallyComplete hN)
    (hK : NonposCurvature hN) (p q : N) :
    Nonempty (ContinuousMap.HomotopyEquiv (PathC N p q) (expToN hN p ⁻¹' {q})) := by
  have cov := isCoveringMap_expToN_of_nonpos hc hK p
  set f := expToN hN p with hf_def
  have hfexp : ∀ y, (f y : V) = exp hN p y := fun y => coe_expToN_of_mem (hc p _ y.2)
  have hf0 : f 0 = p := Subtype.ext ((hfexp 0).trans (by simp [exp_zero p.2]))
  have hdisc : DiscreteTopology (f ⁻¹' {q}) := (cov q).discreteTopology_fiber
  -- the paths as maps into `N`, and their lifts from `0`
  let H : C(I × PathC N p q, N) :=
    ⟨fun x => ⟨(x.2 : C(I, V)) x.1, x.2.2.1 x.1⟩,
      (continuous_eval.comp ((continuous_subtype_val.comp continuous_snd).prodMk
        continuous_fst)).subtype_mk _⟩
  have H0 : ∀ γ, H (0, γ) = f ((ContinuousMap.const (PathC N p q) (0 : tangentSubspace hN p)) γ) :=
    fun γ => by rw [ContinuousMap.const_apply, hf0]; exact Subtype.ext γ.2.2.1
  set L := cov.liftHomotopy H (ContinuousMap.const _ 0) H0 with hL_def
  have hLl : ∀ x, f (L x) = H x := fun x => congrFun (cov.liftHomotopy_lifts H _ H0) x
  have hL0 : ∀ γ, L (0, γ) = 0 := fun γ => cov.liftHomotopy_zero H _ H0 γ
  have hL1 : ∀ γ : PathC N p q, f (L (1, γ)) = q := fun γ => by
    rw [hLl]; exact Subtype.ext γ.2.2.2
  -- the end point of the lift, and the geodesic of a point of the fibre
  let endMap : C(PathC N p q, f ⁻¹' {q}) :=
    ⟨fun γ => ⟨L (1, γ), hL1 γ⟩,
      (L.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩
  let geoMap : C(f ⁻¹' {q}, PathC N p q) :=
    ⟨fun v => ⟨⟨fun t => (f ((t : ℝ) • (v : tangentSubspace hN p)) : V),
      continuous_subtype_val.comp (cov.continuous.comp
        (continuous_subtype_val.smul continuous_const))⟩,
      fun t => (f _).2, by simp [hf0], by simpa using congrArg Subtype.val v.2⟩,
      continuous_of_discreteTopology⟩
  -- `end ∘ geo = id`: the lift of `t ↦ exp_p(tv)` from `0` is the segment `t ↦ tv`
  have hendgeo : endMap.comp geoMap = ContinuousMap.id _ := by
    ext1 v
    apply Subtype.ext
    have h := cov.eq_of_comp_eq (A := I) (g₁ := fun t => L (t, geoMap v))
      (g₂ := fun t => (t : ℝ) • (v : tangentSubspace hN p))
      (L.continuous.comp (continuous_id.prodMk continuous_const))
      (continuous_subtype_val.smul continuous_const)
      (funext fun t => by
        simp only [comp_apply]
        rw [hLl]
        rfl) 0 (by simp [hL0])
    have := congrFun h 1
    change L (1, geoMap v) = (v : tangentSubspace hN p)
    simpa using this
  -- `geo ∘ end ≃ id`: project the straight-line homotopy from the lift to the segment
  let F : (I × PathC N p q) × I → V := fun x =>
    (f ((1 - (x.1.1 : ℝ)) • L (x.2, x.1.2) + (x.1.1 : ℝ) • ((x.2 : ℝ) • L (1, x.1.2))) : V)
  have hF : Continuous F := by
    refine continuous_subtype_val.comp (cov.continuous.comp ?_)
    refine ((continuous_const.sub (continuous_subtype_val.comp (continuous_fst.comp
      continuous_fst))).smul (L.continuous.comp (continuous_snd.prodMk
        (continuous_snd.comp continuous_fst)))).add
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).smul
        ((continuous_subtype_val.comp continuous_snd).smul (L.continuous.comp
          (continuous_const.prodMk (continuous_snd.comp continuous_fst)))))
  let Gc : C(I × PathC N p q, C(I, V)) := ContinuousMap.curry ⟨F, hF⟩
  have hGc : ∀ x t, Gc x t = F (x, t) := fun x t => rfl
  have hmem : ∀ x, Gc x ∈ pathCSet N p q := by
    intro x
    refine ⟨fun t => (f _).2, ?_, ?_⟩
    · rw [hGc]
      simp only [F, Set.Icc.coe_zero, zero_smul, smul_zero, add_zero, hL0, hf0]
    · rw [hGc]
      simp only [F, Set.Icc.coe_one, one_smul, ← add_smul, sub_add_cancel, hL1]
  let G : C(I × PathC N p q, PathC N p q) := ⟨fun x => ⟨Gc x, hmem x⟩, Gc.continuous.subtype_mk _⟩
  have hG0 : ∀ γ, G (0, γ) = ContinuousMap.id _ γ := fun γ => by
    apply Subtype.ext
    ext t
    change F ((0, γ), t) = _
    simp only [F, Set.Icc.coe_zero, sub_zero, one_smul, zero_smul, add_zero, hLl]
    rfl
  have hG1 : ∀ γ, G (1, γ) = (geoMap.comp endMap) γ := fun γ => by
    apply Subtype.ext
    ext t
    change F ((1, γ), t) = _
    simp only [F, Set.Icc.coe_one, sub_self, zero_smul, zero_add, one_smul]
    rfl
  let Hom : ContinuousMap.Homotopy (ContinuousMap.id (PathC N p q)) (geoMap.comp endMap) :=
    { toFun := G
      continuous_toFun := G.continuous
      map_zero_left := hG0
      map_one_left := hG1 }
  refine ⟨⟨endMap, geoMap, ⟨Hom.symm⟩, ?_⟩⟩
  rw [hendgeo]

/-- **The geodesics from `p` to `q` are the points of the fibre of `exp_p` over `q`** (complete
`N`): `v ↦ (t ↦ exp_p(tv))` maps the fibre onto the geodesics `γ ∈ Ω(N; p, q)`, and two points of
the fibre giving the same geodesic on `[0, 1]` are equal. -/
theorem geodesic_iff_mem_fiber (hc : IsGeodesicallyComplete hN) (p q : N) :
    (∀ v ∈ expToN hN p ⁻¹' {q}, (fun t : ℝ => exp hN p (t • (v : V))) ∈ pathSpace N p q ∧
      IsUnbrokenGeodesic hN (fun t : ℝ => exp hN p (t • (v : V)))) ∧
    (∀ γ ∈ pathSpace N p q, IsUnbrokenGeodesic hN γ →
      ∃ v ∈ expToN hN p ⁻¹' {q}, EqOn γ (fun t : ℝ => exp hN p (t • (v : V))) (Icc 0 1)) ∧
    (∀ v ∈ expToN hN p ⁻¹' {q}, ∀ v' ∈ expToN hN p ⁻¹' {q},
      EqOn (fun t : ℝ => exp hN p (t • (v : V))) (fun t : ℝ => exp hN p (t • (v' : V)))
        (Icc 0 1) → v = v') := by
  have hfexp : ∀ y, (expToN hN p y : V) = exp hN p y := fun y => coe_expToN_of_mem (hc p _ y.2)
  refine ⟨fun v hv => ?_, fun γ hγ hgeo => ?_, fun v _ v' _ heq => ?_⟩
  · have hvq : exp hN p v = q := by rw [← hfexp]; exact congrArg Subtype.val hv
    obtain ⟨hmem, hgeo⟩ := ray_mem_pathSpace hc v
    rw [hvq] at hmem
    exact ⟨hmem, hgeo⟩
  · obtain ⟨v, hvq, heq⟩ := exists_eqOn_ray hγ hgeo
    exact ⟨v, Subtype.ext ((hfexp v).trans hvq), heq⟩
  · have hu : UniqueDiffWithinAt ℝ (Icc (0 : ℝ) 1) 0 :=
      uniqueDiffOn_Icc zero_lt_one 0 ⟨le_rfl, zero_le_one⟩
    have d1 := (hasDerivAt_exp_smul_zero p v.2).hasDerivWithinAt (s := Icc (0 : ℝ) 1)
    have d2 := ((hasDerivAt_exp_smul_zero p v'.2).hasDerivWithinAt (s := Icc (0 : ℝ) 1)).congr
      (fun t ht => heq ht) (heq ⟨le_rfl, zero_le_one⟩)
    exact Subtype.ext (hu.eq_deriv _ d1 d2)

/-- **The path space has the homotopy type of a countable discrete set** (the first step of
Milnor's proof of 19.2, p. 102, for every complete `N` of curvature `≤ 0`): `Ω(N; p, q)` is
homotopy equivalent to the fibre of `exp_p` over `q`, a countable discrete space whose points
correspond to the geodesics from `p` to `q` (`Morse.geodesic_iff_mem_fiber`). -/
theorem omega_homotopyEquiv_fiber (hc : IsGeodesicallyComplete hN) (hK : NonposCurvature hN)
    (p q : N) :
    DiscreteTopology (expToN hN p ⁻¹' {q}) ∧ Countable (expToN hN p ⁻¹' {q}) ∧
      Nonempty (ContinuousMap.HomotopyEquiv (PathSp N p q) (expToN hN p ⁻¹' {q})) := by
  obtain ⟨e₁⟩ := (theorem_17_1 hN (p : V) (q : V)).nonempty
  obtain ⟨e₂⟩ := nonempty_homotopyEquiv_pathC_fiber hc hK p q
  have hdisc := ((isCoveringMap_expToN_of_nonpos hc hK p) q).discreteTopology_fiber
  exact ⟨hdisc, TopologicalSpace.separableSpace_iff_countable.1 inferInstance, ⟨e₁.trans e₂⟩⟩

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- **`Ω*` is contractible when `N` is homeomorphic to a vector space**: if `D : T ≅ N` is a
homeomorphism from a real normed space with `D(0) = p`, the continuous paths from `p` to `q` are
contracted onto `t ↦ D(t D⁻¹(q))` by `s ↦ D((1 − s) D⁻¹(γ) + s t D⁻¹(q))`. -/
theorem contractibleSpace_pathC {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    (D : T ≃ₜ N) {p q : N} (hp : D 0 = p) : ContractibleSpace (PathC N p q) := by
  set v := D.symm q with hv_def
  -- the contraction, as a map `(I × Ω*) × I → V`
  let F : (I × PathC N p q) × I → V := fun x =>
    (D ((1 - (x.1.1 : ℝ)) • D.symm ⟨(x.1.2 : C(I, V)) x.2, x.1.2.2.1 x.2⟩ +
      (x.1.1 : ℝ) • ((x.2 : ℝ) • v)) : V)
  have hF : Continuous F := by
    refine continuous_subtype_val.comp (D.continuous.comp ?_)
    refine ((continuous_const.sub (continuous_subtype_val.comp (continuous_fst.comp
      continuous_fst))).smul (D.symm.continuous.comp ?_)).add
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).smul
        ((continuous_subtype_val.comp continuous_snd).smul continuous_const))
    refine Continuous.subtype_mk ?_ _
    exact continuous_eval.comp ((continuous_subtype_val.comp (continuous_snd.comp
      continuous_fst)).prodMk continuous_snd)
  let Hc : C(I × PathC N p q, C(I, V)) := ContinuousMap.curry ⟨F, hF⟩
  have hHc : ∀ x t, Hc x t = F (x, t) := fun x t => rfl
  have hDp : D.symm p = 0 := by rw [← hp, D.symm_apply_apply]
  have hDv : D v = q := D.apply_symm_apply q
  have hmem : ∀ x, Hc x ∈ pathCSet N p q := by
    intro x
    have h0 : (⟨(x.2 : C(I, V)) 0, x.2.2.1 0⟩ : N) = p := Subtype.ext x.2.2.2.1
    have h1 : (⟨(x.2 : C(I, V)) 1, x.2.2.1 1⟩ : N) = q := Subtype.ext x.2.2.2.2
    refine ⟨fun t => (D _).2, ?_, ?_⟩
    · rw [hHc]
      simp only [F, Set.Icc.coe_zero, zero_smul, smul_zero, add_zero, h0, hDp, hp]
    · rw [hHc]
      simp only [F, Set.Icc.coe_one, one_smul, h1, ← hv_def, ← add_smul, sub_add_cancel, hDv]
  let H : C(I × PathC N p q, PathC N p q) := ⟨fun x => ⟨Hc x, hmem x⟩, Hc.continuous.subtype_mk _⟩
  let γ₀ : PathC N p q := ⟨⟨fun t => (D ((t : ℝ) • v) : V),
    continuous_subtype_val.comp (D.continuous.comp (continuous_subtype_val.smul continuous_const))⟩,
    fun t => (D _).2, by simp [hp], by simp [hDv]⟩
  have h0 : ∀ γ : PathC N p q, H (0, γ) = γ := fun γ => by
    apply Subtype.ext
    ext t
    change F ((0, γ), t) = _
    simp [F]
  have h1 : ∀ γ : PathC N p q, H (1, γ) = γ₀ := fun γ => by
    apply Subtype.ext
    ext t
    change F ((1, γ), t) = _
    simp [F, γ₀]
  rw [contractible_iff_id_nullhomotopic]
  exact ⟨γ₀, ⟨
    { toFun := H
      continuous_toFun := H.continuous
      map_zero_left := h0
      map_one_left := h1 }⟩⟩

/-- **Theorem 19.2, Milnor's form for the path space** (p. 102): if `N` is simply connected and
complete, with all sectional curvatures `≤ 0`, then `Ω(N; p, q)` is contractible: it has the
homotopy type of a point.  (`Ω* ≅` the paths of `T_pN` through the diffeomorphism `exp_p`, which
contract to a segment; `Ω ≃ Ω*` by Theorem 17.1.) -/
theorem contractibleSpace_pathSp (hc : IsGeodesicallyComplete hN) (hsc : SimplyConnectedSpace N)
    (hK : NonposCurvature hN) (p q : N) : ContractibleSpace (PathSp N p q) := by
  let _ := hN.chartedSpace
  have hD0 : (expDiffeomorph hc hK hsc p).toHomeomorph 0 = p := by
    change expToN hN p 0 = p
    exact Subtype.ext ((coe_expToN_of_mem (hc p _ (0 : tangentSubspace hN p).2)).trans
      (by simp [exp_zero p.2]))
  have := contractibleSpace_pathC (expDiffeomorph hc hK hsc p).toHomeomorph hD0 (q := q)
  obtain ⟨e⟩ := (theorem_17_1 hN (p : V) (q : V)).nonempty
  exact e.contractibleSpace

/-- **The path space of a simply connected `N`** (Milnor p. 102): if moreover `N` is simply
connected, `Ω(N; p, q)` has the homotopy type of a cell complex with exactly one cell, a
`0`-cell (the unique geodesic of Theorem 19.2). -/
theorem omega_single_cell (hcl : IsClosed N) (hsc : SimplyConnectedSpace N)
    (hK : NonposCurvature hN) (p q : N) :
    ∃ n₀ : ℕ, IsCountableCellComplexType (PathSp N p q) fun n => if n = n₀ then [0] else [] := by
  obtain ⟨geo, hgeo, hall, hex, hpw, hcell⟩ := omega_cells_of_nonpos hcl hK p.2 q.2
  obtain ⟨γ₀, hγ₀, hgeo₀, huniq⟩ :=
    (theorem_19_2 (isGeodesicallyComplete_of_isClosed hcl) hsc hK).1 p q
  obtain ⟨n₀, γ₁, hγ₁, -⟩ := hall γ₀ hγ₀ hgeo₀
  -- every entry of every list is the unique geodesic
  have hall' : ∀ n, ∀ γ ∈ geo n, EqOn γ γ₁ (Icc 0 1) := fun n γ hγ t ht => by
    rw [huniq γ (hgeo n γ hγ).1 (hgeo n γ hγ).2 ht,
      ← huniq γ₁ (hgeo n₀ γ₁ hγ₁).1 (hgeo n₀ γ₁ hγ₁).2 ht]
  have hn : ∀ n, n ≠ n₀ → geo n = [] := fun n hn => by
    rcases eq_or_ne (geo n) [] with h | h
    · exact h
    · obtain ⟨γ, hγ⟩ := List.exists_mem_of_ne_nil _ h
      exact absurd (hex n n₀ γ hγ γ₁ hγ₁ (hall' n γ hγ)) hn
  have hn₀ : (geo n₀).map (fun _ => (0 : ℕ)) = [0] := by
    obtain ⟨γ, l, hl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hγ₁)
    have hl' : l = [] := by
      have h := hpw n₀
      rw [hl, List.pairwise_cons] at h
      rcases eq_or_ne l [] with h' | h'
      · exact h'
      · obtain ⟨γ', hγ'⟩ := List.exists_mem_of_ne_nil _ h'
        have h1 := hall' n₀ γ (by rw [hl]; exact List.mem_cons_self)
        have h2 := hall' n₀ γ' (by rw [hl]; exact List.mem_cons_of_mem _ hγ')
        exact absurd (fun t ht => (h1 ht).trans (h2 ht).symm) (h.1 γ' hγ')
    rw [hl, hl']
    rfl
  refine ⟨n₀, ?_⟩
  have e : (fun n => (geo n).map fun _ => (0 : ℕ)) = fun n => if n = n₀ then [0] else [] := by
    funext n
    split_ifs with h
    · rw [h, hn₀]
    · rw [hn n h]
      rfl
  rwa [← e]

/-! ### Homotopy classes of paths -/

omit [FiniteDimensional ℝ V] in
/-- A path `γ ∈ Ω(N; p, q)` as a continuous path in `N` from `p` to `q`. -/
def pathOfMem {p q : N} {γ : ℝ → V} (hγ : γ ∈ pathSpace N p q) : Path p q where
  toFun t := ⟨γ t, hγ.2.1 t t.2⟩
  continuous_toFun := (hγ.1.2.1.comp_continuous continuous_subtype_val fun t => t.2).subtype_mk _
  source' := Subtype.ext hγ.2.2.1
  target' := Subtype.ext hγ.2.2.2

/-- **Each homotopy class of paths from `p` to `q` contains exactly one geodesic** (Milnor
p. 103), for `N` complete with curvature `≤ 0`: every path `c` from `p` to `q` is homotopic
(relative to the end points) to a geodesic, and two geodesics homotopic to `c` agree on
`[0, 1]`.  The geodesics from `p` are the images of the segments from `0` in `T_pN`, which are
the lifts of the geodesics through the covering `exp_p`; homotopic paths have lifts with the same
end point, and paths of `T_pN` with the same end points are homotopic. -/
theorem homotopy_class_unique_geodesic (hc : IsGeodesicallyComplete hN)
    (hK : NonposCurvature hN) {p q : N} (c : Path p q) :
    (∃ γ : ℝ → V, ∃ hγ : γ ∈ pathSpace N p q, IsUnbrokenGeodesic hN γ ∧
      (pathOfMem hγ).Homotopic c) ∧
    ∀ (γ γ' : ℝ → V) (hγ : γ ∈ pathSpace N p q) (hγ' : γ' ∈ pathSpace N p q),
      IsUnbrokenGeodesic hN γ → IsUnbrokenGeodesic hN γ' → (pathOfMem hγ).Homotopic c →
      (pathOfMem hγ').Homotopic c → EqOn γ γ' (Icc 0 1) := by
  have cov := isCoveringMap_expToN_of_nonpos hc hK p
  set f := expToN hN p with hf_def
  set F : C(tangentSubspace hN p, N) := ⟨f, cov.continuous⟩ with hF_def
  have hf0 : f 0 = p := Subtype.ext ((coe_expToN_of_mem (hc p _ (0 : tangentSubspace hN p).2)).trans
    (by simp [exp_zero p.2]))
  -- the segments from `0`, and the rays they project to
  let seg : tangentSubspace hN p → C(I, tangentSubspace hN p) := fun v =>
    ⟨fun t => (t : ℝ) • v, by fun_prop⟩
  have hseg0 : ∀ v, seg v 0 = 0 := fun v => by simp [seg]
  have hseg1 : ∀ v, seg v 1 = v := fun v => by simp [seg]
  have hray : ∀ {γ : ℝ → V} (hγ : γ ∈ pathSpace N p q) (v : tangentSubspace hN p),
      EqOn γ (fun t : ℝ => exp hN p (t • (v : V))) (Icc 0 1) →
      (pathOfMem hγ : C(I, N)) = F.comp (seg v) := by
    intro γ hγ v heq
    ext t
    change γ t = (f ((t : ℝ) • v) : V)
    rw [heq t.2, coe_expToN_of_mem (hc p _ ((t : ℝ) • v).2)]
    rfl
  have hlift : ∀ {γ : ℝ → V} (hγ : γ ∈ pathSpace N p q) (v : tangentSubspace hN p)
      (heq : EqOn γ (fun t : ℝ => exp hN p (t • (v : V))) (Icc 0 1))
      (h0 : (pathOfMem hγ : C(I, N)) 0 = f 0), cov.liftPath (pathOfMem hγ) 0 h0 = seg v :=
    fun hγ v heq h0 => ((cov.eq_liftPath_iff' h0).2 ⟨by rw [hray hγ v heq]; rfl, hseg0 v⟩).symm
  have hp0 : ∀ {γ : ℝ → V} (hγ : γ ∈ pathSpace N p q), (pathOfMem hγ : C(I, N)) 0 = f 0 :=
    fun hγ => by rw [hf0]; exact (pathOfMem hγ).source
  refine ⟨?_, fun γ γ' hγ hγ' hgeo hgeo' hc₁ hc₂ => ?_⟩
  · -- existence: lift `c`, and compare with the segment to the end point of the lift
    have h0 : (c : C(I, N)) 0 = f 0 := by rw [hf0]; exact c.source
    set Γ := cov.liftPath c 0 h0 with hΓ_def
    set v := Γ 1 with hv_def
    have hfv : f v = q := by
      have := congrFun (cov.liftPath_lifts c 0 h0) 1
      simpa using this
    have hvq : exp hN p v = q := by
      rw [← coe_expToN_of_mem (hc p _ v.2)]
      exact congrArg Subtype.val hfv
    obtain ⟨hmem, hgeo⟩ := ray_mem_pathSpace hc v
    rw [hvq] at hmem
    refine ⟨_, hmem, hgeo, ?_⟩
    -- the segment and `Γ` are homotopic in `T_pN`
    have : ContractibleSpace (tangentSubspace hN p) := inferInstance
    let Γp : Path (0 : tangentSubspace hN p) v := ⟨Γ, cov.liftPath_zero c 0 h0, rfl⟩
    let segp : Path (0 : tangentSubspace hN p) v := ⟨seg v, hseg0 v, hseg1 v⟩
    have hh : (segp : C(I, tangentSubspace hN p)).HomotopicRel Γp {0, 1} :=
      SimplyConnectedSpace.paths_homotopic segp Γp
    have hagree : ∃ a ∈ ({0, 1} : Set I),
        (segp : C(I, tangentSubspace hN p)) a = (Γp : C(I, tangentSubspace hN p)) a :=
      ⟨0, Or.inl rfl, segp.source.trans Γp.source.symm⟩
    have hh' := (cov.homotopicRel_iff_comp hagree).1 hh
    have e1 : (pathOfMem hmem : C(I, N)) = F.comp (seg v) := hray hmem v fun t _ => rfl
    have e2 : F.comp Γ = c := by
      ext t
      exact congrArg Subtype.val (congrFun (cov.liftPath_lifts c 0 h0) t)
    change (pathOfMem hmem : C(I, N)).HomotopicRel c {0, 1}
    rw [e1, ← e2]
    exact hh'
  · -- uniqueness: the lifts of homotopic paths from `0` have the same end point
    obtain ⟨v, hv, heq⟩ := exists_eqOn_ray hγ hgeo
    obtain ⟨v', hv', heq'⟩ := exists_eqOn_ray hγ' hgeo'
    have hh : (pathOfMem hγ : C(I, N)).HomotopicRel (pathOfMem hγ') {0, 1} :=
      Path.Homotopic.trans hc₁ (Path.Homotopic.symm hc₂)
    have h1 := cov.liftPath_apply_one_eq_of_homotopicRel hh 0 (hp0 hγ) (hp0 hγ')
    rw [hlift hγ v heq, hlift hγ' v' heq', hseg1, hseg1] at h1
    intro t ht
    rw [heq ht, heq' ht, h1]

end Morse
