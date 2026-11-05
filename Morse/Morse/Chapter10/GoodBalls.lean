import Morse.Chapter10.RetractionCont
import Morse.Chapter11.ExpSmooth

/-!
Milnor, *Morse Theory*, §17, p. 93 (the proof of Theorem 17.1), for a submanifold `N ⊆ ℝᴷ` with the
induced metric: the *good balls* of Lemma 17.B of the exposition (Exposition/Chapter10.md, §5, "A
proof that works"), the first ingredient of the repaired proof of Theorem 17.1.

# Good balls

## Milnor's text, paraphrased

(p. 93) To prove Theorem 17.1 (the inclusion `Ω ↪ Ω*` of the piecewise smooth paths into the
continuous paths is a homotopy equivalence), Milnor fixes a proper function `f : M → [0, ∞)` and
lets `ε₁(r)` be the supremum of the numbers `e` such that any two points of the compact set
`f⁻¹[0, r]` at distance less than `e` are joined by a unique minimal geodesic, which depends
smoothly on the two points; Corollary 10.8 makes `ε₁(r)` positive.  A continuous path is then
replaced by the broken geodesic through finitely many of its points, consecutive ones being joined
by these minimal geodesics.

## In the embedded setting

* `Morse.IsMinJoin hN y z v`, `Morse.minJoin hN y z`: **the minimal join vector**, the unique
  `v ∈ T_yN` with `exp_y v = z` and `ρ(y, z) = ‖v‖` for which the conclusion of Corollary 10.8
  holds at some scale `δ > ‖v‖` (`Morse.IsShortJoin`); `0` if there is none.  It is one global
  function, so it does not depend on the ball in which it is found (`Morse.minJoin_unique`).
  `Morse.minGeo hN y z s = exp_y(s minJoin(y, z))`: **the minimal geodesic**;
  `Morse.minJoin_self`, `Morse.minGeo_self`, `Morse.minGeo_zero`, `Morse.hasDerivAt_minGeo_zero`.
* `Morse.IsGoodBall hN O`: **a good ball** (Lemma 17.B): an open `O ⊆ V` such that, for one
  `δ > 0`, any two points of `N ∩ O` are at distance `< δ` and joined as in Corollary 10.8 at the
  scale `δ` (`shortJoin`), and the minimal geodesic between them stays in `N ∩ O` (`convex`).
  For a good ball `O` and `y, z ∈ N ∩ O`:
  - `Morse.IsGoodBall.join`: `minJoin y z ∈ T_yN`, `exp_y(minJoin y z) = z`,
    `ρ(y, z) = ‖minJoin y z‖`, and Corollary 10.8 holds at a scale `> ‖minJoin y z‖`;
    `Morse.IsGoodBall.eq_minJoin`: **the minimal geodesic is unique**;
    `Morse.IsGoodBall.exists_uniq`: uniqueness among the tangent vectors of norm `< δ`, `δ`
    uniform on `O`;
  - `Morse.minGeo_zero`, `Morse.IsGoodBall.minGeo_one`, `Morse.IsGoodBall.isGeodesicOn_minGeo`:
    `minGeo y z` is a geodesic from `y` to `z` on an open interval containing `[0, 1]`, of constant
    speed `‖minJoin y z‖ = ρ(y, z)` (`Morse.IsGoodBall.norm_minJoin`);
  - `Morse.IsGoodBall.convex`: **convexity**, `minGeo y z s ∈ N ∩ O` for `0 ≤ s ≤ 1`;
  - `Morse.IsGoodBall.minJoin_minGeo`, `Morse.IsGoodBall.minGeo_minGeo`,
    `Morse.IsGoodBall.riemDist_minGeo`: **sub-arcs** `[0, s]` of minimal geodesics are the minimal
    geodesics, and `ρ(y, minGeo y z s) = s ρ(y, z)`;
  - `Morse.IsGoodBall.continuousOn`, `Morse.IsGoodBall.continuousOn_minGeo`: `minJoin` is
    continuous on `(N ∩ O)²` and `(y, z, s) ↦ minGeo y z s` on `(N ∩ O)² × [0, 1]`;
    `Morse.IsGoodBall.exists_smooth_minGeo`: **smooth dependence**: near each pair of `(N ∩ O)²`,
    `((y, z), s) ↦ minGeo y z s` is the restriction of a map smooth on `U × (−ε, 1 + ε)`, `U` open
    in `V × V`.
* `Morse.exists_isGoodBall_ball`, `Morse.exists_isGoodBall`: **every `x ∈ N` is the centre of good
  balls**: the ambient balls `B(x, r)` are good for all small `r`.
* `Morse.exists_lebesgue_goodBall`: **a Lebesgue number**: for compact `K ⊆ N` there is `ε > 0`
  such that every ambient ball `B(x, ε)`, `x ∈ K`, lies in a good ball.
* The tools: `Morse.exists_secondFundForm_bound` (`R ‖II_y(v, v)‖ ≤ ‖v‖²` near a point),
  `Morse.convexOn_norm_sub_sq` (convexity of `‖γ − x‖²` along geodesics near `x`),
  `Morse.dist_lt_of_isGeodesicOn` (short geodesics between points of a small ball stay in it).

## What Milnor leaves implicit

* **A uniform scale.**  "Joined by a unique minimal geodesic depending smoothly on them" is used for
  all the pairs of a region at once.  Corollary 10.8 gives it at one scale `δ` for all pairs at
  distance `< δ`; the minimal join vector is then the short join vector of Corollary 10.8, and its
  smooth dependence carries over (`Morse.IsGoodBall.eventually_minJoin_eq`).  This is built into
  the definition of a good ball (`shortJoin`).  Smoothness in `(y, z, s)` also needs the smooth
  dependence of geodesics on their initial data over `[0, 1]` (`Morse/Chapter11/ExpSmooth.lean`).
* **The minimal geodesics must stay in the region.**  The repaired proof keeps each piece of a path,
  and the minimal geodesics replacing it, inside one good ball; Milnor's construction does not
  provide this.  Lemma 17.B uses *convex* balls (J. H. C. Whitehead's theorem, proved with normal
  coordinates, the distance from the centre and the Gauss lemma).  Here convexity is proved with the
  **ambient** distance instead: along a geodesic `γ` of `N`, `γ'' = II(γ', γ')`
  (`Morse.IsGeodesicOn.deriv_deriv_eq`), so
  `(‖γ − x‖²)'' = 2‖γ'‖² + 2⟨γ − x, II(γ', γ')⟩ ≥ 2‖γ'‖² (1 − C ‖γ − x‖)`, where
  `‖II_y(v, v)‖ ≤ C ‖v‖²` near `x` (`II` is the derivative of the smooth map `y ↦ P_y`).  So
  `‖γ − x‖²` is convex while `γ` stays within `1/C` of `x`; a geodesic of length `ρ(y, z)` from
  `y ∈ B(x, r)` stays within `r + ρ(y, z)` of `x`; for `y, z ∈ B(x, r)`, `r` small, the convex
  function `‖γ − x‖²` is `< r²` at both ends, hence on `[0, 1]`.  So the ambient balls are convex
  for the minimal geodesics of `N`; no normal coordinates are needed.
* **Sub-arcs of minimal geodesics are minimal geodesics** (needed for the deformation to fix broken
  geodesics): with a uniform scale this is the uniqueness in Corollary 10.8.
* **Lebesgue numbers**: "a set of small diameter lies in a good ball" is the Lebesgue number lemma
  for the cover of a compact set by good balls (here: ambient balls of radius `ε`).
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace ENNReal

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

/-! ### The canonical minimal join vector -/

/-- **`v` is the minimal join vector from `y` to `z`**: `y, z ∈ N`, `v ∈ T_yN`, `exp_y v = z`, the
geodesic `t ↦ exp_y(tv)` is minimal (`ρ(y, z) = ‖v‖`), and the conclusion of Corollary 10.8 holds
for `y, z` at some scale `δ > ‖v‖` (`Morse.IsShortJoin`), so that `v` is the only tangent vector of
norm `< δ` with `exp_y v = z`. -/
def IsMinJoin (y z v : V) : Prop :=
  ∃ (hy : y ∈ N) (hz : z ∈ N), v ∈ tangentSubspace hN ⟨y, hy⟩ ∧ exp hN y v = z ∧
    riemDist (N := N) y z = ENNReal.ofReal ‖v‖ ∧ ∃ δ, ‖v‖ < δ ∧ IsShortJoin hN δ ⟨y, hy⟩ ⟨z, hz⟩

open Classical in
/-- **The canonical minimal join vector** from `y` to `z`: the unique `v` with
`Morse.IsMinJoin hN y z v` (the initial velocity of the minimal geodesic `t ↦ exp_y(tv)` from `y`
to `z`), and `0` if there is none. -/
def minJoin (y z : V) : V := if h : ∃ v, IsMinJoin hN y z v then h.choose else 0

/-- **The canonical minimal geodesic** from `y` to `z`, `s ↦ exp_y(s v(y, z))`, `v = minJoin`;
on `[0, 1]` it runs from `y` to `z` when `y, z` lie in a good ball. -/
def minGeo (y z : V) (s : ℝ) : V := exp hN y (s • minJoin hN y z)

variable {hN}

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- The minimal join vector is unique. -/
theorem IsMinJoin.eq {y z v v' : V} (h : IsMinJoin hN y z v) (h' : IsMinJoin hN y z v') :
    v = v' := by
  obtain ⟨hy, hz, hv, hexp, hρ, δ, hvδ, hJ⟩ := h
  obtain ⟨hy', hz', hv', hexp', hρ', -, -, -⟩ := h'
  obtain ⟨u, -, -, -, -, huniq, -⟩ := hJ
  have hnorm : ‖v'‖ = ‖v‖ := by
    rw [hρ] at hρ'
    exact ((ENNReal.ofReal_eq_ofReal_iff (norm_nonneg _) (norm_nonneg _)).1 hρ').symm
  have e1 : v = u := huniq v hv hvδ hexp
  have e2 : v' = u := huniq v' hv' (hnorm ▸ hvδ) hexp'
  rw [e1, e2]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **`minJoin` is the minimal join vector** whenever there is one (so it does not depend on the
good ball used to find it). -/
theorem minJoin_unique {y z v : V} (h : IsMinJoin hN y z v) : minJoin hN y z = v := by
  have hex : ∃ v, IsMinJoin hN y z v := ⟨v, h⟩
  rw [minJoin, dif_pos hex]
  exact hex.choose_spec.eq h

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem isMinJoin_minJoin {y z v : V} (h : IsMinJoin hN y z v) :
    IsMinJoin hN y z (minJoin hN y z) := by
  rw [minJoin_unique h]; exact h

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- The join vector from `y ∈ N` is always tangent at `y` (it is `0` when there is no minimal
join vector). -/
theorem minJoin_mem_tangentSubspace {y : V} (hy : y ∈ N) (z : V) :
    minJoin hN y z ∈ tangentSubspace hN ⟨y, hy⟩ := by
  by_cases hex : ∃ v, IsMinJoin hN y z v
  · obtain ⟨v, hv⟩ := hex
    rw [minJoin_unique hv]
    obtain ⟨hy', -, hvT, -⟩ := hv
    exact hvT
  · rw [minJoin, dif_neg hex]
    exact Submodule.zero_mem _

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- The vector of Corollary 10.8 (`Morse.IsShortJoin`) is the minimal join vector, and it is the
only tangent vector of norm `< δ` with `exp_y v = z`. -/
theorem isMinJoin_of_isShortJoin {y z : V} (hy : y ∈ N) (hz : z ∈ N) {δ : ℝ}
    (h : IsShortJoin hN δ ⟨y, hy⟩ ⟨z, hz⟩) : ∃ v, IsMinJoin hN y z v ∧
      ‖v‖ < δ ∧ ∀ w ∈ tangentSubspace hN ⟨y, hy⟩, ‖w‖ < δ → exp hN y w = z → w = v := by
  obtain ⟨v, hv, hvδ, hexp, hρ, huniq, -⟩ := id h
  exact ⟨v, ⟨hy, hz, hv, hexp, hρ, δ, hvδ, h⟩, hvδ, huniq⟩

variable (hN) in
/-- **`minJoin y y = 0`**. -/
theorem minJoin_self {y : V} (hy : y ∈ N) : minJoin hN y y = 0 := by
  obtain ⟨s, hs, Ω, -, hyΩ, -, hjoin⟩ := exists_isShortJoin hN ⟨y, hy⟩
  have hJ := hjoin s hs le_rfl ⟨y, hy⟩ ⟨y, hy⟩ hyΩ (by
    rw [riemDist_self hy]; exact ENNReal.ofReal_pos.2 hs)
  refine minJoin_unique ⟨hy, hy, Submodule.zero_mem _, exp_zero hy, ?_, s, ?_, hJ⟩
  · rw [riemDist_self hy, norm_zero, ENNReal.ofReal_zero]
  · rw [norm_zero]; exact hs

variable (hN) in
theorem minGeo_zero {y : V} (hy : y ∈ N) (z : V) : minGeo hN y z 0 = y := by
  simp only [minGeo, zero_smul, exp_zero hy]

variable (hN) in
/-- The minimal geodesic from `y` to itself is constant. -/
theorem minGeo_self {y : V} (hy : y ∈ N) (s : ℝ) : minGeo hN y y s = y := by
  simp only [minGeo, minJoin_self hN hy, smul_zero, exp_zero hy]

variable (hN) in
/-- The minimal geodesic has velocity `minJoin y z` at `0`. -/
theorem hasDerivAt_minGeo_zero {y : V} (hy : y ∈ N) (z : V) :
    HasDerivAt (minGeo hN y z) (minJoin hN y z) 0 :=
  hasDerivAt_exp_smul_zero ⟨y, hy⟩ (minJoin_mem_tangentSubspace hy z)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- The minimal join vector lies in the domain of `exp`. -/
theorem IsMinJoin.mem_expDom {y z v : V} (h : IsMinJoin hN y z v) : (y, v) ∈ expDom hN := by
  obtain ⟨hy, hz, hv, hexp, hρ, -⟩ := h
  by_contra hdom
  have h1 : exp hN y v = y := by
    rw [exp, dif_neg]
    exact hdom
  rw [h1] at hexp
  have h0 : ‖v‖ = 0 := by
    have := hρ.symm
    rw [← hexp, riemDist_self hy, ENNReal.ofReal_eq_zero] at this
    exact le_antisymm this (norm_nonneg _)
  rw [norm_eq_zero.1 h0] at hdom
  exact hdom (zero_mem_expDom hy)

/-- **The minimal geodesic is a geodesic**, on an open interval containing `[0, 1]`, of constant
speed `‖minJoin y z‖`. -/
theorem IsMinJoin.isGeodesicOn_minGeo {y z : V} (h : IsMinJoin hN y z (minJoin hN y z)) :
    ∃ ε > 0, IsGeodesicOn hN (minGeo hN y z) (Ioo (-ε) (1 + ε)) ∧
      ∀ s ∈ Ioo (-ε) (1 + ε), ‖deriv (minGeo hN y z) s‖ = ‖minJoin hN y z‖ := by
  obtain ⟨γ, hγ⟩ := h.mem_expDom
  obtain ⟨ε, hε, hgeo, -⟩ := hγ.isGeodesicOn_exp_smul
  have hgeo' : IsGeodesicOn hN (minGeo hN y z) (Ioo (-ε) (1 + ε)) := hgeo
  obtain ⟨hy, -⟩ := h
  have h0 : (0 : ℝ) ∈ Ioo (-ε) (1 + ε) := ⟨by linarith, by linarith⟩
  refine ⟨ε, hε, hgeo', fun s hs => ?_⟩
  rw [hgeo'.norm_deriv_eq isPreconnected_Ioo hs h0, (hasDerivAt_minGeo_zero hN hy z).deriv]

/-! ### Convexity of the ambient distance along geodesics -/

omit [FiniteDimensional ℝ W] in
variable (hN) in
/-- **A bound for the second fundamental form near a point**: there is `R > 0` with
`R ‖II_y(v, v)‖ ≤ ‖v‖²` for `y ∈ N` with `‖y − x‖ < R` and `v ∈ T_yN`.  (Near `x`, `II_y(v, ·)` is
the derivative of the smooth ambient extension `Morse.projRep` of `y ↦ P_y`, which is bounded near
`x`.) -/
theorem exists_secondFundForm_bound (x : N) :
    ∃ R > 0, ∀ y (hy : y ∈ N), dist y x < R → ∀ v ∈ tangentSubspace hN ⟨y, hy⟩,
      R * ‖secondFundForm hN ⟨y, hy⟩ v v‖ ≤ ‖v‖ ^ 2 := by
  set σ := sliceAt hN x
  have hx : (x : V) ∈ σ.φ.source := mem_sliceAt_source hN x
  have hdQ : ContinuousAt (fderiv ℝ (projRep σ)) x :=
    ((contDiffAt_projRep σ hx).fderiv_right (m := 0) (by simp)).continuousAt
  set C := ‖fderiv ℝ (projRep σ) x‖ + 1 with hC_def
  have hC : 0 < C := by positivity
  have hev : ∀ᶠ y in 𝓝 (x : V), y ∈ σ.φ.source ∧ ‖fderiv ℝ (projRep σ) y‖ < C :=
    (eventually_of_mem (σ.φ.open_source.mem_nhds hx) fun y hy => hy).and
      (hdQ.norm.eventually (gt_mem_nhds (by linarith)))
  obtain ⟨R₁, hR₁, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨min R₁ (1 / C), lt_min hR₁ (by positivity), fun y hy hyx v hv => ?_⟩
  obtain ⟨hysrc, hyC⟩ := hball y (lt_of_lt_of_le hyx (min_le_left _ _))
  have hII : secondFundForm hN ⟨y, hy⟩ v v = fderiv ℝ (projRep σ) y v v := by
    rw [secondFundForm, dN_tanProj_eq_fderiv hN σ (q := ⟨y, hy⟩) hysrc hv]
  rw [hII]
  have h1 : ‖fderiv ℝ (projRep σ) y v v‖ ≤ C * ‖v‖ * ‖v‖ :=
    calc ‖fderiv ℝ (projRep σ) y v v‖ ≤ ‖fderiv ℝ (projRep σ) y‖ * ‖v‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ C * ‖v‖ * ‖v‖ := by gcongr
  calc min R₁ (1 / C) * ‖fderiv ℝ (projRep σ) y v v‖ ≤ (1 / C) * (C * ‖v‖ * ‖v‖) := by
        gcongr
        exact min_le_right _ _
    _ = ‖v‖ ^ 2 := by field_simp

/-- **Convexity of the squared ambient distance along geodesics** (the embedded form of
J. H. C. Whitehead's convexity): if `R ‖II_y(v, v)‖ ≤ ‖v‖²` for `y ∈ N` with `‖y − x‖ < R` and
`v ∈ T_yN`, then along a geodesic staying within `R` of `x` for `s ∈ [a, b]`,
`s ↦ ‖γ(s) − x‖²` is convex on `[a, b]`:
`(‖γ − x‖²)'' = 2‖γ'‖² + 2⟨γ − x, II(γ', γ')⟩ ≥ 2‖γ'‖² (1 − ‖γ − x‖/R) ≥ 0`. -/
theorem convexOn_norm_sub_sq {x : V} {R : ℝ}
    (hR : ∀ y (hy : y ∈ N), dist y x < R → ∀ v ∈ tangentSubspace hN ⟨y, hy⟩,
      R * ‖secondFundForm hN ⟨y, hy⟩ v v‖ ≤ ‖v‖ ^ 2)
    {γ : ℝ → V} {I : Set ℝ} (hγ : IsGeodesicOn hN γ I) {a b : ℝ} (hab : Icc a b ⊆ I)
    (hγx : ∀ s ∈ Icc a b, dist (γ s) x < R) :
    ConvexOn ℝ (Icc a b) (fun s => ‖γ s - x‖ ^ 2) := by
  have hint : interior (Icc a b) = Ioo a b := interior_Icc
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc a b)
    (f' := fun s => 2 * ⟪γ s - x, deriv γ s⟫)
    (f'' := fun s => 2 * (⟪γ s - x, deriv (deriv γ) s⟫ + ⟪deriv γ s, deriv γ s⟫)) ?_ ?_ ?_ ?_
  · exact ((hγ.contDiffOn.continuousOn.mono hab).sub continuousOn_const).norm.pow 2
  · intro s hs
    rw [hint] at hs
    have hsI : s ∈ I := hab (Ioo_subset_Icc_self hs)
    exact (((hγ.hasDerivAt hsI).sub_const x).norm_sq).hasDerivWithinAt
  · intro s hs
    rw [hint] at hs
    have hsI : s ∈ I := hab (Ioo_subset_Icc_self hs)
    have := ((hγ.hasDerivAt hsI).sub_const x).inner ℝ (hγ.hasDerivAt_deriv hsI)
    exact (this.const_mul 2).hasDerivWithinAt
  · intro s hs
    rw [hint] at hs
    have hsI : s ∈ I := hab (Ioo_subset_Icc_self hs)
    have hdist := hγx s (Ioo_subset_Icc_self hs)
    have hII := hR (γ s) (hγ.mem s hsI) hdist (deriv γ s) (hγ.deriv_mem hsI)
    rw [← hγ.deriv_deriv_eq hsI] at hII
    have h1 : -(‖γ s - x‖ * ‖deriv (deriv γ) s‖) ≤ ⟪γ s - x, deriv (deriv γ) s⟫ := by
      have := abs_real_inner_le_norm (γ s - x) (deriv (deriv γ) s)
      linarith [neg_abs_le ⟪γ s - x, deriv (deriv γ) s⟫]
    have h2 : ‖γ s - x‖ * ‖deriv (deriv γ) s‖ ≤ R * ‖deriv (deriv γ) s‖ := by
      gcongr
      rw [← dist_eq_norm]
      exact hdist.le
    rw [real_inner_self_eq_norm_sq]
    nlinarith

/-- **A short geodesic between two points of a small ball stays in the ball**: under the bound of
`Morse.convexOn_norm_sub_sq`, a geodesic `γ` on `(−η, 1 + η)` with `γ(0), γ(1)` in the ball
`B(x, r)` and `r + ‖γ'(0)‖ ≤ R` maps `[0, 1]` into `B(x, r)`.  (It stays within `r + ‖γ'(0)‖ ≤ R` of
`x`, where `‖γ − x‖²` is convex, and is `< r²` at both ends.) -/
theorem dist_lt_of_isGeodesicOn {x : V} {R : ℝ}
    (hR : ∀ y (hy : y ∈ N), dist y x < R → ∀ v ∈ tangentSubspace hN ⟨y, hy⟩,
      R * ‖secondFundForm hN ⟨y, hy⟩ v v‖ ≤ ‖v‖ ^ 2)
    {γ : ℝ → V} {η : ℝ} (hη : 0 < η) (hγ : IsGeodesicOn hN γ (Ioo (-η) (1 + η))) {r : ℝ}
    (h0 : dist (γ 0) x < r) (h1 : dist (γ 1) x < r) (hrR : r + ‖deriv γ 0‖ ≤ R) :
    ∀ s ∈ Icc (0 : ℝ) 1, dist (γ s) x < r := by
  have hsub : Icc (0 : ℝ) 1 ⊆ Ioo (-η) (1 + η) := Icc_subset_Ioo (by linarith) (by linarith)
  have hI0 : (0 : ℝ) ∈ Ioo (-η) (1 + η) := hsub ⟨le_rfl, zero_le_one⟩
  -- the chord is at most the length
  have hchord : ∀ s ∈ Icc (0 : ℝ) 1, ‖γ s - γ 0‖ ≤ ‖deriv γ 0‖ * (s - 0) :=
    norm_image_sub_le_of_norm_deriv_le_segment' (f' := deriv γ)
      (fun s hs => (hγ.hasDerivAt (hsub hs)).hasDerivWithinAt)
      (fun s hs => (hγ.norm_deriv_eq isPreconnected_Ioo (hsub (Ico_subset_Icc_self hs)) hI0).le)
  have hR' : ∀ s ∈ Icc (0 : ℝ) 1, dist (γ s) x < R := by
    intro s hs
    have := hchord s hs
    calc dist (γ s) x ≤ dist (γ s) (γ 0) + dist (γ 0) x := dist_triangle _ _ _
      _ < ‖deriv γ 0‖ * (s - 0) + r := by
          rw [dist_eq_norm]
          linarith
      _ ≤ ‖deriv γ 0‖ * 1 + r := by gcongr; linarith [hs.2]
      _ ≤ R := by linarith
  have hconv := convexOn_norm_sub_sq hR hγ hsub hR'
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg h0
  intro s hs
  have hseg : s ∈ segment ℝ (0 : ℝ) 1 := by rwa [segment_eq_Icc zero_le_one]
  have hle := hconv.le_on_segment ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ hseg
  have hlt : max (‖γ 0 - x‖ ^ 2) (‖γ 1 - x‖ ^ 2) < r ^ 2 := by
    rw [← dist_eq_norm, ← dist_eq_norm]
    exact max_lt (pow_lt_pow_left₀ h0 dist_nonneg two_ne_zero)
      (pow_lt_pow_left₀ h1 dist_nonneg two_ne_zero)
  rw [dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 hr.le (lt_of_le_of_lt hle hlt)

/-! ### Good balls -/

variable (hN) in
/-- **A good ball** (Lemma 17.B of the exposition), in the embedded setting: an open set `O ⊆ V`
such that
* (`shortJoin`) for one `δ > 0`, any two points `y, z` of `N ∩ O` are at distance `< δ` and are
  joined as in Corollary 10.8 at the scale `δ` (`Morse.IsShortJoin`): by a unique geodesic of length
  `< δ`, which is minimal and depends smoothly on `(y, z)`;
* (`convex`) the minimal geodesic `Morse.minGeo` from `y` to `z`, `0 ≤ s ≤ 1`, stays in `N ∩ O`. -/
structure IsGoodBall (O : Set V) : Prop where
  isOpen : IsOpen O
  shortJoin : ∃ δ > 0, ∀ y (hy : y ∈ N ∩ O) z (hz : z ∈ N ∩ O),
    riemDist (N := N) y z < ENNReal.ofReal δ ∧ IsShortJoin hN δ ⟨y, hy.1⟩ ⟨z, hz.1⟩
  convex : ∀ y ∈ N ∩ O, ∀ z ∈ N ∩ O, ∀ s ∈ Icc (0 : ℝ) 1, minGeo hN y z s ∈ N ∩ O

namespace IsGoodBall

variable {O : Set V} (hO : IsGoodBall hN O)
include hO

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- In a good ball, `minJoin y z` is the minimal join vector. -/
theorem isMinJoin {y z : V} (hy : y ∈ N ∩ O) (hz : z ∈ N ∩ O) :
    IsMinJoin hN y z (minJoin hN y z) := by
  obtain ⟨δ, -, hshort⟩ := hO.shortJoin
  obtain ⟨v, hv, -⟩ := isMinJoin_of_isShortJoin hy.1 hz.1 (hshort y hy z hz).2
  exact isMinJoin_minJoin hv

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **The minimal join vector in a good ball**: `minJoin y z` is tangent at `y`,
`exp_y(minJoin y z) = z`, `ρ(y, z) = ‖minJoin y z‖`, and Corollary 10.8 holds for `y, z` at a
scale `δ > ‖minJoin y z‖`. -/
theorem join {y z : V} (hy : y ∈ N ∩ O) (hz : z ∈ N ∩ O) :
    minJoin hN y z ∈ tangentSubspace hN ⟨y, hy.1⟩ ∧ exp hN y (minJoin hN y z) = z ∧
      riemDist (N := N) y z = ENNReal.ofReal ‖minJoin hN y z‖ ∧
      ∃ δ, ‖minJoin hN y z‖ < δ ∧ IsShortJoin hN δ ⟨y, hy.1⟩ ⟨z, hz.1⟩ := by
  obtain ⟨_, _, hT, hexp, hρ, δ, hδ, hJ⟩ := hO.isMinJoin hy hz
  exact ⟨hT, hexp, hρ, δ, hδ, hJ⟩

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **Uniqueness at a uniform scale**: there is `δ > 0` such that for `y, z ∈ N ∩ O`,
`‖minJoin y z‖ < δ` and `minJoin y z` is the only tangent vector at `y` of norm `< δ` with
`exp_y v = z`. -/
theorem exists_uniq : ∃ δ > 0, ∀ y (hy : y ∈ N ∩ O), ∀ z ∈ N ∩ O,
    ‖minJoin hN y z‖ < δ ∧ ∀ w ∈ tangentSubspace hN ⟨y, hy.1⟩, ‖w‖ < δ → exp hN y w = z →
      w = minJoin hN y z := by
  obtain ⟨δ, hδ, hshort⟩ := hO.shortJoin
  refine ⟨δ, hδ, fun y hy z hz => ?_⟩
  obtain ⟨v, hv, hvδ, huniq⟩ := isMinJoin_of_isShortJoin hy.1 hz.1 (hshort y hy z hz).2
  rw [minJoin_unique hv]
  exact ⟨hvδ, huniq⟩

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **The minimal geodesic in a good ball is unique**: a tangent vector `v` at `y` with
`exp_y v = z` and `ρ(y, z) = ‖v‖` is `minJoin y z`. -/
theorem eq_minJoin {y z : V} (hy : y ∈ N ∩ O) (hz : z ∈ N ∩ O) {v : V}
    (hv : v ∈ tangentSubspace hN ⟨y, hy.1⟩) (hexp : exp hN y v = z)
    (hρ : riemDist (N := N) y z = ENNReal.ofReal ‖v‖) : v = minJoin hN y z := by
  have h := hO.isMinJoin hy hz
  obtain ⟨_, _, -, -, hρ', δ, hδ, hJ⟩ := id h
  have hnorm : ‖v‖ = ‖minJoin hN y z‖ := by
    rw [hρ] at hρ'
    exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg _) (norm_nonneg _)).1 hρ'
  exact (h.eq ⟨hy.1, hz.1, hv, hexp, hρ, δ, hnorm ▸ hδ, hJ⟩).symm

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- `‖minJoin y z‖ = ρ(y, z)`: the minimal geodesic has length `ρ(y, z)`. -/
theorem norm_minJoin {y z : V} (hy : y ∈ N ∩ O) (hz : z ∈ N ∩ O) :
    ‖minJoin hN y z‖ = (riemDist (N := N) y z).toReal := by
  rw [(hO.join hy hz).2.2.1, ENNReal.toReal_ofReal (norm_nonneg _)]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem minGeo_one {y z : V} (hy : y ∈ N ∩ O) (hz : z ∈ N ∩ O) : minGeo hN y z 1 = z := by
  rw [minGeo, one_smul]
  exact (hO.join hy hz).2.1

/-- **The minimal geodesic is a geodesic** on an open interval containing `[0, 1]`, with constant
speed `‖minJoin y z‖ = ρ(y, z)`. -/
theorem isGeodesicOn_minGeo {y z : V} (hy : y ∈ N ∩ O) (hz : z ∈ N ∩ O) :
    ∃ ε > 0, IsGeodesicOn hN (minGeo hN y z) (Ioo (-ε) (1 + ε)) ∧
      ∀ s ∈ Ioo (-ε) (1 + ε), ‖deriv (minGeo hN y z) s‖ = ‖minJoin hN y z‖ :=
  (hO.isMinJoin hy hz).isGeodesicOn_minGeo

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- On the pairs of a good ball, near any pair, the minimal join vector is the smooth map `G` of
Corollary 10.8 (`Morse.IsShortJoin`) at that pair. -/
theorem eventually_minJoin_eq {y z : V} (hy : y ∈ N ∩ O) (hz : z ∈ N ∩ O) :
    ∃ O₂ : Set (V × V), IsOpen O₂ ∧ (y, z) ∈ O₂ ∧ ∃ G : V × V → V, ContDiffOn ℝ ∞ G O₂ ∧
      ∀ y' ∈ N ∩ O, ∀ z' ∈ N ∩ O, (y', z') ∈ O₂ → G (y', z') = minJoin hN y' z' := by
  obtain ⟨δ, -, hshort⟩ := hO.shortJoin
  obtain ⟨-, -, -, -, -, -, O₂, hO₂, hmem, G, hG, -, hGspec⟩ := (hshort y hy z hz).2
  refine ⟨O₂, hO₂, hmem, G, hG, fun y' hy' z' hz' hw => ?_⟩
  obtain ⟨hρ', hJ'⟩ := hshort y' hy' z' hz'
  obtain ⟨hGT, hGδ, hGexp⟩ := hGspec ⟨y', hy'.1⟩ ⟨z', hz'.1⟩ hw hρ'
  obtain ⟨u, hu, -, huniq⟩ := isMinJoin_of_isShortJoin hy'.1 hz'.1 hJ'
  rw [minJoin_unique hu]
  exact huniq _ hGT hGδ hGexp

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **The minimal join vector depends continuously on its end points** in a good ball. -/
theorem continuousOn :
    ContinuousOn (fun w : V × V => minJoin hN w.1 w.2) ((N ∩ O) ×ˢ (N ∩ O)) := by
  rintro ⟨y, z⟩ ⟨hy, hz⟩
  obtain ⟨O₂, hO₂, hmem, G, hG, hGeq⟩ := hO.eventually_minJoin_eq hy hz
  have hev : (fun w : V × V => minJoin hN w.1 w.2) =ᶠ[𝓝[(N ∩ O) ×ˢ (N ∩ O)] (y, z)] G := by
    filter_upwards [inter_mem_nhdsWithin _ (hO₂.mem_nhds hmem)] with w hw
    exact (hGeq w.1 hw.1.1 w.2 hw.1.2 hw.2).symm
  exact ((hG.continuousOn.continuousAt (hO₂.mem_nhds hmem)).continuousWithinAt
    ).congr_of_eventuallyEq hev (hGeq y hy z hz hmem).symm

/-- **The minimal geodesics depend continuously on their end points**: `(y, z, s) ↦ minGeo y z s`
is continuous on `(N ∩ O) × (N ∩ O) × [0, 1]`. -/
theorem continuousOn_minGeo :
    ContinuousOn (fun w : V × V × ℝ => minGeo hN w.1 w.2.1 w.2.2)
      ((N ∩ O) ×ˢ (N ∩ O) ×ˢ Icc 0 1) := by
  rintro ⟨y, z, s⟩ ⟨hy, hz, hs⟩
  set S := (N ∩ O) ×ˢ (N ∩ O) ×ˢ Icc (0 : ℝ) 1
  have hj : ContinuousWithinAt (fun w : V × V × ℝ => minJoin hN w.1 w.2.1) S (y, z, s) :=
    ContinuousWithinAt.comp (g := fun w : V × V => minJoin hN w.1 w.2)
      (f := fun w : V × V × ℝ => (w.1, w.2.1)) (hO.continuousOn (y, z) ⟨hy, hz⟩)
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).continuousWithinAt
      fun w hw => ⟨hw.1, hw.2.1⟩
  have h1 : ContinuousWithinAt (fun w : V × V × ℝ => (w.1, w.2.2 • minJoin hN w.1 w.2.1)) S
      (y, z, s) :=
    continuousWithinAt_fst.prodMk ((continuous_snd.comp continuous_snd).continuousWithinAt.smul hj)
  have hdom : (y, s • minJoin hN y z) ∈ expDom hN :=
    mem_expDom_smul (hO.isMinJoin hy hz).mem_expDom hs
  exact ContinuousWithinAt.comp (f := fun w : V × V × ℝ => (w.1, w.2.2 • minJoin hN w.1 w.2.1))
    (x := (y, z, s)) (eventually_mem_expDom_and_continuousWithinAt_exp hdom).2 h1
    fun w hw => ⟨hw.1.1, Submodule.smul_mem _ _ (minJoin_mem_tangentSubspace hw.1.1 _)⟩

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **Sub-arcs of minimal geodesics are minimal geodesics**: for `0 ≤ s ≤ 1`, the minimal join
vector from `y` to `minGeo y z s` is `s minJoin y z`. -/
theorem minJoin_minGeo {y z : V} (hy : y ∈ N ∩ O) (hz : z ∈ N ∩ O) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : minJoin hN y (minGeo hN y z s) = s • minJoin hN y z := by
  obtain ⟨δ, -, huniq⟩ := hO.exists_uniq
  have hz' := hO.convex y hy z hz s hs
  obtain ⟨hlt, -⟩ := huniq y hy z hz
  obtain ⟨-, hU⟩ := huniq y hy (minGeo hN y z s) hz'
  refine (hU _ (Submodule.smul_mem _ _ (minJoin_mem_tangentSubspace hy.1 z)) ?_ rfl).symm
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
  calc s * ‖minJoin hN y z‖ ≤ 1 * ‖minJoin hN y z‖ := by gcongr; exact hs.2
    _ < δ := by rwa [one_mul]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **Sub-arcs of minimal geodesics**, as curves: the minimal geodesic from `y` to `minGeo y z s`
is `τ ↦ minGeo y z (τ s)`. -/
theorem minGeo_minGeo {y z : V} (hy : y ∈ N ∩ O) (hz : z ∈ N ∩ O) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (τ : ℝ) : minGeo hN y (minGeo hN y z s) τ = minGeo hN y z (τ * s) := by
  rw [minGeo, hO.minJoin_minGeo hy hz hs, smul_smul]
  rfl

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- The distance along a minimal geodesic: `ρ(y, minGeo y z s) = s ρ(y, z)` for `0 ≤ s ≤ 1`. -/
theorem riemDist_minGeo {y z : V} (hy : y ∈ N ∩ O) (hz : z ∈ N ∩ O) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    riemDist (N := N) y (minGeo hN y z s) = ENNReal.ofReal (s * ‖minJoin hN y z‖) := by
  rw [(hO.join hy (hO.convex y hy z hz s hs)).2.2.1, hO.minJoin_minGeo hy hz hs, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hs.1]

/-- **The minimal geodesics depend smoothly on their end points**, locally: near each pair
`(y₀, z₀)` of points of `N ∩ O` there are an open `U ∋ (y₀, z₀)` in `V × V`, `ε > 0` and a map
`Φ`, smooth on `U × (−ε, 1 + ε)`, with `Φ((y, z), s) = minGeo y z s` for `y, z ∈ N ∩ O`,
`(y, z) ∈ U`.  (`Φ` is the family of radial geodesics with the initial data
`(r(y), P_{r(y)} G(y, z))`, `r` a smooth retraction onto `N` and `G` the smooth map of
Corollary 10.8, smooth by `Morse.raysGoodE_of_isGeodesicOn`.) -/
theorem exists_smooth_minGeo {y₀ z₀ : V} (hy₀ : y₀ ∈ N ∩ O) (hz₀ : z₀ ∈ N ∩ O) :
    ∃ U : Set (V × V), IsOpen U ∧ (y₀, z₀) ∈ U ∧ ∃ ε > 0, ∃ Φ : (V × V) × ℝ → V,
      ContDiffOn ℝ ∞ Φ (U ×ˢ Ioo (-ε) (1 + ε)) ∧
      ∀ y ∈ N ∩ O, ∀ z ∈ N ∩ O, (y, z) ∈ U → ∀ s, Φ ((y, z), s) = minGeo hN y z s := by
  obtain ⟨O₂, hO₂, hmem, G, hG, hGeq⟩ := hO.eventually_minJoin_eq hy₀ hz₀
  obtain ⟨U₁, hU₁, hy₀U₁, r, hr, hrN, hrid⟩ := exists_retraction hN ⟨y₀, hy₀.1⟩
  set U₀ : Set (V × V) := O₂ ∩ U₁ ×ˢ univ with hU₀_def
  have hU₀ : IsOpen U₀ := hO₂.inter (hU₁.prod isOpen_univ)
  have hu₀ : (y₀, z₀) ∈ U₀ := ⟨hmem, hy₀U₁, trivial⟩
  set c : V × V → V := fun u => r u.1 with hc_def
  set w : V × V → V := fun u => prj hN (r u.1) (G u) with hw_def
  have hcs : ContDiffOn ℝ ∞ c U₀ := hr.comp contDiffOn_fst fun u hu => hu.2.1
  have hcN : ∀ u ∈ U₀, c u ∈ N := fun u hu => hrN u.1 hu.2.1
  have hws : ContDiffOn ℝ ∞ w U₀ :=
    (ContDiffOn.prj_comp hN hcs hcN).clm_apply (hG.mono inter_subset_left)
  have hwT : ∀ u ∈ U₀, prj hN (c u) (w u) = w u := fun u _ => prj_prj hN _ _
  -- on the pairs of the good ball, the data are `(y, minJoin y z)`
  have hcw : ∀ y ∈ N ∩ O, ∀ z ∈ N ∩ O, (y, z) ∈ U₀ →
      c (y, z) = y ∧ w (y, z) = minJoin hN y z := by
    intro y hy z hz hu
    have h1 : r y = y := hrid y hu.2.1 hy.1
    refine ⟨h1, ?_⟩
    change prj hN (r y) (G (y, z)) = minJoin hN y z
    rw [h1, hGeq y hy z hz hu.1]
    exact (prj_eq_self_iff hN hy.1).2 (minJoin_mem_tangentSubspace hy.1 z)
  obtain ⟨η₀, hη₀, hgeo₀, -⟩ := hO.isGeodesicOn_minGeo hy₀ hz₀
  obtain ⟨hc₀, hw₀⟩ := hcw y₀ hy₀ z₀ hz₀ hu₀
  have hbase : IsGeodesicOn hN (fun t => exp hN (c (y₀, z₀)) (t • w (y₀, z₀)))
      (Ioo (-η₀) (1 + η₀)) := by
    rw [hc₀, hw₀]
    exact hgeo₀
  obtain ⟨ε, hε, η, hη, hsub, hsm, -⟩ :=
    raysGoodE_of_isGeodesicOn hU₀ hu₀ hcs hws hcN hwT zero_le_one hη₀ hbase
  refine ⟨ball (y₀, z₀) ε, isOpen_ball, mem_ball_self hε, η, hη, raysE hN c w, hsm,
    fun y hy z hz hu s => ?_⟩
  obtain ⟨h1, h2⟩ := hcw y hy z hz (hsub hu)
  change exp hN (c (y, z)) (s • w (y, z)) = minGeo hN y z s
  rw [h1, h2]
  rfl

end IsGoodBall

/-! ### Existence of good balls -/

variable (hN) in
/-- **Lemma 17.B: every point of `N` is the centre of good balls**: the ambient balls `B(x, r)` are
good for all `r ≤ r₀`.  (Choose `R` with `R ‖II(v, v)‖ ≤ ‖v‖²` near `x`
(`Morse.exists_secondFundForm_bound`), and `s`, `Ω` as in Lemma 10.3 read with the distance
(`Morse.exists_isShortJoin`); for `r ≤ R/3` so small that `B(x, r) ⊆ Ω` and
`ρ(x, y) < min(R/3, s/2)` on `N ∩ B(x, r)`, two points of `N ∩ B(x, r)` are at distance `< s`, and
their minimal geodesic, of length `< 2R/3`, stays in `B(x, R)`, where `‖· − x‖²` is convex along
geodesics, so it stays in `B(x, r)` (`Morse.dist_lt_of_isGeodesicOn`).) -/
theorem exists_isGoodBall_ball {x : V} (hx : x ∈ N) :
    ∃ r₀ > 0, ∀ r ≤ r₀, IsGoodBall hN (ball x r) := by
  obtain ⟨R, hR, hRII⟩ := exists_secondFundForm_bound hN ⟨x, hx⟩
  obtain ⟨s, hs, Ω, hΩ, hxΩ, -, hjoin⟩ := exists_isShortJoin hN ⟨x, hx⟩
  set t := min (R / 3) (s / 2) with ht_def
  have ht : 0 < t := lt_min (by linarith) (by linarith)
  have htR : t ≤ R / 3 := min_le_left _ _
  have hts : t ≤ s / 2 := min_le_right _ _
  obtain ⟨r₁, hr₁, hr₁t⟩ := Metric.mem_nhdsWithin_iff.1
    ((hasBasis_nhdsWithin_riemDist hN ⟨x, hx⟩).mem_of_mem ht)
  obtain ⟨r₂, hr₂, hr₂Ω⟩ := Metric.isOpen_iff.1 hΩ x hxΩ
  refine ⟨min (min r₁ r₂) (R / 3), lt_min (lt_min hr₁ hr₂) (by linarith), fun r hr0 => ?_⟩
  have hrr₁ : r ≤ r₁ := hr0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hrr₂ : r ≤ r₂ := hr0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hrR : r ≤ R / 3 := hr0.trans (min_le_right _ _)
  -- points of `N ∩ B(x, r)` are at distance `< t` from `x`
  have hρx : ∀ y ∈ N ∩ ball x r, riemDist (N := N) x y < ENNReal.ofReal t := fun y hy =>
    hr₁t ⟨ball_subset_ball hrr₁ hy.2, hy.1⟩
  have hρ : ∀ y ∈ N ∩ ball x r, ∀ z ∈ N ∩ ball x r,
      riemDist (N := N) y z < ENNReal.ofReal (2 * t) := by
    intro y hy z hz
    calc riemDist (N := N) y z ≤ riemDist (N := N) y x + riemDist (N := N) x z :=
          riemDist_triangle _ _ _
      _ < ENNReal.ofReal t + ENNReal.ofReal t := by
          rw [riemDist_comm]
          exact ENNReal.add_lt_add (hρx y hy) (hρx z hz)
      _ = ENNReal.ofReal (2 * t) := by rw [← ENNReal.ofReal_add ht.le ht.le, two_mul]
  have hshort : ∀ y (hy : y ∈ N ∩ ball x r) z (hz : z ∈ N ∩ ball x r),
      riemDist (N := N) y z < ENNReal.ofReal s ∧ IsShortJoin hN s ⟨y, hy.1⟩ ⟨z, hz.1⟩ := by
    intro y hy z hz
    have h1 : riemDist (N := N) y z < ENNReal.ofReal s :=
      (hρ y hy z hz).trans_le (ENNReal.ofReal_le_ofReal (by linarith))
    exact ⟨h1, hjoin s hs le_rfl ⟨y, hy.1⟩ ⟨z, hz.1⟩ (hr₂Ω (ball_subset_ball hrr₂ hy.2)) h1⟩
  refine ⟨isOpen_ball, ⟨s, hs, hshort⟩, ?_⟩
  -- convexity
  intro y hy z hz τ hτ
  obtain ⟨v, hv, -, -⟩ := isMinJoin_of_isShortJoin hy.1 hz.1 (hshort y hy z hz).2
  have hmj := isMinJoin_minJoin hv
  obtain ⟨η, hη, hgeo, -⟩ := hmj.isGeodesicOn_minGeo
  have hnorm : ‖minJoin hN y z‖ < 2 * t := by
    have h := hρ y hy z hz
    obtain ⟨-, -, -, -, hρ', -⟩ := hmj
    rw [hρ'] at h
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).1 h
  have hd0 : deriv (minGeo hN y z) 0 = minJoin hN y z := (hasDerivAt_minGeo_zero hN hy.1 z).deriv
  have hexp1 : minGeo hN y z 1 = z := by
    obtain ⟨-, -, -, hexp, -⟩ := hmj
    rw [minGeo, one_smul]
    exact hexp
  have key := dist_lt_of_isGeodesicOn hRII hη hgeo (r := r)
    (by rw [minGeo_zero hN hy.1]; exact hy.2) (by rw [hexp1]; exact hz.2)
    (by rw [hd0]; linarith)
  exact ⟨hgeo.mem τ ⟨by linarith [hτ.1], by linarith [hτ.2]⟩, key τ hτ⟩

variable (hN) in
/-- **Lemma 17.B** (Exposition, Chapter 10, §5): every point `x ∈ N` lies in good balls contained
in any given ambient ball `B(x, ε)`. -/
theorem exists_isGoodBall {x : V} (hx : x ∈ N) {ε : ℝ} (hε : 0 < ε) :
    ∃ O, x ∈ O ∧ O ⊆ Metric.ball x ε ∧ IsGoodBall hN O := by
  obtain ⟨r₀, hr₀, h⟩ := exists_isGoodBall_ball hN hx
  exact ⟨ball x (min r₀ ε), mem_ball_self (lt_min hr₀ hε), ball_subset_ball (min_le_right _ _),
    h _ (min_le_left _ _)⟩

variable (hN) in
/-- **A Lebesgue number for good balls**: for a compact `K ⊆ N` there is `ε > 0` such that every
ambient ball `B(x, ε)`, `x ∈ K`, lies in a good ball; so every subset of `K` of (ambient) diameter
`< ε` lies in a good ball. -/
theorem exists_lebesgue_goodBall {K : Set V} (hK : IsCompact K) (hKN : K ⊆ N) :
    ∃ ε > 0, ∀ x ∈ K, ∃ O, IsGoodBall hN O ∧ Metric.ball x ε ⊆ O := by
  choose O hxO _ hO using fun x : K => exists_isGoodBall hN (hKN x.2) one_pos
  obtain ⟨ε, hε, hleb⟩ := lebesgue_number_lemma_of_metric hK (fun x => (hO x).isOpen)
    fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxO _⟩
  refine ⟨ε, hε, fun x hx => ?_⟩
  obtain ⟨i, hi⟩ := hleb x hx
  exact ⟨O i, hO i, hi⟩

end Morse
