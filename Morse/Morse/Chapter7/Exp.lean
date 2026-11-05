import Morse.Chapter7.GeodesicLocal

/-!
Milnor, *Morse Theory*, §10, pp. 57–58, for a submanifold `N ⊆ ℝᴷ` with the induced metric.

# The exponential map

## Milnor's text, paraphrased

* (p. 57) Let `v ∈ TM_q` and suppose that there is a geodesic `γ : [0, 1] → M` with `γ(0) = q`,
  `dγ/dt (0) = v`.  Then `γ(1)` is denoted `exp_q(v)`, the *exponential* of `v`, and the geodesic
  is `γ(t) = exp_q(tv)`.  (A footnote explains the name: for the unitary group, `exp` at the
  identity is the exponential power series.)
* (p. 58) By Lemma 10.2, `exp_q(v)` is defined when `‖v‖` is small enough; in general not for
  large `v`; but "if defined at all, `exp_q(v)` is always uniquely defined".  `M` is *geodesically
  complete* if `exp_q(v)` is defined for all `q ∈ M` and all `v ∈ TM_q`.
* (p. 58) By Lemma 10.2, `(q, v) ↦ exp_q(v)` is defined throughout a neighbourhood of `(p, 0)` in
  the tangent manifold `TM`, and is differentiable there; `exp_q(0) = q`, and `t ↦ exp_q(tv)` has
  velocity `v` at `t = 0` (this is how Milnor computes the Jacobian in the proof of Lemma 10.3).

## In the embedded setting

* `Morse.IsGeodesicFrom hN γ q v`: `γ` is a geodesic on an open interval `(-δ, 1 + δ)` with
  `γ(0) = q` and `γ'(0) = v`.  `Morse.expDom hN ⊆ V × V` is the set of `(q, v)` for which such a
  geodesic exists, and `Morse.exp hN q v = γ(1)` (with the junk value `q` off the domain).
* `Morse.IsGeodesicFrom.exp_eq`: **`exp` is well defined**, by uniqueness of geodesics.
* `Morse.IsGeodesicFrom.exp_smul`: **`γ(t) = exp_q(tv)`** (p. 57), for `t ∈ (-δ, 1 + δ)`.
* `Morse.exists_exp_eq`: Lemma 10.2 in terms of `exp`: near `(q₀, 0)`, on `TN`, `exp` is the
  restriction of a smooth map on an open set of `V × V`.
* `Morse.exists_isOpen_exp`: **`exp` is defined and smooth on an open neighbourhood of the zero
  section of `TN`**, in Milnor's sense of smoothness for maps on subsets of `ℝᴷ` (locally the
  restriction of a smooth map); `Morse.contMDiffOn_exp`: the same for the manifold structure of
  `TN = Milnor.Problems.tangentBundleSet hN`, a slice submanifold of `V × V` modelled on `Z × Z`
  (from the companion project).
* `Morse.hasFDerivAt_exp_zero`: **`d(exp_q)₀ = id`**: `exp_q`, as a map on the vector space
  `T_qN`, has derivative the inclusion `T_qN → V` at `0`.

## What Milnor leaves implicit

* "If defined at all, `exp_q(v)` is always uniquely defined" is the uniqueness of geodesics in the
  large (`Morse.IsGeodesicOn.eqOn`), not the local uniqueness of Theorem 10.1.
* `γ(t) = exp_q(tv)` uses the homogeneity of the geodesic equation together with the uniqueness in
  the large: `s ↦ γ(ts)` is a geodesic with initial velocity `tv` on an interval containing
  `[0, 1]`.
* **Closed or open interval.**  Milnor defines `exp_q(v)` with a geodesic on `[0, 1]`.  Here the
  geodesic is required on an open interval containing `[0, 1]`, which avoids one-sided derivatives.
  The values agree wherever both are defined, and near the zero section both domains contain all
  of `TN` (Lemma 10.2 gives geodesics on `(-2, 2)`).  A geodesic on `[0, 1]` always extends
  beyond the endpoints, so the two domains are equal: this is proved later, by
  `Morse.exists_initial_ray` (`Morse/Chapter9/GeodesicVariation.lean`) with
  `Morse.mem_expDom_of_isGeodesicOn` (`Morse/Chapter11/ExpSmooth.lean`).
* The smoothness of `exp` in `(q, v)` near the zero section is the smooth dependence in Lemma 10.2,
  which Milnor does not state.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

/-! ### Definition of `exp` -/

/-- `γ` is a geodesic through `q` with initial velocity `v`, defined on an open interval
`(-δ, 1 + δ)` containing `[0, 1]`. -/
def IsGeodesicFrom (γ : ℝ → V) (q v : V) : Prop :=
  ∃ δ > 0, IsGeodesicOn hN γ (Ioo (-δ) (1 + δ)) ∧ γ 0 = q ∧ deriv γ 0 = v

/-- **The domain of the exponential map**: the `(q, v)` for which there is a geodesic `γ` on an
open interval containing `[0, 1]` with `γ(0) = q`, `γ'(0) = v`. -/
def expDom : Set (V × V) := {z | ∃ γ, IsGeodesicFrom hN γ z.1 z.2}

open Classical in
/-- **The exponential map** (Milnor, p. 57): `exp_q(v) = γ(1)` for the geodesic `γ` with
`γ(0) = q`, `γ'(0) = v` (`Morse.IsGeodesicFrom.exp_eq`); `q` if there is none. -/
def exp (q v : V) : V := if h : ∃ γ, IsGeodesicFrom hN γ q v then h.choose 1 else q

variable {hN}

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem IsGeodesicFrom.mem_expDom {γ : ℝ → V} {q v : V} (h : IsGeodesicFrom hN γ q v) :
    (q, v) ∈ expDom hN :=
  ⟨γ, h⟩

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem IsGeodesicFrom.mem {γ : ℝ → V} {q v : V} (h : IsGeodesicFrom hN γ q v) : q ∈ N := by
  obtain ⟨δ, hδ, hγ, h0, -⟩ := h
  rw [← h0]
  exact hγ.mem 0 ⟨by linarith, by linarith⟩

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- A geodesic on an open interval containing `0` and `1` is a geodesic from `γ(0)` with initial
velocity `γ'(0)`. -/
theorem isGeodesicFrom_of_isGeodesicOn {γ : ℝ → V} {s : Set ℝ} (h : IsGeodesicOn hN γ s)
    (hs : IsPreconnected s) (h0 : (0 : ℝ) ∈ s) (h1 : (1 : ℝ) ∈ s) :
    IsGeodesicFrom hN γ (γ 0) (deriv γ 0) := by
  obtain ⟨δ₀, hδ₀, hb₀⟩ := Metric.isOpen_iff.1 h.isOpen 0 h0
  obtain ⟨δ₁, hδ₁, hb₁⟩ := Metric.isOpen_iff.1 h.isOpen 1 h1
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, h.mono isOpen_Ioo fun t ht => ?_, rfl, rfl⟩
  have hm₀ := min_le_left δ₀ δ₁
  have hm₁ := min_le_right δ₀ δ₁
  rcases le_or_gt t 0 with ht0 | ht0
  · exact hb₀ (by rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1])
  rcases le_or_gt 1 t with ht1 | ht1
  · exact hb₁ (by rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [ht.2])
  exact hs.ordConnected.out h0 h1 ⟨ht0.le, ht1.le⟩

/-- Two geodesics from `q` with initial velocity `v` agree on `[0, 1]` (and beyond). -/
theorem IsGeodesicFrom.eqOn {γ₁ γ₂ : ℝ → V} {q v : V} (h₁ : IsGeodesicFrom hN γ₁ q v)
    (h₂ : IsGeodesicFrom hN γ₂ q v) : ∃ δ > 0, EqOn γ₁ γ₂ (Ioo (-δ) (1 + δ)) := by
  obtain ⟨δ₁, hδ₁, hγ₁, h₁0, h₁0'⟩ := h₁
  obtain ⟨δ₂, hδ₂, hγ₂, h₂0, h₂0'⟩ := h₂
  have hsub₁ : Ioo (-min δ₁ δ₂) (1 + min δ₁ δ₂) ⊆ Ioo (-δ₁) (1 + δ₁) :=
    Ioo_subset_Ioo (by linarith [min_le_left δ₁ δ₂]) (by linarith [min_le_left δ₁ δ₂])
  have hsub₂ : Ioo (-min δ₁ δ₂) (1 + min δ₁ δ₂) ⊆ Ioo (-δ₂) (1 + δ₂) :=
    Ioo_subset_Ioo (by linarith [min_le_right δ₁ δ₂]) (by linarith [min_le_right δ₁ δ₂])
  have hm := lt_min hδ₁ hδ₂
  exact ⟨min δ₁ δ₂, hm, (hγ₁.mono isOpen_Ioo hsub₁).eqOn (hγ₂.mono isOpen_Ioo hsub₂)
    isPreconnected_Ioo ⟨by linarith, by linarith⟩ (h₁0.trans h₂0.symm) (h₁0'.trans h₂0'.symm)⟩

/-- **`exp` is well defined** (Milnor, p. 58: "if defined at all, `exp_q(v)` is always uniquely
defined"): `exp_q(v) = γ(1)` for every geodesic `γ` from `q` with initial velocity `v`. -/
theorem IsGeodesicFrom.exp_eq {γ : ℝ → V} {q v : V} (h : IsGeodesicFrom hN γ q v) :
    exp hN q v = γ 1 := by
  have hex : ∃ γ, IsGeodesicFrom hN γ q v := ⟨γ, h⟩
  rw [exp, dif_pos hex]
  obtain ⟨δ, hδ, heq⟩ := hex.choose_spec.eqOn h
  exact heq ⟨by linarith, by linarith⟩

theorem exp_eq_of_mem_expDom {q v : V} (h : (q, v) ∈ expDom hN) :
    ∃ γ, IsGeodesicFrom hN γ q v ∧ exp hN q v = γ 1 :=
  ⟨h.choose, h.choose_spec, h.choose_spec.exp_eq⟩

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem isGeodesicFrom_const {q : V} (hq : q ∈ N) :
    IsGeodesicFrom hN (fun _ => q) q 0 :=
  ⟨1, one_pos, isGeodesicOn_const hN hq isOpen_Ioo, rfl, deriv_const _ _⟩

/-- `exp_q(0) = q`. -/
theorem exp_zero {q : V} (hq : q ∈ N) : exp hN q 0 = q :=
  (isGeodesicFrom_const hq).exp_eq

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem zero_mem_expDom {q : V} (hq : q ∈ N) : (q, (0 : V)) ∈ expDom hN :=
  (isGeodesicFrom_const hq).mem_expDom

/-- **`γ(t) = exp_q(tv)`** (Milnor, p. 57): if `γ` is a geodesic from `q` with initial velocity `v`
on `(-δ, 1 + δ)`, then for `t` in that interval, `s ↦ γ(ts)` is a geodesic from `q` with initial
velocity `tv`, and `exp_q(tv) = γ(t)`. -/
theorem IsGeodesicFrom.exp_smul {γ : ℝ → V} {q v : V} (h : IsGeodesicFrom hN γ q v) :
    ∃ δ > 0, IsGeodesicOn hN γ (Ioo (-δ) (1 + δ)) ∧ ∀ t ∈ Ioo (-δ) (1 + δ),
      IsGeodesicFrom hN (fun s => γ (t * s)) q (t • v) ∧ exp hN q (t • v) = γ t := by
  obtain ⟨δ, hδ, hγ, h0, h0'⟩ := h
  refine ⟨δ, hδ, hγ, fun t ht => ?_⟩
  have hη := hγ.comp_mul_add t 0
  simp only [add_zero] at hη
  have hconv : Convex ℝ ((fun s => t * s) ⁻¹' Ioo (-δ) (1 + δ)) := by
    intro x hx y hy a b ha hb hab
    have := convex_Ioo (-δ) (1 + δ) hx hy ha hb hab
    simp only [mem_preimage, smul_eq_mul] at this ⊢
    convert this using 1
    ring
  have h00 : (0 : ℝ) ∈ (fun s => t * s) ⁻¹' Ioo (-δ) (1 + δ) := by
    simp only [mem_preimage, mul_zero]
    exact ⟨by linarith, by linarith⟩
  have h11 : (1 : ℝ) ∈ (fun s => t * s) ⁻¹' Ioo (-δ) (1 + δ) := by
    simpa only [mem_preimage, mul_one] using ht
  have hfrom := isGeodesicFrom_of_isGeodesicOn hη hconv.isPreconnected h00 h11
  have hd : deriv (fun s => γ (t * s)) 0 = t • v := by
    have h1 : HasDerivAt (fun s : ℝ => t * s) t 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul t
    have h2 := (hγ.hasDerivAt (t := t * 0) (by simp only [mul_zero]; exact
      ⟨by linarith, by linarith⟩)).scomp (0 : ℝ) h1
    rw [show (t * 0 : ℝ) = 0 by ring, h0'] at h2
    exact h2.deriv
  have h0q : γ (t * 0) = q := by simp only [mul_zero, h0]
  rw [hd, h0q] at hfrom
  refine ⟨hfrom, ?_⟩
  rw [hfrom.exp_eq, mul_one]

/-- The radial curve `t ↦ exp_q(tv)` is a geodesic near `[0, 1]`, equal to the geodesic from `q`
with initial velocity `v`. -/
theorem IsGeodesicFrom.isGeodesicOn_exp_smul {γ : ℝ → V} {q v : V}
    (h : IsGeodesicFrom hN γ q v) :
    ∃ δ > 0, IsGeodesicOn hN (fun t => exp hN q (t • v)) (Ioo (-δ) (1 + δ)) ∧
      EqOn (fun t => exp hN q (t • v)) γ (Ioo (-δ) (1 + δ)) := by
  obtain ⟨δ, hδ, hγ, hexp⟩ := h.exp_smul
  have heq : EqOn γ (fun t => exp hN q (t • v)) (Ioo (-δ) (1 + δ)) :=
    fun t ht => ((hexp t ht).2).symm
  exact ⟨δ, hδ, hγ.congr heq, fun t ht => heq.symm ht⟩

/-! ### Smoothness near the zero section -/

/-- **Lemma 10.2 in terms of `exp`**: near `(q₀, 0)`, `exp` is defined on `TN` and is the
restriction of a smooth map on `U × B_ε(0)`. -/
theorem exists_exp_eq (q₀ : N) :
    ∃ U : Set V, IsOpen U ∧ (q₀ : V) ∈ U ∧ ∃ ε > 0, ∃ F : V × V → V,
      ContDiffOn ℝ ∞ F (U ×ˢ ball (0 : V) ε) ∧
      ∀ p : N, (p : V) ∈ U → ∀ v ∈ tangentSubspace hN p, ‖v‖ < ε →
        ∃ γ, IsGeodesicFrom hN γ p v ∧ exp hN p v = F (p, v) := by
  obtain ⟨U, hU, hq₀, ε, hε, Γ, hΓ, hgeo⟩ := lemma_10_2 hN q₀
  have h1 : (1 : ℝ) ∈ Ioo (-2 : ℝ) 2 := ⟨by norm_num, by norm_num⟩
  refine ⟨U, hU, hq₀, ε, hε, fun z => Γ (z.1, z.2, 1), ?_, fun p hp v hv hvε => ?_⟩
  · exact hΓ.comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)).contDiffOn
      fun z hz => ⟨hz.1, hz.2, h1⟩
  · obtain ⟨hg, h0, hd, -⟩ := hgeo p hp v hv hvε
    have hfrom : IsGeodesicFrom hN (fun t => Γ (p, v, t)) p v :=
      ⟨1, one_pos, hg.mono isOpen_Ioo (Ioo_subset_Ioo (by norm_num) (by norm_num)), h0, hd.deriv⟩
    exact ⟨_, hfrom, hfrom.exp_eq⟩

/-- **`exp` is defined and smooth on an open neighbourhood of the zero section of `TN`**: there is
an open set `O ⊆ V × V` containing every `(q, 0)`, `q ∈ N`, such that every `(q, v) ∈ TN ∩ O` is in
the domain of `exp`, and near each point of `TN ∩ O`, `exp` is the restriction to `TN` of a smooth
map on an open set of `V × V`. -/
theorem exists_isOpen_exp :
    ∃ O : Set (V × V), IsOpen O ∧ (∀ q ∈ N, (q, (0 : V)) ∈ O) ∧
      ∀ z ∈ O, z ∈ Milnor.Problems.tangentBundleSet hN → z ∈ expDom hN ∧
        ∃ F : V × V → V, ∃ O' : Set (V × V), IsOpen O' ∧ z ∈ O' ∧ ContDiffOn ℝ ∞ F O' ∧
          ∀ z' ∈ O', z' ∈ Milnor.Problems.tangentBundleSet hN → exp hN z'.1 z'.2 = F z' := by
  choose U hU hqU ε hε F hF hexp using fun q₀ : N => exists_exp_eq (hN := hN) q₀
  refine ⟨⋃ q₀ : N, U q₀ ×ˢ ball (0 : V) (ε q₀),
    isOpen_iUnion fun q₀ => (hU q₀).prod isOpen_ball, fun q hq => ?_, fun z hz hzT => ?_⟩
  · exact mem_iUnion.2 ⟨⟨q, hq⟩, hqU _, mem_ball_self (hε _)⟩
  · obtain ⟨q₀, hz1, hz2⟩ := mem_iUnion.1 hz
    obtain ⟨hzN, hzv⟩ := hzT
    have hz2' : ‖z.2‖ < ε q₀ := by rwa [mem_ball, dist_zero_right] at hz2
    obtain ⟨γ, hγ, -⟩ := hexp q₀ ⟨z.1, hzN⟩ hz1 z.2 hzv hz2'
    refine ⟨hγ.mem_expDom, F q₀, U q₀ ×ˢ ball (0 : V) (ε q₀), (hU q₀).prod isOpen_ball,
      ⟨hz1, hz2⟩, hF q₀, fun z' hz' hz'T => ?_⟩
    obtain ⟨hz'N, hz'v⟩ := hz'T
    have h2 : ‖z'.2‖ < ε q₀ := by
      have := hz'.2
      rwa [mem_ball, dist_zero_right] at this
    exact (hexp q₀ ⟨z'.1, hz'N⟩ hz'.1 z'.2 hz'v h2).choose_spec.2

/-- **`exp` is smooth near the zero section**, for the manifold structure of the tangent bundle
`TN = Milnor.Problems.tangentBundleSet hN` (a slice submanifold of `V × V`, Milnor's "tangent
manifold", p. 58). -/
theorem contMDiffOn_exp :
    ∃ O : Set (V × V), IsOpen O ∧ (∀ q ∈ N, (q, (0 : V)) ∈ O) ∧
      (∀ z ∈ O, z ∈ Milnor.Problems.tangentBundleSet hN → z ∈ expDom hN) ∧
      (letI := (Milnor.Problems.isSliceSubmanifold_tangentBundle hN).chartedSpace
       ContMDiffOn 𝓘(ℝ, Z × Z) 𝓘(ℝ, V) ∞
        (fun z : Milnor.Problems.tangentBundleSet hN => exp hN z.1.1 z.1.2) {z | z.1 ∈ O}) := by
  obtain ⟨O, hO, h0, hexp⟩ := exists_isOpen_exp (hN := hN)
  refine ⟨O, hO, h0, fun z hz hzT => (hexp z hz hzT).1, ?_⟩
  let _ := (Milnor.Problems.isSliceSubmanifold_tangentBundle hN).chartedSpace
  have := (Milnor.Problems.isSliceSubmanifold_tangentBundle hN).isManifold
  intro z hz
  obtain ⟨-, F, O', hO', hzO', hF, hFeq⟩ := hexp z.1 hz z.2
  have hval := (Milnor.Problems.isSliceSubmanifold_tangentBundle hN).contMDiff_val
  have h1 : ContMDiffAt 𝓘(ℝ, Z × Z) 𝓘(ℝ, V) ∞ (F ∘ Subtype.val) z :=
    (hF.contDiffAt (hO'.mem_nhds hzO')).contMDiffAt.comp z (hval z)
  refine (h1.congr_of_eventuallyEq ?_).contMDiffWithinAt
  have hopen : IsOpen {z' : Milnor.Problems.tangentBundleSet hN | z'.1 ∈ O'} :=
    hO'.preimage continuous_subtype_val
  filter_upwards [hopen.mem_nhds hzO'] with z' hz'
  exact hFeq z'.1 hz' z'.2

/-- **`d(exp_q)₀ = id`** (Milnor, p. 58): the exponential map `exp_q : T_qN → V` has, at `0`,
derivative the inclusion of `T_qN` in `V`.  (Proof: near `0`, `exp_q` is smooth by Lemma 10.2, and
its derivative in the direction `v` is the velocity at `0` of `t ↦ exp_q(tv)`, the geodesic with
initial velocity `v`.) -/
theorem hasFDerivAt_exp_zero (q : N) :
    HasFDerivAt (fun v : tangentSubspace hN q => exp hN q v) (tangentSubspace hN q).subtypeL 0 := by
  obtain ⟨U, hU, hqU, ε, hε, F, hF, hexp⟩ := exists_exp_eq (hN := hN) q
  set Fq : V → V := fun v => F (q, v) with hFq
  have hFq_cd : ContDiffAt ℝ ∞ Fq 0 := by
    have h1 : ContDiffAt ℝ ∞ F ((q : V), (0 : V)) :=
      hF.contDiffAt ((hU.prod isOpen_ball).mem_nhds ⟨hqU, mem_ball_self hε⟩)
    exact h1.comp (0 : V) (contDiffAt_const.prodMk contDiffAt_id)
  have hFd : HasFDerivAt Fq (fderiv ℝ Fq 0) 0 :=
    (hFq_cd.differentiableAt (by simp)).hasFDerivAt
  -- `exp_q = Fq` near `0` on `T_qN`
  have hev : (fun v : tangentSubspace hN q => exp hN q v) =ᶠ[𝓝 0]
      fun v : tangentSubspace hN q => Fq v := by
    filter_upwards [ball_mem_nhds (0 : tangentSubspace hN q) hε] with v hv
    rw [mem_ball, dist_zero_right] at hv
    exact (hexp q hqU v v.2 (by simpa using hv)).choose_spec.2
  -- the directional derivatives of `Fq` along `T_qN` at `0` are the identity
  have hdir : ∀ v ∈ tangentSubspace hN q, ‖v‖ < ε → fderiv ℝ Fq 0 v = v := by
    intro v hv hvε
    obtain ⟨γ, hγ, -⟩ := hexp q hqU v hv hvε
    obtain ⟨δ, hδ, hγo, hsm⟩ := hγ.exp_smul
    have h0 : (0 : ℝ) ∈ Ioo (-δ) (1 + δ) := ⟨by linarith, by linarith⟩
    have hline : HasDerivAt (fun t : ℝ => Fq (t • v)) (fderiv ℝ Fq 0 v) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => t • v) v 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
      have hFd' : HasFDerivAt Fq (fderiv ℝ Fq 0) ((0 : ℝ) • v) := by
        rw [zero_smul]; exact hFd
      exact hFd'.comp_hasDerivAt (0 : ℝ) h1
    have hevγ : (fun t : ℝ => Fq (t • v)) =ᶠ[𝓝 0] γ := by
      have hball : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Ioo (-δ) (1 + δ) ∧ |t| < 1 := by
        filter_upwards [Ioo_mem_nhds h0.1 h0.2, Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
          (by norm_num : (0 : ℝ) < 1)] with t h1 h2
        exact ⟨h1, abs_lt.2 h2⟩
      filter_upwards [hball] with t ht
      have hsv : t • v ∈ tangentSubspace hN q := Submodule.smul_mem _ _ hv
      have hnorm : ‖t • v‖ < ε := by
        rw [norm_smul, Real.norm_eq_abs]
        calc |t| * ‖v‖ ≤ 1 * ‖v‖ := by gcongr; exact ht.2.le
          _ < ε := by linarith
      rw [← (hsm t ht.1).2]
      exact ((hexp q hqU (t • v) hsv hnorm).choose_spec.2).symm
    have := hγo.hasDerivAt h0
    rw [hγ.choose_spec.2.2.2] at this
    exact hline.unique (this.congr_of_eventuallyEq hevγ)
  have hD : (fderiv ℝ Fq 0).comp (tangentSubspace hN q).subtypeL =
      (tangentSubspace hN q).subtypeL := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    by_cases hv0 : (v : V) = 0
    · rw [hv0, map_zero]
    set a : ℝ := ε / (2 * ‖(v : V)‖) with ha_def
    have hvpos : 0 < ‖(v : V)‖ := norm_pos_iff.2 hv0
    have ha : 0 < a := by positivity
    have hav : ‖a • (v : V)‖ < ε := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, ha_def]
      field_simp
      linarith
    have := hdir (a • (v : V)) (Submodule.smul_mem _ _ v.2) hav
    rw [map_smul] at this
    exact smul_right_injective V ha.ne' this
  have hFd' : HasFDerivAt Fq (fderiv ℝ Fq 0)
      (((tangentSubspace hN q).subtypeL : tangentSubspace hN q →L[ℝ] V) 0) := by
    rw [map_zero]; exact hFd
  have hT : HasFDerivAt (fun v : tangentSubspace hN q => Fq v)
      ((fderiv ℝ Fq 0).comp (tangentSubspace hN q).subtypeL) 0 :=
    hFd'.comp (0 : tangentSubspace hN q) (tangentSubspace hN q).subtypeL.hasFDerivAt
  rw [hD] at hT
  exact hT.congr_of_eventuallyEq hev

end Morse
