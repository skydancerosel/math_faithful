import Morse.Chapter11.ExpSmooth
import Milnor.Chapter3.Sard

/-!
Milnor, *Morse Theory*, §18, pp. 98–99: the existence of non-conjugate points (Corollary 18.2),
for a submanifold `N ⊆ ℝᴷ` with the induced metric.

# Non-conjugate points

## Milnor's text, paraphrased

* (p. 98) Theorem 17.3 describes `Ω(M; p, q)` well when `p` and `q` are not conjugate along any
  geodesic; this section justifies it by showing that such non-conjugate points always exist.
* **Corollary 18.2** (p. 99): for `p ∈ M` and almost all `q ∈ M`, `p` is not conjugate to `q`
  along any geodesic.  Proof: this "follows immediately" from Theorem 18.1 and Sard's theorem
  (Milnor's 6.1).

## In the embedded setting

* `Morse.conjLocus hN p`: the points `q` conjugate to `p` along some geodesic `γ : [0, 1] → N`
  from `p` to `q` (`Morse.IsConjugate hN γ 0 1`).
* `Morse.theorem_18_1_of_geodesic`: **every geodesic from `p` is a radial geodesic**
  `t ↦ exp_p(tv)`, `v = γ'(0)` in the domain of `exp_p`, and Theorem 18.1 applies to it.
* `Morse.conjLocus_eq`: **the conjugate locus is the set of critical values of `exp_p`** on its
  domain (`exp_p(v)` with `d(exp_p)_v` not one-to-one).
* `Morse.corollary_18_2`: **Corollary 18.2**: the conjugate locus has measure zero in `N`: its
  image under every slice chart of `N` is a null set for every Haar measure on the model space
  `Z`.  `exp_p` composed with a chart is a smooth map between spaces of the same dimension, whose
  critical points are those of `exp_p` (a non-injective derivative stays non-injective, and an
  endomorphism of `Z` is onto iff it is one-to-one), so Sard's theorem (`Milnor.sard`) applies.
* `Morse.dense_compl_conjLocus`: **the points not conjugate to `p` are dense in `N`** (what
  Milnor uses: "such non-conjugate points always exist").
* `Morse.hessNullity_eq_zero_of_notMem_conjLocus`: for such `q`, every geodesic from `p` to `q`
  has a non-degenerate Hessian `E_**` (Theorem 14.1): the hypothesis of Theorems 16.3 and 17.3.
* `Morse.expDomAt_eq_univ`, `Morse.conjLocus_eq_of_complete`: for complete `N` (for instance
  `N` connected and closed in `V`, `Morse.hopf_rinow_of_isClosed`), `exp_p` is defined on all of
  `T_pN` (Milnor's standing assumption) and the conjugate locus is the set of critical values of
  `exp_p : T_pN → N`; none of the other results needs completeness.

## What Milnor leaves implicit

* **"Follows immediately"** hides three facts: a geodesic `γ` from `p` is the radial geodesic
  `t ↦ exp_p(tγ'(0))` (uniqueness of geodesics, and a geodesic segment extends past its end
  points, `Morse.exists_initial_ray`), so that the conjugate locus is the set of critical values
  of `exp_p`; `exp_p` is smooth on its whole domain (`Morse.exists_contDiffOn_exp`), so that
  Sard's theorem applies to it; and the domain is open, since Milnor's completeness assumption is
  dropped.
* **"Measure zero in `M`"** is not defined in the book: Theorem 6.1 (p. 33) states its
  conclusion in these terms, and §6 applies it only to maps into `ℝⁿ`; §18 is where the target is
  a manifold.  Here it means measure zero in every (slice) chart of `N`: Sard's theorem is applied
  to `exp_p` read in a chart, after identifying `T_pN` with the model space `Z` (they have the
  same dimension).
* **Existence of non-conjugate points**, which is what §18 is for, needs one more step: a null set
  has empty interior (a non-empty open set has positive Haar measure), so its complement is dense.
* Milnor's Sard theorem (6.1) is for `C¹` maps; the companion project proves it for smooth maps,
  which is the case here.
-/

open Set Filter Topology Function Module Metric MeasureTheory
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

/-! ### The conjugate locus -/

variable (hN) in
/-- **The points conjugate to `p` along some geodesic** (Milnor p. 99): the `q` for which there is
a geodesic `γ : [0, 1] → N` from `p` to `q` along which `0` and `1` are conjugate. -/
def conjLocus (p : V) : Set V :=
  {q | ∃ γ : ℝ → V, IsSmoothCurveIn hN γ ∧ IsGeodesicOn hN γ (Ioo 0 1) ∧ γ 0 = p ∧ γ 1 = q ∧
    IsConjugate hN γ 0 1}

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- Conjugacy only depends on the curve on `[0, 1]`. -/
theorem IsConjugate.congr_curve {γ γ' : ℝ → V} {a b : ℝ} (h : IsConjugate hN γ a b)
    (heq : EqOn γ γ' (Icc 0 1)) : IsConjugate hN γ' a b := by
  obtain ⟨ha, hb, hab, J, hJ, hJa, hJb, t, ht, hJt⟩ := h
  exact ⟨ha, hb, hab, J, hJ.congr_curve heq, hJa, hJb, t, ht, hJt⟩

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- Conjugacy only depends on the curve on `[0, 1]`. -/
theorem IsConjugate.congr_curve_iff {γ γ' : ℝ → V} {a b : ℝ} (heq : EqOn γ γ' (Icc 0 1)) :
    IsConjugate hN γ a b ↔ IsConjugate hN γ' a b :=
  ⟨fun h => h.congr_curve heq, fun h => h.congr_curve fun _ ht => (heq ht).symm⟩

/-- **Theorem 18.1 along any geodesic from `p`**: a geodesic `γ : [0, 1] → N` with `γ(0) = p` is
the radial geodesic `t ↦ exp_p(tv)` of its initial velocity `v = γ'(0)`; this `v` lies in the
domain of `exp_p`, `exp_p(v) = γ(1)`, and `γ(1)` is conjugate to `p` along `γ` iff `exp_p` is
critical at `v`. -/
theorem theorem_18_1_of_geodesic {p : N} {γ : ℝ → V} (hc : IsSmoothCurveIn hN γ)
    (hgeo : IsGeodesicOn hN γ (Ioo 0 1)) (hγ0 : γ 0 = p) :
    ∃ v : tangentSubspace hN p, (v : V) = velAlong γ 0 ∧ v ∈ expDomAt hN p ∧
      exp hN p v = γ 1 ∧ (IsConjugate hN γ 0 1 ↔ ¬ Injective (dExpAt hN p v)) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  obtain ⟨η, hη, hray, hrayγ⟩ := exists_initial_ray hc hgeo
  have hx : velAlong γ 0 ∈ tangentSubspace hN p := by
    have h := (prj_eq_self_iff hN (hc.mem 0 h0)).1 (hc.velAlong_mem h0)
    rwa [tangentSubspace_congr hN _ p.2 hγ0] at h
  rw [hγ0] at hray hrayγ
  have hxD : (⟨velAlong γ 0, hx⟩ : tangentSubspace hN p) ∈ expDomAt hN p :=
    mem_expDom_of_isGeodesicOn p.2 hx hη hray
  refine ⟨⟨velAlong γ 0, hx⟩, rfl, hxD, ?_, ?_⟩
  · have := hrayγ 1 ⟨zero_le_one, le_rfl⟩
    rwa [one_smul] at this
  · rw [← theorem_18_1 hxD]
    exact IsConjugate.congr_curve_iff fun t ht => (hrayγ t ht).symm

/-- **The conjugate locus of `p` is the set of critical values of `exp_p`** (the proof of
Corollary 18.2): `q` is conjugate to `p` along some geodesic iff `q = exp_p(v)` for a `v` in the
domain of `exp_p` at which `d(exp_p)_v` is not one-to-one. -/
theorem conjLocus_eq (p : N) : conjLocus hN p =
    (fun x : tangentSubspace hN p => exp hN p x) ''
      {x | x ∈ expDomAt hN p ∧ ¬ Injective (dExpAt hN p x)} := by
  ext q
  constructor
  · rintro ⟨γ, hc, hgeo, hγ0, hγ1, hconj⟩
    obtain ⟨v, -, hvD, hv1, hiff⟩ := theorem_18_1_of_geodesic hc hgeo hγ0
    exact ⟨v, ⟨hvD, hiff.1 hconj⟩, hv1.trans hγ1⟩
  · rintro ⟨x, ⟨hxD, hcrit⟩, rfl⟩
    obtain ⟨δ, hδ, hgeo⟩ := isGeodesicOn_ray hxD
    refine ⟨fun t => exp hN p (t • (x : V)), isSmoothCurveIn_ray hxD,
      hgeo.mono isOpen_Ioo (Ioo_subset_Ioo (by linarith) (by linarith)), ?_, ?_,
      (theorem_18_1 hxD).2 hcrit⟩
    · simp only [zero_smul, exp_zero p.2]
    · simp only [one_smul]

/-! ### Corollary 18.2 -/

/-- **Corollary 18.2** (Milnor p. 99): for `p ∈ N`, almost every point of `N` is not conjugate to
`p` along any geodesic: the conjugate locus of `p` has measure zero in `N`, i.e. its image under
every slice chart of `N` is a null set for every Haar measure on the model space `Z`.  (It is the
set of critical values of `exp_p`, `Morse.conjLocus_eq`, null by Sard's theorem.) -/
theorem corollary_18_2 (p : N) (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N) [MeasurableSpace Z]
    [BorelSpace Z] (μ : Measure Z) [μ.IsAddHaarMeasure] :
    μ ((fun y => (σ.φ y).1) '' (conjLocus hN p ∩ σ.φ.source)) = 0 := by
  set T := tangentSubspace hN p
  set E : T → V := fun x => exp hN p x with hE
  -- identify `T_pN` with `Z` (equal dimensions)
  have hdim : finrank ℝ Z = finrank ℝ T := by
    have := finrank_tanAt hN p.2
    rw [tanAt_of_mem hN p.2] at this
    exact this.symm
  let e : Z ≃L[ℝ] T := ContinuousLinearEquiv.ofFinrankEq hdim
  set D := expDomAt hN p
  have hEs : ContDiffOn ℝ ∞ E D := contDiffOn_expAt p
  -- `g = (σ ∘ exp_p ∘ e)₁`, smooth on an open set `U'`
  set U' : Set Z := e ⁻¹' D ∩ (E ∘ e) ⁻¹' σ.φ.source with hU'
  set g : Z → Z := fun z => (σ.φ (E (e z))).1 with hg
  have hEe : ContDiffOn ℝ ∞ (E ∘ e) (e ⁻¹' D) :=
    hEs.comp e.contDiff.contDiffOn (mapsTo_preimage e D)
  have hU'open : IsOpen U' :=
    hEe.continuousOn.isOpen_inter_preimage ((isOpen_expDomAt p).preimage e.continuous)
      σ.φ.open_source
  have hgs : ContDiffOn ℝ ∞ g U' :=
    contDiff_fst.comp_contDiffOn ((Milnor.Problems.sliceChart_contDiffOn σ).comp
      (hEe.mono inter_subset_left) fun z hz => hz.2)
  refine measure_mono_null ?_ (Milnor.sard μ hU'open hgs)
  rintro _ ⟨y, ⟨hy, hys⟩, rfl⟩
  rw [conjLocus_eq] at hy
  obtain ⟨x, ⟨hxD, hcrit⟩, rfl⟩ := hy
  have hz : e.symm x ∈ U' := ⟨by simpa using hxD, by simpa using hys⟩
  refine ⟨e.symm x, ⟨hz, fun hsurj => ?_⟩, by simp [g, hE]⟩
  -- `dg = (dσ ∘ d(exp_p)_x ∘ e)₁` is not one-to-one, hence (an endomorphism of `Z`) not onto
  have hEd : HasFDerivAt E (fderiv ℝ E x) (e (e.symm x)) := by
    rw [e.apply_symm_apply]
    exact ((hEs.contDiffAt ((isOpen_expDomAt p).mem_nhds hxD)).differentiableAt
      (by simp)).hasFDerivAt
  have hEe' : HasFDerivAt (E ∘ e) ((fderiv ℝ E x).comp (e : Z →L[ℝ] T)) (e.symm x) :=
    hEd.comp (e.symm x) e.hasFDerivAt
  have hσd : HasFDerivAt σ.φ (fderiv ℝ σ.φ (E x)) ((E ∘ e) (e.symm x)) := by
    rw [comp_apply, e.apply_symm_apply]
    exact (Milnor.Problems.sliceChart_differentiableAt σ hys).hasFDerivAt
  have hgd : HasFDerivAt g ((ContinuousLinearMap.fst ℝ Z W).comp
      ((fderiv ℝ σ.φ (E x)).comp ((fderiv ℝ E x).comp (e : Z →L[ℝ] T)))) (e.symm x) :=
    (ContinuousLinearMap.fst ℝ Z W).hasFDerivAt.comp _ (hσd.comp (e.symm x) hEe')
  rw [hgd.fderiv] at hsurj
  have hinj := LinearMap.injective_iff_surjective.2 hsurj
  apply hcrit
  intro a b hab
  have h1 : dExpAt hN p x (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have h2 := @hinj (e.symm (a - b)) 0 (by
    change (ContinuousLinearMap.fst ℝ Z W) (fderiv ℝ σ.φ (E x) (fderiv ℝ E x
      ((e : Z →L[ℝ] T) (e.symm (a - b))))) = _
    rw [ContinuousLinearEquiv.coe_coe, e.apply_symm_apply, ← dExpAt_apply, h1, map_zero,
      map_zero, map_zero])
  rw [map_eq_zero_iff _ e.symm.injective, sub_eq_zero] at h2
  exact h2

/-- **Non-conjugate points are dense** (Milnor p. 99, the conclusion drawn from 18.2 for §17):
for every `p ∈ N`, the points of `N` not conjugate to `p` along any geodesic are dense in `N`.
(A nonempty open set of `Z` has positive Haar measure, so it is not contained in the null image of
the conjugate locus under a chart.) -/
theorem dense_compl_conjLocus (p : N) : Dense {q : N | (q : V) ∉ conjLocus hN p} := by
  let _ : MeasurableSpace Z := borel Z
  have : BorelSpace Z := ⟨rfl⟩
  set μ : Measure Z := (Module.Basis.ofVectorSpace ℝ Z).addHaar
  rw [dense_iff_inter_open]
  rintro U hU ⟨q, hqU⟩
  set σ := sliceAt hN q
  set O : Set Z := σ.toChart '' (U ∩ σ.toChart.source) with hOdef
  have hO : IsOpen O :=
    σ.toChart.isOpen_image_of_subset_source (hU.inter σ.toChart.open_source) inter_subset_right
  have hqO : σ.toChart q ∈ O := ⟨q, ⟨hqU, mem_sliceAt_source hN q⟩, rfl⟩
  have hpos : 0 < μ O := hO.measure_pos μ ⟨_, hqO⟩
  have hnsub : ¬ O ⊆ (fun y => (σ.φ y).1) '' (conjLocus hN p ∩ σ.φ.source) := fun h =>
    hpos.ne' (measure_mono_null h (corollary_18_2 p σ μ))
  obtain ⟨z, ⟨y, ⟨hyU, hys⟩, rfl⟩, hz⟩ := not_subset.1 hnsub
  exact ⟨y, hyU, fun hy => hz ⟨y, ⟨hy, hys⟩, rfl⟩⟩

/-- **Outside the conjugate locus of `p`, every geodesic from `p` is non-degenerate**: for
`q ∉ conjLocus hN p`, the Hessian `E_**` at every geodesic `γ ∈ Ω(N; p, q)` has nullity `0`
(Theorem 14.1).  This is the hypothesis of Milnor's Theorems 16.3 and 17.3, which by
Corollary 18.2 holds for almost every `q`. -/
theorem hessNullity_eq_zero_of_notMem_conjLocus {p q : V} (hq : q ∉ conjLocus hN p)
    {γ : ℝ → V} (hγ : γ ∈ pathSpace N p q) (hgeo : IsUnbrokenGeodesic hN γ) :
    hessNullity hN hγ = 0 := by
  by_contra h
  exact hq ⟨γ, hgeo.isSmoothCurveIn hN hγ, hgeo.2, hγ.2.2.1, hγ.2.2.2,
    (hessNullity_pos_iff hγ hgeo).1 (Nat.pos_of_ne_zero h)⟩

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- When `N` is complete, `exp_q` is defined on all of `T_qN` (Milnor's standing assumption in
§18). -/
theorem expDomAt_eq_univ (hc : IsGeodesicallyComplete hN) (q : N) : expDomAt hN q = univ :=
  eq_univ_of_forall fun v => hc q v v.2

/-- **For complete `N`, the conjugate locus is the set of critical values of
`exp_p : T_pN → N`** (Milnor's setting in §18: completeness makes `exp_p` defined everywhere). -/
theorem conjLocus_eq_of_complete (hc : IsGeodesicallyComplete hN) (p : N) :
    conjLocus hN p = (fun x : tangentSubspace hN p => exp hN p x) ''
      {x | ¬ Injective (dExpAt hN p x)} := by
  rw [conjLocus_eq, expDomAt_eq_univ hc]
  simp

end Morse
