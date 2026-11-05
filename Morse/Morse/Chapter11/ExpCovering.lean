import Morse.Chapter11.Curvature
import Morse.Chapter11.NonConjugate

/-!
Milnor, *Morse Theory*, §19, pp. 102–103 (the end of the proof of Theorem 19.2 and the paragraph
on the universal covering), for a submanifold `N ⊆ ℝᴷ` with the induced metric: if `N` is complete
and `exp_p` is nowhere critical, `exp_p : T_pN → N` is a local diffeomorphism and a covering map.
In non-positive curvature `exp_p` is nowhere critical (Lemma 19.1 with Theorem 18.1,
`Morse.injective_dExpAt_of_nonpos`); the consequences are drawn in
`Morse/Chapter11/CartanHadamard.lean`.  The covering argument is the standard proof of the
Cartan–Hadamard theorem, not Milnor's, who works with the path space instead.

# `exp_p` is a covering map

## Milnor's text, paraphrased

* (p. 103, end of the proof of 19.2) By 18.1, `exp_p` is non-critical everywhere, so it is locally
  a diffeomorphism; being one-one and onto, it is a global diffeomorphism.
* (p. 103) If `M` is complete with curvature `≤ 0` but not simply connected, "it is clear" that the
  universal covering space `M̃` inherits a geodesically complete metric of curvature `≤ 0`, so that
  19.2 applies to `M̃`; each homotopy class of paths from `p` to `q` contains exactly one geodesic.

## In the embedded setting

* `Morse.gauss_lemma_expDomAt`: **the Gauss lemma on the whole domain of `exp_p`**,
  `⟨d(exp_p)_w(w), d(exp_p)_w(x)⟩ = ⟨w, x⟩`, with the proof of Lemma 10.5 (Milnor states it only
  in a normal neighbourhood, `Morse.gauss_lemma`); `Morse.norm_fderiv_expAt_apply`: radial
  geodesics have constant speed.
* `Morse.isLocalDiffeomorphAt_expToN`, `Morse.isLocalDiffeomorph_expToN`: **`exp_p : T_pN → N` is
  a local diffeomorphism at every point where `d(exp_p)` is one-to-one** (Milnor's "locally a
  diffeomorphism"), for the manifold structure of `N`.
* `Morse.norm_expLift_le`: **lifts do not escape to infinity**: a lift `Γ` through `exp_p` of a
  smooth curve of speed `≤ L` satisfies `‖Γ(t)‖ ≤ ‖Γ(0)‖ + 1 + Lt`.
* `Morse.exists_expLift`, `Morse.expLift_unique`: **smooth curves lift uniquely through `exp_p`**,
  from any point over the initial point, when `N` is complete and `exp_p` is nowhere critical.
* `Morse.isCoveringMap_expToN`: **`exp_p` is a covering map** (Mathlib's `IsCoveringMap`) under
  the same hypotheses.

## What Milnor leaves implicit

* **The covering space.**  Milnor gets the injectivity of `exp_p` from the path space (Theorem
  17.3), and for non-simply-connected `M` he quotes the universal covering.  Here `T_pN` itself,
  through `exp_p`, is the universal covering of `N`; the only analytic input beyond Lemma 19.1 is
  the completeness of `T_pN` for the metric pulled back by `exp_p`, Milnor's "it is clear".  It
  is used in the form `Morse.norm_expLift_le` (the pulled-back metric is never introduced): by the
  Gauss lemma `⟨Γ, Γ'⟩ = ⟨d(exp_p)_Γ(Γ), c'⟩` and `‖d(exp_p)_Γ(Γ)‖ = ‖Γ‖`, so the radius of a
  lift grows no faster than the length of the curve.  This needs the Gauss lemma for `exp_p` on
  its whole domain, not only in a normal neighbourhood.
* **"Locally a diffeomorphism"** is the inverse function theorem on manifolds (the companion
  project's `Milnor.isLocalDiffeomorphAt_of_isInvertible_mfderiv`): the derivative of `exp_p` as a
  map into `N`, followed by the derivative of the inclusion `N → V`, is `d(exp_p)` as a map into
  `V`, so it is one-to-one, and it is onto because `dim T_pN = dim N`.
* **Lifting curves** is a continuity argument: the set of times up to which a lift exists is
  closed because lifts stay bounded, hence accumulate, and `exp_p` is a local diffeomorphism at
  an accumulation point.
* **The sheets** over a normal ball `B` about `q` are the images of the sections obtained by
  lifting the radial geodesics of `B` from the points over `q`; they depend continuously on the
  end point by the homotopy lifting lemma for local homeomorphisms (Mathlib's
  `IsLocalHomeomorph.continuous_lift`).  Every point over `B` lies on a sheet (lift a radial
  geodesic backwards), and two sheets which meet coincide (uniqueness of lifts: `T_pN` is
  Hausdorff and `exp_p` locally injective).
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace unitInterval

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

/-! ### The Gauss lemma on the whole domain of `exp_p` -/

/-- `exp_p` is smooth at every point of its domain, as a map on the vector space `T_pN`. -/
theorem contDiffAt_expAt {p : N} {v : tangentSubspace hN p} (hv : v ∈ expDomAt hN p) :
    ContDiffAt ℝ ∞ (fun y : tangentSubspace hN p => exp hN p y) v :=
  (contDiffOn_expAt p).contDiffAt ((isOpen_expDomAt p).mem_nhds hv)

/-- **Radial geodesics have constant speed**: `‖d(exp_p)_{ru}(u)‖ = ‖u‖` for `u` in the domain of
`exp_p` and `0 ≤ r ≤ 1`. -/
theorem norm_fderiv_expAt_apply {p : N} {u : tangentSubspace hN p} (hu : u ∈ expDomAt hN p)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    ‖fderiv ℝ (fun y : tangentSubspace hN p => exp hN p y) (r • u) u‖ = ‖(u : V)‖ := by
  obtain ⟨δ, hδ, hgeo⟩ := isGeodesicOn_ray hu
  have hrδ : r ∈ Ioo (-δ) (1 + δ) := ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have h0δ : (0 : ℝ) ∈ Ioo (-δ) (1 + δ) := ⟨by linarith, by linarith⟩
  have hd : HasDerivAt (fun t : ℝ => exp hN p ((t • u : tangentSubspace hN p) : V))
      (fderiv ℝ (fun y : tangentSubspace hN p => exp hN p y) (r • u) u) r := by
    have h1 : HasDerivAt (fun t : ℝ => t • u) u r := by
      simpa using (hasDerivAt_id r).smul_const u
    exact ((contDiffAt_expAt (smul_mem_expDomAt hu hr)).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt r h1
  simp only [Submodule.coe_smul] at hd
  rw [← hd.deriv, hgeo.norm_deriv_eq isPreconnected_Ioo hrδ h0δ,
    (hasDerivAt_exp_smul_zero p u.2).deriv]

/-- **The Gauss lemma on the whole domain of `exp_p`**:
`⟨d(exp_p)_w(w), d(exp_p)_w(x)⟩ = ⟨w, x⟩` for `w` in the domain of `exp_p` and `x ∈ T_pN`. -/
theorem gauss_lemma_expDomAt {p : N} {w : tangentSubspace hN p} (hw : w ∈ expDomAt hN p)
    (x : tangentSubspace hN p) :
    ⟪fderiv ℝ (fun y : tangentSubspace hN p => exp hN p y) w w,
      fderiv ℝ (fun y : tangentSubspace hN p => exp hN p y) w x⟫ = ⟪(w : V), x⟫ := by
  set E : tangentSubspace hN p → V := fun y => exp hN p y with hE_def
  set D := fderiv ℝ E with hD_def
  set D2 := fderiv ℝ D with hD2_def
  have hO : IsOpen (expDomAt hN p) := isOpen_expDomAt p
  have hseg : ∀ r ∈ Icc (0 : ℝ) 1, r • w ∈ expDomAt hN p := fun r hr => smul_mem_expDomAt hw hr
  have hDd : ∀ v ∈ expDomAt hN p, HasFDerivAt D (D2 v) v := fun v hv =>
    (((contDiffAt_expAt hv).fderiv_right (m := ∞) (by simp)).differentiableAt
      (by simp)).hasFDerivAt
  have hEd : ∀ v ∈ expDomAt hN p, HasFDerivAt E (D v) v := fun v hv =>
    ((contDiffAt_expAt hv).differentiableAt (by simp)).hasFDerivAt
  have hlin : ∀ (r : ℝ) (v : tangentSubspace hN p), HasDerivAt (fun s : ℝ => s • v) v r :=
    fun r v => by simpa using (hasDerivAt_id r).smul_const v
  set g : ℝ → ℝ := fun r => ⟪D (r • w) w, D (r • w) (r • x)⟫ with hg_def
  -- `g` is continuous on `[0, 1]`
  have hgc : ContinuousOn g (Icc 0 1) := by
    have hDc : ContinuousOn (fun r : ℝ => D (r • w)) (Icc 0 1) := by
      intro r hr
      have h1 : ContinuousAt (fun r : ℝ => r • w) r :=
        (continuous_id.smul continuous_const).continuousAt
      have h2 : ContinuousAt D ((fun r : ℝ => r • w) r) := (hDd _ (hseg r hr)).continuousAt
      exact (ContinuousAt.comp (f := fun r : ℝ => r • w) h2 h1).continuousWithinAt
    exact (hDc.clm_apply continuousOn_const).inner (hDc.clm_apply
      (continuous_id.smul continuous_const).continuousOn)
  -- `g' = ⟨w, x⟩` on `(0, 1)`
  have hg' : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt g ⟪(w : V), x⟫ r := by
    intro r hr
    have hrI : r ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hr
    have hrw := hseg r hrI
    have hDr : HasDerivAt (fun s : ℝ => D (s • w)) (D2 (r • w) w) r :=
      (hDd _ hrw).comp_hasDerivAt r (hlin r w)
    have ha : HasDerivAt (fun s : ℝ => D (s • w) w) (D2 (r • w) w w) r := by
      simpa using hDr.clm_apply (hasDerivAt_const r w)
    have hb : HasDerivAt (fun s : ℝ => D (s • w) (s • x)) (D2 (r • w) w (r • x) + D (r • w) x) r :=
      hDr.clm_apply (hlin r x)
    have hgd := ha.inner ℝ hb
    -- (i) the acceleration of the radial geodesic is normal, `∂f/∂s` is tangent
    have hi : ⟪D2 (r • w) w w, D (r • w) (r • x)⟫ = 0 := by
      obtain ⟨δ, hδ, hgeo⟩ := isGeodesicOn_ray hw
      have hrδ : r ∈ Ioo (-δ) (1 + δ) := ⟨by linarith [hr.1], by linarith [hr.2]⟩
      have hev : ∀ᶠ t in 𝓝 r, t • w ∈ expDomAt hN p :=
        ((continuous_id.smul continuous_const).continuousAt (x := r)).eventually
          (hO.mem_nhds hrw)
      have hevd : deriv (fun t : ℝ => E (t • w)) =ᶠ[𝓝 r] fun t => D (t • w) w := by
        filter_upwards [hev] with t ht
        exact ((hEd _ ht).comp_hasDerivAt t (hlin t w)).deriv
      have hfun : (fun t : ℝ => E (t • w)) = fun t => exp hN p (t • (w : V)) := by
        funext t; simp [hE_def]
      have hacc : deriv (deriv fun t : ℝ => exp hN p (t • (w : V))) r = D2 (r • w) w w := by
        rw [← hfun, hevd.deriv_eq, ha.deriv]
      have hnormal := hgeo.normal r hrδ
      rw [hacc] at hnormal
      -- `∂f/∂s` is tangent at `exp_p(rw)`
      have hcurve : HasDerivAt (fun s : ℝ => E (r • w + s • (r • x))) (D (r • w) (r • x)) 0 := by
        have h1 : HasDerivAt (fun s : ℝ => r • w + s • (r • x)) (r • x) 0 := by
          simpa using (hlin 0 (r • x)).const_add (r • w)
        have hF' : HasFDerivAt E (D (r • w)) ((fun s : ℝ => r • w + s • (r • x)) 0) := by
          simpa using hEd _ hrw
        exact hF'.comp_hasDerivAt (0 : ℝ) h1
      have hcurveN : ∀ᶠ s in 𝓝 (0 : ℝ), E (r • w + s • (r • x)) ∈ N := by
        have hc : Continuous fun s : ℝ => r • w + s • (r • x) :=
          continuous_const.add (continuous_id.smul continuous_const)
        have : ∀ᶠ s in 𝓝 (0 : ℝ), r • w + s • (r • x) ∈ expDomAt hN p :=
          hc.continuousAt.eventually (hO.mem_nhds (by simpa using hrw))
        filter_upwards [this] with s hs
        exact exp_mem_of_mem_expDom hs
      have htan := hasDerivAt_mem_tangentSubspace hN hcurve hcurveN
      have hbase : E (r • w + (0 : ℝ) • (r • x)) = exp hN p (r • (w : V)) := by
        simp [hE_def]
      rw [tangentSubspace_congr hN _ (hgeo.mem r hrδ) hbase] at htan
      exact Submodule.inner_left_of_mem_orthogonal htan hnormal
    -- (ii) the derivative of `‖∂f/∂r‖² = ‖w + sx‖²` in `s`
    have hii : ⟪D (r • w) w, D2 (r • w) w (r • x) + D (r • w) x⟫ = ⟪(w : V), x⟫ := by
      have hc : HasDerivAt (fun s : ℝ => r • (w + s • x)) (r • x) 0 :=
        ((hlin 0 x).const_add w).const_smul r
      have hDc : HasDerivAt (fun s : ℝ => D (r • (w + s • x))) (D2 (r • w) (r • x)) 0 := by
        have hD' : HasFDerivAt D (D2 (r • w)) ((fun s : ℝ => r • (w + s • x)) 0) := by
          simpa using hDd _ hrw
        exact hD'.comp_hasDerivAt (0 : ℝ) hc
      have hh : HasDerivAt (fun s : ℝ => D (r • (w + s • x)) (w + s • x))
          (D2 (r • w) (r • x) w + D (r • w) x) 0 := by
        simpa using hDc.clm_apply ((hlin 0 x).const_add w)
      have hh2 := hh.norm_sq
      have hev : (fun s : ℝ => ‖D (r • (w + s • x)) (w + s • x)‖ ^ 2) =ᶠ[𝓝 0]
          fun s => ‖((w + s • x : tangentSubspace hN p) : V)‖ ^ 2 := by
        have hc' : Continuous fun s : ℝ => w + s • x :=
          continuous_const.add (continuous_id.smul continuous_const)
        have : ∀ᶠ s in 𝓝 (0 : ℝ), w + s • x ∈ expDomAt hN p :=
          hc'.continuousAt.eventually (hO.mem_nhds (by simpa using hw))
        filter_upwards [this] with s hs
        rw [norm_fderiv_expAt_apply hs hrI]
      have hh3 : HasDerivAt (fun s : ℝ => ‖((w + s • x : tangentSubspace hN p) : V)‖ ^ 2)
          (2 * ⟪(w : V), x⟫) 0 := by
        have := ((hlin 0 x).const_add w).norm_sq
        simpa using this
      have := hh2.unique (hh3.congr_of_eventuallyEq hev)
      simp only [zero_smul, add_zero] at this
      have hsymm : D2 (r • w) (r • x) w = D2 (r • w) w (r • x) :=
        ((contDiffAt_expAt hrw).isSymmSndFDerivAt (by
          simp only [minSmoothness_of_isRCLikeNormedField]
          exact WithTop.coe_le_coe.2 le_top)) (r • x) w
      rw [hsymm] at this
      linarith
    have e : ⟪(w : V), x⟫ = ⟪D (r • w) w, D2 (r • w) w (r • x) + D (r • w) x⟫ +
        ⟪D2 (r • w) w w, D (r • w) (r • x)⟫ := by
      rw [hi, add_zero, hii]
    rw [e]
    exact hgd
  obtain ⟨c, -, hc⟩ := exists_hasDerivAt_eq_slope g (fun _ => ⟪(w : V), x⟫) zero_lt_one hgc hg'
  have hg0 : g 0 = 0 := by simp [hg_def]
  have hg1 : g 1 = ⟪D w w, D w x⟫ := by simp [hg_def]
  rw [hg0, hg1] at hc
  simp only [sub_zero, div_one] at hc
  exact hc.symm

/-! ### `exp_p` is a local diffeomorphism -/

/-- On the domain of `exp_p`, `expToN` is `exp_p`. -/
theorem coe_expToN_of_mem {p : N} {v : tangentSubspace hN p} (hv : v ∈ expDomAt hN p) :
    (expToN hN p v : V) = exp hN p v :=
  coe_expToN hN (exp_mem_of_mem_expDom hv)

/-- `exp_p : T_pN → N` is smooth (for the manifold structure of `N`) at every point of its
domain. -/
theorem contMDiffAt_expToN {p : N} {v : tangentSubspace hN p} (hv : v ∈ expDomAt hN p) :
    letI := hN.chartedSpace
    ContMDiffAt 𝓘(ℝ, tangentSubspace hN p) 𝓘(ℝ, Z) ∞ (expToN hN p) v := by
  refine contMDiffAt_of_val_eventuallyEq hN (contDiffAt_expAt hv) ?_
  filter_upwards [(isOpen_expDomAt p).mem_nhds hv] with w hw
  exact coe_expToN_of_mem hw

/-- **`exp_p` is a local diffeomorphism at every non-critical point of its domain** (the inverse
function theorem): if `d(exp_p)_v` is one-to-one, `exp_p : T_pN → N` is a local diffeomorphism
at `v`. -/
theorem isLocalDiffeomorphAt_expToN {p : N} {v : tangentSubspace hN p} (hv : v ∈ expDomAt hN p)
    (hinj : Injective (dExpAt hN p v)) :
    letI := hN.chartedSpace
    IsLocalDiffeomorphAt 𝓘(ℝ, tangentSubspace hN p) 𝓘(ℝ, Z) ∞ (expToN hN p) v := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  set f := expToN hN p
  have hf : ∀ᶠ y in 𝓝 v, ContMDiffAt 𝓘(ℝ, tangentSubspace hN p) 𝓘(ℝ, Z) ∞ f y := by
    filter_upwards [(isOpen_expDomAt p).mem_nhds hv] with y hy
    exact contMDiffAt_expToN hy
  refine Milnor.isLocalDiffeomorphAt_of_isInvertible_mfderiv hf (by simp) ?_
  -- `val ∘ f = exp_p` near `v`, so `d val ∘ df = d(exp_p)`, injective
  have hval : MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, V) (Subtype.val : N → V) (f v) :=
    (hN.contMDiff_val (f v)).mdifferentiableAt (by simp)
  have hfd : MDifferentiableAt 𝓘(ℝ, tangentSubspace hN p) 𝓘(ℝ, Z) f v :=
    hf.self_of_nhds.mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp v hval hfd
  have hev : (Subtype.val ∘ f) =ᶠ[𝓝 v] fun y : tangentSubspace hN p => exp hN p y := by
    filter_upwards [(isOpen_expDomAt p).mem_nhds hv] with y hy
    exact coe_expToN_of_mem hy
  rw [hev.mfderiv_eq, mfderiv_eq_fderiv] at hcomp
  let L : tangentSubspace hN p →L[ℝ] Z := mfderiv 𝓘(ℝ, tangentSubspace hN p) 𝓘(ℝ, Z) f v
  have key : ∀ a : tangentSubspace hN p,
      fderiv ℝ (fun y : tangentSubspace hN p => exp hN p y) v a =
        mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, V) (Subtype.val : N → V) (f v) (L a) := by
    intro a
    rw [hcomp]
    rfl
  have hLinj : Injective L := by
    intro a b hab
    apply hinj
    change fderiv ℝ (fun y : tangentSubspace hN p => exp hN p y) v a =
      fderiv ℝ (fun y : tangentSubspace hN p => exp hN p y) v b
    rw [key, key, hab]
  have hdim : finrank ℝ (tangentSubspace hN p) = finrank ℝ Z := by
    have := finrank_tanAt hN p.2
    rw [tanAt_of_mem hN p.2] at this
    exact this
  have hLsurj : Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := (L :
      tangentSubspace hN p →ₗ[ℝ] Z))).1 hLinj
  change L.IsInvertible
  exact ⟨(LinearEquiv.ofBijective (L : tangentSubspace hN p →ₗ[ℝ] Z)
    ⟨hLinj, hLsurj⟩).toContinuousLinearEquiv, rfl⟩

/-- **`exp_p` is a local diffeomorphism** `T_pN → N` when `N` is complete and `exp_p` is
nowhere critical. -/
theorem isLocalDiffeomorph_expToN (hc : IsGeodesicallyComplete hN) {p : N}
    (hcrit : ∀ v, Injective (dExpAt hN p v)) :
    letI := hN.chartedSpace
    IsLocalDiffeomorph 𝓘(ℝ, tangentSubspace hN p) 𝓘(ℝ, Z) ∞ (expToN hN p) := fun v =>
  isLocalDiffeomorphAt_expToN (hc p v v.2) (hcrit v)

/-! ### Lifting curves through `exp_p` -/

/-- **A lift of a smooth curve through `exp_p` is differentiable**, and `d(exp_p)` maps its
velocity to the velocity of the curve. -/
theorem hasDerivAt_expLift (hc : IsGeodesicallyComplete hN) {p : N}
    (hcrit : ∀ v, Injective (dExpAt hN p v)) {c : ℝ → V} (hcs : ContDiff ℝ ∞ c)
    (hcN : ∀ t, c t ∈ N) {Γ : ℝ → tangentSubspace hN p} {t₀ : ℝ} (hΓ : ContinuousAt Γ t₀)
    (hlift : ∀ᶠ t in 𝓝 t₀, exp hN p (Γ t) = c t) :
    ∃ Γ' : tangentSubspace hN p, HasDerivAt Γ Γ' t₀ ∧
      fderiv ℝ (fun y : tangentSubspace hN p => exp hN p y) (Γ t₀) Γ' = deriv c t₀ := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  obtain ⟨Φ, hΦs, hΦf⟩ := isLocalDiffeomorph_expToN hc hcrit (Γ t₀)
  set cN : ℝ → N := fun t => ⟨c t, hcN t⟩ with hcN_def
  have hcNs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Z) ∞ cN := hN.contMDiff_codRestrict hcs.contMDiff hcN
  have hsrc : ∀ᶠ t in 𝓝 t₀, Γ t ∈ Φ.source := hΓ.eventually (Φ.open_source.mem_nhds hΦs)
  have hfeq : ∀ᶠ t in 𝓝 t₀, expToN hN p (Γ t) = cN t := by
    filter_upwards [hlift] with t ht
    exact Subtype.ext ((coe_expToN_of_mem (hc p _ (Γ t).2)).trans ht)
  have heq : Γ =ᶠ[𝓝 t₀] fun t => Φ.symm (cN t) := by
    filter_upwards [hsrc, hfeq] with t h1 h2
    rw [← h2, hΦf h1]
    exact (Φ.toPartialEquiv.left_inv h1).symm
  have htgt : cN t₀ ∈ Φ.target := by
    rw [← hfeq.self_of_nhds, hΦf hΦs]
    exact Φ.toPartialEquiv.map_source hΦs
  have hsm : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, tangentSubspace hN p) ∞ (fun t => Φ.symm (cN t)) t₀ :=
    (Φ.symm.contMDiffOn.contMDiffAt (Φ.open_target.mem_nhds htgt)).comp t₀ (hcNs t₀)
  have hcd : ContDiffAt ℝ ∞ (fun t => Φ.symm (cN t)) t₀ := contMDiffAt_iff_contDiffAt.1 hsm
  have hd : HasDerivAt Γ (deriv (fun t => Φ.symm (cN t)) t₀) t₀ :=
    ((hcd.differentiableAt (by simp)).hasDerivAt).congr_of_eventuallyEq heq
  refine ⟨_, hd, ?_⟩
  have hE := ((contDiffAt_expAt (hc p _ (Γ t₀).2)).differentiableAt (by simp)).hasFDerivAt
  have h1 := hE.comp_hasDerivAt t₀ hd
  have h2 : HasDerivAt c (deriv c t₀) t₀ :=
    ((hcs.differentiable (by simp)) t₀).hasDerivAt
  exact h1.unique (h2.congr_of_eventuallyEq hlift)

/-- `‖d(exp_p)_w(w)‖ = ‖w‖` on the domain of `exp_p` (the Gauss lemma with `x = w`). -/
theorem norm_fderiv_expAt_self {p : N} {w : tangentSubspace hN p} (hw : w ∈ expDomAt hN p) :
    ‖fderiv ℝ (fun y : tangentSubspace hN p => exp hN p y) w w‖ = ‖(w : V)‖ := by
  have h := gauss_lemma_expDomAt hw w
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- **Lifts through `exp_p` do not escape to infinity** (what makes the pulled-back metric on
`T_pN` complete): if `Γ` lifts the smooth curve `c` through `exp_p` on `[0, T]` and `‖c'‖ ≤ L`
there, then `‖Γ(t)‖ ≤ ‖Γ(0)‖ + 1 + L t`.  By the Gauss lemma the radial part of `Γ'` is at most
`‖c'‖`: `⟨Γ, Γ'⟩ = ⟨d(exp_p)_Γ(Γ), d(exp_p)_Γ(Γ')⟩ = ⟨d(exp_p)_Γ(Γ), c'⟩`, so
`ψ = √(‖Γ‖² + 1)` has `|ψ'| ≤ L`. -/
theorem norm_expLift_le (hc : IsGeodesicallyComplete hN) {p : N}
    (hcrit : ∀ v, Injective (dExpAt hN p v)) {c : ℝ → V} (hcs : ContDiff ℝ ∞ c)
    (hcN : ∀ t, c t ∈ N) {L T : ℝ} (hL : ∀ t ∈ Icc 0 T, ‖deriv c t‖ ≤ L)
    {Γ : ℝ → tangentSubspace hN p} (hΓ : ContinuousOn Γ (Icc 0 T))
    (hlift : ∀ t ∈ Icc 0 T, exp hN p (Γ t) = c t) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖Γ t‖ ≤ ‖Γ 0‖ + 1 + L * t := by
  set ψ : ℝ → ℝ := fun s => √(‖Γ s‖ ^ 2 + 1) with hψ_def
  have hψpos : ∀ s, 0 < ‖Γ s‖ ^ 2 + 1 := fun s => by positivity
  have hψc : ContinuousOn ψ (Icc 0 T) :=
    ((hΓ.norm.pow 2).add continuousOn_const).sqrt
  -- the derivative of `ψ` in the interior
  have hderiv : ∀ s ∈ Ioo 0 T, ∃ d, HasDerivAt ψ d s ∧ d ≤ L := by
    intro s hs
    have hnhds : Icc 0 T ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
    have hΓs : ContinuousAt Γ s := hΓ.continuousAt hnhds
    have hev : ∀ᶠ t in 𝓝 s, exp hN p (Γ t) = c t :=
      eventually_of_mem hnhds hlift
    obtain ⟨Γ', hΓ', hD⟩ := hasDerivAt_expLift hc hcrit hcs hcN hΓs hev
    have h1 : HasDerivAt (fun s => ‖Γ s‖ ^ 2 + 1) (2 * ⟪Γ s, Γ'⟫) s := by
      simpa using hΓ'.norm_sq.add_const 1
    have h2 := h1.sqrt (hψpos s).ne'
    refine ⟨_, h2, ?_⟩
    -- the Gauss lemma bounds the radial derivative
    have hdom : Γ s ∈ expDomAt hN p := hc p _ (Γ s).2
    have hG := gauss_lemma_expDomAt hdom Γ'
    rw [hD] at hG
    have hin : ⟪Γ s, Γ'⟫ = ⟪fderiv ℝ (fun y : tangentSubspace hN p => exp hN p y) (Γ s) (Γ s),
        deriv c s⟫ := by
      rw [Submodule.coe_inner, hG]
    have hb : |⟪Γ s, Γ'⟫| ≤ ‖Γ s‖ * L := by
      rw [hin]
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [norm_fderiv_expAt_self hdom, Submodule.norm_coe]
      exact mul_le_mul_of_nonneg_left (hL s (Ioo_subset_Icc_self hs)) (norm_nonneg _)
    have hψs : ‖Γ s‖ ≤ ψ s := by
      rw [hψ_def]
      exact Real.le_sqrt_of_sq_le (by linarith)
    have hψs0 : 0 < ψ s := Real.sqrt_pos.2 (hψpos s)
    have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL s (Ioo_subset_Icc_self hs))
    rw [div_le_iff₀ (by positivity)]
    have : ⟪Γ s, Γ'⟫ ≤ ‖Γ s‖ * L := (le_abs_self _).trans hb
    nlinarith
  -- the mean value theorem
  have hmvt := (convex_Icc (0 : ℝ) T).image_sub_le_mul_sub_of_deriv_le hψc
    (fun s hs => by
      rw [interior_Icc] at hs
      obtain ⟨d, hd, -⟩ := hderiv s hs
      exact hd.differentiableAt.differentiableWithinAt)
    (C := L) (fun s hs => by
      rw [interior_Icc] at hs
      obtain ⟨d, hd, hdL⟩ := hderiv s hs
      rw [hd.deriv]
      exact hdL) 0 ⟨le_rfl, ht.1.trans ht.2⟩ t ht ht.1
  have h0 : ψ 0 ≤ ‖Γ 0‖ + 1 := by
    rw [hψ_def, Real.sqrt_le_left (by positivity)]
    nlinarith [norm_nonneg (Γ 0)]
  have ht' : ‖Γ t‖ ≤ ψ t := Real.le_sqrt_of_sq_le (by linarith)
  linarith

/-- `exp_p` is continuous on `T_pN` when `N` is complete. -/
theorem continuous_expAt (hc : IsGeodesicallyComplete hN) (p : N) :
    Continuous (fun y : tangentSubspace hN p => exp hN p y) :=
  continuous_iff_continuousAt.2 fun y => (contDiffAt_expAt (hc p _ y.2)).continuousAt

/-- **Path lifting through `exp_p`**, for smooth curves: if `N` is complete and `exp_p` is
nowhere critical, every smooth curve `c` in `N` lifts through `exp_p` on `[0, 1]` from any point
`v₀` over `c(0)`.  The set of times up to which a lift exists is closed: lifts stay bounded
(`Morse.norm_expLift_le`), so they accumulate at some `w` over the supremal time, and `exp_p` is a
local diffeomorphism near `w`. -/
theorem exists_expLift (hc : IsGeodesicallyComplete hN) {p : N}
    (hcrit : ∀ v, Injective (dExpAt hN p v)) {c : ℝ → V} (hcs : ContDiff ℝ ∞ c)
    (hcN : ∀ t, c t ∈ N) {v₀ : tangentSubspace hN p} (hv₀ : exp hN p v₀ = c 0) :
    ∃ Γ : ℝ → tangentSubspace hN p, ContinuousOn Γ (Icc 0 1) ∧ Γ 0 = v₀ ∧
      ∀ t ∈ Icc (0 : ℝ) 1, exp hN p (Γ t) = c t := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  have hloc := isLocalDiffeomorph_expToN hc hcrit
  -- a bound for the speed of `c` on `[0, 1]`
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hcs.continuous_deriv (by simp)).continuousOn (s := Icc (0 : ℝ) 1))
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0 ⟨le_rfl, zero_le_one⟩)
  set P : ℝ → Prop := fun T => ∃ Γ : ℝ → tangentSubspace hN p, ContinuousOn Γ (Icc 0 T) ∧
    Γ 0 = v₀ ∧ ∀ t ∈ Icc 0 T, exp hN p (Γ t) = c t with hP_def
  set S : Set ℝ := {T | T ∈ Icc (0 : ℝ) 1 ∧ P T} with hS_def
  have hS0 : (0 : ℝ) ∈ S := ⟨⟨le_rfl, zero_le_one⟩, fun _ => v₀, continuousOn_const, rfl,
    fun t ht => by rw [show t = 0 from le_antisymm ht.2 ht.1]; exact hv₀⟩
  have hSb : BddAbove S := ⟨1, fun T hT => hT.1.2⟩
  set T₀ := sSup S with hT₀_def
  have hT₀0 : 0 ≤ T₀ := le_csSup hSb hS0
  obtain ⟨u, -, hu, huS⟩ := exists_seq_tendsto_sSup ⟨0, hS0⟩ hSb
  choose Γ hΓc hΓ0 hΓl using fun n => (huS n).2
  -- the lifts at the times `u n` are bounded
  have hbd : ∀ n, Γ n (u n) ∈ closedBall (0 : tangentSubspace hN p) (‖v₀‖ + 1 + L) := by
    intro n
    have hun := (huS n).1
    have h := norm_expLift_le hc hcrit hcs hcN (L := L) (T := u n)
      (fun t ht => hL t ⟨ht.1, ht.2.trans hun.2⟩) (hΓc n) (hΓl n) ⟨hun.1, le_rfl⟩
    rw [hΓ0 n] at h
    rw [mem_closedBall, dist_zero_right]
    nlinarith [hun.1, hun.2]
  obtain ⟨w, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded isBounded_closedBall hbd
  -- `exp_p(w) = c(T₀)`
  have hut : Tendsto (fun k => u (φ k)) atTop (𝓝 T₀) := hu.comp hφ.tendsto_atTop
  have hw : exp hN p w = c T₀ := by
    have h1 : Tendsto (fun k => exp hN p (Γ (φ k) (u (φ k)))) atTop (𝓝 (exp hN p w)) :=
      ((continuous_expAt hc p).tendsto w).comp hlim
    have h3 : (fun k => exp hN p (Γ (φ k) (u (φ k)))) = fun k => c (u (φ k)) := by
      funext k; exact hΓl (φ k) (u (φ k)) ⟨(huS _).1.1, le_rfl⟩
    rw [h3] at h1
    exact tendsto_nhds_unique h1 ((hcs.continuous.tendsto T₀).comp hut)
  -- the local diffeomorphism at `w`
  obtain ⟨Φ, hΦs, hΦf⟩ := hloc w
  set cN : ℝ → N := fun t => ⟨c t, hcN t⟩ with hcN_def
  have hcNc : Continuous cN := hcs.continuous.subtype_mk _
  have hfw : expToN hN p w = cN T₀ := Subtype.ext ((coe_expToN_of_mem (hc p _ w.2)).trans hw)
  have htgt : cN T₀ ∈ Φ.target := by
    rw [← hfw, hΦf hΦs]; exact Φ.toPartialEquiv.map_source hΦs
  obtain ⟨η, hη, hηt⟩ := Metric.isOpen_iff.1 (Φ.open_target.preimage hcNc) T₀ htgt
  -- a lift reaching `Φ.source`, at a time `a > T₀ - η`
  have hev1 : ∀ᶠ k in atTop, Γ (φ k) (u (φ k)) ∈ Φ.source :=
    hlim.eventually (Φ.open_source.mem_nhds hΦs)
  have hev2 : ∀ᶠ k in atTop, T₀ - η < u (φ k) := hut.eventually (lt_mem_nhds (by linarith))
  obtain ⟨k, hk1, hk2⟩ := (hev1.and hev2).exists
  set a := u (φ k) with ha_def
  have haS := huS (φ k)
  have haT₀ : a ≤ T₀ := le_csSup hSb haS
  -- extend it by `Φ⁻¹ ∘ c` up to `T₁ = min 1 (T₀ + η / 2)`
  set T₁ := min 1 (T₀ + η / 2) with hT₁_def
  have hT₁a : a ≤ T₁ := le_min haS.1.2 (by linarith)
  have hmem : ∀ t, a ≤ t → t ≤ T₁ → cN t ∈ Φ.target := fun t h1 h2 => by
    have h3 := min_le_right 1 (T₀ + η / 2)
    apply hηt
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hlinv : ∀ t, a ≤ t → t ≤ T₁ → expToN hN p (Φ.symm (cN t)) = cN t := fun t h1 h2 => by
    have htg := hmem t h1 h2
    have e : Φ.symm (cN t) = Φ.toPartialEquiv.symm (cN t) := rfl
    rw [e, hΦf (Φ.toPartialEquiv.map_target htg)]
    exact Φ.toPartialEquiv.right_inv htg
  have hT₁S : T₁ ∈ S := by
    refine ⟨⟨haS.1.1.trans hT₁a, min_le_left _ _⟩,
      fun t => if t ≤ a then Γ (φ k) t else Φ.symm (cN t), ?_, ?_, ?_⟩
    · refine ContinuousOn.if ?_ ?_ ?_
      · intro t ht
        have hta : t = a := by
          have := ht.2
          rwa [show {t : ℝ | t ≤ a} = Iic a from rfl, frontier_Iic, mem_singleton_iff] at this
        rw [hta]
        have h1 : expToN hN p (Γ (φ k) a) = cN a :=
          Subtype.ext ((coe_expToN_of_mem (hc p _ (Γ (φ k) a).2)).trans
            (hΓl (φ k) a ⟨haS.1.1, le_rfl⟩))
        rw [← h1, hΦf hk1]
        exact (Φ.toPartialEquiv.left_inv hk1).symm
      · refine (hΓc (φ k)).mono fun t ht => ⟨ht.1.1, ?_⟩
        have := ht.2
        rwa [show {t : ℝ | t ≤ a} = Iic a from rfl, closure_Iic] at this
      · have hsub : Icc 0 T₁ ∩ closure {t : ℝ | ¬t ≤ a} ⊆ Icc a T₁ := fun t ht => by
          have := ht.2
          rw [show {t : ℝ | ¬t ≤ a} = Ioi a from by ext; simp, closure_Ioi] at this
          exact ⟨this, ht.1.2⟩
        refine (Φ.symm.contMDiffOn.continuousOn.comp hcNc.continuousOn fun t ht => ?_).mono hsub
        exact hmem t ht.1 ht.2
    · have ha0 : 0 ≤ a := haS.1.1
      simp only [if_pos ha0, hΓ0]
    · intro t ht
      by_cases hta : t ≤ a
      · simp only [if_pos hta]; exact hΓl _ t ⟨ht.1, hta⟩
      · simp only [if_neg hta]
        have h := congrArg Subtype.val (hlinv t (le_of_not_ge hta) ht.2)
        rwa [coe_expToN_of_mem (hc p _ (Φ.symm (cN t)).2)] at h
  have hT₁le : T₁ ≤ T₀ := le_csSup hSb hT₁S
  have hT₁1 : T₁ = 1 := by
    rcases min_choice 1 (T₀ + η / 2) with h | h
    · rw [hT₁_def, h]
    · exfalso
      rw [← hT₁_def] at h
      linarith
  rw [hT₁1] at hT₁S
  exact hT₁S.2

/-- **Uniqueness of lifts** through `exp_p`: two lifts on `[0, 1]` of the same curve which agree
at one time agree on `[0, 1]` (`exp_p` is a local homeomorphism and `T_pN` is Hausdorff). -/
theorem expLift_unique (hc : IsGeodesicallyComplete hN) {p : N}
    (hcrit : ∀ v, Injective (dExpAt hN p v)) {Γ₁ Γ₂ : ℝ → tangentSubspace hN p}
    (h₁ : ContinuousOn Γ₁ (Icc 0 1)) (h₂ : ContinuousOn Γ₂ (Icc 0 1))
    (he : ∀ t ∈ Icc (0 : ℝ) 1, exp hN p (Γ₁ t) = exp hN p (Γ₂ t)) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (h0 : Γ₁ t₀ = Γ₂ t₀) : EqOn Γ₁ Γ₂ (Icc 0 1) := by
  let _ := hN.chartedSpace
  have hloc := (isLocalDiffeomorph_expToN hc hcrit).isLocalHomeomorph
  refine (T2Space.isSeparatedMap (expToN hN p)).eqOn_of_comp_eqOn hloc.isLocallyInjective
    isPreconnected_Icc h₁ h₂ (fun t ht => ?_) ht₀ h0
  simp only [comp_apply]
  refine Subtype.ext ?_
  rw [coe_expToN_of_mem (hc p _ (Γ₁ t).2), coe_expToN_of_mem (hc p _ (Γ₂ t).2)]
  exact he t ht

/-! ### `exp_p` is a covering map -/

/-- **`exp_p` is a covering map** `T_pN → N` when `N` is complete and `exp_p` is nowhere
critical.  Over a normal ball `B` about `q`, the sheets are the images of the sections obtained by
lifting the radial geodesics `t ↦ exp_q(t G(y))`, `y ∈ B`, from the points of the fibre over `q`
(continuous in `y` by the homotopy lifting lemma for local homeomorphisms); every point over `B`
lies on a sheet (lift the radial geodesic backwards), and two sheets which meet coincide
(uniqueness of lifts). -/
theorem isCoveringMap_expToN (hc : IsGeodesicallyComplete hN) {p : N}
    (hcrit : ∀ v, Injective (dExpAt hN p v)) : IsCoveringMap (expToN hN p) := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  set f := expToN hN p with hf_def
  have hloc := (isLocalDiffeomorph_expToN hc hcrit).isLocalHomeomorph
  have hfc : Continuous f := hloc.continuous
  have hfexp : ∀ y, (f y : V) = exp hN p y := fun y => coe_expToN_of_mem (hc p _ y.2)
  intro q
  obtain ⟨ε, hε, ⟨nc⟩⟩ := exists_isNormalRadius hN q
  -- the normal ball `B` about `q`
  set B : Set N := {y | (y : V) ∈ nc.U} with hB_def
  have hBo : IsOpen B := nc.isOpen_U.preimage continuous_subtype_val
  have hqB : q ∈ B := by
    have := nc.exp_mem_U 0 (Submodule.zero_mem _) (by simpa using hε)
    rwa [exp_zero q.2] at this
  -- radial coordinates on `B`, and the radial geodesics `ρ y`
  have hlgT : ∀ y : B, nc.G y ∈ tangentSubspace hN q := fun y => nc.G_mem _ y.2 y.1.2
  set lg : B → tangentSubspace hN q := fun y => ⟨nc.G y, hlgT y⟩ with hlg_def
  have hlgc : Continuous lg := by
    refine Continuous.subtype_mk ?_ _
    exact nc.contDiffOn_G.continuousOn.comp_continuous (continuous_subtype_val.comp
      continuous_subtype_val) fun y => y.2
  set ρ : B → ℝ → V := fun y t => exp hN q (t • (lg y : V)) with hρ_def
  have hρgeo : ∀ y, IsGeodesicOn hN (ρ y) univ := fun y =>
    isGeodesicOn_univ_exp_smul (hc q) (lg y).2
  have hρs : ∀ y, ContDiff ℝ ∞ (ρ y) := fun y => contDiffOn_univ.1 (hρgeo y).contDiffOn
  have hρN : ∀ y t, ρ y t ∈ N := fun y t => (hρgeo y).mem t (mem_univ t)
  have hρ0 : ∀ y, ρ y 0 = q := fun y => by simp [hρ_def, exp_zero q.2]
  have hρ1 : ∀ y, ρ y 1 = y := fun y => by
    simp only [hρ_def, hlg_def, one_smul]
    exact nc.exp_G _ y.2 y.1.2
  -- the lifts of the radial geodesics from the points of the fibre over `q`
  have hlift : ∀ (e : f ⁻¹' {q}) (y : B), ∃ Γ : ℝ → tangentSubspace hN p,
      ContinuousOn Γ (Icc 0 1) ∧ Γ 0 = e ∧ ∀ t ∈ Icc (0 : ℝ) 1, exp hN p (Γ t) = ρ y t :=
    fun e y => exists_expLift hc hcrit (hρs y) (hρN y) (by
      rw [hρ0, ← hfexp, show f e = q from e.2])
  choose Γ hΓc hΓ0 hΓl using hlift
  -- uniqueness of these lifts
  have huniq : ∀ (y : B) (Γ₁ Γ₂ : ℝ → tangentSubspace hN p), ContinuousOn Γ₁ (Icc 0 1) →
      ContinuousOn Γ₂ (Icc 0 1) → (∀ t ∈ Icc (0 : ℝ) 1, exp hN p (Γ₁ t) = ρ y t) →
      (∀ t ∈ Icc (0 : ℝ) 1, exp hN p (Γ₂ t) = ρ y t) → ∀ t₀ ∈ Icc (0 : ℝ) 1, Γ₁ t₀ = Γ₂ t₀ →
      EqOn Γ₁ Γ₂ (Icc 0 1) := fun y Γ₁ Γ₂ h₁ h₂ hl₁ hl₂ t₀ ht₀ h0 =>
    expLift_unique hc hcrit h₁ h₂ (fun t ht => (hl₁ t ht).trans (hl₂ t ht).symm) ht₀ h0
  -- the sections `sec e : B → T_pN` are continuous (homotopy lifting for local homeomorphisms)
  set H : C(I × B, N) := ⟨fun x => ⟨ρ x.2 x.1, hρN _ _⟩, by
    refine Continuous.subtype_mk ?_ _
    have h1 : Continuous fun x : I × B => (x.1 : ℝ) • lg x.2 :=
      (continuous_subtype_val.comp continuous_fst).smul (hlgc.comp continuous_snd)
    exact (continuous_expAt hc q).comp h1⟩ with hH_def
  have hgc : ∀ e, Continuous fun x : I × B => Γ e x.2 x.1 := by
    intro e
    refine hloc.continuous_lift (T2Space.isSeparatedMap _) H (g := fun x : I × B => Γ e x.2 x.1)
      ?_ ?_ ?_
    · funext x
      exact Subtype.ext ((hfexp _).trans (hΓl e x.2 x.1 x.1.2))
    · simp only [Set.Icc.coe_zero, hΓ0]
      exact continuous_const
    · intro y
      exact (hΓc e y).comp_continuous continuous_subtype_val fun s => s.2
  set sec : f ⁻¹' {q} → B → tangentSubspace hN p := fun e y => Γ e y 1 with hsec_def
  have hsecc : ∀ e, Continuous (sec e) := fun e =>
    (hgc e).comp (continuous_const (y := (1 : I)).prodMk continuous_id)
  have hfsec : ∀ e y, f (sec e y) = y := fun e y =>
    Subtype.ext ((hfexp _).trans ((hΓl e y 1 ⟨zero_le_one, le_rfl⟩).trans (hρ1 y)))
  -- every point over `B` lies on a sheet: lift the radial geodesic backwards
  have hexh : ∀ y : tangentSubspace hN p, (hy : f y ∈ B) →
      ∃ e : f ⁻¹' {q}, sec e ⟨f y, hy⟩ = y := by
    intro y hy
    set z : B := ⟨f y, hy⟩
    set r : ℝ → V := fun t => ρ z (1 - t) with hr_def
    have hrs : ContDiff ℝ ∞ r := (hρs z).comp (contDiff_const.sub contDiff_id)
    obtain ⟨Γr, hΓrc, hΓr0, hΓrl⟩ := exists_expLift hc hcrit hrs (fun t => hρN z (1 - t))
      (v₀ := y) (by simp only [hr_def, sub_zero, hρ1]; exact (hfexp y).symm)
    have he : f (Γr 1) = q := Subtype.ext ((hfexp _).trans (by
      rw [hΓrl 1 ⟨zero_le_one, le_rfl⟩]
      simp only [hr_def, sub_self, hρ0]))
    refine ⟨⟨Γr 1, he⟩, ?_⟩
    have hmaps : MapsTo (fun t : ℝ => 1 - t) (Icc 0 1) (Icc 0 1) := fun t ht =>
      ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hrev : ContinuousOn (fun t => Γr (1 - t)) (Icc 0 1) :=
      hΓrc.comp (continuous_const.sub continuous_id).continuousOn hmaps
    have hEq := huniq z _ _ (hΓc ⟨Γr 1, he⟩ z) hrev (hΓl ⟨Γr 1, he⟩ z)
      (fun t ht => by
        rw [hΓrl (1 - t) (hmaps ht)]
        simp only [hr_def, sub_sub_cancel]) 0 ⟨le_rfl, zero_le_one⟩
      (by rw [hΓ0]; simp)
    have h1 := hEq ⟨zero_le_one, le_rfl⟩
    simp only [sub_self] at h1
    rw [hΓr0] at h1
    exact h1
  -- the fibre over `q` is discrete
  have hdisc : DiscreteTopology (f ⁻¹' {q}) := by
    rw [discreteTopology_iff_locallyInjective q]
    have h := hloc.isLocallyInjective.comp_right continuous_subtype_val
      (Subtype.val_injective (p := fun y => y ∈ f ⁻¹' {q}))
    have e : (f ∘ Subtype.val : f ⁻¹' {q} → N) = fun _ => q := funext fun y => y.2
    rwa [e] at h
  -- an empty fibre: nothing lies over `B`
  rcases isEmpty_or_nonempty (f ⁻¹' {q}) with hemp | hne
  · refine IsEvenlyCovered.of_preimage_eq_empty _ (hBo.mem_nhds hqB) ?_
    refine eq_empty_of_forall_notMem fun y hy => ?_
    obtain ⟨e, -⟩ := hexh y hy
    exact hemp.false e
  -- the sheets `sec e (B)`
  set U : f ⁻¹' {q} → Set (tangentSubspace hN p) := fun e => range (sec e) with hU_def
  have hUo : ∀ e, IsOpen (U e) := by
    intro e
    refine isOpen_iff_mem_nhds.2 ?_
    rintro _ ⟨z₀, rfl⟩
    obtain ⟨φ, hφs, hφf⟩ := hloc (sec e z₀)
    set Q : Set B := sec e ⁻¹' φ.source with hQ_def
    have hQ : IsOpen Q := φ.open_source.preimage (hsecc e)
    have hQ' : IsOpen (Subtype.val '' Q : Set N) := hBo.isOpenMap_subtype_val Q hQ
    refine Filter.mem_of_superset ((φ.open_source.inter (hQ'.preimage hfc)).mem_nhds
      ⟨hφs, z₀, hφs, (hfsec e z₀).symm⟩) ?_
    rintro y ⟨hy, z, hz, hzy⟩
    refine ⟨z, φ.injOn hz hy ?_⟩
    rw [← hφf]
    change f (sec e z) = f y
    rw [hfsec e z, hzy]
  have hinj : ∀ e, InjOn f (U e) := by
    rintro e _ ⟨z₁, rfl⟩ _ ⟨z₂, rfl⟩ h
    rw [hfsec, hfsec] at h
    rw [Subtype.ext h]
  have hsurj : ∀ e, SurjOn f (U e) B := fun e z hz => ⟨sec e ⟨z, hz⟩, ⟨_, rfl⟩, hfsec e _⟩
  have hdisj : Pairwise (Disjoint on U) := by
    intro e₁ e₂ hne'
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨z₁, rfl⟩ ⟨z₂, h⟩
    have hz : z₂ = z₁ := by
      have := congrArg f h
      rw [hfsec, hfsec] at this
      exact Subtype.ext this
    subst hz
    have hEq := huniq z₂ _ _ (hΓc e₁ z₂) (hΓc e₂ z₂) (hΓl e₁ z₂) (hΓl e₂ z₂) 1
      ⟨zero_le_one, le_rfl⟩ h.symm
    have h0 := hEq ⟨le_rfl, zero_le_one⟩
    rw [hΓ0, hΓ0] at h0
    exact hne' (Subtype.ext h0)
  have hexh' : f ⁻¹' B ⊆ ⋃ e, U e := fun y hy => by
    obtain ⟨e, he⟩ := hexh y hy
    exact mem_iUnion.2 ⟨e, ⟨_, he⟩⟩
  have hopen_iff : ∀ e {W : Set N}, W ⊆ B → (IsOpen W ↔ IsOpen (f ⁻¹' W ∩ U e)) := by
    intro e W hWB
    constructor
    · intro hW
      exact (hW.preimage hfc).inter (hUo e)
    · intro hW
      have heq : W = f '' (f ⁻¹' W ∩ U e) := by
        refine Subset.antisymm (fun z hz => ?_) ?_
        · exact ⟨sec e ⟨z, hWB hz⟩, ⟨by rw [mem_preimage, hfsec]; exact hz, _, rfl⟩,
            hfsec e _⟩
        · rintro _ ⟨y, hy, rfl⟩
          exact hy.1
      rw [heq]
      exact hloc.isOpenMap _ hW
  exact IsEvenlyCovered.of_trivialization
    (t := hBo.trivializationDiscrete U B hopen_iff hinj hsurj hdisj hexh') hqB

end Morse
