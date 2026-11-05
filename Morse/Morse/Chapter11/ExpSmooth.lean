import Morse.Chapter9.GeodesicVariation
import Morse.Chapter7.HopfRinow

/-!
Milnor, *Morse Theory*, §18, pp. 98–99: Theorem 18.1 (conjugate points are the critical points of
the exponential map), with the smoothness of `exp` on its whole domain on which it rests, for a
submanifold `N ⊆ ℝᴷ` with the induced metric.

# The exponential map is smooth on its domain; Theorem 18.1

## Milnor's text, paraphrased

* (p. 98) A smooth map between manifolds of the same dimension is *critical* at a point if its
  differential there is not one-to-one.  This is applied to `exp = exp_p : TM_p → M`, `TM_p`
  regarded as a manifold.  Milnor assumes `M` complete, so that `exp` is defined everywhere, and
  remarks that this assumption could easily be removed.
* **Theorem 18.1** (p. 98): `exp v` is conjugate to `p` along `γ_v(t) = exp(tv)` iff `exp` is
  critical at `v`.  Proof: for `X ≠ 0` in the kernel of `exp_*` at `v`, choose a path `v(u)` with
  `v(0) = v`, `v'(0) = X`; then `α(u, t) = exp(t v(u))` is a variation through geodesics, so its
  variation field `W` is a Jacobi field (Lemma 14.3) with `W(0) = 0`, `W(1) = exp_* X = 0` and
  `DW/dt(0) = D/∂u v(u) ≠ 0`.  Conversely (p. 99), if `exp_*` is non-singular at `v`, the fields
  `W_1, …, W_n` built from a basis `X_1, …, X_n` vanish at `p` and their values `exp_*(X_i)` at
  `exp v` are independent; as the Jacobi fields vanishing at `p` form an `n`-dimensional space, no
  non-trivial one vanishes at `exp v` as well.

## In the embedded setting

* `Morse.exists_contDiffOn_exp`: **`exp` is smooth on its whole domain**: near every `(p, v)` of
  `Morse.expDom` it is the restriction to `TN` of a smooth map on an open set of `V × V`, and the
  domain is open in `TN` (`Morse.exists_isOpen_expDom`); `Morse.contMDiffOn_exp_expDom` is the
  same statement for the manifold structure of `TN`.  (Chapter 7 gives smoothness only near the
  zero section, `Morse.contMDiffOn_exp`, and continuity on the whole domain.)  The proof continues
  geodesics step by step with the local smooth flow, as in the proof of Lemma 14.4
  (`Morse.raysGood_of_isGeodesicOn`), now for initial data depending smoothly on a parameter in
  any normed space (`Morse.raysGoodE_of_isGeodesicOn`), applied to the data `(r(y), P_{r(y)} w)`
  where `r` is a smooth local retraction onto `N` (`Morse.exists_retraction`).
* `Morse.expDomAt hN q ⊆ T_qN`: the domain of `exp_q`, open (`Morse.isOpen_expDomAt`) and
  star-shaped (`Morse.smul_mem_expDomAt`); `exp_q` is smooth on it (`Morse.contDiffOn_expAt`), and
  `Morse.dExpAt hN q v`, its derivative at `v`, is Milnor's `exp_*` at `v`.
* `Morse.expJacobi hN q v X`: the variation field `W_X(t) = t d(exp_q)_{tv}(X)` of
  `α(u, t) = exp_q(t(v + uX))`, a Jacobi field along `γ_v` (`Morse.isJacobiField_expJacobi`) with
  `W_X(0) = 0`, `DW_X/dt(0) = X` (`Morse.covAlong_expJacobi_zero`) and `W_X(1) = d(exp_q)_v X`.
* `Morse.conjSpace_eq_map_ker`: **the Jacobi fields along `γ_v` vanishing at `0` and `1` are the
  `W_X` with `X ∈ ker d(exp_q)_v`**, and `X ↦ W_X` is injective (`Morse.expJacobi_injective`);
  `Morse.theorem_18_1_multiplicity`: **the multiplicity of `exp_q(v)` as a conjugate point equals
  the nullity of `d(exp_q)_v`**; `Morse.theorem_18_1`: **Theorem 18.1**.

## What Milnor leaves implicit

* **`exp_p` is treated as a smooth map on all of `TM_p`.**  §10 gives smoothness only near the zero
  section (Lemma 10.2).  Smoothness on the whole domain is the smooth dependence of geodesics on
  their initial data over a compact time interval, proved here as `Morse.exists_contDiffOn_exp`.
* **Completeness is not needed**, as Milnor says: what replaces it is that the domain of `exp_p` is
  open and star-shaped, which is part of the same dependence theorem.
* **`DW/dt(0) = D/∂u v(u) ≠ 0`**, the step Milnor passes over: here `W_X(t) = t d(exp_q)_{tv}(X)`,
  so `DW_X/dt(0) = d(exp_q)_0(X) = X` by `d(exp_q)₀ = id` (`Morse.hasFDerivAt_exp_zero`); this
  replaces the symmetry lemma and the covariant derivative along the constant curve
  `u ↦ α(u, 0) = p`.
* **The variation must be smooth on a box `(−ε, ε) × [0, 1]`**: the segment `{tv : 0 ≤ t ≤ 1}` is
  compact and lies in the open domain of `exp_p`, so a box around it does (the tube lemma).
  Milnor's path `v(u)` is taken to be the straight line `v + uX`.
* "**Clearly** no non-trivial Jacobi field vanishes at both `p` and `exp v`": this is the statement
  that `X ↦ W_X` maps `TM_p` isomorphically onto the `n`-dimensional space of Jacobi fields
  vanishing at `0` (a Jacobi field is determined by `J(0)` and `DJ/dt(0)`, Corollary 14.B of the
  exposition); it also gives the equality of the multiplicity with the nullity of `exp_*`, which
  Milnor does not state.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

/-! ### The time derivative on `E × ℝ` -/

section TimeDeriv

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The partial derivative `∂G/∂t` of a map `G : E × ℝ → F`. -/
def partialT (G : E × ℝ → F) (p : E × ℝ) : F := fderiv ℝ G p ((0 : E), (1 : ℝ))

theorem hasDerivAt_partialT {G : E × ℝ → F} {p : E × ℝ} (h : DifferentiableAt ℝ G p) :
    HasDerivAt (fun t => G (p.1, t)) (partialT G p) p.2 := by
  have hl : HasDerivAt (fun t : ℝ => (p.1, t)) ((0 : E), (1 : ℝ)) p.2 :=
    (hasDerivAt_const _ _).prodMk (hasDerivAt_id _)
  exact h.hasFDerivAt.comp_hasDerivAt p.2 hl

theorem contDiffOn_partialT {G : E × ℝ → F} {O : Set (E × ℝ)} (hO : IsOpen O)
    (hG : ContDiffOn ℝ ∞ G O) : ContDiffOn ℝ ∞ (partialT G) O :=
  (hG.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const

end TimeDeriv

/-! ### Smooth dependence of radial geodesics on parameters in a normed space -/

section RaysE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable (hN) in
/-- The radial geodesics `t ↦ exp_{c(u)}(t w(u))` of a family of initial data with parameter
`u ∈ E`, as a function of `(u, t)`. -/
def raysE (c w : E → V) (p : E × ℝ) : V := exp hN (c p.1) (p.2 • w p.1)

variable (hN) in
/-- The radial geodesics of the data `(c(u), w(u))`, `u` in the ball of radius `ε` about `u₀`,
exist on `(−η, b + η)` and depend smoothly on `(u, t)` there. -/
def RaysGoodE (c w : E → V) (U₀ : Set E) (u₀ : E) (b : ℝ) : Prop :=
  ∃ ε > 0, ∃ η > 0, ball u₀ ε ⊆ U₀ ∧
    ContDiffOn ℝ ∞ (raysE hN c w) (ball u₀ ε ×ˢ Ioo (-η) (b + η)) ∧
    ∀ u ∈ ball u₀ ε, IsGeodesicOn hN (fun t => exp hN (c u) (t • w u)) (Ioo (-η) (b + η))

variable {c w : E → V} {U₀ : Set E} {u₀ : E} (hU₀ : IsOpen U₀) (hu₀ : u₀ ∈ U₀)
  (hcs : ContDiffOn ℝ ∞ c U₀) (hws : ContDiffOn ℝ ∞ w U₀) (hcN : ∀ u ∈ U₀, c u ∈ N)
  (hwT : ∀ u ∈ U₀, prj hN (c u) (w u) = w u)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem RaysGoodE.mono {b b' : ℝ} (h : RaysGoodE hN c w U₀ u₀ b) (hb' : b' ≤ b) :
    RaysGoodE hN c w U₀ u₀ b' := by
  obtain ⟨ε, hε, η, hη, hsub, hsm, hgeo⟩ := h
  have hI : Ioo (-η) (b' + η) ⊆ Ioo (-η) (b + η) := Ioo_subset_Ioo le_rfl (by linarith)
  exact ⟨ε, hε, η, hη, hsub, hsm.mono (prod_mono subset_rfl hI),
    fun u hu => (hgeo u hu).mono isOpen_Ioo hI⟩

include hU₀ hu₀ hcs hws hcN hwT in
/-- The start: near `t = 0`, the local smooth flow. -/
theorem raysGoodE_zero : RaysGoodE hN c w U₀ u₀ 0 := by
  obtain ⟨U₁, hU₁, hx, h, hh, Φ, hΦ, hloc⟩ := exists_smooth_ray hN ⟨c u₀, hcN u₀ hu₀⟩
    (R := ‖w u₀‖ + 1) (by positivity)
  have hcont : ContinuousAt (fun u => (c u, w u)) u₀ :=
    (hcs.prodMk hws).continuousOn.continuousAt (hU₀.mem_nhds hu₀)
  have hev : ∀ᶠ u in 𝓝 u₀, u ∈ U₀ ∧ c u ∈ U₁ ∧ ‖w u‖ < ‖w u₀‖ + 1 := by
    have h1 := hcont.eventually ((hU₁.prod (isOpen_lt continuous_norm continuous_const)).mem_nhds
      (show (c u₀, w u₀) ∈ U₁ ×ˢ {x : V | ‖x‖ < ‖w u₀‖ + 1} from ⟨hx, by simp⟩))
    filter_upwards [hU₀.mem_nhds hu₀, h1] with u hu h1u using ⟨hu, h1u.1, h1u.2⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hI : Ioo (-(h / 2)) (0 + h / 2) ⊆ Ioo (-h) h :=
    Ioo_subset_Ioo (by linarith) (by linarith)
  refine ⟨ε, hε, h / 2, by positivity, fun u hu => (hball u hu).1, ?_, fun u hu => ?_⟩
  · have hmaps : MapsTo (fun p : E × ℝ => (c p.1, w p.1, p.2))
        (ball u₀ ε ×ˢ Ioo (-(h / 2)) (0 + h / 2))
        (U₁ ×ˢ ball (0 : V) (‖w u₀‖ + 1) ×ˢ Ioo (-h) h) :=
      fun p hp => ⟨(hball p.1 hp.1).2.1, mem_ball_zero_iff.2 (hball p.1 hp.1).2.2, hI hp.2⟩
    have hinner : ContDiffOn ℝ ∞ (fun p : E × ℝ => (c p.1, w p.1, p.2))
        (ball u₀ ε ×ˢ Ioo (-(h / 2)) (0 + h / 2)) :=
      ((hcs.comp contDiffOn_fst fun p hp => (hball p.1 hp.1).1).prodMk
        ((hws.comp contDiffOn_fst fun p hp => (hball p.1 hp.1).1).prodMk contDiffOn_snd))
    refine (hΦ.comp hinner hmaps).congr fun p hp => ?_
    have hu := hball p.1 hp.1
    exact ((hloc ⟨c p.1, hcN p.1 hu.1⟩ hu.2.1 (w p.1)
      ((prj_eq_self_iff hN (hcN p.1 hu.1)).1 (hwT p.1 hu.1)) hu.2.2).2 p.2 (hI hp.2))
  · have hu' := hball u hu
    exact (hloc ⟨c u, hcN u hu'.1⟩ hu'.2.1 (w u) ((prj_eq_self_iff hN (hcN u hu'.1)).1
      (hwT u hu'.1)) hu'.2.2).1.mono isOpen_Ioo hI

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- The velocity of the ray of `(c(u), w(u))` at time `t` is `∂/∂t` of `raysE`. -/
theorem deriv_raysE_eq {O : Set (E × ℝ)} (hO : IsOpen O) (hsm : ContDiffOn ℝ ∞ (raysE hN c w) O)
    {p : E × ℝ} (hp : p ∈ O) :
    deriv (fun t => exp hN (c p.1) (t • w p.1)) p.2 = partialT (raysE hN c w) p :=
  (hasDerivAt_partialT ((hsm.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp))).deriv

include hcN hwT in
/-- **One step**, as `Morse.RaysGood.step`: the rays continue by a local smooth flow `Φ`. -/
theorem RaysGoodE.step {b : ℝ} (hb : 0 ≤ b) (hgood : RaysGoodE hN c w U₀ u₀ b) {U₁ : Set V}
    (hU₁ : IsOpen U₁) {R h : ℝ} (hh : 0 < h) {Φ : V × V × ℝ → V}
    (hΦ : ContDiffOn ℝ ∞ Φ (U₁ ×ˢ ball (0 : V) R ×ˢ Ioo (-h) h))
    (hloc : ∀ y : N, (y : V) ∈ U₁ → ∀ v ∈ tangentSubspace hN y, ‖v‖ < R →
      IsGeodesicOn hN (fun t => exp hN y (t • v)) (Ioo (-h) h) ∧
      ∀ t ∈ Ioo (-h) h, exp hN y (t • v) = Φ (y, v, t))
    (hb₁ : exp hN (c u₀) (b • w u₀) ∈ U₁)
    (hb₂ : ‖deriv (fun t => exp hN (c u₀) (t • w u₀)) b‖ < R) :
    RaysGoodE hN c w U₀ u₀ (b + h / 2) := by
  obtain ⟨ε, hε, η, hη, hsub, hsm, hgeo⟩ := hgood
  have hO : IsOpen (ball u₀ ε ×ˢ Ioo (-η) (b + η)) := isOpen_ball.prod isOpen_Ioo
  have hbI : b ∈ Ioo (-η) (b + η) := ⟨by linarith, by linarith⟩
  have h0I : (0 : ℝ) ∈ Ioo (-η) (b + η) := ⟨by linarith, by linarith⟩
  have hu₀ε : u₀ ∈ ball u₀ ε := mem_ball_self hε
  -- position and velocity at time `b`, smooth in `u`
  set F : E → V := fun u => raysE hN c w (u, b) with hFdef
  set G : E → V := fun u => partialT (raysE hN c w) (u, b) with hGdef
  have hmapsb : MapsTo (fun u : E => (u, b)) (ball u₀ ε) (ball u₀ ε ×ˢ Ioo (-η) (b + η)) :=
    fun u hu => ⟨hu, hbI⟩
  have hF : ContDiffOn ℝ ∞ F (ball u₀ ε) :=
    hsm.comp (contDiffOn_id.prodMk contDiffOn_const) hmapsb
  have hG : ContDiffOn ℝ ∞ G (ball u₀ ε) :=
    (contDiffOn_partialT hO hsm).comp (contDiffOn_id.prodMk contDiffOn_const) hmapsb
  have hG' : ∀ u ∈ ball u₀ ε, deriv (fun t => exp hN (c u) (t • w u)) b = G u := fun u hu =>
    deriv_raysE_eq hO hsm (hmapsb hu)
  -- for `u` near `u₀`, they stay in the domain of `Φ`
  have hcont : ContinuousAt (fun u => (F u, G u)) u₀ :=
    (hF.prodMk hG).continuousOn.continuousAt (isOpen_ball.mem_nhds hu₀ε)
  have hev : ∀ᶠ u in 𝓝 u₀, u ∈ ball u₀ ε ∧ F u ∈ U₁ ∧ ‖G u‖ < R := by
    have hFG0 : (F u₀, G u₀) ∈ U₁ ×ˢ {x : V | ‖x‖ < R} := by
      refine ⟨hb₁, ?_⟩
      change ‖G u₀‖ < R
      rw [← hG' u₀ hu₀ε]
      exact hb₂
    have h1 := hcont.eventually
      ((hU₁.prod (isOpen_lt continuous_norm continuous_const)).mem_nhds hFG0)
    filter_upwards [isOpen_ball.mem_nhds hu₀ε, h1] with u hu h1u using ⟨hu, h1u.1, h1u.2⟩
  obtain ⟨ε', hε', hball'⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hpre : (fun t => t - b) ⁻¹' Ioo (-h) h = Ioo (b - h) (b + h) := by
    ext t; simp only [mem_preimage, mem_Ioo]; constructor <;> intro h' <;>
      constructor <;> linarith [h'.1, h'.2]
  -- each ray continues by the flow `Φ`
  have hcontu : ∀ u ∈ ball u₀ ε',
      IsGeodesicOn hN (fun t => exp hN (c u) (t • w u)) (Ioo (-η) (b + η) ∪ Ioo (b - h) (b + h)) ∧
      ∀ t ∈ Ioo (b - h) (b + h), exp hN (c u) (t • w u) = Φ (F u, G u, t - b) := by
    intro u hu
    obtain ⟨huε, hFU, hGR⟩ := hball' u hu
    have hgu := hgeo u huε
    have hcu : c u ∈ N := hcN u (hsub huε)
    have hwu : w u ∈ tangentSubspace hN ⟨c u, hcu⟩ :=
      (prj_eq_self_iff hN hcu).1 (hwT u (hsub huε))
    have hFN : F u ∈ N := hgu.mem b hbI
    have hGT : G u ∈ tangentSubspace hN ⟨F u, hFN⟩ := by
      rw [← hG' u huε]; exact hgu.deriv_mem hbI
    have hflow : geoFlow hN (c u, w u) b = (F u, G u) := by
      rw [geoFlow_eq_exp, hG' u huε]
      rfl
    have hJ := hloc ⟨F u, hFN⟩ hFU (G u) hGT hGR
    have hJ' : IsGeodesicOn hN (fun t => exp hN (geoFlow hN (c u, w u) b).1
        (t • (geoFlow hN (c u, w u) b).2)) (Ioo (-h) h) := by
      rw [hflow]; exact hJ.1
    obtain ⟨hU, hfl⟩ := isGeodesicOn_exp_smul_union hcu hwu hgu isPreconnected_Ioo h0I hbI hJ'
      isPreconnected_Ioo ⟨by linarith, hh⟩
    rw [hpre] at hU
    refine ⟨hU, fun t ht => ?_⟩
    have ht' : t - b ∈ Ioo (-h) h := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have := congrArg Prod.fst (hfl (t - b) ht')
    rw [add_sub_cancel, hflow] at this
    rw [← (hJ.2 (t - b) ht')]
    exact this
  set η' := min η (h / 4) with hη'def
  have hη' : 0 < η' := lt_min hη (by positivity)
  have hη'η : η' ≤ η := min_le_left _ _
  have hη'h : η' ≤ h / 4 := min_le_right _ _
  have hsub' : ball u₀ ε' ⊆ ball u₀ ε := fun u hu => (hball' u hu).1
  have hcover : Ioo (-η') (b + h / 2 + η') ⊆ Ioo (-η) (b + η) ∪ Ioo (b - h) (b + h) := by
    intro t ht
    rcases lt_or_ge t (b + η) with htb | htb
    · exact Or.inl ⟨by linarith [ht.1], htb⟩
    · exact Or.inr ⟨by linarith, by linarith [ht.2]⟩
  refine ⟨ε', hε', η', hη', fun u hu => hsub (hsub' hu), ?_, fun u hu =>
    (hcontu u hu).1.mono isOpen_Ioo hcover⟩
  -- smoothness: near each point, either the old rays or the composition with `Φ`
  have hA : ContDiffOn ℝ ∞ (raysE hN c w) (ball u₀ ε' ×ˢ Ioo (b - h) (b + h)) := by
    have hinner : ContDiffOn ℝ ∞ (fun p : E × ℝ => (F p.1, G p.1, p.2 - b))
        (ball u₀ ε' ×ˢ Ioo (b - h) (b + h)) :=
      ((hF.mono hsub').comp contDiffOn_fst fun p hp => hp.1).prodMk
        (((hG.mono hsub').comp contDiffOn_fst fun p hp => hp.1).prodMk
          (contDiffOn_snd.sub contDiffOn_const))
    have hmaps : MapsTo (fun p : E × ℝ => (F p.1, G p.1, p.2 - b))
        (ball u₀ ε' ×ˢ Ioo (b - h) (b + h)) (U₁ ×ˢ ball (0 : V) R ×ˢ Ioo (-h) h) :=
      fun p hp => ⟨(hball' p.1 hp.1).2.1, mem_ball_zero_iff.2 (hball' p.1 hp.1).2.2,
        by linarith [hp.2.1], by linarith [hp.2.2]⟩
    refine (hΦ.comp hinner hmaps).congr fun p hp => ?_
    exact (hcontu p.1 hp.1).2 p.2 hp.2
  refine contDiffOn_of_locally_contDiffOn fun p hp => ?_
  rcases lt_or_ge p.2 (b + η) with hpb | hpb
  · refine ⟨ball u₀ ε ×ˢ Ioo (-η) (b + η), hO, ⟨hsub' hp.1, by linarith [hp.2.1], hpb⟩, ?_⟩
    exact hsm.mono inter_subset_right
  · refine ⟨ball u₀ ε' ×ˢ Ioo (b - h) (b + h), isOpen_ball.prod isOpen_Ioo,
      ⟨hp.1, by linarith, by linarith [hp.2.2]⟩, ?_⟩
    exact hA.mono inter_subset_right

include hU₀ hu₀ hcs hws hcN hwT in
/-- **Smooth dependence on the initial data over a compact interval, with parameters in a normed
space** (the multi-parameter form of `Morse.raysGood_of_isGeodesicOn`). -/
theorem raysGoodE_of_isGeodesicOn {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ)
    (hbase : IsGeodesicOn hN (fun t => exp hN (c u₀) (t • w u₀)) (Ioo (-δ) (B + δ))) :
    RaysGoodE hN c w U₀ u₀ B := by
  set S := {b ∈ Icc 0 B | RaysGoodE hN c w U₀ u₀ b} with hSdef
  have hS0 : (0 : ℝ) ∈ S := ⟨⟨le_rfl, hB⟩, raysGoodE_zero hU₀ hu₀ hcs hws hcN hwT⟩
  have hSbdd : BddAbove S := ⟨B, fun b hb => hb.1.2⟩
  set b₀ := sSup S with hb₀def
  have hb₀0 : 0 ≤ b₀ := le_csSup hSbdd hS0
  have hb₀B : b₀ ≤ B := csSup_le ⟨0, hS0⟩ fun b hb => hb.1.2
  have hb₀I : b₀ ∈ Ioo (-δ) (B + δ) := ⟨by linarith, by linarith⟩
  set γ₀ : ℝ → V := fun t => exp hN (c u₀) (t • w u₀) with hγ₀
  obtain ⟨U₁, hU₁, hxU, h, hh, Φ, hΦ, hloc⟩ := exists_smooth_ray hN ⟨γ₀ b₀, hbase.mem b₀ hb₀I⟩
    (R := ‖deriv γ₀ b₀‖ + 1) (by positivity)
  have hcont : ContinuousAt (fun t => (γ₀ t, deriv γ₀ t)) b₀ :=
    (hbase.contDiffOn.continuousOn.prodMk hbase.contDiffOn_deriv.continuousOn).continuousAt
      (isOpen_Ioo.mem_nhds hb₀I)
  have hev : ∀ᶠ t in 𝓝 b₀, γ₀ t ∈ U₁ ∧ ‖deriv γ₀ t‖ < ‖deriv γ₀ b₀‖ + 1 :=
    hcont.eventually ((hU₁.prod (isOpen_lt continuous_norm continuous_const)).mem_nhds
      (show (γ₀ b₀, deriv γ₀ b₀) ∈ U₁ ×ˢ {x : V | ‖x‖ < ‖deriv γ₀ b₀‖ + 1} from ⟨hxU, by simp⟩))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hm : 0 < min r (h / 4) := lt_min hr (by positivity)
  obtain ⟨s, hsS, hs⟩ := exists_lt_of_lt_csSup ⟨0, hS0⟩ (show b₀ - min r (h / 4) < b₀ by linarith)
  have hsb₀ : s ≤ b₀ := le_csSup hSbdd hsS
  have hsr : s ∈ ball b₀ r := by
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [min_le_left r (h / 4)]
  obtain ⟨hsU, hsR⟩ := hball s hsr
  have hstep := hsS.2.step hcN hwT hsS.1.1 hU₁ hh hΦ hloc hsU hsR
  have hmin : min (s + h / 2) B ∈ S := ⟨⟨le_min (by linarith [hsS.1.1]) hB, min_le_right _ _⟩,
    hstep.mono (min_le_left _ _)⟩
  have hle : min (s + h / 2) B ≤ b₀ := le_csSup hSbdd hmin
  have hlt : b₀ < s + h / 2 := by linarith [min_le_right r (h / 4)]
  have hBeq : min (s + h / 2) B = B := by
    rcases min_choice (s + h / 2) B with h' | h'
    · rw [h'] at hle; exfalso; linarith
    · exact h'
  rw [hBeq] at hmin
  exact hmin.2

end RaysE

/-! ### A smooth local retraction onto `N` -/

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
variable (hN) in
include hN in
/-- **A smooth retraction onto `N` near a point**: from the slice chart `σ` at `p`,
`r(y) = σ⁻¹((σ y)₁, 0)` is smooth near `p`, takes values in `N`, and fixes the points of `N`. -/
theorem exists_retraction (p : N) : ∃ U : Set V, IsOpen U ∧ (p : V) ∈ U ∧ ∃ r : V → V,
    ContDiffOn ℝ ∞ r U ∧ (∀ y ∈ U, r y ∈ N) ∧ ∀ y ∈ U, y ∈ N → r y = y := by
  set σ := sliceAt hN p
  set g : V → Z := fun y => (σ.φ y).1 with hg_def
  have hg : ContDiffOn ℝ ∞ g σ.φ.source :=
    contDiff_fst.comp_contDiffOn (Milnor.Problems.sliceChart_contDiffOn σ)
  refine ⟨σ.φ.source ∩ g ⁻¹' σ.toChart.target,
    hg.continuousOn.isOpen_inter_preimage σ.φ.open_source (isOpen_toChart_target σ),
    ⟨mem_sliceAt_source hN p, toChart_apply_mem_target σ (mem_sliceAt_source hN p)⟩,
    fun y => sliceParam σ (g y), ?_, fun y hy => sliceParam_mem σ hy.2, fun y hy hyN => ?_⟩
  · exact (contDiffOn_sliceParam σ).comp (hg.mono inter_subset_left) fun y hy => hy.2
  · exact sliceParam_toChart σ (q := ⟨y, hyN⟩) hy.1

/-! ### `exp` is smooth on its whole domain -/

/-- The domain of `exp` lies in the tangent bundle `TN`. -/
theorem expDom_subset_tangentBundleSet : expDom hN ⊆ Milnor.Problems.tangentBundleSet hN := by
  rintro z ⟨γ, δ, hδ, hγ, h0, h0'⟩
  have hI : (0 : ℝ) ∈ Ioo (-δ) (1 + δ) := ⟨by linarith, by linarith⟩
  have hq : z.1 ∈ N := by rw [← h0]; exact hγ.mem 0 hI
  refine ⟨hq, ?_⟩
  have := hγ.deriv_mem hI
  rwa [h0', tangentSubspace_congr hN _ hq h0] at this

/-- The radial curve of a point of `TN` is a geodesic from it as soon as it is a geodesic on an
open interval containing `[0, 1]`. -/
theorem mem_expDom_of_isGeodesicOn {y w : V} (hy : y ∈ N)
    (hw : w ∈ tangentSubspace hN ⟨y, hy⟩) {η : ℝ} (hη : 0 < η)
    (hg : IsGeodesicOn hN (fun t => exp hN y (t • w)) (Ioo (-η) (1 + η))) :
    (y, w) ∈ expDom hN := by
  refine ⟨fun t => exp hN y (t • w), η, hη, hg, ?_, ?_⟩
  · simp only [zero_smul, exp_zero hy]
  · exact (hasDerivAt_exp_smul_zero (hN := hN) ⟨y, hy⟩ hw).deriv

/-- **`exp` is smooth on its whole domain** (the global smooth dependence of geodesics on their
initial data): near every `(p, v)` in the domain of `exp` there are an open `O ⊆ V × V` and a map
`F`, smooth on `O`, such that every point of `TN ∩ O` lies in the domain and `exp = F` there. -/
theorem exists_contDiffOn_exp {p v : V} (h : (p, v) ∈ expDom hN) :
    ∃ O : Set (V × V), IsOpen O ∧ (p, v) ∈ O ∧ ∃ F : V × V → V, ContDiffOn ℝ ∞ F O ∧
      ∀ z ∈ O, z ∈ Milnor.Problems.tangentBundleSet hN → z ∈ expDom hN ∧
        exp hN z.1 z.2 = F z := by
  obtain ⟨hpN, hvT⟩ := expDom_subset_tangentBundleSet h
  obtain ⟨γ, hγ⟩ := h
  obtain ⟨U, hU, hpU, r, hr, hrN, hrid⟩ := exists_retraction hN ⟨p, hpN⟩
  -- the family of initial data `u = (y, w) ↦ (r(y), P_{r(y)} w)`
  set U₀ : Set (V × V) := U ×ˢ univ with hU₀
  set c : V × V → V := fun u => r u.1 with hc
  set w : V × V → V := fun u => prj hN (r u.1) u.2 with hw
  have hcs : ContDiffOn ℝ ∞ c U₀ := hr.comp contDiffOn_fst fun u hu => hu.1
  have hcN : ∀ u ∈ U₀, c u ∈ N := fun u hu => hrN u.1 hu.1
  have hws : ContDiffOn ℝ ∞ w U₀ := (ContDiffOn.prj_comp hN hcs hcN).clm_apply contDiffOn_snd
  have hwT : ∀ u ∈ U₀, prj hN (c u) (w u) = w u := fun u _ => prj_prj hN _ _
  have hcw : ∀ z ∈ U₀, z ∈ Milnor.Problems.tangentBundleSet hN → c z = z.1 ∧ w z = z.2 := by
    rintro z hz ⟨hzN, hzT⟩
    have h1 : c z = z.1 := hrid z.1 hz.1 hzN
    refine ⟨h1, ?_⟩
    change prj hN (r z.1) z.2 = z.2
    rw [show r z.1 = z.1 from h1]
    exact (prj_eq_self_iff hN hzN).2 hzT
  -- the base ray
  obtain ⟨δ, hδ, hgeo, -⟩ := hγ.isGeodesicOn_exp_smul
  have hpv : (p, v) ∈ U₀ := ⟨hpU, trivial⟩
  obtain ⟨hc0, hw0⟩ := hcw (p, v) hpv ⟨hpN, hvT⟩
  have hbase : IsGeodesicOn hN (fun t => exp hN (c (p, v)) (t • w (p, v))) (Ioo (-δ) (1 + δ)) := by
    rw [hc0, hw0]; exact hgeo
  obtain ⟨ε, hε, η, hη, hsub, hsm, hrays⟩ := raysGoodE_of_isGeodesicOn (hU.prod isOpen_univ) hpv
    hcs hws hcN hwT zero_le_one hδ hbase
  have h1η : (1 : ℝ) ∈ Ioo (-η) (1 + η) := ⟨by linarith, by linarith⟩
  refine ⟨ball (p, v) ε, isOpen_ball, mem_ball_self hε, fun u => raysE hN c w (u, 1), ?_, ?_⟩
  · exact hsm.comp (contDiffOn_id.prodMk contDiffOn_const) fun u hu => ⟨hu, h1η⟩
  · intro z hz hzT
    obtain ⟨hcz, hwz⟩ := hcw z (hsub hz) hzT
    have hg := hrays z hz
    rw [hcz, hwz] at hg
    refine ⟨mem_expDom_of_isGeodesicOn hzT.1 hzT.2 hη hg, ?_⟩
    simp only [raysE, one_smul, hcz, hwz]

/-- **The domain of `exp` is open in `TN`**. -/
theorem exists_isOpen_expDom : ∃ O : Set (V × V), IsOpen O ∧
    O ∩ Milnor.Problems.tangentBundleSet hN = expDom hN := by
  choose O hO hzO F hF hexp using fun z : expDom hN => exists_contDiffOn_exp (hN := hN) z.2
  refine ⟨⋃ z, O z, isOpen_iUnion hO, Subset.antisymm ?_ fun z hz => ?_⟩
  · rintro z ⟨hz, hzT⟩
    obtain ⟨z', hz'⟩ := mem_iUnion.1 hz
    exact (hexp z' z hz' hzT).1
  · exact ⟨mem_iUnion.2 ⟨⟨z, hz⟩, hzO _⟩, expDom_subset_tangentBundleSet hz⟩

/-- **`exp` is smooth on its domain**, for the manifold structure of the tangent bundle `TN` (a
slice submanifold of `V × V` modelled on `Z × Z`): the extension of `Morse.contMDiffOn_exp`
(smoothness near the zero section) to the whole domain. -/
theorem contMDiffOn_exp_expDom :
    letI := (Milnor.Problems.isSliceSubmanifold_tangentBundle hN).chartedSpace
    ContMDiffOn 𝓘(ℝ, Z × Z) 𝓘(ℝ, V) ∞
      (fun z : Milnor.Problems.tangentBundleSet hN => exp hN z.1.1 z.1.2)
      {z | z.1 ∈ expDom hN} := by
  let _ := (Milnor.Problems.isSliceSubmanifold_tangentBundle hN).chartedSpace
  have := (Milnor.Problems.isSliceSubmanifold_tangentBundle hN).isManifold
  intro z hz
  obtain ⟨O, hO, hzO, F, hF, hFeq⟩ := exists_contDiffOn_exp (hN := hN) hz
  have hval := (Milnor.Problems.isSliceSubmanifold_tangentBundle hN).contMDiff_val
  have h1 : ContMDiffAt 𝓘(ℝ, Z × Z) 𝓘(ℝ, V) ∞ (F ∘ Subtype.val) z :=
    (hF.contDiffAt (hO.mem_nhds hzO)).contMDiffAt.comp z (hval z)
  refine (h1.congr_of_eventuallyEq ?_).contMDiffWithinAt
  have hopen : IsOpen {z' : Milnor.Problems.tangentBundleSet hN | z'.1 ∈ O} :=
    hO.preimage continuous_subtype_val
  filter_upwards [hopen.mem_nhds hzO] with z' hz'
  exact (hFeq z'.1 hz' z'.2).2

/-! ### The exponential map at one point -/

variable (hN) in
/-- **The domain of `exp_q`** in `T_qN`: the `v` for which the geodesic `t ↦ exp_q(tv)` exists on an
open interval containing `[0, 1]` (all of `T_qN` when `N` is complete). -/
def expDomAt (q : N) : Set (tangentSubspace hN q) := {v | ((q : V), (v : V)) ∈ expDom hN}

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem zero_mem_expDomAt (q : N) : (0 : tangentSubspace hN q) ∈ expDomAt hN q :=
  zero_mem_expDom q.2

/-- The domain of `exp_q` is star-shaped about `0`. -/
theorem smul_mem_expDomAt {q : N} {v : tangentSubspace hN q} (hv : v ∈ expDomAt hN q) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : t • v ∈ expDomAt hN q := by
  obtain ⟨γ, hγ⟩ := hv
  obtain ⟨δ, hδ, -, hsm⟩ := hγ.exp_smul
  exact (hsm t ⟨by linarith [ht.1], by linarith [ht.2]⟩).1.mem_expDom

/-- Near a point of the domain of `exp_q`, `exp_q` is the restriction of a smooth map. -/
theorem exists_contDiffAt_expAt {q : N} {v : tangentSubspace hN q} (hv : v ∈ expDomAt hN q) :
    ∃ O : Set (tangentSubspace hN q), IsOpen O ∧ v ∈ O ∧ O ⊆ expDomAt hN q ∧
      ContDiffOn ℝ ∞ (fun y : tangentSubspace hN q => exp hN q y) O := by
  obtain ⟨O, hO, hvO, F, hF, hFeq⟩ := exists_contDiffOn_exp (hN := hN) hv
  set ι : tangentSubspace hN q → V × V := fun y => ((q : V), (y : V)) with hι
  have hιc : ContDiff ℝ ∞ ι := contDiff_const.prodMk (tangentSubspace hN q).subtypeL.contDiff
  have hT : ∀ y : tangentSubspace hN q, ι y ∈ Milnor.Problems.tangentBundleSet hN :=
    fun y => ⟨q.2, y.2⟩
  refine ⟨ι ⁻¹' O, hO.preimage hιc.continuous, hvO, fun y hy => (hFeq _ hy (hT y)).1, ?_⟩
  exact (hF.comp hιc.contDiffOn (mapsTo_preimage ι O)).congr fun y hy => (hFeq _ hy (hT y)).2

/-- **The domain of `exp_q` is open** in `T_qN`. -/
theorem isOpen_expDomAt (q : N) : IsOpen (expDomAt hN q) := by
  refine isOpen_iff_forall_mem_open.2 fun v hv => ?_
  obtain ⟨O, hO, hvO, hOD, -⟩ := exists_contDiffAt_expAt hv
  exact ⟨O, hOD, hO, hvO⟩

/-- **`exp_q` is smooth on its domain** in `T_qN` (Milnor's `exp : TM_p → M`, p. 98). -/
theorem contDiffOn_expAt (q : N) :
    ContDiffOn ℝ ∞ (fun y : tangentSubspace hN q => exp hN q y) (expDomAt hN q) := by
  intro v hv
  obtain ⟨O, hO, hvO, -, hsm⟩ := exists_contDiffAt_expAt hv
  exact ((hsm.contDiffAt (hO.mem_nhds hvO)).contDiffWithinAt)

/-- The radial geodesic `γ_v(t) = exp_q(tv)` of a vector of the domain is a geodesic on an open
interval containing `[0, 1]`. -/
theorem isGeodesicOn_ray {q : N} {v : tangentSubspace hN q} (hv : v ∈ expDomAt hN q) :
    ∃ δ > 0, IsGeodesicOn hN (fun t => exp hN q (t • (v : V))) (Ioo (-δ) (1 + δ)) := by
  obtain ⟨γ, hγ⟩ := hv
  obtain ⟨δ, hδ, hgeo, -⟩ := hγ.isGeodesicOn_exp_smul
  exact ⟨δ, hδ, hgeo⟩

/-- `γ_v(t) = exp_q(tv)` is a smooth curve in `N` on `[0, 1]`. -/
theorem isSmoothCurveIn_ray {q : N} {v : tangentSubspace hN q} (hv : v ∈ expDomAt hN q) :
    IsSmoothCurveIn hN (fun t => exp hN q (t • (v : V))) := by
  obtain ⟨δ, hδ, hgeo⟩ := isGeodesicOn_ray hv
  have hsub : Icc (0 : ℝ) 1 ⊆ Ioo (-δ) (1 + δ) := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact ⟨hgeo.contDiffOn.mono hsub, fun t ht => hgeo.mem t (hsub ht)⟩

/-! ### Theorem 18.1 -/

variable (hN) in
/-- **The Jacobi fields of the variation `exp_q(t(v + uX))`** (the proof of Theorem 18.1):
`W_X(t) = d(exp_q)_{tv}(tX) = t d(exp_q)_{tv}(X)`, normalized to be constant off `[0, 1]`. -/
def expJacobi (q : N) (v : tangentSubspace hN q) : tangentSubspace hN q →ₗ[ℝ] (ℝ → V) where
  toFun X t := (projIcc (0 : ℝ) 1 zero_le_one t : ℝ) •
    fderiv ℝ (fun y : tangentSubspace hN q => exp hN q y)
      ((projIcc (0 : ℝ) 1 zero_le_one t : ℝ) • v) X
  map_add' X Y := by
    funext t
    simp only [map_add, smul_add, Pi.add_apply]
  map_smul' a X := by
    funext t
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply]
    rw [smul_comm]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem expJacobi_apply_of_mem {q : N} (v X : tangentSubspace hN q) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : expJacobi hN q v X t =
      t • fderiv ℝ (fun y : tangentSubspace hN q => exp hN q y) (t • v) X := by
  simp only [expJacobi, LinearMap.coe_mk, AddHom.coe_mk, projIcc_of_mem _ ht]

variable (hN) in
/-- **`d(exp_q)_v`**: the derivative at `v` of `exp_q : T_qN → V`, as a linear map (Milnor's
`exp_* : T(TM_p)_v → TM_{exp v}`, with `T(TM_p)_v` identified with `TM_p`). -/
def dExpAt (q : N) (v : tangentSubspace hN q) : tangentSubspace hN q →ₗ[ℝ] V :=
  (fderiv ℝ (fun y : tangentSubspace hN q => exp hN q y) v : tangentSubspace hN q →L[ℝ] V)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem dExpAt_apply (q : N) (v X : tangentSubspace hN q) :
    dExpAt hN q v X = fderiv ℝ (fun y : tangentSubspace hN q => exp hN q y) v X := rfl

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem expJacobi_zero {q : N} (v X : tangentSubspace hN q) : expJacobi hN q v X 0 = 0 := by
  rw [expJacobi_apply_of_mem v X ⟨le_rfl, zero_le_one⟩, zero_smul]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem expJacobi_one {q : N} (v X : tangentSubspace hN q) :
    expJacobi hN q v X 1 = fderiv ℝ (fun y : tangentSubspace hN q => exp hN q y) v X := by
  rw [expJacobi_apply_of_mem v X ⟨zero_le_one, le_rfl⟩, one_smul, one_smul]

/-- **The variation through geodesics** `α(u, t) = exp_q(t(v + uX))` (Milnor p. 98): its variation
field `expJacobi hN q v X` is a Jacobi field along `γ_v` (Lemma 14.3). -/
theorem isJacobiField_expJacobi {q : N} {v : tangentSubspace hN q} (hv : v ∈ expDomAt hN q)
    (X : tangentSubspace hN q) :
    IsJacobiField hN (fun t => exp hN q (t • (v : V))) (expJacobi hN q v X) := by
  set E : tangentSubspace hN q → V := fun y => exp hN q y with hE
  set g : ℝ × ℝ → tangentSubspace hN q := fun p => p.2 • (v + p.1 • X) with hg
  have hgc : ContDiff ℝ ∞ g :=
    contDiff_snd.smul (contDiff_const.add (contDiff_fst.smul contDiff_const))
  -- a box `(-ε, ε) × [0, 1]` mapped into the domain of `exp_q` (tube lemma)
  have hK : ({0} : Set ℝ) ×ˢ Icc (0 : ℝ) 1 ⊆ g ⁻¹' expDomAt hN q := by
    rintro ⟨u, t⟩ ⟨hu, ht⟩
    rw [mem_singleton_iff] at hu
    subst hu
    simp only [mem_preimage, hg, zero_smul, add_zero]
    exact smul_mem_expDomAt hv ht
  obtain ⟨U', T', hU', -, h0U', hIT', hsub⟩ := generalized_tube_lemma isCompact_singleton
    isCompact_Icc ((isOpen_expDomAt q).preimage hgc.continuous) hK
  obtain ⟨ε, hε, hεU'⟩ := Metric.isOpen_iff.1 hU' 0 (h0U' rfl)
  have hbox : Ioo (-ε) ε ×ˢ Icc (0 : ℝ) 1 ⊆ g ⁻¹' expDomAt hN q := fun p hp =>
    hsub ⟨hεU' (by rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]; exact hp.1), hIT' hp.2⟩
  set α : ℝ → ℝ → V := fun u t => E (g (u, t)) with hα
  have hαs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => α p.1 p.2) (Ioo (-ε) ε ×ˢ Icc (0 : ℝ) 1) :=
    (contDiffOn_expAt q).comp hgc.contDiffOn hbox
  have hαN : ∀ u ∈ Ioo (-ε) ε, ∀ t ∈ Icc (0 : ℝ) 1, α u t ∈ N := fun u hu t ht =>
    exp_mem_of_mem_expDom (hbox ⟨hu, ht⟩)
  have hgeo : ∀ u ∈ Ioo (-ε) ε, IsGeodesicOn hN (α u) (Ioo 0 1) := by
    intro u hu
    have h1 : v + u • X ∈ expDomAt hN q := by
      have := hbox (show (u, (1 : ℝ)) ∈ Ioo (-ε) ε ×ˢ Icc (0 : ℝ) 1 from
        ⟨hu, zero_le_one, le_rfl⟩)
      simpa [hg] using this
    obtain ⟨δ, hδ, hgeo⟩ := isGeodesicOn_ray h1
    refine (hgeo.mono isOpen_Ioo (Ioo_subset_Ioo (by linarith) (by linarith))).congr
      fun t _ => ?_
    simp [hα, hg, hE]
  have hJ := lemma_14_3 hε hαs hαN hgeo
  have hα0 : α 0 = fun t => exp hN q (t • (v : V)) := by
    funext t; simp [hα, hg, hE]
  rw [hα0] at hJ
  refine hJ.congr fun t ht => ?_
  -- the chain rule: `∂α/∂u (0, t) = dE_{tv}(tX)`
  have hgt : t • v ∈ expDomAt hN q := smul_mem_expDomAt hv ht
  have hEd : HasFDerivAt E (fderiv ℝ E (t • v)) (t • (v + (0 : ℝ) • X)) := by
    rw [zero_smul, add_zero]
    exact (((contDiffOn_expAt q).contDiffAt ((isOpen_expDomAt q).mem_nhds hgt)).differentiableAt
      (by simp)).hasFDerivAt
  have hl : HasDerivAt (fun u : ℝ => t • (v + u • X)) (t • X) 0 := by
    have h1 : HasDerivAt (fun u : ℝ => v + u • X) ((1 : ℝ) • X) 0 :=
      ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add v
    rw [one_smul] at h1
    exact h1.const_smul t
  have h2 := hEd.comp_hasDerivAt (0 : ℝ) hl
  rw [expJacobi_apply_of_mem v X ht]
  change deriv (E ∘ fun u => t • (v + u • X)) 0 = _
  rw [h2.deriv, map_smul]

/-- `DW_X/dt (0) = X` (Milnor p. 98, by `d(exp_q)₀ = id`). -/
theorem covAlong_expJacobi_zero {q : N} {v : tangentSubspace hN q} (X : tangentSubspace hN q) :
    covAlong hN (fun t => exp hN q (t • (v : V))) (expJacobi hN q v X) 0 = X := by
  set E : tangentSubspace hN q → V := fun y => exp hN q y with hE
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h0D : (0 : ℝ) • v ∈ expDomAt hN q := by rw [zero_smul]; exact zero_mem_expDomAt q
  have hL : DifferentiableAt ℝ (fun t : ℝ => fderiv ℝ E (t • v) X) 0 := by
    have hD : ContDiffAt ℝ ∞ (fderiv ℝ E) ((0 : ℝ) • v) :=
      ((contDiffOn_expAt q).contDiffAt ((isOpen_expDomAt q).mem_nhds h0D)).fderiv_right
        (m := ∞) (by simp)
    exact ((hD.comp (0 : ℝ) (contDiffAt_id.smul contDiffAt_const)).clm_apply
      contDiffAt_const).differentiableAt (by simp)
  have hd : HasDerivAt (fun t : ℝ => t • fderiv ℝ E (t • v) X) (fderiv ℝ E ((0 : ℝ) • v) X) 0 := by
    have h := (hasDerivAt_id' (0 : ℝ)).smul hL.hasDerivAt
    rw [zero_smul, zero_add, one_smul] at h
    exact h
  have hdW : derivWithin (expJacobi hN q v X) (Icc 0 1) 0 = fderiv ℝ E 0 X := by
    rw [derivWithin_congr (fun t ht => expJacobi_apply_of_mem v X ht)
      (expJacobi_apply_of_mem v X h0),
      hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one 0 h0), zero_smul]
  have hE0 : fderiv ℝ E 0 = (tangentSubspace hN q).subtypeL := (hasFDerivAt_exp_zero q).fderiv
  rw [covAlong, hdW, hE0]
  simp only [Submodule.subtypeL_apply, zero_smul, exp_zero q.2]
  exact (prj_eq_self_iff hN q.2).2 X.2

theorem expJacobi_mem_jacobiSpace {q : N} {v : tangentSubspace hN q} (hv : v ∈ expDomAt hN q)
    (X : tangentSubspace hN q) :
    expJacobi hN q v X ∈ jacobiSpace hN _ (isSmoothCurveIn_ray hv) :=
  ⟨isJacobiField_expJacobi hv X, fun t => by
    simp only [expJacobi, LinearMap.coe_mk, AddHom.coe_mk, projIcc_projIcc]⟩

theorem expJacobi_injective {q : N} (v : tangentSubspace hN q) : Injective (expJacobi hN q v) :=
  fun X Y h => by
    have h1 := covAlong_expJacobi_zero (hN := hN) (v := v) X
    have h2 := covAlong_expJacobi_zero (hN := hN) (v := v) Y
    rw [h] at h1
    exact Subtype.ext (h1.symm.trans h2)

/-- **The Jacobi fields vanishing at `0` are exactly the `W_X`**, with `X = DJ/dt(0)` (a Jacobi
field is determined by `J(0)` and `DJ/dt(0)`, Milnor p. 77; this replaces the dimension count of
p. 99). -/
theorem eq_expJacobi {q : N} {v : tangentSubspace hN q} (hv : v ∈ expDomAt hN q) {J : ℝ → V}
    (hJ : J ∈ jacobiSpace hN _ (isSmoothCurveIn_ray hv)) (h0 : J 0 = 0) :
    ∃ X : tangentSubspace hN q, J = expJacobi hN q v X := by
  set hc := isSmoothCurveIn_ray hv
  set γ : ℝ → V := fun t => exp hN q (t • (v : V))
  have h00 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hγ0 : γ 0 = q := by simp [γ, exp_zero q.2]
  have hX : covAlong hN γ J 0 ∈ tangentSubspace hN q := by
    have h := prj_mem hN q.2 (derivWithin J (Icc 0 1) 0)
    rw [covAlong, hγ0]
    exact h
  refine ⟨⟨covAlong hN γ J 0, hX⟩, ?_⟩
  have hinj := (jacEval_bijective hc h00).1
  have := @hinj ⟨J, hJ⟩ ⟨_, expJacobi_mem_jacobiSpace hv ⟨covAlong hN γ J 0, hX⟩⟩ ?_
  · exact congrArg Subtype.val this
  · refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change J 0 = expJacobi hN q v _ 0
      rw [h0, expJacobi_zero]
    · change covAlong hN γ J 0 = covAlong hN γ (expJacobi hN q v _) 0
      rw [covAlong_expJacobi_zero]

/-- **The Jacobi fields along `γ_v` vanishing at `0` and `1` are the `W_X` with `X` in the kernel
of `d(exp_q)_v`** (the proof of Theorem 18.1). -/
theorem conjSpace_eq_map_ker {q : N} {v : tangentSubspace hN q} (hv : v ∈ expDomAt hN q) :
    conjSpace hN _ (isSmoothCurveIn_ray hv) 0 1 =
      (LinearMap.ker (dExpAt hN q v)).map
        (expJacobi hN q v) := by
  ext J
  rw [mem_conjSpace]
  constructor
  · rintro ⟨hJ, h0, h1⟩
    obtain ⟨X, rfl⟩ := eq_expJacobi hv hJ h0
    refine ⟨X, ?_, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, dExpAt_apply, ← expJacobi_one]
    exact h1
  · rintro ⟨X, hX, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, dExpAt_apply] at hX
    exact ⟨expJacobi_mem_jacobiSpace hv X, expJacobi_zero v X, by rw [expJacobi_one, hX]⟩

/-- **Theorem 18.1, the multiplicity** (Milnor p. 98, made precise as in the exposition): the
multiplicity of `exp_q(v)` as a conjugate point of `q` along `γ_v(t) = exp_q(tv)` is the
dimension of the kernel of `d(exp_q)_v`. -/
theorem theorem_18_1_multiplicity {q : N} {v : tangentSubspace hN q} (hv : v ∈ expDomAt hN q) :
    conjMultiplicity hN _ (isSmoothCurveIn_ray hv) 0 1 =
      finrank ℝ (LinearMap.ker (dExpAt hN q v)) := by
  rw [conjMultiplicity, conjSpace_eq_map_ker hv]
  exact (Submodule.equivMapOfInjective _ (expJacobi_injective v) _).finrank_eq.symm

/-- **Theorem 18.1** (Milnor p. 98): `exp_q(v)` is conjugate to `q` along the geodesic
`γ_v(t) = exp_q(tv)` if and only if `exp_q` is critical at `v`, i.e. `d(exp_q)_v` is not
one-to-one. -/
theorem theorem_18_1 {q : N} {v : tangentSubspace hN q} (hv : v ∈ expDomAt hN q) :
    IsConjugate hN (fun t => exp hN q (t • (v : V))) 0 1 ↔
      ¬ Injective (dExpAt hN q v) := by
  have h : 0 < finrank ℝ (LinearMap.ker (dExpAt hN q v)) ↔ LinearMap.ker (dExpAt hN q v) ≠ ⊥ := by
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
  rw [isConjugate_iff (isSmoothCurveIn_ray hv), theorem_18_1_multiplicity hv, h]
  simp only [ne_eq, LinearMap.ker_eq_bot]
  simp

end Morse
