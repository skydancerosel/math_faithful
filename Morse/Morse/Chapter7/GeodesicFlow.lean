import Morse.Chapter7.Metric

/-!
Milnor, *Morse Theory*, §10, pp. 57–58, 62 and 64, for a submanifold `N ⊆ ℝᴷ` with the induced
metric.

# The geodesic flow, geodesic completeness, and the converse of Corollary 10.10

## Milnor's text, paraphrased

* (p. 58) `M` is *geodesically complete* if `exp_q(v)` is defined for all `q ∈ M` and all
  `v ∈ TM_q`; this is clearly equivalent, he says, to the requirement that every geodesic segment
  extends indefinitely, the form in which the definition is recalled on p. 62.
* (p. 64) After Corollary 10.10: conversely, if `M` is complete as a metric space, it is
  geodesically complete; Milnor calls this not difficult, using Lemma 10.3, and refers to Hopf and
  Rinow for the details.
* (p. 64, proof of Corollary 10.10) `exp_p` maps the disk of radius `d` in `TM_p` onto a compact
  set: this needs `exp_p` continuous on the whole disk.

## In the embedded setting

* `Morse.IsGeodesicOn.exp_smul_eq`: **`exp` along a geodesic**: for every geodesic `γ` on an open
  interval containing `0`, `γ(t) = exp_{γ(0)}(t γ'(0))`.  So the curves `t ↦ exp_y(tw)` represent
  all geodesics, and `Morse.geoFlow` (position and velocity of `t ↦ exp_y(tw)` at time `t`) is the
  geodesic flow wherever the geodesic exists.
* `Morse.exists_localFlow_exp`: **the local flow, uniformly**: near any `x₀ ∈ N` and for speeds
  `< R`, the geodesics exist for a uniform time `τ`, and their position and velocity are continuous
  in `(y, w, t)` (Lemma 10.2 with smooth dependence, rescaled by homogeneity);
  `Morse.exists_isGeodesicOn_exp_smul`: local existence.
* `Morse.isGeodesicOn_exp_smul_union`: **continuing a geodesic** by the geodesic which starts at
  its position and velocity at some time `s`.
* `Morse.eventually_mem_expDom_and_continuousWithinAt_exp`: **the domain of `exp` is open in `TN`
  and `exp` is continuous on it** (the global dependence on initial conditions, the exposition's
  Lemma B); `Morse.continuousOn_exp`: `exp_p` is continuous on `T_pN` when it is defined on all of
  it.
* `Morse.IsGeodesicallyComplete hN`: Milnor's definition (p. 58).
  `Morse.isGeodesicOn_univ_exp_smul`: if `exp_q` is defined on `T_qN`, then `t ↦ exp_q(tv)` is a
  geodesic on all of `ℝ`;
  `Morse.isGeodesicallyComplete_iff`: **the two definitions (pp. 58 and 62) agree**.
* `Morse.isGeodesicallyComplete_of_isRiemComplete`: **metric completeness implies geodesic
  completeness** (p. 64).

## What Milnor leaves implicit

* **The two definitions of geodesic completeness** agree only by gluing geodesics, which rests on
  the uniqueness of geodesics in the large (`Morse.IsGeodesicOn.eqOn`).
* **Continuity of `exp_p` on large disks**, needed for Corollary 10.10, is not given by Lemma 10.2,
  which concerns small vectors.  It is the global dependence of geodesics on their initial data:
  here it is obtained by covering a compact geodesic arc `γ([0, 1])` by finitely many
  neighbourhoods on which all geodesics of bounded speed exist for a uniform time `2τ₀`, and
  continuing the geodesics with initial data near `(p, v)` by steps of length `τ₀`; at each step
  the position and velocity are compositions of continuous maps.
* **The converse of Corollary 10.10** needs only the uniform local existence of Lemma 10.2 near one
  point, not Lemma 10.3: if the geodesic `γ` with initial velocity `v` existed only on `[0, T₀)`,
  then `ρ(γ(t), γ(t')) ≤ ‖v‖ |t − t'|` makes `γ(tₙ)`, `tₙ ↑ T₀`, a Cauchy sequence; its limit `x`
  has a neighbourhood in which all geodesics of speed `‖v‖` exist for a uniform time `τ`, so `γ`
  continues beyond `T₀`.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace ENNReal NNReal

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

/-! ### `exp` along a geodesic -/

/-- A preimage of a preconnected set of `ℝ` under an affine map is preconnected. -/
theorem isPreconnected_preimage_mul_add {s : Set ℝ} (hs : IsPreconnected s) (a b : ℝ) :
    IsPreconnected ((fun t => a * t + b) ⁻¹' s) := by
  refine Real.convex_iff_isPreconnected.1 fun x hx y hy c d hc hd hcd => ?_
  have := (Real.convex_iff_isPreconnected.2 hs) hx hy hc hd hcd
  simp only [mem_preimage, smul_eq_mul] at this ⊢
  convert this using 1
  calc a * (c * x + d * y) + b = a * (c * x + d * y) + b * (c + d) := by rw [hcd, mul_one]
    _ = c * (a * x + b) + d * (a * y + b) := by ring

variable {hN}

/-- **`exp` along a geodesic** (Milnor, p. 57, `γ(t) = exp_q(tv)`): if `γ` is a geodesic on an open
interval `s ∋ 0`, then `exp_{γ(0)}(t γ'(0)) = γ(t)` for every `t ∈ s`. -/
theorem IsGeodesicOn.exp_smul_eq {γ : ℝ → V} {s : Set ℝ} (h : IsGeodesicOn hN γ s)
    (hs : IsPreconnected s) (h0 : (0 : ℝ) ∈ s) {t : ℝ} (ht : t ∈ s) :
    exp hN (γ 0) (t • deriv γ 0) = γ t := by
  have hη := h.comp_mul_add t 0
  have hpre := isPreconnected_preimage_mul_add hs t 0
  simp only [add_zero] at hη hpre
  have h00 : (0 : ℝ) ∈ (fun σ => t * σ) ⁻¹' s := by simpa using h0
  have h11 : (1 : ℝ) ∈ (fun σ => t * σ) ⁻¹' s := by simpa using ht
  have hfrom := isGeodesicFrom_of_isGeodesicOn hη hpre h00 h11
  have hd : deriv (fun σ => γ (t * σ)) 0 = t • deriv γ 0 := by
    have h1 : HasDerivAt (fun σ : ℝ => t * σ) t 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul t
    have h2 := HasDerivAt.scomp (h := fun σ : ℝ => t * σ) (0 : ℝ)
      (h.hasDerivAt (t := t * 0) (by simpa using h0)) h1
    simp only [mul_zero] at h2
    exact h2.deriv
  rw [hd] at hfrom
  have := hfrom.exp_eq
  simp only [mul_zero, mul_one] at this
  exact this

/-- On a geodesic `γ` through `γ(0)` (on an open interval `s ∋ 0`), the curve
`t ↦ exp_{γ(0)}(t γ'(0))` coincides with `γ`; in particular it is a geodesic on `s`. -/
theorem IsGeodesicOn.eqOn_exp_smul {γ : ℝ → V} {s : Set ℝ} (h : IsGeodesicOn hN γ s)
    (hs : IsPreconnected s) (h0 : (0 : ℝ) ∈ s) :
    EqOn (fun t => exp hN (γ 0) (t • deriv γ 0)) γ s :=
  fun _ ht => h.exp_smul_eq hs h0 ht

/-! ### The geodesic flow -/

variable (hN) in
/-- **The geodesic flow**, read off from `exp`: the position and the velocity at time `t` of the
curve `s ↦ exp_y(s w)`, for `z = (y, w)`.  Where the geodesic with initial data `(y, w)` exists,
this is its position and velocity at time `t` (`Morse.IsGeodesicOn.exp_smul_eq`). -/
def geoFlow (z : V × V) (t : ℝ) : V × V :=
  (exp hN z.1 (t • z.2), deriv (fun s => exp hN z.1 (s • z.2)) t)

variable (hN) in
/-- **The geodesic flow near a point, uniformly** (Lemma 10.2 with smooth dependence, rescaled):
for `x₀ ∈ N` and a speed bound `R > 0` there are an open `U ∋ x₀`, a time `τ > 0` and a map `Φ`,
continuous on `U × B_R(0) × (-τ, τ)`, such that for `y ∈ N ∩ U` and `w ∈ T_yN`, `‖w‖ < R`, the
curve `t ↦ exp_y(tw)` is a geodesic on `(-τ, τ)` with initial velocity `w`, and its position and
velocity at time `t` are `Φ(y, w, t)`. -/
theorem exists_localFlow_exp (x₀ : N) {R : ℝ} (hR : 0 < R) :
    ∃ U : Set V, IsOpen U ∧ (x₀ : V) ∈ U ∧ ∃ τ > 0, ∃ Φ : V × V × ℝ → V × V,
      ContinuousOn Φ (U ×ˢ ball (0 : V) R ×ˢ Ioo (-τ) τ) ∧
      ∀ y : N, (y : V) ∈ U → ∀ w ∈ tangentSubspace hN y, ‖w‖ < R →
        IsGeodesicOn hN (fun t => exp hN y (t • w)) (Ioo (-τ) τ) ∧
        HasDerivAt (fun t : ℝ => exp hN y (t • w)) w 0 ∧
        ∀ t ∈ Ioo (-τ) τ, geoFlow hN ((y : V), w) t = Φ ((y : V), w, t) := by
  obtain ⟨U, hU, hx₀U, ε, hε, Γ, hΓ, hgeo⟩ := lemma_10_2 hN x₀
  set a := ε / (2 * R) with ha_def
  have ha : 0 < a := by positivity
  have haR : a * R < ε := by
    have : a * R = ε / 2 := by rw [ha_def]; field_simp
    linarith
  set O := U ×ˢ ball (0 : V) ε ×ˢ Ioo (-2 : ℝ) 2 with hO_def
  have hO : IsOpen O := hU.prod (isOpen_ball.prod isOpen_Ioo)
  set ι : V × V × ℝ → V × V × ℝ := fun z => (z.1, a • z.2.1, a⁻¹ * z.2.2) with hι_def
  have hι : Continuous ι := by
    simp only [hι_def]
    fun_prop
  have hιmaps : MapsTo ι (U ×ˢ ball (0 : V) R ×ˢ Ioo (-(2 * a)) (2 * a)) O := by
    rintro ⟨y, w, t⟩ ⟨hy, hw, ht⟩
    refine ⟨hy, ?_, ?_⟩
    · rw [mem_ball, dist_zero_right] at hw ⊢
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
      calc a * ‖w‖ ≤ a * R := by gcongr
        _ < ε := haR
    · have h1 : -(2 * a) < t := ht.1
      have h2 : t < 2 * a := ht.2
      constructor
      · rw [lt_inv_mul_iff₀ ha]; linarith
      · rw [inv_mul_lt_iff₀ ha]; linarith
  have hdΓ : ContinuousOn (fderiv ℝ Γ) O := hΓ.continuousOn_fderiv_of_isOpen hO (by simp)
  refine ⟨U, hU, hx₀U, 2 * a, by positivity,
    fun z => (Γ (ι z), a⁻¹ • fderiv ℝ Γ (ι z) ((0 : V), (0 : V), (1 : ℝ))), ?_, ?_⟩
  · exact (hΓ.continuousOn.comp hι.continuousOn hιmaps).prodMk
      (((hdΓ.comp hι.continuousOn hιmaps).clm_apply continuousOn_const).const_smul a⁻¹)
  · intro y hyU w hw hwR
    have haw : a • w ∈ tangentSubspace hN y := Submodule.smul_mem _ _ hw
    have hawε : ‖a • w‖ < ε := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
      calc a * ‖w‖ ≤ a * R := by gcongr
        _ < ε := haR
    obtain ⟨hg, h0, hd, -⟩ := hgeo y hyU (a • w) haw hawε
    -- the rescaled geodesic `η(t) = Γ(y, a w, t / a)`
    set η : ℝ → V := fun t => Γ ((y : V), a • w, a⁻¹ * t) with hη_def
    have hpre : (fun t => a⁻¹ * t + 0) ⁻¹' Ioo (-2 : ℝ) 2 = Ioo (-(2 * a)) (2 * a) := by
      ext t
      simp only [mem_preimage, add_zero, mem_Ioo]
      rw [lt_inv_mul_iff₀ ha, inv_mul_lt_iff₀ ha]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    have hηgeo : IsGeodesicOn hN η (Ioo (-(2 * a)) (2 * a)) := by
      have := hg.comp_mul_add a⁻¹ 0
      rw [hpre] at this
      simpa only [add_zero] using this
    have hI0 : (0 : ℝ) ∈ Ioo (-(2 * a)) (2 * a) := ⟨by linarith, by linarith⟩
    have hη0 : η 0 = y := by simp only [hη_def, mul_zero]; exact h0
    have hlin : ∀ t : ℝ, HasDerivAt (fun t : ℝ => ((y : V), a • w, a⁻¹ * t))
        ((0 : V), (0 : V), a⁻¹) t := fun t =>
      (hasDerivAt_const _ _).prodMk ((hasDerivAt_const _ _).prodMk
        (by simpa using (hasDerivAt_id t).const_mul a⁻¹))
    have hηD : ∀ t ∈ Ioo (-(2 * a)) (2 * a), HasDerivAt η
        (a⁻¹ • fderiv ℝ Γ (ι ((y : V), w, t)) ((0 : V), (0 : V), (1 : ℝ))) t := by
      intro t ht
      have hmem : ι ((y : V), w, t) ∈ O :=
        hιmaps ⟨hyU, by rw [mem_ball, dist_zero_right]; exact hwR, ht⟩
      have hΓd : HasFDerivAt Γ (fderiv ℝ Γ (ι ((y : V), w, t))) (ι ((y : V), w, t)) :=
        ((hΓ.contDiffAt (hO.mem_nhds hmem)).differentiableAt (by simp)).hasFDerivAt
      have h1 := hΓd.comp_hasDerivAt t (hlin t)
      have e : fderiv ℝ Γ (ι ((y : V), w, t)) ((0 : V), (0 : V), a⁻¹) =
          a⁻¹ • fderiv ℝ Γ (ι ((y : V), w, t)) ((0 : V), (0 : V), (1 : ℝ)) := by
        rw [← map_smul]
        congr 1
        ext <;> simp
      rw [e] at h1
      exact h1
    have hηd0 : deriv η 0 = w := by
      rw [(hηD 0 hI0).deriv]
      have h1 := hd.deriv
      have h2 : HasDerivAt (fun s => Γ ((y : V), a • w, s))
          (fderiv ℝ Γ (ι ((y : V), w, 0)) ((0 : V), (0 : V), (1 : ℝ))) 0 := by
        have hmem : ι ((y : V), w, 0) ∈ O :=
          hιmaps ⟨hyU, by rw [mem_ball, dist_zero_right]; exact hwR, hI0⟩
        have hΓd : HasFDerivAt Γ (fderiv ℝ Γ (ι ((y : V), w, 0))) (ι ((y : V), w, 0)) :=
          ((hΓ.contDiffAt (hO.mem_nhds hmem)).differentiableAt (by simp)).hasFDerivAt
        have hl : HasDerivAt (fun s : ℝ => ((y : V), a • w, s)) ((0 : V), (0 : V), (1 : ℝ)) 0 :=
          (hasDerivAt_const _ _).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_id 0))
        have hι0 : ι ((y : V), w, 0) = ((y : V), a • w, 0) := by simp [hι_def]
        rw [hι0] at hΓd ⊢
        exact hΓd.comp_hasDerivAt (0 : ℝ) hl
      rw [h2.deriv] at h1
      rw [h1, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
    -- `exp_y(t w) = η(t)` on `(-2a, 2a)`
    have heq : EqOn (fun t => exp hN y (t • w)) η (Ioo (-(2 * a)) (2 * a)) := by
      intro t ht
      have := hηgeo.exp_smul_eq isPreconnected_Ioo hI0 ht
      rwa [hη0, hηd0] at this
    have hgeoexp : IsGeodesicOn hN (fun t => exp hN y (t • w)) (Ioo (-(2 * a)) (2 * a)) :=
      hηgeo.congr heq.symm
    have hev : ∀ t ∈ Ioo (-(2 * a)) (2 * a), (fun t => exp hN y (t • w)) =ᶠ[𝓝 t] η :=
      fun t ht => eventually_of_mem (isOpen_Ioo.mem_nhds ht) heq
    refine ⟨hgeoexp, ?_, fun t ht => ?_⟩
    · have := (hηD 0 hI0).congr_of_eventuallyEq (hev 0 hI0)
      rw [← (hηD 0 hI0).deriv, hηd0] at this
      exact this
    · have e1 : exp hN y (t • w) = η t := heq ht
      simp only [geoFlow]
      rw [e1, (hev t ht).deriv_eq, (hηD t ht).deriv]

/-- **Local existence of geodesics**, in terms of `exp`: for `y ∈ N` and `w ∈ T_yN`, the curve
`t ↦ exp_y(tw)` is a geodesic on an interval `(-τ, τ)`, with initial velocity `w`. -/
theorem exists_isGeodesicOn_exp_smul (y : N) {w : V} (hw : w ∈ tangentSubspace hN y) :
    ∃ τ > 0, IsGeodesicOn hN (fun t => exp hN y (t • w)) (Ioo (-τ) τ) ∧
      HasDerivAt (fun t : ℝ => exp hN y (t • w)) w 0 := by
  obtain ⟨U, -, hyU, τ, hτ, Φ, -, hU⟩ := exists_localFlow_exp hN y (R := ‖w‖ + 1) (by positivity)
  obtain ⟨h1, h2, -⟩ := hU y hyU w hw (by linarith)
  exact ⟨τ, hτ, h1, h2⟩

/-- The curve `t ↦ exp_y(tw)` has velocity `w` at `0`. -/
theorem hasDerivAt_exp_smul_zero (y : N) {w : V} (hw : w ∈ tangentSubspace hN y) :
    HasDerivAt (fun t : ℝ => exp hN y (t • w)) w 0 :=
  (exists_isGeodesicOn_exp_smul y hw).choose_spec.2.2

/-- The geodesic flow at time `0` is the identity of `TN`. -/
theorem geoFlow_zero {y w : V} (hy : y ∈ N) (hw : w ∈ tangentSubspace hN ⟨y, hy⟩) :
    geoFlow hN (y, w) 0 = (y, w) := by
  have := (hasDerivAt_exp_smul_zero (hN := hN) ⟨y, hy⟩ hw).deriv
  simp only [geoFlow, zero_smul, exp_zero hy]
  rw [this]

/-! ### Continuing geodesics -/

/-- **Continuing a geodesic** (the gluing behind maximal geodesics, which Milnor uses without
comment when he speaks of extending geodesics, p. 62): suppose `t ↦ exp_y(tw)` is a geodesic on an
open interval `I ∋ 0`, let `s ∈ I`, and let `(y', w')` be its position and velocity at time `s`.
If `t ↦ exp_{y'}(tw')` is a geodesic on an open interval `J ∋ 0`, then `t ↦ exp_y(tw)` is a
geodesic on `I ∪ (s + J)`, and `geoFlow (y, w) (s + t) = geoFlow (y', w') t` for `t ∈ J`. -/
theorem isGeodesicOn_exp_smul_union {y w : V} (hy : y ∈ N)
    (hw : w ∈ tangentSubspace hN ⟨y, hy⟩) {I J : Set ℝ}
    (hI : IsGeodesicOn hN (fun t => exp hN y (t • w)) I) (hIc : IsPreconnected I)
    (hI0 : (0 : ℝ) ∈ I) {s : ℝ} (hs : s ∈ I)
    (hJ : IsGeodesicOn hN
      (fun t => exp hN (geoFlow hN (y, w) s).1 (t • (geoFlow hN (y, w) s).2)) J)
    (hJc : IsPreconnected J) (hJ0 : (0 : ℝ) ∈ J) :
    IsGeodesicOn hN (fun t => exp hN y (t • w)) (I ∪ (fun t => t - s) ⁻¹' J) ∧
      ∀ t ∈ J, geoFlow hN (y, w) (s + t) = geoFlow hN (geoFlow hN (y, w) s) t := by
  classical
  set γ₁ : ℝ → V := fun t => exp hN y (t • w) with hγ₁
  set y' := (geoFlow hN (y, w) s).1 with hy'
  set w' := (geoFlow hN (y, w) s).2 with hw'
  have hy'N : y' ∈ N := hI.mem s hs
  have hw'T : w' ∈ tangentSubspace hN ⟨y', hy'N⟩ := hI.deriv_mem hs
  set J' := (fun t => t - s) ⁻¹' J with hJ'
  have hJ'eq : (fun t => 1 * t + -s) ⁻¹' J = J' := by
    ext t
    simp [hJ', sub_eq_add_neg]
  set γ₂ : ℝ → V := fun t => exp hN y' ((t - s) • w') with hγ₂
  have hγ₂geo : IsGeodesicOn hN γ₂ J' := by
    have := hJ.comp_mul_add 1 (-s)
    rw [hJ'eq] at this
    simpa only [one_mul, ← sub_eq_add_neg] using this
  have hJ'c : IsPreconnected J' := by
    rw [← hJ'eq]
    exact isPreconnected_preimage_mul_add hJc 1 (-s)
  have hsJ' : s ∈ J' := by simpa [hJ'] using hJ0
  -- positions and velocities at time `s`
  have hγ₂s : γ₁ s = γ₂ s := by
    simp only [hγ₂, sub_self, zero_smul, exp_zero hy'N]
    rfl
  have hγ₂s' : deriv γ₁ s = deriv γ₂ s := by
    have h1 := hasDerivAt_exp_smul_zero (hN := hN) ⟨y', hy'N⟩ hw'T
    have h2 : HasDerivAt γ₂ w' s := by
      have h1' : HasDerivAt (fun t : ℝ => exp hN y' (t • w')) w' (s - s) := by
        rw [sub_self]; exact h1
      exact h1'.comp_sub_const s s
    rw [h2.deriv]
    rfl
  have hIJ : IsPreconnected (I ∩ J') := by
    have := isPreconnected_iff_ordConnected.1 hIc
    have := isPreconnected_iff_ordConnected.1 hJ'c
    exact isPreconnected_iff_ordConnected.2 inferInstance
  have hIJo : IsOpen (I ∩ J') := hI.isOpen.inter hγ₂geo.isOpen
  have heqIJ : EqOn γ₁ γ₂ (I ∩ J') :=
    (hI.mono hIJo inter_subset_left).eqOn (hγ₂geo.mono hIJo inter_subset_right) hIJ ⟨hs, hsJ'⟩
      hγ₂s hγ₂s'
  -- the glued curve
  set g : ℝ → V := fun t => if t ∈ I then γ₁ t else γ₂ t with hg
  have hgI : EqOn g γ₁ I := fun t ht => by simp only [hg, if_pos ht]
  have hgJ : EqOn g γ₂ J' := fun t ht => by
    by_cases htI : t ∈ I
    · simp only [hg, if_pos htI]
      exact heqIJ ⟨htI, ht⟩
    · simp only [hg, if_neg htI]
  have hggeo : IsGeodesicOn hN g (I ∪ J') :=
    isGeodesicOn_of_locally hN (hI.isOpen.union hγ₂geo.isOpen) fun t ht => by
      rcases ht with ht | ht
      · exact ⟨I, ht, subset_union_left, hI.congr hgI.symm⟩
      · exact ⟨J', ht, subset_union_right, hγ₂geo.congr hgJ.symm⟩
  have hg0 : g 0 = y := by
    rw [hgI hI0]
    simp only [hγ₁, zero_smul, exp_zero hy]
  have hg0' : deriv g 0 = w := by
    have hev : g =ᶠ[𝓝 0] γ₁ := eventually_of_mem (hI.isOpen.mem_nhds hI0) hgI
    rw [hev.deriv_eq]
    exact (hasDerivAt_exp_smul_zero (hN := hN) ⟨y, hy⟩ hw).deriv
  have hU := IsPreconnected.union s hs hsJ' hIc hJ'c
  have heq : EqOn γ₁ g (I ∪ J') := fun t ht => by
    have := hggeo.exp_smul_eq hU (Or.inl hI0) ht
    rwa [hg0, hg0'] at this
  refine ⟨hggeo.congr heq.symm, fun t ht => ?_⟩
  have hst : s + t ∈ J' := by simpa [hJ'] using ht
  have hev : γ₁ =ᶠ[𝓝 (s + t)] γ₂ := by
    filter_upwards [hγ₂geo.isOpen.mem_nhds hst] with t' ht'
    rw [heq (Or.inr ht'), hgJ ht']
  have e1 : γ₁ (s + t) = exp hN y' (t • w') := by
    rw [hev.self_of_nhds]
    simp only [hγ₂, add_sub_cancel_left]
  have e2 : deriv γ₁ (s + t) = deriv (fun t => exp hN y' (t • w')) t := by
    have := deriv_comp_sub_const (f := fun t => exp hN y' (t • w')) (a := s) (x := s + t)
    rw [add_sub_cancel_left] at this
    rw [hev.deriv_eq]
    exact this
  exact Prod.ext e1 e2

/-! ### `exp` is continuous on its domain -/

/-- **`exp` is continuous on its domain, and the domain is open in `TN`** (the global smooth
dependence of geodesics on their initial data, the exposition's Lemma B, which Corollary 10.10
needs).  If the geodesic `γ` with initial data `(p, v)` exists on `[0, 1]`, then so does the one
with initial data `z ∈ TN` near `(p, v)`, and `exp z` depends continuously on `z`.  Proof: cover
the compact arc `γ([0, 1])` by finitely many neighbourhoods on which the local flow of
`Morse.exists_localFlow_exp` exists for a uniform time `2τ₀`, and continue the geodesics with
initial data near `(p, v)` by steps of length `τ₀`, gluing with
`Morse.isGeodesicOn_exp_smul_union`; at each step the position and velocity are a composition of
continuous maps. -/
theorem eventually_mem_expDom_and_continuousWithinAt_exp {p v : V} (h : (p, v) ∈ expDom hN) :
    (∀ᶠ z in 𝓝[Milnor.Problems.tangentBundleSet hN] (p, v), z ∈ expDom hN) ∧
      ContinuousWithinAt (fun z : V × V => exp hN z.1 z.2)
        (Milnor.Problems.tangentBundleSet hN) (p, v) := by
  set TN := Milnor.Problems.tangentBundleSet hN with hTN
  obtain ⟨γ, hγ⟩ := h
  have hpN : p ∈ N := hγ.mem
  obtain ⟨δ₀, hδ₀, hγo, hγ0, hγ0'⟩ := hγ
  have hI0 : (0 : ℝ) ∈ Ioo (-δ₀) (1 + δ₀) := ⟨by linarith, by linarith⟩
  have hv : v ∈ tangentSubspace hN ⟨p, hpN⟩ := by
    have := hγo.deriv_mem hI0
    rw [hγ0'] at this
    convert this using 2
    exact Subtype.ext hγ0.symm
  have hpvT : (p, v) ∈ TN := ⟨hpN, hv⟩
  -- the curve `t ↦ exp_p(tv)` is `γ`
  have hc : EqOn (fun t => exp hN p (t • v)) γ (Ioo (-δ₀) (1 + δ₀)) := by
    have := hγo.eqOn_exp_smul isPreconnected_Ioo hI0
    rwa [hγ0, hγ0'] at this
  have hflowγ : ∀ s ∈ Ioo (-δ₀) (1 + δ₀), geoFlow hN (p, v) s = (γ s, deriv γ s) := by
    intro s hs
    have hev : (fun t => exp hN p (t • v)) =ᶠ[𝓝 s] γ :=
      eventually_of_mem (isOpen_Ioo.mem_nhds hs) hc
    exact Prod.ext (hc hs) hev.deriv_eq
  have hγN : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ N := fun s hs =>
    hγo.mem s ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hspeed : ∀ s ∈ Ioo (-δ₀) (1 + δ₀), ‖deriv γ s‖ = ‖v‖ := fun s hs => by
    rw [hγo.norm_deriv_eq isPreconnected_Ioo hs hI0, hγ0']
  set R := ‖v‖ + 1 with hR
  have hR0 : 0 < R := by positivity
  -- local flows along `γ([0, 1])`, with a uniform time
  choose U hU hxU τ hτ Φ hΦ hflow using fun x : N => exists_localFlow_exp hN x hR0
  have hK : IsCompact (γ '' Icc 0 1) := isCompact_Icc.image_of_continuousOn
    (hγo.contDiffOn.continuousOn.mono fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover (fun x : N => U x) (fun x => hU x) fun y hy => by
    obtain ⟨s, hs, rfl⟩ := hy
    exact mem_iUnion.2 ⟨⟨γ s, hγN s hs⟩, hxU _⟩
  have hcov : ∀ s ∈ Icc (0 : ℝ) 1, ∃ i ∈ F, γ s ∈ U i := fun s hs => by
    have := hF (mem_image_of_mem γ hs)
    simpa only [mem_iUnion, exists_prop] using this
  have hFne : F.Nonempty := by
    obtain ⟨i, hi, -⟩ := hcov 0 ⟨le_rfl, zero_le_one⟩
    exact ⟨i, hi⟩
  have hinf : 0 < F.inf' hFne τ := (Finset.lt_inf'_iff hFne).2 fun i _ => hτ i
  set τ₀ := F.inf' hFne τ / 2 with hτ₀_def
  have hτ₀ : 0 < τ₀ := by positivity
  have hτ₀lt : ∀ i ∈ F, τ₀ < τ i := fun i hi => by
    have := Finset.inf'_le τ hi
    rw [hτ₀_def]
    linarith
  -- the statement proved by induction: geodesics with initial data near `(p, v)` exist on
  -- `[0, s]`, and their position and velocity at time `s` depend continuously on the data
  let P : ℝ → Prop := fun s =>
    (∀ᶠ z in 𝓝[TN] (p, v), ∃ δ > 0,
      IsGeodesicOn hN (fun t => exp hN z.1 (t • z.2)) (Ioo (-δ) (s + δ))) ∧
    ContinuousWithinAt (fun z => geoFlow hN z s) TN (p, v)
  have hTNev : ∀ᶠ z in 𝓝[TN] (p, v), z ∈ TN := self_mem_nhdsWithin
  have hRev : ∀ᶠ z in 𝓝[TN] (p, v), ‖z.2‖ < R := by
    have : ∀ᶠ z in 𝓝 (p, v), ‖z.2‖ < R :=
      (continuous_snd.norm.continuousAt (x := (p, v))).eventually
        (gt_mem_nhds (by simp only [hR]; linarith))
    exact nhdsWithin_le_nhds this
  have hP0 : P 0 := by
    have hUev : ∀ᶠ z in 𝓝[TN] (p, v), z.1 ∈ U ⟨p, hpN⟩ :=
      nhdsWithin_le_nhds (continuous_fst.continuousAt.eventually ((hU _).mem_nhds (hxU _)))
    refine ⟨?_, ?_⟩
    · filter_upwards [hTNev, hRev, hUev] with z hzT hzR hzU
      obtain ⟨hz1, hz2⟩ := hzT
      refine ⟨τ ⟨p, hpN⟩, hτ _, ?_⟩
      have := (hflow ⟨p, hpN⟩ ⟨z.1, hz1⟩ hzU z.2 hz2 hzR).1
      simpa only [zero_add] using this
    · refine continuousWithinAt_id.congr (fun z hz => ?_) (geoFlow_zero hpN hv)
      obtain ⟨hz1, hz2⟩ := hz
      exact geoFlow_zero hz1 hz2
  -- one step of length `≤ τ₀`
  have hstep : ∀ s ∈ Ico (0 : ℝ) 1, P s → P (min (s + τ₀) 1) := by
    rintro s ⟨hs0, hs1⟩ ⟨hPev, hPc⟩
    set s' := min (s + τ₀) 1 with hs'
    set h := s' - s with hh
    have hh0 : 0 < h := by
      rw [hh, hs']
      exact sub_pos.2 (lt_min (by linarith) hs1)
    have hhτ : h ≤ τ₀ := by
      rw [hh, hs']
      linarith [min_le_left (s + τ₀) 1]
    have hsI : s ∈ Ioo (-δ₀) (1 + δ₀) := ⟨by linarith, by linarith⟩
    obtain ⟨i, hiF, hγsU⟩ := hcov s ⟨hs0, hs1.le⟩
    have hτi := hτ₀lt i hiF
    have hpt : geoFlow hN (p, v) s = (γ s, deriv γ s) := hflowγ s hsI
    have hUev : ∀ᶠ z in 𝓝[TN] (p, v), (geoFlow hN z s).1 ∈ U i := by
      have h1 : ContinuousWithinAt (fun z => (geoFlow hN z s).1) TN (p, v) := hPc.fst
      refine h1.eventually_mem ((hU i).mem_nhds ?_)
      change (geoFlow hN (p, v) s).1 ∈ U i
      rw [hpt]
      exact hγsU
    have hglue : ∀ᶠ z in 𝓝[TN] (p, v), (∃ δ > 0,
        IsGeodesicOn hN (fun t => exp hN z.1 (t • z.2)) (Ioo (-δ) (s' + δ))) ∧
        geoFlow hN z s' = Φ i ((geoFlow hN z s).1, (geoFlow hN z s).2, h) := by
      filter_upwards [hTNev, hRev, hPev, hUev] with z hzT hzR hzgeo hzU
      obtain ⟨δ, hδ, hzgeo⟩ := hzgeo
      obtain ⟨hz1, hz2⟩ := hzT
      have hsI' : s ∈ Ioo (-δ) (s + δ) := ⟨by linarith, by linarith⟩
      have h0I : (0 : ℝ) ∈ Ioo (-δ) (s + δ) := ⟨by linarith, by linarith⟩
      have hy'N : (geoFlow hN z s).1 ∈ N := hzgeo.mem s hsI'
      have hw'T : (geoFlow hN z s).2 ∈ tangentSubspace hN ⟨(geoFlow hN z s).1, hy'N⟩ :=
        hzgeo.deriv_mem hsI'
      have hw'R : ‖(geoFlow hN z s).2‖ < R := by
        have h1 : ‖(geoFlow hN z s).2‖ = ‖deriv (fun t : ℝ => exp hN z.1 (t • z.2)) 0‖ :=
          hzgeo.norm_deriv_eq isPreconnected_Ioo hsI' h0I
        rw [h1, (hasDerivAt_exp_smul_zero (hN := hN) ⟨z.1, hz1⟩ hz2).deriv]
        exact hzR
      obtain ⟨hJgeo, -, hJflow⟩ := hflow i ⟨_, hy'N⟩ hzU _ hw'T hw'R
      have hJ0 : (0 : ℝ) ∈ Ioo (-τ i) (τ i) := ⟨by linarith [hτ i], hτ i⟩
      obtain ⟨hgeo', hflow'⟩ := isGeodesicOn_exp_smul_union hz1 hz2 hzgeo isPreconnected_Ioo h0I
        hsI' hJgeo isPreconnected_Ioo hJ0
      have hhJ : h ∈ Ioo (-τ i) (τ i) := ⟨by linarith, by linarith⟩
      refine ⟨⟨min δ (τ i - τ₀), lt_min hδ (by linarith), hgeo'.mono isOpen_Ioo ?_⟩, ?_⟩
      · intro t ht
        have h1 := min_le_left δ (τ i - τ₀)
        have h2 := min_le_right δ (τ i - τ₀)
        have hs's : s' = s + h := by rw [hh]; ring
        rcases lt_or_ge t (s + δ) with hts | hts
        · exact Or.inl ⟨by linarith [ht.1], hts⟩
        · refine Or.inr ⟨?_, ?_⟩
          · change -τ i < t - s
            linarith
          · change t - s < τ i
            linarith [ht.2]
      · have hs's : s' = s + h := by rw [hh]; ring
        rw [hs's, hflow' h hhJ]
        exact hJflow h hhJ
    refine ⟨hglue.mono fun z hz => hz.1, ?_⟩
    have hΦc : ContinuousAt (Φ i) (γ s, deriv γ s, h) := by
      refine (hΦ i).continuousAt (IsOpen.mem_nhds ((hU i).prod (isOpen_ball.prod isOpen_Ioo))
        ⟨hγsU, ?_, ?_⟩)
      · rw [mem_ball, dist_zero_right, hspeed s hsI]
        linarith
      · exact ⟨by linarith, by linarith⟩
    have hin : ContinuousWithinAt (fun z => ((geoFlow hN z s).1, (geoFlow hN z s).2, h)) TN
        (p, v) := hPc.fst.prodMk (hPc.snd.prodMk continuousWithinAt_const)
    have hpt' : ((geoFlow hN (p, v) s).1, (geoFlow hN (p, v) s).2, h) = (γ s, deriv γ s, h) := by
      rw [hpt]
    rw [← hpt'] at hΦc
    exact (ContinuousAt.comp_continuousWithinAt
      (f := fun z => ((geoFlow hN z s).1, (geoFlow hN z s).2, h)) (x := (p, v)) hΦc hin)
      |>.congr_of_eventuallyEq (hglue.mono fun z hz => hz.2) (hglue.self_of_nhdsWithin hpvT).2
  -- iterate
  have hiter : ∀ k : ℕ, P (min (k * τ₀) 1) := by
    intro k
    induction k with
    | zero => simpa using hP0
    | succ k ih =>
      by_cases hk : 1 ≤ (k : ℝ) * τ₀
      · have h1 : min ((k : ℝ) * τ₀) 1 = 1 := min_eq_right hk
        have h2 : min (((k + 1 : ℕ) : ℝ) * τ₀) 1 = 1 := min_eq_right (by push_cast; nlinarith)
        rw [h2]
        rw [h1] at ih
        exact ih
      · push Not at hk
        have h1 : min ((k : ℝ) * τ₀) 1 = k * τ₀ := min_eq_left hk.le
        rw [h1] at ih
        have := hstep (k * τ₀) ⟨by positivity, hk⟩ ih
        have h2 : ((k + 1 : ℕ) : ℝ) * τ₀ = k * τ₀ + τ₀ := by push_cast; ring
        rw [h2]
        exact this
  obtain ⟨k, hk⟩ := exists_nat_ge (1 / τ₀)
  have hP1 : P 1 := by
    have := hiter k
    rwa [min_eq_right] at this
    rw [div_le_iff₀ hτ₀] at hk
    linarith
  obtain ⟨hP1ev, hP1c⟩ := hP1
  refine ⟨?_, ?_⟩
  · filter_upwards [hTNev, hP1ev] with z hzT hz
    obtain ⟨δ, hδ, hzgeo⟩ := hz
    obtain ⟨hz1, hz2⟩ := hzT
    exact ⟨fun t => exp hN z.1 (t • z.2), δ, hδ, hzgeo, by simp only [zero_smul, exp_zero hz1],
      (hasDerivAt_exp_smul_zero (hN := hN) ⟨z.1, hz1⟩ hz2).deriv⟩
  · have : (fun z : V × V => exp hN z.1 z.2) = fun z => (geoFlow hN z 1).1 := by
      funext z
      simp only [geoFlow, one_smul]
    rw [this]
    exact hP1c.fst

/-- **`exp_p` is continuous on `T_pN`** when it is defined on all of `T_pN`. -/
theorem continuousOn_exp {p : N} (hp : ∀ v ∈ tangentSubspace hN p, ((p : V), v) ∈ expDom hN) :
    ContinuousOn (fun v => exp hN p v) (tangentSubspace hN p) := by
  intro v hv
  exact (eventually_mem_expDom_and_continuousWithinAt_exp (hp v hv)).2.comp
    (continuousWithinAt_const.prodMk continuousWithinAt_id) fun w hw => ⟨p.2, hw⟩

/-! ### Geodesic completeness -/

variable (hN) in
/-- **Geodesic completeness** (Milnor, p. 58): `exp_q(v)` is defined for every `q ∈ N` and every
`v ∈ T_qN`.  Equivalently (p. 62), every geodesic extends to all of `ℝ`
(`Morse.isGeodesicallyComplete_iff`). -/
def IsGeodesicallyComplete : Prop :=
  ∀ q : N, ∀ v ∈ tangentSubspace hN q, ((q : V), v) ∈ expDom hN

/-- **If `exp_q` is defined on all of `T_qN`, the geodesics through `q` are defined on `ℝ`**:
`t ↦ exp_q(tv)` is a geodesic on `ℝ` for every `v ∈ T_qN`. -/
theorem isGeodesicOn_univ_exp_smul {q : N}
    (hq : ∀ v ∈ tangentSubspace hN q, ((q : V), v) ∈ expDom hN) {v : V}
    (hv : v ∈ tangentSubspace hN q) :
    IsGeodesicOn hN (fun t => exp hN q (t • v)) univ := by
  -- near `[0, T]`, for every `T > 0` and every `w ∈ T_qN`
  have key : ∀ T : ℝ, 0 < T → ∀ w ∈ tangentSubspace hN q, ∃ δ > 0,
      IsGeodesicOn hN (fun t => exp hN q (t • w)) (Ioo (-δ) (T + δ)) := by
    intro T hT w hw
    obtain ⟨γ, hγ⟩ := hq (T • w) (Submodule.smul_mem _ _ hw)
    change IsGeodesicFrom hN γ (q : V) (T • w) at hγ
    obtain ⟨δ, hδ, hgeo, hexp⟩ := hγ.exp_smul
    have hη := hgeo.comp_mul_add T⁻¹ 0
    have hsub : (fun t => T⁻¹ * t + 0) ⁻¹' Ioo (-δ) (1 + δ) = Ioo (-(T * δ)) (T + T * δ) := by
      ext t
      simp only [mem_preimage, add_zero, mem_Ioo]
      rw [lt_inv_mul_iff₀ hT, inv_mul_lt_iff₀ hT]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith
    rw [hsub] at hη
    refine ⟨T * δ, by positivity, hη.congr fun t ht => ?_⟩
    have ht' : T⁻¹ * t + 0 ∈ Ioo (-δ) (1 + δ) := by rw [← hsub] at ht; exact ht
    have h1 : exp hN q ((T⁻¹ * t + 0) • (T • w)) = γ (T⁻¹ * t + 0) := (hexp _ ht').2
    have h2 : (T⁻¹ * t + 0) • (T • w) = t • w := by
      rw [smul_smul, add_zero, mul_comm T⁻¹ t, mul_assoc, inv_mul_cancel₀ hT.ne', mul_one]
    change γ (T⁻¹ * t + 0) = exp hN q (t • w)
    rw [← h1, h2]
  refine isGeodesicOn_of_locally hN isOpen_univ fun t _ => ?_
  rcases le_or_gt 0 t with ht | ht
  · obtain ⟨δ, hδ, hg⟩ := key (t + 1) (by linarith) v hv
    exact ⟨Ioo (-δ) (t + 1 + δ), ⟨by linarith, by linarith⟩, subset_univ _, hg⟩
  · obtain ⟨δ, hδ, hg⟩ := key (-t + 1) (by linarith) (-v) (neg_mem hv)
    have hg' := hg.comp_mul_add (-1) 0
    refine ⟨(fun s => -1 * s + 0) ⁻¹' Ioo (-δ) (-t + 1 + δ), ?_, subset_univ _,
      hg'.congr fun s _ => ?_⟩
    · simp only [mem_preimage, mem_Ioo]
      constructor <;> linarith
    · simp only [smul_neg, neg_smul, neg_neg, add_zero, neg_one_mul]

/-- **Geodesic completeness, Milnor's second form** (p. 62: "every geodesic segment can be
extended indefinitely"): `N` is geodesically complete iff every geodesic on an open interval is
the restriction of a geodesic on `ℝ`. -/
theorem isGeodesicallyComplete_iff :
    IsGeodesicallyComplete hN ↔ ∀ (γ : ℝ → V) (s : Set ℝ), IsGeodesicOn hN γ s →
      IsPreconnected s → s.Nonempty → ∃ γ' : ℝ → V, IsGeodesicOn hN γ' univ ∧ EqOn γ' γ s := by
  constructor
  · intro h γ s hγ hs ⟨t₀, ht₀⟩
    set q : N := ⟨γ t₀, hγ.mem t₀ ht₀⟩
    have hv : deriv γ t₀ ∈ tangentSubspace hN q := hγ.deriv_mem ht₀
    have hg := (isGeodesicOn_univ_exp_smul (h q) hv).comp_mul_add 1 (-t₀)
    simp only [preimage_univ, one_mul, ← sub_eq_add_neg] at hg
    refine ⟨_, hg, ?_⟩
    have h0 : exp hN q ((t₀ - t₀) • deriv γ t₀) = γ t₀ := by
      rw [sub_self, zero_smul, exp_zero q.2]
    have h0' : deriv (fun t => exp hN q ((t - t₀) • deriv γ t₀)) t₀ = deriv γ t₀ := by
      have h1 := hasDerivAt_exp_smul_zero q hv
      have h1' : HasDerivAt (fun t : ℝ => exp hN q (t • deriv γ t₀)) (deriv γ t₀) (t₀ - t₀) := by
        rw [sub_self]; exact h1
      exact (h1'.comp_sub_const t₀ t₀).deriv
    exact (hg.mono hγ.isOpen (subset_univ _)).eqOn hγ hs ht₀ h0 h0'
  · intro h q v hv
    obtain ⟨τ, hτ, hgeo, hd⟩ := exists_isGeodesicOn_exp_smul q hv
    obtain ⟨γ', hγ', heq⟩ := h _ _ hgeo isPreconnected_Ioo ⟨0, by simp [hτ]⟩
    have h0 : (0 : ℝ) ∈ Ioo (-τ) τ := ⟨by linarith, hτ⟩
    have hev : γ' =ᶠ[𝓝 0] fun t => exp hN q (t • v) :=
      eventually_of_mem (isOpen_Ioo.mem_nhds h0) heq
    refine ⟨γ', 1, one_pos, hγ'.mono isOpen_Ioo (subset_univ _), ?_, ?_⟩
    · rw [heq h0]
      simp only [zero_smul, exp_zero q.2]
    · rw [hev.deriv_eq, hd.deriv]

/-- **Metric completeness implies geodesic completeness** (Milnor, p. 64: "not difficult, using
Lemma 10.3", with the details left to Hopf and Rinow; the proof is the exposition's, and uses only
the uniform local existence of Lemma 10.2).  If the geodesic `t ↦ exp_q(tv)` existed only on
`[0, T₀)`, its points at times `tₙ ↑ T₀` would form a `ρ`-Cauchy sequence (`ρ(γ(t), γ(t')) ≤
‖v‖ |t − t'|`), converging to some `x ∈ N`; the geodesics with initial data near `x` and speed
`‖v‖` all exist for a uniform time `τ` (`Morse.exists_localFlow_exp`), so the geodesic continues
past `T₀` (`Morse.isGeodesicOn_exp_smul_union`). -/
theorem isGeodesicallyComplete_of_isRiemComplete (h : IsRiemComplete N) :
    IsGeodesicallyComplete hN := by
  intro q v hv
  set c : ℝ → V := fun t => exp hN q (t • v) with hc_def
  set A : Set ℝ := {T | 0 ≤ T ∧ ∃ δ > 0, IsGeodesicOn hN c (Ioo (-δ) (T + δ))} with hA_def
  suffices h1 : (1 : ℝ) ∈ A by
    obtain ⟨-, δ, hδ, hgeo⟩ := h1
    exact ⟨c, δ, hδ, hgeo, by simp only [hc_def, zero_smul, exp_zero q.2],
      (hasDerivAt_exp_smul_zero q hv).deriv⟩
  by_contra h1
  have hdown : ∀ T ∈ A, ∀ T', 0 ≤ T' → T' ≤ T → T' ∈ A := by
    rintro T ⟨-, δ, hδ, hg⟩ T' hT' hle
    exact ⟨hT', δ, hδ, hg.mono isOpen_Ioo (Ioo_subset_Ioo le_rfl (by linarith))⟩
  have hA1 : ∀ T ∈ A, T < 1 := fun T hT => by
    by_contra hle
    exact h1 (hdown T hT 1 zero_le_one (not_lt.1 hle))
  obtain ⟨τq, hτq, hgq, -⟩ := exists_isGeodesicOn_exp_smul q hv
  have hA0 : (0 : ℝ) ∈ A := ⟨le_rfl, τq, hτq, by simpa only [zero_add] using hgq⟩
  have hbdd : BddAbove A := ⟨1, fun T hT => (hA1 T hT).le⟩
  set T₀ := sSup A with hT₀_def
  have hT₀pos : 0 < T₀ := by
    have hm : min (τq / 2) (1 / 2) ∈ A := by
      refine ⟨by positivity, τq / 2, by positivity, hgq.mono isOpen_Ioo
        (Ioo_subset_Ioo (by linarith) ?_)⟩
      linarith [min_le_left (τq / 2) (1 / 2)]
    exact lt_of_lt_of_le (by positivity) (le_csSup hbdd hm)
  -- below `T₀` the curve is a geodesic of speed `‖v‖`
  have hgeoAt : ∀ t, 0 ≤ t → t < T₀ → ∃ δ > 0, ∃ T, t < T ∧
      IsGeodesicOn hN c (Ioo (-δ) (T + δ)) := by
    intro t ht0 ht
    obtain ⟨T, ⟨-, δ, hδ, hg⟩, hT⟩ := exists_lt_of_lt_csSup ⟨0, hA0⟩ ht
    exact ⟨δ, hδ, T, hT, hg⟩
  have hcN : ∀ t, 0 ≤ t → t < T₀ → c t ∈ N := fun t ht0 ht => by
    obtain ⟨δ, hδ, T, hT, hg⟩ := hgeoAt t ht0 ht
    exact hg.mem t ⟨by linarith, by linarith⟩
  have hdist : ∀ t t', 0 ≤ t → t ≤ t' → t' < T₀ →
      riemDist (N := N) (c t) (c t') ≤ ENNReal.ofReal (‖v‖ * (t' - t)) := by
    intro t t' ht htt' ht'
    obtain ⟨δ, hδ, T, hT, hg⟩ := hgeoAt t' (by linarith) ht'
    have hsub : Icc t t' ⊆ Ioo (-δ) (T + δ) := Icc_subset_Ioo (by linarith) (by linarith)
    have h0 : (0 : ℝ) ∈ Ioo (-δ) (T + δ) := ⟨by linarith, by linarith⟩
    have := riemDist_le_pathLength (N := N)
      (IsPiecewiseSmooth.of_contDiffOn hg.contDiffOn htt' hsub) fun s hs => hg.mem s (hsub hs)
    rwa [hg.pathLength_eq isPreconnected_Ioo htt' hsub h0, (hasDerivAt_exp_smul_zero q hv).deriv]
      at this
  have hdist' : ∀ t t', 0 ≤ t → t < T₀ → 0 ≤ t' → t' < T₀ →
      riemDist (N := N) (c t) (c t') ≤ ENNReal.ofReal (‖v‖ * |t' - t|) := by
    intro t t' ht htT ht' ht'T
    rcases le_total t t' with hle | hle
    · rw [abs_of_nonneg (by linarith)]
      exact hdist t t' ht hle ht'T
    · rw [riemDist_comm, abs_of_nonpos (by linarith), neg_sub]
      exact hdist t' t ht' hle htT
  -- the Cauchy sequence `c(tₙ)`, `tₙ = T₀ − T₀/(n + 2)`
  set tn : ℕ → ℝ := fun n => T₀ - T₀ / ((n : ℝ) + 2) with htn_def
  have htn0 : ∀ n, 0 ≤ tn n := fun n => by
    simp only [htn_def, sub_nonneg]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have htnT : ∀ n, tn n < T₀ := fun n => by
    simp only [htn_def]
    have : 0 < T₀ / ((n : ℝ) + 2) := by positivity
    linarith
  have htn_lim : Tendsto tn atTop (𝓝 T₀) := by
    have h1 : Tendsto (fun n : ℕ => T₀ / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (2 : ℝ)))
      exact this.const_div_atTop T₀
    simpa using (tendsto_const_nhds (x := T₀)).sub h1
  obtain ⟨x, hxN, hx⟩ := h (fun n => c (tn n)) (fun n => hcN _ (htn0 n) (htnT n)) fun ε hε => by
    obtain ⟨n₀, hn₀⟩ := Metric.cauchySeq_iff.1 htn_lim.cauchySeq (ε / (‖v‖ + 1)) (by positivity)
    refine ⟨n₀, fun m hm n hn => (hdist' _ _ (htn0 m) (htnT m) (htn0 n) (htnT n)).trans_lt ?_⟩
    rw [ENNReal.ofReal_lt_ofReal_iff hε]
    have h1 : |tn n - tn m| < ε / (‖v‖ + 1) := by
      have := hn₀ n hn m hm
      rwa [Real.dist_eq] at this
    calc ‖v‖ * |tn n - tn m| ≤ (‖v‖ + 1) * |tn n - tn m| := by
          gcongr; linarith
      _ < (‖v‖ + 1) * (ε / (‖v‖ + 1)) := by gcongr
      _ = ε := by field_simp
  -- the uniform local flow near the limit point
  obtain ⟨U, hU, hxU, τ, hτ, Φ, -, hflow⟩ :=
    exists_localFlow_exp hN ⟨x, hxN⟩ (R := ‖v‖ + 1) (by positivity)
  have hev1 : ∀ᶠ n in atTop, c (tn n) ∈ U := by
    obtain ⟨r, hr, hrU⟩ := (hasBasis_nhdsWithin_riemDist hN ⟨x, hxN⟩).mem_iff.1
      (mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hxU))
    filter_upwards [hx.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hr))] with n hn
    apply hrU
    change riemDist (N := N) x (c (tn n)) < ENNReal.ofReal r
    rwa [riemDist_comm]
  have hev2 : ∀ᶠ n in atTop, T₀ - τ / 2 < tn n :=
    htn_lim.eventually (lt_mem_nhds (by linarith))
  obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
  -- continue the geodesic past `T₀`
  obtain ⟨δ, hδ, T, hT, hg⟩ := hgeoAt (tn n) (htn0 n) (htnT n)
  have hsI : tn n ∈ Ioo (-δ) (T + δ) := ⟨by linarith [htn0 n], by linarith⟩
  have h0I : (0 : ℝ) ∈ Ioo (-δ) (T + δ) := ⟨by linarith, by linarith [htn0 n]⟩
  have hyN : (geoFlow hN ((q : V), v) (tn n)).1 ∈ N := hg.mem _ hsI
  have hwT : (geoFlow hN ((q : V), v) (tn n)).2 ∈
      tangentSubspace hN ⟨(geoFlow hN ((q : V), v) (tn n)).1, hyN⟩ := hg.deriv_mem hsI
  have hwR : ‖(geoFlow hN ((q : V), v) (tn n)).2‖ < ‖v‖ + 1 := by
    have h1 : ‖(geoFlow hN ((q : V), v) (tn n)).2‖ = ‖deriv c 0‖ :=
      hg.norm_deriv_eq isPreconnected_Ioo hsI h0I
    rw [h1, (hasDerivAt_exp_smul_zero q hv).deriv]
    linarith
  obtain ⟨hJgeo, -, -⟩ := hflow ⟨_, hyN⟩ hn1 _ hwT hwR
  have hJ0 : (0 : ℝ) ∈ Ioo (-τ) τ := ⟨by linarith, hτ⟩
  obtain ⟨hgeo', -⟩ := isGeodesicOn_exp_smul_union q.2 hv hg isPreconnected_Ioo h0I hsI hJgeo
    isPreconnected_Ioo hJ0
  have hnew : T₀ + τ / 4 ∈ A := by
    refine ⟨by linarith, min δ (τ / 4), lt_min hδ (by linarith), hgeo'.mono isOpen_Ioo ?_⟩
    intro t ht
    have h1 := min_le_left δ (τ / 4)
    have h2 := min_le_right δ (τ / 4)
    rcases lt_or_ge t (T + δ) with hts | hts
    · exact Or.inl ⟨by linarith [ht.1], hts⟩
    · refine Or.inr ⟨?_, ?_⟩
      · change -τ < t - tn n
        linarith
      · change t - tn n < τ
        linarith [ht.2]
  have := le_csSup hbdd hnew
  linarith

end Morse
