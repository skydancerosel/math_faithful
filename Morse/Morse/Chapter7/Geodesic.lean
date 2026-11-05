import Morse.Chapter6.Parallel
import Morse.Chapter7.ODE

/-!
Milnor, *Morse Theory*, §10, pp. 55–57, for a submanifold `N ⊆ ℝᴷ` with the induced metric.

# Geodesics

## Milnor's text, paraphrased

* **Definition** (p. 55).  On a connected Riemannian manifold `M`, a parametrized path `γ : I → M`
  (`I` any interval of real numbers) is a *geodesic* if its acceleration `D/dt (dγ/dt)` vanishes
  identically: the velocity field is parallel along `γ`.  Then
  `d/dt ⟨dγ/dt, dγ/dt⟩ = 2 ⟨D/dt dγ/dt, dγ/dt⟩ = 0`, so the speed `‖dγ/dt‖` is constant, and the
  parameter is a linear function of arc length (it is arc length iff the speed is `1`).
* In a coordinate system the geodesic equation is a system of second-order differential equations
  (p. 55), so existence and uniqueness depend on Theorem 10.1 (`Morse/Chapter7/ODE.lean`).
* **Homogeneity** (p. 57): if `t ↦ γ(t)` is a geodesic, so is `t ↦ γ(ct)` for every constant `c`.

## The embedded setting

`N ⊆ V` is a slice submanifold (`Milnor.IsSliceSubmanifold`) of a finite-dimensional inner product
space `V` (Milnor's `ℝᴷ`), with the induced metric, as in `Morse/Chapter6/`.  There the covariant
derivative along a curve is `D/dt = P ∘ d/dt` (`Morse.covDeriv`), `P_q` the orthogonal projection
onto `T_qN`; so a geodesic is a curve in `N` whose acceleration in `V` is **normal** to `N`: the
motion of a particle constrained to `N` and subject to no other force.

* `Morse.IsGeodesicOn hN γ s`: `γ : ℝ → V` is smooth on the open set `s ⊆ ℝ`, maps `s` into `N`,
  and `γ''(t) ⊥ T_{γ(t)}N` for `t ∈ s`.  For a smooth curve `c : ℝ → N` this is Milnor's
  definition `D/dt (dc/dt) = 0` (`Morse.isGeodesicOn_univ_iff_covDeriv`).
* **The geodesic equation** `γ'' = II(γ', γ')`, `II` the second fundamental form
  (`Morse.IsGeodesicOn.deriv_deriv_eq`, `Morse.isGeodesicOn_of_deriv_deriv_eq`).  As a first-order
  system on the tangent bundle `TN ⊆ V × V` it is `(x, v)' = (v, II_x(v, v))`: geodesics are the
  projections of the integral curves in `TN` of the geodesic spray `Morse.geodesicSpray`
  (`Morse.isGeodesicOn_iff_hasDerivAt_geodesicSpray`, `Morse.IsGeodesicOn.mem_tangentBundleSet`).
* **Constant speed** (p. 55): `Morse.IsGeodesicOn.norm_deriv_eq`.
* **Homogeneity** (p. 57): `Morse.IsGeodesicOn.comp_mul_add`: `t ↦ γ(at + b)` is a geodesic.
* **Uniqueness**: `Morse.IsGeodesicOn.eqOn`: two geodesics on an open interval with the same
  position and velocity at one time coincide.  Near a time `t₀` (`Morse.IsGeodesicOn.eventuallyEq`)
  the lifts `(γ, γ')` both solve `(x, v)' = (v, dQ_x(v) v)`, where `Q = Morse.projRep σ` is the
  smooth extension of `x ↦ P_x` to an open set of `V` given by a slice chart `σ` at `γ(t₀)`: on
  `TN` this field is `(v, II_x(v, v))`, and it is smooth near the lifts, so Grönwall's inequality
  applies (`Morse.ode_eventuallyEq`).  The global statement follows by connectedness.
* Local existence, and Lemma 10.2, are in `Morse/Chapter7/GeodesicLocal.lean`.

## What Milnor leaves implicit

* **Uniqueness beyond one chart.**  Theorem 10.1 gives uniqueness only for small times inside one
  coordinate neighbourhood; Milnor's "the unique geodesic" needs the connectedness argument of
  `Morse.IsGeodesicOn.eqOn` (on an abstract manifold also the Hausdorff property, automatic for
  `N ⊆ V`).
* **Closed intervals.**  Milnor allows any interval, `[0, 1]` in the definition of `exp` (p. 57),
  with one-sided derivatives at the ends.  Here geodesics live on open sets; a geodesic on `[0, 1]`
  extends a little beyond its ends by local existence, so `exp` is defined in
  `Morse/Chapter7/Exp.lean` with geodesics on open intervals containing `[0, 1]`.
* **The equation as an ODE.**  The right side of `γ'' = II(γ', γ')` involves the derivative of
  `P`, which is defined only along `N`; the smooth local extension `Q` of `P` makes it an ordinary
  differential equation in `V × V`.  (For existence the equation is solved in a chart instead, see
  `Morse/Chapter7/GeodesicLocal.lean`.)
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

/-- Tangent spaces at equal points of `N` are equal. -/
theorem tangentSubspace_congr {x y : V} (hx : x ∈ N) (hy : y ∈ N) (hxy : x = y) :
    tangentSubspace hN ⟨x, hx⟩ = tangentSubspace hN ⟨y, hy⟩ := by
  subst hxy
  rfl

/-! ### Geodesics -/

/-- **A geodesic of `N`** (Milnor, p. 55) on an open set `s ⊆ ℝ` (in practice an open interval):
a curve `γ : ℝ → V`, smooth on `s`, with values in `N` on `s`, whose acceleration `γ''(t)` is
normal to `N` at `γ(t)` for every `t ∈ s`.  For the induced metric this is Milnor's
`D/dt (dγ/dt) = 0` (`Morse.isGeodesicOn_univ_iff_covDeriv`), since `D/dt = P ∘ d/dt`. -/
structure IsGeodesicOn (γ : ℝ → V) (s : Set ℝ) : Prop where
  isOpen : IsOpen s
  mem : ∀ t ∈ s, γ t ∈ N
  contDiffOn : ContDiffOn ℝ ∞ γ s
  normal : ∀ t (ht : t ∈ s), deriv (deriv γ) t ∈ (tangentSubspace hN ⟨γ t, mem t ht⟩)ᗮ

namespace IsGeodesicOn

variable {hN} {γ : ℝ → V} {s : Set ℝ}

theorem contDiffAt (h : IsGeodesicOn hN γ s) {t : ℝ} (ht : t ∈ s) : ContDiffAt ℝ ∞ γ t :=
  h.contDiffOn.contDiffAt (h.isOpen.mem_nhds ht)

theorem hasDerivAt (h : IsGeodesicOn hN γ s) {t : ℝ} (ht : t ∈ s) :
    HasDerivAt γ (deriv γ t) t :=
  ((h.contDiffAt ht).differentiableAt (by simp)).hasDerivAt

theorem contDiffOn_deriv (h : IsGeodesicOn hN γ s) : ContDiffOn ℝ ∞ (deriv γ) s :=
  h.contDiffOn.deriv_of_isOpen h.isOpen (by simp)

theorem hasDerivAt_deriv (h : IsGeodesicOn hN γ s) {t : ℝ} (ht : t ∈ s) :
    HasDerivAt (deriv γ) (deriv (deriv γ) t) t :=
  ((h.contDiffOn_deriv.contDiffAt (h.isOpen.mem_nhds ht)).differentiableAt (by simp)).hasDerivAt

theorem eventually_mem (h : IsGeodesicOn hN γ s) {t : ℝ} (ht : t ∈ s) :
    ∀ᶠ τ in 𝓝 t, γ τ ∈ N :=
  eventually_of_mem (h.isOpen.mem_nhds ht) h.mem

theorem mono (h : IsGeodesicOn hN γ s) {s' : Set ℝ} (hs' : IsOpen s') (hss : s' ⊆ s) :
    IsGeodesicOn hN γ s' where
  isOpen := hs'
  mem t ht := h.mem t (hss ht)
  contDiffOn := h.contDiffOn.mono hss
  normal t ht := h.normal t (hss ht)

/-- Being a geodesic depends only on the values on `s`. -/
theorem congr (h : IsGeodesicOn hN γ s) {γ' : ℝ → V} (heq : EqOn γ γ' s) :
    IsGeodesicOn hN γ' s where
  isOpen := h.isOpen
  mem t ht := heq ht ▸ h.mem t ht
  contDiffOn := h.contDiffOn.congr fun t ht => (heq ht).symm
  normal t ht := by
    have hev : γ =ᶠ[𝓝 t] γ' := eventually_of_mem (h.isOpen.mem_nhds ht) heq
    rw [← hev.deriv.deriv_eq, ← tangentSubspace_congr hN (h.mem t ht) _ (heq ht)]
    exact h.normal t ht

/-- **Homogeneity** (Milnor, p. 57): if `t ↦ γ(t)` is a geodesic, so is `t ↦ γ(at + b)`. -/
theorem comp_mul_add (h : IsGeodesicOn hN γ s) (a b : ℝ) :
    IsGeodesicOn hN (fun t => γ (a * t + b)) ((fun t => a * t + b) ⁻¹' s) := by
  have hcont : Continuous fun t : ℝ => a * t + b := (continuous_const.mul continuous_id).add
    continuous_const
  have hopen : IsOpen ((fun t => a * t + b) ⁻¹' s) := h.isOpen.preimage hcont
  have hlin : ∀ t, HasDerivAt (fun t : ℝ => a * t + b) a t := fun t => by
    simpa using ((hasDerivAt_id t).const_mul a).add_const b
  have hd : ∀ t ∈ (fun t => a * t + b) ⁻¹' s,
      HasDerivAt (fun t => γ (a * t + b)) (a • deriv γ (a * t + b)) t :=
    fun t ht => (h.hasDerivAt ht).scomp t (hlin t)
  refine ⟨hopen, fun t ht => h.mem _ ht, h.contDiffOn.comp
    ((contDiff_const.mul contDiff_id).add contDiff_const).contDiffOn fun t ht => ht,
    fun t ht => ?_⟩
  have hev : deriv (fun t => γ (a * t + b)) =ᶠ[𝓝 t] fun t => a • deriv γ (a * t + b) :=
    eventually_of_mem (hopen.mem_nhds ht) fun τ hτ => (hd τ hτ).deriv
  have h2 : HasDerivAt (fun t => a • deriv γ (a * t + b))
      (a • (a • deriv (deriv γ) (a * t + b))) t :=
    ((h.hasDerivAt_deriv ht).scomp t (hlin t)).const_smul a
  rw [hev.deriv_eq, h2.deriv]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (h.normal _ ht))

end IsGeodesicOn

/-- Constant curves are geodesics. -/
theorem isGeodesicOn_const {q : V} (hq : q ∈ N) {s : Set ℝ} (hs : IsOpen s) :
    IsGeodesicOn hN (fun _ => q) s where
  isOpen := hs
  mem _ _ := hq
  contDiffOn := contDiffOn_const
  normal t _ := by simp only [deriv_const', Submodule.zero_mem]

/-! ### Velocities, the geodesic equation, constant speed and uniqueness -/

variable [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W]

/-- **The velocity of a curve in `N` is tangent to `N`**, for a curve which lies in `N` near the
time considered and is differentiable at that time. -/
theorem hasDerivAt_mem_tangentSubspace {c : ℝ → V} {t : ℝ} {v : V} (hc : HasDerivAt c v t)
    (hmem : ∀ᶠ s in 𝓝 t, c s ∈ N) : v ∈ tangentSubspace hN ⟨c t, hmem.self_of_nhds⟩ := by
  set q : N := ⟨c t, hmem.self_of_nhds⟩
  set σ := sliceAt hN q
  have hq : c t ∈ σ.φ.source := mem_sliceAt_source hN q
  have hφ : HasFDerivAt σ.φ (fderiv ℝ σ.φ (c t)) (c t) :=
    (Milnor.Problems.sliceChart_differentiableAt σ hq).hasFDerivAt
  have hg : HasDerivAt (fun s => (σ.φ (c s)).2) ((fderiv ℝ σ.φ (c t) v).2) t :=
    hasDerivAt_snd_comp (hφ.comp_hasDerivAt t hc)
  have hsrc : ∀ᶠ s in 𝓝 t, c s ∈ σ.φ.source :=
    hc.continuousAt.eventually (σ.φ.open_source.mem_nhds hq)
  have h0 : (fun s => (σ.φ (c s)).2) =ᶠ[𝓝 t] fun _ => (0 : W) := by
    filter_upwards [hmem, hsrc] with s h1 h2
    exact (σ.slice _ h2).1 h1
  have h1 : (fderiv ℝ σ.φ (c t) v).2 = 0 :=
    hg.unique ((hasDerivAt_const t (0 : W)).congr_of_eventuallyEq h0)
  exact (Milnor.Problems.sliceChart_mem_tangentSpace_iff hN σ (a := q) hq v).2 h1

/-- Along a curve `c` in `N` with velocity `v` at `t`, the derivative of `s ↦ Q(c(s))`, where
`Q = projRep σ` (`σ` the slice chart at `c(t)`) is the local extension of `x ↦ P_x`, is
`D_v = dN P (c t) v`. -/
theorem hasDerivAt_projRep_comp {c : ℝ → V} {t : ℝ} {v : V} (hc : HasDerivAt c v t)
    (hmem : ∀ᶠ s in 𝓝 t, c s ∈ N) :
    HasDerivAt (fun s => projRep (sliceAt hN ⟨c t, hmem.self_of_nhds⟩) (c s))
      (dN hN (tanProj hN) ⟨c t, hmem.self_of_nhds⟩ v) t := by
  set q : N := ⟨c t, hmem.self_of_nhds⟩
  have hq := mem_sliceAt_source hN q
  have hQ := (contDiffAt_projRep (sliceAt hN q) hq).differentiableAt (by simp)
  rw [dN_tanProj_eq_fderiv hN (sliceAt hN q) hq (hasDerivAt_mem_tangentSubspace hN hc hmem)]
  exact hQ.hasFDerivAt.comp_hasDerivAt t hc

namespace IsGeodesicOn

variable {hN} {γ : ℝ → V} {s : Set ℝ}

/-- The velocity of a geodesic is tangent to `N`. -/
theorem deriv_mem (h : IsGeodesicOn hN γ s) {t : ℝ} (ht : t ∈ s) :
    deriv γ t ∈ tangentSubspace hN ⟨γ t, h.mem t ht⟩ :=
  hasDerivAt_mem_tangentSubspace hN (h.hasDerivAt ht) (h.eventually_mem ht)

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- `P(γ'') = 0`: Milnor's `D/dt (dγ/dt) = 0`. -/
theorem tanProj_deriv_deriv (h : IsGeodesicOn hN γ s) {t : ℝ} (ht : t ∈ s) :
    tanProj hN ⟨γ t, h.mem t ht⟩ (deriv (deriv γ) t) = 0 :=
  (tanProj_eq_zero_iff hN).2 (h.normal t ht)

/-! ### The geodesic equation -/

/-- **The geodesic equation** for `N ⊆ V`: `γ'' = II(γ', γ')`, where `II` is the second
fundamental form (`Morse.secondFundForm`).  Proof: differentiate `Q(γ) γ' = γ'`, where `Q` is the
local extension of `P`: `II(γ', γ') + P γ'' = γ''`, and `P γ'' = 0`. -/
theorem deriv_deriv_eq (h : IsGeodesicOn hN γ s) {t : ℝ} (ht : t ∈ s) :
    deriv (deriv γ) t = secondFundForm hN ⟨γ t, h.mem t ht⟩ (deriv γ t) (deriv γ t) := by
  set q : N := ⟨γ t, h.mem t ht⟩ with hq_def
  set σ := sliceAt hN q
  have hq : γ t ∈ σ.φ.source := mem_sliceAt_source hN q
  have hQ := hasDerivAt_projRep_comp hN (h.hasDerivAt ht) (h.eventually_mem ht)
  have hsrc : ∀ᶠ τ in 𝓝 t, γ τ ∈ σ.φ.source :=
    (h.hasDerivAt ht).continuousAt.eventually (σ.φ.open_source.mem_nhds hq)
  have hev : (fun τ => projRep σ (γ τ) (deriv γ τ)) =ᶠ[𝓝 t] deriv γ := by
    filter_upwards [eventually_of_mem (h.isOpen.mem_nhds ht) fun τ hτ => hτ, hsrc] with τ hτ hτs
    rw [projRep_eq hN σ (x := ⟨γ τ, h.mem τ hτ⟩) hτs]
    exact tanProj_eq_self hN (h.deriv_mem hτ)
  have h1 := (hQ.clm_apply (h.hasDerivAt_deriv ht)).congr_of_eventuallyEq hev.symm
  have h2 := h1.unique (h.hasDerivAt_deriv ht)
  rw [projRep_eq hN σ (x := q) hq, h.tanProj_deriv_deriv ht, add_zero] at h2
  exact h2.symm

/-- **Constant speed**, infinitesimally: `d/dt ‖γ'‖² = 2 ⟨γ'', γ'⟩ = 0`. -/
theorem hasDerivAt_norm_sq (h : IsGeodesicOn hN γ s) {t : ℝ} (ht : t ∈ s) :
    HasDerivAt (fun τ => ‖deriv γ τ‖ ^ 2) 0 t := by
  have h1 := (h.hasDerivAt_deriv ht).norm_sq
  rwa [Submodule.inner_right_of_mem_orthogonal (h.deriv_mem ht) (h.normal t ht), mul_zero] at h1

/-- **A geodesic has constant speed** (Milnor, p. 55). -/
theorem norm_deriv_eq (h : IsGeodesicOn hN γ s) (hs : IsPreconnected s) {t t' : ℝ} (ht : t ∈ s)
    (ht' : t' ∈ s) : ‖deriv γ t‖ = ‖deriv γ t'‖ := by
  have hc := h.isOpen.is_const_of_deriv_eq_zero hs (f := fun τ => ‖deriv γ τ‖ ^ 2)
    (fun τ hτ => (h.hasDerivAt_norm_sq hτ).differentiableAt.differentiableWithinAt)
    (fun τ hτ => (h.hasDerivAt_norm_sq hτ).deriv) ht ht'
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hc

/-! ### Uniqueness -/

/-- **Local uniqueness of geodesics**: two geodesics with the same position and velocity at `t₀`
agree near `t₀`.  Their lifts `(γ, γ')` solve `(x, v)' = (v, dQ_x(v) v)`, `Q = projRep σ`. -/
theorem eventuallyEq {γ₁ γ₂ : ℝ → V} {s₁ s₂ : Set ℝ} (h₁ : IsGeodesicOn hN γ₁ s₁)
    (h₂ : IsGeodesicOn hN γ₂ s₂) {t₀ : ℝ} (ht₁ : t₀ ∈ s₁) (ht₂ : t₀ ∈ s₂)
    (h0 : γ₁ t₀ = γ₂ t₀) (h0' : deriv γ₁ t₀ = deriv γ₂ t₀) : γ₁ =ᶠ[𝓝 t₀] γ₂ := by
  set q : N := ⟨γ₁ t₀, h₁.mem t₀ ht₁⟩
  set σ := sliceAt hN q
  have hq : γ₁ t₀ ∈ σ.φ.source := mem_sliceAt_source hN q
  set G : V × V → V × V := fun z => (z.2, fderiv ℝ (projRep σ) z.1 z.2 z.2) with hG
  have hGs : ContDiffAt ℝ 1 G (γ₁ t₀, deriv γ₁ t₀) := by
    have hQ : ContDiffAt ℝ ∞ (fderiv ℝ (projRep σ)) (γ₁ t₀) :=
      (contDiffAt_projRep σ (q := q) hq).fderiv_right (m := ∞) (by simp)
    have h1 : ContDiffAt ℝ ∞ (fun z : V × V => fderiv ℝ (projRep σ) z.1)
        (γ₁ t₀, deriv γ₁ t₀) := ContDiffAt.comp (γ₁ t₀, deriv γ₁ t₀) hQ contDiffAt_fst
    exact (contDiffAt_snd.prodMk ((h1.clm_apply contDiffAt_snd).clm_apply contDiffAt_snd)).of_le
      (by exact_mod_cast le_top)
  have hlift : ∀ {γ : ℝ → V} {s : Set ℝ}, IsGeodesicOn hN γ s → t₀ ∈ s → γ t₀ = γ₁ t₀ →
      ∀ᶠ t in 𝓝 t₀, HasDerivAt (fun τ => (γ τ, deriv γ τ)) (G (γ t, deriv γ t)) t := by
    intro γ s h ht hγ
    have hsrc : ∀ᶠ t in 𝓝 t₀, γ t ∈ σ.φ.source :=
      (h.hasDerivAt ht).continuousAt.eventually (σ.φ.open_source.mem_nhds (by rw [hγ]; exact hq))
    filter_upwards [eventually_of_mem (h.isOpen.mem_nhds ht) fun τ hτ => hτ, hsrc] with t hts htσ
    have e := h.deriv_deriv_eq hts
    rw [secondFundForm, dN_tanProj_eq_fderiv hN σ (q := ⟨γ t, h.mem t hts⟩) htσ
      (h.deriv_mem hts)] at e
    have hdd := h.hasDerivAt_deriv hts
    rw [e] at hdd
    exact (h.hasDerivAt hts).prodMk hdd
  have key := ode_eventuallyEq (f := fun τ => (γ₁ τ, deriv γ₁ τ))
    (g := fun τ => (γ₂ τ, deriv γ₂ τ)) hGs (hlift h₁ ht₁ rfl) (hlift h₂ ht₂ h0.symm)
    (by rw [h0, h0'])
  filter_upwards [key] with t ht
  exact congrArg Prod.fst ht

/-- **Uniqueness of geodesics** ("uniqueness in the large", which Milnor uses without comment):
two geodesics on an open interval `s` with the same position and velocity at one time coincide on
`s`. -/
theorem eqOn {γ₁ γ₂ : ℝ → V} (h₁ : IsGeodesicOn hN γ₁ s) (h₂ : IsGeodesicOn hN γ₂ s)
    (hs : IsPreconnected s) {t₀ : ℝ} (ht₀ : t₀ ∈ s) (h0 : γ₁ t₀ = γ₂ t₀)
    (h0' : deriv γ₁ t₀ = deriv γ₂ t₀) : EqOn γ₁ γ₂ s := by
  have key := eqOn_of_eventuallyEq (f := fun t => (γ₁ t, deriv γ₁ t))
    (g := fun t => (γ₂ t, deriv γ₂ t)) h₁.isOpen hs
    (h₁.contDiffOn.continuousOn.prodMk h₁.contDiffOn_deriv.continuousOn)
    (h₂.contDiffOn.continuousOn.prodMk h₂.contDiffOn_deriv.continuousOn)
    (fun t ht he => by
      have e := h₁.eventuallyEq h₂ ht ht (congrArg Prod.fst he) (congrArg Prod.snd he)
      filter_upwards [e, e.deriv] with τ h1 h2
      rw [h1, h2]) ht₀ (by rw [h0, h0'])
  exact fun t ht => congrArg Prod.fst (key ht)



end IsGeodesicOn

/-- **The geodesic equation, converse**: a smooth curve in `N` with `γ'' = II(γ', γ')` is a
geodesic (`II` is normal to `N`). -/
theorem isGeodesicOn_of_deriv_deriv_eq {γ : ℝ → V} {s : Set ℝ} (hs : IsOpen s)
    (hmem : ∀ t ∈ s, γ t ∈ N) (hγ : ContDiffOn ℝ ∞ γ s)
    (heq : ∀ t (ht : t ∈ s), deriv (deriv γ) t =
      secondFundForm hN ⟨γ t, hmem t ht⟩ (deriv γ t) (deriv γ t)) :
    IsGeodesicOn hN γ s := by
  refine ⟨hs, hmem, hγ, fun t ht => ?_⟩
  have hd : HasDerivAt γ (deriv γ t) t :=
    ((hγ.contDiffAt (hs.mem_nhds ht)).differentiableAt (by simp)).hasDerivAt
  have hT := hasDerivAt_mem_tangentSubspace hN hd (eventually_of_mem (hs.mem_nhds ht) hmem)
  rw [heq t ht]
  exact secondFundForm_mem_orthogonal hN hT hT

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **Milnor's definition** (p. 55): a smooth curve `c : ℝ → N` is a geodesic iff its velocity
field is parallel, `D/dt (dc/dt) = 0`, with `D/dt` the covariant derivative of
`Morse/Chapter6/Parallel.lean`. -/
theorem isGeodesicOn_univ_iff_covDeriv {c : ℝ → N} (hc : ContDiff ℝ ∞ (fun t => (c t : V))) :
    IsGeodesicOn hN (fun t => (c t : V)) univ ↔ ∀ t, covDeriv hN c (velocity c) t = 0 := by
  constructor
  · intro h t
    exact h.tanProj_deriv_deriv (mem_univ t)
  · intro h
    exact ⟨isOpen_univ, fun t _ => (c t).2, hc.contDiffOn,
      fun t _ => (tanProj_eq_zero_iff hN).1 (h t)⟩

/-! ### The geodesic equation as a first-order system on `TN` -/

open Classical in
/-- **The geodesic spray** of `N`: the vector field `(x, v) ↦ (v, II_x(v, v))` on the tangent
bundle `TN ⊆ V × V` (`(v, 0)` off `N`, a junk value). -/
def geodesicSpray (z : V × V) : V × V :=
  if h : z.1 ∈ N then (z.2, secondFundForm hN ⟨z.1, h⟩ z.2 z.2) else (z.2, 0)

/-- The lift `t ↦ (γ(t), γ'(t))` of a geodesic lies in the tangent bundle `TN`. -/
theorem IsGeodesicOn.mem_tangentBundleSet {γ : ℝ → V} {s : Set ℝ} (h : IsGeodesicOn hN γ s)
    {t : ℝ} (ht : t ∈ s) : (γ t, deriv γ t) ∈ Milnor.Problems.tangentBundleSet hN :=
  ⟨h.mem t ht, h.deriv_mem ht⟩

/-- **The geodesic equation as a first-order system on `TN`** (Milnor's reduction of Theorem 10.1
to a first-order system, p. 56): a smooth curve `γ` with values in `N` on the open set `s` is a
geodesic iff its lift `t ↦ (γ(t), γ'(t))`, which lies in `TN`, is an integral curve of the
geodesic spray `(x, v) ↦ (v, II_x(v, v))`. -/
theorem isGeodesicOn_iff_hasDerivAt_geodesicSpray {γ : ℝ → V} {s : Set ℝ} (hs : IsOpen s)
    (hmem : ∀ t ∈ s, γ t ∈ N) (hγ : ContDiffOn ℝ ∞ γ s) :
    IsGeodesicOn hN γ s ↔ ∀ t ∈ s,
      HasDerivAt (fun τ => (γ τ, deriv γ τ)) (geodesicSpray hN (γ t, deriv γ t)) t := by
  constructor
  · intro h t ht
    have e : geodesicSpray hN (γ t, deriv γ t) = (deriv γ t, deriv (deriv γ) t) := by
      rw [geodesicSpray, dif_pos (h.mem t ht), h.deriv_deriv_eq ht]
    rw [e]
    exact (h.hasDerivAt ht).prodMk (h.hasDerivAt_deriv ht)
  · intro h
    refine isGeodesicOn_of_deriv_deriv_eq hN hs hmem hγ fun t ht => ?_
    have h2 := hasDerivAt_snd_comp (h t ht)
    rw [geodesicSpray, dif_pos (hmem t ht)] at h2
    exact h2.deriv

end Morse
