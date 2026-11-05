import Morse.Chapter7.NormalNbhd

/-!
Milnor, *Morse Theory*, §10, pp. 59–61 (Lemmas 10.5 and 10.6), for a submanifold `N ⊆ ℝᴷ` with the
induced metric.

# The Gauss lemma, and radial coordinates

## Milnor's text, paraphrased

* **Lemma 10.5** (p. 60, the Gauss lemma).  In `U_q`, the geodesics through `q` are the orthogonal
  trajectories of the hypersurfaces `{exp_q(v) : v ∈ TM_q, ‖v‖ = constant}`.  Proof: for a curve
  `t ↦ v(t)` in `TM_q` with `‖v(t)‖ = 1` and `f(r, t) = exp_q(r v(t))`,
  `∂/∂r ⟨∂f/∂r, ∂f/∂t⟩ = ⟨D/∂r ∂f/∂r, ∂f/∂t⟩ + ⟨∂f/∂r, D/∂r ∂f/∂t⟩`; the first term vanishes since
  `r ↦ f(r, t)` is a geodesic, the second is `½ ∂/∂t ‖∂f/∂r‖² = 0` (symmetry, Lemma 8.7, and
  `‖∂f/∂r‖ = ‖v(t)‖ = 1`).  So `⟨∂f/∂r, ∂f/∂t⟩` does not depend on `r`, and it vanishes at `r = 0`.
* **Lemma 10.6** (p. 60): for a piecewise smooth curve `ω(t) = exp_q(r(t) v(t))` in `U_q − {q}`
  (`0 < r(t) < ε`, `‖v(t)‖ = 1`), `∫ₐᵇ ‖dω/dt‖ dt ≥ |r(b) − r(a)|`, with equality only if `r` is
  monotone and `v` constant.  Proof: `dω/dt = (∂f/∂r) r'(t) + ∂f/∂t`, the two terms are orthogonal
  and `‖∂f/∂r‖ = 1`, so `‖dω/dt‖² ≥ |r'(t)|²`, with equality only if `∂f/∂t = 0`, "hence only if
  `dv/dt = 0`".

## In the embedded setting

For a normal radius `ε` at `q` (`Morse.NormalCoord`: `F` extends `exp_q|B_ε(q)` smoothly, `G` its
inverse):

* `Morse.NormalCoord.inner_fderiv_F` and `Morse.gauss_lemma`: **the Gauss lemma** in the form
  `⟨d(exp_q)_w(w), d(exp_q)_w(x)⟩ = ⟨w, x⟩` for `w ∈ B_ε(q)`, `x ∈ T_qN`.  For `x ⊥ w`
  (`Morse.gauss_lemma_orthogonal`) this is Milnor's statement: the radial velocity `d(exp_q)_w(w)`
  is orthogonal to `d(exp_q)_w(x)`, which spans the tangent space of the image of the sphere
  `‖v‖ = ‖w‖`.  The proof is Milnor's, with `f(r, s) = exp_q(r(w + sx))`: in `V`, the term
  `⟨∂²f/∂r², ∂f/∂s⟩` vanishes because the acceleration of a geodesic is normal and `∂f/∂s` is
  tangent, and the derivative of `‖∂f/∂r‖² = ‖w + sx‖²` (constant speed) in `s` gives the second.
* `Morse.NormalCoord.hasDerivAt_radius`: **Lemma 10.6, pointwise.**  For a curve `ω` in
  `U_q − {q}`, differentiable at `t`, the radius `ρ(s) = ‖exp_q⁻¹(ω(s))‖` has `|ρ'(t)| ≤ ‖ω'(t)‖`,
  and if `ρ'(t) = ‖ω'(t)‖` the direction `exp_q⁻¹(ω)/ρ` has derivative `0` at `t`.  The integrated
  form, and Theorem 10.4, are in `Morse/Chapter7/Shortest.lean`.

## What Milnor leaves implicit

* **Hypersurfaces.**  That the sets `{exp_q(v) : ‖v‖ = r}` are hypersurfaces with tangent vectors
  `d/dt exp_q(r v(t))` uses that `exp_q` is a diffeomorphism on `B_ε(q)`.  The form
  `⟨d(exp_q)_w(w), d(exp_q)_w(x)⟩ = ⟨w, x⟩` proved here needs no curve `v(t)` at all.
* **Equality in Lemma 10.6** ("only if `∂f/∂t = 0`, hence only if `dv/dt = 0`") uses that
  `d(exp_q)_w` is injective for `w ∈ B_ε(q)` (`Morse.NormalCoord.fderiv_G_fderiv_F`), which holds
  because `exp_q` is a diffeomorphism there, and `r > 0`.  Here the inequality is obtained from the
  Cauchy–Schwarz inequality `|⟨d(exp_q)_w(w), ω'⟩| ≤ ‖w‖ ‖ω'‖` and the Gauss lemma
  `⟨d(exp_q)_w(w), ω'⟩ = ⟨w, w'⟩ = ρ ρ'`, without splitting `ω'` into radial and spherical parts;
  equality in Cauchy–Schwarz then gives `w' ∥ w`.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

omit [FiniteDimensional ℝ V] in
/-- The derivative of the norm, away from `0`. -/
theorem hasDerivAt_norm_of_ne {f : ℝ → V} {f' : V} {t : ℝ} (hf : HasDerivAt f f' t)
    (h0 : f t ≠ 0) : HasDerivAt (fun s => ‖f s‖) (⟪f t, f'⟫ / ‖f t‖) t := by
  have hpos : 0 < ‖f t‖ := norm_pos_iff.2 h0
  have h1 := hf.norm_sq.sqrt (by positivity)
  simp only [Real.sqrt_sq (norm_nonneg _)] at h1
  convert h1 using 1
  field_simp

/-- The derivative of a curve lying in a subspace `K` lies in `K`. -/
theorem hasDerivAt_mem_of_eventually_mem {K : Submodule ℝ V} {f : ℝ → V} {f' : V} {t : ℝ}
    (hf : HasDerivAt f f' t) (hK : ∀ᶠ s in 𝓝 t, f s ∈ K) : f' ∈ K := by
  have h1 : HasDerivAt (fun s => K.starProjection (f s)) (K.starProjection f') t :=
    K.starProjection.hasFDerivAt.comp_hasDerivAt t hf
  have hev : (fun s => K.starProjection (f s)) =ᶠ[𝓝 t] f := by
    filter_upwards [hK] with s hs
    exact Submodule.starProjection_eq_self_iff.2 hs
  have h2 := h1.unique (hf.congr_of_eventuallyEq hev)
  exact Submodule.starProjection_eq_self_iff.1 h2

namespace NormalCoord

variable {q : N} {ε : ℝ} (nc : NormalCoord hN q ε)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem contDiffAt_F {v : V} (hv : v ∈ tangentSubspace hN q) (hvε : ‖v‖ < ε) :
    ContDiffAt ℝ ∞ nc.F v :=
  nc.contDiffOn_F.contDiffAt (nc.isOpen_O.mem_nhds (nc.mem_O v hv hvε))

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem hasFDerivAt_F {v : V} (hv : v ∈ tangentSubspace hN q) (hvε : ‖v‖ < ε) :
    HasFDerivAt nc.F (fderiv ℝ nc.F v) v :=
  ((nc.contDiffAt_F hv hvε).differentiableAt (by simp)).hasFDerivAt

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- Near a point of `B_ε(q)`, along the line through it in a direction of `T_qN`, `F = exp_q`. -/
theorem eventually_F_eq {w x : V} (hw : w ∈ tangentSubspace hN q) (hwε : ‖w‖ < ε)
    (hx : x ∈ tangentSubspace hN q) {a : ℝ → ℝ} (ha : Continuous a) {s₀ : ℝ} (hs₀ : a s₀ = 0) :
    ∀ᶠ s in 𝓝 s₀, ‖w + a s • x‖ < ε ∧ w + a s • x ∈ tangentSubspace hN q ∧
      nc.F (w + a s • x) = exp hN q (w + a s • x) := by
  have hc : Continuous fun s => ‖w + a s • x‖ :=
    (continuous_const.add (ha.smul continuous_const)).norm
  have h1 : ∀ᶠ s in 𝓝 s₀, ‖w + a s • x‖ < ε :=
    hc.continuousAt.eventually (gt_mem_nhds (by simpa [hs₀] using hwε))
  filter_upwards [h1] with s hs
  have hmem : w + a s • x ∈ tangentSubspace hN q := add_mem hw (Submodule.smul_mem _ _ hx)
  exact ⟨hs, hmem, nc.F_eq _ hmem hs⟩

/-- **The radial geodesics have constant speed**: `‖dF_{ru}(u)‖ = ‖u‖` for `u ∈ B_ε(q)` and
`0 ≤ r ≤ 1`; and `t ↦ exp_q(tu)` is a geodesic near `[0, 1]` with velocity `dF_{ru}(u)` at `r`. -/
theorem norm_fderiv_F_apply {u : V} (hu : u ∈ tangentSubspace hN q) (huε : ‖u‖ < ε) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) :
    ‖fderiv ℝ nc.F (r • u) u‖ = ‖u‖ := by
  obtain ⟨γ, hγ, -⟩ := exp_eq_of_mem_expDom (nc.mem_expDom u hu huε)
  obtain ⟨δ, hδ, hgeo, heq⟩ := hγ.isGeodesicOn_exp_smul
  obtain ⟨δ', -, -, -, h0'⟩ := hγ
  have hrδ : r ∈ Ioo (-δ) (1 + δ) := ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have h0δ : (0 : ℝ) ∈ Ioo (-δ) (1 + δ) := ⟨by linarith, by linarith⟩
  have hru : ‖r • u‖ < ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr.1]
    calc r * ‖u‖ ≤ 1 * ‖u‖ := by gcongr; exact hr.2
      _ < ε := by linarith
  have hruT : r • u ∈ tangentSubspace hN q := Submodule.smul_mem _ _ hu
  -- `exp_q(tu) = F(tu)` near `r`
  have hev : (fun t : ℝ => exp hN q (t • u)) =ᶠ[𝓝 r] fun t => nc.F (t • u) := by
    have := nc.eventually_F_eq hruT hru hu (a := fun t => t - r) (continuous_id.sub
      continuous_const) (s₀ := r) (sub_self r)
    filter_upwards [this] with t ht
    have e : r • u + (t - r) • u = t • u := by rw [← add_smul, add_sub_cancel]
    rw [e] at ht
    exact ht.2.2.symm
  have hd : HasDerivAt (fun t : ℝ => nc.F (t • u)) (fderiv ℝ nc.F (r • u) u) r := by
    have h1 : HasDerivAt (fun t : ℝ => t • u) u r := by
      simpa using (hasDerivAt_id r).smul_const u
    exact (nc.hasFDerivAt_F hruT hru).comp_hasDerivAt r h1
  have hd' : deriv (fun t : ℝ => exp hN q (t • u)) r = fderiv ℝ nc.F (r • u) u :=
    (hd.congr_of_eventuallyEq hev).deriv
  have hspeed := hgeo.norm_deriv_eq isPreconnected_Ioo hrδ h0δ
  have hd0 : deriv (fun t : ℝ => exp hN q (t • u)) 0 = u := by
    have hev0 : (fun t : ℝ => exp hN q (t • u)) =ᶠ[𝓝 0] γ :=
      eventually_of_mem (isOpen_Ioo.mem_nhds h0δ) heq
    rw [hev0.deriv_eq, h0']
  rw [← hd', hspeed, hd0]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- `G` inverts `F` infinitesimally: `dG_{F(w)}(dF_w(v)) = v` for `w ∈ B_ε(q)`, `v ∈ T_qN`.  In
particular `d(exp_q)_w` is injective on `T_qN`. -/
theorem fderiv_G_fderiv_F {w : V} (hw : w ∈ tangentSubspace hN q) (hwε : ‖w‖ < ε) {v : V}
    (hv : v ∈ tangentSubspace hN q) : fderiv ℝ nc.G (nc.F w) (fderiv ℝ nc.F w v) = v := by
  have hFw : nc.F w = exp hN q w := nc.F_eq w hw hwε
  have hU : nc.F w ∈ nc.U := by rw [hFw]; exact nc.exp_mem_U w hw hwε
  have hGd : HasFDerivAt nc.G (fderiv ℝ nc.G (nc.F w)) (nc.F w) :=
    ((nc.contDiffOn_G.contDiffAt (nc.isOpen_U.mem_nhds hU)).differentiableAt (by simp)).hasFDerivAt
  have hline : HasDerivAt (fun s : ℝ => w + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add w
  have hFd : HasFDerivAt nc.F (fderiv ℝ nc.F w) ((fun s : ℝ => w + s • v) 0) := by
    simpa using nc.hasFDerivAt_F hw hwε
  have h1 := hFd.comp_hasDerivAt (0 : ℝ) hline
  have hGd' : HasFDerivAt nc.G (fderiv ℝ nc.G (nc.F w)) ((nc.F ∘ fun s : ℝ => w + s • v) 0) := by
    simpa using hGd
  have h2 := hGd'.comp_hasDerivAt (0 : ℝ) h1
  have hev : (nc.G ∘ nc.F ∘ fun s : ℝ => w + s • v) =ᶠ[𝓝 0] fun s => w + s • v := by
    have := nc.eventually_F_eq hw hwε hv (a := id) continuous_id (s₀ := 0) rfl
    filter_upwards [this] with s hs
    simp only [Function.comp_apply, id] at hs ⊢
    rw [hs.2.2, nc.G_exp _ hs.2.1 hs.1]
  exact h2.unique (hline.congr_of_eventuallyEq hev)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem injective_fderiv_F {w : V} (hw : w ∈ tangentSubspace hN q) (hwε : ‖w‖ < ε) {v : V}
    (hv : v ∈ tangentSubspace hN q) (h0 : fderiv ℝ nc.F w v = 0) : v = 0 := by
  rw [← nc.fderiv_G_fderiv_F hw hwε hv, h0, map_zero]

/-- **The Gauss lemma** (Milnor's Lemma 10.5), for the smooth extension `F` of `exp_q`:
`⟨dF_w(w), dF_w(x)⟩ = ⟨w, x⟩` for `w ∈ B_ε(q)` and `x ∈ T_qN`. -/
theorem inner_fderiv_F {w x : V} (hw : w ∈ tangentSubspace hN q) (hwε : ‖w‖ < ε)
    (hx : x ∈ tangentSubspace hN q) :
    ⟪fderiv ℝ nc.F w w, fderiv ℝ nc.F w x⟫ = ⟪w, x⟫ := by
  set D := fderiv ℝ nc.F with hD_def
  set D2 := fderiv ℝ (fderiv ℝ nc.F) with hD2_def
  have hseg : ∀ r ∈ Icc (0 : ℝ) 1, r • w ∈ tangentSubspace hN q ∧ ‖r • w‖ < ε := by
    intro r hr
    refine ⟨Submodule.smul_mem _ _ hw, ?_⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr.1]
    calc r * ‖w‖ ≤ 1 * ‖w‖ := by gcongr; exact hr.2
      _ < ε := by linarith
  have hDd : ∀ r ∈ Icc (0 : ℝ) 1, HasFDerivAt D (D2 (r • w)) (r • w) := fun r hr =>
    (((nc.contDiffAt_F (hseg r hr).1 (hseg r hr).2).fderiv_right (m := ∞)
      (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hlin : ∀ (r : ℝ) (v : V), HasDerivAt (fun s : ℝ => s • v) v r := fun r v => by
    simpa using (hasDerivAt_id r).smul_const v
  set g : ℝ → ℝ := fun r => ⟪D (r • w) w, D (r • w) (r • x)⟫ with hg_def
  -- `g` is continuous on `[0, 1]`
  have hgc : ContinuousOn g (Icc 0 1) := by
    have hDc : ContinuousOn (fun r : ℝ => D (r • w)) (Icc 0 1) := by
      intro r hr
      have h1 : ContinuousAt (fun r : ℝ => r • w) r :=
        (continuous_id.smul continuous_const).continuousAt
      have h2 : ContinuousAt D ((fun r : ℝ => r • w) r) := (hDd r hr).continuousAt
      exact (ContinuousAt.comp (f := fun r : ℝ => r • w) h2 h1).continuousWithinAt
    exact (hDc.clm_apply continuousOn_const).inner (hDc.clm_apply
      (continuous_id.smul continuous_const).continuousOn)
  -- `g' = ⟨w, x⟩` on `(0, 1)`
  have hg' : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt g ⟪w, x⟫ r := by
    intro r hr
    have hrI : r ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hr
    obtain ⟨hrwT, hrwε⟩ := hseg r hrI
    have hDr : HasDerivAt (fun s : ℝ => D (s • w)) (D2 (r • w) w) r :=
      (hDd r hrI).comp_hasDerivAt r (hlin r w)
    have ha : HasDerivAt (fun s : ℝ => D (s • w) w) (D2 (r • w) w w) r := by
      simpa using hDr.clm_apply (hasDerivAt_const r w)
    have hb : HasDerivAt (fun s : ℝ => D (s • w) (s • x)) (D2 (r • w) w (r • x) + D (r • w) x) r :=
      hDr.clm_apply (hlin r x)
    have hgd := ha.inner ℝ hb
    -- (i) the acceleration of the radial geodesic is normal, `∂f/∂s` is tangent
    have hi : ⟪D2 (r • w) w w, D (r • w) (r • x)⟫ = 0 := by
      obtain ⟨γ, hγ, -⟩ := exp_eq_of_mem_expDom (nc.mem_expDom w hw hwε)
      obtain ⟨δ, hδ, hgeo, -⟩ := hγ.isGeodesicOn_exp_smul
      have hrδ : r ∈ Ioo (-δ) (1 + δ) := ⟨by linarith [hr.1], by linarith [hr.2]⟩
      have hev : (fun t : ℝ => exp hN q (t • w)) =ᶠ[𝓝 r] fun t => nc.F (t • w) := by
        have := nc.eventually_F_eq hrwT hrwε hw (a := fun t => t - r)
          (continuous_id.sub continuous_const) (s₀ := r) (sub_self r)
        filter_upwards [this] with t ht
        have e : r • w + (t - r) • w = t • w := by rw [← add_smul, add_sub_cancel]
        rw [e] at ht
        exact ht.2.2.symm
      have hevd : deriv (fun t : ℝ => nc.F (t • w)) =ᶠ[𝓝 r] fun t => D (t • w) w := by
        have hO : ∀ᶠ t in 𝓝 r, t • w ∈ nc.O :=
          ((continuous_id.smul continuous_const).continuousAt (x := r)).eventually
            (nc.isOpen_O.mem_nhds (nc.mem_O _ hrwT hrwε))
        filter_upwards [hO] with t ht
        exact (((nc.contDiffOn_F.contDiffAt (nc.isOpen_O.mem_nhds ht)).differentiableAt
          (by simp)).hasFDerivAt.comp_hasDerivAt t (hlin t w)).deriv
      have hacc : deriv (deriv fun t : ℝ => exp hN q (t • w)) r = D2 (r • w) w w := by
        rw [hev.deriv.deriv_eq, hevd.deriv_eq, ha.deriv]
      have hnormal := hgeo.normal r hrδ
      rw [hacc] at hnormal
      -- `∂f/∂s` is tangent at `exp_q(rw)`
      have hcurve : HasDerivAt (fun s : ℝ => nc.F (r • w + s • (r • x))) (D (r • w) (r • x)) 0 := by
        have h1 : HasDerivAt (fun s : ℝ => r • w + s • (r • x)) (r • x) 0 := by
          simpa using (hlin 0 (r • x)).const_add (r • w)
        have hF' : HasFDerivAt nc.F (D (r • w)) ((fun s : ℝ => r • w + s • (r • x)) 0) := by
          simpa using nc.hasFDerivAt_F hrwT hrwε
        exact hF'.comp_hasDerivAt (0 : ℝ) h1
      have hrx : r • x ∈ tangentSubspace hN q := Submodule.smul_mem _ _ hx
      have hcurveN : ∀ᶠ s in 𝓝 (0 : ℝ), nc.F (r • w + s • (r • x)) ∈ N := by
        have := nc.eventually_F_eq hrwT hrwε hrx (a := id) continuous_id (s₀ := 0) rfl
        filter_upwards [this] with s hs
        rw [id] at hs
        rw [hs.2.2]
        exact nc.exp_mem hs.2.1 hs.1
      have htan := hasDerivAt_mem_tangentSubspace hN hcurve hcurveN
      have hbase : nc.F (r • w + (0 : ℝ) • (r • x)) = exp hN q (r • w) := by
        rw [zero_smul, add_zero]; exact nc.F_eq _ hrwT hrwε
      rw [tangentSubspace_congr hN _ (nc.exp_mem hrwT hrwε) hbase] at htan
      exact Submodule.inner_left_of_mem_orthogonal htan hnormal
    -- (ii) the derivative of `‖∂f/∂r‖² = ‖w + sx‖²` in `s`
    have hii : ⟪D (r • w) w, D2 (r • w) w (r • x) + D (r • w) x⟫ = ⟪w, x⟫ := by
      have hc : HasDerivAt (fun s : ℝ => r • (w + s • x)) (r • x) 0 :=
        ((hlin 0 x).const_add w).const_smul r
      have hDc : HasDerivAt (fun s : ℝ => D (r • (w + s • x))) (D2 (r • w) (r • x)) 0 := by
        have hD' : HasFDerivAt D (D2 (r • w)) ((fun s : ℝ => r • (w + s • x)) 0) := by
          simpa using hDd r hrI
        exact hD'.comp_hasDerivAt (0 : ℝ) hc
      have hh : HasDerivAt (fun s : ℝ => D (r • (w + s • x)) (w + s • x))
          (D2 (r • w) (r • x) w + D (r • w) x) 0 := by
        simpa using hDc.clm_apply ((hlin 0 x).const_add w)
      have hh2 := hh.norm_sq
      have hev : (fun s : ℝ => ‖D (r • (w + s • x)) (w + s • x)‖ ^ 2) =ᶠ[𝓝 0]
          fun s => ‖w + s • x‖ ^ 2 := by
        have := nc.eventually_F_eq hw hwε hx (a := id) continuous_id (s₀ := 0) rfl
        filter_upwards [this] with s hs
        rw [id] at hs
        rw [nc.norm_fderiv_F_apply hs.2.1 hs.1 hrI]
      have hh3 : HasDerivAt (fun s : ℝ => ‖w + s • x‖ ^ 2) (2 * ⟪w, x⟫) 0 := by
        simpa using ((hlin 0 x).const_add w).norm_sq
      have := hh2.unique (hh3.congr_of_eventuallyEq hev)
      simp only [zero_smul, add_zero] at this
      have hsymm : D2 (r • w) (r • x) w = D2 (r • w) w (r • x) :=
        ((nc.contDiffAt_F hrwT hrwε).isSymmSndFDerivAt (by
          simp only [minSmoothness_of_isRCLikeNormedField]
          exact WithTop.coe_le_coe.2 le_top)) (r • x) w
      rw [hsymm] at this
      linarith
    have e : ⟪w, x⟫ = ⟪D (r • w) w, D2 (r • w) w (r • x) + D (r • w) x⟫ +
        ⟪D2 (r • w) w w, D (r • w) (r • x)⟫ := by
      rw [hi, add_zero, hii]
    rw [e]
    exact hgd
  obtain ⟨c, -, hc⟩ := exists_hasDerivAt_eq_slope g (fun _ => ⟪w, x⟫) zero_lt_one hgc hg'
  have hg0 : g 0 = 0 := by simp [hg_def]
  have hg1 : g 1 = ⟪D w w, D w x⟫ := by simp [hg_def]
  rw [hg0, hg1] at hc
  simp only [sub_zero, div_one] at hc
  exact hc.symm

/-- **Lemma 10.6, pointwise** (radial coordinates).  Let `c` be a curve in `U_q ∩ N`, `c(t) ≠ q`,
differentiable at `t`.  Then the radius `ρ(s) = ‖exp_q⁻¹(c(s))‖ = ‖G(c(s))‖` has a derivative
`ρ'` at `t` with `|ρ'| ≤ ‖c'(t)‖`; and if `ρ' = ‖c'(t)‖`, the direction `G(c)/ρ` has derivative
`0` at `t`. -/
theorem hasDerivAt_radius {c : ℝ → V} {t : ℝ} {c' : V} (hc : HasDerivAt c c' t)
    (hmem : ∀ᶠ s in 𝓝 t, c s ∈ N) (hU : c t ∈ nc.U) (hne : c t ≠ q) :
    ∃ r', HasDerivAt (fun s => ‖nc.G (c s)‖) r' t ∧ |r'| ≤ ‖c'‖ ∧
      (r' = ‖c'‖ → HasDerivAt (fun s => ‖nc.G (c s)‖⁻¹ • nc.G (c s)) 0 t) := by
  have hcN : c t ∈ N := hmem.self_of_nhds
  set w := nc.G (c t) with hw_def
  have hwT : w ∈ tangentSubspace hN q := nc.G_mem _ hU hcN
  have hwε : ‖w‖ < ε := nc.norm_G_lt _ hU hcN
  have hw0 : w ≠ 0 := by
    intro h
    apply hne
    rw [← nc.exp_G _ hU hcN, ← hw_def, h]
    exact exp_zero q.2
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hGd : HasFDerivAt nc.G (fderiv ℝ nc.G (c t)) (c t) :=
    ((nc.contDiffOn_G.contDiffAt (nc.isOpen_U.mem_nhds hU)).differentiableAt (by simp)).hasFDerivAt
  set w' := fderiv ℝ nc.G (c t) c' with hw'_def
  have hW : HasDerivAt (fun s => nc.G (c s)) w' t := hGd.comp_hasDerivAt t hc
  have hUt : ∀ᶠ s in 𝓝 t, c s ∈ nc.U := hc.continuousAt.eventually (nc.isOpen_U.mem_nhds hU)
  have hw'T : w' ∈ tangentSubspace hN q := by
    refine hasDerivAt_mem_of_eventually_mem hW ?_
    filter_upwards [hmem, hUt] with s h1 h2
    exact nc.G_mem _ h2 h1
  -- `F ∘ G ∘ c = c` near `t`, so `dF_w(w') = c'`
  have hev : (fun s => nc.F (nc.G (c s))) =ᶠ[𝓝 t] c := by
    filter_upwards [hmem, hUt] with s h1 h2
    rw [nc.F_eq _ (nc.G_mem _ h2 h1) (nc.norm_G_lt _ h2 h1), nc.exp_G _ h2 h1]
  have hFd : HasFDerivAt nc.F (fderiv ℝ nc.F w) ((fun s => nc.G (c s)) t) :=
    nc.hasFDerivAt_F hwT hwε
  have hc' : fderiv ℝ nc.F w w' = c' :=
    (hFd.comp_hasDerivAt t hW).unique (hc.congr_of_eventuallyEq hev)
  have hr := hasDerivAt_norm_of_ne hW hw0
  refine ⟨⟪w, w'⟫ / ‖w‖, hr, ?_, ?_⟩
  · -- Gauss and Cauchy–Schwarz
    have hG1 := nc.inner_fderiv_F hwT hwε hw'T
    have hG2 := nc.inner_fderiv_F hwT hwε hwT
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hG2
    have hnorm : ‖fderiv ℝ nc.F w w‖ = ‖w‖ :=
      (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hG2
    rw [hc'] at hG1
    rw [abs_div, abs_norm, div_le_iff₀ hwpos, ← hG1]
    calc |⟪fderiv ℝ nc.F w w, c'⟫| ≤ ‖fderiv ℝ nc.F w w‖ * ‖c'‖ := abs_real_inner_le_norm _ _
      _ = ‖c'‖ * ‖w‖ := by rw [hnorm, mul_comm]
  · intro heq
    have hG1 := nc.inner_fderiv_F hwT hwε hw'T
    have hG2 := nc.inner_fderiv_F hwT hwε hwT
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hG2
    have hnorm : ‖fderiv ℝ nc.F w w‖ = ‖w‖ :=
      (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hG2
    rw [hc'] at hG1
    have hww' : ⟪w, w'⟫ = ‖w‖ * ‖c'‖ := by
      rw [div_eq_iff hwpos.ne'] at heq
      linarith
    have h1 : ⟪fderiv ℝ nc.F w w, c'⟫ = ‖fderiv ℝ nc.F w w‖ * ‖c'‖ := by
      rw [hG1, hnorm, hww']
    have h2 := inner_eq_norm_mul_iff_real.1 h1
    rw [hnorm] at h2
    set l := ‖c'‖ / ‖w‖ with hl_def
    have hc'eq : c' = l • fderiv ℝ nc.F w w := by
      rw [hl_def, div_eq_inv_mul, mul_smul, h2, smul_smul, inv_mul_cancel₀ hwpos.ne', one_smul]
    have h3 : fderiv ℝ nc.F w (w' - l • w) = 0 := by
      rw [map_sub, map_smul, hc', ← hc'eq, sub_self]
    have h4 : w' = l • w :=
      sub_eq_zero.1 (nc.injective_fderiv_F hwT hwε
        (sub_mem hw'T (Submodule.smul_mem _ _ hwT)) h3)
    have hinv := hr.inv (norm_ne_zero_iff.2 hw0)
    have hdir := hinv.smul hW
    have hval : (fun s => ‖nc.G (c s)‖)⁻¹ t • w' +
        (-(⟪nc.G (c t), w'⟫ / ‖nc.G (c t)‖) / ‖nc.G (c t)‖ ^ 2) • nc.G (c t) = 0 := by
      change ‖w‖⁻¹ • w' + (-(⟪w, w'⟫ / ‖w‖) / ‖w‖ ^ 2) • w = 0
      rw [h4, inner_smul_right, real_inner_self_eq_norm_sq, smul_smul, ← add_smul]
      have hne : ‖w‖ ≠ 0 := hwpos.ne'
      have : ‖w‖⁻¹ * l + -(l * ‖w‖ ^ 2 / ‖w‖) / ‖w‖ ^ 2 = 0 := by
        field_simp
        ring
      rw [this, zero_smul]
    rw [hval] at hdir
    exact hdir

end NormalCoord

/-- **The Gauss lemma** (Milnor's Lemma 10.5), for `exp_q` as a map on the vector space
`T_qN`: if `ε` is a normal radius at `q`, then `⟨d(exp_q)_w(w), d(exp_q)_w(x)⟩ = ⟨w, x⟩` for
`w ∈ T_qN` with `‖w‖ < ε` and every `x ∈ T_qN`. -/
theorem gauss_lemma {q : N} {ε : ℝ} (h : IsNormalRadius hN q ε) (w x : tangentSubspace hN q)
    (hw : ‖(w : V)‖ < ε) :
    ⟪fderiv ℝ (fun v : tangentSubspace hN q => exp hN q v) w w,
      fderiv ℝ (fun v : tangentSubspace hN q => exp hN q v) w x⟫ = ⟪(w : V), x⟫ := by
  obtain ⟨nc⟩ := h
  have hev : (fun v : tangentSubspace hN q => exp hN q v) =ᶠ[𝓝 w]
      fun v : tangentSubspace hN q => nc.F v := by
    have hball : ∀ᶠ v : tangentSubspace hN q in 𝓝 w, ‖(v : V)‖ < ε :=
      (continuous_norm.comp continuous_subtype_val).continuousAt.eventually (gt_mem_nhds hw)
    filter_upwards [hball] with v hv
    exact (nc.F_eq v v.2 hv).symm
  have hFd : HasFDerivAt nc.F (fderiv ℝ nc.F w)
      (((tangentSubspace hN q).subtypeL : tangentSubspace hN q →L[ℝ] V) w) :=
    nc.hasFDerivAt_F w.2 hw
  have hT : HasFDerivAt (fun v : tangentSubspace hN q => nc.F v)
      ((fderiv ℝ nc.F w).comp (tangentSubspace hN q).subtypeL) w :=
    hFd.comp w (tangentSubspace hN q).subtypeL.hasFDerivAt
  rw [(hT.congr_of_eventuallyEq hev).fderiv]
  exact nc.inner_fderiv_F w.2 hw x.2

/-- **The Gauss lemma, Milnor's form**: the radial geodesics through `q` are orthogonal to the
images under `exp_q` of the spheres `‖v‖ = r`: for `w, x ∈ T_qN` with `‖w‖ < ε` and `x ⊥ w`
(`x` tangent to the sphere through `w`), `d(exp_q)_w(w) ⊥ d(exp_q)_w(x)`. -/
theorem gauss_lemma_orthogonal {q : N} {ε : ℝ} (h : IsNormalRadius hN q ε)
    (w x : tangentSubspace hN q) (hw : ‖(w : V)‖ < ε) (hwx : ⟪(w : V), x⟫ = 0) :
    ⟪fderiv ℝ (fun v : tangentSubspace hN q => exp hN q v) w w,
      fderiv ℝ (fun v : tangentSubspace hN q => exp hN q v) w x⟫ = 0 := by
  rw [gauss_lemma h w x hw, hwx]

end Morse
