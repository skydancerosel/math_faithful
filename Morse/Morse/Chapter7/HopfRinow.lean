import Morse.Chapter7.GeodesicFlow
import Milnor.Chapter6.EulerSphere

/-!
Milnor, *Morse Theory*, §10, pp. 61–65 (Theorem 10.9, Corollary 10.10 and its converse), for a
submanifold `N ⊆ ℝᴷ` with the induced metric.

# The Hopf–Rinow theorem

## Milnor's text, paraphrased

* **Theorem 10.9** (Hopf and Rinow, p. 62): if `M` is geodesically complete, any two points can
  be joined by a minimal geodesic (a geodesic whose length is at most that of every piecewise
  smooth path with the same endpoints, p. 61).
* **Proof** (pp. 62–64, Diagram 10).  Let `r = ρ(p, q) > 0`, let `S` be a small spherical shell
  of radius `δ` about `p` (inside a normal neighbourhood), and `p₀ = exp_p(δv)`, `‖v‖ = 1`, a point
  of `S` nearest to `q` (`S` is compact).  As every path from `p` to `q` passes through `S`,
  `ρ(p, q) = δ + ρ(p₀, q)`.  For `γ(t) = exp_p(tv)` one proves `ρ(γ(t), q) = r − t` for all
  `t ∈ [δ, r]`; at `t = r` this gives `γ(r) = q`.  Let `t₀` be the supremum of the `t` where the
  identity holds; it holds at `t₀` by continuity.  If `t₀ < r`, take a small shell `S'` of radius
  `δ'` about `γ(t₀)` and its point `p₀'` nearest to `q`; as before `ρ(p₀', q) = r − t₀ − δ'`, so
  `ρ(p, p₀') ≥ t₀ + δ'`.  Following `γ` to `γ(t₀)` and then a minimal geodesic to `p₀'` gives a
  path of length exactly `t₀ + δ'`; this broken geodesic has minimal length, so it is an unbroken
  geodesic by Corollary 10.7 and coincides with `γ`.  Thus `γ(t₀ + δ') = p₀'` and the identity
  holds at `t₀ + δ'`, a contradiction.
* **Corollary 10.10** (p. 64): if `M` is geodesically complete, every bounded subset of `M` has
  compact closure: if `X` has diameter `d` and `p ∈ X`, `exp_p` maps the disk of radius `d` of
  `TM_p` onto a compact set which contains `X` by Theorem 10.9.  Consequently `M` is complete as a
  metric space.  The converse (p. 64) is `Morse.isGeodesicallyComplete_of_isRiemComplete`
  (`Morse/Chapter7/GeodesicFlow.lean`).  Henceforth Milnor speaks of complete Riemannian manifolds.
* (p. 65) The unit sphere `Sⁿ` (whose geodesics are the great circles).

## In the embedded setting

* `Morse.IsMinimalGeodesic hN γ a b`: minimal geodesics (p. 61).
* `Morse.NormalCoord.exists_riemDist_eq_add`: the nearest point `p₀` of the sphere `S`, with
  `ρ(p, q) = δ + ρ(p₀, q)`.
* `Morse.broken_geodesic_eq`: **a broken geodesic of minimal length is unbroken**.
* `Morse.theorem_10_9`: **Theorem 10.9 at one point**: if `exp_p` is defined on all of `T_pN`,
  every `q` at finite distance from `p` is `exp_p(v)` with `‖v‖ = ρ(p, q)`, and `t ↦ exp_p(tv)`,
  `0 ≤ t ≤ 1`, is a minimal geodesic.  `Morse.theorem_10_9'`: Milnor's statement.
* `Morse.corollary_10_10`: **Corollary 10.10**, from its halves
  `Morse.isCompact_closure_of_isRiemBounded` and `Morse.isRiemComplete_of_forall_isCompact_closure`.
* `Morse.hopf_rinow`: **the Hopf–Rinow theorem**: for connected nonempty `N`, metric completeness,
  geodesic completeness, "`exp_p` is defined on `T_pN` for one `p`", and "bounded sets have compact
  closure" are equivalent.  `Morse.hopf_rinow_of_isRiemComplete`: the consequences of metric
  completeness: geodesics extend to `ℝ`, minimal geodesics of length `ρ`, closed bounded subsets
  are compact (`Morse.isCompact_of_isClosed_of_isRiemBounded`).
* `Morse.hopf_rinow_of_isClosed`, `Morse.hopf_rinow_of_isCompact`: **closed (for instance compact)
  connected submanifolds** of `V` satisfy all of these (by `Morse.isRiemComplete_of_isClosed`);
  this covers the compact Lie groups of Part IV once embedded in a space of matrices.
  `Morse.sphere_hopf_rinow`: the round sphere `Sⁿ`, `n ≥ 1`.

## What Milnor leaves implicit

* **`δ < ρ(p, q)`, and `δ' < r − t₀` in the inductive step.**  Milnor only asks `δ < ε`.  If
  `δ ≥ ρ(p, q)`, then `q` lies within the shell and paths from `p` to `q` need not meet `S`; if
  `δ' > r − t₀`, the new time `t₀ + δ'` overshoots `r`.
* **That every path from `p` to `q` passes through `S`** uses the shell-crossing lemma
  (`Morse.NormalCoord.exists_crossing`): a path may leave the normal neighbourhood, and its first
  exit from the normal ball lies on `S` because closed normal balls are closed.
* **The point of `S` nearest to `q` exists** because `ρ(·, q)` is continuous
  (`Morse.continuousOn_riemDist_left`) and `S` is compact and nonempty; `S` is nonempty because a
  path from `p` to `q` crosses it (if `dim N = 0`, `S` is empty but then no such path exists).
* **"By continuity"** the identity holds at the supremum `t₀`: this is the continuity of
  `t ↦ ρ(γ(t), q)`; the supremum argument is the continuous induction
  `IsClosed.Icc_subset_of_forall_exists_gt`.
* **The broken geodesic is unbroken and coincides with `γ`**: Corollary 10.7 applies because both
  pieces have unit speed (so does the one-sided derivative at the break) and the broken path is
  minimal; that it coincides with `γ` is the uniqueness of geodesics in the large
  (`Morse.IsGeodesicOn.eqOn`) from a time before the break, extended to the endpoint by
  continuity.  Milnor's minimal geodesic from `γ(t₀)` to `p₀'` is the radial geodesic of the
  normal ball (Theorem 10.4).
* **Completeness is used only at `p`**: the proof only needs the geodesic `t ↦ exp_p(tv)`
  (`Morse.theorem_10_9`), as the exposition notes.
* **Corollary 10.10** needs: `exp_p` continuous on the whole disk (`Morse.continuousOn_exp`, the
  global dependence on initial conditions, not given by Lemma 10.2); `M` connected, so that
  distances are finite and Theorem 10.9 applies to all of `X`; and, for completeness, that a
  Cauchy sequence is bounded and that a Cauchy sequence with a convergent subsequence converges.
* **Bounded closed sets are compact** (the form in which the theorem is usually quoted) follows
  from "bounded sets have compact closure" because that closure lies in `N`.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace ENNReal NNReal

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

/-! ### Minimal geodesics -/

/-- **A minimal geodesic** (Milnor, p. 61) on `[a, b]`: the restriction of a geodesic on an open
set containing `[a, b]`, whose length is at most the length of every piecewise smooth path in `N`
with the same endpoints. -/
def IsMinimalGeodesic (γ : ℝ → V) (a b : ℝ) : Prop :=
  a ≤ b ∧ (∃ s, Icc a b ⊆ s ∧ IsGeodesicOn hN γ s) ∧
    ∀ (c : ℝ → V) (a' b' : ℝ), IsPiecewiseSmooth c a' b' → (∀ t ∈ Icc a' b', c t ∈ N) →
      c a' = γ a → c b' = γ b → pathLength γ a b ≤ pathLength c a' b'

variable {hN}

/-- `exp` takes values in `N` on its domain. -/
theorem exp_mem_of_mem_expDom {p v : V} (h : (p, v) ∈ expDom hN) : exp hN p v ∈ N := by
  obtain ⟨γ, hγ, he⟩ := exp_eq_of_mem_expDom h
  obtain ⟨δ, hδ, hγo, -, -⟩ := hγ
  rw [he]
  exact hγo.mem 1 ⟨by linarith, by linarith⟩

/-! ### The nearest point of a small sphere -/

namespace NormalCoord

variable {p : N} {ε : ℝ} (nc : NormalCoord hN p ε)

include nc in
/-- **Step 1 of Milnor's proof of Theorem 10.9** (p. 63): if `0 < δ < ε` (`ε` a normal radius at
`p`) and `δ < ρ(p, q) < ∞`, there is a point `p₀ = exp_p(w)`, `‖w‖ = δ`, on the sphere
`S = exp_p(S_δ)` with `ρ(p, q) = δ + ρ(p₀, q)`.  Every path from `p` to `q` crosses `S`
(`Morse.NormalCoord.exists_crossing`: this needs `δ < ρ(p, q)`), so
`ρ(p, q) ≥ δ + min_{s ∈ S} ρ(s, q)`; the minimum exists since `S` is compact and `ρ(·, q)` is
continuous (`Morse.continuousOn_riemDist_left`); the reverse inequality is the triangle
inequality with `ρ(p, s) = δ` on `S`. -/
theorem exists_riemDist_eq_add {δ : ℝ} (hδ : 0 < δ) (hδε : δ < ε) {q : V}
    (hq : ENNReal.ofReal δ < riemDist (N := N) p q) (hq' : riemDist (N := N) p q ≠ ⊤) :
    ∃ w ∈ tangentSubspace hN p, ‖w‖ = δ ∧
      riemDist (N := N) p q = ENNReal.ofReal δ + riemDist (N := N) (exp hN p w) q := by
  have hqN : q ∈ N := by
    by_contra h
    exact hq' (riemDist_eq_top_of_notMem h)
  have hqball : q ∉ nc.ballSet δ := fun h =>
    absurd ((nc.riemDist_lt_iff hδ hδε.le).2 ⟨hqN, h⟩) (not_lt.2 hq.le)
  -- the sphere `S = exp_p(S_δ)`
  set Sph : Set V := sphere (0 : V) δ ∩ (tangentSubspace hN p : Set V) with hSph
  set S : Set V := (fun w => exp hN p w) '' Sph with hS_def
  have hSph_ε : ∀ w ∈ Sph, w ∈ tangentSubspace hN p ∧ ‖w‖ < ε := fun w hw =>
    ⟨hw.2, by rw [← mem_sphere_zero_iff_norm.1 hw.1] at hδε; exact hδε⟩
  have hSc : IsCompact S := by
    have hK : IsCompact Sph :=
      (isCompact_sphere 0 δ).inter_right (Submodule.closed_of_finiteDimensional _)
    have heq : S = nc.F '' Sph :=
      image_congr fun w hw => (nc.F_eq w (hSph_ε w hw).1 (hSph_ε w hw).2).symm
    rw [heq]
    exact hK.image_of_continuousOn (nc.contDiffOn_F.continuousOn.mono fun w hw =>
      nc.mem_O w (hSph_ε w hw).1 (hSph_ε w hw).2)
  have hSN : S ⊆ N := by
    rintro _ ⟨w, hw, rfl⟩
    exact nc.exp_mem (hSph_ε w hw).1 (hSph_ε w hw).2
  -- every path from `p` to `q` crosses `S`
  have hcross : ∀ L ∈ pathLengths (N := N) p q,
      ∃ y ∈ S, ENNReal.ofReal δ + riemDist (N := N) y q ≤ L := by
    rintro L ⟨c, a, b, hc, hcN, ha, hb, rfl⟩
    obtain ⟨t₁, t₂, ht₁, ht₁₂, ht₂, -, hU, hG, -, hL⟩ :=
      nc.exists_crossing hc.isAdmissible hcN ha hδ hδε (by rw [hb]; exact hqball)
    have hyU : c t₂ ∈ nc.U := (hU t₂ ⟨ht₁₂, le_rfl⟩).1
    have hyN : c t₂ ∈ N := hcN t₂ ⟨by linarith, ht₂⟩
    refine ⟨c t₂, ⟨nc.G (c t₂), ⟨mem_sphere_zero_iff_norm.2 hG, nc.G_mem _ hyU hyN⟩,
      nc.exp_G _ hyU hyN⟩, ?_⟩
    have h1 := riemDist_le_pathLength (N := N) (hc.mono (by linarith) ht₂ le_rfl)
      fun t ht => hcN t ⟨by linarith [ht.1], ht.2⟩
    rw [hb] at h1
    have h2 := hc.isAdmissible.pathLength_add (m := t₂) ⟨by linarith, ht₂⟩
    have h3 := (hc.isAdmissible.mono le_rfl (by linarith) ht₂).pathLength_le ht₁ ht₁₂.le le_rfl
    have h4 := (hc.isAdmissible.mono (by linarith) ht₂ le_rfl).pathLength_nonneg
    calc ENNReal.ofReal δ + riemDist (N := N) (c t₂) q
        ≤ ENNReal.ofReal δ + ENNReal.ofReal (pathLength c t₂ b) := by gcongr
      _ = ENNReal.ofReal (δ + pathLength c t₂ b) := (ENNReal.ofReal_add hδ.le h4).symm
      _ ≤ ENNReal.ofReal (pathLength c a b) := ENNReal.ofReal_le_ofReal (by linarith)
  -- `S` is not empty: a path from `p` to `q` exists
  have hne : S.Nonempty := by
    have : (pathLengths (N := N) p q).Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty] at h
      exact hq' (by rw [riemDist, h, sInf_empty])
    obtain ⟨L, hL⟩ := this
    obtain ⟨y, hy, -⟩ := hcross L hL
    exact ⟨y, hy⟩
  -- the point of `S` nearest to `q`
  obtain ⟨y₀, hy₀S, hy₀⟩ := hSc.exists_isMinOn hne ((continuousOn_riemDist_left hN q).mono hSN)
  obtain ⟨w₀, hw₀, rfl⟩ := hy₀S
  have hw₀n : ‖w₀‖ = δ := mem_sphere_zero_iff_norm.1 hw₀.1
  refine ⟨w₀, hw₀.2, hw₀n, le_antisymm ?_ ?_⟩
  · refine (riemDist_triangle (N := N) p (exp hN p w₀) q).trans_eq ?_
    rw [nc.riemDist_exp hw₀.2 (hSph_ε w₀ hw₀).2, hw₀n]
  · refine le_sInf fun L hL => ?_
    obtain ⟨y, hyS, hy⟩ := hcross L hL
    refine le_trans ?_ hy
    gcongr
    exact isMinOn_iff.1 hy₀ y hyS

end NormalCoord

/-! ### Broken geodesics -/

/-- **A broken geodesic of minimal length is unbroken** (Milnor, p. 63: the broken geodesic has
minimal length, hence is an unbroken geodesic by Corollary 10.7, hence coincides with `γ`).  Let
`γ` be a unit-speed geodesic on `ℝ`, `0 < t₀ < t₁`, and `σ` a unit-speed geodesic on an open
interval containing `[t₀, t₁]`, with `σ(t₀) = γ(t₀)`.  If the broken path (`γ` on `[0, t₀]`, then
`σ`), of length `t₁`, is minimal, i.e. `ρ(γ(0), σ(t₁)) ≥ t₁`, then `σ(t₁) = γ(t₁)`.  The broken
path is a geodesic on `(0, t₁)` by Corollary 10.7 (`Morse.corollary_10_7`); it agrees with `γ`
near `t₀/2`, hence on `(0, t₁)` by uniqueness (`Morse.IsGeodesicOn.eqOn`), and at `t₁` by
continuity. -/
theorem broken_geodesic_eq {γ σ : ℝ → V} (hγ : IsGeodesicOn hN γ univ) (hγ1 : ‖deriv γ 0‖ = 1)
    {s : Set ℝ} (hσ : IsGeodesicOn hN σ s) (hs : IsPreconnected s) {t₀ t₁ : ℝ} (ht₀ : 0 < t₀)
    (ht₀₁ : t₀ < t₁) (hsub : Icc t₀ t₁ ⊆ s) (hσ1 : ‖deriv σ t₀‖ = 1) (hjoin : σ t₀ = γ t₀)
    (hmin : ENNReal.ofReal t₁ ≤ riemDist (N := N) (γ 0) (σ t₁)) : σ t₁ = γ t₁ := by
  classical
  set c : ℝ → V := fun t => if t ≤ t₀ then γ t else σ t with hc_def
  have hγps : IsPiecewiseSmooth γ 0 t₀ :=
    IsPiecewiseSmooth.of_contDiffOn hγ.contDiffOn ht₀.le (subset_univ _)
  have hσps : IsPiecewiseSmooth σ t₀ t₁ :=
    IsPiecewiseSmooth.of_contDiffOn hσ.contDiffOn ht₀₁.le hsub
  have hcps : IsPiecewiseSmooth c 0 t₁ := hγps.concat hσps hjoin.symm
  have hcN : ∀ t ∈ Icc 0 t₁, c t ∈ N := fun t ht => by
    simp only [hc_def]
    split_ifs with h
    · exact hγ.mem t (mem_univ _)
    · exact hσ.mem t (hsub ⟨(not_le.1 h).le, ht.2⟩)
  have hγspeed : ∀ t, ‖deriv γ t‖ = 1 := fun t =>
    (hγ.norm_deriv_eq isPreconnected_univ (mem_univ t) (mem_univ 0)).trans hγ1
  have hσspeed : ∀ t ∈ s, ‖deriv σ t‖ = 1 := fun t ht =>
    (hσ.norm_deriv_eq hs ht (hsub ⟨le_rfl, ht₀₁.le⟩)).trans hσ1
  have hunit : ∀ t ∈ Ioo 0 t₁, DifferentiableAt ℝ c t → ‖deriv c t‖ = 1 := by
    intro t ht hdiff
    rcases lt_trichotomy t t₀ with hlt | heq | hgt
    · have hev : c =ᶠ[𝓝 t] γ := by
        filter_upwards [Iio_mem_nhds hlt] with x hx
        simp only [hc_def, if_pos (mem_Iio.1 hx).le]
      rw [hev.deriv_eq]
      exact hγspeed t
    · subst heq
      have h1 : HasDerivWithinAt c (deriv c t) (Iic t) t := hdiff.hasDerivAt.hasDerivWithinAt
      have h2 : HasDerivWithinAt c (deriv γ t) (Iic t) t :=
        ((hγ.hasDerivAt (mem_univ t)).hasDerivWithinAt).congr
          (fun x hx => by simp only [hc_def, if_pos (mem_Iic.1 hx)])
          (by simp only [hc_def, le_refl, if_true])
      rw [(uniqueDiffWithinAt_Iic t).eq_deriv _ h1 h2]
      exact hγspeed t
    · have hev : c =ᶠ[𝓝 t] σ := by
        filter_upwards [Ioi_mem_nhds hgt] with x hx
        simp only [hc_def, if_neg (not_le.2 (mem_Ioi.1 hx))]
      rw [hev.deriv_eq]
      exact hσspeed t (hsub ⟨hgt.le, ht.2.le⟩)
  have hlen : pathLength c 0 t₁ = t₁ := by
    rw [pathLength_eq_of_norm_deriv hcps.isAdmissible hunit]
    ring
  have hc0 : c 0 = γ 0 := by simp only [hc_def, if_pos ht₀.le]
  have hct₁ : c t₁ = σ t₁ := by simp only [hc_def, if_neg (not_le.2 ht₀₁)]
  have hmin' : ∀ (c' : ℝ → V) (a b : ℝ), IsPiecewiseSmooth c' a b →
      (∀ t ∈ Icc a b, c' t ∈ N) → c' a = c 0 → c' b = c t₁ →
      pathLength c 0 t₁ ≤ pathLength c' a b := by
    intro c' a b hc' hc'N ha hb
    have h1 := riemDist_le_pathLength (N := N) hc' hc'N
    rw [ha, hb, hc0, hct₁] at h1
    rw [hlen]
    exact (ENNReal.ofReal_le_ofReal_iff hc'.isAdmissible.pathLength_nonneg).1 (hmin.trans h1)
  have hcgeo := corollary_10_7 hN hcps hcN hunit hmin'
  -- the broken path agrees with `γ` near `t₀ / 2`, hence on `(0, t₁)`
  have hhalf : t₀ / 2 ∈ Ioo 0 t₁ := ⟨by linarith, by linarith⟩
  have hev : c =ᶠ[𝓝 (t₀ / 2)] γ := by
    filter_upwards [Iio_mem_nhds (by linarith : t₀ / 2 < t₀)] with x hx
    simp only [hc_def, if_pos (le_of_lt (mem_Iio.1 hx))]
  have heq := hcgeo.eqOn (hγ.mono isOpen_Ioo (subset_univ _)) isPreconnected_Ioo hhalf
    hev.self_of_nhds hev.deriv_eq
  -- and at `t₁`, by continuity
  have heq' : EqOn c γ (Icc 0 t₁) :=
    heq.of_subset_closure hcps.2.1 (hγ.contDiffOn.continuousOn.mono (subset_univ _))
      Ioo_subset_Icc_self (by rw [closure_Ioo (by linarith : (0 : ℝ) ≠ t₁)])
  rw [← hct₁]
  exact heq' ⟨by linarith, le_rfl⟩

/-! ### Theorem 10.9 -/

/-- A geodesic `t ↦ exp_p(tv)` on `ℝ` from `p` to `q` on `[0, 1]`, of length `‖v‖ = ρ(p, q)`, is
minimal. -/
theorem isMinimalGeodesic_exp_smul {p : N} {v : V} (hv : v ∈ tangentSubspace hN p)
    (hgeo : IsGeodesicOn hN (fun t => exp hN p (t • v)) univ)
    (hρ : riemDist (N := N) p (exp hN p v) = ENNReal.ofReal ‖v‖) :
    IsMinimalGeodesic hN (fun t => exp hN p (t • v)) 0 1 ∧
      pathLength (fun t => exp hN p (t • v)) 0 1 = ‖v‖ := by
  have hlen : pathLength (fun t => exp hN p (t • v)) 0 1 = ‖v‖ := by
    rw [hgeo.pathLength_eq isPreconnected_univ zero_le_one (subset_univ _) (mem_univ 0),
      (hasDerivAt_exp_smul_zero p hv).deriv]
    ring
  refine ⟨⟨zero_le_one, ⟨univ, subset_univ _, hgeo⟩, fun c a b hc hcN ha hb => ?_⟩, hlen⟩
  have h1 := riemDist_le_pathLength (N := N) hc hcN
  simp only [ha, hb, zero_smul, one_smul, exp_zero p.2, hρ] at h1
  rw [hlen]
  exact (ENNReal.ofReal_le_ofReal_iff hc.isAdmissible.pathLength_nonneg).1 h1

/-- **Theorem 10.9 (Hopf–Rinow), at one point** (Milnor, pp. 62–64, with the exposition's remark
that completeness is used only at `p`).  If `exp_p` is defined on all of `T_pN`, every `q ∈ N` at
finite distance from `p` is joined to `p` by a minimal geodesic: there is `v ∈ T_pN` with
`exp_p(v) = q` and `‖v‖ = ρ(p, q)`, and `t ↦ exp_p(tv)`, `0 ≤ t ≤ 1`, is a minimal geodesic.

Milnor's proof: for a small sphere `S` about `p` and its point `p₀ = exp_p(δu)` nearest to `q`
(`Morse.NormalCoord.exists_riemDist_eq_add`), the geodesic `γ(t) = exp_p(tu)` satisfies
`ρ(γ(t), q) = r − t` for `t ∈ [δ, r]`, `r = ρ(p, q)`: the set of such `t` is closed, and if `t₀`
is in it, `t₀ < r`, the same construction at `γ(t₀)` with radius `δ' < r − t₀` produces a broken
geodesic of minimal length, which is unbroken (`Morse.broken_geodesic_eq`), so `t₀ + δ'` is in it
too; continuous induction (`IsClosed.Icc_subset_of_forall_exists_gt`) gives `t = r`, so
`γ(r) = q`. -/
theorem theorem_10_9 {p : N} (hp : ∀ v ∈ tangentSubspace hN p, ((p : V), v) ∈ expDom hN)
    {q : N} (hpq : riemDist (N := N) p q ≠ ⊤) :
    ∃ v ∈ tangentSubspace hN p, exp hN p v = q ∧ riemDist (N := N) p q = ENNReal.ofReal ‖v‖ ∧
      IsMinimalGeodesic hN (fun t => exp hN p (t • v)) 0 1 := by
  set r := (riemDist (N := N) p q).toReal with hr_def
  have hr : riemDist (N := N) p q = ENNReal.ofReal r := (ENNReal.ofReal_toReal hpq).symm
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  have hfinish : ∀ v ∈ tangentSubspace hN p, exp hN p v = q → ‖v‖ = r →
      ∃ v ∈ tangentSubspace hN p, exp hN p v = q ∧
        riemDist (N := N) p q = ENNReal.ofReal ‖v‖ ∧
        IsMinimalGeodesic hN (fun t => exp hN p (t • v)) 0 1 := by
    intro v hv hexp hvr
    have hρ : riemDist (N := N) p q = ENNReal.ofReal ‖v‖ := by rw [hvr, hr]
    refine ⟨v, hv, hexp, hρ, (isMinimalGeodesic_exp_smul hv (isGeodesicOn_univ_exp_smul hp hv)
      (by rw [hexp, hρ])).1⟩
  rcases eq_or_lt_of_le hr0 with hr0' | hrpos
  · have hpq' : p = q := eq_of_riemDist_eq_zero hN (by rw [hr, ← hr0', ENNReal.ofReal_zero])
    exact hfinish 0 (Submodule.zero_mem _) (by rw [exp_zero p.2, hpq']) (by rw [norm_zero, hr0'])
  -- Step 1 at `p`
  obtain ⟨ε, hε, ⟨nc⟩⟩ := exists_isNormalRadius hN p
  set δ := min ε r / 2 with hδ_def
  have hδ : 0 < δ := by positivity
  have hδε : δ < ε := by have := min_le_left ε r; linarith
  have hδr : δ < r := by have := min_le_right ε r; linarith
  obtain ⟨w₀, hw₀, hw₀n, hstep₁⟩ := nc.exists_riemDist_eq_add hδ hδε
    (by rw [hr]; exact (ENNReal.ofReal_lt_ofReal_iff hrpos).2 hδr) hpq
  -- the unit-speed geodesic `γ(t) = exp_p(tu)`
  set u := δ⁻¹ • w₀ with hu_def
  have hu : u ∈ tangentSubspace hN p := Submodule.smul_mem _ _ hw₀
  have hun : ‖u‖ = 1 := by
    rw [hu_def, norm_smul, hw₀n, Real.norm_eq_abs, abs_inv, abs_of_pos hδ, inv_mul_cancel₀ hδ.ne']
  set γ : ℝ → V := fun t => exp hN p (t • u) with hγ_def
  have hγgeo : IsGeodesicOn hN γ univ := isGeodesicOn_univ_exp_smul hp hu
  have hγ0 : γ 0 = p := by simp only [hγ_def, zero_smul, exp_zero p.2]
  have hγd : deriv γ 0 = u := (hasDerivAt_exp_smul_zero p hu).deriv
  have hγδ : γ δ = exp hN p w₀ := by
    simp only [hγ_def, hu_def, smul_smul, mul_inv_cancel₀ hδ.ne', one_smul]
  have hγc : Continuous γ := continuous_iff_continuousAt.2 fun t =>
    (hγgeo.hasDerivAt (mem_univ t)).continuousAt
  -- the set of `t` with `ρ(γ(t), q) = r − t`
  set A : Set ℝ := {t | riemDist (N := N) (γ t) q = ENNReal.ofReal (r - t)} with hA_def
  have hAc : IsClosed A := isClosed_eq
    ((continuousOn_riemDist_left hN q).comp_continuous hγc fun t => hγgeo.mem t (mem_univ t))
    (ENNReal.continuous_ofReal.comp (continuous_const.sub continuous_id))
  have hδA : δ ∈ A := by
    change riemDist (N := N) (γ δ) q = ENNReal.ofReal (r - δ)
    rw [hγδ, ENNReal.ofReal_sub r hδ.le]
    rw [hr, add_comm] at hstep₁
    exact ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top hstep₁.symm
  -- the inductive step
  have hgt : ∀ x ∈ A ∩ Ico δ r, ∀ y ∈ Ioi x, (A ∩ Ioc x y).Nonempty := by
    rintro t₀ ⟨ht₀A, hδt₀, ht₀r⟩ y hy
    have hy : t₀ < y := hy
    have ht₀ : 0 < t₀ := lt_of_lt_of_le hδ hδt₀
    set x₀ : N := ⟨γ t₀, hγgeo.mem t₀ (mem_univ _)⟩
    obtain ⟨ε', hε', ⟨nc'⟩⟩ := exists_isNormalRadius hN x₀
    set δ' := min ε' (min (r - t₀) (y - t₀)) / 2 with hδ'_def
    have hδ' : 0 < δ' := by
      have : 0 < min (r - t₀) (y - t₀) := lt_min (by linarith) (by linarith)
      positivity
    have hm1 := min_le_left ε' (min (r - t₀) (y - t₀))
    have hm2 := min_le_right ε' (min (r - t₀) (y - t₀))
    have hm3 := min_le_left (r - t₀) (y - t₀)
    have hm4 := min_le_right (r - t₀) (y - t₀)
    have hδ'ε : δ' < ε' := by linarith
    have hδ'r : δ' < r - t₀ := by linarith
    have hδ'y : δ' < y - t₀ := by linarith
    have hρx₀ : riemDist (N := N) x₀ q = ENNReal.ofReal (r - t₀) := ht₀A
    obtain ⟨w, hw, hwn, hstep⟩ := nc'.exists_riemDist_eq_add hδ' hδ'ε
      (by rw [hρx₀]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hδ'r)
      (by rw [hρx₀]; exact ENNReal.ofReal_ne_top)
    -- `ρ(p₀', q) = r − t₀ − δ'`
    have hρp₀' : riemDist (N := N) (exp hN x₀ w) q = ENNReal.ofReal (r - (t₀ + δ')) := by
      rw [show r - (t₀ + δ') = (r - t₀) - δ' by ring, ENNReal.ofReal_sub _ hδ'.le]
      rw [hρx₀, add_comm] at hstep
      exact ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top hstep.symm
    -- `ρ(p, p₀') ≥ t₀ + δ'`
    have hfar : ENNReal.ofReal (t₀ + δ') ≤ riemDist (N := N) p (exp hN x₀ w) := by
      have h1 := riemDist_triangle (N := N) p (exp hN x₀ w) q
      rw [hr, hρp₀'] at h1
      have h2 : ENNReal.ofReal r = ENNReal.ofReal (t₀ + δ') + ENNReal.ofReal (r - (t₀ + δ')) := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
        ring_nf
      rw [h2] at h1
      exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 h1
    -- the radial geodesic `σ` from `γ(t₀)` to `p₀'`, at unit speed
    obtain ⟨δ'', hδ'', hrad, hrad0⟩ := nc'.radial hw (by rw [hwn]; exact hδ'ε)
    set a := δ'⁻¹ with ha_def
    have ha : 0 < a := inv_pos.2 hδ'
    have hσgeo := hrad.comp_mul_add a (-a * t₀)
    set σ : ℝ → V := fun t => exp hN x₀ ((a * t + -a * t₀) • w) with hσ_def
    have hsub : Icc t₀ (t₀ + δ') ⊆ (fun t => a * t + -a * t₀) ⁻¹' Ioo (-δ'') (1 + δ'') := by
      intro t ht
      have h1 : a * t + -a * t₀ = (t - t₀) / δ' := by rw [ha_def]; field_simp; ring
      simp only [mem_preimage, h1, mem_Ioo]
      constructor
      · have : 0 ≤ (t - t₀) / δ' := div_nonneg (by linarith [ht.1]) hδ'.le
        linarith
      · have : (t - t₀) / δ' ≤ 1 := (div_le_one hδ').2 (by linarith [ht.2])
        linarith
    have hσt₀ : σ t₀ = γ t₀ := by
      simp only [hσ_def, show a * t₀ + -a * t₀ = 0 by ring, zero_smul, exp_zero x₀.2]
      rfl
    have hσend : σ (t₀ + δ') = exp hN x₀ w := by
      have h1 : a * (t₀ + δ') + -a * t₀ = 1 := by rw [ha_def]; field_simp; ring
      simp only [hσ_def, h1, one_smul]
    have hσd : ‖deriv σ t₀‖ = 1 := by
      have hlin : HasDerivAt (fun t : ℝ => a * t + -a * t₀) a t₀ := by
        simpa using ((hasDerivAt_id t₀).const_mul a).add_const (-a * t₀)
      have hf : HasDerivAt (fun τ : ℝ => exp hN x₀ (τ • w)) w (a * t₀ + -a * t₀) := by
        rw [show a * t₀ + -a * t₀ = 0 by ring]
        have := hrad.hasDerivAt (t := 0) ⟨by linarith, by linarith⟩
        rwa [hrad0] at this
      have h2 := hf.scomp t₀ hlin
      have hσeq : deriv σ t₀ = a • w := h2.deriv
      rw [hσeq, norm_smul, hwn, Real.norm_eq_abs, abs_of_pos ha, ha_def,
        inv_mul_cancel₀ hδ'.ne']
    have hmin : ENNReal.ofReal (t₀ + δ') ≤ riemDist (N := N) (γ 0) (σ (t₀ + δ')) := by
      rw [hγ0, hσend]
      exact hfar
    have hgun : ‖deriv γ 0‖ = 1 := by rw [hγd, hun]
    have hbroken := broken_geodesic_eq hγgeo hgun hσgeo (isPreconnected_preimage_mul_add
      isPreconnected_Ioo a (-a * t₀)) ht₀ (by linarith) hsub hσd hσt₀ hmin
    refine ⟨t₀ + δ', ?_, by linarith, by linarith⟩
    change riemDist (N := N) (γ (t₀ + δ')) q = ENNReal.ofReal (r - (t₀ + δ'))
    rw [← hbroken, hσend, hρp₀']
  have hIcc := IsClosed.Icc_subset_of_forall_exists_gt (hAc.inter isClosed_Icc) hδA hgt
  have hrA : r ∈ A := hIcc ⟨hδr.le, le_rfl⟩
  have hγr : γ r = q := by
    have h0 : riemDist (N := N) (γ r) q = 0 := by
      have : riemDist (N := N) (γ r) q = ENNReal.ofReal (r - r) := hrA
      rw [this, sub_self, ENNReal.ofReal_zero]
    have := eq_of_riemDist_eq_zero hN (p := ⟨γ r, hγgeo.mem r (mem_univ _)⟩) (q := q) h0
    exact congrArg Subtype.val this
  refine hfinish (r • u) (Submodule.smul_mem _ _ hu) ?_ ?_
  · rw [← hγr]
  · rw [norm_smul, hun, mul_one, Real.norm_eq_abs, abs_of_nonneg hr0]

/-- **Theorem 10.9 (Hopf–Rinow)**, Milnor's statement (p. 62): if `N` is connected and
geodesically complete, any two points of `N` are joined by a minimal geodesic, whose length is
their distance. -/
theorem theorem_10_9' (hconn : IsPreconnected N) (hc : IsGeodesicallyComplete hN) (p q : N) :
    ∃ γ : ℝ → V, IsMinimalGeodesic hN γ 0 1 ∧ γ 0 = p ∧ γ 1 = q ∧
      riemDist (N := N) p q = ENNReal.ofReal (pathLength γ 0 1) := by
  obtain ⟨v, hv, hexp, hρ, hmin⟩ := theorem_10_9 (hc p) (riemDist_ne_top hN hconn p.2 q.2)
  have hlen := (isMinimalGeodesic_exp_smul hv (isGeodesicOn_univ_exp_smul (hc p) hv)
    (by rw [hexp, hρ])).2
  refine ⟨_, hmin, by simp only [zero_smul, exp_zero p.2], by simp only [one_smul, hexp], ?_⟩
  rw [hlen, hρ]

/-! ### Corollary 10.10 -/

/-- **Corollary 10.10, first part, at one point**: if `N` is connected and `exp_p` is defined on
all of `T_pN`, every `ρ`-bounded set `X` has compact closure, contained in `N`.  (Milnor, p. 64:
`X` lies in `exp_p` of a closed disk of `T_pN`, by Theorem 10.9; that image is compact because
`exp_p` is continuous on the whole disk, `Morse.continuousOn_exp`, which Milnor does not prove.) -/
theorem isCompact_closure_of_isRiemBounded {p : N}
    (hp : ∀ v ∈ tangentSubspace hN p, ((p : V), v) ∈ expDom hN) (hconn : IsPreconnected N)
    {X : Set V} (hX : IsRiemBounded N X) : IsCompact (closure X) ∧ closure X ⊆ N := by
  rcases X.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  obtain ⟨d, hd⟩ := hX
  have hXN : X ⊆ N := fun x hx => by
    by_contra h
    have := hd x hx x hx
    rw [riemDist_eq_top_of_notMem h] at this
    exact ENNReal.ofReal_ne_top (top_le_iff.1 this)
  set d' := max d 0 with hd'_def
  have hd' : 0 ≤ d' := le_max_right d 0
  set R := (riemDist (N := N) p x₀).toReal + d' with hR_def
  have hR0 : 0 ≤ R := add_nonneg ENNReal.toReal_nonneg hd'
  have hρR : ∀ x ∈ X, riemDist (N := N) p x ≤ ENNReal.ofReal R := by
    intro x hx
    rw [hR_def, ENNReal.ofReal_add ENNReal.toReal_nonneg hd',
      ENNReal.ofReal_toReal (riemDist_ne_top hN hconn p.2 (hXN hx₀))]
    refine (riemDist_triangle (N := N) p x₀ x).trans ?_
    gcongr
    exact (hd x₀ hx₀ x hx).trans (ENNReal.ofReal_le_ofReal (le_max_left d 0))
  set K := (fun v => exp hN p v) '' (closedBall (0 : V) R ∩ (tangentSubspace hN p : Set V))
    with hK_def
  have hKc : IsCompact K :=
    ((isCompact_closedBall 0 R).inter_right
      (Submodule.closed_of_finiteDimensional _)).image_of_continuousOn
      ((continuousOn_exp hp).mono inter_subset_right)
  have hKN : K ⊆ N := by
    rintro _ ⟨v, hv, rfl⟩
    exact exp_mem_of_mem_expDom (hp v hv.2)
  have hXK : X ⊆ K := by
    intro x hx
    obtain ⟨v, hv, hexp, hρ, -⟩ := theorem_10_9 hp (q := ⟨x, hXN hx⟩)
      (riemDist_ne_top hN hconn p.2 (hXN hx))
    refine ⟨v, ⟨?_, hv⟩, hexp⟩
    rw [mem_closedBall, dist_zero_right]
    have := hρR x hx
    rw [show riemDist (N := N) p x = ENNReal.ofReal ‖v‖ from hρ] at this
    exact (ENNReal.ofReal_le_ofReal_iff hR0).1 this
  have hcl : closure X ⊆ K := closure_minimal hXK hKc.isClosed
  exact ⟨hKc.of_isClosed_subset isClosed_closure hcl, hcl.trans hKN⟩

variable (hN) in
include hN in
/-- **Corollary 10.10, second part** (Milnor, p. 64: consequently `M` is complete as a metric
space): if every `ρ`-bounded set has compact closure in `N`, then `(N, ρ)` is complete.  A Cauchy
sequence is eventually bounded, so it has a subsequence converging to a point of `N`, and a Cauchy
sequence with a convergent subsequence converges. -/
theorem isRiemComplete_of_forall_isCompact_closure
    (h : ∀ X : Set V, IsRiemBounded N X → IsCompact (closure X) ∧ closure X ⊆ N) :
    IsRiemComplete N := by
  intro x hxN hx
  obtain ⟨n₀, hn₀⟩ := hx 1 one_pos
  set X := range fun k : ℕ => x (k + n₀) with hX_def
  have hXb : IsRiemBounded N X := by
    refine ⟨1, ?_⟩
    rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
    exact (hn₀ _ (by omega) _ (by omega)).le
  obtain ⟨hXc, hXN⟩ := h X hXb
  obtain ⟨y, hy, φ, hφ, hlim⟩ := hXc.tendsto_subseq (x := fun k => x (k + n₀))
    fun k => subset_closure ⟨k, rfl⟩
  have hyN : y ∈ N := hXN hy
  have hsub : Tendsto (fun k => riemDist (N := N) (x (φ k + n₀)) y) atTop (𝓝 0) :=
    tendsto_riemDist_of_tendsto hN hyN (tendsto_nhdsWithin_iff.2
      ⟨hlim, Eventually.of_forall fun k => hxN _⟩)
  refine ⟨y, hyN, ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_⟩
  obtain ⟨η, -, hη1, hη2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hη : 0 < η := ENNReal.ofReal_pos.1 hη1
  obtain ⟨n₁, hn₁⟩ := hx (η / 2) (by positivity)
  have hev := (hsub.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (half_pos hη)))).and
    (hφ.tendsto_atTop.eventually (eventually_ge_atTop n₁))
  obtain ⟨k, hk1, hk2⟩ := hev.exists
  filter_upwards [eventually_ge_atTop n₁] with n hn
  calc riemDist (N := N) (x n) y ≤ riemDist (N := N) (x n) (x (φ k + n₀)) +
        riemDist (N := N) (x (φ k + n₀)) y := riemDist_triangle _ _ _
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) :=
        add_le_add (hn₁ n hn _ (by omega)).le hk1.le
    _ = ENNReal.ofReal η := by rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]
    _ ≤ ε := hη2.le

/-- **Corollary 10.10** (Milnor, p. 64): if `N` is connected and geodesically complete, then every
`ρ`-bounded subset of `N` has compact closure, and consequently `(N, ρ)` is complete as a metric
space. -/
theorem corollary_10_10 (hconn : IsPreconnected N) (hc : IsGeodesicallyComplete hN) :
    (∀ X : Set V, IsRiemBounded N X → IsCompact (closure X) ∧ closure X ⊆ N) ∧
      IsRiemComplete N := by
  rcases N.eq_empty_or_nonempty with hN0 | ⟨p, hp⟩
  · have h : ∀ X : Set V, IsRiemBounded N X → IsCompact (closure X) ∧ closure X ⊆ N := by
      intro X hX
      have hX0 : X = ∅ := by
        rcases X.eq_empty_or_nonempty with h | ⟨x, hx⟩
        · exact h
        · obtain ⟨d, hd⟩ := hX
          have := hd x hx x hx
          rw [riemDist_eq_top_of_notMem (by rw [hN0]; exact notMem_empty x)] at this
          exact absurd (top_le_iff.1 this) ENNReal.ofReal_ne_top
      simp [hX0]
    exact ⟨h, isRiemComplete_of_forall_isCompact_closure hN h⟩
  have h := fun X hX => isCompact_closure_of_isRiemBounded (hc ⟨p, hp⟩) hconn (X := X) hX
  exact ⟨h, isRiemComplete_of_forall_isCompact_closure hN h⟩

/-! ### The Hopf–Rinow theorem -/

omit [FiniteDimensional ℝ V] in
/-- **Bounded closed subsets are compact** (the Heine–Borel property), when bounded sets have
compact closure. -/
theorem isCompact_of_isClosed_of_isRiemBounded
    (h : ∀ X : Set V, IsRiemBounded N X → IsCompact (closure X) ∧ closure X ⊆ N)
    {X : Set N} (hXc : IsClosed X) (hXb : IsRiemBounded N (Subtype.val '' X)) : IsCompact X := by
  obtain ⟨hc, hcN⟩ := h _ hXb
  have heq : Subtype.val '' X = closure (Subtype.val '' X) := by
    refine Subset.antisymm subset_closure fun y hy => ?_
    have hyX : (⟨y, hcN hy⟩ : N) ∈ closure X := closure_subtype.2 hy
    rw [hXc.closure_eq] at hyX
    exact ⟨_, hyX, rfl⟩
  rw [Topology.IsInducing.subtypeVal.isCompact_iff, heq]
  exact hc

variable (hN) in
/-- **The Hopf–Rinow theorem** (Milnor, Theorem 10.9, Corollary 10.10 and its converse,
pp. 62–64).  For a connected nonempty `N` the following are equivalent:
1. `(N, ρ)` is a complete metric space;
2. `N` is geodesically complete (`exp_q` is defined on all of `T_qN` for every `q`);
3. `exp_p` is defined on all of `T_pN` for some `p ∈ N`;
4. every `ρ`-bounded set has compact closure, contained in `N`. -/
theorem hopf_rinow (hconn : IsPreconnected N) (hne : N.Nonempty) :
    [IsRiemComplete N, IsGeodesicallyComplete hN,
      ∃ p : N, ∀ v ∈ tangentSubspace hN p, ((p : V), v) ∈ expDom hN,
      ∀ X : Set V, IsRiemBounded N X → IsCompact (closure X) ∧ closure X ⊆ N].TFAE := by
  tfae_have 1 → 2 := isGeodesicallyComplete_of_isRiemComplete
  tfae_have 2 → 3 := fun h => ⟨⟨hne.some, hne.some_mem⟩, h _⟩
  tfae_have 3 → 4 := fun ⟨p, hp⟩ X hX => isCompact_closure_of_isRiemBounded hp hconn hX
  tfae_have 4 → 1 := isRiemComplete_of_forall_isCompact_closure hN
  tfae_finish

variable (hN) in
/-- **The Hopf–Rinow theorem, for a complete `N`** (Milnor, Theorem 10.9 with Corollary 10.10 and
its converse).  If `N` is connected and `(N, ρ)` is complete, then
1. every geodesic extends to a geodesic on all of `ℝ`, i.e. `exp_q` is defined on all of `T_qN`
   for every `q ∈ N`;
2. any two points `p, q` are joined by a minimal geodesic `γ : [0, 1] → N`, of length `ρ(p, q)`;
3. every closed `ρ`-bounded subset of `N` is compact. -/
theorem hopf_rinow_of_isRiemComplete (hconn : IsPreconnected N) (h : IsRiemComplete N) :
    IsGeodesicallyComplete hN ∧
    (∀ (γ : ℝ → V) (s : Set ℝ), IsGeodesicOn hN γ s → IsPreconnected s → s.Nonempty →
      ∃ γ' : ℝ → V, IsGeodesicOn hN γ' univ ∧ EqOn γ' γ s) ∧
    (∀ p q : N, ∃ γ : ℝ → V, IsMinimalGeodesic hN γ 0 1 ∧ γ 0 = p ∧ γ 1 = q ∧
      riemDist (N := N) p q = ENNReal.ofReal (pathLength γ 0 1)) ∧
    (∀ X : Set N, IsClosed X → IsRiemBounded N (Subtype.val '' X) → IsCompact X) := by
  have hc := isGeodesicallyComplete_of_isRiemComplete (hN := hN) h
  exact ⟨hc, isGeodesicallyComplete_iff.1 hc, theorem_10_9' hconn hc,
    fun X hXc hXb => isCompact_of_isClosed_of_isRiemBounded (corollary_10_10 hconn hc).1 hXc hXb⟩

/-! ### Closed submanifolds; the round sphere -/

variable (hN) in
/-- **Closed submanifolds are complete** (the key application in the embedded setting): if `N` is
connected and closed in `V`, then `(N, ρ)` is complete (`Morse.isRiemComplete_of_isClosed`), so
all the conclusions of the Hopf–Rinow theorem hold: geodesics extend to `ℝ`, any two points are
joined by a minimal geodesic, and closed bounded subsets are compact. -/
theorem hopf_rinow_of_isClosed (hconn : IsPreconnected N) (hcl : IsClosed N) :
    IsGeodesicallyComplete hN ∧
    (∀ (γ : ℝ → V) (s : Set ℝ), IsGeodesicOn hN γ s → IsPreconnected s → s.Nonempty →
      ∃ γ' : ℝ → V, IsGeodesicOn hN γ' univ ∧ EqOn γ' γ s) ∧
    (∀ p q : N, ∃ γ : ℝ → V, IsMinimalGeodesic hN γ 0 1 ∧ γ 0 = p ∧ γ 1 = q ∧
      riemDist (N := N) p q = ENNReal.ofReal (pathLength γ 0 1)) ∧
    (∀ X : Set N, IsClosed X → IsRiemBounded N (Subtype.val '' X) → IsCompact X) :=
  hopf_rinow_of_isRiemComplete hN hconn (isRiemComplete_of_isClosed hN hcl)

variable (hN) in
/-- **Compact submanifolds are complete** (the exposition, Chapter 7 §5: compact Riemannian
manifolds are complete), e.g. the compact Lie groups of Part IV once embedded in a space of
matrices: a compact `N` is closed in `V`. -/
theorem hopf_rinow_of_isCompact (hconn : IsPreconnected N) (hK : IsCompact N) :
    IsGeodesicallyComplete hN ∧
    (∀ (γ : ℝ → V) (s : Set ℝ), IsGeodesicOn hN γ s → IsPreconnected s → s.Nonempty →
      ∃ γ' : ℝ → V, IsGeodesicOn hN γ' univ ∧ EqOn γ' γ s) ∧
    (∀ p q : N, ∃ γ : ℝ → V, IsMinimalGeodesic hN γ 0 1 ∧ γ 0 = p ∧ γ 1 = q ∧
      riemDist (N := N) p q = ENNReal.ofReal (pathLength γ 0 1)) ∧
    (∀ X : Set N, IsClosed X → IsRiemBounded N (Subtype.val '' X) → IsCompact X) :=
  hopf_rinow_of_isClosed hN hconn hK.isClosed

open Milnor.Sphere in
/-- **The round sphere** `Sⁿ ⊆ ℝⁿ⁺¹`, `n ≥ 1` (Milnor, p. 65), with the induced metric, is
geodesically complete, and any two of its points are joined by a minimal geodesic of length their
distance. -/
theorem sphere_hopf_rinow {n : ℕ} (hn : 1 ≤ n) :
    IsGeodesicallyComplete (sphSub n) ∧
    ∀ p q : Sph n, ∃ γ : ℝ → EuclideanSpace ℝ (Fin (n + 1)), IsMinimalGeodesic (sphSub n) γ 0 1 ∧
      γ 0 = p ∧ γ 1 = q ∧ riemDist (N := Sph n) p q = ENNReal.ofReal (pathLength γ 0 1) := by
  have hconn : IsPreconnected (Sph n) := by
    change IsPreconnected ((sphG (n := n)) ⁻¹' {0})
    rw [preimage_eq_sphere]
    refine (isConnected_sphere ?_ 0 zero_le_one).isPreconnected
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (by omega : 1 < n + 1)
  obtain ⟨h1, -, h3, -⟩ := hopf_rinow_of_isCompact (sphSub n) hconn isCompact_sph
  exact ⟨h1, h3⟩

end Morse
