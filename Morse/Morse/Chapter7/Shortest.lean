import Morse.Chapter7.GaussLemma
import Morse.Chapter7.Path

/-!
Milnor, *Morse Theory*, §10, pp. 59–61 (Lemma 10.6 and Theorem 10.4), for a submanifold
`N ⊆ ℝᴷ` with the induced metric.

# Short geodesics are shortest

## Milnor's text, paraphrased

* **Theorem 10.4** (p. 59).  Let `W`, `ε` be as in Lemma 10.3, `γ : [0, 1] → M` the geodesic of
  length `< ε` joining two points of `W`, and `ω : [0, 1] → M` any other piecewise smooth path
  joining the same two points.  Then `∫ ‖dγ/dt‖ ≤ ∫ ‖dω/dt‖`, where equality can hold only if the
  point set `ω([0, 1])` coincides with `γ([0, 1])`.  So `γ` is the shortest path joining its
  endpoints.
* Proof (p. 61): for a path `ω` from `q` to `q' = exp_q(rv)`, `0 < r < ε`, `‖v‖ = 1`, and any
  `δ > 0`, Milnor asserts that `ω` contains a segment from the spherical shell of radius `δ` to the
  shell of radius `r`, lying between the two shells; it has length `≥ r − δ` by Lemma 10.6; let
  `δ → 0`.  If the images of `ω` and `γ` differ, he says, "we easily obtain a strict
  inequality".

## In the embedded setting

Fix a normal radius `ε` at `q` (`Morse.NormalCoord`).  `Morse.NormalCoord.ballSet nc s` is an open
set of `V` cutting out the normal ball `B_s(q) = exp_q(B_s(0))` from `N`;
`Morse.NormalCoord.closedBallSet nc s = exp_q(closedBall(0, s) ∩ T_qN)` is compact.  Paths are
admissible paths `c : [a, b] → N` (`Morse/Chapter7/Path.lean`), which include the piecewise smooth
ones.

* `Morse.NormalCoord.radius_sub_le_pathLength`: **Lemma 10.6**, `L(c) ≥ ρ(b) − ρ(a)` for `c` in the
  punctured normal neighbourhood, `ρ = ‖exp_q⁻¹ ∘ c‖`; with equality the direction
  `exp_q⁻¹(c)/ρ` is constant (`Morse.NormalCoord.direction_eq_of_pathLength_eq`).
* `Morse.NormalCoord.exists_crossing`: **paths leaving the normal ball** (the exposition's Lemma C):
  a path in `N` from `q` to a point outside `B_s(q)` has a segment `[t₁, t₂]` from the last visit
  of `q` before the first exit from `B_s(q)` to that exit, and this segment has length `≥ s`.  The
  path may leave `U_q` afterwards; the first exit point is on the sphere `S_s(q)` because the
  closed normal ball is compact, hence closed in `V`.
* `Morse.NormalCoord.norm_le_pathLength`: **Theorem 10.4, inequality**: a path from `q` to
  `exp_q(v)`, `‖v‖ < ε`, has length `≥ ‖v‖`, the length of the geodesic `t ↦ exp_q(tv)` on `[0, 1]`
  (`Morse.NormalCoord.pathLength_exp_smul`).
* `Morse.NormalCoord.eq_exp_of_pathLength_eq`: **Theorem 10.4, equality, in the sharp form**: if
  the length is `‖v‖`, then `c(t) = exp_q(ρ(t) v)` with `ρ(t) = L(c|[a, t])/‖v‖`, a continuous
  nondecreasing map of `[a, b]` onto `[0, 1]`: `c` is a monotone reparametrization of the geodesic.
  Milnor's weaker conclusion `c([a, b]) = γ([0, 1])` follows
  (`Morse.NormalCoord.image_eq_of_pathLength_eq`).
* `Morse.theorem_10_4`: Milnor's statement, with `W`, `ε` from Lemma 10.3.

## What Milnor leaves implicit

* **The segment between the shells.**  A competing path may leave the normal neighbourhood `U_q`
  and come back.  That it nevertheless contains a segment from the shell of radius `δ` to the
  shell of radius `r` lying between them uses that closed normal balls are closed in `M` (compact
  in a Hausdorff space): the first exit point from the open ball lies on its closure, hence on the
  sphere (`Morse.NormalCoord.exists_crossing`).
* **The equality case** "we easily obtain a strict inequality" is the analysis of the last visit of
  `q` and the first arrival on the sphere: the path is constant before and after, and in between
  each of its subsegments realizes the equality case of Lemma 10.6.  Milnor's conclusion that the
  images coincide is too weak for Corollary 10.7 (a path running along `γ` at variable speed, or
  back and forth, has the same image); the sharp form gives `c = γ ∘ ρ` with `ρ` monotone.
* **Lemma 10.6, equality**, needs the fundamental theorem of calculus for the direction
  `exp_q⁻¹(c)/ρ`, whose derivative vanishes almost everywhere and which is differentiable off a
  countable set.
-/

open Set Filter Topology Function Module Metric MeasureTheory
open scoped ContDiff Manifold RealInnerProductSpace Interval

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

/-! ### Lengths of geodesics -/

/-- **The length of a geodesic** on `[a, b]` is its (constant) speed times `b − a`. -/
theorem IsGeodesicOn.pathLength_eq {γ : ℝ → V} {s : Set ℝ} (h : IsGeodesicOn hN γ s)
    (hs : IsPreconnected s) {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ s) {t₀ : ℝ} (ht₀ : t₀ ∈ s) :
    pathLength γ a b = ‖deriv γ t₀‖ * (b - a) :=
  pathLength_eq_of_norm_deriv
    (IsPiecewiseSmooth.of_contDiffOn h.contDiffOn hab hsub).isAdmissible
    fun _ ht _ => h.norm_deriv_eq hs (hsub (Ioo_subset_Icc_self ht)) ht₀

namespace NormalCoord

variable {q : N} {ε : ℝ} (nc : NormalCoord hN q ε)

theorem mem_U_self : (q : V) ∈ nc.U := by
  have := nc.exp_mem_U 0 (Submodule.zero_mem _) (by simpa using nc.pos)
  rwa [exp_zero q.2] at this

theorem G_self : nc.G q = 0 := by
  have := nc.G_exp 0 (Submodule.zero_mem _) (by simpa using nc.pos)
  rwa [exp_zero q.2] at this

theorem G_ne_zero {y : V} (hyU : y ∈ nc.U) (hyN : y ∈ N) (hne : y ≠ q) : nc.G y ≠ 0 := by
  intro h
  apply hne
  rw [← nc.exp_G y hyU hyN, h, exp_zero q.2]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem continuousOn_G : ContinuousOn nc.G nc.U := nc.contDiffOn_G.continuousOn

/-- The open set of `V` cutting the normal ball `B_s(q) = exp_q(B_s(0))` out of `N`. -/
def ballSet (s : ℝ) : Set V := nc.U ∩ nc.G ⁻¹' ball 0 s

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem isOpen_ballSet (s : ℝ) : IsOpen (nc.ballSet s) :=
  nc.continuousOn_G.isOpen_inter_preimage nc.isOpen_U isOpen_ball

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem mem_ballSet {s : ℝ} {y : V} : y ∈ nc.ballSet s ↔ y ∈ nc.U ∧ ‖nc.G y‖ < s := by
  rw [ballSet, mem_inter_iff, mem_preimage, mem_ball, dist_zero_right]

/-- The closed normal ball `exp_q(closedBall(0, s) ∩ T_qN)`. -/
def closedBallSet (s : ℝ) : Set V := nc.F '' (closedBall 0 s ∩ (tangentSubspace hN q : Set V))

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **Closed normal balls are compact** (for `s < ε`), hence closed in `V`. -/
theorem isCompact_closedBallSet {s : ℝ} (hs : s < ε) : IsCompact (nc.closedBallSet s) := by
  have hK : IsCompact (closedBall (0 : V) s ∩ (tangentSubspace hN q : Set V)) :=
    (isCompact_closedBall 0 s).inter_right (Submodule.closed_of_finiteDimensional _)
  refine hK.image_of_continuousOn (nc.contDiffOn_F.continuousOn.mono fun v hv => ?_)
  exact nc.mem_O v hv.2 (lt_of_le_of_lt (by simpa using hv.1) hs)

theorem mem_closedBallSet {s : ℝ} (hs : s < ε) {y : V} :
    y ∈ nc.closedBallSet s ↔ y ∈ N ∧ y ∈ nc.U ∧ ‖nc.G y‖ ≤ s := by
  constructor
  · rintro ⟨v, ⟨hv, hvT⟩, rfl⟩
    have hvs : ‖v‖ ≤ s := by simpa using hv
    have hvε : ‖v‖ < ε := lt_of_le_of_lt hvs hs
    rw [nc.F_eq v hvT hvε]
    exact ⟨nc.exp_mem hvT hvε, nc.exp_mem_U v hvT hvε, by rw [nc.G_exp v hvT hvε]; exact hvs⟩
  · rintro ⟨hyN, hyU, hys⟩
    refine ⟨nc.G y, ⟨by simpa using hys, nc.G_mem y hyU hyN⟩, ?_⟩
    rw [nc.F_eq _ (nc.G_mem y hyU hyN) (nc.norm_G_lt y hyU hyN), nc.exp_G y hyU hyN]

include nc in
/-- The radial geodesic `t ↦ exp_q(tv)`, `v ∈ B_ε(q)`: a geodesic near `[0, 1]` with velocity `v`
at `0`. -/
theorem radial {v : V} (hv : v ∈ tangentSubspace hN q) (hvε : ‖v‖ < ε) :
    ∃ δ > 0, IsGeodesicOn hN (fun t : ℝ => exp hN q (t • v)) (Ioo (-δ) (1 + δ)) ∧
      deriv (fun t : ℝ => exp hN q (t • v)) 0 = v := by
  obtain ⟨γ, hγ, -⟩ := exp_eq_of_mem_expDom (nc.mem_expDom v hv hvε)
  obtain ⟨δ, hδ, hgeo, heq⟩ := hγ.isGeodesicOn_exp_smul
  obtain ⟨-, -, -, -, h0'⟩ := hγ
  refine ⟨δ, hδ, hgeo, ?_⟩
  have h0δ : (0 : ℝ) ∈ Ioo (-δ) (1 + δ) := ⟨by linarith, by linarith⟩
  have hev : (fun t : ℝ => exp hN q (t • v)) =ᶠ[𝓝 0] γ :=
    eventually_of_mem (isOpen_Ioo.mem_nhds h0δ) heq
  rw [hev.deriv_eq, h0']

include nc in
/-- **The length of the geodesic `t ↦ exp_q(tv)` on `[0, 1]` is `‖v‖`.** -/
theorem pathLength_exp_smul {v : V} (hv : v ∈ tangentSubspace hN q) (hvε : ‖v‖ < ε) :
    pathLength (fun t : ℝ => exp hN q (t • v)) 0 1 = ‖v‖ := by
  obtain ⟨δ, hδ, hgeo, hd⟩ := nc.radial hv hvε
  rw [hgeo.pathLength_eq isPreconnected_Ioo zero_le_one
    (Icc_subset_Ioo (by linarith) (by linarith)) (t₀ := 0) ⟨by linarith, by linarith⟩, hd]
  ring

/-! ### Lemma 10.6 -/

/-- **Lemma 10.6** (Milnor, p. 60): along an admissible path `c` in `U_q ∩ N − {q}`, the length is
at least the increase of the radius `ρ = ‖exp_q⁻¹ ∘ c‖`. -/
theorem radius_sub_le_pathLength {c : ℝ → V} {a b : ℝ} (hc : IsAdmissible c a b)
    (hmem : ∀ t ∈ Icc a b, c t ∈ N ∧ c t ∈ nc.U ∧ c t ≠ q) :
    ‖nc.G (c b)‖ - ‖nc.G (c a)‖ ≤ pathLength c a b := by
  obtain ⟨C, hC, hd⟩ := hc.countable
  set ρ : ℝ → ℝ := fun t => ‖nc.G (c t)‖ with hρ_def
  have hρc : ContinuousOn ρ (Icc a b) :=
    (nc.continuousOn_G.comp hc.continuousOn fun t ht => (hmem t ht).2.1).norm
  have hρd : ∀ t ∈ Ioo a b \ C, HasDerivAt ρ (deriv ρ t) t ∧ |deriv ρ t| ≤ ‖deriv c t‖ := by
    intro t ht
    have htI : t ∈ Icc a b := Ioo_subset_Icc_self ht.1
    have hNn : ∀ᶠ s in 𝓝 t, c s ∈ N :=
      eventually_of_mem (Ioo_mem_nhds ht.1.1 ht.1.2) fun s hs => (hmem s (Ioo_subset_Icc_self hs)).1
    obtain ⟨r', hr', hle, -⟩ :=
      nc.hasDerivAt_radius (hd t ht).hasDerivAt hNn (hmem t htI).2.1 (hmem t htI).2.2
    rw [hr'.deriv]
    exact ⟨hr', hle⟩
  have hint : IntervalIntegrable (deriv ρ) volume a b := by
    refine hc.integrable.mono_fun' (aestronglyMeasurable_deriv ρ _) ?_
    exact ae_uIoc_of_forall_Ioo_diff hc.le hC fun t ht => by
      simpa only [Real.norm_eq_abs] using (hρd t ht).2
  have hftc : ∫ t in a..b, deriv ρ t = ρ b - ρ a :=
    integral_eq_of_hasDerivAt_off_countable_of_le ρ (deriv ρ) hc.le hC hρc
      (fun t ht => (hρd t ht).1) hint
  rw [← hftc]
  exact intervalIntegral.integral_mono_ae_restrict hc.le hint hc.integrable
    (ae_Icc_of_forall_Ioo_diff hC fun t ht => (le_abs_self _).trans (hρd t ht).2)

/-- **Lemma 10.6, equality** (Milnor, p. 60): if the length equals the increase of the radius, the
direction `exp_q⁻¹(c)/ρ` is constant. -/
theorem direction_eq_of_pathLength_eq {c : ℝ → V} {a b : ℝ} (hc : IsAdmissible c a b)
    (hmem : ∀ t ∈ Icc a b, c t ∈ N ∧ c t ∈ nc.U ∧ c t ≠ q)
    (heq : pathLength c a b = ‖nc.G (c b)‖ - ‖nc.G (c a)‖) :
    ∀ t ∈ Icc a b, ‖nc.G (c t)‖⁻¹ • nc.G (c t) = ‖nc.G (c b)‖⁻¹ • nc.G (c b) := by
  obtain ⟨C, hC, hd⟩ := hc.countable
  set ρ : ℝ → ℝ := fun t => ‖nc.G (c t)‖ with hρ_def
  set u : ℝ → V := fun t => ‖nc.G (c t)‖⁻¹ • nc.G (c t) with hu_def
  have hGc : ContinuousOn (fun t => nc.G (c t)) (Icc a b) :=
    nc.continuousOn_G.comp hc.continuousOn fun t ht => (hmem t ht).2.1
  have hne : ∀ t ∈ Icc a b, nc.G (c t) ≠ 0 := fun t ht =>
    nc.G_ne_zero (hmem t ht).2.1 (hmem t ht).1 (hmem t ht).2.2
  have hρc : ContinuousOn ρ (Icc a b) := hGc.norm
  have huc : ContinuousOn u (Icc a b) :=
    (hρc.inv₀ fun t ht => norm_ne_zero_iff.2 (hne t ht)).smul hGc
  -- pointwise facts off `C`
  have hpt : ∀ t ∈ Ioo a b \ C, HasDerivAt ρ (deriv ρ t) t ∧ |deriv ρ t| ≤ ‖deriv c t‖ ∧
      HasDerivAt u (deriv u t) t ∧ (deriv ρ t = ‖deriv c t‖ → deriv u t = 0) := by
    intro t ht
    have htI : t ∈ Icc a b := Ioo_subset_Icc_self ht.1
    have hNn : ∀ᶠ s in 𝓝 t, c s ∈ N :=
      eventually_of_mem (Ioo_mem_nhds ht.1.1 ht.1.2) fun s hs => (hmem s (Ioo_subset_Icc_self hs)).1
    obtain ⟨r', hr', hle, hdir⟩ :=
      nc.hasDerivAt_radius (hd t ht).hasDerivAt hNn (hmem t htI).2.1 (hmem t htI).2.2
    have hGd : HasFDerivAt nc.G (fderiv ℝ nc.G (c t)) (c t) :=
      ((nc.contDiffOn_G.contDiffAt (nc.isOpen_U.mem_nhds (hmem t htI).2.1)).differentiableAt
        (by simp)).hasFDerivAt
    have hW := hGd.comp_hasDerivAt t (hd t ht).hasDerivAt
    have hu : HasDerivAt u _ t := (hr'.inv (norm_ne_zero_iff.2 (hne t htI))).smul hW
    rw [hr'.deriv]
    refine ⟨hr', hle, hu.differentiableAt.hasDerivAt, fun h => (hdir h).deriv⟩
  -- `‖c'‖ = ρ'` almost everywhere
  have hint : IntervalIntegrable (deriv ρ) volume a b := by
    refine hc.integrable.mono_fun' (aestronglyMeasurable_deriv ρ _) ?_
    exact ae_uIoc_of_forall_Ioo_diff hc.le hC fun t ht => by
      simpa only [Real.norm_eq_abs] using (hpt t ht).2.1
  have hftc : ∫ t in a..b, deriv ρ t = ρ b - ρ a :=
    integral_eq_of_hasDerivAt_off_countable_of_le ρ (deriv ρ) hc.le hC hρc
      (fun t ht => (hpt t ht).1) hint
  have hzero : ∫ t in a..b, (‖deriv c t‖ - deriv ρ t) = 0 := by
    rw [intervalIntegral.integral_sub hc.integrable hint, hftc]
    change pathLength c a b - (ρ b - ρ a) = 0
    rw [heq]
    ring
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc a b)] fun t => ‖deriv c t‖ - deriv ρ t := by
    have := ae_uIoc_of_forall_Ioo_diff hc.le hC fun t ht =>
      sub_nonneg.2 ((le_abs_self _).trans (hpt t ht).2.1)
    rwa [uIoc_of_le hc.le] at this
  have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hc.le hnonneg
    (hc.integrable.sub hint)).1 hzero
  -- `u' = 0` almost everywhere
  have hu0 : ∀ᵐ t ∂(volume.restrict (Ι a b)), deriv u t = 0 := by
    have h1 := ae_uIoc_of_forall_Ioo_diff hc.le hC fun t ht =>
      fun h : ‖deriv c t‖ - deriv ρ t = 0 => (hpt t ht).2.2.2 (sub_eq_zero.1 h).symm
    rw [uIoc_of_le hc.le] at h1 ⊢
    filter_upwards [h1, hae] with t h1 h2
    exact h1 h2
  intro t ht
  have hsub : Ι t b ⊆ Ι a b := by
    rw [uIoc_of_le ht.2, uIoc_of_le hc.le]
    exact Ioc_subset_Ioc ht.1 le_rfl
  have hu0' : ∀ᵐ x ∂(volume.restrict (Ι t b)), deriv u x = 0 :=
    ae_restrict_of_ae_restrict_of_subset hsub hu0
  have hintu : IntervalIntegrable (deriv u) volume t b := by
    have h0 : IntervalIntegrable (fun _ => (0 : V)) volume t b := intervalIntegrable_const
    exact h0.congr_ae (hu0'.mono fun x hx => hx.symm)
  have hftcu := integral_eq_of_hasDerivAt_off_countable_of_le u (deriv u) ht.2 hC
    (huc.mono (Icc_subset_Icc ht.1 le_rfl))
    (fun s hs => (hpt s ⟨⟨by linarith [hs.1.1, ht.1], hs.1.2⟩, hs.2⟩).2.2.1) hintu
  have hint0 : ∫ s in t..b, deriv u s = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : V)) ?_]
    · simp
    have := hu0'
    rw [ae_restrict_iff' measurableSet_uIoc] at this
    exact this
  rw [hint0] at hftcu
  exact (sub_eq_zero.1 hftcu.symm).symm

/-! ### Paths leaving the normal ball -/

/-- **Paths leaving the normal ball** (the exposition's Lemma C).  Let `c` be an admissible path in
`N` from `q` to a point outside the normal ball `B_s(q)`, `0 < s < ε`.  Let `t₂` be the first time
`c` leaves `B_s(q)` and `t₁` the last time before `t₂` at which `c` is at `q`.  Then on `(t₁, t₂]`
the path lies in `U_q − {q}`, it is in `B_s(q)` before `t₂`, `c(t₂)` is on the sphere of radius
`s`, and `L(c|[t₁, t₂]) ≥ s`.  (After `t₂` the path may leave `U_q`.) -/
theorem exists_crossing {c : ℝ → V} {a b : ℝ} (hc : IsAdmissible c a b)
    (hcN : ∀ t ∈ Icc a b, c t ∈ N) (ha : c a = q) {s : ℝ} (hs : 0 < s) (hsε : s < ε)
    (hb : c b ∉ nc.ballSet s) :
    ∃ t₁ t₂, a ≤ t₁ ∧ t₁ < t₂ ∧ t₂ ≤ b ∧ c t₁ = q ∧
      (∀ t ∈ Ioc t₁ t₂, c t ∈ nc.U ∧ c t ≠ q) ∧ ‖nc.G (c t₂)‖ = s ∧
      (∀ t ∈ Ico t₁ t₂, ‖nc.G (c t)‖ < s) ∧ s ≤ pathLength c t₁ t₂ := by
  have hqball : (q : V) ∈ nc.ballSet s := (nc.mem_ballSet).2 ⟨nc.mem_U_self, by
    rw [nc.G_self, norm_zero]; exact hs⟩
  -- the first exit time `t₂`
  set S₂ := Icc a b ∩ c ⁻¹' (nc.ballSet s)ᶜ with hS₂_def
  have hS₂c : IsClosed S₂ :=
    hc.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc (nc.isOpen_ballSet s).isClosed_compl
  have hbS₂ : b ∈ S₂ := ⟨⟨hc.le, le_rfl⟩, hb⟩
  have hS₂bdd : BddBelow S₂ := ⟨a, fun t ht => ht.1.1⟩
  set t₂ := sInf S₂ with ht₂_def
  have ht₂S : t₂ ∈ S₂ := hS₂c.csInf_mem ⟨b, hbS₂⟩ hS₂bdd
  have haS₂ : a ∉ S₂ := fun h => h.2 (by rw [ha]; exact hqball)
  have hat₂ : a < t₂ := lt_of_le_of_ne ht₂S.1.1 fun h => haS₂ (h ▸ ht₂S)
  have hbefore : ∀ t ∈ Ico a t₂, c t ∈ nc.ballSet s := by
    intro t ht
    by_contra hcon
    have : t ∈ S₂ := ⟨⟨ht.1, ht.2.le.trans ht₂S.1.2⟩, hcon⟩
    exact absurd (csInf_le hS₂bdd this) (not_le.2 ht.2)
  -- `c(t₂)` is on the sphere of radius `s`
  have ht₂cl : c t₂ ∈ nc.closedBallSet s := by
    have hcl : IsClosed (nc.closedBallSet s) := (nc.isCompact_closedBallSet hsε).isClosed
    have hcont : ContinuousWithinAt c (Ico a t₂) t₂ :=
      (hc.continuousOn t₂ ht₂S.1).mono (Ico_subset_Icc_self.trans
        (Icc_subset_Icc le_rfl ht₂S.1.2))
    have : (𝓝[Ico a t₂] t₂).NeBot := right_nhdsWithin_Ico_neBot hat₂
    refine hcl.mem_of_tendsto hcont (eventually_nhdsWithin_of_forall fun t ht => ?_)
    have h1 := hbefore t ht
    rw [nc.mem_ballSet] at h1
    exact (nc.mem_closedBallSet hsε).2 ⟨hcN t ⟨ht.1, ht.2.le.trans ht₂S.1.2⟩, h1.1, h1.2.le⟩
  obtain ⟨-, ht₂U, ht₂le⟩ := (nc.mem_closedBallSet hsε).1 ht₂cl
  have ht₂s : ‖nc.G (c t₂)‖ = s := by
    refine le_antisymm ht₂le (not_lt.1 fun hlt => ht₂S.2 ?_)
    exact (nc.mem_ballSet).2 ⟨ht₂U, hlt⟩
  have ht₂q : c t₂ ≠ q := by
    intro h
    rw [h, nc.G_self, norm_zero] at ht₂s
    exact hs.ne' ht₂s.symm
  -- the last visit `t₁` of `q` before `t₂`
  set S₁ := Icc a t₂ ∩ c ⁻¹' {(q : V)} with hS₁_def
  have hS₁c : IsClosed S₁ :=
    (hc.continuousOn.mono (Icc_subset_Icc le_rfl ht₂S.1.2)).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_singleton
  have haS₁ : a ∈ S₁ := ⟨⟨le_rfl, hat₂.le⟩, ha⟩
  have hS₁bdd : BddAbove S₁ := ⟨t₂, fun t ht => ht.1.2⟩
  set t₁ := sSup S₁ with ht₁_def
  have ht₁S : t₁ ∈ S₁ := hS₁c.csSup_mem ⟨a, haS₁⟩ hS₁bdd
  have ht₁t₂ : t₁ < t₂ := lt_of_le_of_ne ht₁S.1.2 fun h => ht₂q (h ▸ ht₁S.2)
  have hafter : ∀ t ∈ Ioc t₁ t₂, c t ∈ nc.U ∧ c t ≠ q := by
    intro t ht
    refine ⟨?_, fun h => ?_⟩
    · rcases eq_or_lt_of_le ht.2 with h | h
      · rw [h]; exact ht₂U
      · exact ((nc.mem_ballSet).1 (hbefore t ⟨ht₁S.1.1.trans ht.1.le, h⟩)).1
    · have : t ∈ S₁ := ⟨⟨ht₁S.1.1.trans ht.1.le, ht.2⟩, h⟩
      exact absurd (le_csSup hS₁bdd this) (not_le.2 ht.1)
  refine ⟨t₁, t₂, ht₁S.1.1, ht₁t₂, ht₂S.1.2, ht₁S.2, hafter, ht₂s, fun t ht => ?_, ?_⟩
  · exact ((nc.mem_ballSet).1 (hbefore t ⟨ht₁S.1.1.trans ht.1, ht.2⟩)).2
  · -- the length of `[t₁, t₂]`: let the inner end tend to `t₁`
    have hct : IsAdmissible c t₁ t₂ := hc.mono ht₁S.1.1 ht₁t₂.le ht₂S.1.2
    refine le_of_forall_pos_lt_add fun η hη => ?_
    have hρc : ContinuousWithinAt (fun t => ‖nc.G (c t)‖) (Icc t₁ t₂) t₁ := by
      have h1 : ContinuousWithinAt c (Icc t₁ t₂) t₁ :=
        hct.continuousOn t₁ ⟨le_rfl, ht₁t₂.le⟩
      have h2 : ContinuousAt nc.G (c t₁) := by
        rw [ht₁S.2]
        exact nc.continuousOn_G.continuousAt (nc.isOpen_U.mem_nhds nc.mem_U_self)
      exact (h2.comp_continuousWithinAt h1).norm
    have h0 : ‖nc.G (c t₁)‖ = 0 := by rw [ht₁S.2, nc.G_self, norm_zero]
    have hev : ∀ᶠ t in 𝓝[Icc t₁ t₂] t₁, ‖nc.G (c t)‖ < η :=
      hρc.eventually (gt_mem_nhds (by simp only [h0]; exact hη))
    have : (𝓝[Ioo t₁ t₂] t₁).NeBot := left_nhdsWithin_Ioo_neBot ht₁t₂
    have hev' : ∀ᶠ t in 𝓝[Ioo t₁ t₂] t₁, ‖nc.G (c t)‖ < η :=
      nhdsWithin_mono t₁ Ioo_subset_Icc_self hev
    obtain ⟨t', ht'η, ht'I⟩ := (hev'.and self_mem_nhdsWithin).exists
    have h1 := nc.radius_sub_le_pathLength (hc.mono (ht₁S.1.1.trans ht'I.1.le) ht'I.2.le ht₂S.1.2)
      fun t ht => ⟨hcN t ⟨ht₁S.1.1.trans (ht'I.1.le.trans ht.1), ht.2.trans ht₂S.1.2⟩,
        hafter t ⟨ht'I.1.trans_le ht.1, ht.2⟩⟩
    have h2 := hct.pathLength_le ht'I.1.le ht'I.2.le le_rfl
    rw [ht₂s] at h1
    linarith

/-! ### Theorem 10.4 -/

include nc in
/-- **Theorem 10.4, inequality** (Milnor, p. 59): an admissible path in `N` from `q` to `exp_q(v)`,
`‖v‖ < ε`, has length at least `‖v‖`, the length of the geodesic `t ↦ exp_q(tv)`, `0 ≤ t ≤ 1`
(`Morse.NormalCoord.pathLength_exp_smul`).  The path may leave the normal neighbourhood. -/
theorem norm_le_pathLength {c : ℝ → V} {a b : ℝ} (hc : IsAdmissible c a b)
    (hcN : ∀ t ∈ Icc a b, c t ∈ N) (ha : c a = q) {v : V} (hv : v ∈ tangentSubspace hN q)
    (hvε : ‖v‖ < ε) (hb : c b = exp hN q v) : ‖v‖ ≤ pathLength c a b := by
  rcases eq_or_ne v 0 with rfl | hv0
  · rw [norm_zero]; exact hc.pathLength_nonneg
  have hs : 0 < ‖v‖ := norm_pos_iff.2 hv0
  have hbs : c b ∉ nc.ballSet ‖v‖ := by
    rw [nc.mem_ballSet, hb, nc.G_exp v hv hvε]
    exact fun h => lt_irrefl _ h.2
  obtain ⟨t₁, t₂, ht₁, ht₁₂, ht₂, -, -, -, -, hL⟩ := nc.exists_crossing hc hcN ha hs hvε hbs
  exact hL.trans (hc.pathLength_le ht₁ ht₁₂.le ht₂)

include nc in
/-- **Theorem 10.4, equality, sharp form**: if an admissible path `c` in `N` from `q` to
`exp_q(v)`, `0 < ‖v‖ < ε`, has length exactly `‖v‖`, then `c(t) = exp_q(ρ(t) v)` for
`ρ(t) = L(c|[a, t])/‖v‖`, a continuous nondecreasing function from `ρ(a) = 0` to `ρ(b) = 1`
(`Morse.IsAdmissible.continuousOn_pathLength`, `Morse.IsAdmissible.monotoneOn_pathLength`): `c`
is a monotone reparametrization of the geodesic `t ↦ exp_q(tv)`. -/
theorem eq_exp_of_pathLength_eq {c : ℝ → V} {a b : ℝ} (hc : IsAdmissible c a b)
    (hcN : ∀ t ∈ Icc a b, c t ∈ N) (ha : c a = q) {v : V} (hv : v ∈ tangentSubspace hN q)
    (hvε : ‖v‖ < ε) (hb : c b = exp hN q v) (hv0 : v ≠ 0) (heq : pathLength c a b = ‖v‖) :
    ∀ t ∈ Icc a b, c t = exp hN q ((pathLength c a t / ‖v‖) • v) := by
  set s := ‖v‖ with hs_def
  have hs : 0 < s := norm_pos_iff.2 hv0
  have hbs : c b ∉ nc.ballSet s := by
    rw [nc.mem_ballSet, hb, nc.G_exp v hv hvε]
    exact fun h => lt_irrefl _ h.2
  obtain ⟨t₁, t₂, ht₁, ht₁₂, ht₂, hct₁, hafter, ht₂s, hbefore, hL⟩ :=
    nc.exists_crossing hc hcN ha hs hvε hbs
  -- splitting the length
  have hsplit₁ := hc.pathLength_add (m := t₁) ⟨ht₁, ht₁₂.le.trans ht₂⟩
  have hsplit₂ := (hc.mono ht₁ (ht₁₂.le.trans ht₂) le_rfl).pathLength_add (m := t₂) ⟨ht₁₂.le, ht₂⟩
  have hn₁ := (hc.mono le_rfl ht₁ (ht₁₂.le.trans ht₂)).pathLength_nonneg
  have hn₃ := (hc.mono (ht₁.trans ht₁₂.le) ht₂ le_rfl).pathLength_nonneg
  have hL₁ : pathLength c a t₁ = 0 := by linarith
  have hL₃ : pathLength c t₂ b = 0 := by linarith
  have hL₂ : pathLength c t₁ t₂ = s := by linarith
  -- `c` is constant on `[a, t₁]` and on `[t₂, b]`
  have hconst₁ := (hc.mono le_rfl ht₁ (ht₁₂.le.trans ht₂)).eq_of_pathLength_eq_zero hL₁
  have hconst₃ := (hc.mono (ht₁.trans ht₁₂.le) ht₂ le_rfl).eq_of_pathLength_eq_zero hL₃
  have hct₂ : c t₂ = exp hN q v := by rw [← hb, hconst₃ b ⟨ht₂, le_rfl⟩]
  have hGt₂ : nc.G (c t₂) = v := by rw [hct₂, nc.G_exp v hv hvε]
  -- on `(t₁, t₂]`
  have hmid : ∀ t ∈ Ioc t₁ t₂, pathLength c t₁ t = ‖nc.G (c t)‖ ∧
      c t = exp hN q ((‖nc.G (c t)‖ / s) • v) := by
    intro t ht
    have htN : c t ∈ N := hcN t ⟨ht₁.trans ht.1.le, ht.2.trans ht₂⟩
    obtain ⟨htU, htq⟩ := hafter t ht
    have hGT := nc.G_mem _ htU htN
    have hGε := nc.norm_G_lt _ htU htN
    have hlow₁ : ‖nc.G (c t)‖ ≤ pathLength c t₁ t :=
      nc.norm_le_pathLength (hc.mono ht₁ ht.1.le (ht.2.trans ht₂))
        (fun x hx => hcN x ⟨ht₁.trans hx.1, hx.2.trans (ht.2.trans ht₂)⟩) hct₁ hGT hGε
        (nc.exp_G _ htU htN).symm
    have hct' : IsAdmissible c t t₂ := hc.mono (ht₁.trans ht.1.le) ht.2 ht₂
    have hmem' : ∀ x ∈ Icc t t₂, c x ∈ N ∧ c x ∈ nc.U ∧ c x ≠ q := fun x hx =>
      ⟨hcN x ⟨ht₁.trans (ht.1.le.trans hx.1), hx.2.trans ht₂⟩,
        hafter x ⟨ht.1.trans_le hx.1, hx.2⟩⟩
    have hlow₂ := nc.radius_sub_le_pathLength hct' hmem'
    rw [ht₂s] at hlow₂
    have hsplit := (hc.mono ht₁ ht₁₂.le ht₂).pathLength_add (m := t) ⟨ht.1.le, ht.2⟩
    have heq₁ : pathLength c t₁ t = ‖nc.G (c t)‖ := by linarith
    have heq₂ : pathLength c t t₂ = ‖nc.G (c t₂)‖ - ‖nc.G (c t)‖ := by rw [ht₂s]; linarith
    refine ⟨heq₁, ?_⟩
    have hdir := nc.direction_eq_of_pathLength_eq hct' hmem' heq₂ t ⟨le_rfl, ht.2⟩
    rw [hGt₂, ← hs_def] at hdir
    have hGt0 : ‖nc.G (c t)‖ ≠ 0 := norm_ne_zero_iff.2 (nc.G_ne_zero htU htN htq)
    have hG : nc.G (c t) = (‖nc.G (c t)‖ / s) • v :=
      calc nc.G (c t) = ‖nc.G (c t)‖ • (‖nc.G (c t)‖⁻¹ • nc.G (c t)) := by
            rw [smul_smul, mul_inv_cancel₀ hGt0, one_smul]
        _ = ‖nc.G (c t)‖ • (s⁻¹ • v) := by rw [hdir]
        _ = (‖nc.G (c t)‖ / s) • v := by rw [smul_smul, div_eq_mul_inv]
    rw [← hG, nc.exp_G _ htU htN]
  intro t ht
  rcases le_or_gt t t₁ with htt₁ | htt₁
  · -- before `t₁`: `c(t) = q`, `ρ(t) = 0`
    have hLt : pathLength c a t = 0 := le_antisymm
      (hL₁ ▸ (hc.mono le_rfl ht₁ (ht₁₂.le.trans ht₂)).pathLength_le le_rfl ht.1 htt₁)
      (hc.mono le_rfl ht.1 ht.2).pathLength_nonneg
    rw [hconst₁ t ⟨ht.1, htt₁⟩, hLt, zero_div, zero_smul, exp_zero q.2, ha]
  rcases le_or_gt t t₂ with htt₂ | htt₂
  · -- between `t₁` and `t₂`
    obtain ⟨h1, h2⟩ := hmid t ⟨htt₁, htt₂⟩
    have hsplit := (hc.mono le_rfl ht.1 ht.2).pathLength_add (m := t₁) ⟨ht₁, htt₁.le⟩
    rw [h2]
    congr 2
    rw [← hsplit, hL₁, zero_add, h1]
  · -- after `t₂`: `c(t) = exp_q(v)`, `ρ(t) = 1`
    have hsplit := (hc.mono le_rfl ht.1 ht.2).pathLength_add (m := t₂) ⟨ht₁.trans ht₁₂.le, htt₂.le⟩
    have hLt₂t : pathLength c t₂ t = 0 := le_antisymm
      (hL₃ ▸ (hc.mono (ht₁.trans ht₁₂.le) ht₂ le_rfl).pathLength_le le_rfl htt₂.le ht.2)
      (hc.mono (ht₁.trans ht₁₂.le) htt₂.le ht.2).pathLength_nonneg
    have hLat₂ : pathLength c a t₂ = s := by
      have := (hc.mono le_rfl (ht₁.trans ht₁₂.le) ht₂).pathLength_add (m := t₁) ⟨ht₁, ht₁₂.le⟩
      rw [← this, hL₁, zero_add, hL₂]
    rw [← hsplit, hLat₂, hLt₂t, add_zero, div_self hs.ne', one_smul,
      hconst₃ t ⟨htt₂.le, ht.2⟩, hct₂]

include nc in
/-- **Theorem 10.4, Milnor's equality clause**: with equality, the point set `c([a, b])` coincides
with `γ([0, 1])`, `γ(t) = exp_q(tv)`. -/
theorem image_eq_of_pathLength_eq {c : ℝ → V} {a b : ℝ} (hc : IsAdmissible c a b)
    (hcN : ∀ t ∈ Icc a b, c t ∈ N) (ha : c a = q) {v : V} (hv : v ∈ tangentSubspace hN q)
    (hvε : ‖v‖ < ε) (hb : c b = exp hN q v) (hv0 : v ≠ 0) (heq : pathLength c a b = ‖v‖) :
    c '' Icc a b = (fun t : ℝ => exp hN q (t • v)) '' Icc 0 1 := by
  have hs : 0 < ‖v‖ := norm_pos_iff.2 hv0
  have hrep := nc.eq_exp_of_pathLength_eq hc hcN ha hv hvε hb hv0 heq
  set ρ : ℝ → ℝ := fun t => pathLength c a t / ‖v‖ with hρ_def
  have hρc : ContinuousOn ρ (Icc a b) := hc.continuousOn_pathLength.div_const _
  have hρa : ρ a = 0 := by simp [hρ_def, pathLength]
  have hρb : ρ b = 1 := by simp [hρ_def, heq, div_self hs.ne']
  have hρmaps : ρ '' Icc a b = Icc 0 1 := by
    apply Subset.antisymm
    · rintro _ ⟨t, ht, rfl⟩
      have h1 := hc.monotoneOn_pathLength ⟨le_rfl, hc.le⟩ ht ht.1
      have h2 := hc.monotoneOn_pathLength ht ⟨hc.le, le_rfl⟩ ht.2
      simp only [pathLength, intervalIntegral.integral_same] at h1
      constructor
      · exact div_nonneg h1 hs.le
      · rw [div_le_one hs, ← heq]; exact h2
    · have := intermediate_value_Icc hc.le hρc
      rwa [hρa, hρb] at this
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨ρ t, hρmaps ▸ mem_image_of_mem ρ ht, (hrep t ht).symm⟩
  · rintro ⟨τ, hτ, rfl⟩
    rw [← hρmaps] at hτ
    obtain ⟨t, ht, rfl⟩ := hτ
    exact ⟨t, ht, hrep t ht⟩

end NormalCoord

/-- **Milnor's Theorem 10.4** (p. 59).  For `W = N ∩ O` and `ε` as in Lemma 10.3 (at any point
`p`), let `q₁, q₂ ∈ W` and let `γ(t) = exp_{q₁}(tv)`, `0 ≤ t ≤ 1`, be the geodesic of length
`‖v‖ < ε` joining them.  Then every piecewise smooth path `c` in `N` joining `q₁` to `q₂` has
length `≥ L(γ) = ‖v‖`, and equality holds only if `c([a, b]) = γ([0, 1])`; in fact then `c` is a
monotone reparametrization of `γ` (`Morse.NormalCoord.eq_exp_of_pathLength_eq`). -/
theorem theorem_10_4 (p : N) :
    ∃ O : Set V, IsOpen O ∧ (p : V) ∈ O ∧ ∃ ε > 0, ∀ q₁ q₂ : N, (q₁ : V) ∈ O → (q₂ : V) ∈ O →
      ∃ v ∈ tangentSubspace hN q₁, ‖v‖ < ε ∧ exp hN q₁ v = q₂ ∧
        pathLength (fun t : ℝ => exp hN q₁ (t • v)) 0 1 = ‖v‖ ∧
        ∀ (c : ℝ → V) (a b : ℝ), IsPiecewiseSmooth c a b → (∀ t ∈ Icc a b, c t ∈ N) →
          c a = q₁ → c b = q₂ → ‖v‖ ≤ pathLength c a b ∧
            (pathLength c a b = ‖v‖ →
              c '' Icc a b = (fun t : ℝ => exp hN q₁ (t • v)) '' Icc 0 1) := by
  obtain ⟨O, hO, hpO, ε, hε, h1, -, h3⟩ := lemma_10_3 hN p
  refine ⟨O, hO, hpO, ε, hε, fun q₁ q₂ hq₁ hq₂ => ?_⟩
  obtain ⟨v, ⟨hv, hvε, hexp⟩, -⟩ := h1 q₁ q₂ hq₁ hq₂
  obtain ⟨nc⟩ := h3 q₁ hq₁
  refine ⟨v, hv, hvε, hexp, nc.pathLength_exp_smul hv hvε, fun c a b hc hcN ha hb => ?_⟩
  have hb' : c b = exp hN q₁ v := by rw [hb, hexp]
  refine ⟨nc.norm_le_pathLength hc.isAdmissible hcN ha hv hvε hb', fun heq => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv0
  · -- `q₁ = q₂` and `c` has length `0`, so it is constant
    rw [norm_zero] at heq
    have hconst := hc.isAdmissible.eq_of_pathLength_eq_zero heq
    have hab := hc.1
    ext y
    simp only [mem_image, smul_zero]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, by rw [hconst t ht, ha, exp_zero q₁.2]⟩
    · rintro ⟨τ, -, rfl⟩
      exact ⟨a, ⟨le_rfl, hab⟩, by rw [ha, exp_zero q₁.2]⟩
  · exact nc.image_eq_of_pathLength_eq hc.isAdmissible hcN ha hv hvε hb' hv0 heq

end Morse
