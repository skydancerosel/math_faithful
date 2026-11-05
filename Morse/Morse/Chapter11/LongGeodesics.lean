import Morse.Chapter11.Myers

/-!
Milnor, *Morse Theory*, §19, p. 106: the index estimate in the proof of Theorem 19.6 (a geodesic
of length `> kπr` has index `≥ k` when `K(U, U) ≥ (n − 1)/r²`), for a submanifold `N ⊆ ℝᴷ` with
the induced metric.

# Long geodesics have large index

## Milnor's text, paraphrased

**Theorem 19.6** (p. 106): if `M` is compact and its Ricci tensor is everywhere positive definite,
`Ω(M; p, q)` has the homotopy type of a CW complex with finitely many cells in each dimension.
Proof: the continuous function `K(U, U)` on the compact space of unit vectors has a minimum
`(n − 1)/r² > 0`.  Every geodesic of length `> πr` has index `≥ 1` (Theorem 19.4); more generally,
one of length `> kπr` has index `≥ k`: for each `i = 1, …, k` there is a field `X_i` along `γ`,
vanishing outside `((i − 1)/k, i/k)`, with `E_**(X_i, X_i) < 0`; clearly `E_**(X_i, X_j) = 0` for
`i ≠ j`, so the `X_i` span a `k`-dimensional space on which `E_**` is negative definite.  If `p`
and `q` are not conjugate along any geodesic, by 16.3 there are only finitely many geodesics of
length `≤ kπr`, hence finitely many of index `< k`; with 17.3 this proves the theorem.

## In the embedded setting

* `Morse.sinBump a b P`: the field `sin(π(t − a)/(b − a)) P(t)` on `[a, b]`, `0` elsewhere;
  `Morse.sinBump_mem_pathTangent`: it lies in `TΩ_γ` (piecewise smooth with breaks at `a`, `b`).
* `Morse.energyHessian_sinBump`: `½ E_**(X, X) = ∫_a^b (κ² cos²(κ(t − a)) − sin²(κ(t − a))
  ⟨R(V, P)V, P⟩) dt`, `κ = π/(b − a)`; `Morse.energyHessian_sinBump_disjoint`: **fields on pieces
  with disjoint interiors are `E_**`-orthogonal** (Milnor's "clearly").
* `Morse.exists_sinBump_neg`: on a piece of length `b − a` with `L(b − a) > πr`, one of the
  frame fields perpendicular to `γ` (`Morse.exists_parallel_frame`) gives `E_**(X, X) < 0`.
* `Morse.theorem_19_6_index`: **a geodesic of length `> kπr` has index `≥ k`**;
  `Morse.pathLength_le_of_formIndex_lt` (index `< k` ⇒ length `≤ kπr`, the form used in 19.6);
  `Morse.le_finsum_conjMultiplicity_of_ricci`: with the index theorem, such a geodesic has at
  least `k` conjugate points in `(0, 1)`, counted with multiplicity.

## Not done here

The rest of Theorem 19.6 depends on Theorem 16.3 (finitely many geodesics below a given length
between non-conjugate points), Theorem 17.3 (the CW homotopy type of `Ω`) and, for arbitrary
`p, q`, on 17.1, 18.2 and Lemma 17.D of the exposition; it is proved in
`Morse/Chapter11/PositiveRicci.lean` (`Morse.theorem_19_6`, with the existence of the minimum
`(n − 1)/r²` on the compact unit tangent bundle, `Morse.exists_ricciLowerBound`),
`Morse/Chapter11/RicciHomology.lean` and `Morse/Chapter11/PositiveRicciAll.lean`
(`Morse.theorem_19_6_all`, all end points).  Here the estimate is stated under the hypothesis
`Morse.RicciLowerBound hN r`.

## What Milnor leaves implicit

* **"Clearly `E_**(X_i, X_j) = 0` for `i ≠ j`"**: in the integral form of `E_**` the integrand
  vanishes except at the common end point of the two pieces (a null set), since each field vanishes
  on an open set around every point off its piece; there are no jump terms to worry about in the
  integral form.
* **A similar argument**: on a piece of length `1/k` the test fields are `sin(πk(t − (i − 1)/k))`
  times parallel unit fields perpendicular to `γ`; the computation of 19.4 gives
  `Σ_j ½ E_**(X_{ij}, X_{ij}) ≤ (n − 1)(π²k² − L²/r²)/(2k) < 0`, so for each `i` one `j = j(i)`
  works; `n ≥ 2` is needed as in 19.4.
* **"Span a `k`-dimensional space"**: the `X_i` are non-zero with disjoint supports, so a
  combination `Σ c_i X_i` has `E_** = Σ c_i² E_**(X_i, X_i) < 0` unless all `c_i = 0`; this gives
  both negative definiteness and linear independence.
-/

open Set Filter Topology Function Module Metric Real MeasureTheory
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

/-! ### Integrals over the pieces -/

/-- An integral over `[0, 1]` of a function that vanishes on `(0, a)` and on `(b, 1)` and agrees
with a continuous `F` on `(a, b)` is `∫_a^b F`. -/
theorem integral_eq_of_eqOn_pieces {G F : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 1) (hF : Continuous F) (h1 : EqOn G 0 (Ioo 0 a)) (h2 : EqOn G F (Ioo a b))
    (h3 : EqOn G 0 (Ioo b 1)) : ∫ t in (0 : ℝ)..1, G t = ∫ t in a..b, F t := by
  have i1 : IntervalIntegrable G volume 0 a :=
    (intervalIntegrable_const (c := (0 : ℝ))).congr_uIoo
      (by rw [uIoo_of_le ha]; exact fun t ht => (h1 ht).symm)
  have i2 : IntervalIntegrable G volume a b :=
    (hF.intervalIntegrable a b).congr_uIoo
      (by rw [uIoo_of_le hab]; exact fun t ht => (h2 ht).symm)
  have i3 : IntervalIntegrable G volume b 1 :=
    (intervalIntegrable_const (c := (0 : ℝ))).congr_uIoo
      (by rw [uIoo_of_le hb]; exact fun t ht => (h3 ht).symm)
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 (i2.trans i3),
    ← intervalIntegral.integral_add_adjacent_intervals i2 i3,
    intervalIntegral.integral_congr_Ioo_of_le ha h1,
    intervalIntegral.integral_congr_Ioo_of_le hab h2,
    intervalIntegral.integral_congr_Ioo_of_le hb h3]
  simp

/-- `∫_a^b sin²(κ(t − a)) dt = ∫_a^b cos²(κ(t − a)) dt = (b − a)/2` when `κ(b − a) = π`. -/
theorem integral_sin_sq_shift {a b κ : ℝ} (hκ : κ * (b - a) = π) :
    ∫ t in a..b, sin (κ * (t - a)) ^ 2 = (b - a) / 2 := by
  have hκ0 : κ ≠ 0 := by rintro rfl; simp at hκ; exact pi_ne_zero hκ.symm
  have h := intervalIntegral.integral_comp_mul_sub (fun x => sin x ^ 2) hκ0 (κ * a)
    (a := a) (b := b)
  simp only [mul_sub] at h ⊢
  rw [h, sub_self, ← mul_sub, hκ, integral_sin_sq]
  simp only [sin_zero, cos_zero, sin_pi, cos_pi, smul_eq_mul]
  rw [← hκ]
  field_simp
  ring

theorem integral_cos_sq_shift {a b κ : ℝ} (hκ : κ * (b - a) = π) :
    ∫ t in a..b, cos (κ * (t - a)) ^ 2 = (b - a) / 2 := by
  have hκ0 : κ ≠ 0 := by rintro rfl; simp at hκ; exact pi_ne_zero hκ.symm
  have h := intervalIntegral.integral_comp_mul_sub (fun x => cos x ^ 2) hκ0 (κ * a)
    (a := a) (b := b)
  simp only [mul_sub] at h ⊢
  rw [h, sub_self, ← mul_sub, hκ, integral_cos_sq]
  simp only [sin_zero, cos_zero, sin_pi, cos_pi, smul_eq_mul]
  rw [← hκ]
  field_simp
  ring

/-! ### The test fields supported in `[a, b]` -/

/-- **Milnor's test field on `[a, b]`** (p. 106): `sin(π(t − a)/(b − a)) P(t)` for `t ∈ [a, b]`,
`0` elsewhere (written with a clamp, which makes continuity evident). -/
def sinBump (a b : ℝ) (P : ℝ → V) (t : ℝ) : V :=
  sin (π / (b - a) * (max a (min t b) - a)) • P t

section SinBump

variable {a b : ℝ} {P : ℝ → V}

omit [FiniteDimensional ℝ V] in
theorem sinBump_of_mem {t : ℝ} (ht : t ∈ Icc a b) :
    sinBump a b P t = sin (π / (b - a) * (t - a)) • P t := by
  rw [sinBump, min_eq_left ht.2, max_eq_right ht.1]

omit [FiniteDimensional ℝ V] in
theorem sinBump_of_le (hab : a ≤ b) {t : ℝ} (ht : t ≤ a) : sinBump a b P t = 0 := by
  rw [sinBump, min_eq_left (ht.trans hab), max_eq_left ht, sub_self, mul_zero, sin_zero,
    zero_smul]

omit [FiniteDimensional ℝ V] in
theorem sinBump_of_ge (hab : a < b) {t : ℝ} (ht : b ≤ t) : sinBump a b P t = 0 := by
  rw [sinBump, min_eq_right ht, max_eq_right hab.le, div_mul_cancel₀ _ (sub_ne_zero.2 hab.ne'),
    sin_pi, zero_smul]

omit [FiniteDimensional ℝ V] in
theorem sinBump_eventually_zero (hab : a < b) {t : ℝ} (ht : t ∉ Icc a b) :
    sinBump a b P =ᶠ[𝓝 t] 0 := by
  rcases not_and_or.1 ht with h | h
  · filter_upwards [Iio_mem_nhds (not_le.1 h)] with s hs using sinBump_of_le hab.le hs.le
  · filter_upwards [Ioi_mem_nhds (not_le.1 h)] with s hs using sinBump_of_ge hab hs.le

omit [FiniteDimensional ℝ V] in
theorem sinBump_eventuallyEq {t : ℝ} (ht : t ∈ Ioo a b) :
    sinBump a b P =ᶠ[𝓝 t] fun s => sin (π / (b - a) * (s - a)) • P s := by
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs using sinBump_of_mem (Ioo_subset_Icc_self hs)

end SinBump

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem curvOp_zero_right (q : N) (x : V) : curvOp hN q x 0 = 0 := by
  simpa using curvOp_smul_right hN q (0 : ℝ) x 0

section Fields

variable {p q : V} {γ : ℝ → V} {c : ℝ → N} {P : ℝ → V} {a b : ℝ}

omit [FiniteDimensional ℝ W] in
/-- `sinBump a b P` is smooth on `[a, b]`-pieces, so it is a field of `TΩ_γ`. -/
theorem sinBump_mem_pathTangent (hcs : ContDiff ℝ ∞ (fun t => (c t : V)))
    (hγc : ∀ t ∈ Icc (0 : ℝ) 1, γ t = c t) (hP : IsParallel hN c P) (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ 1) : sinBump a b P ∈ pathTangent hN γ := by
  have hPs : ContDiff ℝ ∞ P := hP.contDiff hN hcs
  have hsm : ContDiff ℝ ∞ (fun s => sin (π / (b - a) * (s - a)) • P s) :=
    (contDiff_sin.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))).smul hPs
  have hcont : Continuous (sinBump a b P) :=
    (continuous_sin.comp (continuous_const.mul ((continuous_const.max
      (continuous_id.min continuous_const)).sub continuous_const))).smul hPs.continuous
  refine ⟨⟨zero_le_one, hcont.continuousOn, {a, b}, fun s t hs hst ht hB => ?_⟩, fun t ht => ?_,
    sinBump_of_le hab.le ha, sinBump_of_ge hab hb⟩
  · have haB : a ∉ Ioo s t := hB a (by simp)
    have hbB : b ∉ Ioo s t := hB b (by simp)
    rcases le_or_gt t a with hta | hta
    · exact (contDiffOn_const (c := (0 : V))).congr fun x hx =>
        sinBump_of_le hab.le (hx.2.trans hta)
    rcases le_or_gt b s with hbs | hbs
    · exact (contDiffOn_const (c := (0 : V))).congr fun x hx => sinBump_of_ge hab (hbs.trans hx.1)
    have has : a ≤ s := by
      by_contra h
      exact haB ⟨not_le.1 h, hta⟩
    have htb : t ≤ b := by
      by_contra h
      exact hbB ⟨hbs, not_le.1 h⟩
    exact hsm.contDiffOn.congr fun x hx => sinBump_of_mem ⟨has.trans hx.1, hx.2.trans htb⟩
  · rw [sinBump, map_smul, hγc t ht, (prj_eq_self_iff hN (c t).2).2 (hP.mem t)]

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- On the open set where `sinBump a b P` vanishes, so do it and `D/dt` of it. -/
theorem covD_sinBump_of_notMem {γ : ℝ → V} (hab : a < b) {t : ℝ} (ht : t ∉ Icc a b) :
    covD hN γ (sinBump a b P) t = 0 ∧ sinBump a b P t = 0 := by
  have hev := sinBump_eventually_zero (P := P) hab ht
  refine ⟨?_, hev.self_of_nhds⟩
  rw [covD, hev.deriv_eq]
  simp

/-- **The second variation along `sinBump a b P`** (`P` parallel and of norm `1` along a smooth
curve `c` equal to `γ` on `[0, 1]`, `Vf = γ'` on `(0, 1)`):
`½ E_**(X, X) = ∫_a^b (κ² cos²(κ(t − a)) − sin²(κ(t − a)) ⟨R(V, P)V, P⟩) dt`, `κ = π/(b − a)`. -/
theorem energyHessian_sinBump (hγ : γ ∈ pathSpace N p q) (hcs : ContDiff ℝ ∞ (fun t => (c t : V)))
    (hγc : ∀ t ∈ Icc (0 : ℝ) 1, γ t = c t) (hP : IsParallel hN c P) (hP1 : ∀ t, ‖P t‖ = 1)
    {Vf : ℝ → V} (hVfs : ContDiff ℝ ∞ Vf) (hVfT : ∀ t, Vf t ∈ tangentSubspace hN (c t))
    (hVγ : ∀ t ∈ Ioo (0 : ℝ) 1, deriv γ t = Vf t) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    energyHessian hN hγ ⟨_, sinBump_mem_pathTangent hcs hγc hP ha hab hb⟩
      ⟨_, sinBump_mem_pathTangent hcs hγc hP ha hab hb⟩ = 2 * ∫ t in a..b,
        ((π / (b - a)) ^ 2 * cos (π / (b - a) * (t - a)) ^ 2 -
          sin (π / (b - a) * (t - a)) ^ 2 * ⟪curvR hN (c t) (Vf t) (P t) (Vf t), P t⟫) := by
  have hPs : ContDiff ℝ ∞ P := hP.contDiff hN hcs
  have hT : ∀ t, prj hN (c t) (P t) = P t := fun t => (prj_eq_self_iff hN (c t).2).2 (hP.mem t)
  have hk := continuous_inner_curvR hcs hVfs hVfT hPs hP.mem
  rw [energyHessian_eq_integral]
  congr 1
  refine integral_eq_of_eqOn_pieces ha hab.le hb (by fun_prop) (fun t ht => ?_) (fun t ht => ?_)
    (fun t ht => ?_)
  · obtain ⟨h1, h2⟩ := covD_sinBump_of_notMem (hN := hN) (γ := γ) (P := P) hab
      (fun h => not_le.2 ht.2 h.1)
    simp [h1, h2]
  · set κ := π / (b - a)
    have hd : HasDerivAt (fun s => sin (κ * (s - a)) • P s)
        (sin (κ * (t - a)) • deriv P t + (cos (κ * (t - a)) * κ) • P t) t := by
      have h1 : HasDerivAt (fun s => sin (κ * (s - a))) (cos (κ * (t - a)) * κ) t := by
        simpa using (((hasDerivAt_id t).sub_const a).const_mul κ).sin
      exact h1.smul (hP.differentiable t).hasDerivAt
    have hprj0 : prj hN (c t) (deriv P t) = 0 := by
      rw [prj_of_mem hN (c t).2]
      exact hP.covDeriv_eq_zero t
    have ht01 : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_lt ha ht.1, lt_of_lt_of_le ht.2 hb⟩
    have hγt : γ t = c t := hγc t (Ioo_subset_Icc_self ht01)
    have hcov : covD hN γ (sinBump a b P) t = (κ * cos (κ * (t - a))) • P t := by
      rw [covD, (sinBump_eventuallyEq ht).deriv_eq, hd.deriv, hγt, map_add, map_smul, map_smul,
        hprj0, hT, smul_zero, zero_add, mul_comm]
    change ⟪covD hN γ (sinBump a b P) t, covD hN γ (sinBump a b P) t⟫ -
        ⟪curvR hN (γ t) (deriv γ t) (sinBump a b P t) (deriv γ t), sinBump a b P t⟫ = _
    rw [hcov, sinBump_of_mem (Ioo_subset_Icc_self ht), hγt, hVγ t ht01, curvR_of_mem hN (c t).2,
      curvOp_smul_right, real_inner_smul_left, real_inner_smul_right, smul_apply,
      real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, hP1,
      ← curvR_of_mem hN (c t).2]
    ring
  · obtain ⟨h1, h2⟩ := covD_sinBump_of_notMem (hN := hN) (γ := γ) (P := P) hab
      (fun h => not_le.2 ht.1 h.2)
    simp [h1, h2]

/-- **Fields with disjoint supports are `E_**`-orthogonal** (Milnor p. 106: "clearly
`E_**(X_i, X_j) = 0` for `i ≠ j`"): the integrand vanishes off the common end point. -/
theorem energyHessian_sinBump_disjoint (hγ : γ ∈ pathSpace N p q)
    (hcs : ContDiff ℝ ∞ (fun t => (c t : V))) (hγc : ∀ t ∈ Icc (0 : ℝ) 1, γ t = c t)
    {P' : ℝ → V} (hP : IsParallel hN c P) (hP' : IsParallel hN c P') {a' b' : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b ≤ 1) (ha' : 0 ≤ a') (hab' : a' < b') (hb' : b' ≤ 1) (hba' : b ≤ a') :
    energyHessian hN hγ ⟨_, sinBump_mem_pathTangent hcs hγc hP ha hab hb⟩
      ⟨_, sinBump_mem_pathTangent hcs hγc hP' ha' hab' hb'⟩ = 0 := by
  rw [energyHessian_eq_integral]
  suffices h : ∫ t in (0 : ℝ)..1, (⟪covD hN γ (sinBump a b P) t,
      covD hN γ (sinBump a' b' P') t⟫ - ⟪curvR hN (γ t) (deriv γ t) (sinBump a b P t)
      (deriv γ t), sinBump a' b' P' t⟫) = 0 by
    simp only at h ⊢
    rw [h, mul_zero]
  rw [integral_eq_of_eqOn_pieces (F := fun _ => 0) ha hab.le hb continuous_const
    (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_)]
  · simp
  · obtain ⟨h1, h2⟩ := covD_sinBump_of_notMem (hN := hN) (γ := γ) (P := P) hab
      (fun h => not_le.2 ht.2 h.1)
    have hγN : γ t ∈ N := by
      rw [hγc t ⟨ht.1.le, (ht.2.trans hab).le.trans hb⟩]
      exact (c t).2
    simp [h1, h2, curvR_of_mem hN hγN, curvOp_zero_right]
  · obtain ⟨h1, h2⟩ := covD_sinBump_of_notMem (hN := hN) (γ := γ) (P := P') hab'
      (fun h => not_le.2 (ht.2.trans_le hba') h.1)
    simp [h1, h2]
  · obtain ⟨h1, h2⟩ := covD_sinBump_of_notMem (hN := hN) (γ := γ) (P := P) hab
      (fun h => not_le.2 ht.1 h.2)
    have hγN : γ t ∈ N := by
      rw [hγc t ⟨ha.trans (hab.le.trans ht.1.le), ht.2.le⟩]
      exact (c t).2
    simp [h1, h2, curvR_of_mem hN hγN, curvOp_zero_right]

end Fields

/-! ### Long geodesics have large index -/

/-- **On each piece some test field has negative energy** (Milnor p. 106): if `γ` has length
`L`, `0 ≤ a < b ≤ 1` and `L(b − a) > πr`, then for one of the `n − 1` frame fields `P_i`
perpendicular to `γ`, `E_**(sinBump a b P_i, sinBump a b P_i) < 0`: summed over `i`,
`½ Σ E_** ≤ (n − 1)(b − a)(κ² − L²/r²)/2 < 0`, `κ = π/(b − a)`. -/
theorem exists_sinBump_neg {r : ℝ} (hr : 0 < r) (hn : 2 ≤ finrank ℝ Z) {p q : V} {γ : ℝ → V}
    (hγ : γ ∈ pathSpace N p q)
    {c : ℝ → N} (hcs : ContDiff ℝ ∞ (fun t => (c t : V))) (hγc : ∀ t ∈ Icc (0 : ℝ) 1, γ t = c t)
    {Vf : ℝ → V} (hVfs : ContDiff ℝ ∞ Vf) (hVfT : ∀ t, Vf t ∈ tangentSubspace hN (c t))
    (hVγ : ∀ t ∈ Ioo (0 : ℝ) 1, deriv γ t = Vf t) {ι : Type*} {s : Finset ι} {P : ι → ℝ → V}
    (hP : ∀ i, IsParallel hN c (P i)) (hPn : ∀ i t, ‖P i t‖ = 1)
    (hcard : s.card + 1 = finrank ℝ Z)
    (hksum : ∀ t, pathLength γ 0 1 ^ 2 * (s.card / r ^ 2) ≤
      ∑ i ∈ s, ⟪curvR hN (c t) (Vf t) (P i t) (Vf t), P i t⟫)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (hL : π * r < pathLength γ 0 1 * (b - a)) :
    ∃ i ∈ s, energyHessian hN hγ ⟨_, sinBump_mem_pathTangent hcs hγc (hP i) ha hab hb⟩
      ⟨_, sinBump_mem_pathTangent hcs hγc (hP i) ha hab hb⟩ < 0 := by
  set L := pathLength γ 0 1 with hLdef
  set κ := π / (b - a) with hκ
  have hba : 0 < b - a := sub_pos.2 hab
  have hκba : κ * (b - a) = π := by rw [hκ, div_mul_cancel₀ _ hba.ne']
  have hcardR : (s.card : ℝ) = (finrank ℝ Z : ℝ) - 1 := by
    rw [← hcard]; push_cast; ring
  set k : ι → ℝ → ℝ := fun i t => ⟪curvR hN (c t) (Vf t) (P i t) (Vf t), P i t⟫ with hk
  set f : ι → ℝ → ℝ := fun i t => κ ^ 2 * cos (κ * (t - a)) ^ 2 - sin (κ * (t - a)) ^ 2 * k i t
    with hf
  have hfc : ∀ i, Continuous (f i) := fun i => by
    have := continuous_inner_curvR hcs hVfs hVfT ((hP i).contDiff hN hcs) (hP i).mem
    simp only [hf, hk]
    fun_prop
  have hE : ∀ i, energyHessian hN hγ ⟨_, sinBump_mem_pathTangent hcs hγc (hP i) ha hab hb⟩
      ⟨_, sinBump_mem_pathTangent hcs hγc (hP i) ha hab hb⟩ = 2 * ∫ t in a..b, f i t :=
    fun i => energyHessian_sinBump hγ hcs hγc (hP i) (hPn i) hVfs hVfT hVγ ha hab hb
  set g : ℝ → ℝ := fun t => s.card * (κ ^ 2 * cos (κ * (t - a)) ^ 2) -
    s.card * (L ^ 2 / r ^ 2) * sin (κ * (t - a)) ^ 2 with hg
  have hgc : Continuous g := by simp only [hg]; fun_prop
  have hfg : ∀ t, ∑ i ∈ s, f i t ≤ g t := by
    intro t
    have h1 : ∑ i ∈ s, f i t = s.card * (κ ^ 2 * cos (κ * (t - a)) ^ 2) -
        sin (κ * (t - a)) ^ 2 * ∑ i ∈ s, k i t := by
      simp only [hf, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    rw [h1]
    have h2 := hksum t
    have h3 : 0 ≤ sin (κ * (t - a)) ^ 2 := sq_nonneg _
    have h4 : s.card * (L ^ 2 / r ^ 2) = L ^ 2 * (s.card / r ^ 2) := by ring
    simp only [hg]
    rw [h4]
    nlinarith
  have hint : ∫ t in a..b, g t =
      s.card * (κ ^ 2 * ((b - a) / 2)) - s.card * (L ^ 2 / r ^ 2) * ((b - a) / 2) := by
    simp only [hg]
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_cos_sq_shift hκba, integral_sin_sq_shift hκba]
    · exact (by fun_prop : Continuous fun t : ℝ => (s.card : ℝ) *
        (κ ^ 2 * cos (κ * (t - a)) ^ 2)).intervalIntegrable a b
    · exact (by fun_prop : Continuous fun t : ℝ => (s.card : ℝ) * (L ^ 2 / r ^ 2) *
        sin (κ * (t - a)) ^ 2).intervalIntegrable a b
  have hneg : ∑ i ∈ s, (2 * ∫ t in a..b, f i t) < 0 := by
    rw [← Finset.mul_sum, ← intervalIntegral.integral_finsetSum fun i _ =>
      (hfc i).intervalIntegrable a b]
    have hle : ∫ t in a..b, ∑ i ∈ s, f i t ≤ ∫ t in a..b, g t :=
      intervalIntegral.integral_mono_on hab.le
        ((continuous_finsetSum s fun i _ => hfc i).intervalIntegrable a b)
        (hgc.intervalIntegrable a b) fun t _ => hfg t
    rw [hint] at hle
    have hcpos : (1 : ℝ) ≤ s.card := by
      rw [hcardR]
      have : (2 : ℝ) ≤ finrank ℝ Z := by exact_mod_cast hn
      linarith
    have hκL : κ ^ 2 < L ^ 2 / r ^ 2 := by
      rw [lt_div_iff₀ (by positivity)]
      have h1 : κ * (b - a) * r < L * (b - a) := by rw [hκba]; exact hL
      have h2 : κ * r < L := by nlinarith
      have h3 : 0 ≤ κ * r := by positivity
      nlinarith
    have hneg' : (s.card : ℝ) * ((b - a) / 2) * (κ ^ 2 - L ^ 2 / r ^ 2) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) (by linarith)
    nlinarith
  by_contra hall
  push Not at hall
  exact (Finset.sum_nonneg fun i hi => (hE i).symm ▸ hall i hi).not_gt hneg

/-- **Theorem 19.6, the index estimate** (Milnor p. 106): if `n ≥ 2` and `K(U, U) ≥ (n − 1)/r²`
for all unit vectors, every geodesic `γ ∈ Ω(N; p, q)` of length `> kπr` has index `≥ k`.  For
`i = 0, …, k − 1` some field `X_i = sin(πk(t − i/k)) P_j(t)` on `[i/k, (i + 1)/k]` (`0` elsewhere)
has `E_**(X_i, X_i) < 0`; fields on different pieces are `E_**`-orthogonal, so `E_**` is negative
definite on the `k`-dimensional span of the `X_i`. -/
theorem theorem_19_6_index {r : ℝ} (hr : 0 < r) (hn : 2 ≤ finrank ℝ Z)
    (hRic : RicciLowerBound hN r) {p q : V} {γ : ℝ → V} (hγ : γ ∈ pathSpace N p q)
    (hgeo : IsUnbrokenGeodesic hN γ) {k : ℕ} (hL : k * π * r < pathLength γ 0 1) :
    (k : ℕ∞) ≤ formIndex (energyHessian hN hγ) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  set L := pathLength γ 0 1 with hLdef
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hLpos : 0 < L := lt_of_le_of_lt (by positivity) hL
  obtain ⟨c, hcs, hγc, Vf, hVfs, hVfT, hVγ, u, s, P, hP, hPn, hcard, hksum⟩ :=
    exists_parallel_frame hγ hgeo hLpos
  -- the pieces `[i/k, (i + 1)/k]`
  set a : Fin k → ℝ := fun i => (i : ℝ) / k with ha_def
  set b : Fin k → ℝ := fun i => ((i : ℝ) + 1) / k with hb_def
  have ha : ∀ i, 0 ≤ a i := fun i => by positivity
  have hab : ∀ i, a i < b i := fun i => div_lt_div_of_pos_right (by linarith) hkR
  have hb : ∀ i, b i ≤ 1 := fun i => by
    rw [hb_def, div_le_one hkR]
    exact_mod_cast i.2
  have hlen : ∀ i, π * r < L * (b i - a i) := fun i => by
    have h1 : b i - a i = 1 / k := by
      simp only [ha_def, hb_def]
      field_simp
      ring
    rw [h1, mul_one_div, lt_div_iff₀ hkR]
    linarith
  have hex := fun i => exists_sinBump_neg hr hn hγ hcs hγc hVfs hVfT hVγ hP hPn hcard
    (hksum r hRic) (ha i) (hab i) (hb i) (hlen i)
  choose j hj hneg using hex
  set Y : Fin k → pathTangent hN γ := fun i =>
    ⟨_, sinBump_mem_pathTangent hcs hγc (hP (j i)) (ha i) (hab i) (hb i)⟩ with hY
  have hYY : ∀ i, energyHessian hN hγ (Y i) (Y i) < 0 := hneg
  have hsep : ∀ i i' : Fin k, i < i' → b i ≤ a i' := fun i i' h => by
    simp only [ha_def, hb_def]
    rw [div_le_div_iff_of_pos_right hkR]
    exact_mod_cast h
  have horth : ∀ i i', i ≠ i' → energyHessian hN hγ (Y i) (Y i') = 0 := by
    intro i i' hii'
    rcases lt_or_gt_of_ne hii' with h | h
    · exact energyHessian_sinBump_disjoint hγ hcs hγc (hP (j i)) (hP (j i')) (ha i) (hab i)
        (hb i) (ha i') (hab i') (hb i') (hsep i i' h)
    · rw [LinearMap.BilinForm.isSymm_def.1 (energyHessian_isSymm hN hγ)]
      exact energyHessian_sinBump_disjoint hγ hcs hγc (hP (j i')) (hP (j i)) (ha i') (hab i')
        (hb i') (ha i) (hab i) (hb i) (hsep i' i h)
  -- `E_**` on the span of the `Y_i`
  set Φ := Fintype.linearCombination ℝ Y with hΦdef
  have hΦ : ∀ x, energyHessian hN hγ (Φ x) (Φ x) =
      ∑ i, x i ^ 2 * energyHessian hN hγ (Y i) (Y i) := by
    intro x
    simp only [hΦdef, Fintype.linearCombination_apply, LinearMap.BilinForm.sum_left,
      LinearMap.BilinForm.sum_right, LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_eq_single i (fun i' _ hi' => by rw [horth i' i hi']; ring)
      (by simp)]
    ring
  have hΦneg : ∀ x, x ≠ 0 → energyHessian hN hγ (Φ x) (Φ x) < 0 := by
    intro x hx
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hx
    rw [hΦ, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
    have h1 : x i₀ ^ 2 * energyHessian hN hγ (Y i₀) (Y i₀) < 0 :=
      mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hi₀) (hYY i₀)
    have h2 : ∑ i ∈ Finset.univ.erase i₀, x i ^ 2 * energyHessian hN hγ (Y i) (Y i) ≤ 0 :=
      Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hYY i).le
    linarith
  have hinj : Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 fun x hx => ?_
    by_contra hx0
    have := hΦneg x hx0
    simp [hx] at this
  have hS : IsNegDefOn (energyHessian hN hγ) (LinearMap.range Φ) := by
    rintro _ ⟨x, rfl⟩ hx0
    exact hΦneg x fun h => hx0 (by rw [h, map_zero])
  have h := le_formIndex hS
  rwa [LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun] at h

/-- **Theorem 19.6, the index estimate, contrapositive** (Milnor p. 106, used with Theorem 16.3):
a geodesic of index `< k` has length `≤ kπr`. -/
theorem pathLength_le_of_formIndex_lt {r : ℝ} (hr : 0 < r) (hn : 2 ≤ finrank ℝ Z)
    (hRic : RicciLowerBound hN r) {p q : V} {γ : ℝ → V} (hγ : γ ∈ pathSpace N p q)
    (hgeo : IsUnbrokenGeodesic hN γ) {k : ℕ} (hk : formIndex (energyHessian hN hγ) < k) :
    pathLength γ 0 1 ≤ k * π * r :=
  not_lt.1 fun hL => (theorem_19_6_index hr hn hRic hγ hgeo hL).not_gt hk

/-- **Theorem 19.6, the index estimate, with the index theorem**: a geodesic of length `> kπr`
contains at least `k` points `γ(t)`, `0 < t < 1`, conjugate to `γ(0)`, counted with
multiplicity. -/
theorem le_finsum_conjMultiplicity_of_ricci {r : ℝ} (hr : 0 < r) (hn : 2 ≤ finrank ℝ Z)
    (hRic : RicciLowerBound hN r) {p q : V} {γ : ℝ → V} (hγ : γ ∈ pathSpace N p q)
    (hgeo : IsUnbrokenGeodesic hN γ) {k : ℕ} (hL : k * π * r < pathLength γ 0 1) :
    k ≤ ∑ᶠ t ∈ Ioo (0 : ℝ) 1, conjMultiplicity hN γ (hgeo.isSmoothCurveIn hN hγ) 0 t := by
  have h := theorem_19_6_index hr hn hRic hγ hgeo hL
  rw [(theorem_15_1 hN hγ hgeo).2] at h
  exact_mod_cast h

end Morse
