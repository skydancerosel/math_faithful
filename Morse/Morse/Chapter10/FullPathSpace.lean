import Morse.Chapter10.Omega
import Morse.Appendix.MonotoneUnion

/-!
Milnor, *Morse Theory*, §17, p. 93: the space `Ω*` of continuous paths and the inclusion
`Ω → Ω*`, with the analytic and topological preliminaries of the proof of Theorem 17.1 given in
Exposition/Chapter10.md, §5 ("A proof that works").

# The full path space `Ω*`

## Milnor's text, paraphrased

(p. 93) `Ω* = Ω*(M; p, q)` is the space of all continuous paths from `p` to `q` with the
compact-open topology; it is the topology of the uniform metric `d*`, and since `d ≥ d*` the
natural map `i : Ω → Ω*` is continuous.  **Theorem 17.1**: `i` is a homotopy equivalence.

## In the embedded setting

* `Morse.PathC N p q`: `Ω*`, the continuous maps `γ : [0, 1] → V` with values in `N`, `γ 0 = p`,
  `γ 1 = q`, as a subspace of `C([0, 1], V)` (uniform metric).
* `Morse.PathSp.toPathC`: **the inclusion `i : Ω → Ω*`**; `Morse.PathSp.edist_toPathC_le`
  (`d* ≤ d`) and `Morse.PathSp.continuous_toPathC`.
* `Morse.PathSp.tendsto_integral_norm_deriv_sub_sq`: **convergence in Milnor's metric controls
  the velocities in `L²`**: if `γⱼ → γ` in `Ω` then `∫₀¹ ‖γⱼ' − γ'‖² → 0`, although `d` only
  involves the speeds `‖γ'‖`: the energies converge, and the velocities converge weakly
  (integration by parts on the smooth pieces of `γ`, `Morse.PathSp.integral_inner_deriv_eq`, and
  uniform convergence).  Conversely `Morse.PathSp.tendsto_of_tendsto_apply_of_integral`:
  pointwise convergence and `L²` convergence of the velocities give convergence for `d`.
* `Morse.isHomotopyDirectLimit_preimage`: Example 1 of the Appendix pulled back along a continuous
  map, so that it applies to `Ω` (whose pseudo-metric is not Hausdorff) through `i`.
* `Morse.dy`, `Morse.dseg`: dyadic subdivisions of `[0, 1]`.

## What Milnor leaves implicit

* **`Ω` is not Hausdorff** here (paths are functions on `ℝ`, and Milnor's `d` only sees `[0, 1]`),
  so Example 1 of the Appendix (paracompact Hausdorff spaces) is applied in `Ω*` and pulled back.
* **The `L²` term of `d` controls velocities, not only speeds.**  This is what makes maps defined
  pointwise by smooth formulas, such as the interpolation of a path with a broken geodesic along
  minimal geodesics, continuous for `d`.
-/

open Set Filter Topology Function Module Metric MeasureTheory
open scoped ContDiff Manifold RealInnerProductSpace ENNReal Interval NNReal unitInterval

noncomputable section

namespace Morse

/-! ### Dyadic subdivisions -/

/-- The dyadic points `j / 2^k`. -/
def dy (k j : ℕ) : ℝ := j / 2 ^ k

/-- The dyadic interval of level `k` containing `s ∈ [0, 1]`: `⌊s 2^k⌋`, capped at `2^k − 1`. -/
def dseg (k : ℕ) (s : ℝ) : ℕ := min ⌊s * 2 ^ k⌋₊ (2 ^ k - 1)

theorem dy_nonneg (k j : ℕ) : 0 ≤ dy k j := by unfold dy; positivity

theorem dy_succ_sub (k j : ℕ) : dy k (j + 1) - dy k j = 1 / 2 ^ k := by
  unfold dy; push_cast; ring

theorem dy_lt_succ (k j : ℕ) : dy k j < dy k (j + 1) := by
  have := dy_succ_sub k j
  have : (0 : ℝ) < 1 / 2 ^ k := by positivity
  linarith

theorem dy_mono (k : ℕ) {i j : ℕ} (h : i ≤ j) : dy k i ≤ dy k j := by
  unfold dy
  gcongr

theorem dy_le_one {k j : ℕ} (hj : j ≤ 2 ^ k) : dy k j ≤ 1 := by
  unfold dy
  rw [div_le_one (by positivity)]
  exact_mod_cast hj

theorem dy_two_pow (k : ℕ) : dy k (2 ^ k) = 1 := by
  unfold dy
  push_cast
  exact div_self (by positivity)

theorem dy_zero (k : ℕ) : dy k 0 = 0 := by simp [dy]

theorem dy_succ_level (k j : ℕ) : dy (k + 1) (2 * j) = dy k j := by
  unfold dy
  push_cast
  rw [pow_succ]
  field_simp

theorem dseg_lt (k : ℕ) (s : ℝ) : dseg k s < 2 ^ k := by
  unfold dseg
  have : 0 < 2 ^ k := by positivity
  omega

theorem mem_Icc_dseg {k : ℕ} {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    s ∈ Icc (dy k (dseg k s)) (dy k (dseg k s + 1)) := by
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have hfl := Nat.floor_le (show 0 ≤ s * 2 ^ k by have := hs.1; positivity)
  have hlt := Nat.lt_floor_add_one (s * 2 ^ k)
  unfold dseg dy
  rcases le_total ⌊s * 2 ^ k⌋₊ (2 ^ k - 1) with h | h
  · rw [min_eq_left h]
    constructor
    · rw [div_le_iff₀ h2]; exact hfl
    · rw [le_div_iff₀ h2]; push_cast; linarith
  · rw [min_eq_right h]
    have h1 : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
    have hcast : ((2 ^ k - 1 : ℕ) : ℝ) = 2 ^ k - 1 := by
      rw [Nat.cast_sub h1]; push_cast; ring
    constructor
    · rw [div_le_iff₀ h2, hcast]
      have : ((2 ^ k - 1 : ℕ) : ℝ) ≤ ⌊s * 2 ^ k⌋₊ := by exact_mod_cast h
      rw [hcast] at this
      linarith
    · rw [le_div_iff₀ h2]
      push_cast
      rw [Nat.cast_sub h1]
      push_cast
      nlinarith [hs.2]

/-- Each dyadic interval of level `k + 1` lies in one of level `k`. -/
theorem Icc_dy_succ_subset (k j : ℕ) :
    Icc (dy (k + 1) j) (dy (k + 1) (j + 1)) ⊆ Icc (dy k (j / 2)) (dy k (j / 2 + 1)) := by
  intro s hs
  have h1 : dy k (j / 2) ≤ dy (k + 1) j :=
    (le_of_eq (dy_succ_level k (j / 2)).symm).trans
      (dy_mono (k + 1) (show 2 * (j / 2) ≤ j by omega))
  have h2 : dy (k + 1) (j + 1) ≤ dy k (j / 2 + 1) :=
    (dy_mono (k + 1) (show j + 1 ≤ 2 * (j / 2 + 1) by omega)).trans
      (le_of_eq (dy_succ_level k (j / 2 + 1)))
  exact ⟨h1.trans hs.1, hs.2.trans h2⟩



/-! ### Homotopy direct limits of preimages of open covers -/

/-- **Example 1, pulled back** (Milnor p. 149): if `Y` is paracompact and Hausdorff and every
point of `Y` lies in the interior of some `B_n`, then for every continuous `g : X → Y` the space
`X` is the homotopy direct limit of the `g⁻¹(B_n)` (no assumption on `X`). -/
theorem isHomotopyDirectLimit_preimage {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ParacompactSpace Y] [T2Space Y] {B : ℕ → Set Y} (hB : Monotone B)
    (hint : ∀ y, ∃ n, y ∈ interior (B n)) (g : C(X, Y)) :
    IsHomotopyDirectLimit fun n => g ⁻¹' B n := by
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ (fun n => interior (B n))
    (fun _ => isOpen_interior) (fun y _ => mem_iUnion.2 (hint y))
  have hcont : Continuous fun y => ∑ᶠ n, ρ n y • (n : ℝ) :=
    ρ.continuous_finsum_smul fun _ _ _ => continuousAt_const
  refine isHomotopyDirectLimit_of_level (fun m n h => preimage_mono (hB h))
    ((⟨_, hcont⟩ : C(Y, ℝ)).comp g)
    (fun x => finsum_nonneg fun n => smul_nonneg (ρ.nonneg n (g x)) (Nat.cast_nonneg n)) ?_
  intro i x hx
  have hz : ∀ j ≤ i, ρ j (g x) = 0 := fun j hj => by
    by_contra h
    exact hx (hB hj (interior_subset (hρ j (subset_tsupport _ h))))
  have hfin : (support fun j => ρ j (g x)).Finite := ρ.locallyFinite.point_finite (g x)
  change (i : ℝ) + 1 ≤ ∑ᶠ n, ρ n (g x) • (n : ℝ)
  calc (i : ℝ) + 1 = ∑ᶠ j, ρ j (g x) * ((i : ℝ) + 1) := by
        rw [← finsum_mul, ρ.sum_eq_one (mem_univ (g x)), one_mul]
    _ ≤ ∑ᶠ j, ρ j (g x) • (j : ℝ) := by
        refine finsum_le_finsum' (hfin.subset ?_) (hfin.subset ?_) fun j => ?_
        · intro j hj
          exact fun h => hj (by simp [h])
        · intro j hj
          exact fun h => hj (by simp [h])
        · rcases le_or_gt j i with hj | hj
          · simp [hz j hj]
          · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hj
            rw [smul_eq_mul]
            exact mul_le_mul_of_nonneg_left this (ρ.nonneg j (g x))

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

/-! ### The space `Ω*` of continuous paths -/

variable (N) in
/-- **Milnor's `Ω* = Ω*(M; p, q)`** (p. 93): the continuous paths `[0, 1] → N` from `p` to `q`,
as a subspace of `C([0, 1], V)` with the compact-open (= uniform) topology. -/
def pathCSet (p q : V) : Set C(I, V) := {γ | (∀ t, γ t ∈ N) ∧ γ 0 = p ∧ γ 1 = q}

variable (N) in
/-- `Ω*` as a type. -/
abbrev PathC (p q : V) : Type _ := ↥(pathCSet N p q)

namespace PathSp

variable {p q : V}

/-- The underlying continuous path `[0, 1] → V` of a piecewise smooth path. -/
def toC (γ : PathSp N p q) : C(I, V) :=
  ⟨fun t => γ (t : ℝ), γ.mem.1.2.1.comp_continuous continuous_subtype_val fun t => t.2⟩

/-- **The inclusion `i : Ω → Ω*`** (Milnor p. 93). -/
def toPathC (γ : PathSp N p q) : PathC N p q :=
  ⟨toC γ, fun t => γ.mem.2.1 t t.2, γ.mem.2.2.1, γ.mem.2.2.2⟩

omit [FiniteDimensional ℝ V] in
theorem toPathC_apply (γ : PathSp N p q) (t : I) : (toPathC γ : C(I, V)) t = γ (t : ℝ) := rfl

/-- `d* ≤ d`: the uniform distance is at most Milnor's distance. -/
theorem edist_toPathC_le (γ γ' : PathSp N p q) : edist (toPathC γ) (toPathC γ') ≤ edist γ γ' := by
  refine le_trans ?_ (supDist_le_edist γ γ')
  rcases eq_or_ne (supDist N γ γ') ⊤ with h | h
  · rw [h]
    exact le_top
  · rw [edist_dist, ← ENNReal.ofReal_toReal h]
    refine ENNReal.ofReal_le_ofReal ?_
    change dist (toC γ) (toC γ') ≤ _
    refine (ContinuousMap.dist_le ENNReal.toReal_nonneg).2 fun t => ?_
    rw [dist_eq_norm]
    have h1 := ofReal_norm_sub_le_riemDist (N := N) (γ' (t : ℝ)) (γ (t : ℝ))
    have h2 := riemDist_le_supDist (N := N) (γ := (γ : ℝ → V)) (γ' := (γ' : ℝ → V)) t.2
    rw [riemDist_comm] at h1
    exact (ENNReal.ofReal_le_iff_le_toReal h).1 (h1.trans h2)

/-- **`i : Ω → Ω*` is continuous** (Milnor p. 93: `d ≥ d*`). -/
theorem continuous_toPathC : Continuous (toPathC : PathSp N p q → PathC N p q) :=
  (LipschitzWith.of_edist_le edist_toPathC_le).continuous

end PathSp


namespace PathSp

variable {p q : V}



omit [FiniteDimensional ℝ V] in
/-- A piecewise smooth path is differentiable at every point of `(0, 1)` off its break points. -/
theorem hasDerivAt_of_notMem {γ : ℝ → V} {B : Finset ℝ}
    (hB : ∀ s t, 0 ≤ s → s < t → t ≤ 1 → (∀ x ∈ B, x ∉ Ioo s t) → ContDiffOn ℝ ∞ γ (Icc s t))
    {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (hτB : τ ∉ B) : HasDerivAt γ (deriv γ τ) τ := by
  obtain ⟨s, s', hs, hsτ, hτs', hs', hBs⟩ := Morse.exists_piece_around B hτ.1 hτ.2 hτB
  have h := hB s s' hs (hsτ.trans hτs') hs' hBs
  exact ((h.contDiffAt (Icc_mem_nhds hsτ hτs')).differentiableAt (by simp)).hasDerivAt

/-- **Uniform convergence from Milnor's metric**: if `γⱼ → γ` in `Ω`, then `γⱼ → γ` uniformly on
`[0, 1]` for the norm of `V`. -/
theorem eventually_norm_sub_le_of_tendsto {ι : Type*} {l : Filter ι} {γs : ι → PathSp N p q}
    {γ : PathSp N p q} (h : Tendsto γs l (𝓝 γ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in l, ∀ t ∈ Icc (0 : ℝ) 1, ‖γs j t - γ t‖ ≤ ε := by
  have h1 := (EMetric.tendsto_nhds.1 h) (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
  filter_upwards [h1] with j hj t ht
  have h2 : ENNReal.ofReal ‖γ t - γs j t‖ ≤ ENNReal.ofReal ε :=
    ((ofReal_norm_sub_le_riemDist (N := N) (γs j t) (γ t)).trans
      (riemDist_le_supDist (N := N) ht)).trans ((supDist_le_edist _ _).trans hj.le)
  rw [norm_sub_rev]
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).1 h2

omit [FiniteDimensional ℝ V] in
/-- **Integration by parts on a smooth piece of `γ`**: if `γ` is smooth on `[s, t] ⊆ [0, 1]` with
`K = γ'` there, then for any `β ∈ Ω`,
`∫ₛᵗ ⟨β', K⟩ = ⟨β(t), K(t)⟩ − ⟨β(s), K(s)⟩ − ∫ₛᵗ ⟨β, K'⟩`. -/
theorem integral_inner_deriv_eq {β : ℝ → V} (hβ : β ∈ pathSpace N p q) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s < t) (ht : t ≤ 1) {K : ℝ → V} (hK : ContDiffOn ℝ ∞ K (Icc s t)) :
    ∫ τ in s..t, ⟪deriv β τ, K τ⟫ =
      ⟪β t, K t⟫ - ⟪β s, K s⟫ - ∫ τ in s..t, ⟪β τ, derivWithin K (Icc s t) τ⟫ := by
  obtain ⟨-, hβc, Bβ, hBβ⟩ := hβ.1
  have hK1 := hK.derivWithin (uniqueDiffOn_Icc hst) (m := ∞) (by simp)
  have hβc' : ContinuousOn β (Icc s t) := hβc.mono (Icc_subset_Icc hs ht)
  -- the integrands
  have hint1 : IntervalIntegrable (fun τ => ⟪deriv β τ, K τ⟫) volume s t := by
    refine intervalIntegrable_of_piecewise (B := Bβ) (lo := s) (hi := t)
      (fun a b ha hab hb hB => ?_) le_rfl hst.le le_rfl
    obtain ⟨h1, h2⟩ := IsPiecewiseSmooth.derivWithin_piece hab
      (hBβ a b (hs.trans ha) hab (hb.trans ht) hB)
    exact ⟨fun τ => ⟪derivWithin β (Icc a b) τ, K τ⟫,
      h1.continuousOn.inner (hK.continuousOn.mono (Icc_subset_Icc ha hb)),
      fun τ hτ => by simp only [h2 hτ]⟩
  have hint2 : IntervalIntegrable (fun τ => ⟪β τ, derivWithin K (Icc s t) τ⟫) volume s t :=
    (hβc'.inner hK1.continuousOn).intervalIntegrable_of_Icc hst.le
  have hFTC := integral_eq_of_hasDerivAt_off_countable_of_le
    (fun τ => ⟪β τ, K τ⟫) (fun τ => ⟪deriv β τ, K τ⟫ + ⟪β τ, derivWithin K (Icc s t) τ⟫)
    hst.le (Bβ.countable_toSet) (hβc'.inner hK.continuousOn) (fun τ hτ => ?_) (hint1.add hint2)
  · rw [intervalIntegral.integral_add hint1 hint2] at hFTC
    linarith
  · have hτ01 : τ ∈ Ioo (0 : ℝ) 1 := ⟨hs.trans_lt hτ.1.1, hτ.1.2.trans_le ht⟩
    have hβd := hasDerivAt_of_notMem hBβ hτ01 hτ.2
    have hKd : HasDerivAt K (derivWithin K (Icc s t) τ) τ := by
      have hdiff := (hK.differentiableOn (by simp)) τ (Ioo_subset_Icc_self hτ.1)
      exact (hdiff.hasDerivWithinAt).hasDerivAt (Icc_mem_nhds hτ.1.1 hτ.1.2)
    have := hβd.inner ℝ hKd
    rwa [add_comm] at this

/-- **Weak convergence of the velocities**: if `γⱼ → γ` in `Ω` (Milnor's metric), then
`∫₀¹ ⟨γⱼ', γ'⟩ → ∫₀¹ ‖γ'‖²` (integration by parts on the smooth pieces of `γ`, and uniform
convergence). -/
theorem tendsto_integral_inner_deriv {ι : Type*} {l : Filter ι} {γs : ι → PathSp N p q}
    {γ : PathSp N p q} (h : Tendsto γs l (𝓝 γ)) :
    Tendsto (fun j => ∫ t in (0 : ℝ)..1, ⟪deriv (γs j) t, deriv γ t⟫) l
      (𝓝 (∫ t in (0 : ℝ)..1, ‖deriv γ t‖ ^ 2)) := by
  obtain ⟨-, -, B, hB⟩ := γ.mem.1
  have hintj : ∀ (j : ι) a b, 0 ≤ a → a ≤ b → b ≤ 1 →
      IntervalIntegrable (fun t => ⟪deriv (γs j) t, deriv γ t⟫) volume a b := fun j a b ha hab hb =>
    intervalIntegrable_comp_deriv (γs j).mem.1 γ.mem.1 (Φ := fun z : V × V => ⟪z.1, z.2⟫)
      (by fun_prop) ha hab hb
  have hint : ∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 →
      IntervalIntegrable (fun t => ‖deriv γ t‖ ^ 2) volume a b := fun a b ha hab hb =>
    (γ.mem.1.mono ha hab hb).intervalIntegrable_norm_deriv_sq
  refine piecewise_induction (B := B) (lo := 0) (hi := 1)
    (P := fun a b => Tendsto (fun j => ∫ t in a..b, ⟪deriv (γs j) t, deriv γ t⟫) l
      (𝓝 (∫ t in a..b, ‖deriv γ t‖ ^ 2))) (fun s t hs hst ht hBst => ?_)
    (fun a x b ha hax hxb hb _ h₁ h₂ => ?_) 0 1 le_rfl zero_lt_one le_rfl
  · -- a smooth piece `[s, t]` of `γ`
    have hγst := hB s t hs hst ht hBst
    obtain ⟨hK, hKeq⟩ := IsPiecewiseSmooth.derivWithin_piece hst hγst
    set K := derivWithin (γ : ℝ → V) (Icc s t) with hK_def
    have hK1 := hK.derivWithin (uniqueDiffOn_Icc hst) (m := ∞) (by simp)
    -- rewrite both sides by integration by parts
    have hj : ∀ j, ∫ τ in s..t, ⟪deriv (γs j) τ, deriv γ τ⟫ =
        ⟪γs j t, K t⟫ - ⟪γs j s, K s⟫ - ∫ τ in s..t, ⟪γs j τ, derivWithin K (Icc s t) τ⟫ := by
      intro j
      rw [← integral_inner_deriv_eq (γs j).mem hs hst ht hK]
      exact intervalIntegral.integral_congr_Ioo_of_le hst.le fun τ hτ => by rw [hKeq hτ]
    have h0 : ∫ τ in s..t, ‖deriv γ τ‖ ^ 2 =
        ⟪γ t, K t⟫ - ⟪γ s, K s⟫ - ∫ τ in s..t, ⟪γ τ, derivWithin K (Icc s t) τ⟫ := by
      rw [← integral_inner_deriv_eq γ.mem hs hst ht hK]
      exact intervalIntegral.integral_congr_Ioo_of_le hst.le fun τ hτ => by
        rw [← hKeq hτ, real_inner_self_eq_norm_sq]
    simp only [hj, h0]
    have hpt : ∀ x₀ ∈ Icc (0 : ℝ) 1, Tendsto (fun j => (γs j : ℝ → V) x₀) l (𝓝 (γ x₀)) := by
      intro x₀ hx₀
      refine Metric.tendsto_nhds.2 fun ε hε => ?_
      filter_upwards [eventually_norm_sub_le_of_tendsto h (half_pos hε)] with j hj
      rw [dist_eq_norm]
      exact (hj x₀ hx₀).trans_lt (half_lt_self hε)
    have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨hs, hst.le.trans ht⟩
    have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨hs.trans hst.le, ht⟩
    refine ((((hpt t ht01).inner tendsto_const_nhds).sub
      ((hpt s hs01).inner tendsto_const_nhds)).sub ?_)
    -- the integral term, by uniform convergence
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hK1.continuousOn
    have hγc : ContinuousOn (γ : ℝ → V) (Icc s t) := γ.mem.1.2.1.mono (Icc_subset_Icc hs ht)
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    set η := ε / (2 * ((t - s) * (|M| + 1))) with hη
    have hη0 : 0 < η := by positivity
    filter_upwards [eventually_norm_sub_le_of_tendsto h hη0] with j hj
    have hjc : ContinuousOn (γs j : ℝ → V) (Icc s t) := (γs j).mem.1.2.1.mono (Icc_subset_Icc hs ht)
    rw [dist_eq_norm, ← intervalIntegral.integral_sub
      ((hjc.inner hK1.continuousOn).intervalIntegrable_of_Icc hst.le)
      ((hγc.inner hK1.continuousOn).intervalIntegrable_of_Icc hst.le)]
    have hbound : ∀ τ ∈ Ι s t, ‖⟪(γs j : ℝ → V) τ, derivWithin K (Icc s t) τ⟫ -
        ⟪γ τ, derivWithin K (Icc s t) τ⟫‖ ≤ η * (|M| + 1) := by
      intro τ hτ
      rw [uIoc_of_le hst.le] at hτ
      have hτ' : τ ∈ Icc s t := Ioc_subset_Icc_self hτ
      rw [← inner_sub_left, Real.norm_eq_abs]
      refine (abs_real_inner_le_norm _ _).trans ?_
      have h1 := hj τ ⟨hs.trans hτ'.1, hτ'.2.trans ht⟩
      have h2 : ‖derivWithin K (Icc s t) τ‖ ≤ |M| + 1 := (hM τ hτ').trans (by
        linarith [le_abs_self M])
      exact mul_le_mul h1 h2 (norm_nonneg _) hη0.le
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hbound).trans_lt ?_
    rw [abs_of_pos (sub_pos.2 hst)]
    have hpos : 0 < (t - s) * (|M| + 1) := by positivity
    have hts : t - s ≠ 0 := (sub_pos.2 hst).ne'
    have hkey : η * (|M| + 1) * (t - s) = ε / 2 := by
      rw [hη]
      field_simp
    rw [hkey]
    linarith
  · -- gluing two pieces
    have e1 : ∀ j, ∫ τ in a..b, ⟪deriv (γs j) τ, deriv γ τ⟫ =
        (∫ τ in a..x, ⟪deriv (γs j) τ, deriv γ τ⟫) + ∫ τ in x..b, ⟪deriv (γs j) τ, deriv γ τ⟫ :=
      fun j => (intervalIntegral.integral_add_adjacent_intervals
        (hintj j a x ha hax.le (hxb.le.trans hb)) (hintj j x b (ha.trans hax.le) hxb.le hb)).symm
    have e0 : ∫ τ in a..b, ‖deriv γ τ‖ ^ 2 =
        (∫ τ in a..x, ‖deriv γ τ‖ ^ 2) + ∫ τ in x..b, ‖deriv γ τ‖ ^ 2 :=
      (intervalIntegral.integral_add_adjacent_intervals (hint a x ha hax.le (hxb.le.trans hb))
        (hint x b (ha.trans hax.le) hxb.le hb)).symm
    simp only [e1, e0]
    exact h₁.add h₂

/-- **Convergence in Milnor's metric controls the velocities in `L²`**: if `γⱼ → γ` in `Ω`, then
`∫₀¹ ‖γⱼ' − γ'‖² → 0` (not only the speeds: `‖γⱼ' − γ'‖² = ‖γⱼ'‖² − 2⟨γⱼ', γ'⟩ + ‖γ'‖²`, the
energies converge, and the velocities converge weakly). -/
theorem tendsto_integral_norm_deriv_sub_sq {ι : Type*} {l : Filter ι} {γs : ι → PathSp N p q}
    {γ : PathSp N p q} (h : Tendsto γs l (𝓝 γ)) :
    Tendsto (fun j => ∫ t in (0 : ℝ)..1, ‖deriv (γs j) t - deriv γ t‖ ^ 2) l (𝓝 0) := by
  have hE : Tendsto (fun j => energy (γs j : ℝ → V) 0 1) l (𝓝 (energy (γ : ℝ → V) 0 1)) :=
    ((continuous_energy le_rfl zero_le_one le_rfl).tendsto γ).comp h
  have hI := tendsto_integral_inner_deriv h
  have heq : ∀ j, ∫ t in (0 : ℝ)..1, ‖deriv (γs j) t - deriv γ t‖ ^ 2 =
      energy (γs j : ℝ → V) 0 1 - 2 * (∫ t in (0 : ℝ)..1, ⟪deriv (γs j) t, deriv γ t⟫) +
        energy (γ : ℝ → V) 0 1 := by
    intro j
    have i1 := (γs j).mem.1.intervalIntegrable_norm_deriv_sq
    have i2 : IntervalIntegrable (fun t => ⟪deriv (γs j) t, deriv γ t⟫) volume 0 1 :=
      intervalIntegrable_comp_deriv (γs j).mem.1 γ.mem.1 (Φ := fun z : V × V => ⟪z.1, z.2⟫)
        (by fun_prop) le_rfl zero_le_one le_rfl
    have i3 := γ.mem.1.intervalIntegrable_norm_deriv_sq
    simp only [norm_sub_sq_real]
    rw [intervalIntegral.integral_add (i1.sub (i2.const_mul 2)) i3,
      intervalIntegral.integral_sub i1 (i2.const_mul 2), intervalIntegral.integral_const_mul]
    rfl
  simp only [heq]
  have := (hE.sub (hI.const_mul 2)).add (tendsto_const_nhds (x := energy (γ : ℝ → V) 0 1))
  convert this using 2
  rw [energy]
  ring


variable (hN) in
include hN in
/-- **A criterion for convergence in Milnor's metric**: pointwise convergence on `[0, 1]` and
`L²` convergence of the velocities. -/
theorem tendsto_of_tendsto_apply_of_integral {ι : Type*} {l : Filter ι} {αs : ι → PathSp N p q}
    {α : PathSp N p q} (hpt : ∀ s ∈ Icc (0 : ℝ) 1, Tendsto (fun j => αs j s) l (𝓝 (α s)))
    (hL2 : Tendsto (fun j => ∫ t in (0 : ℝ)..1, ‖deriv (αs j) t - deriv α t‖ ^ 2) l (𝓝 0)) :
    Tendsto αs l (𝓝 α) := by
  set C := 2 * energy (α : ℝ → V) 0 1 + 2 with hC
  have hint : ∀ j, IntervalIntegrable (fun t => ‖deriv (αs j) t - deriv α t‖ ^ 2) volume 0 1 :=
    fun j => intervalIntegrable_comp_deriv (αs j).mem.1 α.mem.1
      (Φ := fun z : V × V => ‖z.1 - z.2‖ ^ 2) (by fun_prop) le_rfl zero_le_one le_rfl
  -- energy bound
  have hEj : ∀ᶠ j in l, energy (αs j : ℝ → V) 0 1 ≤ C := by
    filter_upwards [hL2.eventually (ge_mem_nhds one_pos)] with j hj
    have h1 : ∀ t, ‖deriv (αs j) t‖ ^ 2 ≤
        2 * ‖deriv α t‖ ^ 2 + 2 * ‖deriv (αs j) t - deriv α t‖ ^ 2 := fun t => by
      have := norm_add_le (deriv α t) (deriv (αs j) t - deriv α t)
      rw [add_sub_cancel] at this
      have h := pow_le_pow_left₀ (norm_nonneg _) this 2
      nlinarith [sq_nonneg (‖deriv α t‖ - ‖deriv (αs j) t - deriv α t‖)]
    have h2 := intervalIntegral.integral_mono_on zero_le_one
      (αs j).mem.1.intervalIntegrable_norm_deriv_sq
      ((α.mem.1.intervalIntegrable_norm_deriv_sq.const_mul 2).add ((hint j).const_mul 2))
      fun t _ => h1 t
    rw [intervalIntegral.integral_add (α.mem.1.intervalIntegrable_norm_deriv_sq.const_mul 2)
      ((hint j).const_mul 2), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at h2
    change energy (αs j : ℝ → V) 0 1 ≤ 2 * energy (α : ℝ → V) 0 1 + 2 * _ at h2
    rw [hC]
    linarith
  have hE : energy (α : ℝ → V) 0 1 ≤ C := by
    rw [hC]
    linarith [energy_nonneg_of_le (γ := (α : ℝ → V)) zero_le_one]
  rw [tendsto_iff_edist_tendsto_0, ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨r, -, hr, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hr' : 0 < r := ENNReal.ofReal_pos.1 hr
  have h1 := eventually_supDist_le_of_tendsto_apply hN (C := C) (l := l)
    (αs := fun j => (αs j : ℝ → V)) (hEj.mono fun j hj => ⟨(αs j).mem, hj⟩) α.mem hE hpt
    (e := r / 2) (by positivity)
  have h2 := hL2.eventually (gt_mem_nhds (show (0 : ℝ) < (r / 2) ^ 2 by positivity))
  filter_upwards [h1, h2] with j h1 h2
  have h3 : l2Dist (αs j : ℝ → V) α ≤ r / 2 := by
    rw [l2Dist]
    calc √(∫ τ in (0 : ℝ)..1, (speed (αs j : ℝ → V) τ - speed (α : ℝ → V) τ) ^ 2)
        ≤ √(∫ τ in (0 : ℝ)..1, ‖deriv (αs j) τ - deriv α τ‖ ^ 2) := by
          refine Real.sqrt_le_sqrt (intervalIntegral.integral_mono_on zero_le_one
            (intervalIntegrable_speed (αs j).mem α.mem (Φ := fun z => (z.1 - z.2) ^ 2)
              (by fun_prop) le_rfl zero_le_one le_rfl) (hint j) fun t _ => ?_)
          simp only [speed]
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (abs_norm_sub_norm_le _ _) 2
      _ ≤ √((r / 2) ^ 2) := Real.sqrt_le_sqrt h2.le
      _ = r / 2 := Real.sqrt_sq (by positivity)
  calc edist (αs j) α = supDist N (αs j : ℝ → V) α + ENNReal.ofReal (l2Dist (αs j : ℝ → V) α) :=
        edist_def _ _
    _ ≤ ENNReal.ofReal (r / 2) + ENNReal.ofReal (r / 2) :=
        add_le_add h1 (ENNReal.ofReal_le_ofReal h3)
    _ = ENNReal.ofReal r := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf
    _ ≤ ε := hrε.le

end PathSp

end Morse
