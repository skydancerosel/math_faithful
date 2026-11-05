import Mathlib

/-!
Milnor, *Morse Theory*, §2, pp. 10–11.

# Global flows of bounded Lipschitz vector fields (the first half of Lemma 2.4)

Milnor states (p. 10):

> **Lemma 2.4.** A smooth vector field on `M` which vanishes outside of a compact set `K ⊂ M`
> generates a unique 1-parameter group of diffeomorphisms of `M`.

and, for the proof, quotes the local theory of ordinary differential equations as "well known"
(p. 10: "such a differential equation, locally, has a unique solution which depends smoothly on
the initial conditions. (Compare Graves, 'The Theory of Functions of Real Variables,' p. 166.)").
He then covers `K` by finitely many neighbourhoods `U` on which solutions exist for `|t| < ε`,
lets `ε₀` be the smallest `ε`, observes that the solution through `q ∉ K` is constant, and
defines `φ_t` for `|t| ≥ ε₀` by iterating `φ_{ε₀/2}` (p. 11): "It is not difficult to verify that
`φ_t` is well defined, smooth, and satisfies the condition `φ_{t+s} = φ_t ∘ φ_s`."

This file proves the part of Lemma 2.4 that does not involve smoothness, for a vector field
`X : E → E` on a Banach space `E` (in the applications `E = ℝᴷ`) which is **bounded and globally
Lipschitz** (`Morse.IsBddLipschitz`); a `C¹` field vanishing outside a compact set is such a field
(`Morse.IsBddLipschitz.of_contDiff`). Smoothness of the flow is `Morse/Flow/Smooth.lean`.

## How the argument differs from Milnor's, and what his text leaves implicit

* **No iteration of `φ_{ε₀/2}`.** For a field bounded by `M`, every solution starting at `x`
  stays in the ball of radius `M a` about `x` for `|t| ≤ a`, so the Picard–Lindelöf theorem
  (Mathlib's `IsPicardLindelof`) gives a solution on `[-a, a]` for *every* `a`, with no
  shrinking of the time interval. Solutions on nested intervals agree by uniqueness, and
  `γ(t) = α_{|t| + 1}(t)` is a solution on all of `ℝ` (`exists_isIntegralCurve`). This replaces
  Milnor's decomposition `t = k (ε₀/2) + r`, whose non-uniqueness (e.g.
  `ε₀/4 = 0 · ε₀/2 + ε₀/4 = 1 · ε₀/2 - ε₀/4`) his "it is not difficult to verify that `φ_t` is
  well defined" passes over.
* **The group law** `φ_{s+t} = φ_s ∘ φ_t`, which Milnor says "is clear" for small times and "not
  difficult to verify" in general, is the uniqueness of integral curves applied to
  `s ↦ φ_{s+t}(x)` and `s ↦ φ_s(φ_t(x))` (`IsBddLipschitz.flow_add`).
* **Uniqueness of solutions** (Milnor: "has a unique solution") is Grönwall's inequality
  (Mathlib's `ODE_solution_unique_univ`). On a manifold it also needs the Hausdorff property,
  automatic here.
* **Where compactness of the support is used.** Only to make `X` bounded and globally Lipschitz.
  Milnor's remark (p. 11) that the hypothesis cannot be omitted (`X = d/dt` on `(0, 1)`) shows
  that some such global condition is needed.
* **Continuity.** The flow is Lipschitz in `x` with constant `e^{K|t|}` (Grönwall,
  `IsBddLipschitz.dist_flow_le`) and `M`-Lipschitz in `t`, hence jointly continuous, and each
  `φ_t` is a homeomorphism with inverse `φ_{-t}` (`IsBddLipschitz.flowHomeomorph`).
* **Zeros of `X` are fixed** (Milnor: "Setting `φ_t(q) = q` for `q ∉ K`"): the constant curve is
  a solution (`IsBddLipschitz.flow_of_eq_zero`).
* **Invariant sets** (not in Milnor; meant for submanifolds `M ⊆ ℝᴷ`): a closed set `S`
  through each point of which there is a local integral curve staying in `S` is invariant under
  the flow (`IsBddLipschitz.flow_mem`).

## Main definitions and results

* `Morse.IsBddLipschitz X`: `X` is bounded and globally Lipschitz.
* `Morse.flow X t x`: the value at time `t` of the integral curve of `X` through `x` at time `0`
  (defined for every `X`, with a junk value when no global integral curve exists).
* `Morse.IsBddLipschitz.isIntegralCurve_flow`, `flow_zero`, `flow_add`, `eq_flow` (every integral
  curve is a flow line), `dist_flow_le`, `continuous_flow`, `flowHomeomorph`, `flow_of_eq_zero`,
  `flow_mem`, `flow_smul` (`φ^{cX}_t = φ^X_{ct}`), `flow_nat_mul` (`φ_{nt} = (φ_t)ⁿ`).
-/

open Set Filter Topology Metric Function
open scoped NNReal

noncomputable section

namespace Morse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The standing hypothesis -/

/-- The hypothesis under which the global flow is constructed: the vector field `X : E → E` is
bounded and globally Lipschitz. -/
structure IsBddLipschitz (X : E → E) : Prop where
  bounded : ∃ M : ℝ, ∀ x, ‖X x‖ ≤ M
  lipschitz : ∃ K : ℝ≥0, LipschitzWith K X

/-- A `C¹` vector field vanishing outside a compact set (Milnor's hypothesis in Lemma 2.4) is
bounded and globally Lipschitz: `X` and `dX` are continuous with compact support, hence bounded,
and a bound on `dX` is a Lipschitz constant by the mean value inequality. -/
theorem IsBddLipschitz.of_contDiff {X : E → E} (hX : ContDiff ℝ 1 X) (hs : HasCompactSupport X) :
    IsBddLipschitz X := by
  refine ⟨hs.exists_bound_of_continuous hX.continuous, ?_⟩
  obtain ⟨C, hC⟩ := (hs.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (hX.continuous_fderiv one_ne_zero)
  refine ⟨C.toNNReal, lipschitzWith_of_nnnorm_fderiv_le (hX.differentiable one_ne_zero)
    fun x => ?_⟩
  rw [← NNReal.coe_le_coe, coe_nnnorm]
  exact (hC x).trans (Real.le_coe_toNNReal C)

theorem IsBddLipschitz.smul {X : E → E} (hX : IsBddLipschitz X) (c : ℝ) :
    IsBddLipschitz (c • X) := by
  obtain ⟨M, hM⟩ := hX.bounded
  obtain ⟨K, hK⟩ := hX.lipschitz
  refine ⟨⟨|c| * M, fun x => ?_⟩, ⟨‖c‖₊ * K, (lipschitzWith_smul c).comp hK⟩⟩
  rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hM x) (abs_nonneg c)

/-! ### Existence and uniqueness of integral curves -/

/-- Uniqueness of integral curves of a Lipschitz field on an open interval (Grönwall). -/
theorem eqOn_Ioo_of_hasDerivAt {X : E → E} {K : ℝ≥0} (hK : LipschitzWith K X) {f g : ℝ → E}
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) (hf : ∀ t ∈ Ioo a b, HasDerivAt f (X (f t)) t)
    (hg : ∀ t ∈ Ioo a b, HasDerivAt g (X (g t)) t) (h : f t₀ = g t₀) : EqOn f g (Ioo a b) :=
  ODE_solution_unique_of_mem_Ioo (v := fun _ => X) (s := fun _ => univ)
    (fun _ _ => hK.lipschitzOnWith) ht₀ (fun t ht => ⟨hf t ht, mem_univ _⟩)
    (fun t ht => ⟨hg t ht, mem_univ _⟩) h

/-- Two integral curves of a bounded Lipschitz field defined on all of `ℝ` which agree at one
time agree everywhere. -/
theorem IsBddLipschitz.isIntegralCurve_eq {X : E → E} (hX : IsBddLipschitz X) {γ δ : ℝ → E}
    (hγ : IsIntegralCurve γ (fun _ => X)) (hδ : IsIntegralCurve δ (fun _ => X)) {t₀ : ℝ}
    (h : γ t₀ = δ t₀) : γ = δ := by
  obtain ⟨K, hK⟩ := hX.lipschitz
  exact ODE_solution_unique_univ (v := fun _ => X) (s := fun _ => univ) (K := K)
    (fun _ => hK.lipschitzOnWith) (fun t => ⟨hγ t, mem_univ _⟩) (fun t => ⟨hδ t, mem_univ _⟩) h

variable [CompleteSpace E]

/-- Picard–Lindelöf on `(-a, a)`: since `‖X‖ ≤ M`, a solution starting at `x` cannot leave the
ball of radius `M a` before time `a`, so no shrinking of the time interval is needed. -/
theorem IsBddLipschitz.exists_local {X : E → E} (hX : IsBddLipschitz X) (x : E) (a : ℝ) :
    ∃ α : ℝ → E, α 0 = x ∧ ∀ t ∈ Ioo (-a) a, HasDerivAt α (X (α t)) t := by
  rcases le_or_gt a 0 with ha | ha
  · exact ⟨fun _ => x, rfl, fun t ht => absurd (ht.1.trans ht.2) (by linarith)⟩
  obtain ⟨M, hM⟩ := hX.bounded
  obtain ⟨K, hK⟩ := hX.lipschitz
  have hL : ∀ y, ‖X y‖ ≤ M.toNNReal := fun y => (hM y).trans (Real.le_coe_toNNReal M)
  have h0 : (0 : ℝ) ∈ Icc (-a) a := ⟨by linarith, ha.le⟩
  have hpl : IsPicardLindelof (fun _ => X) (⟨0, h0⟩ : Icc (-a) a) x
      (M.toNNReal * a.toNNReal) 0 M.toNNReal K :=
    IsPicardLindelof.of_time_independent (fun y _ => hL y) hK.lipschitzOnWith (by
      simp only [sub_zero, zero_sub, neg_neg, max_self, NNReal.coe_mul, NNReal.coe_zero,
        Real.coe_toNNReal a ha.le, le_refl])
  obtain ⟨α, hα0, hα⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, hα0, fun t ht => (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)⟩

/-- **Global existence.** A bounded Lipschitz field has an integral curve through every point,
defined for all times. -/
theorem IsBddLipschitz.exists_isIntegralCurve {X : E → E} (hX : IsBddLipschitz X) (x : E) :
    ∃ γ : ℝ → E, γ 0 = x ∧ IsIntegralCurve γ (fun _ => X) := by
  obtain ⟨K, hK⟩ := hX.lipschitz
  choose α hα0 hα using hX.exists_local x
  -- solutions on nested intervals agree
  have key : ∀ a b t : ℝ, |t| < a → |t| < b → α a t = α b t := by
    intro a b t ha hb
    have hc : |t| < min a b := lt_min ha hb
    have hc0 : 0 < min a b := (abs_nonneg t).trans_lt hc
    refine eqOn_Ioo_of_hasDerivAt hK (t₀ := 0) ⟨by linarith, hc0⟩
      (fun s hs => hα a s ⟨by linarith [hs.1, min_le_left a b], hs.2.trans_le (min_le_left a b)⟩)
      (fun s hs => hα b s ⟨by linarith [hs.1, min_le_right a b],
        hs.2.trans_le (min_le_right a b)⟩)
      (by rw [hα0, hα0]) (abs_lt.1 hc)
  refine ⟨fun t => α (|t| + 1) t, hα0 _, fun t => ?_⟩
  have ht : t ∈ Ioo (-(|t| + 1)) (|t| + 1) := abs_lt.1 (lt_add_one _)
  refine (hα (|t| + 1) t ht).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact key _ _ s (lt_add_one _) (abs_lt.2 hs)

/-! ### The flow -/

open Classical in
/-- The flow of the vector field `X`: `flow X t x` is the value at time `t` of the integral curve
of `X` through `x` at time `0`. If integral curves through `x` defined on all of `ℝ` exist, one of
them is chosen; when `X` is bounded and Lipschitz there is exactly one
(`IsBddLipschitz.exists_isIntegralCurve`, `IsBddLipschitz.isIntegralCurve_eq`). Otherwise
`flow X t x = x`, a junk value. -/
def flow (X : E → E) (t : ℝ) (x : E) : E :=
  if h : ∃ γ : ℝ → E, γ 0 = x ∧ IsIntegralCurve γ (fun _ => X) then h.choose t else x

variable {X : E → E}

theorem IsBddLipschitz.flow_spec (hX : IsBddLipschitz X) (x : E) :
    flow X 0 x = x ∧ IsIntegralCurve (fun t => flow X t x) (fun _ => X) := by
  have h := hX.exists_isIntegralCurve x
  simp only [flow, dif_pos h]
  exact h.choose_spec

@[simp]
theorem IsBddLipschitz.flow_zero (hX : IsBddLipschitz X) (x : E) : flow X 0 x = x :=
  (hX.flow_spec x).1

theorem IsBddLipschitz.flow_zero' (hX : IsBddLipschitz X) : flow X 0 = id :=
  funext hX.flow_zero

/-- `t ↦ flow X t x` is an integral curve of `X`. -/
theorem IsBddLipschitz.isIntegralCurve_flow (hX : IsBddLipschitz X) (x : E) :
    IsIntegralCurve (fun t => flow X t x) (fun _ => X) :=
  (hX.flow_spec x).2

theorem IsBddLipschitz.hasDerivAt_flow (hX : IsBddLipschitz X) (t : ℝ) (x : E) :
    HasDerivAt (fun t => flow X t x) (X (flow X t x)) t :=
  hX.isIntegralCurve_flow x t

/-- Every integral curve of `X` is a flow line: `γ t = φ_{t - t₀}(γ t₀)`. -/
theorem IsBddLipschitz.eq_flow (hX : IsBddLipschitz X) {γ : ℝ → E}
    (hγ : IsIntegralCurve γ (fun _ => X)) (t₀ t : ℝ) : γ t = flow X (t - t₀) (γ t₀) := by
  have h1 : IsIntegralCurve (fun t => flow X (t - t₀) (γ t₀)) (fun _ => X) := fun s =>
    (hX.hasDerivAt_flow (s - t₀) (γ t₀)).comp_sub_const s t₀
  exact congrFun (hX.isIntegralCurve_eq hγ h1 (t₀ := t₀) (by simp [hX.flow_zero])) t

/-- **The group law** `φ_{s+t} = φ_s ∘ φ_t`. -/
theorem IsBddLipschitz.flow_add (hX : IsBddLipschitz X) (s t : ℝ) (x : E) :
    flow X (s + t) x = flow X s (flow X t x) := by
  have := hX.eq_flow (hX.isIntegralCurve_flow x) t (s + t)
  rwa [add_sub_cancel_right] at this

theorem IsBddLipschitz.flow_comp (hX : IsBddLipschitz X) (s t : ℝ) :
    flow X (s + t) = flow X s ∘ flow X t :=
  funext (hX.flow_add s t)

@[simp]
theorem IsBddLipschitz.flow_neg_flow (hX : IsBddLipschitz X) (t : ℝ) (x : E) :
    flow X (-t) (flow X t x) = x := by
  rw [← hX.flow_add, neg_add_cancel, hX.flow_zero]

@[simp]
theorem IsBddLipschitz.flow_flow_neg (hX : IsBddLipschitz X) (t : ℝ) (x : E) :
    flow X t (flow X (-t) x) = x := by
  rw [← hX.flow_add, add_neg_cancel, hX.flow_zero]

/-- `φ_{n t} = (φ_t)ⁿ`. -/
theorem IsBddLipschitz.flow_nat_mul (hX : IsBddLipschitz X) (n : ℕ) (t : ℝ) :
    flow X (n * t) = (flow X t)^[n] := by
  induction n with
  | zero => ext x; simp [hX.flow_zero]
  | succ n ih =>
    ext x
    rw [Function.iterate_succ_apply', ← ih, ← hX.flow_add]
    congr 1
    push_cast
    ring

/-- **Rescaling time.** The flow of `c • X` is the flow of `X` run at speed `c`. -/
theorem IsBddLipschitz.flow_smul (hX : IsBddLipschitz X) (c t : ℝ) (x : E) :
    flow (c • X) t x = flow X (c * t) x := by
  have h : IsIntegralCurve (fun s => flow X (c * s) x) (fun _ => c • X) := fun s => by
    have := (hX.hasDerivAt_flow (c * s) x).scomp s ((hasDerivAt_id s).const_mul c)
    simpa [Function.comp_def] using this
  have := (hX.smul c).eq_flow h 0 t
  simpa [hX.flow_zero] using this.symm

/-- **Zeros of `X` are fixed points of the flow.** -/
theorem IsBddLipschitz.flow_of_eq_zero (hX : IsBddLipschitz X) {x : E} (hx : X x = 0) (t : ℝ) :
    flow X t x = x := by
  have := hX.eq_flow (γ := fun _ => x) (isIntegralCurve_const fun _ => hx) 0 t
  simpa using this.symm

/-- Milnor's "`φ_t(q) = q` for `q ∉ K`". -/
theorem IsBddLipschitz.flow_of_notMem_tsupport (hX : IsBddLipschitz X) {x : E}
    (hx : x ∉ tsupport X) (t : ℝ) : flow X t x = x :=
  hX.flow_of_eq_zero (image_eq_zero_of_notMem_tsupport hx) t

/-! ### Continuity -/

omit [CompleteSpace E] in
/-- Grönwall: two integral curves of a `K`-Lipschitz field separate at most like `e^{K t}`. -/
theorem dist_le_of_hasDerivAt {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V) {f g : ℝ → E}
    (hf : ∀ t, HasDerivAt f (V (f t)) t) (hg : ∀ t, HasDerivAt g (V (g t)) t) {t : ℝ}
    (ht : 0 ≤ t) : dist (f t) (g t) ≤ dist (f 0) (g 0) * Real.exp (K * t) := by
  have := dist_le_of_trajectories_ODE (v := fun _ => V) (K := K) (a := 0) (b := t)
    (fun _ => hV) (HasDerivAt.continuousOn fun s _ => hf s) (fun s _ => (hf s).hasDerivWithinAt)
    (HasDerivAt.continuousOn fun s _ => hg s) (fun s _ => (hg s).hasDerivWithinAt) le_rfl t
    ⟨ht, le_rfl⟩
  simpa using this

/-- **Lipschitz dependence on the initial point**, with constant `e^{K|t|}`. -/
theorem IsBddLipschitz.dist_flow_le (hX : IsBddLipschitz X) {K : ℝ≥0} (hK : LipschitzWith K X)
    (t : ℝ) (x y : E) : dist (flow X t x) (flow X t y) ≤ dist x y * Real.exp (K * |t|) := by
  rcases le_total 0 t with ht | ht
  · have := dist_le_of_hasDerivAt hK (hX.isIntegralCurve_flow x) (hX.isIntegralCurve_flow y) ht
    simpa [hX.flow_zero, abs_of_nonneg ht] using this
  · -- run the flow backwards: `s ↦ φ_{-s}(x)` is an integral curve of `-X`
    have hrev : ∀ z s, HasDerivAt (fun s => flow X (-s) z) ((-X) (flow X (-s) z)) s := by
      intro z s
      have := (hX.hasDerivAt_flow (-s) z).scomp s (hasDerivAt_neg s)
      simpa [Function.comp_def] using this
    have := dist_le_of_hasDerivAt hK.neg (hrev x) (hrev y) (t := -t) (neg_nonneg.2 ht)
    simpa [hX.flow_zero, abs_of_nonpos ht] using this

theorem IsBddLipschitz.lipschitzWith_flow (hX : IsBddLipschitz X) {K : ℝ≥0}
    (hK : LipschitzWith K X) (t : ℝ) :
    LipschitzWith (Real.exp (K * |t|)).toNNReal (flow X t) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [Real.coe_toNNReal _ (Real.exp_pos _).le, mul_comm]
    exact hX.dist_flow_le hK t x y

/-- The flow lines are `M`-Lipschitz in time when `‖X‖ ≤ M`. -/
theorem IsBddLipschitz.dist_flow_flow_le (hX : IsBddLipschitz X) {M : ℝ} (hM : ∀ x, ‖X x‖ ≤ M)
    (s t : ℝ) (x : E) : dist (flow X s x) (flow X t x) ≤ M * |s - t| := by
  have := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t => flow X t x) (f' := fun t => X (flow X t x))
    (fun r _ => (hX.hasDerivAt_flow r x).hasDerivWithinAt) (fun r _ => hM _) (mem_univ t)
    (mem_univ s)
  rwa [dist_eq_norm, ← Real.norm_eq_abs]

/-- **Joint continuity** of `(t, x) ↦ φ_t(x)`. -/
theorem IsBddLipschitz.continuous_flow (hX : IsBddLipschitz X) :
    Continuous (fun p : ℝ × E => flow X p.1 p.2) := by
  obtain ⟨M, hM⟩ := hX.bounded
  obtain ⟨K, hK⟩ := hX.lipschitz
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine continuous_iff_continuousAt.2 fun p => ?_
  refine continuousAt_of_locally_lipschitz one_pos (Real.exp (K * (|p.1| + 1)) + M)
    fun q hq => ?_
  have h1 : dist q.2 p.2 ≤ dist q p := by rw [Prod.dist_eq]; exact le_max_right _ _
  have h2 : dist q.1 p.1 ≤ dist q p := by rw [Prod.dist_eq]; exact le_max_left _ _
  have h3 : |q.1| ≤ |p.1| + 1 := by
    have := abs_sub_abs_le_abs_sub q.1 p.1
    rw [← Real.dist_eq] at this
    linarith
  have h4 : Real.exp (K * |q.1|) ≤ Real.exp (K * (|p.1| + 1)) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h3 K.2)
  calc dist (flow X q.1 q.2) (flow X p.1 p.2)
      ≤ dist (flow X q.1 q.2) (flow X q.1 p.2) + dist (flow X q.1 p.2) (flow X p.1 p.2) :=
        dist_triangle _ _ _
    _ ≤ dist q.2 p.2 * Real.exp (K * |q.1|) + M * |q.1 - p.1| :=
        add_le_add (hX.dist_flow_le hK _ _ _) (hX.dist_flow_flow_le hM _ _ _)
    _ ≤ dist q p * Real.exp (K * (|p.1| + 1)) + M * dist q p := by
        rw [← Real.dist_eq]
        gcongr
    _ = (Real.exp (K * (|p.1| + 1)) + M) * dist q p := by ring

theorem IsBddLipschitz.continuous_flow_right (hX : IsBddLipschitz X) (t : ℝ) :
    Continuous (flow X t) :=
  hX.continuous_flow.comp (continuous_const.prodMk continuous_id)

theorem IsBddLipschitz.continuous_flow_left (hX : IsBddLipschitz X) (x : E) :
    Continuous (fun t => flow X t x) :=
  hX.continuous_flow.comp (continuous_id.prodMk continuous_const)

/-- Each `φ_t` is a homeomorphism of `E`, with inverse `φ_{-t}`. -/
def IsBddLipschitz.flowHomeomorph (hX : IsBddLipschitz X) (t : ℝ) : E ≃ₜ E where
  toFun := flow X t
  invFun := flow X (-t)
  left_inv := hX.flow_neg_flow t
  right_inv := hX.flow_flow_neg t
  continuous_toFun := hX.continuous_flow_right t
  continuous_invFun := hX.continuous_flow_right (-t)

@[simp]
theorem IsBddLipschitz.coe_flowHomeomorph (hX : IsBddLipschitz X) (t : ℝ) :
    ⇑(hX.flowHomeomorph t) = flow X t :=
  rfl

@[simp]
theorem IsBddLipschitz.coe_flowHomeomorph_symm (hX : IsBddLipschitz X) (t : ℝ) :
    ⇑(hX.flowHomeomorph t).symm = flow X (-t) :=
  rfl

/-! ### Invariant closed sets -/

/-- A closed set which is invariant under the flow for small times is invariant for all times:
the set of times `t` with `φ_t(x) ∈ S` is closed (continuity) and open (the group law), hence
all of `ℝ`. -/
theorem IsBddLipschitz.flow_mem_of_eventually (hX : IsBddLipschitz X) {S : Set E}
    (hS : IsClosed S) (hloc : ∀ y ∈ S, ∀ᶠ s in 𝓝 0, flow X s y ∈ S) {x : E} (hx : x ∈ S)
    (t : ℝ) : flow X t x ∈ S := by
  let T : Set ℝ := {t | flow X t x ∈ S}
  have hclosed : IsClosed T := hS.preimage (hX.continuous_flow_left x)
  have hopen : IsOpen T := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have hsub : Tendsto (fun u => u - t) (𝓝 t) (𝓝 0) := by
      simpa using (tendsto_id.sub_const t : Tendsto (fun u : ℝ => u - t) (𝓝 t) (𝓝 (t - t)))
    filter_upwards [hsub.eventually (hloc _ ht)] with u hu
    change flow X u x ∈ S
    rwa [show flow X u x = flow X (u - t) (flow X t x) by rw [← hX.flow_add, sub_add_cancel]]
  have : T = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨0, by simp [T, hX.flow_zero, hx]⟩
  rw [Set.eq_univ_iff_forall] at this
  exact this t

/-- **Invariance criterion.** If `S` is closed and through every point of `S` there is a local
integral curve of `X` which stays in `S`, then every flow line starting in `S` stays in `S`. -/
theorem IsBddLipschitz.flow_mem (hX : IsBddLipschitz X) {S : Set E} (hS : IsClosed S)
    (hloc : ∀ y ∈ S, ∃ ε > 0, ∃ γ : ℝ → E, γ 0 = y ∧
      ∀ t ∈ Ioo (-ε) ε, HasDerivAt γ (X (γ t)) t ∧ γ t ∈ S)
    {x : E} (hx : x ∈ S) (t : ℝ) : flow X t x ∈ S := by
  refine hX.flow_mem_of_eventually hS (fun y hy => ?_) hx t
  obtain ⟨ε, hε, γ, hγ0, hγ⟩ := hloc y hy
  obtain ⟨K, hK⟩ := hX.lipschitz
  have hε' : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.2 hε, hε⟩
  have heq : EqOn (fun s => flow X s y) γ (Ioo (-ε) ε) :=
    eqOn_Ioo_of_hasDerivAt hK hε' (fun s _ => hX.hasDerivAt_flow s y)
      (fun s hs => (hγ s hs).1) (by simp [hX.flow_zero, hγ0])
  filter_upwards [Ioo_mem_nhds hε'.1 hε'.2] with s hs
  rw [show flow X s y = γ s from heq hs]
  exact (hγ s hs).2

end Morse
