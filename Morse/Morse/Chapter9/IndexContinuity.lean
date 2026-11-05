import Morse.Chapter9.IndexReduction

/-!
Milnor, *Morse Theory*, §15, pp. 85–86: the quadratic forms `H_τ` on the fixed space `Σ`, their
continuity in `τ`, Assertion (3) (`λ` is continuous from the left) and the first half of
Assertion (4) (`λ(τ + ε) ≤ λ(τ) + ν`), for a submanifold `N ⊆ ℝᴷ` with the induced metric.

# The forms `H_τ`

## Milnor's text, paraphrased

(p. 86) Choose the subdivision so that `t_i < τ < t_{i+1}`.  Then `λ(τ)` is the index of a
quadratic form `H_τ` on the space of broken Jacobi fields along `γ_τ` for `0 < t₁ < ⋯ < t_i < τ`,
which is isomorphic to `Σ = TM_{γ(t₁)} ⊕ ⋯ ⊕ TM_{γ(t_i)}`, independent of `τ`.  "Evidently the
quadratic form `H_τ` on `Σ` varies continuously with `τ`."  **Assertion (3)**: `H_τ` is negative
definite on a subspace `𝒱` of dimension `λ(τ)`, hence so is `H_τ'` for `τ'` close to `τ`, so
`λ(τ') ≥ λ(τ)`; with Assertion (1), `λ(τ − ε) = λ(τ)`.  **Assertion (4), first half**: `H_τ` is
positive definite on a subspace of dimension `ni − λ(τ) − ν`, hence so is `H_τ'` for `τ'` near
`τ`, and `λ(τ') ≤ dim Σ − (ni − λ(τ) − ν) = λ(τ) + ν`.

## In the embedded setting

* `Morse.Hform hc B τ`: Milnor's `H_τ`, the Hessian on the broken Jacobi fields along `γ|[0, τ]`
  transported to `Σ = Morse.nodeSpace hN γ B` by `Morse.nodeEquiv`; it is defined for the `τ` in
  `Morse.validFor hc B` (those for which `B` is a fine subdivision of `[0, τ]`), `0` otherwise.
  `Morse.formIndex_Hform`: its index is `λ(τ)`; `Morse.finrank_ker_Hform`: its nullity is `ν(τ)`.
* **Lemma 15.C of the exposition** ("evidently ... varies continuously"):
  `Morse.continuousWithinAt_Hform`.  By the second variation formula
  `H_τ(x, y) = −2 Σ_b ⟨y_b, Δ_b DW_x/dt⟩`, and the broken Jacobi field `W_x` does not depend on
  `τ` on `[0, t_i]`; the only dependence is through `DY^τ/dt(t_i)`, where `Y^τ` is the Jacobi field
  with `Y^τ(t_i) = x_i`, `Y^τ(τ) = 0`.  This is the solution `z` of the linear system
  `L(τ) z = c(τ)`, `L(τ) z = J_{(0, z)}(τ)`, `c(τ) = −J_{(x_i, 0)}(τ)` (Jacobi fields with initial
  data at `t_i`), with `L(τ)` injective because `t_i` and `τ` are not conjugate (they are closer
  than `h₀`), so `z` is continuous (`Morse.continuousWithinAt_of_injective`, a perturbation
  argument replacing Cramer's rule).
* **Assertion (3)**: `Morse.assertion_3`; **Assertion (4), `≤`**: `Morse.assertion_4_le`.

## What Milnor leaves implicit

* "Evidently `H_τ` varies continuously with `τ`": this needs the non-conjugacy of `t_i` and `τ`
  (otherwise `Y^τ` is not defined), the linear dependence of Jacobi fields on their initial
  data, and the continuity of the solution of an injective linear system.
* The positive definite subspace of dimension `ni − λ(τ) − ν` comes from Sylvester's law of
  inertia together with `nullity H_τ = ν(τ)` (Lemma 15.4 and Theorem 14.1 for `γ_τ`).
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N} {γ : ℝ → V}
  (hc : IsSmoothCurveIn hN γ)

/-! ### Continuity of the solution of an injective linear system -/

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- If `L(τ)z(τ) = c(τ)` with `L`, `c` continuous at `τ₀` and `L(τ₀)` injective (on a finite
dimensional space), then `z` is continuous at `τ₀`. -/
theorem continuousWithinAt_of_injective {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {L : ℝ → E →L[ℝ] F}
    {c : ℝ → F} {z : ℝ → E} {s : Set ℝ} {τ₀ : ℝ} (hL : ContinuousAt L τ₀)
    (hinj : Injective (L τ₀)) (hc : ContinuousAt c τ₀) (hz : ∀ τ ∈ s, L τ (z τ) = c τ)
    (hτ₀ : τ₀ ∈ s) : ContinuousWithinAt z s τ₀ := by
  obtain ⟨K, hK, hanti⟩ := LinearMap.exists_antilipschitzWith (L τ₀ : E →ₗ[ℝ] F)
    (LinearMap.ker_eq_bot.2 hinj)
  have hKpos : (0 : ℝ) < K := hK
  have hbound : ∀ v, ‖v‖ ≤ K * ‖L τ₀ v‖ := fun v => by
    have := hanti.le_mul_dist v 0
    simpa [dist_eq_norm] using this
  -- near `τ₀`, `‖v‖ ≤ 2K ‖L(τ) v‖`
  have hnear : ∀ᶠ τ in 𝓝 τ₀, ‖L τ - L τ₀‖ < 1 / (2 * K) :=
    (hL.sub continuousAt_const).norm.eventually
      (gt_mem_nhds (by simp only [Pi.sub_apply, sub_self, norm_zero]; positivity))
  have hbound' : ∀ᶠ τ in 𝓝 τ₀, ∀ v, ‖v‖ ≤ 2 * K * ‖L τ v‖ := by
    filter_upwards [hnear] with τ hτ v
    have h1 : ‖L τ₀ v‖ ≤ ‖L τ v‖ + ‖L τ - L τ₀‖ * ‖v‖ := by
      calc ‖L τ₀ v‖ = ‖L τ v - (L τ - L τ₀) v‖ := by simp
        _ ≤ ‖L τ v‖ + ‖(L τ - L τ₀) v‖ := norm_sub_le _ _
        _ ≤ ‖L τ v‖ + ‖L τ - L τ₀‖ * ‖v‖ := by gcongr; exact (L τ - L τ₀).le_opNorm v
    have h2 : K * (‖L τ - L τ₀‖ * ‖v‖) ≤ ‖v‖ / 2 := by
      have : K * ‖L τ - L τ₀‖ ≤ 1 / 2 := by
        rw [lt_div_iff₀ (by positivity)] at hτ
        linarith
      nlinarith [norm_nonneg v]
    nlinarith [hbound v, norm_nonneg (L τ v)]
  -- the defect `c(τ) − L(τ)z(τ₀)` tends to `0`
  have hdef : Tendsto (fun τ => c τ - L τ (z τ₀)) (𝓝 τ₀) (𝓝 0) := by
    have h1 : Tendsto (fun τ => c τ - L τ (z τ₀)) (𝓝 τ₀) (𝓝 (c τ₀ - L τ₀ (z τ₀))) :=
      hc.tendsto.sub (hL.clm_apply
        (continuousAt_const : ContinuousAt (fun _ : ℝ => z τ₀) τ₀)).tendsto
    rwa [hz τ₀ hτ₀, sub_self] at h1
  have hlim : Tendsto (fun τ => 2 * (K : ℝ) * ‖c τ - L τ (z τ₀)‖) (𝓝[s] τ₀) (𝓝 0) := by
    have := (hdef.norm.const_mul (2 * (K : ℝ))).mono_left (nhdsWithin_le_nhds (s := s))
    simpa using this
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [nhdsWithin_le_nhds hbound', self_mem_nhdsWithin] with τ hτ hτs
  have := hτ (z τ - z τ₀)
  rwa [map_sub, hz τ hτs] at this

/-! ### The forms `H_τ` on `Σ` -/

variable (hN γ) in
/-- The parameters `τ ∈ (0, 1]` for which `B` is a fine subdivision of `[0, τ]`. -/
def validFor (hc : IsSmoothCurveIn hN γ) (B : Finset ℝ) : Set ℝ :=
  {τ | IsFine hN γ hc B τ ∧ 0 < τ ∧ τ ≤ 1}

open Classical in
/-- The broken Jacobi field along `γ|[0, τ]` with values `x` at the division points (`0` if `τ`
is not valid). -/
def brokenOf (B : Finset ℝ) (τ : ℝ) (x : nodeSpace hN γ B) : pathTangent hN γ :=
  if h : τ ∈ validFor hN γ hc B then
    ((nodeEquiv hc h.2.1 h.2.2 h.1).symm x : pathTangent hN γ) else 0

theorem brokenOf_mem {B : Finset ℝ} {τ : ℝ} (h : τ ∈ validFor hN γ hc B) (x : nodeSpace hN γ B) :
    brokenOf hc B τ x ∈ brokenSpace hc B τ := by
  rw [brokenOf, dif_pos h]
  exact ((nodeEquiv hc h.2.1 h.2.2 h.1).symm x).2

theorem brokenOf_apply_node {B : Finset ℝ} {τ : ℝ} (h : τ ∈ validFor hN γ hc B)
    (x : nodeSpace hN γ B) (b : B) :
    ((brokenOf hc B τ x : pathTangent hN γ) : ℝ → V) b = (x : B → V) b := by
  rw [brokenOf, dif_pos h]
  have := (nodeEquiv hc h.2.1 h.2.2 h.1).apply_symm_apply x
  exact congrFun (congrArg Subtype.val this) b

open Classical in
variable (hN γ) in
/-- **Milnor's `H_τ`** (p. 86): the Hessian on the broken Jacobi fields along `γ|[0, τ]`, read on
`Σ` through their values at the division points (`0` if `τ` is not valid). -/
def Hform (hc : IsSmoothCurveIn hN γ) (B : Finset ℝ) (τ : ℝ) :
    LinearMap.BilinForm ℝ (nodeSpace hN γ B) :=
  if h : τ ∈ validFor hN γ hc B then
    ((energyHessian hN hc.mem_pathSpace).restrict (brokenSpace hc B τ)).compl₁₂
      (nodeEquiv hc h.2.1 h.2.2 h.1).symm.toLinearMap
      (nodeEquiv hc h.2.1 h.2.2 h.1).symm.toLinearMap
  else 0

theorem Hform_apply {B : Finset ℝ} {τ : ℝ} (h : τ ∈ validFor hN γ hc B)
    (x y : nodeSpace hN γ B) :
    Hform hN γ hc B τ x y = energyHessian hN hc.mem_pathSpace (brokenOf hc B τ x)
      (brokenOf hc B τ y) := by
  rw [Hform, dif_pos h, brokenOf, brokenOf, dif_pos h, dif_pos h]
  rfl

theorem Hform_isSymm (B : Finset ℝ) (τ : ℝ) : (Hform hN γ hc B τ).IsSymm := by
  rw [LinearMap.BilinForm.isSymm_def]
  intro x y
  by_cases h : τ ∈ validFor hN γ hc B
  · rw [Hform_apply hc h, Hform_apply hc h]
    exact LinearMap.BilinForm.isSymm_def.1 (energyHessian_isSymm hN hc.mem_pathSpace) _ _
  · simp [Hform, dif_neg h]

/-- **The index of `H_τ` is `λ(τ)`** (Lemma 15.4). -/
theorem formIndex_Hform {B : Finset ℝ} {τ : ℝ} (h : τ ∈ validFor hN γ hc B) :
    formIndex (Hform hN γ hc B τ) = indexUpTo hN γ hc τ := by
  rw [indexUpTo, lemma_15_4 hc h.2.1 h.2.2 h.1]
  refine formIndex_eq_of_equiv (nodeEquiv hc h.2.1 h.2.2 h.1).symm fun x y => ?_
  rw [Hform, dif_pos h]
  rfl

/-- **The nullity of `H_τ` is `ν(τ)`**, the multiplicity of `τ` as a conjugate point of `0`. -/
theorem finrank_ker_Hform {B : Finset ℝ} {τ : ℝ} (h : τ ∈ validFor hN γ hc B) :
    finrank ℝ (LinearMap.ker (Hform hN γ hc B τ)) = conjMultiplicity hN γ hc 0 τ := by
  rw [← finrank_ker_broken hc h.2.1 h.2.2 h.1]
  set e := (nodeEquiv hc h.2.1 h.2.2 h.1).symm
  set E' := (energyHessian hN hc.mem_pathSpace).restrict (brokenSpace hc B τ)
  have happ : ∀ x y, Hform hN γ hc B τ x y = E' (e x) (e y) := fun x y => by
    rw [Hform, dif_pos h]; rfl
  have hker : LinearMap.ker (Hform hN γ hc B τ) = (LinearMap.ker E').comap e.toLinearMap := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_comap, LinearMap.mem_ker]
    constructor
    · intro hx
      ext Y
      have := congrArg (fun f => f (e.symm Y)) hx
      simp only [LinearMap.zero_apply, happ, LinearEquiv.apply_symm_apply] at this
      exact this
    · intro hx
      ext y
      rw [happ]
      change E' (e x) (e y) = 0
      rw [show E' (e x) = 0 from hx, LinearMap.zero_apply]
  rw [hker, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]

/-! ### Lemma 15.C: `H_τ` varies continuously with `τ` -/

/-- A fine subdivision of `[0, τ₀]` is fine for every `τ` after its last division point, within
`h₀` of it. -/
theorem isFine_of_isFine {B : Finset ℝ} {τ₀ τ : ℝ} (hB : IsFine hN γ hc B τ₀)
    (hm : ∀ b ∈ B, b < τ) (_hτ : 0 < τ) (hlast : ∀ b ∈ insert 0 B, (∀ c ∈ B, c ≤ b) →
      τ - b ≤ fineMesh hN γ hc) : IsFine hN γ hc B τ := by
  classical
  refine ⟨fun b hb => ⟨(hB.1 b hb).1, hm b hb⟩, fun s s' hs hss' hs' hp => ?_⟩
  set m := (insert (0 : ℝ) B).max' (Finset.insert_nonempty _ _)
  have hmmem : m ∈ insert (0 : ℝ) B := Finset.max'_mem _ _
  have hmax : ∀ c ∈ B, c ≤ m := fun c hc => Finset.le_max' _ c (Finset.mem_insert_of_mem hc)
  by_cases hsm : m ≤ s
  · have := hlast m hmmem hmax
    linarith
  · push Not at hsm
    -- then `m ∈ B` and `s' ≤ m < τ₀`
    rcases Finset.mem_insert.1 hmmem with h0 | hmB
    · linarith
    · have hs'm : s' ≤ m := by
        by_contra h
        exact hp m hmB ⟨hsm, lt_of_not_ge h⟩
      exact hB.2 s s' hs hss' (hs'm.trans (hB.1 m hmB).2.le) hp

/-- **The second variation formula for `H_τ`** (Milnor pp. 84, 86):
`H_τ(x, y) = −2 Σ_b ⟨y_b, Δ_b DW_x/dt⟩`. -/
theorem Hform_eq_jumps {B : Finset ℝ} {τ : ℝ} (h : τ ∈ validFor hN γ hc B)
    (x y : nodeSpace hN γ B) :
    Hform hN γ hc B τ x y = -2 * ∑ b ∈ B.attach, ⟪(y : B → V) b,
      prj hN (γ b) (jump ((brokenOf hc B τ x : pathTangent hN γ) : ℝ → V) b)⟫ := by
  rw [Hform_apply hc h, energyHessian_broken_eq hc h.2.1 h.2.2 h.1 (brokenOf_mem hc h x)
    (brokenSpace_le_fieldsUpTo hc B τ (brokenOf_mem hc h y))]
  congr 1
  rw [← Finset.sum_attach]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [brokenOf_apply_node hc h y b]

/-- **The broken Jacobi fields for different `τ` agree up to the last division point.** -/
theorem brokenOf_eqOn {B : Finset ℝ} (hBne : B.Nonempty) {τ τ' : ℝ} (h : τ ∈ validFor hN γ hc B)
    (h' : τ' ∈ validFor hN γ hc B) (x : nodeSpace hN γ B) :
    EqOn ((brokenOf hc B τ x : pathTangent hN γ) : ℝ → V)
      ((brokenOf hc B τ' x : pathTangent hN γ) : ℝ → V) (Icc 0 (B.max' hBne)) := by
  classical
  set m := B.max' hBne
  have hmB : m ∈ B := B.max'_mem hBne
  have hm0 : 0 < m := (h.1.1 m hmB).1
  set X := ((brokenOf hc B τ x : pathTangent hN γ) : ℝ → V)
  set X' := ((brokenOf hc B τ' x : pathTangent hN γ) : ℝ → V)
  have hfine : IsFine hN γ hc (B.erase m) m := by
    refine ⟨fun b hb => ⟨(h.1.1 b (Finset.mem_of_mem_erase hb)).1,
      lt_of_le_of_ne (B.le_max' b (Finset.mem_of_mem_erase hb)) (Finset.ne_of_mem_erase hb)⟩,
      fun s s' hs hss' hs' hp => h.1.2 s s' hs hss' (hs'.trans (h.1.1 m hmB).2.le) fun b hb => ?_⟩
    by_cases hbm : b = m
    · rw [hbm]; exact fun hI => absurd hs' (not_le.2 hI.2)
    · exact hp b (Finset.mem_erase.2 ⟨hbm, hb⟩)
  have hbroken : ∀ {σ} (hσ : σ ∈ validFor hN γ hc B),
      IsBrokenJacobi hN γ hc (B.erase m) m ((brokenOf hc B σ x : pathTangent hN γ) : ℝ → V) :=
    fun hσ s s' hs hss' hs' hp => (brokenOf_mem hc hσ x).2 s s' hs hss'
      (hs'.trans (hσ.1.1 m hmB).2.le) fun b hb => by
        by_cases hbm : b = m
        · rw [hbm]; exact fun hI => absurd hs' (not_le.2 hI.2)
        · exact hp b (Finset.mem_erase.2 ⟨hbm, hb⟩)
  have hdiff : IsBrokenJacobi hN γ hc (B.erase m) m (X - X') := fun s s' hs hss' hs' hp => by
    obtain ⟨J, hJ, hXJ⟩ := hbroken h s s' hs hss' hs' hp
    obtain ⟨J', hJ', hXJ'⟩ := hbroken h' s s' hs hss' hs' hp
    exact ⟨J - J', Submodule.sub_mem _ hJ hJ', fun t ht => by
      simp only [Pi.sub_apply, X, X']
      rw [hXJ ht, hXJ' ht]⟩
  have h0 := IsBrokenJacobi.eqOn_zero hc hm0 (((h.1.1 m hmB).2.le).trans h.2.2) hfine hdiff
    (by simp [X, X', (brokenOf hc B τ x).2.2.2.1, (brokenOf hc B τ' x).2.2.2.1])
    (by simp [X, X', brokenOf_apply_node hc h x ⟨m, hmB⟩, brokenOf_apply_node hc h' x ⟨m, hmB⟩])
    (fun b hb => by
      have hbB := Finset.mem_of_mem_erase hb
      simp [X, X', brokenOf_apply_node hc h x ⟨b, hbB⟩, brokenOf_apply_node hc h' x ⟨b, hbB⟩])
  intro t ht
  have := h0 ht
  simpa [sub_eq_zero] using this

/-- The value at `τ` of the jump of `W_x` at a division point is continuous in `τ` (the heart of
Lemma 15.C). -/
theorem continuousWithinAt_jump {B : Finset ℝ} {τ₀ : ℝ} (h₀ : τ₀ ∈ validFor hN γ hc B)
    (x : nodeSpace hN γ B) {b : ℝ} (hb : b ∈ B) :
    ContinuousWithinAt (fun τ => prj hN (γ b)
      (jump ((brokenOf hc B τ x : pathTangent hN γ) : ℝ → V) b)) (validFor hN γ hc B) τ₀ := by
  classical
  have hBne : B.Nonempty := ⟨b, hb⟩
  set m := B.max' hBne
  have hmB : m ∈ B := B.max'_mem hBne
  have hm : m ∈ Ioo 0 τ₀ := h₀.1.1 m hmB
  have hm1 : m ∈ Ioo (0 : ℝ) 1 := ⟨hm.1, hm.2.trans_le h₀.2.2⟩
  have hm01 : m ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hm1
  have hb0 : 0 < b := (h₀.1.1 b hb).1
  have hbm : b ≤ m := B.le_max' b hb
  set W : ℝ → ℝ → V := fun τ => ((brokenOf hc B τ x : pathTangent hN γ) : ℝ → V)
  have hagree : ∀ τ ∈ validFor hN γ hc B, EqOn (W τ) (W τ₀) (Icc 0 m) := fun τ hτ =>
    brokenOf_eqOn hc hBne hτ h₀ x
  rcases lt_or_eq_of_le hbm with hbm | rfl
  · -- `b < m`: the jump does not depend on `τ`
    refine continuousWithinAt_const.congr (fun τ hτ => ?_) rfl
    have hev : W τ =ᶠ[𝓝 b] W τ₀ :=
      eventually_of_mem (Icc_mem_nhds hb0 hbm) fun t ht => hagree τ hτ ht
    change prj hN (γ b) (jump (W τ) b) = prj hN (γ b) (jump (W τ₀) b)
    rw [jump_congr hev]
  -- `b = m`: the left derivative is fixed, the right one is `DY^τ/dt(m)`
  set dL := derivWithin (W τ₀) (Iic m) m
  have hleft : ∀ τ ∈ validFor hN γ hc B, derivWithin (W τ) (Iic m) m = dL := fun τ hτ => by
    refine Filter.EventuallyEq.derivWithin_eq ?_ (hagree τ hτ ⟨hm.1.le, le_rfl⟩)
    filter_upwards [Icc_mem_nhdsLE hm.1] with t ht using hagree τ hτ ht
  set ρ : ℝ → V := fun τ => prj hN (γ m) (derivWithin (W τ) (Ici m) m)
  suffices hρ : ContinuousWithinAt ρ (validFor hN γ hc B) τ₀ by
    refine (hρ.sub (continuousWithinAt_const (b := prj hN (γ m) dL))).congr
      (fun τ hτ => ?_) ?_
    · change prj hN (γ m) (jump (W τ) m) = ρ τ - prj hN (γ m) dL
      rw [jump, map_sub, hleft τ hτ]
    · change prj hN (γ m) (jump (W τ₀) m) = ρ τ₀ - prj hN (γ m) dL
      rw [jump, map_sub, hleft τ₀ h₀]
  -- the linear system `L(τ) z = c(τ)`
  have hA := hc.continuous_jacA
  set T := tanAt hN (γ m)
  set L : ℝ → T →L[ℝ] V := fun τ => (ContinuousLinearMap.fst ℝ V V).comp
    ((linFlow (jacA hN γ) hA m τ).comp ((ContinuousLinearMap.inr ℝ V V).comp T.subtypeL))
  have hLapp : ∀ τ (z : T), L τ z = (jacSol hN γ m (0, (z : V)) τ).1 := fun τ z => rfl
  set xm := (x : B → V) ⟨m, hmB⟩
  set c : ℝ → V := fun τ => -(jacSol hN γ m (xm, 0) τ).1
  have hT : ∀ v, prj hN (γ m) v ∈ T := fun v => prj_mem_tanAt hN (hc.mem m hm01) v
  set z : ℝ → T := fun τ => ⟨ρ τ, hT _⟩
  -- the right derivative is `DY^τ/dt(m)`, `Y^τ` the Jacobi field on the last piece
  have hz : ∀ τ ∈ validFor hN γ hc B, L τ (z τ) = c τ := by
    intro τ hτ
    have hmτ : m < τ := (hτ.1.1 m hmB).2
    obtain ⟨Y, hY, hWY⟩ := (brokenOf_mem hc hτ x).2 m τ hm.1.le hmτ le_rfl fun b' hb' hbI =>
      absurd (B.le_max' b' hb') (not_le.2 hbI.1)
    have hYd : HasDerivAt Y (deriv Y m) m :=
      ((hY.1.contDiffOn.contDiffAt (Icc_mem_nhds hm1.1 hm1.2)).differentiableAt
        (by simp)).hasDerivAt
    have hρY : ρ τ = covAlong hN γ Y m := by
      have h1 : derivWithin (W τ) (Ici m) m = deriv Y m := by
        refine (hYd.hasDerivWithinAt.congr_of_eventuallyEq ?_ (hWY ⟨le_rfl, hmτ.le⟩)).derivWithin
          (uniqueDiffWithinAt_Ici m)
        filter_upwards [Icc_mem_nhdsGE hmτ] with t ht using hWY ht
      change prj hN (γ m) (derivWithin (W τ) (Ici m) m) = _
      rw [h1, covAlong, hYd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one m hm01)]
    have hYm : Y m = xm := by
      rw [← hWY ⟨le_rfl, hmτ.le⟩]
      exact brokenOf_apply_node hc hτ x ⟨m, hmB⟩
    have hYτ : Y τ = 0 := by
      rw [← hWY ⟨hmτ.le, le_rfl⟩]
      exact fieldsUpTo_apply_self hτ.2.1.le hτ.2.2
        (brokenSpace_le_fieldsUpTo hc B τ (brokenOf_mem hc hτ x))
    have key := hY.1.eqOn_jacSol hc hm01 (⟨hτ.2.1.le, hτ.2.2⟩ : τ ∈ Icc (0 : ℝ) 1)
    rw [hYm, ← hρY] at key
    have hsplit : ((xm, ρ τ) : V × V) = (xm, 0) + (0, ρ τ) := by simp
    rw [hsplit, jacSol_add hc] at key
    have := congrArg Prod.fst key
    simp only [Pi.add_apply, Prod.fst_add, hYτ] at this
    rw [hLapp]
    change (jacSol hN γ m (0, ρ τ) τ).1 = -(jacSol hN γ m (xm, 0) τ).1
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact this.symm
  -- `L(τ₀)` is injective: `m` and `τ₀` are not conjugate
  have hinj : Injective (L τ₀) := by
    refine (injective_iff_map_eq_zero (L τ₀)).2 fun w hw => ?_
    have hw' : (jacSol hN γ m (0, (w : V)) τ₀).1 = 0 := hw
    have hw0 : prj hN (γ m) (w : V) = w := (mem_tanAt hN (hc.mem m hm01)).1 w.2
    obtain ⟨hJ, hcov⟩ := isJacobiField_jacSol hc hm01 (ζ := (0, (w : V))) (by simp) hw0
    set J := fun t => (jacSol hN γ m (0, (w : V)) t).1
    have hJm : J m = 0 := by simp [J, jacSol_self hc]
    have hJ0 := eq_zero_of_short hc (hJ.comp_projIcc_mem hc) hm.1.le hm.2 h₀.2.2
      (h₀.1.2 m τ₀ hm.1.le hm.2 le_rfl fun b' hb' hbI => absurd (B.le_max' b' hb')
        (not_le.2 hbI.1))
      (by simp [projIcc_of_mem _ hm01, hJm])
      (by simp [projIcc_of_mem _ (⟨h₀.2.1.le, h₀.2.2⟩ : τ₀ ∈ Icc (0 : ℝ) 1), J, hw'])
    have hcovm : covAlong hN γ J m = 0 := by
      rw [covAlong, derivWithin_congr (f := fun t => J (projIcc (0 : ℝ) 1 zero_le_one t))
        (fun t ht => by simp [projIcc_of_mem _ ht]) (by simp [projIcc_of_mem _ hm01]), hJ0]
      simp
    rw [hcov m hm01, jacSol_self hc] at hcovm
    exact Subtype.ext hcovm
  have hLc : Continuous L := by
    have := continuous_linFlow hA m
    exact continuous_const.clm_comp (this.clm_comp continuous_const)
  have hcc : Continuous c := ((continuous_linSol hA m (xm, 0)).fst).neg
  have hzc := continuousWithinAt_of_injective hLc.continuousAt hinj hcc.continuousAt hz h₀
  exact continuous_subtype_val.continuousAt.comp_continuousWithinAt hzc

/-- **Lemma 15.C of the exposition** (Milnor p. 86, "evidently the quadratic form `H_τ` on `Σ`
varies continuously with `τ`"). -/
theorem continuousWithinAt_Hform {B : Finset ℝ} {τ₀ : ℝ} (h₀ : τ₀ ∈ validFor hN γ hc B)
    (x y : nodeSpace hN γ B) :
    ContinuousWithinAt (fun τ => Hform hN γ hc B τ x y) (validFor hN γ hc B) τ₀ := by
  classical
  set ŷ := ((brokenOf hc B τ₀ y : pathTangent hN γ) : ℝ → V)
  have hform : ∀ τ ∈ validFor hN γ hc B, Hform hN γ hc B τ x y = -2 * ∑ b ∈ B,
      ⟪ŷ b, prj hN (γ b) (jump ((brokenOf hc B τ x : pathTangent hN γ) : ℝ → V) b)⟫ := by
    intro τ hτ
    rw [Hform_apply hc hτ, energyHessian_broken_eq hc hτ.2.1 hτ.2.2 hτ.1 (brokenOf_mem hc hτ x)
      (brokenSpace_le_fieldsUpTo hc B τ (brokenOf_mem hc hτ y))]
    congr 1
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [brokenOf_apply_node hc hτ y ⟨b, hb⟩, ← brokenOf_apply_node hc h₀ y ⟨b, hb⟩]
  refine ContinuousWithinAt.congr ?_ hform (hform τ₀ h₀)
  refine continuousWithinAt_const.mul ?_
  exact tendsto_finsetSum _ fun b hb =>
    (continuousWithinAt_const.inner (continuousWithinAt_jump hc h₀ x hb) : ContinuousWithinAt _ _ _)

/-! ### Assertions (3) and (4), first half -/

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- **Lemma 15.A (3) within a set**: definiteness persists along a family continuous within `s`. -/
theorem eventually_isNegDefOn_within {M : Type*} [AddCommGroup M] [Module ℝ M]
    {H : ℝ → LinearMap.BilinForm ℝ M} {S : Submodule ℝ M} [FiniteDimensional ℝ S] {s : Set ℝ}
    {τ₀ : ℝ} (hτ₀ : τ₀ ∈ s) (hH : ∀ x ∈ S, ∀ y ∈ S, ContinuousWithinAt (fun τ => H τ x y) s τ₀)
    (h₀ : IsNegDefOn (H τ₀) S) : ∀ᶠ τ in 𝓝[s] τ₀, IsNegDefOn (H τ) S := by
  have h := eventually_isNegDefOn (τ₀ := (⟨τ₀, hτ₀⟩ : s)) (H := fun τ : s => H τ) (S := S)
    (fun x hx y hy => (continuousWithinAt_iff_continuousAt_domRestrict _ hτ₀).1 (hH x hx y hy)) h₀
  rw [nhdsWithin_eq_map_subtype_coe hτ₀]
  exact h

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
theorem eventually_isPosDefOn_within {M : Type*} [AddCommGroup M] [Module ℝ M]
    {H : ℝ → LinearMap.BilinForm ℝ M} {S : Submodule ℝ M} [FiniteDimensional ℝ S] {s : Set ℝ}
    {τ₀ : ℝ} (hτ₀ : τ₀ ∈ s) (hH : ∀ x ∈ S, ∀ y ∈ S, ContinuousWithinAt (fun τ => H τ x y) s τ₀)
    (h₀ : IsPosDefOn (H τ₀) S) : ∀ᶠ τ in 𝓝[s] τ₀, IsPosDefOn (H τ) S := by
  have h := eventually_isPosDefOn (τ₀ := (⟨τ₀, hτ₀⟩ : s)) (H := fun τ : s => H τ) (S := S)
    (fun x hx y hy => (continuousWithinAt_iff_continuousAt_domRestrict _ hτ₀).1 (hH x hx y hy)) h₀
  rw [nhdsWithin_eq_map_subtype_coe hτ₀]
  exact h

/-- For a fine subdivision of `[0, τ]` whose last point `m` is within `h₀ / 2` of `τ`, every
`τ' ∈ (m, τ + h₀ / 2)`, `τ' ≤ 1`, is valid. -/
theorem mem_validFor_of_near {B : Finset ℝ} {τ : ℝ} (hτ : 0 < τ) (hB : IsFine hN γ hc B τ)
    (hlast : ∀ b ∈ insert 0 B, b < τ ∧ (∀ c ∈ B, c ≤ b) → τ - b ≤ fineMesh hN γ hc / 2)
    {τ' : ℝ} (hτ'1 : τ' ≤ 1) (hτ'τ : τ' < τ + fineMesh hN γ hc / 2)
    (hmτ' : (insert (0 : ℝ) B).max' (Finset.insert_nonempty _ _) < τ') :
    τ' ∈ validFor hN γ hc B := by
  classical
  set m := (insert (0 : ℝ) B).max' (Finset.insert_nonempty _ _)
  have hmmem : m ∈ insert (0 : ℝ) B := Finset.max'_mem _ _
  have hmax : ∀ c ∈ B, c ≤ m := fun c hc => Finset.le_max' _ c (Finset.mem_insert_of_mem hc)
  have hm0 : 0 ≤ m := Finset.le_max' _ 0 (Finset.mem_insert_self _ _)
  have hmτ : m < τ := by
    rcases Finset.mem_insert.1 hmmem with h0 | hmB
    · rw [h0]; exact hτ
    · exact (hB.1 m hmB).2
  have hτm := hlast m hmmem ⟨hmτ, hmax⟩
  refine ⟨isFine_of_isFine hc hB (fun b hb => (hmax b hb).trans_lt hmτ') (hm0.trans_lt hmτ')
    fun b hb hbmax => ?_, hm0.trans_lt hmτ', hτ'1⟩
  have hbm : b = m := by
    refine le_antisymm (Finset.le_max' _ b hb) ?_
    rcases Finset.mem_insert.1 hmmem with h0 | hmB
    · rw [h0]
      rcases Finset.mem_insert.1 hb with h0' | hb'
      · rw [h0']
      · exact (hB.1 b hb').1.le
    · exact hbmax m hmB
  rw [hbm]
  linarith

end Morse
