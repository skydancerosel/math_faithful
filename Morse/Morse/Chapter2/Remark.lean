import Morse.Chapter2.Regular

/-!
Milnor, *Morse Theory*, §3, p. 13 (the Remark after Theorem 3.1) and Diagram 3 (p. 14).

# The compactness of `f⁻¹[a, b]` cannot be omitted

Milnor's remark, paraphrased: the hypothesis that `f⁻¹[a, b]` is compact cannot be dropped from
Theorem 3.1. Diagram 3 shows a surface with its height function, from which a point `p` with
`a ≤ f(p) ≤ b` has been removed; then "clearly" `M^a` is not a deformation retract of `M^b`.

We formalize a concrete version of Diagram 3: the bowl `f(z) = ‖z‖²` on the plane `ℂ = ℝ²`, with
`a = 1/4`, `b = 4` and `p = i`, so that `f(p) = 1`.

* On the whole plane `f⁻¹[1/4, 4]` is a compact annulus without critical points, and Theorem 3.1
  applies: the disc of radius `1/2` is a strong deformation retract of the disc of radius `2`
  (`remark_p13_plane`).
* On `M = ℂ \ {i}` (an open subset of the plane, hence a surface) the slab `f⁻¹[1/4, 4]` is the
  annulus minus `i`: it still contains no critical point (`remark_p13_not_isCriticalPoint`), but it
  is no longer compact (`remark_p13_not_isCompact`). Now `M^{1/4}` is the closed disc of radius
  `1/2`, which is contractible, while `M^4`, the closed disc of radius `2` minus `i`, is not
  (`not_contractibleSpace`). Hence `M^{1/4}` and `M^4` are not homotopy equivalent
  (`remark_p13`); in particular `M^{1/4}` is not a deformation retract of `M^4`, and the two are not
  homeomorphic (`remark_p13_not_isStrongDeformationRetract`, `remark_p13_not_homeomorph`).

## What Milnor's text leaves implicit

"Clearly" hides a piece of algebraic topology: the punctured disc is not contractible, because a
loop around the puncture is not null-homotopic. We prove it with Mathlib's homotopy lifting property
for the covering `exp : ℂ → ℂ \ {0}` (`IsCoveringMap.liftHomotopy`, `Complex.isCoveringMap_exp`).
If `z ↦ z - i` were null-homotopic on `M^4`, restricting the null-homotopy to the loop
`s ↦ i + e^{2πis}` and lifting it through `exp` would give a continuous integer-valued function on
`[0, 1]` (the winding numbers of the intermediate loops) equal to `1` at `0` and to `0` at `1`,
contradicting the intermediate value theorem (`not_nullhomotopic`).
-/

open Set Filter Topology Complex
open scoped Real

noncomputable section

namespace Morse

namespace RemarkP13

/-! ### Winding numbers -/

/-- A continuous integer-valued function on a connected space is constant. -/
theorem eq_of_forall_eq_intCast {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {k : X → ℝ} (hk : Continuous k) (hint : ∀ x, ∃ n : ℤ, k x = n) (x y : X) : k x = k y := by
  have key : ∀ u v : X, ∀ m n : ℤ, k u = m → k v = n → m < n → False := by
    intro u v m n hu hv hmn
    have hmn' : (m : ℝ) + 1 ≤ n := by exact_mod_cast hmn
    obtain ⟨w, hw⟩ := intermediate_value_univ u v hk
      (show (m : ℝ) + 1 / 2 ∈ Icc (k u) (k v) by rw [hu, hv]; constructor <;> linarith)
    obtain ⟨l, hl⟩ := hint w
    have h1 : (m : ℝ) < l := by rw [← hl, hw]; linarith
    have h2 : (l : ℝ) < m + 1 := by rw [← hl, hw]; linarith
    have h1' : m < l := by exact_mod_cast h1
    have h2' : l < m + 1 := by exact_mod_cast h2
    omega
  obtain ⟨m, hm⟩ := hint x
  obtain ⟨n, hn⟩ := hint y
  rcases lt_trichotomy m n with h | h | h
  · exact (key x y m n hm hn h).elim
  · rw [hm, hn, h]
  · exact (key y x n m hn hm h).elim

/-- **A loop with winding number one is not null-homotopic.** If `γ` is a loop in `X` and
`j : X → ℂ \ {0}` maps it to the loop `s ↦ e^{2πis}`, then `j` is not null-homotopic. -/
theorem not_nullhomotopic {X : Type*} [TopologicalSpace X] (j : C(X, {z : ℂ // z ≠ 0}))
    (γ : C(unitInterval, X)) (hγ : γ 0 = γ 1)
    (hjγ : ∀ s : unitInterval, (j (γ s) : ℂ) = exp (↑(2 * π * s) * Complex.I)) :
    ¬j.Nullhomotopic := by
  rintro ⟨y, ⟨H⟩⟩
  let G : C(unitInterval × unitInterval, {z : ℂ // z ≠ 0}) :=
    H.toContinuousMap.comp ((ContinuousMap.id unitInterval).prodMap γ)
  have hG : ∀ t s, G (t, s) = H (t, γ s) := fun _ _ => rfl
  let f₀ : C(unitInterval, ℂ) := ⟨fun s => ↑(2 * π * s) * Complex.I, by fun_prop⟩
  have G_0 : ∀ s, G (0, s) =
      (fun z : ℂ => (⟨exp z, exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) (f₀ s) := by
    intro s
    apply Subtype.ext
    rw [hG, H.apply_zero]
    exact hjγ s
  let L := isCoveringMap_exp.liftHomotopy G f₀ G_0
  have hlift : ∀ p, exp (L p) = (G p : ℂ) := fun p =>
    congrArg Subtype.val (congrFun (isCoveringMap_exp.liftHomotopy_lifts G f₀ G_0) p)
  have hzero : ∀ s, L (0, s) = f₀ s := isCoveringMap_exp.liftHomotopy_zero G f₀ G_0
  -- two lifts of the same point differ by an integer multiple of `2πi`
  have hint : ∀ t s s' : unitInterval, G (t, s) = G (t, s') →
      ∃ n : ℤ, (L (t, s) - L (t, s')).im / (2 * π) = n := by
    intro t s s' h
    have : exp (L (t, s)) = exp (L (t, s')) := by rw [hlift, hlift, h]
    obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 this
    refine ⟨n, ?_⟩
    rw [hn, add_sub_cancel_left]
    simp [Real.pi_ne_zero]
  have hLc : ∀ s : unitInterval, Continuous fun t : unitInterval => L (t, s) := fun s =>
    L.continuous.comp (continuous_id.prodMk continuous_const)
  have hLc' : ∀ t : unitInterval, Continuous fun s : unitInterval => L (t, s) := fun t =>
    L.continuous.comp (continuous_const.prodMk continuous_id)
  -- `k t` is the winding number of the loop `G (t, ·)`
  let k : unitInterval → ℝ := fun t => (L (t, 1) - L (t, 0)).im / (2 * π)
  have hk : Continuous k :=
    ((Complex.continuous_im.comp ((hLc 1).sub (hLc 0))).div_const _)
  have hkint : ∀ t, ∃ n : ℤ, k t = n := fun t => hint t 1 0 (by rw [hG, hG, hγ])
  have hk0 : k 0 = 1 := by
    change (L (0, 1) - L (0, 0)).im / (2 * π) = 1
    rw [hzero, hzero]
    simp [f₀, Complex.mul_im]
  -- the last loop is constant, so its winding number is `0`
  have hk1 : k 1 = 0 := by
    let m : unitInterval → ℝ := fun s => (L (1, s) - L (1, 0)).im / (2 * π)
    have hm : Continuous m :=
      ((Complex.continuous_im.comp ((hLc' 1).sub continuous_const)).div_const _)
    have hmint : ∀ s, ∃ n : ℤ, m s = n := fun s =>
      hint 1 s 0 (by rw [hG, hG, H.apply_one, H.apply_one]; rfl)
    have := eq_of_forall_eq_intCast hm hmint 1 0
    simpa [m, k] using this
  have := eq_of_forall_eq_intCast hk hkint 0 1
  rw [hk0, hk1] at this
  exact one_ne_zero this

/-! ### The punctured plane -/

/-- The surface of the example: the plane minus the point `p = i`. -/
abbrev M : Set ℂ := {Complex.I}ᶜ

/-- The height function `f(z) = ‖z‖²` on `M`. -/
def F (z : M) : ℝ := ‖(z : ℂ)‖ ^ 2

theorem mem_closedBall_of_mem_sublevel (z : sublevel F (1 / 4)) :
    ((z : M) : ℂ) ∈ Metric.closedBall (0 : ℂ) (1 / 2) := by
  have h : ‖((z : M) : ℂ)‖ ^ 2 ≤ 1 / 4 := z.2
  rw [Metric.mem_closedBall, dist_zero_right]
  nlinarith [norm_nonneg ((z : M) : ℂ)]

theorem mem_M_of_mem_closedBall (w : Metric.closedBall (0 : ℂ) (1 / 2)) : (w : ℂ) ∈ M := by
  intro h
  have hw := w.2
  rw [Metric.mem_closedBall, dist_zero_right, show (w : ℂ) = Complex.I from h, norm_I] at hw
  norm_num at hw

theorem mem_sublevel_of_mem_closedBall (w : Metric.closedBall (0 : ℂ) (1 / 2)) :
    (⟨w, mem_M_of_mem_closedBall w⟩ : M) ∈ sublevel F (1 / 4) := by
  have hw := w.2
  rw [Metric.mem_closedBall, dist_zero_right] at hw
  change ‖(w : ℂ)‖ ^ 2 ≤ 1 / 4
  nlinarith [norm_nonneg (w : ℂ)]

/-- `M^{1/4}` is the closed disc of radius `1/2` (the removed point lies above level `1/4`). -/
def sublevelHomeomorph : sublevel F (1 / 4) ≃ₜ Metric.closedBall (0 : ℂ) (1 / 2) where
  toFun z := ⟨((z : M) : ℂ), mem_closedBall_of_mem_sublevel z⟩
  invFun w := ⟨⟨w, mem_M_of_mem_closedBall w⟩, mem_sublevel_of_mem_closedBall w⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
    mem_closedBall_of_mem_sublevel
  continuous_invFun := (continuous_subtype_val.subtype_mk mem_M_of_mem_closedBall).subtype_mk
    mem_sublevel_of_mem_closedBall

instance : ContractibleSpace (sublevel F (1 / 4)) :=
  haveI : ContractibleSpace (Metric.closedBall (0 : ℂ) (1 / 2)) :=
    (convex_closedBall 0 (1 / 2)).contractibleSpace (Metric.nonempty_closedBall.2 (by norm_num))
  sublevelHomeomorph.contractibleSpace

/-- `z ↦ z - i`, from `M^4` to `ℂ \ {0}`. -/
def j : C(sublevel F 4, {z : ℂ // z ≠ 0}) where
  toFun z := ⟨((z : M) : ℂ) - Complex.I, sub_ne_zero.2 (z : M).2⟩
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_subtype_val).sub continuous_const).subtype_mk _

/-- The loop `s ↦ i + e^{2πis}` in `M^4`, around the removed point. -/
def γ : C(unitInterval, sublevel F 4) where
  toFun s := ⟨⟨Complex.I + exp (↑(2 * π * s) * Complex.I), by
      simp only [M, mem_compl_iff, mem_singleton_iff, add_eq_left]
      exact exp_ne_zero _⟩, by
    change ‖Complex.I + exp (↑(2 * π * s) * Complex.I)‖ ^ 2 ≤ 4
    have h1 : ‖Complex.I + exp (↑(2 * π * s) * Complex.I)‖ ≤ 2 :=
      (norm_add_le _ _).trans (by rw [norm_I, norm_exp_ofReal_mul_I]; norm_num)
    nlinarith [norm_nonneg (Complex.I + exp (↑(2 * π * s) * Complex.I))]⟩
  continuous_toFun := by
    refine (Continuous.subtype_mk ?_ _).subtype_mk _
    fun_prop

theorem γ_zero_eq_one : γ 0 = γ 1 := by
  apply Subtype.ext
  apply Subtype.ext
  change Complex.I + exp (↑(2 * π * ((0 : unitInterval) : ℝ)) * Complex.I) =
    Complex.I + exp (↑(2 * π * ((1 : unitInterval) : ℝ)) * Complex.I)
  simp only [Set.Icc.coe_zero, Set.Icc.coe_one, mul_zero, mul_one, ofReal_zero, zero_mul,
    exp_zero]
  push_cast
  rw [exp_two_pi_mul_I]

/-- **`M^4` is not contractible**: the loop `γ` winds once around the removed point. -/
theorem not_contractibleSpace : ¬ContractibleSpace (sublevel F 4) := by
  intro h
  have hj : j.Nullhomotopic := by
    simpa using (id_nullhomotopic (sublevel F 4)).comp_right j
  exact not_nullhomotopic j γ γ_zero_eq_one (fun s => add_sub_cancel_left _ _) hj

/-! ### The Remark on p. 13 -/

/-- In the example `M = ℂ \ {i}`, `f = ‖·‖²`, the slab `f⁻¹[1/4, 4]` contains no critical point:
the only critical point of `‖·‖²` on the plane is `0`, at level `0`. -/
theorem remark_p13_not_isCriticalPoint (z : ℂ) (hz : ‖z‖ ^ 2 ∈ Icc (1 / 4 : ℝ) 4) :
    ¬IsCriticalPoint (fun z : ℂ => ‖z‖ ^ 2) z := by
  intro hcrit
  have h2 : (2 • innerSL ℝ z : ℂ →L[ℝ] ℝ) = 0 :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt.unique hcrit
  have h3 : z = 0 := by simpa using congrArg (fun L : ℂ →L[ℝ] ℝ => L z) h2
  have := hz.1
  rw [h3, norm_zero] at this
  norm_num at this

/-- In the example, the slab `f⁻¹[1/4, 4] ⊆ M` is not compact: the removed point `i` is a limit of
points of the slab. -/
theorem remark_p13_not_isCompact : ¬IsCompact (F ⁻¹' Icc (1 / 4) 4) := by
  intro hc
  have hcl := (hc.image continuous_subtype_val).isClosed
  have hI : Complex.I ∉ ((↑) : M → ℂ) '' (F ⁻¹' Icc (1 / 4) 4) := by
    rintro ⟨z, -, hz⟩
    exact z.2 hz
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hcl.isOpen_compl Complex.I hI
  set δ := min (ε / 2) (1 / 2) with hδ_def
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  have hδε : δ < ε := (min_le_left _ _).trans_lt (by linarith)
  have hnorm : ‖((1 + δ : ℝ) : ℂ) * Complex.I‖ = 1 + δ := by
    rw [norm_mul, norm_I, mul_one, norm_real, Real.norm_of_nonneg (by linarith)]
  have hne : ((1 + δ : ℝ) : ℂ) * Complex.I ∈ M := by
    intro h
    have h' := congrArg (fun z : ℂ => ‖z‖) (show ((1 + δ : ℝ) : ℂ) * Complex.I = Complex.I from h)
    simp only [hnorm, norm_I] at h'
    linarith
  refine hball (show ((1 + δ : ℝ) : ℂ) * Complex.I ∈ Metric.ball Complex.I ε from ?_)
    ⟨⟨_, hne⟩, ⟨?_, ?_⟩, rfl⟩
  · rw [Metric.mem_ball, dist_eq_norm,
      show ((1 + δ : ℝ) : ℂ) * Complex.I - Complex.I = (δ : ℂ) * Complex.I by push_cast; ring,
      norm_mul, norm_I, mul_one, norm_real, Real.norm_of_nonneg hδ.le]
    exact hδε
  · change 1 / 4 ≤ ‖((1 + δ : ℝ) : ℂ) * Complex.I‖ ^ 2
    rw [hnorm]
    nlinarith
  · change ‖((1 + δ : ℝ) : ℂ) * Complex.I‖ ^ 2 ≤ 4
    rw [hnorm]
    nlinarith

/-- **Milnor's Remark** (p. 13): in the example, `M^{1/4}` and `M^4` are not homotopy equivalent,
although `f⁻¹[1/4, 4]` contains no critical point. So the compactness hypothesis of Theorem 3.1
cannot be omitted. -/
theorem remark_p13 :
    ¬Nonempty (ContinuousMap.HomotopyEquiv (sublevel F (1 / 4)) (sublevel F 4)) := by
  rintro ⟨e⟩
  exact not_contractibleSpace e.symm.contractibleSpace

/-- Milnor's formulation: "Clearly `M^a` is not a deformation retract of `M^b`." -/
theorem remark_p13_not_isStrongDeformationRetract :
    ¬IsStrongDeformationRetract ((↑) ⁻¹' sublevel F (1 / 4) : Set (sublevel F 4)) := fun h =>
  remark_p13 ⟨(h.exists_homotopyEquiv (sublevel_mono F (by norm_num))).choose⟩

/-- The first half of Theorem 3.1 fails too: `M^{1/4}` and `M^4` are not even homeomorphic. -/
theorem remark_p13_not_homeomorph : ¬Nonempty (sublevel F (1 / 4) ≃ₜ sublevel F 4) :=
  fun ⟨e⟩ => remark_p13 ⟨e.toHomotopyEquiv⟩

/-- **With the point put back, Theorem 3.1 applies**: on the whole plane, `f⁻¹[1/4, 4]` is a compact
annulus without critical points, and the disc of radius `1/2` is a strong deformation retract of
the disc of radius `2`. -/
theorem remark_p13_plane :
    IsStrongDeformationRetract ((↑) ⁻¹' sublevel (fun z : ℂ => ‖z‖ ^ 2) (1 / 4) :
      Set (sublevel (fun z : ℂ => ‖z‖ ^ 2) 4)) := by
  have hK : IsCompact ((fun z : ℂ => ‖z‖ ^ 2) ⁻¹' Icc (1 / 4) 4) := by
    refine Metric.isCompact_of_isClosed_isBounded
      (isClosed_Icc.preimage (contDiff_norm_sq ℝ (n := 0)).continuous)
      ((Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2)).subset fun z hz => ?_)
    rw [Metric.mem_closedBall, dist_zero_right]
    have : ‖z‖ ^ 2 ≤ 4 := hz.2
    nlinarith [norm_nonneg z]
  exact (theorem_3_1 (contDiff_norm_sq ℝ) (by norm_num) hK
    fun z hz => remark_p13_not_isCriticalPoint z hz).2.1

end RemarkP13

end Morse
