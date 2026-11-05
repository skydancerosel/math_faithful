import Milnor.Chapter7.Scale
import Milnor.Chapter7.Transition

/-!
# The cancelling homotopy

For a unit vector `w`, `a > 0` and a smooth `ρ : ℝ → ℝ` going from `1` to `-1`, the family
`G_t(z) = (⟪w, z⟫² - a² ρ(t)) • w + (z - ⟪w, z⟫ • w)` has zero set `{λ • w : λ² = a² ρ(t)}`: two
points `±a • w` at `t = 0`, none at `t = 1`.  Composed with the collapse map it is a homotopy
`cancelΦ` that cancels two preimage points of the north pole with opposite signs.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace Classical

noncomputable section

namespace Milnor

open Sphere

namespace Framed

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)

/-! ### Definitions -/

/-- Orthogonal projection onto the line spanned by `w` (for `‖w‖ = 1`): `z ↦ ⟪w, z⟫ • w`. -/
def projW (w : E) : E →L[ℝ] E := (innerSL ℝ w).smulRight w

theorem projW_apply (w z : E) : projW w z = ⟪w, z⟫ • w := by
  simp [projW]

/-- The inner map of the cancelling homotopy. -/
def cancelG (w : E) (a : ℝ) (ρ : ℝ → ℝ) (q : E × ℝ) : E :=
  (⟪w, q.1⟫ ^ 2 - a ^ 2 * ρ q.2) • w + (q.1 - ⟪w, q.1⟫ • w)

/-- The cancelling homotopy, centred at `c₀`. -/
def cancelΦ {b : Fin m → E} (hb : LinearIndependent ℝ b) (c : ℝ) (w : E) (a : ℝ) (ρ : ℝ → ℝ)
    (c₀ : E) (q : E × ℝ) : Sph m :=
  collapse hb c (cancelG w a ρ (q.1 - c₀, q.2))

/-- The derivative of a time slice of `cancelG` at the point `l • w`. -/
def Tcan (w : E) (l : ℝ) : E →L[ℝ] E :=
  (2 * l) • projW w + (ContinuousLinearMap.id ℝ E - projW w)

theorem Tcan_apply (w : E) (l : ℝ) (z : E) :
    Tcan w l z = (2 * l) • ⟪w, z⟫ • w + (z - ⟪w, z⟫ • w) := by
  simp [Tcan, projW_apply]

theorem inner_self_of_norm_one {w : E} (hw : ‖w‖ = 1) : ⟪w, w⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, hw, one_pow]

/-! ### Smoothness -/

/-- A `ContDiff` map on `E × ℝ` is `ContMDiff` for the product model. -/
theorem contMDiff_prod_of_contDiff {f : E × ℝ → E} (hf : ContDiff ℝ ∞ f) :
    ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ f := by
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  exact contMDiff_iff_contDiff.2 hf

/-- A `HasFDerivAt` statement on `E × ℝ` gives `HasMFDerivAt` for the product model. -/
theorem hasMFDerivAt_prod_of_hasFDerivAt {f : E × ℝ → E} {q : E × ℝ} {f' : E × ℝ →L[ℝ] E}
    (hf : HasFDerivAt f f' q) :
    HasMFDerivAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) f q f' := by
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  exact hasMFDerivAt_iff_hasFDerivAt.2 hf

theorem contDiff_cancelG (w : E) (a : ℝ) {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) :
    ContDiff ℝ ∞ (cancelG w a ρ) := by
  have h1 : ContDiff ℝ ∞ (fun q : E × ℝ => ⟪w, q.1⟫) :=
    (innerSL ℝ w).contDiff.comp contDiff_fst
  have h2 : ContDiff ℝ ∞ (fun q : E × ℝ => ρ q.2) := hρ.comp contDiff_snd
  exact (((h1.pow 2).sub (contDiff_const.mul h2)).smul contDiff_const).add
    (contDiff_fst.sub (h1.smul contDiff_const))

theorem contMDiff_cancelΦ {b : Fin m → E} (hb : LinearIndependent ℝ b) (c : ℝ) (w : E) (a : ℝ)
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (c₀ : E) :
    ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ (cancelΦ hb c w a ρ c₀) := by
  have h : ContDiff ℝ ∞ (fun q : E × ℝ => cancelG w a ρ (q.1 - c₀, q.2)) :=
    (contDiff_cancelG w a hρ).comp ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd)
  exact (contMDiff_collapse hb c).comp (contMDiff_prod_of_contDiff h)

/-! ### The zero set -/

theorem cancelG_eq_zero_iff {w : E} (hw : ‖w‖ = 1) (a : ℝ) (ρ : ℝ → ℝ) (z : E) (t : ℝ) :
    cancelG w a ρ (z, t) = 0 ↔ ∃ l : ℝ, z = l • w ∧ l ^ 2 = a ^ 2 * ρ t := by
  have hww := inner_self_of_norm_one hw
  constructor
  · intro h
    have h1 : ⟪w, cancelG w a ρ (z, t)⟫ = ⟪w, z⟫ ^ 2 - a ^ 2 * ρ t := by
      simp only [cancelG, inner_add_right, inner_sub_right, inner_smul_right, hww]; ring
    rw [h, inner_zero_right] at h1
    have h2 : z - ⟪w, z⟫ • w = 0 := by
      have h' := h
      simp only [cancelG] at h'
      rw [← h1, zero_smul, zero_add] at h'
      exact h'
    exact ⟨⟪w, z⟫, sub_eq_zero.1 h2, sub_eq_zero.1 h1.symm⟩
  · rintro ⟨l, rfl, hl⟩
    simp only [cancelG, inner_smul_right, hww, mul_one, hl, sub_self, zero_smul, zero_add]

theorem cancelΦ_eq_north_iff {b : Fin m → E} (hb : LinearIndependent ℝ b) {c : ℝ} (hc : c ≠ 0)
    {w : E} (hw : ‖w‖ = 1) (a : ℝ) (ρ : ℝ → ℝ) (c₀ s : E) (t : ℝ) :
    cancelΦ hb c w a ρ c₀ (s, t) = north ↔ ∃ l : ℝ, s = c₀ + l • w ∧ l ^ 2 = a ^ 2 * ρ t := by
  simp only [cancelΦ]
  rw [collapse_eq_north_iff hb hc, cancelG_eq_zero_iff hw]
  simp only [sub_eq_iff_eq_add']

/-! ### Behaviour far away -/

theorem norm_cancelG_ge {w : E} (hw : ‖w‖ = 1) {a : ℝ} (ha : 0 < a) {ρ : ℝ → ℝ}
    (hρ1 : ∀ t, |ρ t| ≤ 1) {r : ℝ} (har : 2 * a ≤ r) {z : E} {t : ℝ} (hz : r ≤ ‖z‖) :
    min (r / 2) (r ^ 2 / 4) ≤ ‖cancelG w a ρ (z, t)‖ := by
  have hww := inner_self_of_norm_one hw
  set p := ⟪w, z⟫ with hp
  set u := z - p • w with hu
  set α := p ^ 2 - a ^ 2 * ρ t with hα
  have hwu : ⟪w, u⟫ = 0 := by
    rw [hu, inner_sub_right, inner_smul_right, hww]; ring
  have hG : cancelG w a ρ (z, t) = α • w + u := rfl
  have hN : ‖cancelG w a ρ (z, t)‖ ^ 2 = α ^ 2 + ‖u‖ ^ 2 := by
    rw [hG, norm_add_sq_real, norm_smul, real_inner_smul_left, hwu, Real.norm_eq_abs, hw, mul_one,
      sq_abs]
    ring
  have hz2 : ‖z‖ ^ 2 = p ^ 2 + ‖u‖ ^ 2 := by
    have hzu : z = p • w + u := by rw [hu]; abel
    conv_lhs => rw [hzu]
    rw [norm_add_sq_real, norm_smul, real_inner_smul_left, hwu, Real.norm_eq_abs, hw, mul_one,
      sq_abs]
    ring
  have hr : 0 < r := by linarith
  have hN0 : 0 ≤ ‖cancelG w a ρ (z, t)‖ := norm_nonneg _
  have hzr : r ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ hr.le hz 2
  have ha2 : a ^ 2 ≤ r ^ 2 / 4 := by nlinarith
  have hρt : a ^ 2 * ρ t ≤ a ^ 2 :=
    mul_le_of_le_one_right (sq_nonneg a) (abs_le.1 (hρ1 t)).2
  by_cases hcase : r ^ 2 / 2 ≤ ‖u‖ ^ 2
  · refine le_trans (min_le_left _ _) ?_
    have h1 : (r / 2) ^ 2 ≤ ‖cancelG w a ρ (z, t)‖ ^ 2 := by
      rw [hN]; nlinarith [sq_nonneg α]
    exact (pow_le_pow_iff_left₀ (by positivity) hN0 two_ne_zero).1 h1
  · refine le_trans (min_le_right _ _) ?_
    push Not at hcase
    have hp2 : r ^ 2 / 2 ≤ p ^ 2 := by linarith
    have hα' : r ^ 2 / 4 ≤ α := by rw [hα]; linarith
    have hα0 : 0 ≤ α := le_trans (by positivity) hα'
    have h1 : α ^ 2 ≤ ‖cancelG w a ρ (z, t)‖ ^ 2 := by
      rw [hN]; nlinarith [sq_nonneg ‖u‖]
    exact le_trans hα' ((pow_le_pow_iff_left₀ hα0 hN0 two_ne_zero).1 h1)

theorem cancelΦ_eq_south {b : Fin m → E} (hb : LinearIndependent ℝ b) {c ε₀ : ℝ}
    (hsouth : ∀ z, ε₀ / 2 ≤ ‖z‖ → collapse hb c z = south) {w : E} (hw : ‖w‖ = 1) {a : ℝ}
    (ha : 0 < a) {ρ : ℝ → ℝ} (hρ1 : ∀ t, |ρ t| ≤ 1) {r : ℝ} (har : 2 * a ≤ r)
    (hr : ε₀ / 2 ≤ min (r / 2) (r ^ 2 / 4)) (c₀ : E) {s : E} {t : ℝ} (hs : r ≤ ‖s - c₀‖) :
    cancelΦ hb c w a ρ c₀ (s, t) = south :=
  hsouth _ (le_trans hr (norm_cancelG_ge hw ha hρ1 har hs))

/-! ### Derivatives -/

theorem hasFDerivAt_cancelG_slice {w : E} (hw : ‖w‖ = 1) (a : ℝ) (ρ : ℝ → ℝ) (t : ℝ) (l : ℝ) :
    HasFDerivAt (fun z => cancelG w a ρ (z, t)) (Tcan w l) (l • w) := by
  have hww := inner_self_of_norm_one hw
  have hin : HasFDerivAt (fun z : E => ⟪w, z⟫) (innerSL ℝ w) (l • w) :=
    (innerSL ℝ w).hasFDerivAt
  have hraw := (((hin.pow 2).sub_const (a ^ 2 * ρ t)).smul_const w).add
    ((hasFDerivAt_id (l • w)).sub (hin.smul_const w))
  refine hraw.congr_fderiv (ContinuousLinearMap.ext fun h => ?_)
  simp [Tcan_apply, inner_smul_right, hw]
  module

theorem hasMFDerivAt_cancelΦ_slice {b : Fin m → E} (hb : LinearIndependent ℝ b) (c : ℝ) {w : E}
    (hw : ‖w‖ = 1) (a : ℝ) (ρ : ℝ → ℝ) (c₀ : E) (t : ℝ) {l : ℝ} (hl : l ^ 2 = a ^ 2 * ρ t) :
    HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun s => cancelΦ hb c w a ρ c₀ (s, t)) (c₀ + l • w)
      ((c • basisCLM b).comp (Tcan w l)) := by
  set g : E → E := fun s => cancelG w a ρ (s - c₀, t) with hg
  have hg0 : g (c₀ + l • w) = 0 := by
    show cancelG w a ρ (c₀ + l • w - c₀, t) = 0
    exact (cancelG_eq_zero_iff hw a ρ _ t).2 ⟨l, by simp, hl⟩
  have hgd : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) g (c₀ + l • w) (Tcan w l) := by
    refine hasMFDerivAt_iff_hasFDerivAt.2 ?_
    have hf : HasFDerivAt (fun s : E => s - c₀) (ContinuousLinearMap.id ℝ E) (c₀ + l • w) :=
      (hasFDerivAt_id _).sub_const c₀
    have hg' : HasFDerivAt (fun z => cancelG w a ρ (z, t)) (Tcan w l) (c₀ + l • w - c₀) := by
      rw [add_sub_cancel_left]; exact hasFDerivAt_cancelG_slice hw a ρ t l
    have := hg'.comp (c₀ + l • w) hf
    rw [ContinuousLinearMap.comp_id] at this
    exact this
  have hcd : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (collapse hb c) (g (c₀ + l • w)) (c • basisCLM b) := by
    rw [hg0]; exact hasMFDerivAt_collapse_zero hb c
  exact hcd.comp (c₀ + l • w) hgd

/-! ### `Tcan` is invertible with determinant `2 l` -/

theorem inner_Tcan {w : E} (hw : ‖w‖ = 1) (l : ℝ) (z : E) : ⟪w, Tcan w l z⟫ = 2 * l * ⟪w, z⟫ := by
  simp only [Tcan_apply, inner_add_right, inner_sub_right, inner_smul_right,
    inner_self_of_norm_one hw]
  ring

theorem Tcan_injective {w : E} (hw : ‖w‖ = 1) {l : ℝ} (hl : l ≠ 0) : Injective (Tcan w l) := by
  refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
  have h1 := inner_Tcan hw l z
  rw [hz, inner_zero_right] at h1
  have h2 : ⟪w, z⟫ = 0 := by
    rcases mul_eq_zero.1 h1.symm with h | h
    · exact absurd (by linarith : l = 0) hl
    · exact h
  have h3 := Tcan_apply w l z
  rw [hz, h2, zero_smul, smul_zero, zero_add, sub_zero] at h3
  exact h3.symm

theorem Tcan_bijective {w : E} (hw : ‖w‖ = 1) {l : ℝ} (hl : l ≠ 0) :
    Function.Bijective (Tcan w l) :=
  ⟨Tcan_injective hw hl, LinearMap.injective_iff_surjective
    (f := (Tcan w l : E →ₗ[ℝ] E)) |>.1 (Tcan_injective hw hl)⟩

theorem det_Tcan {w : E} (hw : ‖w‖ = 1) (l : ℝ) :
    LinearMap.det ((Tcan w l : E →L[ℝ] E) : E →ₗ[ℝ] E) = 2 * l := by
  have hww := inner_self_of_norm_one hw
  have hv : Orthonormal ℝ ((↑) : ({w} : Set E) → E) := by
    rw [orthonormal_subtype_iff_ite]
    intro x hx y hy
    rw [Set.mem_singleton_iff] at hx hy
    subst hx; subst hy; rw [if_pos rfl]; exact hww
  obtain ⟨u, v, hwu, hv⟩ := hv.exists_orthonormalBasis_extension
  have hw_mem : w ∈ u := hwu (Set.mem_singleton w)
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : u, (i₀ : E) = w := ⟨⟨w, hw_mem⟩, rfl⟩
  have hvi : ∀ i, v i = (i : E) := fun i => by rw [hv]
  have hvi₀ : v i₀ = w := by rw [hvi, hi₀]
  have horth := orthonormal_iff_ite.1 v.orthonormal
  have hT : ∀ i : u, Tcan w l (v i) = (if i = i₀ then 2 * l else 1) • v i := by
    intro i
    by_cases hi : i = i₀
    · subst hi; rw [if_pos rfl, Tcan_apply, hvi₀]; simp [hw]
    · rw [if_neg hi, Tcan_apply, one_smul]
      have h0 : ⟪w, v i⟫ = 0 := by
        have := horth i₀ i
        rw [if_neg (Ne.symm hi), hvi₀] at this
        exact this
      rw [h0, zero_smul, smul_zero, zero_add, sub_zero]
  rw [← LinearMap.det_toMatrix v.toBasis]
  have hM : LinearMap.toMatrix v.toBasis v.toBasis ((Tcan w l : E →L[ℝ] E) : E →ₗ[ℝ] E) =
      Matrix.diagonal (fun i : u => if i = i₀ then 2 * l else 1) := by
    ext i j
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe, hT j,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply, inner_smul_right,
      horth i j, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  rw [hM, Matrix.det_diagonal]
  simp [Finset.prod_ite_eq']

/-! ### Regularity of the north pole -/

/-- The full derivative of the inner map of `cancelΦ`. -/
def Dcan (w : E) (a : ℝ) (ρ : ℝ → ℝ) (t l : ℝ) : E × ℝ →L[ℝ] E :=
  (Tcan w l).comp (ContinuousLinearMap.fst ℝ E ℝ) -
    (ContinuousLinearMap.snd ℝ E ℝ).smulRight ((a ^ 2 * deriv ρ t) • w)

theorem Dcan_apply (w : E) (a : ℝ) (ρ : ℝ → ℝ) (t l : ℝ) (h : E) (τ : ℝ) :
    Dcan w a ρ t l (h, τ) = Tcan w l h - τ • (a ^ 2 * deriv ρ t) • w := by
  simp [Dcan]

theorem hasFDerivAt_cancelG_full {w : E} (hw : ‖w‖ = 1) (a : ℝ) {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (c₀ : E) (t l : ℝ) :
    HasFDerivAt (fun q : E × ℝ => cancelG w a ρ (q.1 - c₀, q.2)) (Dcan w a ρ t l)
      (c₀ + l • w, t) := by
  have hww := inner_self_of_norm_one hw
  have hin : HasFDerivAt (fun q : E × ℝ => ⟪w, q.1 - c₀⟫)
      ((innerSL ℝ w).comp (ContinuousLinearMap.fst ℝ E ℝ)) (c₀ + l • w, t) :=
    (innerSL ℝ w).hasFDerivAt.comp (c₀ + l • w, t) (hasFDerivAt_fst.sub_const c₀)
  have hρd : HasFDerivAt (fun q : E × ℝ => ρ q.2)
      ((ContinuousLinearMap.toSpanSingleton ℝ (deriv ρ t)).comp (ContinuousLinearMap.snd ℝ E ℝ))
      (c₀ + l • w, t) :=
    ((hρ.differentiable (by simp)) t).hasDerivAt.hasFDerivAt.comp (c₀ + l • w, t) hasFDerivAt_snd
  have hraw := (((hin.pow 2).sub (hρd.const_mul (a ^ 2))).smul_const w).add
    ((hasFDerivAt_fst.sub_const c₀).sub (hin.smul_const w))
  refine hraw.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
  obtain ⟨h, τ⟩ := q
  simp [Dcan_apply, Tcan_apply, inner_smul_right, hw, ContinuousLinearMap.toSpanSingleton_apply]
  module

theorem surjective_Dcan {w : E} (hw : ‖w‖ = 1) {a : ℝ} (ha : 0 < a) {ρ : ℝ → ℝ}
    (hρ' : ∀ t, ρ t = 0 → deriv ρ t ≠ 0) {l t : ℝ} (hl : l ^ 2 = a ^ 2 * ρ t) :
    Surjective (Dcan w a ρ t l) := by
  have hww := inner_self_of_norm_one hw
  intro y
  by_cases hl0 : l = 0
  · subst hl0
    have hρt : ρ t = 0 := by
      have : a ^ 2 * ρ t = 0 := by rw [← hl]; ring
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (pow_eq_zero_iff two_ne_zero |>.1 h) ha.ne'
      · exact h
    have hκ : a ^ 2 * deriv ρ t ≠ 0 := mul_ne_zero (pow_ne_zero 2 ha.ne') (hρ' t hρt)
    refine ⟨(y - ⟪w, y⟫ • w, -⟪w, y⟫ / (a ^ 2 * deriv ρ t)), ?_⟩
    rw [Dcan_apply, Tcan_apply]
    simp only [inner_sub_right, inner_smul_right, hww, mul_one, sub_self, zero_smul, sub_zero,
      mul_zero, zero_add, smul_smul, div_mul_cancel₀ _ hκ]
    module
  · obtain ⟨h, hh⟩ := (Tcan_bijective hw hl0).2 y
    exact ⟨(h, 0), by rw [Dcan_apply, hh, zero_smul, sub_zero]⟩

theorem surjective_mfderiv_cancelΦ {b : Fin m → E} (hb : LinearIndependent ℝ b) {c : ℝ}
    (hc : c ≠ 0) {w : E} (hw : ‖w‖ = 1) {a : ℝ} (ha : 0 < a) {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hρ' : ∀ t, ρ t = 0 → deriv ρ t ≠ 0) (c₀ : E) {l t : ℝ} (hl : l ^ 2 = a ^ 2 * ρ t) :
    Function.Surjective
      (mfderiv (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (cancelΦ hb c w a ρ c₀) (c₀ + l • w, t)) := by
  set G : E × ℝ → E := fun q => cancelG w a ρ (q.1 - c₀, q.2) with hG
  have hG0 : G (c₀ + l • w, t) = 0 := by
    show cancelG w a ρ (c₀ + l • w - c₀, t) = 0
    exact (cancelG_eq_zero_iff hw a ρ _ t).2 ⟨l, by simp, hl⟩
  have hGd : HasMFDerivAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) G (c₀ + l • w, t) (Dcan w a ρ t l) :=
    hasMFDerivAt_prod_of_hasFDerivAt (hasFDerivAt_cancelG_full hw a hρ c₀ t l)
  have hcd : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (collapse hb c) (G (c₀ + l • w, t))
      (c • basisCLM b) := by
    rw [hG0]; exact hasMFDerivAt_collapse_zero hb c
  have hΦ : HasMFDerivAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (cancelΦ hb c w a ρ c₀)
      (c₀ + l • w, t) ((c • basisCLM b).comp (Dcan w a ρ t l)) :=
    hcd.comp (c₀ + l • w, t) hGd
  rw [hΦ.mfderiv]
  have hsc : Surjective (c • basisCLM b) := by
    intro y
    obtain ⟨v, hv⟩ := (basisCLM_bijective hb).2 y
    refine ⟨c⁻¹ • v, ?_⟩
    rw [smul_apply, map_smul, hv, smul_smul, mul_inv_cancel₀ hc, one_smul]
  exact hsc.comp (surjective_Dcan hw ha hρ' hl)

/-! ### Time independence and the transition function -/

theorem cancelΦ_congr_time {b : Fin m → E} (hb : LinearIndependent ℝ b) (c : ℝ) (w : E) (a : ℝ)
    {ρ : ℝ → ℝ} (c₀ : E) {t t' : ℝ} (h : ρ t = ρ t') (s : E) :
    cancelΦ hb c w a ρ c₀ (s, t) = cancelΦ hb c w a ρ c₀ (s, t') := by
  simp [cancelΦ, cancelG, h]

theorem exists_rho {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧ (∀ t, t ≤ ε → ρ t = 1) ∧ (∀ t, 1 - ε ≤ t → ρ t = -1) ∧
      (∀ t, |ρ t| ≤ 1) ∧ ∀ t, ρ t = 0 → deriv ρ t ≠ 0 := by
  obtain ⟨ρ₀, hs, h0, h1, h01, hd⟩ := exists_timeTransition hε hε'
  refine ⟨fun t => 1 - 2 * ρ₀ t, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_const.sub (contDiff_const.mul hs)
  · intro t ht; show 1 - 2 * ρ₀ t = 1; rw [h0 t ht]; norm_num
  · intro t ht; show 1 - 2 * ρ₀ t = -1; rw [h1 t ht]; norm_num
  · intro t; rw [abs_le]; have := h01 t; constructor <;> linarith
  · intro t ht
    simp only at ht
    have hρt : ρ₀ t = 1 / 2 := by linarith
    have hlt : ε < t := by
      by_contra h; push Not at h; have := h0 t h; linarith
    have hlt' : t < 1 - ε := by
      by_contra h; push Not at h; have := h1 t h; linarith
    have hpos := hd t hlt hlt'
    have hdiff : DifferentiableAt ℝ ρ₀ t := (hs.differentiable (by simp)) t
    rw [deriv_const_sub, deriv_const_mul _ hdiff]
    intro h; linarith

end Framed

end Milnor
