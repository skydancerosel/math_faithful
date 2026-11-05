import Morse.Chapter3.EulerChar
import Milnor.Chapter6.EulerSphere

/-!
Milnor, *Morse Theory*, §5, p. 29 (`χ(M) = C₀ - C₁ + ⋯ ± Cₙ`, formula (3)) and §6, Application 2
(pp. 36–37), on the sphere `Sⁿ ⊆ ℝⁿ⁺¹`, `n ≥ 1`; the height function, as in Reeb's theorem
(Theorem 4.1, p. 25).

# The alternating count of critical points on `Sⁿ`

The companion project computes the Euler number of `Sⁿ` (the integer of the Poincaré–Hopf
theorem) to be `1 + (-1)ⁿ` (`Milnor.Sphere.indexSum_sph`; Milnor, *Topology from the
Differentiable Viewpoint*, p. 39).  With the main theorem of `Morse/Chapter3/EulerChar.lean`:

* `Morse.sum_critCount_sph`: **every Morse function on `Sⁿ` has `Σ_λ (-1)^λ C_λ = 1 + (-1)ⁿ`.**

The height function `h(x) = ⟪e, x⟫`, `e` a unit vector, has exactly two critical points, both
non-degenerate: the situation of Reeb's theorem (Theorem 4.1, p. 25).  It is checked directly
against the formula:

* `Morse.isCriticalPointM_heightFun_iff`: its critical points are `e` and `-e`;
* `Morse.hessT_heightFun`: at `q ∈ Sⁿ` its Hessian on `T_qSⁿ = q^⊥` (in the sense of
  `Morse.hessT`) is `-⟪e, q⟫ ⟪·, ·⟫`, read off from the derivative of its gradient field
  `e - ⟪e, x⟫ x` (`Milnor.Sphere.dvr_gradSph_apply`), the field of *Topology from the
  Differentiable Viewpoint*, p. 39;
* `Morse.indexM_heightFun_pos`, `Morse.indexM_heightFun_neg`: the index is `n` at the maximum `e`
  and `0` at the minimum `-e`; `Morse.isMorseFunction_heightFun`: `h` is a Morse function;
* `Morse.critCount_heightFun`: `C₀ = Cₙ = 1` and `C_λ = 0` otherwise, so that
  `Σ_λ (-1)^λ C_λ = 1 + (-1)ⁿ` directly (`Morse.sum_critCount_heightFun`), in agreement with
  `Morse.sum_critCount_sph`.

Conversely, `Morse.IsEulerNumber.eq_sph` recomputes the Euler number of `Sⁿ` by Morse theory, as
in Application 2: every Euler number of `Sⁿ` is `Σ_λ (-1)^λ C_λ` for the height function, that
is, `1 + (-1)ⁿ`.  This uses the index of a gradient field at a non-degenerate critical point
(`Morse.indexN_tangentialGradient`) in place of the companion project's direct evaluation of the
two indices of the field `e - ⟪e, x⟫ x`.

## What Milnor leaves implicit

In the proof of Reeb's theorem (p. 25) the two critical points are "the minimum and maximum
points", and the sets `f⁻¹[0, ε]` and `f⁻¹[1 - ε, 1]` are closed `n`-cells "by 2.2": the indices
`0` at a minimum and `n` at a maximum are used without comment.  For the height function on `Sⁿ`
they are `Morse.indexM_heightFun_neg` and `Morse.indexM_heightFun_pos`, from the Hessian on the
tangent space, `⟪·, ·⟫` at `-e` and `-⟪·, ·⟫` at `e`.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1 + 1))
local notation "𝔻" => EuclideanSpace ℝ (Fin (d + 1))
local notation "𝕊" => Milnor.Sphere.Sph (d + 1)
local notation "hS" => Milnor.Sphere.sphSub (d + 1)
local notation "hSc" => Milnor.Sphere.isCompact_sph (n := d + 1)
local notation "hSne" => Milnor.Sphere.nonempty_sph_set (n := d + 1)

/-! ### Every Morse function on `Sⁿ` -/

/-- **The Euler number of `Sⁿ` is `1 + (-1)ⁿ`** (the companion project's
`Milnor.Sphere.indexSum_sph`; Milnor, *Topology from the Differentiable Viewpoint*, p. 39). -/
theorem isEulerNumber_sph : IsEulerNumber hS hSc hSne (1 + (-1) ^ (d + 1)) :=
  fun v hv hvT _ z hz hzero => Milnor.Sphere.indexSum_sph (Nat.succ_pos d) v hv
    (fun q => (Milnor.Sphere.mem_range_mfd_val_iff q (v q)).1 (hvT q)) z hz hzero

/-- **Formula (3) on the sphere**: every Morse function `f` on `Sⁿ`, `n ≥ 1`, satisfies
`Σ_λ (-1)^λ C_λ = 1 + (-1)ⁿ`. -/
theorem sum_critCount_sph {f : 𝕊 → ℝ} (hf : letI := (hS).chartedSpace; IsMorseFunction 𝔻 f) :
    letI := (hS).chartedSpace
    ∑ k ∈ Finset.range (d + 2), (-1 : ℤ) ^ k * critCount 𝔻 f k = 1 + (-1) ^ (d + 1) :=
  isEulerNumber_sph.sum_critCount_eq hS hSc hSne (Nat.succ_pos d) hf

/-! ### The height function -/

/-- **The height function** `x ↦ ⟪e, x⟫` on `ℝⁿ⁺¹`; on `Sⁿ` it is `heightFun e ∘ Subtype.val`. -/
def heightFun (e : 𝔼) (x : 𝔼) : ℝ := ⟪e, x⟫

theorem contDiff_heightFun (e : 𝔼) : ContDiff ℝ ∞ (heightFun (d := d) e) :=
  (innerSL ℝ e).contDiff

/-- The gradient of the height function is `e`. -/
theorem gradient_heightFun (e x : 𝔼) : gradient (heightFun e) x = e := by
  refine ext_inner_right ℝ fun w => ?_
  rw [← Milnor.fderiv_apply_eq_inner_gradient]
  have h : heightFun e = ⇑(innerSL ℝ e) := rfl
  rw [h, (innerSL ℝ e).fderiv, innerSL_apply_apply]

/-- **The tangential gradient of the height function is Milnor's field** `e - ⟪e, x⟫ x` of p. 39
(`Milnor.Sphere.gradSph`). -/
theorem tangentialGradient_heightFun (e : 𝔼) :
    tangentialGradient hS (heightFun e) = Milnor.Sphere.gradSph e := by
  funext q
  rw [tangentialGradient, gradient_heightFun]
  refine Submodule.eq_starProjection_of_mem_orthogonal (Milnor.Sphere.tangent_gradSph e q) ?_
  rw [Submodule.mem_orthogonal]
  intro u hu
  have hqu : ⟪q.1, u⟫ = 0 := (Milnor.Sphere.mem_range_mfd_val_iff q u).1 hu
  change ⟪u, e - (e - ⟪e, q.1⟫ • q.1)⟫ = 0
  rw [sub_sub_cancel, real_inner_smul_right, real_inner_comm q.1 u, hqu, mul_zero]

variable {e : EuclideanSpace ℝ (Fin (d + 1 + 1))} (he : e ∈ Milnor.Sphere.Sph (d + 1))

include he in
/-- **The critical points of the height function on `Sⁿ` are `e` and `-e`.** -/
theorem isCriticalPointM_heightFun_iff (q : 𝕊) :
    letI := (hS).chartedSpace
    IsCriticalPointM 𝔻 (heightFun e ∘ Subtype.val) q ↔ q.1 = e ∨ q.1 = -e := by
  rw [← tangentialGradient_eq_zero_iff hS ((contDiff_heightFun e).differentiable (by simp) _),
    tangentialGradient_heightFun]
  exact Milnor.Sphere.gradHeight_eq_zero_iff he q.2

/-- **The Hessian of the height function on `T_qSⁿ`**: `-⟪e, q⟫ ⟪t, s⟫`. -/
theorem hessT_heightFun (e : 𝔼) (q : 𝕊) (t s : Milnor.Tub.tanN hS q) :
    hessT hS hSc hSne (heightFun e) q t s = -(⟪e, q.1⟫ * ⟪(t : 𝔼), (s : 𝔼)⟫) := by
  rw [hessT_apply_eq_inner_dvr hS hSc hSne (contDiff_heightFun e), tangentialGradient_heightFun,
    Milnor.Sphere.dvr_gradSph_apply e q t.2]
  have hs : ⟪q.1, (s : 𝔼)⟫ = 0 := (Milnor.Sphere.mem_tanN_iff q s).1 s.2
  rw [inner_neg_left, inner_add_left, real_inner_smul_left, real_inner_smul_left, hs, mul_zero,
    add_zero]

/-- The Hessian of the height function is non-degenerate where `⟪e, q⟫ ≠ 0`. -/
theorem isNondegenerate_hessT_heightFun (e : 𝔼) {q : 𝕊} (hq : ⟪e, q.1⟫ ≠ 0) :
    IsNondegenerate (hessT hS hSc hSne (heightFun e) q) := by
  rw [isNondegenerate_iff]
  intro t ht
  have h := ht t
  rw [hessT_heightFun, neg_eq_zero, mul_eq_zero, real_inner_self_eq_norm_sq] at h
  rcases h with h | h
  · exact absurd h hq
  · exact Subtype.ext (norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h))

include he in
/-- **The height function is a Morse function on `Sⁿ`.** -/
theorem isMorseFunction_heightFun :
    letI := (hS).chartedSpace
    IsMorseFunction 𝔻 (heightFun e ∘ (Subtype.val : 𝕊 → 𝔼)) := by
  let _ := (hS).chartedSpace
  refine ⟨contMDiff_comp_val hS (contDiff_heightFun e), fun q hq => ?_⟩
  refine (isNondegenerate_hessT_iff hS hSc hSne (contDiff_heightFun e) hq).1
    (isNondegenerate_hessT_heightFun e ?_)
  have hee : ⟪e, e⟫ = (1 : ℝ) := Milnor.Sphere.inner_self_eq_one_of_mem he
  rcases (isCriticalPointM_heightFun_iff he q).1 hq with h | h <;> rw [h]
  · rw [hee]; norm_num
  · rw [inner_neg_right, hee]; norm_num

include he in
/-- **The index of the height function at the maximum `e` is `n`.** -/
theorem indexM_heightFun_pos :
    letI := (hS).chartedSpace
    indexM 𝔻 (heightFun e ∘ Subtype.val) (⟨e, he⟩ : 𝕊) = d + 1 := by
  let _ := (hS).chartedSpace
  have hcrit : IsCriticalPointM 𝔻 (heightFun e ∘ Subtype.val) (⟨e, he⟩ : 𝕊) :=
    (isCriticalPointM_heightFun_iff he _).2 (Or.inl rfl)
  have hee : ⟪e, e⟫ = (1 : ℝ) := Milnor.Sphere.inner_self_eq_one_of_mem he
  rw [← index_hessT hS hSc hSne (contDiff_heightFun e) hcrit, index_eq_finrank_of_negDef,
    Milnor.Sphere.finrank_tanN]
  intro t ht
  rw [hessT_heightFun]
  change -(⟪e, e⟫ * ⟪(t : 𝔼), (t : 𝔼)⟫) < 0
  rw [hee, one_mul, neg_lt_zero, real_inner_self_eq_norm_sq]
  exact pow_pos (norm_pos_iff.2 fun h => ht (Subtype.ext h)) 2

include he in
/-- **The index of the height function at the minimum `-e` is `0`.** -/
theorem indexM_heightFun_neg :
    letI := (hS).chartedSpace
    indexM 𝔻 (heightFun e ∘ Subtype.val) (⟨-e, Milnor.Sphere.neg_mem he⟩ : 𝕊) = 0 := by
  let _ := (hS).chartedSpace
  have hcrit : IsCriticalPointM 𝔻 (heightFun e ∘ Subtype.val)
      (⟨-e, Milnor.Sphere.neg_mem he⟩ : 𝕊) :=
    (isCriticalPointM_heightFun_iff he _).2 (Or.inr rfl)
  have hee : ⟪e, e⟫ = (1 : ℝ) := Milnor.Sphere.inner_self_eq_one_of_mem he
  rw [← index_hessT hS hSc hSne (contDiff_heightFun e) hcrit]
  refine index_eq_zero_of_nonneg fun t => ?_
  rw [hessT_heightFun]
  change 0 ≤ -(⟪e, -e⟫ * ⟪(t : 𝔼), (t : 𝔼)⟫)
  rw [inner_neg_right, hee, neg_one_mul, neg_neg]
  exact real_inner_self_nonneg

include he in
/-- **The Morse numbers of the height function on `Sⁿ`**: `C₀ = Cₙ = 1`, all others `0`. -/
theorem critCount_heightFun (k : ℕ) :
    letI := (hS).chartedSpace
    critCount 𝔻 (heightFun e ∘ (Subtype.val : 𝕊 → 𝔼)) k =
      (if k = 0 then 1 else 0) + (if k = d + 1 then 1 else 0) := by
  let _ := (hS).chartedSpace
  set A : 𝕊 := ⟨e, he⟩ with hA
  set B : 𝕊 := ⟨-e, Milnor.Sphere.neg_mem he⟩ with hB
  have hAB : A ≠ B := by
    intro h
    have h1 : e = -e := congrArg Subtype.val h
    have hee : ⟪e, e⟫ = (1 : ℝ) := Milnor.Sphere.inner_self_eq_one_of_mem he
    have h2 : ⟪e, -e⟫ = (1 : ℝ) := by rw [← h1]; exact hee
    rw [inner_neg_right, hee] at h2
    norm_num at h2
  have hcrit : ∀ q, IsCriticalPointM 𝔻 (heightFun e ∘ Subtype.val) q ↔ q = A ∨ q = B := by
    intro q
    rw [isCriticalPointM_heightFun_iff he, hA, hB, Subtype.ext_iff, Subtype.ext_iff]
  have hiA := indexM_heightFun_pos he
  have hiB := indexM_heightFun_neg he
  rw [← hA] at hiA
  rw [← hB] at hiB
  unfold critCount
  by_cases h0 : k = 0
  · subst h0
    have hset : {q : 𝕊 | IsCriticalPointM 𝔻 (heightFun e ∘ Subtype.val) q ∧
        indexM 𝔻 (heightFun e ∘ Subtype.val) q = 0} = {B} := by
      ext q
      simp only [mem_ofPred_eq, mem_singleton_iff, hcrit]
      constructor
      · rintro ⟨hq | hq, hi⟩
        · rw [hq, hiA] at hi; exact absurd hi (Nat.succ_ne_zero d)
        · exact hq
      · rintro rfl; exact ⟨Or.inr rfl, hiB⟩
    rw [hset, ncard_singleton]
    simp
  · by_cases h1 : k = d + 1
    · subst h1
      have hset : {q : 𝕊 | IsCriticalPointM 𝔻 (heightFun e ∘ Subtype.val) q ∧
          indexM 𝔻 (heightFun e ∘ Subtype.val) q = d + 1} = {A} := by
        ext q
        simp only [mem_ofPred_eq, mem_singleton_iff, hcrit]
        constructor
        · rintro ⟨hq | hq, hi⟩
          · exact hq
          · rw [hq, hiB] at hi; exact absurd hi.symm (Nat.succ_ne_zero d)
        · rintro rfl; exact ⟨Or.inl rfl, hiA⟩
      rw [hset, ncard_singleton]
      simp
    · have hset : {q : 𝕊 | IsCriticalPointM 𝔻 (heightFun e ∘ Subtype.val) q ∧
          indexM 𝔻 (heightFun e ∘ Subtype.val) q = k} = ∅ := by
        ext q
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, hcrit]
        rintro (rfl | rfl)
        · rw [hiA]; exact Ne.symm h1
        · rw [hiB]; exact Ne.symm h0
      rw [hset, ncard_empty, if_neg h0, if_neg h1]

include he in
/-- **Formula (3) for the height function, computed from its critical points**:
`Σ_λ (-1)^λ C_λ = 1 + (-1)ⁿ`, from `C₀ = Cₙ = 1` alone (no Poincaré–Hopf), in agreement with
`Morse.sum_critCount_sph`. -/
theorem sum_critCount_heightFun :
    letI := (hS).chartedSpace
    ∑ k ∈ Finset.range (d + 2),
        (-1 : ℤ) ^ k * critCount 𝔻 (heightFun e ∘ (Subtype.val : 𝕊 → 𝔼)) k =
      1 + (-1) ^ (d + 1) := by
  let _ := (hS).chartedSpace
  simp_rw [critCount_heightFun he]
  push_cast
  simp only [mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_range]
  simp

include he in
/-- **The Euler number of `Sⁿ`, recomputed by Morse theory**: any Euler number of `Sⁿ` (the
integer of the Poincaré–Hopf theorem) is `Σ_λ (-1)^λ C_λ` for the height function, that is,
`1 + (-1)ⁿ`.  (The companion project's `Milnor.Sphere.eq_of_indexSum_sph` evaluates the two
indices of Milnor's field directly instead.) -/
theorem IsEulerNumber.eq_sph {χ : ℤ} (hχ : IsEulerNumber hS hSc hSne χ) :
    χ = 1 + (-1) ^ (d + 1) := by
  rw [hχ.eq_sum_critCount hS hSc hSne (Nat.succ_pos d) (isMorseFunction_heightFun he),
    sum_critCount_heightFun he]

end Morse
