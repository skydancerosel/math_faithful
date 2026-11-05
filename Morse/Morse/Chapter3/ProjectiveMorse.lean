import Morse.Chapter3.ProjectiveSpace
import Morse.Homology.MorseHomology
import Morse.Chapter2.CWType

/-!
Milnor, *Morse Theory*, §4, pp. 26–27 (complex projective space) and §5, p. 31 (Corollary 5.4);
Exposition/Chapter3.md, §3 (Proposition B, Corollary C) and §6.

# A Morse function on `ℂPⁿ`, and the homology of `ℂPⁿ`

## Milnor's text, paraphrased

(p. 26) Let `c₀, …, cₙ` be distinct real numbers and `f = Σ_j c_j |z_j|²` on `ℂPⁿ` (the scan
drops the sum and the square).  In the coordinates `x_j + i y_j = (|z₀|/z₀) z_j` on `U₀`,
`f = c₀ + Σ_j (c_j − c₀)(x_j² + y_j²)`, so `p₀ = (1 : 0 : ⋯ : 0)` is the only critical point in
`U₀`, non-degenerate of index twice the number of `j` with `c_j < c₀`; likewise on each `U_k`.
Hence `f` has exactly one critical point of each index `0, 2, 4, …, 2n`.  (p. 27) By Theorem 3.5,
`ℂPⁿ` has the homotopy type of a CW complex `e⁰ ∪ e² ∪ ⋯ ∪ e²ⁿ`, and its integral homology is
`ℤ` in the even dimensions `≤ 2n`, `0` otherwise.  (p. 31) Corollary 5.4 gives the homology of
`ℂPⁿ` without Theorem 3.5.

## What is formalized

`ℂPⁿ` is `Morse.grassmannian (Fin (n + 1)) 1` (`Morse/Chapter3/ProjectiveSpace.lean`) and
Milnor's `f` is `Morse.CP.height c : P ↦ Σ_j c_j Re P_jj` restricted to it (`|z_j|² = P_jj`).

* `Morse.CP.height_param`: **Milnor's formula** `f = c_k + Σ_{j ≠ k}(c_j − c_k)(x_j² + y_j²)` on
  `U_k` (`Morse.CP.model`).
* `Morse.CP.isCriticalPointM_height_iff`: **Proposition B, critical points**: for distinct `c_j`
  the critical points of `f` are exactly the points `p_k = param k 0`, the projections
  `Matrix.single k k 1` onto the coordinate axes (`Morse.CP.param_zero`).
* `Morse.CP.isNondegenerate_indexM_height`: **`p_k` is non-degenerate of index
  `2 #{j : c_j < c_k}`** (`Morse.CP.rank`); `Morse.CP.isNondegenerate_of_isCriticalPointM`:
  `f` is a Morse function.
* `Morse.CP.bijective_rank`, `Morse.CP.critCount_height`: **`C_λ = 1` for `λ = 0, 2, …, 2n` and
  `C_λ = 0` otherwise.**
* `Morse.CP.exists_cells`: **Theorem 3.5 for `ℂPⁿ`**, the homotopy type of an iterated
  adjunction space with one cell in each even dimension `≤ 2n` (from `Morse.theorem_3_5_count'`).
* `Morse.CP.bettiNumber_eq`, `Morse.bettiNumber_complexProjectiveSpace`: **the homology of `ℂPⁿ`
  over any field**, `dim H_λ(ℂPⁿ; 𝕜) = 1` for `λ = 0, 2, …, 2n` and `0` otherwise, by the
  lacunary principle (Corollary 5.4, `Morse.Homology.bettiNumber_eq_critCount_of_lacunary`).

## What Milnor leaves implicit

* **The formula for `f`.**  The scan of p. 26 prints `f = c_j |z_j|`; the coordinate formula
  shows that `Σ_j c_j |z_j|²` is meant (as in Exposition/Chapter3.md).
* **Critical points, Hessian and index in a chart.**  "The only critical point in `U₀`" and the
  index are read off the coordinate expression; this uses that critical points, non-degeneracy
  and the index may be computed in any slice parametrization
  (`Morse.isCriticalPointM_comp_val_iff_sliceParam`, `Morse.index_hessian_comp_sliceParam`).
  Here the parametrization at `q ∈ U_k` is `z ↦ param k (coord k q + z)`, so the computation is
  that of the quadratic polynomial `Morse.CP.model` at `coord k q`
  (`Morse.CP.crit_index_of_mem`).
* **The count `C_λ`.**  That one gets exactly one critical point of each even index uses that
  `k ↦ #{j : c_j < c_k}` is a bijection of `{0, …, n}` (`Morse.CP.bijective_rank`), Milnor's
  implicit "renumber so that `c₀ < ⋯ < cₙ`".
* **Integral homology is not formalized**: the project's homology results are over fields, and
  Milnor's passage to `H_*(ℂPⁿ; ℤ)` (cellular homology, or the lacunary argument with integer
  coefficients, Proposition G of the exposition) is not done.
-/

open Matrix Set Filter Topology Function Module
open scoped ContDiff Manifold Morse.MatrixInner

noncomputable section

namespace Morse

namespace CP

variable {n : ℕ} (c : Fin (n + 1) → ℝ)

/-- **Milnor's function** `f = Σ c_j |z_j|²` on `ℂPⁿ` (p. 26), as `Σ c_j Re P_jj` on matrices. -/
def height (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : ℝ := ∑ j, c j * (P j j).re

theorem contDiff_height : ContDiff ℝ ∞ (height c) := by
  unfold height
  refine ContDiff.sum fun j _ => contDiff_const.mul ?_
  exact Complex.reCLM.contDiff.comp (contDiff_entry (𝕜 := ℂ) j j)

/-- The weights `c_j − c_k` of `f` in the coordinates on `U_k`. -/
def weight (k : Fin (n + 1)) (p : Fin n × Fin 2) : ℝ := c (k.succAbove p.1) - c k

/-- The diagonal bilinear form `(v, w) ↦ Σ_p w_p v_p u_p` on `ℝ²ⁿ`. -/
def wform (w : Fin n × Fin 2 → ℝ) : Model n →L[ℝ] Model n →L[ℝ] ℝ :=
  ∑ p, w p • (ContinuousLinearMap.proj p : Model n →L[ℝ] ℝ).smulRight
    (ContinuousLinearMap.proj p : Model n →L[ℝ] ℝ)

theorem wform_apply (w : Fin n × Fin 2 → ℝ) (v u : Model n) :
    wform w v u = ∑ p, w p * v p * u p := by
  simp [wform, mul_assoc]

/-- `f` in the coordinates on `U_k`: `c_k + Σ_{j ≠ k} (c_j − c_k)(x_j² + y_j²)`. -/
def model (k : Fin (n + 1)) (z : Model n) : ℝ := c k + wform (weight c k) z z

theorem height_param (k : Fin (n + 1)) {z : Model n} (hz : nsq z ≤ 1) :
    height c (param k z) = model c k z := by
  have hd : ∀ a, (param k z a a).re = Complex.normSq (vec k z a) := fun a => by
    simp only [param, of_apply, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
  have hr : ∑ p : Fin n × Fin 2, weight c k p * z p * z p =
      ∑ i, (c (k.succAbove i) - c k) * Complex.normSq (cz z i) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.sum_univ_two, weight, cz, Complex.normSq_mk]
    ring
  simp only [height, hd, model, wform_apply, hr]
  rw [Fin.sum_univ_succAbove _ k]
  simp only [vec, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, Complex.normSq_ofReal,
    Real.mul_self_sqrt (sub_nonneg.2 hz)]
  rw [nsq_eq, mul_sub, mul_one, Finset.mul_sum]
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

theorem hasFDerivAt_model (k : Fin (n + 1)) (z : Model n) :
    HasFDerivAt (model c k) (wform (weight c k) z + (wform (weight c k)).flip z) z := by
  have h := (wform (weight c k)).hasFDerivAt_of_bilinear (hasFDerivAt_id z) (hasFDerivAt_id z)
  have heq : (wform (weight c k)).precompR (Model n) (id z) (ContinuousLinearMap.id ℝ _) +
      (wform (weight c k)).precompL (Model n) (ContinuousLinearMap.id ℝ _) (id z) =
      wform (weight c k) z + (wform (weight c k)).flip z := by
    ext v; simp
  rw [heq] at h
  exact h.const_add (c k)

theorem hessian_model (k : Fin (n + 1)) (z v u : Model n) :
    hessian (model c k) z v u = 2 * ∑ p, weight c k p * v p * u p := by
  have hc : fderiv ℝ (model c k) = fderiv ℝ (fun w => wform (weight c k) w w) := by
    funext w
    exact fderiv_const_add (c k)
  rw [hessian, hc, ← hessian, hessian_bilinear, wform_apply, wform_apply, two_mul]
  congr 1
  exact Finset.sum_congr rfl fun p _ => by ring

variable {c}

theorem weight_ne_zero (hc : Injective c) (k : Fin (n + 1)) (p : Fin n × Fin 2) :
    weight c k p ≠ 0 := by
  rw [weight, sub_ne_zero]
  exact fun h => Fin.succAbove_ne k p.1 (hc h)

theorem eq_zero_of_forall (hc : Injective c) (k : Fin (n + 1)) {v : Model n}
    (h : ∀ u : Model n, ∑ p, weight c k p * v p * u p = 0) : v = 0 := by
  funext p
  have := h (Pi.single p 1)
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at this
  exact (mul_eq_zero.1 this).resolve_left (weight_ne_zero hc k p)

theorem isCriticalPoint_model_iff (hc : Injective c) (k : Fin (n + 1)) (z : Model n) :
    IsCriticalPoint (model c k) z ↔ z = 0 := by
  constructor
  · intro h
    have h2 := (hasFDerivAt_model c k z).unique h
    refine eq_zero_of_forall hc k fun u => ?_
    have := congrArg (fun T => T u) h2
    simp only [_root_.add_apply, ContinuousLinearMap.flip_apply,
      _root_.zero_apply, wform_apply] at this
    have h3 : ∑ p, weight c k p * z p * u p = ∑ p, weight c k p * u p * z p :=
      Finset.sum_congr rfl fun p _ => by ring
    linarith
  · rintro rfl
    have := hasFDerivAt_model c k 0
    simp only [map_zero, add_zero] at this
    exact this

theorem isNondegenerate_hessian_model (hc : Injective c) (k : Fin (n + 1)) (z : Model n) :
    IsNondegenerate (hessian (model c k) z) := by
  rw [isNondegenerate_iff]
  intro v hv
  refine eq_zero_of_forall hc k fun u => ?_
  have := hv u
  rw [hessian_model] at this
  linarith

/-- The number of `c_j` below `c_k`. -/
def rank (c : Fin (n + 1) → ℝ) (k : Fin (n + 1)) : ℕ := (Finset.univ.filter fun j => c j < c k).card

theorem index_hessian_model (k : Fin (n + 1)) (z : Model n) :
    index (hessian (model c k) z) = 2 * rank c k := by
  have hq : quadForm (hessian (model c k) z) =
      QuadraticMap.weightedSumSquares ℝ (fun p => 2 * weight c k p) := by
    ext v
    simp only [quadForm_apply, hessian_model, QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [index, hq, QuadraticForm.sigNeg_weightedSumSquares]
  have hset : {p : Fin n × Fin 2 | 2 * weight c k p < 0} =
      ↑((Finset.univ.filter fun i : Fin n => c (k.succAbove i) < c k) ×ˢ
        (Finset.univ : Finset (Fin 2))) := by
    ext p
    simp only [weight, Set.mem_ofPred_eq, Finset.coe_product, Finset.coe_filter, Finset.mem_univ,
      true_and, Finset.coe_univ, Set.mem_prod, Set.mem_univ, and_true]
    constructor <;> intro h <;> linarith
  rw [hset, Set.ncard_coe_finset, Finset.card_product, Finset.card_univ, Fintype.card_fin, rank,
    mul_comm]
  congr 1
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succAbove _ k]
  simp

theorem nsq_zero : nsq (0 : Model n) = 0 := by simp [nsq]

theorem vec_zero (k : Fin (n + 1)) : vec k (0 : Model n) = Pi.single k 1 := by
  funext a
  refine Fin.succAboveCases k ?_ (fun i => ?_) a
  · simp [vec, nsq_zero]
  · simp [vec, cz, Fin.succAbove_ne k i, Complex.ext_iff]

/-- The critical point `p_k = (0 : ⋯ : 1 : ⋯ : 0)`, the projection onto the `k`-th axis. -/
theorem param_zero (k : Fin (n + 1)) : param k (0 : Model n) = Matrix.single k k 1 := by
  ext a b
  simp only [param, of_apply, vec_zero, Pi.single_apply, Matrix.single_apply]
  by_cases ha : a = k <;> by_cases hb : b = k <;> simp_all [eq_comm]

theorem param_zero_mem (k : Fin (n + 1)) : param k (0 : Model n) ∈ grassmannian (Fin (n + 1)) 1 :=
  param_mem k (by rw [nsq_zero]; exact zero_le_one)

/-- **The computation on `U_k`**: at `q ∈ U_k`, `q` is critical iff its coordinates vanish, and
then it is non-degenerate of index `2 #{j : c_j < c_k}`. -/
theorem crit_index_of_mem (hc : Injective c) (q : grassmannian (Fin (n + 1)) 1) (k : Fin (n + 1))
    (hk : 0 < ((q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) k k).re) :
    letI := (isSliceSubmanifold (n := n)).chartedSpace
    (IsCriticalPointM (Model n) (height c ∘ Subtype.val) q ↔ coord k q = 0) ∧
      (coord k q = 0 → IsNondegenerate (hessianM (Model n) (height c ∘ Subtype.val) q) ∧
        indexM (Model n) (height c ∘ Subtype.val) q = 2 * rank c k) := by
  let _ := (isSliceSubmanifold (n := n)).chartedSpace
  have hN := isSliceSubmanifold (n := n)
  obtain ⟨σ, hσx, hσ0, hσp⟩ := exists_sliceChart k q.2 hk
  set z₀ := coord k (q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) with hz₀
  have hz₀1 := (nsq_coord_lt_and_param_coord k q.2 hk).1
  have hnear : ∀ᶠ z in 𝓝 (0 : Model n), nsq (z₀ + z) < 1 := by
    have hcont : Continuous fun z : Model n => nsq (z₀ + z) :=
      contDiff_nsq.continuous.comp (continuous_const.add continuous_id)
    have := hcont.continuousAt (x := 0)
    exact this.eventually (gt_mem_nhds (by simpa using hz₀1))
  have hev : height c ∘ sliceParam σ =ᶠ[𝓝 0] fun z => model c k (z₀ + z) := by
    filter_upwards [hσp, hnear] with z hz hz1
    rw [Function.comp_apply, hz, height_param c k hz1.le]
  have hσ1 : (σ.φ (q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).1 = 0 := by rw [hσ0]; rfl
  have hF := contDiff_height c
  have hcrit := isCriticalPointM_comp_val_iff_sliceParam hN σ (q := q) hσx
    (hF.differentiable (by simp) _)
  rw [hσ1] at hcrit
  have htr : HasFDerivAt (fun z => model c k (z₀ + z))
      (wform (weight c k) z₀ + (wform (weight c k)).flip z₀) 0 := by
    have h1 := hasFDerivAt_model c k (z₀ + 0)
    have h2 : HasFDerivAt (fun z : Model n => z₀ + z) (ContinuousLinearMap.id ℝ (Model n)) 0 :=
      (hasFDerivAt_id 0).const_add z₀
    have h3 := h1.comp (0 : Model n) h2
    simp only [add_zero, ContinuousLinearMap.comp_id] at h3
    exact h3
  have hiff : IsCriticalPointM (Model n) (height c ∘ Subtype.val) q ↔ z₀ = 0 := by
    rw [hcrit]
    constructor
    · intro h
      have h' : IsCriticalPoint (fun z => model c k (z₀ + z)) 0 := h.congr_of_eventuallyEq hev.symm
      have hD := htr.unique h'
      have : IsCriticalPoint (model c k) z₀ := by
        have := hasFDerivAt_model c k z₀
        rw [hD] at this
        exact this
      exact (isCriticalPoint_model_iff hc k z₀).1 this
    · intro h0
      have : IsCriticalPoint (fun z => model c k (z₀ + z)) 0 := by
        simp only [h0, zero_add]
        exact (isCriticalPoint_model_iff hc k 0).2 rfl
      exact this.congr_of_eventuallyEq hev
  refine ⟨hiff, fun h0 => ?_⟩
  have hcq := hiff.2 h0
  have hhess : hessian (height c ∘ sliceParam σ) 0 = hessian (model c k) 0 := by
    rw [hessian_congr hev]
    simp only [h0, zero_add]
  have hnd := isNondegenerate_hessian_comp_sliceParam_iff hN σ hσx
    (hF.contDiffAt.of_le (by norm_cast)) hcq
  have hind := index_hessian_comp_sliceParam hN σ hσx (hF.contDiffAt.of_le (by norm_cast)) hcq
  rw [hσ1, hhess] at hnd hind
  exact ⟨hnd.1 (isNondegenerate_hessian_model hc k 0), hind ▸ index_hessian_model k 0⟩

theorem re_param_zero_kk (k : Fin (n + 1)) : 0 < (param k (0 : Model n) k k).re := by
  rw [param_kk k (by rw [nsq_zero]; exact zero_le_one), nsq_zero]; simp

/-- **Proposition B, the critical points** (Milnor p. 26): for distinct `c_j`, the critical points
of `f` are exactly the `n + 1` points `p_k = (0 : ⋯ : 1 : ⋯ : 0)`. -/
theorem isCriticalPointM_height_iff (hc : Injective c) (q : grassmannian (Fin (n + 1)) 1) :
    letI := (isSliceSubmanifold (n := n)).chartedSpace
    IsCriticalPointM (Model n) (height c ∘ Subtype.val) q ↔
      ∃ k, (q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = param k 0 := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := exists_re_diag_pos q.2
    have h0 := (crit_index_of_mem hc q k hk).1.1 h
    refine ⟨k, ?_⟩
    rw [← h0, (nsq_coord_lt_and_param_coord k q.2 hk).2]
  · rintro ⟨k, hk⟩
    have hk' : 0 < ((q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) k k).re := hk ▸ re_param_zero_kk k
    refine (crit_index_of_mem hc q k hk').1.2 ?_
    rw [hk, coord_param k (by rw [nsq_zero]; exact zero_lt_one)]

/-- **Proposition B, the indices** (Milnor p. 26): `p_k` is non-degenerate of index
`2 #{j : c_j < c_k}`. -/
theorem isNondegenerate_indexM_height (hc : Injective c) (k : Fin (n + 1)) :
    letI := (isSliceSubmanifold (n := n)).chartedSpace
    IsNondegenerate (hessianM (Model n) (height c ∘ Subtype.val)
        (⟨param k 0, param_zero_mem k⟩ : grassmannian (Fin (n + 1)) 1)) ∧
      indexM (Model n) (height c ∘ Subtype.val)
        (⟨param k 0, param_zero_mem k⟩ : grassmannian (Fin (n + 1)) 1) = 2 * rank c k :=
  (crit_index_of_mem hc ⟨param k 0, param_zero_mem k⟩ k (re_param_zero_kk k)).2
    (coord_param k (by rw [nsq_zero]; exact zero_lt_one))

/-- **`f` is a Morse function** on `ℂPⁿ`: all its critical points are non-degenerate. -/
theorem isNondegenerate_of_isCriticalPointM (hc : Injective c) (q : grassmannian (Fin (n + 1)) 1) :
    letI := (isSliceSubmanifold (n := n)).chartedSpace
    IsCriticalPointM (Model n) (height c ∘ Subtype.val) q →
      IsNondegenerate (hessianM (Model n) (height c ∘ Subtype.val) q) := by
  intro h
  obtain ⟨k, hk⟩ := (isCriticalPointM_height_iff hc q).1 h
  have hq : q = ⟨param k 0, param_zero_mem k⟩ := Subtype.ext hk
  subst hq
  exact (isNondegenerate_indexM_height hc k).1

theorem rank_lt (k : Fin (n + 1)) : rank c k < n + 1 := by
  have : (Finset.univ.filter fun j => c j < c k) ⊆ Finset.univ.erase k := fun j hj => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact Finset.mem_erase.2 ⟨fun h => by rw [h] at hj; exact lt_irrefl _ hj, Finset.mem_univ _⟩
  have := Finset.card_le_card this
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at this
  exact Nat.lt_succ_of_le (by simpa [rank] using this)

theorem rank_lt_rank {j k : Fin (n + 1)} (h : c j < c k) : rank c j < rank c k := by
  refine Finset.card_lt_card ⟨fun i hi => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi.trans h
  · have := hsub (Finset.mem_filter.2 ⟨Finset.mem_univ j, h⟩)
    simp at this

/-- **The rank `k ↦ #{j : c_j < c_k}` is a bijection of `{0, …, n}`** when the `c_j` are
distinct. -/
theorem bijective_rank (hc : Injective c) :
    Bijective fun k : Fin (n + 1) => (⟨rank c k, rank_lt k⟩ : Fin (n + 1)) := by
  refine Finite.injective_iff_bijective.1 fun j k hjk => ?_
  have h : rank c j = rank c k := congrArg Fin.val hjk
  by_contra hne
  rcases lt_or_gt_of_ne (hc.ne hne) with h' | h'
  · exact (rank_lt_rank h').ne h
  · exact (rank_lt_rank h').ne h.symm

/-- **The Morse numbers of `f`** (Milnor p. 27): `C_λ = 1` for `λ = 0, 2, …, 2n`, else `0`. -/
theorem critCount_height (hc : Injective c) (l : ℕ) :
    letI := (isSliceSubmanifold (n := n)).chartedSpace
    critCount (Model n) (height c ∘ Subtype.val : grassmannian (Fin (n + 1)) 1 → ℝ) l =
      if Even l ∧ l ≤ 2 * n then 1 else 0 := by
  let _ := (isSliceSubmanifold (n := n)).chartedSpace
  set pt : Fin (n + 1) → grassmannian (Fin (n + 1)) 1 := fun k => ⟨param k 0, param_zero_mem k⟩
  have hpt : Injective pt := by
    intro j k hjk
    have h := congrArg (fun q : grassmannian (Fin (n + 1)) 1 => (q : Matrix _ _ ℂ) k k) hjk
    simp only [pt, param_zero, Matrix.single_apply] at h
    by_contra hne
    simp [hne] at h
  have hset : {q : grassmannian (Fin (n + 1)) 1 |
      IsCriticalPointM (Model n) (height c ∘ Subtype.val) q ∧
        indexM (Model n) (height c ∘ Subtype.val) q = l} = pt '' {k | 2 * rank c k = l} := by
    ext q
    constructor
    · rintro ⟨hq, hi⟩
      obtain ⟨k, hk⟩ := (isCriticalPointM_height_iff hc q).1 hq
      have hq' : q = pt k := Subtype.ext hk
      subst hq'
      exact ⟨k, by rw [← hi, (isNondegenerate_indexM_height hc k).2]; rfl, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨(isCriticalPointM_height_iff hc _).2 ⟨k, rfl⟩,
        (isNondegenerate_indexM_height hc k).2.trans hk⟩
  rw [critCount, hset, Set.ncard_image_of_injective _ hpt]
  obtain ⟨hinj, hsurj⟩ := bijective_rank hc
  split_ifs with hl
  · obtain ⟨⟨m, hm⟩, hl2⟩ := hl
    obtain ⟨k, hk⟩ := hsurj ⟨m, by omega⟩
    have hk' : rank c k = m := congrArg Fin.val hk
    rw [Set.ncard_eq_one]
    refine ⟨k, Set.eq_singleton_iff_unique_mem.2 ⟨by simp only [Set.mem_ofPred_eq]; omega,
      fun j hj => hinj (Fin.ext ?_)⟩⟩
    simp only [Set.mem_ofPred_eq] at hj
    simp only
    omega
  · rw [Set.ncard_eq_zero]
    refine Set.eq_empty_of_forall_notMem fun k hk => hl ⟨⟨rank c k, ?_⟩, ?_⟩
    · simp only [Set.mem_ofPred_eq] at hk; omega
    · have := rank_lt (c := c) k
      simp only [Set.mem_ofPred_eq] at hk; omega

theorem lacunary (hc : Injective c) (i : ℕ) :
    letI := (isSliceSubmanifold (n := n)).chartedSpace
    critCount (Model n) (height c ∘ Subtype.val : grassmannian (Fin (n + 1)) 1 → ℝ) i = 0 ∨
      critCount (Model n) (height c ∘ Subtype.val : grassmannian (Fin (n + 1)) 1 → ℝ) (i + 1)
        = 0 := by
  simp only [critCount_height hc]
  rcases Nat.even_or_odd i with h | h
  · right; simp [Nat.even_add_one, h]
  · left; simp [Nat.not_even_iff_odd.2 h]

/-- **The homology of `ℂPⁿ` over any field** (Milnor p. 27 and Corollary 5.4, p. 31):
`H_λ(ℂPⁿ; 𝕜)` is one-dimensional for `λ = 0, 2, …, 2n` and zero otherwise, by the lacunary
principle applied to Milnor's function. -/
theorem bettiNumber_eq (hc : Injective c) {𝕜 : Type} [Field 𝕜] (l : ℕ) :
    Homology.bettiNumber 𝕜 (grassmannian (Fin (n + 1)) 1) l =
      if Even l ∧ l ≤ 2 * n then 1 else 0 := by
  let _ := (isSliceSubmanifold (n := n)).chartedSpace
  rw [Homology.bettiNumber_eq_critCount_of_lacunary isSliceSubmanifold isCompact
    (contDiff_height c) (isNondegenerate_of_isCriticalPointM hc) (Homeomorph.refl _)
    (lacunary hc) l, critCount_height hc]

/-- **Theorem 3.5 for `ℂPⁿ`** (Milnor p. 27): `ℂPⁿ` has the homotopy type of a CW complex
`e⁰ ∪ e² ∪ ⋯ ∪ e²ⁿ`: an iterated adjunction space with one cell in each even dimension `≤ 2n` and
no other cells. -/
theorem exists_cells (hc : Injective c) :
    ∃ cells : List ℕ, IsFiniteCellComplexType (grassmannian (Fin (n + 1)) 1) cells ∧
      ∀ l : ℕ, cells.count l = if Even l ∧ l ≤ 2 * n then 1 else 0 := by
  let _ := (isSliceSubmanifold (n := n)).chartedSpace
  obtain ⟨cells, hcell, hcount⟩ := theorem_3_5_count' isSliceSubmanifold isCompact
    (contDiff_height c) (isNondegenerate_of_isCriticalPointM hc)
  exact ⟨cells, hcell, fun l => (hcount l).trans (critCount_height hc l)⟩

end CP

/-- **The homology of complex projective space over any field** (Milnor pp. 26–27, 31):
`dim H_λ(ℂPⁿ; 𝕜) = 1` for `λ = 0, 2, …, 2n` and `0` otherwise, `ℂPⁿ` being the Hermitian
projections of trace one. -/
theorem bettiNumber_complexProjectiveSpace (n : ℕ) {𝕜 : Type} [Field 𝕜] (l : ℕ) :
    Homology.bettiNumber 𝕜 (grassmannian (Fin (n + 1)) 1) l =
      if Even l ∧ l ≤ 2 * n then 1 else 0 :=
  CP.bettiNumber_eq (c := fun j => (j : ℝ)) (Nat.cast_injective.comp Fin.val_injective) l

end Morse
