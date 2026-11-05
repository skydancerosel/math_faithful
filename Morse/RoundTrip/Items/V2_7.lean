import Morse
import RoundTrip.Check
import RoundTrip.Blind.V2_7

open Set Metric
open scoped ContDiff Manifold

noncomputable section

namespace RoundTrip.V2_7

/-- The project's statement (the pushout lemmas for a cell meeting a closed set in its boundary),
universe instantiated at `0`. -/
def A : Prop :=
  (type_of% @Morse.isPushout_of_cell.{0}) ∧ (type_of% @Morse.exists_isPushout_union_cell.{0}) ∧
  (type_of% @Morse.exists_isPushout_union_cell_of_t2.{0}) ∧
  (type_of% @Morse.exists_homotopyEquiv_pushout_of_cell.{0})

theorem A_holds : A :=
  ⟨@Morse.isPushout_of_cell.{0}, @Morse.exists_isPushout_union_cell.{0},
    @Morse.exists_isPushout_union_cell_of_t2.{0}, @Morse.exists_homotopyEquiv_pushout_of_cell.{0}⟩

/-! ### `B` holds outright (elementary coordinate geometry in the Morse chart) -/

section Coord

variable {n l : ℕ} (hl : l ≤ n)

/-- `ℝ^l → ℝⁿ`, padding with zeros. -/
def pad (z : EuclideanSpace ℝ (Fin l)) : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm fun i => if h : i.val < l then z ⟨i.val, h⟩ else 0

include hl in
/-- `ℝⁿ → ℝ^l`, the first `l` coordinates. -/
def proj (u : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin l) :=
  (EuclideanSpace.equiv (Fin l) ℝ).symm fun j => u ⟨j.val, lt_of_lt_of_le j.2 hl⟩

theorem pad_apply (z : EuclideanSpace ℝ (Fin l)) (i : Fin n) :
    pad (n := n) z i = if h : i.val < l then z ⟨i.val, h⟩ else 0 := rfl

theorem proj_apply (u : EuclideanSpace ℝ (Fin n)) (j : Fin l) :
    proj hl u j = u ⟨j.val, lt_of_lt_of_le j.2 hl⟩ := rfl

theorem continuous_pad : Continuous (pad (n := n) (l := l)) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.comp (continuous_pi fun i => by
    by_cases h : i.val < l
    · simp only [h, dif_pos]; exact (EuclideanSpace.proj (𝕜 := ℝ) _).continuous
    · simp only [h, dif_neg, not_false_eq_true]; exact continuous_const)

theorem continuous_proj : Continuous (proj hl) :=
  (EuclideanSpace.equiv (Fin l) ℝ).symm.continuous.comp
    (continuous_pi fun _ => (EuclideanSpace.proj (𝕜 := ℝ) _).continuous)

/-- Sums over the first `l` coordinates. -/
theorem sum_lt (g : Fin n → ℝ) :
    ∑ i : Fin n with i.val < l, g i = ∑ j : Fin l, g (Fin.castLE hl j) := by
  have : (Finset.univ.filter fun i : Fin n => i.val < l) =
      Finset.univ.map (Fin.castLEEmb hl) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb_apply]
    exact ⟨fun h => ⟨⟨i.val, h⟩, rfl⟩, fun ⟨j, hj⟩ => hj ▸ j.2⟩
  rw [this, Finset.sum_map]
  rfl

theorem norm_sq_eq (z : EuclideanSpace ℝ (Fin l)) : ‖z‖ ^ 2 = ∑ j, z j ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

include hl in
theorem xi_pad (z : EuclideanSpace ℝ (Fin l)) : xi l (pad (n := n) z) = ‖z‖ ^ 2 := by
  rw [xi, sum_lt hl, norm_sq_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pad_apply, dif_pos (by simp)]
  rfl

omit hl in
theorem pad_eq_zero (z : EuclideanSpace ℝ (Fin l)) (i : Fin n) (hi : l ≤ i.val) :
    pad (n := n) z i = 0 := by
  rw [pad_apply, dif_neg (by omega)]

include hl in
theorem norm_pad (z : EuclideanSpace ℝ (Fin l)) : ‖pad (n := n) z‖ = ‖z‖ := by
  have h1 : ‖pad (n := n) z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [norm_sq_eq, ← xi_pad hl, xi]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => i.val < l)]
    have : ∑ i : Fin n with ¬ i.val < l, pad (n := n) z i ^ 2 = 0 :=
      Finset.sum_eq_zero fun i hi => by
        rw [pad_eq_zero z i (by simpa using (Finset.mem_filter.1 hi).2)]; ring
    rw [this, add_zero]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1

theorem sq_norm_proj (u : EuclideanSpace ℝ (Fin n)) : ‖proj hl u‖ ^ 2 = xi l u := by
  rw [norm_sq_eq, xi, sum_lt hl]
  rfl

theorem pad_proj (u : EuclideanSpace ℝ (Fin n)) (hu : ∀ i : Fin n, l ≤ i.val → u i = 0) :
    pad (proj hl u) = u := by
  ext i
  rw [pad_apply]
  split_ifs with h
  · rfl
  · exact (hu i (by omega)).symm

theorem proj_pad (z : EuclideanSpace ℝ (Fin l)) : proj hl (pad (n := n) z) = z := by
  ext j
  rw [proj_apply, pad_apply, dif_pos j.2]

theorem eta_eq_zero (u : EuclideanSpace ℝ (Fin n)) (hu : ∀ i : Fin n, l ≤ i.val → u i = 0) :
    eta l u = 0 :=
  Finset.sum_eq_zero fun i hi => by
    rw [hu i (Finset.mem_filter.1 hi).2]; ring

end Coord

theorem B_holds : B := by
  intro n M _ _ _ _ f p hf hp y hpy hy0 hfy
  set l := Morse.indexM (EuclideanSpace ℝ (Fin n)) f p with hl_def
  have hl : l ≤ n := by
    have := Morse.indexM_le_finrank (E := EuclideanSpace ℝ (Fin n)) f p
    rwa [finrank_euclideanSpace_fin] at this
  let e := y.toOpenPartialHomeomorph
  have he : ∀ x, e x = y x := fun _ => rfl
  -- a ball around `0 = y p` inside the target
  have h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ e.target := hy0 ▸ e.map_source hpy
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 e.open_target 0 h0
  refine ⟨(r / 2) ^ 2, by positivity, fun ε hε hεr => ⟨?_, ?_⟩⟩
  · -- `e^λ ∩ M^{c-ε} = ė^λ`: on `e^λ`, `η = 0`, so `f = c - ξ`
    ext q
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨hq, hfq⟩
      refine ⟨hq, le_antisymm hq.2.2 ?_⟩
      rw [hfy q hq.1, eta_eq_zero _ hq.2.1] at hfq
      linarith
    · rintro ⟨hq, hxi⟩
      refine ⟨hq, ?_⟩
      rw [hfy q hq.1, eta_eq_zero _ hq.2.1, hxi]
      linarith
  · -- the homeomorphism `e^λ ≃ₜ` unit ball of `ℝ^λ`
    have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
    have hsr : Real.sqrt ε < r := by
      have : Real.sqrt ε < r / 2 := by
        rw [Real.sqrt_lt' (by positivity)]; exact hεr
      linarith
    -- the inverse map lands in the target
    have hpadT : ∀ z : EuclideanSpace ℝ (Fin l), ‖z‖ ≤ 1 →
        pad (n := n) (Real.sqrt ε • z) ∈ e.target := by
      intro z hz
      apply hball
      rw [mem_ball_zero_iff, norm_pad hl, norm_smul, Real.norm_of_nonneg hsε.le]
      calc Real.sqrt ε * ‖z‖ ≤ Real.sqrt ε * 1 := by gcongr
        _ < r := by rw [mul_one]; exact hsr
    have hxi_le : ∀ q ∈ eCell y l ε, ‖proj hl (y q)‖ ≤ Real.sqrt ε := by
      intro q hq
      rw [← Real.sqrt_sq (norm_nonneg _), sq_norm_proj]
      exact Real.sqrt_le_sqrt hq.2.2
    let toF : eCell y l ε → Cell l := fun q =>
      ⟨(Real.sqrt ε)⁻¹ • proj hl (y q.1), by
        rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hsε.le,
          inv_mul_le_iff₀ hsε, mul_one]
        exact hxi_le q.1 q.2⟩
    let invF : Cell l → eCell y l ε := fun z =>
      ⟨e.symm (pad (Real.sqrt ε • z.1)), by
        have hT := hpadT z.1 (mem_closedBall_zero_iff.1 z.2)
        have hyy : y (e.symm (pad (Real.sqrt ε • z.1))) = pad (Real.sqrt ε • z.1) :=
          e.right_inv hT
        refine ⟨e.map_target hT, fun i hi => ?_, ?_⟩
        · rw [hyy]; exact pad_eq_zero _ i hi
        · rw [hyy, xi_pad hl, norm_smul, Real.norm_of_nonneg hsε.le, mul_pow,
            Real.sq_sqrt hε.le]
          have := mem_closedBall_zero_iff.1 z.2
          have h1 : ‖z.1‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z.1]
          nlinarith⟩
    have hc_to : Continuous toF := by
      have h1 : Continuous fun q : eCell y l ε => e q.1 :=
        e.continuousOn.comp_continuous continuous_subtype_val fun q => q.2.1
      have h2 : Continuous fun q : eCell y l ε => (Real.sqrt ε)⁻¹ • proj hl (e q.1) :=
        (continuous_const_smul _).comp ((continuous_proj hl).comp h1)
      exact h2.subtype_mk _
    have hc_inv : Continuous invF := by
      have h3 : Continuous fun z : Cell l => pad (n := n) (Real.sqrt ε • z.1) :=
        continuous_pad.comp ((continuous_const_smul _).comp continuous_subtype_val)
      exact (e.continuousOn_symm.comp_continuous h3
        fun z => hpadT z.1 (mem_closedBall_zero_iff.1 z.2)).subtype_mk _
    let h : eCell y l ε ≃ₜ Cell l :=
      { toFun := toF
        invFun := invF
        left_inv := fun q => by
          apply Subtype.ext
          change e.symm (pad (Real.sqrt ε • ((Real.sqrt ε)⁻¹ • proj hl (y q.1)))) = q.1
          rw [smul_inv_smul₀ hsε.ne', pad_proj hl _ q.2.2.1]
          exact e.left_inv q.2.1
        right_inv := fun z => by
          apply Subtype.ext
          change (Real.sqrt ε)⁻¹ • proj hl (y (e.symm (pad (Real.sqrt ε • z.1)))) = z.1
          rw [show y (e.symm (pad (Real.sqrt ε • z.1))) = pad (Real.sqrt ε • z.1) from
            e.right_inv (hpadT z.1 (mem_closedBall_zero_iff.1 z.2)), proj_pad,
            inv_smul_smul₀ hsε.ne']
        continuous_toFun := hc_to
        continuous_invFun := hc_inv }
    refine ⟨h, fun q => ?_⟩
    change ‖(Real.sqrt ε)⁻¹ • proj hl (y q.1)‖ = 1 ↔ _
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hsε.le, inv_mul_eq_one₀ hsε.ne',
      ← Real.sqrt_sq (norm_nonneg (proj hl (y q.1))), sq_norm_proj]
    constructor
    · intro h1
      have := congrArg (· ^ 2) h1
      rwa [Real.sq_sqrt hε.le, Real.sq_sqrt (by rw [← sq_norm_proj hl]; positivity),
        eq_comm] at this
    · intro h1
      rw [h1]

theorem A_to_B : A → B := fun _ => B_holds

/-! `B ⇒ A` is not proved: `A` consists of general-topology lemmas (a closed set `A ⊆ W` with a
cell `χ` meeting it exactly in its boundary sphere gives a pushout square in `TopCat`; the
homotopy-equivalence corollary). `B` is Milnor's coordinate statement in a Morse chart and says
nothing about pushouts: these are exactly the part Milnor "does not argue" (V2_7's text), and
`B` explicitly does not formalise it. -/

#rt_check RoundTrip.V2_7.A_to_B [Morse.isPushout_of_cell, Morse.exists_isPushout_union_cell,
  Morse.exists_isPushout_union_cell_of_t2, Morse.exists_homotopyEquiv_pushout_of_cell]

end RoundTrip.V2_7

end
