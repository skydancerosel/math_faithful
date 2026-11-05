import Milnor.Chapter7.ProdNbhdS
import Milnor.Chapter7.TubeData
import Milnor.Chapter7.Identify

/-!
# The map of a framed cobordism, part A (Milnor §7, proof of Theorem A, second half)

For a framed cobordism `S ⊆ M × ℝ` we set up the tube map `G_S` with a clamp shared with the
two ends, the formulas of `G_S` on the product ends, a bound on the time shift, compactness
of `S ∩ (M × [a, b])`, and a uniform injectivity radius (using the tube data of the ends outside
a compact piece).
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace Classical

noncomputable section

namespace Milnor

open Sphere

namespace Framed

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  {hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M} (hMc : IsCompact M) (hne : M.Nonempty)
  {n p : ℕ} {F₀ F₁ : FramedSub hM n p} (X : FramedCob hM F₀ F₁)

/-! ### The ends -/

theorem mem_S_end0 (x : F₀.N) {t : ℝ} (ht : t < X.ε) : (x.1, t) ∈ X.S := (X.end0 (x.1, t) ht).2 x.2
theorem mem_S_end1 (x : F₁.N) {t : ℝ} (ht : 1 - X.ε < t) : (x.1, t) ∈ X.S :=
  (X.end1 (x.1, t) ht).2 x.2
theorem fst_mem_N0 (q : X.S) (hq : q.1.2 < X.ε) : q.1.1 ∈ F₀.N := (X.end0 q.1 hq).1 q.2
theorem fst_mem_N1 (q : X.S) (hq : 1 - X.ε < q.1.2) : q.1.1 ∈ F₁.N := (X.end1 q.1 hq).1 q.2

/-- On the end `t < ε`, the tube map of `S` is the tube map of `N₀` times the identity. -/
theorem GxS_end0 (lam : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (q : X.S)
    (hq : q.1.2 < X.ε) (s : EuclideanSpace ℝ (Fin p)) :
    GxS hMc hne X lam (q, s) = (Gx hMc hne F₀ lam (⟨q.1.1, fst_mem_N0 X q hq⟩, s), q.1.2) := by
  have hu : ∀ i, X.u i q = (F₀.v i ⟨q.1.1, fst_mem_N0 X q hq⟩, 0) := fun i =>
    X.u_end0 i q (fst_mem_N0 X q hq) hq
  unfold GxS GambS Gx Gamb
  simp only [hu, Prod.smul_mk, smul_zero, Prod.fst_add, Prod.snd_add, Prod.fst_sum, Prod.snd_sum,
    Finset.sum_const_zero, add_zero]
  rfl

/-- On the end `1 - ε < t`, the tube map of `S` is the tube map of `N₁` times the identity. -/
theorem GxS_end1 (lam : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (q : X.S)
    (hq : 1 - X.ε < q.1.2) (s : EuclideanSpace ℝ (Fin p)) :
    GxS hMc hne X lam (q, s) = (Gx hMc hne F₁ lam (⟨q.1.1, fst_mem_N1 X q hq⟩, s), q.1.2) := by
  have hu : ∀ i, X.u i q = (F₁.v i ⟨q.1.1, fst_mem_N1 X q hq⟩, 0) := fun i =>
    X.u_end1 i q (fst_mem_N1 X q hq) hq
  unfold GxS GambS Gx Gamb
  simp only [hu, Prod.smul_mk, smul_zero, Prod.fst_add, Prod.snd_add, Prod.fst_sum, Prod.snd_sum,
    Finset.sum_const_zero, add_zero]
  rfl

/-! ### Bounds -/

theorem bound_v0_of_bound_u {C : ℝ} (hC : ∀ i q, ‖X.u i q‖ ≤ C) (i : Fin p) (x : F₀.N) :
    ‖F₀.v i x‖ ≤ C := by
  have hq : (x.1, (0 : ℝ)) ∈ X.S := mem_S_end0 X x X.hε
  have h1 := X.u_end0 i ⟨(x.1, 0), hq⟩ x.2 X.hε
  have h2 := hC i ⟨(x.1, 0), hq⟩
  rw [h1] at h2
  exact (norm_fst_le _).trans h2

theorem bound_v1_of_bound_u {C : ℝ} (hC : ∀ i q, ‖X.u i q‖ ≤ C) (i : Fin p) (x : F₁.N) :
    ‖F₁.v i x‖ ≤ C := by
  have hq : (x.1, (1 : ℝ)) ∈ X.S := mem_S_end1 X x (by linarith [X.hε])
  have h1 := X.u_end1 i ⟨(x.1, 1), hq⟩ x.2 (by linarith [X.hε])
  have h2 := hC i ⟨(x.1, 1), hq⟩
  rw [h1] at h2
  exact (norm_fst_le _).trans h2

/-- The time shift of the tube map is small. -/
theorem abs_snd_GxS_sub_le {C : ℝ} (hC : ∀ i q, ‖X.u i q‖ ≤ C)
    (lam : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (q : X.S × EuclideanSpace ℝ (Fin p)) :
    |(GxS hMc hne X lam q).2 - q.1.1.2| ≤ p * (‖lam q.2‖ * C) := by
  have h1 : (GxS hMc hne X lam q).2 - q.1.1.2 = (∑ i, (lam q.2) i • X.u i q.1).2 := by
    simp [GxS, GambS, embS, embXR]
  rw [h1, ← Real.norm_eq_abs]
  calc ‖(∑ i, (lam q.2) i • X.u i q.1).2‖ ≤ ‖∑ i, (lam q.2) i • X.u i q.1‖ := norm_snd_le _
    _ ≤ p * (‖lam q.2‖ * C) := norm_sum_smul_le' X hC _ _

/-! ### Compactness of the finite-time piece -/

theorem isCompact_S_Icc {a b : ℝ} (ha : a ≤ 0) (hb : 1 ≤ b) :
    IsCompact {q ∈ X.S | a ≤ q.2 ∧ q.2 ≤ b} := by
  have hset : {q ∈ X.S | a ≤ q.2 ∧ q.2 ≤ b} =
      (F₀.N ×ˢ Icc a 0) ∪ ({q ∈ X.S | 0 ≤ q.2 ∧ q.2 ≤ 1} ∪ (F₁.N ×ˢ Icc 1 b)) := by
    ext q
    simp only [mem_setOf_eq, mem_union, mem_prod, mem_Icc]
    constructor
    · rintro ⟨hq, h1, h2⟩
      by_cases h0 : q.2 ≤ 0
      · exact Or.inl ⟨(X.end0 q (by linarith [X.hε])).1 hq, h1, h0⟩
      · by_cases h1' : q.2 ≤ 1
        · exact Or.inr (Or.inl ⟨hq, by linarith, h1'⟩)
        · exact Or.inr (Or.inr ⟨(X.end1 q (by linarith [X.hε])).1 hq, by linarith, h2⟩)
    · rintro (⟨hN, h1, h2⟩ | ⟨hq, h1, h2⟩ | ⟨hN, h1, h2⟩)
      · exact ⟨(X.end0 q (by linarith [X.hε])).2 hN, h1, by linarith⟩
      · exact ⟨hq, by linarith, by linarith⟩
      · exact ⟨(X.end1 q (by linarith [X.hε])).2 hN, by linarith, h2⟩
  rw [hset]
  exact (F₀.compact.prod isCompact_Icc).union (X.compact.union (F₁.compact.prod isCompact_Icc))

/-! ### Injectivity at the ends -/

section inj

variable {lam : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)} {a₀ : ℝ}
  (hlam_id : ∀ t, ‖t‖ ≤ a₀ → lam t = t) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i q, ‖X.u i q‖ ≤ C)
  (T₀ : TubeData hMc hne F₀) (hT₀ : T₀.lam = lam) (T₁ : TubeData hMc hne F₁) (hT₁ : T₁.lam = lam)
  {ε₀ : ℝ} (hε₀a : ε₀ ≤ a₀) (hε₀0 : ε₀ ≤ T₀.ε) (hε₀1 : ε₀ ≤ T₁.ε) (hε₀C : p * (ε₀ * C) < X.ε / 4)

include hlam_id hC0 hC hT₀ hε₀a hε₀0 hε₀C in
/-- Injectivity when the first point lies deep in the end `t < ε`. -/
theorem eq_of_GxS_eq_end0 (q q' : X.S × EuclideanSpace ℝ (Fin p)) (hq : ‖q.2‖ < ε₀)
    (hq' : ‖q'.2‖ < ε₀) (ht : q.1.1.2 < X.ε - X.ε / 2)
    (h : GxS hMc hne X lam q = GxS hMc hne X lam q') : q = q' := by
  have hb : ∀ (r : X.S × EuclideanSpace ℝ (Fin p)), ‖r.2‖ < ε₀ →
      |(GxS hMc hne X lam r).2 - r.1.1.2| < X.ε / 4 := by
    intro r hr
    have h1 : ‖lam r.2‖ ≤ ε₀ := by rw [hlam_id _ (hr.le.trans hε₀a)]; exact hr.le
    have h2 := abs_snd_GxS_sub_le hMc hne X hC lam r
    have h3 : (p : ℝ) * (‖lam r.2‖ * C) ≤ p * (ε₀ * C) := by gcongr
    linarith
  have hqε : q.1.1.2 < X.ε := by linarith [X.hε]
  have hGq := GxS_end0 hMc hne X lam q.1 hqε q.2
  have hq'ε : q'.1.1.2 < X.ε := by
    have h1 := hb q hq
    have h2 := hb q' hq'
    rw [h] at h1
    obtain ⟨h1a, h1b⟩ := abs_sub_lt_iff.1 h1
    obtain ⟨h2a, h2b⟩ := abs_sub_lt_iff.1 h2
    linarith
  have hGq' := GxS_end0 hMc hne X lam q'.1 hq'ε q'.2
  rw [hGq, hGq'] at h
  have hfst := congrArg Prod.fst h
  have hsnd := congrArg Prod.snd h
  simp only at hfst hsnd
  -- injectivity of the tube map of `N₀`
  have hfst' : Gx hMc hne F₀ T₀.lam (⟨q.1.1.1, fst_mem_N0 X q.1 hqε⟩, q.2) =
      Gx hMc hne F₀ T₀.lam (⟨q'.1.1.1, fst_mem_N0 X q'.1 hq'ε⟩, q'.2) := by
    rw [hT₀]; exact hfst
  have hm1 : (⟨q.1.1.1, fst_mem_N0 X q.1 hqε⟩, q.2) ∈ PN.tube F₀.N p T₀.ε := by
    show ‖q.2‖ < T₀.ε; exact hq.trans_le hε₀0
  have hm2 : (⟨q'.1.1.1, fst_mem_N0 X q'.1 hq'ε⟩, q'.2) ∈ PN.tube F₀.N p T₀.ε := by
    show ‖q'.2‖ < T₀.ε; exact hq'.trans_le hε₀0
  have hinj := T₀.hinj hm1 hm2 hfst'
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at hinj
  refine Prod.ext (Subtype.ext (Prod.ext hinj.1 hsnd)) hinj.2

include hlam_id hC0 hC hT₁ hε₀a hε₀1 hε₀C in
/-- Injectivity when the first point lies deep in the end `1 - ε < t`. -/
theorem eq_of_GxS_eq_end1 (q q' : X.S × EuclideanSpace ℝ (Fin p)) (hq : ‖q.2‖ < ε₀)
    (hq' : ‖q'.2‖ < ε₀) (ht : 1 - X.ε + X.ε / 2 < q.1.1.2)
    (h : GxS hMc hne X lam q = GxS hMc hne X lam q') : q = q' := by
  have hb : ∀ (r : X.S × EuclideanSpace ℝ (Fin p)), ‖r.2‖ < ε₀ →
      |(GxS hMc hne X lam r).2 - r.1.1.2| < X.ε / 4 := by
    intro r hr
    have h1 : ‖lam r.2‖ ≤ ε₀ := by rw [hlam_id _ (hr.le.trans hε₀a)]; exact hr.le
    have h2 := abs_snd_GxS_sub_le hMc hne X hC lam r
    have h3 : (p : ℝ) * (‖lam r.2‖ * C) ≤ p * (ε₀ * C) := by gcongr
    linarith
  have hqε : 1 - X.ε < q.1.1.2 := by linarith [X.hε]
  have hGq := GxS_end1 hMc hne X lam q.1 hqε q.2
  have hq'ε : 1 - X.ε < q'.1.1.2 := by
    have h1 := hb q hq
    have h2 := hb q' hq'
    rw [h] at h1
    obtain ⟨h1a, h1b⟩ := abs_sub_lt_iff.1 h1
    obtain ⟨h2a, h2b⟩ := abs_sub_lt_iff.1 h2
    linarith
  have hGq' := GxS_end1 hMc hne X lam q'.1 hq'ε q'.2
  rw [hGq, hGq'] at h
  have hfst := congrArg Prod.fst h
  have hsnd := congrArg Prod.snd h
  simp only at hfst hsnd
  have hfst' : Gx hMc hne F₁ T₁.lam (⟨q.1.1.1, fst_mem_N1 X q.1 hqε⟩, q.2) =
      Gx hMc hne F₁ T₁.lam (⟨q'.1.1.1, fst_mem_N1 X q'.1 hq'ε⟩, q'.2) := by
    rw [hT₁]; exact hfst
  have hm1 : (⟨q.1.1.1, fst_mem_N1 X q.1 hqε⟩, q.2) ∈ PN.tube F₁.N p T₁.ε := by
    show ‖q.2‖ < T₁.ε; exact hq.trans_le hε₀1
  have hm2 : (⟨q'.1.1.1, fst_mem_N1 X q'.1 hq'ε⟩, q'.2) ∈ PN.tube F₁.N p T₁.ε := by
    show ‖q'.2‖ < T₁.ε; exact hq'.trans_le hε₀1
  have hinj := T₁.hinj hm1 hm2 hfst'
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at hinj
  refine Prod.ext (Subtype.ext (Prod.ext hinj.1 hsnd)) hinj.2

end inj

/-! ### The injectivity radius of the cobordism -/

/-- **A uniform injectivity radius for the tube map of `S`**, with bijective derivative on the
tube over `S ∩ (M × [-3, 4])`. -/
theorem exists_injRadius_S {lam : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    (hlam : ContDiff ℝ ∞ lam) {a₀ : ℝ} (ha₀ : 0 < a₀) (hlam_id : ∀ t, ‖t‖ ≤ a₀ → lam t = t)
    (hmemS : ∀ q, (GambS X lam q).1 ∈ Tub.Nε hM hMc hne)
    {C : ℝ} (hC0 : 0 < C) (hC : ∀ i q, ‖X.u i q‖ ≤ C)
    (T₀ : TubeData hMc hne F₀) (hT₀ : T₀.lam = lam) (T₁ : TubeData hMc hne F₁) (hT₁ : T₁.lam = lam) :
    letI := hM.chartedSpace; haveI := hM.isManifold; letI := X.hS.chartedSpace;
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ a₀ ∧ ε ≤ T₀.ε ∧ ε ≤ T₁.ε ∧ p * (ε * C) < X.ε / 4 ∧
      InjOn (GxS hMc hne X lam) (PN.tube X.S p ε) ∧
      ∀ q ∈ PN.tube X.S p ε, -3 ≤ q.1.1.2 → q.1.1.2 ≤ 4 →
        Bijective (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
          (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) (GxS hMc hne X lam) q) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := X.hS.chartedSpace
  haveI := X.hS.isManifold
  have hlam_ev : ∀ᶠ t in 𝓝 (0 : EuclideanSpace ℝ (Fin p)), lam t = t := by
    filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin p)) ha₀] with t ht
    exact hlam_id t (mem_ball_zero_iff.1 ht).le
  have hlam0 : lam 0 = 0 := hlam_ev.self_of_nhds
  have hG := contMDiff_GxS hMc hne X hlam hmemS
  have hbij0 := bijective_mfd_GxS_zero hMc hne X hlam hlam_ev hmemS
  -- the compact piece
  set K'' : Set X.S := {q | -3 ≤ q.1.2 ∧ q.1.2 ≤ 4} with hK''
  have hK''c : IsCompact K'' := by
    rw [Subtype.isCompact_iff]
    have : Subtype.val '' K'' = {q ∈ X.S | -3 ≤ q.2 ∧ q.2 ≤ 4} := by
      ext q
      constructor
      · rintro ⟨r, hr, rfl⟩; exact ⟨r.2, hr⟩
      · rintro ⟨hq, h1, h2⟩; exact ⟨⟨q, hq⟩, ⟨h1, h2⟩, rfl⟩
    rw [this]
    exact isCompact_S_Icc X (by norm_num) (by norm_num)
  -- the preliminary radius
  set ε₀ : ℝ := min (min T₀.ε T₁.ε) (min a₀ (X.ε / (8 * (p * C + 1)))) with hε₀
  have hε₀pos : 0 < ε₀ := lt_min (lt_min T₀.hε T₁.hε) (lt_min ha₀ (by have := X.hε; positivity))
  have hε₀0 : ε₀ ≤ T₀.ε := (min_le_left _ _).trans (min_le_left _ _)
  have hε₀1 : ε₀ ≤ T₁.ε := (min_le_left _ _).trans (min_le_right _ _)
  have hε₀a : ε₀ ≤ a₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hε₀C : p * (ε₀ * C) < X.ε / 4 := by
    have h1 : ε₀ ≤ X.ε / (8 * (p * C + 1)) := (min_le_right _ _).trans (min_le_right _ _)
    have hpc : (0 : ℝ) ≤ p * C := by positivity
    have h2 : (p : ℝ) * (ε₀ * C) ≤ p * C * (X.ε / (8 * (p * C + 1))) := by
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ p * C)
      linarith [this]
    have h3 : (p : ℝ) * C * (X.ε / (8 * (p * C + 1))) < X.ε / 4 := by
      rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [X.hε, mul_nonneg hpc X.hε.le]
    linarith
  -- injectivity outside the compact piece comes from the ends
  have hout : ∀ q q' : X.S × EuclideanSpace ℝ (Fin p), ‖q.2‖ < ε₀ → ‖q'.2‖ < ε₀ → q.1 ∉ K'' →
      GxS hMc hne X lam q = GxS hMc hne X lam q' → q = q' := by
    intro q q' hq hq' hK h
    have hK' : q.1.1.2 < -3 ∨ 4 < q.1.1.2 := by
      by_contra hcon
      push_neg at hcon
      exact hK ⟨hcon.1, hcon.2⟩
    rcases hK' with h1 | h1
    · exact eq_of_GxS_eq_end0 hMc hne X hlam_id hC0.le hC T₀ hT₀ hε₀a hε₀0 hε₀C q q' hq hq'
        (by linarith [X.hε, X.hε']) h
    · exact eq_of_GxS_eq_end1 hMc hne X hlam_id hC0.le hC T₁ hT₁ hε₀a hε₀1 hε₀C q q' hq hq'
        (by linarith [X.hε, X.hε']) h
  obtain ⟨ε₁, hε₁, hε₁le, hinj⟩ := PN.exists_injOn hG K'' hK''c hε₀pos (fun q _ => hbij0 q)
    (GxS_zero_injective hMc hne X hlam0) hout
  obtain ⟨ε₂, hε₂, hb₂⟩ := PN.exists_ball_bijective hG K'' hK''c (fun q _ => hbij0 q)
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (min_le_left _ _).trans (hε₁le.trans hε₀a)
  · exact (min_le_left _ _).trans (hε₁le.trans hε₀0)
  · exact (min_le_left _ _).trans (hε₁le.trans hε₀1)
  · have : (p : ℝ) * (min ε₁ ε₂ * C) ≤ p * (ε₀ * C) := by
      gcongr; exact (min_le_left _ _).trans hε₁le
    linarith
  · intro q hq q' hq' h
    exact hinj q q' (lt_of_lt_of_le hq (min_le_left _ _)) (lt_of_lt_of_le hq' (min_le_left _ _)) h
  · rintro ⟨q, s⟩ hq h1 h2
    exact hb₂ q ⟨h1, h2⟩ s (lt_of_lt_of_le hq (min_le_right _ _))


/-! ### Restriction of the tube map to an open piece -/

section restrict

variable {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ N]
  {EX HX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [FiniteDimensional ℝ EX]
  [TopologicalSpace HX]
  {IX : ModelWithCorners ℝ EX HX} {Y : Type*} [TopologicalSpace Y] [ChartedSpace HX Y]
  [IsManifold IX ∞ Y]

/-- The inclusion `U × ℝᵖ → N × ℝᵖ` has derivative the identity. -/
theorem hasMFDerivAt_incl_prod (U : TopologicalSpace.Opens N) (r : U × EuclideanSpace ℝ (Fin p)) :
    HasMFDerivAt (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      (fun r : U × EuclideanSpace ℝ (Fin p) => ((r.1 : N), r.2)) r
      (ContinuousLinearMap.id ℝ _) := by
  have h1 := HasMFDerivAt.comp r (g := (Subtype.val : U → N)) (f := Prod.fst)
    (hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
      (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
      ((contMDiff_subtype_val (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) (n := ∞)
        (U := U)).mdifferentiableAt (by simp) : MDifferentiableAt _ _ (Subtype.val : U → N) r.1))
    (hasMFDerivAt_fst (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) (M := U) (M' := EuclideanSpace ℝ (Fin p)) r)
  have h2 := hasMFDerivAt_snd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) (M := U) (M' := EuclideanSpace ℝ (Fin p)) r
  have h3 := h1.prodMk h2
  rw [mfd_subtype_val_opens] at h3
  refine HasMFDerivAt.congr_mfderiv h3 ?_
  show ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n + 1)))).comp
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin p)))).prod
      (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin p))) =
    ContinuousLinearMap.id ℝ _
  ext w <;> simp

/-- The derivative of a restricted map. -/
theorem mfd_restrict_prod (U : TopologicalSpace.Opens N) {G : N × EuclideanSpace ℝ (Fin p) → Y}
    (hG : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) IX ∞ G)
    (r : U × EuclideanSpace ℝ (Fin p)) :
    mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) IX
      (fun r : U × EuclideanSpace ℝ (Fin p) => G ((r.1 : N), r.2)) r =
    mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) IX G
      ((r.1 : N), r.2) := by
  have h1 := hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod
    𝓘(ℝ, EuclideanSpace ℝ (Fin p))) (J := IX)
    (hG.mdifferentiableAt (by simp) : MDifferentiableAt _ _ G ((r.1 : N), r.2))
  have h2 := HasMFDerivAt.mfd_eq (HasMFDerivAt.comp r (g := G)
    (f := fun r : U × EuclideanSpace ℝ (Fin p) => ((r.1 : N), r.2)) h1
    (hasMFDerivAt_incl_prod U r))
  have h2' : mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) IX
      (fun r : U × EuclideanSpace ℝ (Fin p) => G ((r.1 : N), r.2)) r =
      (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) IX G
        ((r.1 : N), r.2)).comp (ContinuousLinearMap.id ℝ _) := h2
  rw [h2']
  exact ContinuousLinearMap.comp_id _

end restrict

/-! ### The map of the cobordism -/

include X in
/-- **The map of a framed cobordism.**  There is a smooth `H : M × ℝ → Sᵖ` whose restrictions
to `t = 0` and `t = 1` have Pontryagin manifolds `F₀` and `F₁` at the north pole (with a common
basis `c • b`). -/
theorem exists_cobMap (b : Fin p → EuclideanSpace ℝ (Fin p)) (hb : LinearIndependent ℝ b) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    ∃ (H : M × ℝ → Sph p)
      (hH : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ H)
      (c : ℝ) (hc : 0 < c) (hcb : LinearIndependent ℝ (fun i => c • b i))
      (hy0 : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
        (fun z => H (z, 0)) north)
      (hy1 : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
        (fun z => H (z, 1)) north),
      pontryagin hM hMc hne (hH.comp (contMDiff_id.prodMk contMDiff_const)) hy0 F₀.dim
        (fun i => c • b i) hcb = F₀ ∧
      pontryagin hM hMc hne (hH.comp (contMDiff_id.prodMk contMDiff_const)) hy1 F₁.dim
        (fun i => c • b i) hcb = F₁ := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := X.hS.chartedSpace
  haveI := X.hS.isManifold
  -- bounds and the shared clamp
  obtain ⟨C, hC0, hC⟩ := exists_bound_u X
  have hC₀ := bound_v0_of_bound_u X hC
  have hC₁ := bound_v1_of_bound_u X hC
  set tε := Tub.tubε hM hMc hne with htε
  have htε0 : 0 < tε := Tub.tubε_pos hM hMc hne
  set a₀ : ℝ := tε / (8 * (p * C + 1)) with ha₀def
  have ha₀ : 0 < a₀ := by positivity
  obtain ⟨lam, hlam, hlam_id, hlam_b, -⟩ :=
    exists_clamp (E := EuclideanSpace ℝ (Fin p)) ha₀ (le_refl (2 * a₀))
  have hbC : p * (2 * a₀ * C) < tε := by
    rw [ha₀def]
    have h1 : (p : ℝ) * (2 * (tε / (8 * (p * C + 1))) * C) =
        tε * (2 * p * C) / (8 * (p * C + 1)) := by
      field_simp
    rw [h1, div_lt_iff₀ (by positivity)]
    have hpc : (0 : ℝ) ≤ p * C := by positivity
    exact mul_lt_mul_of_pos_left (by nlinarith [hpc]) htε0
  have hmem₀ : ∀ q, Gamb F₀ lam q ∈ Tub.Nε hM hMc hne :=
    Gamb_mem_Nε hMc hne F₀ hC₀ hlam_b hC0.le hbC
  have hmem₁ : ∀ q, Gamb F₁ lam q ∈ Tub.Nε hM hMc hne :=
    Gamb_mem_Nε hMc hne F₁ hC₁ hlam_b hC0.le hbC
  have hmemS : ∀ q, (GambS X lam q).1 ∈ Tub.Nε hM hMc hne :=
    GambS_fst_mem_Nε hMc hne X hC hlam_b hC0.le hbC
  obtain ⟨T₀, hT₀, -⟩ := exists_tubeData_of_lam hMc hne F₀ hlam ha₀ hlam_id hmem₀
  obtain ⟨T₁, hT₁, -⟩ := exists_tubeData_of_lam hMc hne F₁ hlam ha₀ hlam_id hmem₁
  obtain ⟨ε, hε, hεa, hε0, hε1, hεC, hinjS, hbijS⟩ :=
    exists_injRadius_S hMc hne X hlam ha₀ hlam_id hmemS hC0 hC T₀ hT₀ T₁ hT₁
  have hG := contMDiff_GxS hMc hne X hlam hmemS
  have hlam0 : lam 0 = 0 := hlam_id 0 (by rw [norm_zero]; exact ha₀.le)
  have hshift : ∀ (q : X.S) (s : EuclideanSpace ℝ (Fin p)), ‖s‖ < ε →
      |(GxS hMc hne X lam (q, s)).2 - q.1.2| < 1 / 8 := by
    intro q s hs
    have h1 := abs_snd_GxS_sub_le hMc hne X hC lam (q, s)
    have h2 : ‖lam s‖ ≤ ε := by rw [hlam_id _ (hs.le.trans hεa)]; exact hs.le
    have h3 : (p : ℝ) * (‖lam s‖ * C) ≤ p * (ε * C) := by gcongr
    have h4 : X.ε / 4 < 1 / 8 := by linarith [X.hε']
    linarith
  -- the open piece
  set So : TopologicalSpace.Opens X.S :=
    ⟨{q | -3 < q.1.2 ∧ q.1.2 < 4}, (isOpen_lt continuous_const
      (continuous_snd.comp continuous_subtype_val)).inter
      (isOpen_lt (continuous_snd.comp continuous_subtype_val) continuous_const)⟩ with hSo
  set Go : So × EuclideanSpace ℝ (Fin p) → M × ℝ := fun r => GxS hMc hne X lam (r.1.1, r.2) with hGodef
  have hGo : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) ∞ Go :=
    hG.comp (((contMDiff_subtype_val (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))).comp
      contMDiff_fst).prodMk contMDiff_snd)
  have hinjo : InjOn Go (PN.tube So p ε) := by
    intro r hr r' hr' h
    have hr1 : (r.1.1, r.2) ∈ PN.tube X.S p ε := hr
    have hr1' : (r'.1.1, r'.2) ∈ PN.tube X.S p ε := hr'
    have := hinjS hr1 hr1' h
    simp only [Prod.mk.injEq] at this
    exact Prod.ext (Subtype.ext this.1) this.2
  have hbijo : ∀ r ∈ PN.tube So p ε,
      Bijective (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) Go r) := by
    intro r hr
    rw [hGodef, mfd_restrict_prod So hG r]
    have hr3 : -3 < (Subtype.val (Subtype.val r.1) : M × ℝ).2 ∧
        (Subtype.val (Subtype.val r.1) : M × ℝ).2 < 4 := r.1.2
    exact hbijS (r.1.1, r.2) hr hr3.1.le hr3.2.le
  -- the collapse map
  obtain ⟨c, hc, hcs⟩ := exists_scale hb hε
  have hcb : LinearIndependent ℝ (fun i => c • b i) := by
    convert hb.units_smul (fun _ => Units.mk0 c hc.ne') using 1
    funext i
    simp [Pi.smul_apply', Units.smul_def]
  -- the time clamp
  obtain ⟨lt, hlt, hlt_id, hlt_b, -⟩ := exists_clamp (E := ℝ) (a := 3 / 4) (b := 3 / 2)
    (by norm_num) (by norm_num)
  set ρ : ℝ → ℝ := fun t => 1 / 2 + lt (t - 1 / 2) with hρdef
  have hρs : ContDiff ℝ ∞ ρ := contDiff_const.add (hlt.comp (contDiff_id.sub contDiff_const))
  have hρ_id : ∀ t, |t - 1 / 2| ≤ 3 / 4 → ρ t = t := fun t ht => by
    simp only [hρdef]
    rw [hlt_id _ (by rw [Real.norm_eq_abs]; exact ht)]; ring
  have hρ0 : ρ 0 = 0 := hρ_id 0 (by norm_num)
  have hρ1 : ρ 1 = 1 := hρ_id 1 (by norm_num)
  have hρmem : ∀ t, -2 < ρ t ∧ ρ t < 3 := fun t => by
    have := hlt_b (t - 1 / 2)
    rw [Real.norm_eq_abs] at this
    have h := abs_le.1 this
    simp only [hρdef]
    constructor <;> linarith
  by_cases hneo : Nonempty So
  swap
  · -- the cobordism is empty on the finite part: both ends are empty
    have hN₀ : F₀.N = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro x hx
      exact hneo ⟨⟨⟨(x, 0), mem_S_end0 X ⟨x, hx⟩ X.hε⟩, by constructor <;> norm_num⟩⟩
    have hN₁ : F₁.N = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro x hx
      exact hneo ⟨⟨⟨(x, 1), mem_S_end1 X ⟨x, hx⟩ (by linarith [X.hε])⟩, by constructor <;> norm_num⟩⟩
    have hH : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
      (fun _ : M × ℝ => (south : Sph p)) := contMDiff_const
    have hpre0 : (fun z : M => (fun _ : M × ℝ => (south : Sph p)) (z, 0)) ⁻¹' {north} = F₀.N := by
      rw [hN₀]; ext z; simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      exact south_ne_north
    have hpre1 : (fun z : M => (fun _ : M × ℝ => (south : Sph p)) (z, 1)) ⁻¹' {north} = F₁.N := by
      rw [hN₁]; ext z; simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      exact south_ne_north
    obtain ⟨hy0, hcb', heq0⟩ := pontryagin_eq_of_collapse hM hMc hne F₀
      (hH.comp (contMDiff_id.prodMk contMDiff_const)) hpre0 hb hc hε
      (fun x => absurd x.2 (eq_empty_iff_forall_notMem.1 hN₀ x.1))
    obtain ⟨hy1, hcb1, heq1⟩ := pontryagin_eq_of_collapse hM hMc hne F₁
      (hH.comp (contMDiff_id.prodMk contMDiff_const)) hpre1 hb hc hε
      (fun x => absurd x.2 (eq_empty_iff_forall_notMem.1 hN₁ x.1))
    exact ⟨_, hH, c, hc, hcb, hy0, hy1, heq0, heq1⟩
  -- the product neighbourhood of the open piece
  set Vo := Go '' PN.tube So p ε with hVodef
  have hVo : IsOpen Vo := PN.isOpen_image_tube hGo hbijo
  set Gi := PN.Ginv Go ε with hGidef
  have hGi_G : ∀ r ∈ PN.tube So p ε, Gi (Go r) = r := fun r hr => PN.Ginv_G hinjo hr
  have hG_Gi : ∀ zt ∈ Vo, Go (Gi zt) = zt := fun zt hz => PN.G_Ginv hz
  have hGi_mem : ∀ zt ∈ Vo, Gi zt ∈ PN.tube So p ε := fun zt hz => PN.Ginv_mem hz
  -- the map on the strip
  set H₀ : M × ℝ → Sph p := fun zt => if zt ∈ Vo then collapse hb c (Gi zt).2 else south with hH₀def
  have hH₀_mem : ∀ zt ∈ Vo, H₀ zt = collapse hb c (Gi zt).2 := fun zt hz => by simp [hH₀def, hz]
  have hH₀_not : ∀ zt ∉ Vo, H₀ zt = south := fun zt hz => by simp [hH₀def, hz]
  set Str : Set (M × ℝ) := {zt | -2 < zt.2 ∧ zt.2 < 3} with hStr
  have hStro : IsOpen Str :=
    (isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const)
  set Ko : Set So := {r | -5 / 2 ≤ r.1.1.2 ∧ r.1.1.2 ≤ 7 / 2} with hKo
  have hKoc : IsCompact Ko := by
    rw [Subtype.isCompact_iff]
    have h1 : Subtype.val '' Ko = {q : X.S | -5 / 2 ≤ q.1.2 ∧ q.1.2 ≤ 7 / 2} := by
      ext q
      constructor
      · rintro ⟨r, hr, rfl⟩; exact hr
      · rintro ⟨h1, h2⟩
        exact ⟨⟨q, by constructor <;> linarith⟩, ⟨h1, h2⟩, rfl⟩
    rw [h1, Subtype.isCompact_iff]
    have h2 : Subtype.val '' {q : X.S | -5 / 2 ≤ q.1.2 ∧ q.1.2 ≤ 7 / 2} =
        {q ∈ X.S | -5 / 2 ≤ q.2 ∧ q.2 ≤ 7 / 2} := by
      ext q
      constructor
      · rintro ⟨r, hr, rfl⟩; exact ⟨r.2, hr⟩
      · rintro ⟨hq, h1, h2⟩; exact ⟨⟨q, hq⟩, ⟨h1, h2⟩, rfl⟩
    rw [h2]
    exact isCompact_S_Icc X (by norm_num) (by norm_num)
  set Cl := Go '' (Ko ×ˢ closedBall (0 : EuclideanSpace ℝ (Fin p)) (ε / 2)) with hCl
  have hClc : IsCompact Cl := (hKoc.prod (isCompact_closedBall _ _)).image hGo.continuous
  have hH₀_south : ∀ zt ∈ Str, zt ∉ Cl → H₀ zt = south := by
    intro zt hzS hzC
    by_cases hzV : zt ∈ Vo
    · rw [hH₀_mem zt hzV]
      obtain ⟨r, hr, rfl⟩ := hzV
      rw [hGi_G r hr]
      apply hcs
      by_contra hlt'
      push_neg at hlt'
      apply hzC
      refine ⟨r, ⟨?_, mem_closedBall_zero_iff.2 hlt'.le⟩, rfl⟩
      have hsh := hshift r.1 r.2 hr
      have := abs_sub_lt_iff.1 hsh
      show -5 / 2 ≤ (Subtype.val (Subtype.val r.1) : M × ℝ).2 ∧
        (Subtype.val (Subtype.val r.1) : M × ℝ).2 ≤ 7 / 2
      have hzS' : -2 < (GxS hMc hne X lam (r.1, r.2)).2 ∧ (GxS hMc hne X lam (r.1, r.2)).2 < 3 := hzS
      constructor <;> linarith [this.1, this.2, hzS'.1, hzS'.2]
    · exact hH₀_not zt hzV
  have hH₀at : ∀ zt ∈ Str, ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ H₀ zt := by
    intro zt hzS
    by_cases hz : zt ∈ Vo
    · have h1 : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
          𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ (fun zt' => collapse hb c (Gi zt').2) zt := by
        have hsnd : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
            𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ (fun r : So × EuclideanSpace ℝ (Fin p) => r.2) :=
          contMDiff_snd
        exact ((contMDiff_collapse hb c).comp hsnd).contMDiffAt.comp zt
          (PN.contMDiffAt_Ginv hGo hbijo hinjo hz)
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [hVo.mem_nhds hz] with zt' hz'
      exact hH₀_mem zt' hz'
    · have hzC : zt ∉ Cl := fun h => hz (by
        obtain ⟨r, ⟨-, hr⟩, rfl⟩ := h
        exact ⟨r, (mem_closedBall_zero_iff.1 hr).trans_lt (by linarith), rfl⟩)
      have h1 : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
          𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ (fun _ : M × ℝ => (south : Sph p)) zt := contMDiffAt_const
      refine h1.congr_of_eventuallyEq ?_
      have hopen : IsOpen (Str ∩ Clᶜ) := hStro.inter hClc.isClosed.isOpen_compl
      filter_upwards [hopen.mem_nhds ⟨hzS, hzC⟩] with zt' hz'
      exact hH₀_south zt' hz'.1 hz'.2
  -- the global map
  set H : M × ℝ → Sph p := fun zt => H₀ (zt.1, ρ zt.2) with hHdef
  have hH : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ H := by
    intro zt
    have hmap : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) ∞ (fun zt : M × ℝ => (zt.1, ρ zt.2)) :=
      contMDiff_fst.prodMk ((contMDiff_iff_contDiff.2 hρs).comp contMDiff_snd)
    exact (hH₀at (zt.1, ρ zt.2) (hρmem zt.2)).comp zt hmap.contMDiffAt
  -- the level set of `H₀`
  have hH₀_north : ∀ zt, H₀ zt = north ↔ ∃ r : So, zt = r.1.1 := by
    intro zt
    constructor
    · intro h
      by_cases hz : zt ∈ Vo
      · rw [hH₀_mem zt hz, collapse_eq_north_iff hb hc.ne'] at h
        refine ⟨(Gi zt).1, ?_⟩
        have h1 := hG_Gi zt hz
        have h2 : Gi zt = ((Gi zt).1, 0) := Prod.ext rfl h
        rw [h2] at h1
        have h3 : Go ((Gi zt).1, 0) = ((Gi zt).1).1.1 := by
          show GxS hMc hne X lam (((Gi zt).1).1, 0) = _
          rw [GxS_zero hMc hne X hlam0]
        exact h1.symm.trans h3
      · rw [hH₀_not zt hz] at h
        exact absurd h south_ne_north
    · rintro ⟨r, rfl⟩
      have hq : (r, (0 : EuclideanSpace ℝ (Fin p))) ∈ PN.tube So p ε := by
        show ‖(0 : EuclideanSpace ℝ (Fin p))‖ < ε; rw [norm_zero]; exact hε
      have h1 : Go (r, 0) = r.1.1 := by
        show GxS hMc hne X lam (r.1, 0) = _
        rw [GxS_zero hMc hne X hlam0]
      have hz : r.1.1 ∈ Vo := ⟨(r, 0), hq, h1⟩
      rw [hH₀_mem _ hz]
      have h2 : Gi r.1.1 = (r, 0) := by rw [← h1]; exact hGi_G _ hq
      rw [h2]
      exact collapse_zero hb c
  -- the level sets at `t = 0` and `t = 1`
  have hpre0 : (fun z : M => H (z, 0)) ⁻¹' {north} = F₀.N := by
    ext z
    simp only [mem_preimage, mem_singleton_iff, hHdef, hρ0]
    rw [hH₀_north]
    constructor
    · rintro ⟨r, hr⟩
      have : (z, (0 : ℝ)) ∈ X.S := by rw [hr]; exact r.1.2
      exact (X.end0 (z, 0) X.hε).1 this
    · intro hz
      exact ⟨⟨⟨(z, 0), mem_S_end0 X ⟨z, hz⟩ X.hε⟩, by constructor <;> norm_num⟩, rfl⟩
  have hpre1 : (fun z : M => H (z, 1)) ⁻¹' {north} = F₁.N := by
    ext z
    simp only [mem_preimage, mem_singleton_iff, hHdef, hρ1]
    rw [hH₀_north]
    constructor
    · rintro ⟨r, hr⟩
      have : (z, (1 : ℝ)) ∈ X.S := by rw [hr]; exact r.1.2
      exact (X.end1 (z, 1) (by linarith [X.hε])).1 this
    · intro hz
      exact ⟨⟨⟨(z, 1), mem_S_end1 X ⟨z, hz⟩ (by linarith [X.hε])⟩, by constructor <;> norm_num⟩, rfl⟩
  -- the collapse form along the framing at `t = 0`
  have hline0 : ∀ (x : F₀.N) (i : Fin p) (s : ℝ), |s| < ε →
      H (Tub.tubr hM hMc hne (x.1.1 + s • F₀.v i x), 0) = collapse hb c (s • EuclideanSpace.single i 1) := by
    intro x i s hs
    simp only [hHdef, hρ0]
    set r : So := ⟨⟨(x.1, 0), mem_S_end0 X x X.hε⟩, by constructor <;> norm_num⟩ with hr
    have hs1 : ‖s • EuclideanSpace.single i (1 : ℝ)‖ = |s| := by
      rw [norm_smul, EuclideanSpace.norm_single, norm_one, mul_one, Real.norm_eq_abs]
    have hq : (r, s • EuclideanSpace.single i (1 : ℝ)) ∈ PN.tube So p ε := by
      show ‖s • EuclideanSpace.single i (1 : ℝ)‖ < ε; rw [hs1]; exact hs
    have hGr : Go (r, s • EuclideanSpace.single i 1) = (Tub.tubr hM hMc hne (x.1.1 + s • F₀.v i x), 0) := by
      show GxS hMc hne X lam (r.1, s • EuclideanSpace.single i 1) = _
      rw [GxS_end0 hMc hne X lam r.1 (show r.1.1.2 < X.ε from X.hε)]
      have hx : (⟨r.1.1.1, fst_mem_N0 X r.1 X.hε⟩ : F₀.N) = x := Subtype.ext rfl
      rw [hx, Gx_line hMc hne F₀ hlam_id x i (hs.le.trans hεa)]
    have hzV : (Tub.tubr hM hMc hne (x.1.1 + s • F₀.v i x), (0 : ℝ)) ∈ Vo := ⟨_, hq, hGr⟩
    rw [hH₀_mem _ hzV, ← hGr, hGi_G _ hq]
  have hline1 : ∀ (x : F₁.N) (i : Fin p) (s : ℝ), |s| < ε →
      H (Tub.tubr hM hMc hne (x.1.1 + s • F₁.v i x), 1) = collapse hb c (s • EuclideanSpace.single i 1) := by
    intro x i s hs
    simp only [hHdef, hρ1]
    have h1ε : 1 - X.ε < (1 : ℝ) := by linarith [X.hε]
    set r : So := ⟨⟨(x.1, 1), mem_S_end1 X x h1ε⟩, by constructor <;> norm_num⟩ with hr
    have hs1 : ‖s • EuclideanSpace.single i (1 : ℝ)‖ = |s| := by
      rw [norm_smul, EuclideanSpace.norm_single, norm_one, mul_one, Real.norm_eq_abs]
    have hq : (r, s • EuclideanSpace.single i (1 : ℝ)) ∈ PN.tube So p ε := by
      show ‖s • EuclideanSpace.single i (1 : ℝ)‖ < ε; rw [hs1]; exact hs
    have hGr : Go (r, s • EuclideanSpace.single i 1) = (Tub.tubr hM hMc hne (x.1.1 + s • F₁.v i x), 1) := by
      show GxS hMc hne X lam (r.1, s • EuclideanSpace.single i 1) = _
      rw [GxS_end1 hMc hne X lam r.1 (show 1 - X.ε < r.1.1.2 from h1ε)]
      have hx : (⟨r.1.1.1, fst_mem_N1 X r.1 h1ε⟩ : F₁.N) = x := Subtype.ext rfl
      rw [hx, Gx_line hMc hne F₁ hlam_id x i (hs.le.trans hεa)]
    have hzV : (Tub.tubr hM hMc hne (x.1.1 + s • F₁.v i x), (1 : ℝ)) ∈ Vo := ⟨_, hq, hGr⟩
    rw [hH₀_mem _ hzV, ← hGr, hGi_G _ hq]
  obtain ⟨hy0, hcb', heq0⟩ := pontryagin_eq_of_collapse hM hMc hne F₀
    (hH.comp (contMDiff_id.prodMk contMDiff_const)) hpre0 hb hc hε hline0
  obtain ⟨hy1, hcb1, heq1⟩ := pontryagin_eq_of_collapse hM hMc hne F₁
    (hH.comp (contMDiff_id.prodMk contMDiff_const)) hpre1 hb hc hε hline1
  exact ⟨H, hH, c, hc, hcb, hy0, hy1, heq0, heq1⟩

end Framed

end Milnor
