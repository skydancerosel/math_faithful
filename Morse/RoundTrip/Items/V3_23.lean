import Morse
import RoundTrip.Check
import RoundTrip.Blind.V3_23

open Module Morse Morse.Torus
open scoped ContDiff Manifold

namespace RoundTrip.V3_23

/-- The project's statement: the nine listed theorems (`Morse.Torus.height` is a definition). -/
def A : Prop :=
  type_of% @Morse.Torus.isCriticalPointM_height_iff ∧
  type_of% @Morse.Torus.criticalValues_height ∧
  type_of% @Morse.Torus.pointP_spec ∧
  type_of% @Morse.Torus.pointQ_spec ∧
  type_of% @Morse.Torus.pointR_spec ∧
  type_of% @Morse.Torus.pointS_spec ∧
  type_of% @Morse.Torus.isMorseFunction_height ∧
  type_of% @Morse.Torus.critCount_height ∧
  type_of% @Morse.hessian_comp_sliceParam_of_fderiv_eq_zero.{0, 0, 0}

theorem A_holds : A :=
  ⟨@Morse.Torus.isCriticalPointM_height_iff, @Morse.Torus.criticalValues_height,
    @Morse.Torus.pointP_spec, @Morse.Torus.pointQ_spec, @Morse.Torus.pointR_spec,
    @Morse.Torus.pointS_spec, @Morse.Torus.isMorseFunction_height, @Morse.Torus.critCount_height,
    @Morse.hessian_comp_sliceParam_of_fderiv_eq_zero.{0, 0, 0}⟩

/-- `A` with the slice-submanifold proof `isSliceSubmanifold_torus hr hrR` (which occurs inside
the statements, through the charted space) replaced by an arbitrary proof `hT`. Same statement by
proof irrelevance (`A_iff_A'`); needed because `#rt_check` follows the constants of the
statements. -/
def A' : Prop :=
  (∀ {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hT : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn 3) (Rn 2) (Rn 1) (Morse.torus R r)),
    letI := hT.chartedSpace
    (∀ q : Morse.torus R r, IsCriticalPointM (Rn 2) (height R r ∘ Subtype.val) q ↔
      (q : Rn 3) = pointP R r ∨ (q : Rn 3) = pointQ R r ∨ (q : Rn 3) = pointR R r ∨
        (q : Rn 3) = pointS R r) ∧
    {c | ∃ q : Morse.torus R r, IsCriticalPointM (Rn 2) (height R r ∘ Subtype.val) q ∧
      height R r q = c} = {0, 2 * r, 2 * R, 2 * R + 2 * r} ∧
    (IsNondegenerateCriticalPointM (Rn 2) (height R r ∘ Subtype.val) ⟨pointP R r, pointP_mem hr hrR⟩ ∧
      indexM (Rn 2) (height R r ∘ Subtype.val) ⟨pointP R r, pointP_mem hr hrR⟩ = 0) ∧
    (IsNondegenerateCriticalPointM (Rn 2) (height R r ∘ Subtype.val) ⟨pointQ R r, pointQ_mem hrR⟩ ∧
      indexM (Rn 2) (height R r ∘ Subtype.val) ⟨pointQ R r, pointQ_mem hrR⟩ = 1) ∧
    (IsNondegenerateCriticalPointM (Rn 2) (height R r ∘ Subtype.val) ⟨pointR R r, pointR_mem hrR⟩ ∧
      indexM (Rn 2) (height R r ∘ Subtype.val) ⟨pointR R r, pointR_mem hrR⟩ = 1) ∧
    (IsNondegenerateCriticalPointM (Rn 2) (height R r ∘ Subtype.val) ⟨pointS R r, pointS_mem hr hrR⟩ ∧
      indexM (Rn 2) (height R r ∘ Subtype.val) ⟨pointS R r, pointS_mem hr hrR⟩ = 2) ∧
    IsMorseFunction (Rn 2) (height R r ∘ (Subtype.val : Morse.torus R r → Rn 3)) ∧
    ∀ k, critCount (Rn 2) (height R r ∘ (Subtype.val : Morse.torus R r → Rn 3)) k =
      if k = 0 then 1 else if k = 1 then 2 else if k = 2 then 1 else 0) ∧
  type_of% @Morse.hessian_comp_sliceParam_of_fderiv_eq_zero.{0, 0, 0}

theorem A_iff_A' : A ↔ A' := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨fun hr hrR _ ↦ ⟨h1 hr hrR, h2 hr hrR, h3 hr hrR, h4 hr hrR, h5 hr hrR, h6 hr hrR,
      h7 hr hrR, h8 hr hrR⟩, h9⟩
  · rintro ⟨h, h9⟩
    exact ⟨fun hr hrR ↦ (h hr hrR (isSliceSubmanifold_torus hr hrR)).1,
      fun hr hrR ↦ (h hr hrR (isSliceSubmanifold_torus hr hrR)).2.1,
      fun hr hrR ↦ (h hr hrR (isSliceSubmanifold_torus hr hrR)).2.2.1,
      fun hr hrR ↦ (h hr hrR (isSliceSubmanifold_torus hr hrR)).2.2.2.1,
      fun hr hrR ↦ (h hr hrR (isSliceSubmanifold_torus hr hrR)).2.2.2.2.1,
      fun hr hrR ↦ (h hr hrR (isSliceSubmanifold_torus hr hrR)).2.2.2.2.2.1,
      fun hr hrR ↦ (h hr hrR (isSliceSubmanifold_torus hr hrR)).2.2.2.2.2.2.1,
      fun hr hrR ↦ (h hr hrR (isSliceSubmanifold_torus hr hrR)).2.2.2.2.2.2.2, h9⟩

/-! ### Vocabulary -/

theorem torus_eq (R r : ℝ) : torus R r = Morse.torus R r := rfl
theorem hgt_eq (R r : ℝ) : hgt R r = height R r := rfl
theorem pP_eq (R r : ℝ) : pP R r = pointP R r := by
  ext i; fin_cases i <;> simp [pP, pointP, onAxis]
theorem pQ_eq (R r : ℝ) : pQ R r = pointQ R r := by
  ext i; fin_cases i <;> simp [pQ, pointQ, onAxis]
theorem pR_eq (R r : ℝ) : pR R r = pointR R r := by
  ext i; fin_cases i <;> simp [pR, pointR, onAxis]
theorem pS_eq (R r : ℝ) : pS R r = pointS R r := by
  ext i; fin_cases i <;> simp [pS, pointS, onAxis]

/-! ### The two directions -/

theorem A'_to_B : A' → B := by
  intro hA R r hr hrR hN
  let _ := hN.chartedSpace
  obtain ⟨h1, -, hP, hQ, hR, hS, -⟩ := hA.1 hr hrR hN
  rw [pP_eq, pQ_eq, pR_eq, pS_eq]
  refine ⟨pointP_mem hr hrR, pointQ_mem hrR, pointR_mem hrR, pointS_mem hr hrR, h1, ?_, ?_, ?_, ?_⟩
  · rintro ⟨x, hx⟩ (rfl : x = _); exact hP
  · rintro ⟨x, hx⟩ (rfl : x = _); exact hQ
  · rintro ⟨x, hx⟩ (rfl : x = _); exact hR
  · rintro ⟨x, hx⟩ (rfl : x = _); exact hS

theorem A_to_B : A → B := fun h ↦ A'_to_B (A_iff_A'.1 h)

theorem B_to_A' : B → A' := by
  intro hB
  refine ⟨fun {R r} hr hrR hT ↦ ?_, ?_⟩
  · let _ := hT.chartedSpace
    obtain ⟨-, -, -, -, hcrit, hP, hQ, hR, hS⟩ := hB R r hr hrR hT
    simp only [pP_eq, pQ_eq, pR_eq, pS_eq] at hcrit hP hQ hR hS
    have h1 : ∀ q : Morse.torus R r, IsCriticalPointM (Rn 2) (height R r ∘ Subtype.val) q ↔
        (q : Rn 3) = pointP R r ∨ (q : Rn 3) = pointQ R r ∨ (q : Rn 3) = pointR R r ∨
          (q : Rn 3) = pointS R r := hcrit
    set P : Morse.torus R r := ⟨pointP R r, pointP_mem hr hrR⟩
    set Q : Morse.torus R r := ⟨pointQ R r, pointQ_mem hrR⟩
    set R' : Morse.torus R r := ⟨pointR R r, pointR_mem hrR⟩
    set S : Morse.torus R r := ⟨pointS R r, pointS_mem hr hrR⟩
    have h1' : ∀ q : Morse.torus R r, IsCriticalPointM (Rn 2) (height R r ∘ Subtype.val) q ↔
        q = P ∨ q = Q ∨ q = R' ∨ q = S := by
      intro q; rw [h1]; simp only [Subtype.ext_iff, P, Q, R', S]
    have sP := hP P rfl
    have sQ := hQ Q rfl
    have sR := hR R' rfl
    have sS := hS S rfl
    refine ⟨h1, ?_, sP, sQ, sR, sS, ?_, ?_⟩
    · -- the critical values (the project's argument, from B's description of the critical set)
      ext c
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, h1']
      constructor
      · rintro ⟨q, h | h | h | h, rfl⟩ <;> subst h
        · exact Or.inl height_pointP
        · exact Or.inr (Or.inl height_pointQ)
        · exact Or.inr (Or.inr (Or.inl height_pointR))
        · exact Or.inr (Or.inr (Or.inr height_pointS))
      · rintro (rfl | rfl | rfl | rfl)
        · exact ⟨_, Or.inl rfl, height_pointP⟩
        · exact ⟨_, Or.inr (Or.inl rfl), height_pointQ⟩
        · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), height_pointR⟩
        · exact ⟨_, Or.inr (Or.inr (Or.inr rfl)), height_pointS⟩
    · refine ⟨contMDiff_comp_val hT contDiff_height, fun q hq ↦ ?_⟩
      rcases (h1' q).1 hq with rfl | rfl | rfl | rfl
      exacts [sP.1.2, sQ.1.2, sR.1.2, sS.1.2]
    · -- the Morse numbers (the project's counting argument, from B's facts)
      intro k
      have hQR : Q ≠ R' := by
        intro h
        have := congrArg (fun x : Morse.torus R r => (x : Rn 3) 0) h
        simp [Q, R', pointQ, pointR] at this
        linarith
      have key : ∀ q : Morse.torus R r, (IsCriticalPointM (Rn 2) (height R r ∘ Subtype.val) q ∧
          indexM (Rn 2) (height R r ∘ Subtype.val) q = k) ↔
          (q = P ∧ k = 0) ∨ (q = Q ∧ k = 1) ∨ (q = R' ∧ k = 1) ∨ (q = S ∧ k = 2) := by
        intro q
        rw [h1']
        constructor
        · rintro ⟨h | h | h | h, hk⟩ <;> subst h
          · exact Or.inl ⟨rfl, hk.symm.trans sP.2⟩
          · exact Or.inr (Or.inl ⟨rfl, hk.symm.trans sQ.2⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨rfl, hk.symm.trans sR.2⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨rfl, hk.symm.trans sS.2⟩))
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact ⟨Or.inl rfl, sP.2⟩
          · exact ⟨Or.inr (Or.inl rfl), sQ.2⟩
          · exact ⟨Or.inr (Or.inr (Or.inl rfl)), sR.2⟩
          · exact ⟨Or.inr (Or.inr (Or.inr rfl)), sS.2⟩
      unfold critCount
      rw [Set.ext key]
      rcases Nat.lt_or_ge k 3 with hk | hk
      · interval_cases k
        · simp
        · have hset : {q : Morse.torus R r | q = P ∧ 1 = 0 ∨ q = Q ∧ 1 = 1 ∨ q = R' ∧ 1 = 1 ∨
              q = S ∧ 1 = 2} = {Q, R'} := by
            ext q
            simp
          rw [hset, Set.ncard_pair hQR]
          rfl
        · simp
      · simp [show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega]
  · -- Lagrange's rule for the Hessian: a general calculus lemma with no counterpart in `B`,
    -- re-proved from the project's chain rule for Hessians (`Morse.hessian_comp`)
    intro V _ _ Z _ _ W _ _ N σ G q hq hG h0 v w
    have hx : sliceParam σ (σ.φ q).1 = q := sliceParam_toChart σ hq
    have hG' : ContDiffAt ℝ 2 G (sliceParam σ (σ.φ q).1) := by rw [hx]; exact hG
    have h0' : fderiv ℝ G (sliceParam σ (σ.φ q).1) = 0 := by rw [hx]; exact h0
    have hψ : ContDiffAt ℝ 2 (sliceParam σ) (σ.φ q).1 :=
      (contDiffAt_sliceParam σ (toChart_apply_mem_target σ hq)).of_le (by norm_cast)
    rw [hessian_comp hG' hψ h0', hx]

theorem B_to_A : B → A := fun h ↦ A_iff_A'.2 (B_to_A' h)

/- `#rt_check` on `A_to_B` / `B_to_A` themselves reports the theorems behind the proof term
`isSliceSubmanifold_torus hr hrR` inside the statement `A`; the proofs are checked on `A'_to_B`
and `B_to_A'`. -/
#rt_check RoundTrip.V3_23.A'_to_B [Morse.Torus.isCriticalPointM_height_iff,
  Morse.Torus.criticalValues_height, Morse.Torus.pointP_spec, Morse.Torus.pointQ_spec,
  Morse.Torus.pointR_spec, Morse.Torus.pointS_spec, Morse.Torus.isMorseFunction_height,
  Morse.Torus.critCount_height, Morse.hessian_comp_sliceParam_of_fderiv_eq_zero]
#rt_check RoundTrip.V3_23.B_to_A' [Morse.Torus.isCriticalPointM_height_iff,
  Morse.Torus.criticalValues_height, Morse.Torus.pointP_spec, Morse.Torus.pointQ_spec,
  Morse.Torus.pointR_spec, Morse.Torus.pointS_spec, Morse.Torus.isMorseFunction_height,
  Morse.Torus.critCount_height, Morse.hessian_comp_sliceParam_of_fderiv_eq_zero]
#rt_overlap RoundTrip.V3_23.B_to_A' [Morse.Torus.isCriticalPointM_height_iff,
  Morse.Torus.criticalValues_height, Morse.Torus.pointP_spec, Morse.Torus.pointQ_spec,
  Morse.Torus.pointR_spec, Morse.Torus.pointS_spec, Morse.Torus.isMorseFunction_height,
  Morse.Torus.critCount_height, Morse.hessian_comp_sliceParam_of_fderiv_eq_zero]

end RoundTrip.V3_23
