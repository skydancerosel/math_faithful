import Morse.Chapter15.SplittingClifford

/-!
Milnor, *Morse Theory*, §24, pp. 144–146; Exposition/Chapter15.md, §6 (Lemma 6.1 and the case
`k ≢ 2 (mod 4)`).

# The data for the index bound: Lemma 6.1 with Lemma 24.8

## Milnor's text, paraphrased

(pp. 144–145) Split `ℝⁿ = M_1 ⊕ ⋯ ⊕ M_s` into minimal pieces; each has dimension `m_{k+1}`, so
`s = n/m_{k+1}`.  If the geodesic is not minimal, some `a_{h₀} ≥ 3`; Lemma 24.8 gives, for each
`j ≠ h₀`, an eigenvector of `K_A` with eigenvalue `(a_{h₀} + a_j)²/4 ≥ 4`.

## What is formalized

* `Morse.IsOmegaOps.exists_piece_gt`: if `A² ≠ −1`, some minimal piece has `A² = −c`, `c > 1`
  (otherwise `A² = −1` on the span of all pieces, which is everything).
* `Morse.IsOmegaOps.exists_inter`: **Lemma 24.8 between two pieces** (`k + 1 ≤ 8`,
  `k + 1 ≢ 3 (mod 4)`).
* `Morse.IsOmegaOps.exists_omegaPieceData`: **the data** (`Morse.OmegaPieceData`): `a₀ > 1`, for
  each of the `s` pieces `j ≠ h₀` a `b_j ≥ 1` and operators `D_{j,l} = interOp T_j ∘ A^l`
  (`l < r₀`; `r₀ = 2` only for `k = 0`) with all the relations needed by
  `Morse.exists_killing_spaces`, and **`(s + 1) · m_{k+1} = n`**.

## What Milnor leaves implicit

* The hypothesis `a_j² ≥ 1` on every piece (from `exp(πA) = −I`, `Morse.one_le_of_minInvar`) is
  all that is used of the oddness of the `a_j`; `a_{h₀} > 1` suffices for `τ < 1`.
* For `k = 0` (Lemma 24.2) each pair contributes two eigenvectors (`D` and `DA`, the two
  `2 × 2` blocks `C_±` of the exposition), which gives Milnor's `2m − 2` rather than `m − 1`.
-/

open Set Module

noncomputable section

namespace Morse

section Data

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {k : ℕ} {a q : E →L[ℝ] E} {j : ℕ → E →L[ℝ] E}

/-- The data produced by Lemma 6.1 and Lemma 24.8 for the index bound. -/
structure OmegaPieceData (k : ℕ) (a q : E →L[ℝ] E) (j : ℕ → E →L[ℝ] E) (r₀ : ℕ) (κ : Type*)
    [Fintype κ] [DecidableEq κ] where
  a₀ : ℝ
  b : κ → ℝ
  d : κ × Fin r₀ → E →L[ℝ] E
  R : E →L[ℝ] E
  Q : κ → E →L[ℝ] E
  ha₀ : 1 < a₀
  hb : ∀ i, 1 ≤ b i
  hq : ∀ i, d i * q = q * d i
  hj : ∀ i α, 1 ≤ α → α < k → d i * j α = j α * d i
  rel : ∀ i, b i.1 • (d i * a) = -a₀ • (a * d i)
  left : ∀ i, a * (a * d i) = -(b i.1) ^ 2 • d i
  right : ∀ i, d i * a * a = -a₀ ^ 2 • d i
  hR : ∀ i, d i * R = d i
  hR' : ∀ i, ContinuousLinearMap.adjoint (d i) * R = 0
  hQ : ∀ j' i, Q j' * (a * d i) = if i.1 = j' then a * d i else 0
  hind : ∀ j', LinearIndependent ℝ (fun l : Fin r₀ => a * d (j', l))

theorem IsOmegaOps.exists_piece_gt (h : IsOmegaOps k a q j) (hnm : a * a ≠ -1)
    {L : List (Submodule ℝ E)} (hL1 : ∀ M ∈ L, IsMinInvar (omegaGens k a q j) M)
    (hL4 : (⊤ : Submodule ℝ E) ≤ L.foldr (· ⊔ ·) ⊥)
    (hge : ∀ M : Submodule ℝ E, IsMinInvar (omegaGens k a q j) M → ∀ c : ℝ,
      (∀ v ∈ M, a (a v) = -(c • v)) → 1 ≤ c) :
    ∃ M ∈ L, ∃ c : ℝ, (∀ v ∈ M, a (a v) = -(c • v)) ∧ 1 < c := by
  by_contra hcon
  push Not at hcon
  set K : Submodule ℝ E := LinearMap.ker (((a * a + 1 : E →L[ℝ] E)) : E →ₗ[ℝ] E)
  have hMK : ∀ M ∈ L, M ≤ K := fun M hM v hv => by
    obtain ⟨c, hc⟩ := h.exists_sq_eq (hL1 M hM)
    have h1 := hcon M hM c hc
    have h2 := hge M (hL1 M hM) c hc
    have hc1 : c = 1 := le_antisymm h1 h2
    change ((a * a + 1 : E →L[ℝ] E)) v = 0
    rw [add_apply, one_apply_eq_self]
    change a (a v) + v = 0
    rw [hc v hv, hc1, one_smul, neg_add_cancel]
  have hfold : ∀ L' : List (Submodule ℝ E), (∀ M ∈ L', M ≤ K) → L'.foldr (· ⊔ ·) ⊥ ≤ K := by
    intro L' hL'
    induction L' with
    | nil => exact bot_le
    | cons M L'' ih =>
      rw [List.foldr_cons]
      exact sup_le (hL' M List.mem_cons_self) (ih fun M' hM' => hL' M' (List.mem_cons_of_mem _ hM'))
  have htop : (⊤ : Submodule ℝ E) ≤ K := hL4.trans (hfold L hMK)
  apply hnm
  refine ContinuousLinearMap.ext fun v => ?_
  have hv : v ∈ K := htop Submodule.mem_top
  change ((a * a + 1 : E →L[ℝ] E)) v = 0 at hv
  rw [add_apply, one_apply_eq_self] at hv
  rw [neg_apply, one_apply_eq_self]
  exact eq_neg_of_add_eq_zero_left hv

/-- **Lemma 24.8 between two pieces** (Milnor p. 145): if `A² = −a₀²` on `M₀` and `−b²` on `M₁`
(both minimal), there is an isomorphism `T : M₀ ≅ M₁` with `TJ_α = J_αT`, `TJ = JT`,
`T(JA/a₀) = −(JA/b)T` (Milnor's "isomorphism from `M_h` to `M̄_j`"), for `k + 1 ≢ 3 (mod 4)`. -/
theorem IsOmegaOps.exists_inter (h : IsOmegaOps k a q j) (hk8 : k + 1 ≤ 8)
    (hk3 : (k + 1) % 4 ≠ 3) {M₀ M₁ : Submodule ℝ E} (hM₀ : IsMinInvar (omegaGens k a q j) M₀)
    (hM₁ : IsMinInvar (omegaGens k a q j) M₁) {a₀ b : ℝ} (ha₀ : 0 < a₀) (hb : 0 < b)
    (hc₀ : ∀ v ∈ M₀, a (a v) = -(a₀ ^ 2 • v)) (hc₁ : ∀ v ∈ M₁, a (a v) = -(b ^ 2 • v)) :
    ∃ T : M₀ ≃ₗ[ℝ] M₁, IsInter hM₀.2.1 hM₁.2.1 a₀⁻¹ (-b⁻¹) (T : M₀ →ₗ[ℝ] M₁) := by
  have hC₀ := h.isClifford_cliffFam (hM := hM₀.2.1) (s := a₀⁻¹) hc₀
    (by field_simp)
  have hC₁ := h.isClifford_cliffFam (hM := hM₁.2.1) (s := -b⁻¹) hc₁
    (by field_simp)
  have hm₀ := h.isMinimal_cliffFam (hM := hM₀.2.1) hM₀ (inv_ne_zero ha₀.ne')
  have hm₁ := h.isMinimal_cliffFam (hM := hM₁.2.1) hM₁ (neg_ne_zero.2 (inv_ne_zero hb.ne'))
  obtain ⟨T, hT⟩ := exists_iso_of_isMinimal hk8 hk3 hC₀ hC₁ hm₀ hm₁
  exact ⟨T, fun α h1 h2 v => hT α h1 h2 v⟩

theorem IsOmegaOps.exists_omegaPieceData (h : IsOmegaOps k a q j) (hk8 : k + 1 ≤ 8)
    (hk3 : (k + 1) % 4 ≠ 3)
    (hge : ∀ M : Submodule ℝ E, IsMinInvar (omegaGens k a q j) M → ∀ c : ℝ,
      (∀ v ∈ M, a (a v) = -(c • v)) → 1 ≤ c)
    (hnm : a * a ≠ -1) {r₀ : ℕ} (hr₀ : r₀ = 1 ∨ (r₀ = 2 ∧ k = 0)) :
    ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ), Nonempty (OmegaPieceData k a q j r₀ κ) ∧
      (Fintype.card κ + 1) * milnorM (k + 1) = finrank ℝ E := by
  classical
  obtain ⟨L, hL1, hL2, hL3, hL4⟩ := exists_minInvar_decomp h.isStarSigned ⊤ isInvar_top
  have hmin : ∀ M ∈ L, IsMinInvar (omegaGens k a q j) M := fun M hM => (hL1 M hM).1
  obtain ⟨M₀, hM₀L, c₀, hc₀, hc₀1⟩ := h.exists_piece_gt hnm hmin hL4 hge
  obtain ⟨i₀, hi₀⟩ := List.mem_iff_get.1 hM₀L
  have hsc : ∀ i : Fin L.length, ∃ c : ℝ, ∀ v ∈ L.get i, a (a v) = -(c • v) := fun i =>
    h.exists_sq_eq (hmin _ (List.get_mem L i))
  choose cf hcf using hsc
  have hcf1 : ∀ i, 1 ≤ cf i := fun i => hge _ (hmin _ (List.get_mem L i)) _ (hcf i)
  have horth : ∀ i i' : Fin L.length, i ≠ i' → L.get i ⟂ L.get i' := by
    intro i i' hii'
    have hp := List.pairwise_iff_get.1 hL2
    rcases lt_or_gt_of_ne hii' with hlt | hgt
    · exact hp i i' hlt
    · exact (hp i' i hgt).symm
  set a₀ := Real.sqrt c₀ with ha₀def
  have ha₀ : 1 < a₀ := by
    rw [ha₀def, Real.lt_sqrt zero_le_one]; simpa using hc₀1
  have ha₀sq : a₀ ^ 2 = c₀ := Real.sq_sqrt (by linarith)
  set κ := {i : Fin L.length // i ≠ i₀}
  set b : κ → ℝ := fun i => Real.sqrt (cf i.1) with hbdef
  have hb1 : ∀ i, 1 ≤ b i := fun i => by
    rw [hbdef, Real.le_sqrt zero_le_one (by linarith [hcf1 i.1])]; simpa using hcf1 i.1
  have hbsq : ∀ i, b i ^ 2 = cf i.1 := fun i => Real.sq_sqrt (by linarith [hcf1 i.1])
  have hM₀min := hmin M₀ hM₀L
  have hc₀' : ∀ v ∈ M₀, a (a v) = -(a₀ ^ 2 • v) := by rw [ha₀sq]; exact hc₀
  have hT : ∀ i : κ, ∃ T : M₀ ≃ₗ[ℝ] (L.get i.1), IsInter hM₀min.2.1
      (hmin _ (List.get_mem L i.1)).2.1 a₀⁻¹ (-(b i)⁻¹) (T : M₀ →ₗ[ℝ] L.get i.1) :=
    fun i => h.exists_inter hk8 hk3 hM₀min (hmin _ (List.get_mem L i.1)) (by linarith)
      (by linarith [hb1 i]) hc₀' (by rw [hbsq]; exact hcf i.1)
  choose T hTi using hT
  set d : κ × Fin r₀ → E →L[ℝ] E := fun i =>
    interOp (T i.1 : M₀ →ₗ[ℝ] L.get i.1.1) * a ^ (i.2 : ℕ) with hddef
  have hr₀2 : ∀ l : Fin r₀, (l : ℕ) ≠ 0 → k = 0 := fun l hl => by
    rcases hr₀ with rfl | ⟨rfl, hk⟩
    · exact absurd (Nat.lt_one_iff.1 l.2) hl
    · exact hk
  have hcommP : ∀ n : ℕ, M₀.starProjection * a ^ n = a ^ n * M₀.starProjection := fun n => by
    have hc : Commute M₀.starProjection a := ContinuousLinearMap.ext fun v =>
      hM₀min.2.1.starProjection_comm h.isStarSigned IsOmegaOps.a_mem v
    exact (hc.pow_right n).eq
  -- the fields
  have fq : ∀ i, d i * q = q * d i := fun i => by
    by_cases hl : (i.2 : ℕ) = 0
    · simp only [hddef, hl, pow_zero, mul_one]
      exact interOp_comm_q h (hTi i.1)
    · rw [h.q_zero (hr₀2 i.2 hl), mul_one, one_mul]
  have fj : ∀ i α, 1 ≤ α → α < k → d i * j α = j α * d i := fun i α h1 h2 => by
    have hl : (i.2 : ℕ) = 0 := by
      by_contra hl; have := hr₀2 i.2 hl; omega
    simp only [hddef, hl, pow_zero, mul_one]
    exact interOp_comm_j h (hTi i.1) h1 h2
  have hpow : ∀ n : ℕ, a ^ n * a = a * a ^ n := fun n => by rw [← pow_succ, pow_succ']
  have frel : ∀ i, b i.1 • (d i * a) = -a₀ • (a * d i) := fun i => by
    have hb0 : b i.1 ≠ 0 := by linarith [hb1 i.1]
    simp only [hddef]
    rw [mul_assoc, hpow, ← mul_assoc, interOp_a h (hTi i.1) (inv_ne_zero (by linarith)),
      smul_mul_assoc, smul_smul, show b i.1 * (a₀⁻¹⁻¹ * -(b i.1)⁻¹) = -a₀ by field_simp,
      mul_assoc]
  have fleft : ∀ i, a * (a * d i) = -(b i.1) ^ 2 • d i := fun i => by
    simp only [hddef]
    rw [← mul_assoc, ← mul_assoc, mul_assoc a a, a_a_interOp (hcf i.1.1), smul_mul_assoc,
      hbsq]
  have fright : ∀ i, d i * a * a = -a₀ ^ 2 • d i := fun i => by
    have hca : Commute (a ^ (i.2 : ℕ)) a := (Commute.refl a).pow_left _
    calc d i * a * a = interOp (T i.1 : M₀ →ₗ[ℝ] L.get i.1.1) * a * a * a ^ (i.2 : ℕ) := by
          simp only [hddef, mul_assoc, hca.eq]
      _ = -a₀ ^ 2 • d i := by
          rw [interOp_a_a h hM₀min.2.1 hc₀', smul_mul_assoc]
  have fR : ∀ i, d i * M₀.starProjection = d i := fun i => by
    simp only [hddef]
    rw [mul_assoc, ← hcommP, ← mul_assoc, interOp_starProjection]
  have fR' : ∀ i, ContinuousLinearMap.adjoint (d i) * M₀.starProjection = 0 := fun i => by
    have horth0 : M₀ ⟂ L.get i.1.1 := by
      rw [← hi₀]; exact horth i₀ i.1.1 (Ne.symm i.1.2)
    simp only [hddef]
    rw [← ContinuousLinearMap.star_eq_adjoint, star_mul, mul_assoc,
      ContinuousLinearMap.star_eq_adjoint (interOp _), adjoint_interOp_starProjection horth0,
      mul_zero]
  have fQ : ∀ (j' : κ) i, (L.get j'.1).starProjection * (a * d i) =
      if i.1 = j' then a * d i else 0 := fun j' i => by
    have e : (L.get j'.1).starProjection * (a * d i) =
        (L.get j'.1).starProjection * (a * interOp (T i.1 : M₀ →ₗ[ℝ] L.get i.1.1)) *
          a ^ (i.2 : ℕ) := by
      simp only [hddef, mul_assoc]
    rw [e]
    by_cases hij : i.1 = j'
    · subst hij
      rw [if_pos rfl, starProjection_a_interOp (hmin _ (List.get_mem L i.1.1)).2.1]
      simp only [hddef, mul_assoc]
    · rw [if_neg hij, starProjection_a_interOp_of_orth (hmin _ (List.get_mem L i.1.1)).2.1
        (horth j'.1 i.1.1 fun e => hij (Subtype.ext e).symm), zero_mul]
  have hc0 : ∀ j' : κ, cf j'.1 ≠ 0 := fun j' => by linarith [hcf1 j'.1]
  have find : ∀ j' : κ, LinearIndependent ℝ (fun l : Fin r₀ => a * d (j', l)) := fun j' => by
    rcases hr₀ with rfl | ⟨rfl, hk⟩
    · rw [linearIndependent_unique_iff]
      have : (default : Fin 1) = 0 := rfl
      simp only [hddef, this, Fin.val_zero, pow_zero, mul_one]
      exact a_interOp_ne_zero hM₀min.1 (T j').injective (hcf j'.1) (hc0 j')
    · have e : (fun l : Fin 2 => a * d (j', l)) =
          ![a * interOp (T j' : M₀ →ₗ[ℝ] L.get j'.1), a * interOp (T j' : M₀ →ₗ[ℝ] L.get j'.1) * a] := by
        funext l
        fin_cases l <;> simp [hddef, mul_assoc]
      rw [e]
      exact linearIndependent_a_interOp hM₀min.2.1 hM₀min.1 (T j').injective hc₀'
        (by positivity) (hcf j'.1) (hc0 j')
  -- the dimension count
  have hdimM : ∀ M ∈ L, finrank ℝ M = milnorM (k + 1) := fun M hM => by
    obtain ⟨c, hc⟩ := h.exists_sq_eq (hmin M hM)
    have hc1 := hge M (hmin M hM) c hc
    have hcpos : 0 < c := by linarith
    set s := (Real.sqrt c)⁻¹
    have hs : s * s * c = 1 := by
      simp only [s]
      rw [← mul_inv, Real.mul_self_sqrt hcpos.le, inv_mul_cancel₀ hcpos.ne']
    have hs0 : s ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 hcpos).ne'
    exact finrank_eq_milnorM_of_isMinimal hk8
      (h.isClifford_cliffFam (hM := (hmin M hM).2.1) (s := s) hc hs)
      (h.isMinimal_cliffFam (hM := (hmin M hM).2.1) (hmin M hM) hs0)
  have hsum : L.length * milnorM (k + 1) = finrank ℝ E := by
    rw [← finrank_top ℝ E, ← hL3, List.map_congr_left hdimM, List.map_const', List.sum_replicate,
      smul_eq_mul]
  have hcard : Fintype.card κ + 1 = L.length := by
    have := Fintype.card_subtype_compl (fun i : Fin L.length => i = i₀)
    simp only [Fintype.card_fin, Fintype.card_subtype_eq] at this
    have hpos : 0 < L.length := i₀.pos
    change Fintype.card {i : Fin L.length // ¬ i = i₀} + 1 = L.length
    rw [this]; omega
  have pd : OmegaPieceData k a q j r₀ κ :=
    { a₀ := a₀
      b := b
      d := d
      R := M₀.starProjection
      Q := fun j' => (L.get j'.1).starProjection
      ha₀ := ha₀
      hb := hb1
      hq := fq
      hj := fj
      rel := frel
      left := fleft
      right := fright
      hR := fR
      hR' := fR'
      hQ := fQ
      hind := find }
  refine ⟨κ, inferInstance, inferInstance, ⟨pd⟩, ?_⟩
  rw [hcard, hsum]

end Data

end Morse
