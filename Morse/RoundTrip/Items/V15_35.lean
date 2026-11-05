import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_35

open Matrix Set
open scoped Matrix ContDiff Topology unitInterval

namespace RoundTrip.V15_35

/-- The project's statement (universes instantiated at `0`, arbitrary finite index types): Milnor's
`i` for `k = 2` (`i = J_1`) and `k = 6` (`i = J_1⋯J_5`) satisfies `Morse.IsCentralI` (`i² = −1`,
`iᵀ = −i`, commutes with whatever commutes with `J_1, …, J_{k−1}`, anticommutes with whatever
anticommutes with them, commutes with the `J_α`); for any `ii` with `IsCentralI J k ii` (`k ≠ 0`)
and `p, X ∈ Ω_k(n)`, `|f(X)| = 1` for `f(X) = det_ℂ(pᵀX)`, `f(p) = 1`, and
`f(p exp(tV)) = e^{−√−1 t tr(V·ii)/2}` for `V ∈ 𝒯_p`; the classes `omegaComp J k ii w` (paths from
`J_k` to `−J_k` in the stratum of `J_k`, angle of `f` ending at `w`) are clopen in the project's
path space (Milnor's metric) and pairwise disjoint; and a path agreeing on `[0, 1]` with
`J_k exp(tV)` lies in `omegaComp w` iff `w = −tr(V·ii)/2`. -/
def A : Prop :=
  type_of% @Morse.isCentralI_two.{0} ∧ type_of% @Morse.isCentralI_six.{0} ∧
    type_of% @Morse.norm_omegaF.{0} ∧ type_of% @Morse.omegaF_self.{0} ∧
    type_of% @Morse.omegaF_geo.{0} ∧ type_of% @Morse.isClopen_omegaComp.{0} ∧
    type_of% @Morse.disjoint_omegaComp.{0} ∧ type_of% @Morse.mem_omegaComp_geo_iff.{0}

theorem A_holds : A :=
  ⟨@Morse.isCentralI_two.{0}, @Morse.isCentralI_six.{0}, @Morse.norm_omegaF.{0},
    @Morse.omegaF_self.{0}, @Morse.omegaF_geo.{0}, @Morse.isClopen_omegaComp.{0},
    @Morse.disjoint_omegaComp.{0}, @Morse.mem_omegaComp_geo_iff.{0}⟩

/-! ### Vocabulary: B's `Ω_k(n)`, `det_ℂ`, `tr_ℂ`, `i` -/

section Vocab
variable {ι : Type} [Fintype ι] [DecidableEq ι]
set_option linter.unusedSectionVars false

theorem isACFam_iff (Js : ℕ → Mat ι) (m : ℕ) : IsACFam Js m ↔ Morse.IsAnticommFamily Js m :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.cs, h.anti⟩⟩

theorem omegaK_eq_omega (Js : ℕ → Mat ι) (k : ℕ) : OmegaK Js k = Morse.Omega Js k := by
  cases k with
  | zero => rfl
  | succ k =>
    ext J
    simp only [OmegaK, Morse.Omega, IsCplxStr, Morse.IsComplexStructure, AntiComm,
      Set.mem_ofPred_eq]
    refine and_congr Iff.rfl (forall_congr' fun α => forall_congr' fun _ => forall_congr' fun _ =>
      ⟨fun h => by rw [h, neg_neg], fun h => by rw [h, neg_neg]⟩)

theorem one_sub_projQ (i : Mat ι) : 1 - projQ i = Morse.projM i := by
  rw [show projQ i = Morse.projP i from rfl, ← Morse.projP_add_projM (ii := i),
    add_sub_cancel_left]

/-- B's `det_ℂ` is the project's `cdet`. -/
theorem cdet_eq (i U : Mat ι) : cdet i U = Morse.cdet i U := by
  rw [cdet, Morse.cdet, one_sub_projQ]
  rfl

/-- B's `tr_ℂ A = tr(A_ℂ Q)` is `−√−1·tr(A·i)/2` for `tr A = 0`. -/
theorem ctr_eq (i A : Mat ι) (htr : trace A = 0) :
    ctr i A = (((-(trace (A * i)) / 2 : ℝ)) : ℂ) * Complex.I := by
  rw [ctr, show projQ i = Morse.projP i from rfl, show cplx A = Morse.cplx A from rfl,
    Morse.projP, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one,
    Matrix.mul_smul, trace_smul, trace_sub, trace_smul, ← map_mul, Morse.trace_cplx,
    Morse.trace_cplx, htr]
  push_cast
  simp only [smul_eq_mul]
  ring

theorem iProd_succ (Js : ℕ → Mat ι) (m : ℕ) : iProd Js (m + 1) = iProd Js m * Js (m + 1) := rfl

theorem iProd_mem_orth (Js : ℕ → Mat ι) :
    ∀ m, (∀ α, 1 ≤ α → α ≤ m → Js α ∈ orthogonalGroup ι ℝ) → iProd Js m ∈ orthogonalGroup ι ℝ
  | 0, _ => (orthogonalGroup ι ℝ).one_mem
  | m + 1, h => by
    rw [iProd_succ]
    exact (orthogonalGroup ι ℝ).mul_mem (iProd_mem_orth Js m fun α h1 h2 => h α h1 (by omega))
      (h (m + 1) (by omega) le_rfl)

theorem comm_iProd (Js : ℕ → Mat ι) (X : Mat ι) :
    ∀ m, (∀ α, 1 ≤ α → α ≤ m → Commute X (Js α)) → Commute X (iProd Js m)
  | 0, _ => Commute.one_right X
  | m + 1, h => by
    rw [iProd_succ]
    exact (comm_iProd Js X m fun α h1 h2 => h α h1 (by omega)).mul_right
      (h (m + 1) (by omega) le_rfl)

/-- `Y (J_1 ⋯ J_m) = (−1)^m (J_1 ⋯ J_m) Y` when `Y` anticommutes with `J_1, …, J_m`. -/
theorem anti_iProd (Js : ℕ → Mat ι) (Y : Mat ι) :
    ∀ m, (∀ α, 1 ≤ α → α ≤ m → Y * Js α = -(Js α * Y)) →
      Y * iProd Js m = ((-1 : ℝ) ^ m) • (iProd Js m * Y)
  | 0, _ => by simp [iProd]
  | m + 1, h => by
    have ih := anti_iProd Js Y m fun α h1 h2 => h α h1 (by omega)
    rw [iProd_succ, ← Matrix.mul_assoc, ih, Matrix.smul_mul, Matrix.mul_assoc,
      h (m + 1) (by omega) le_rfl, Matrix.mul_neg, pow_succ, mul_neg_one, neg_smul, smul_neg,
      ← Matrix.mul_assoc]

theorem isACFam_mono {Js : ℕ → Mat ι} {m : ℕ} (h : IsACFam Js (m + 1)) : IsACFam Js m :=
  ⟨fun α h1 h2 => h.1 α h1 (by omega), fun α β h1 h2 h3 h4 hne => h.2 α β h1 (by omega) h3
    (by omega) hne⟩

/-- `(J_1 ⋯ J_m)² = (−1)^{m(m+1)/2}`. -/
theorem sq_iProd (Js : ℕ → Mat ι) :
    ∀ m, IsACFam Js m → iProd Js m * iProd Js m = ((-1 : ℝ) ^ (m * (m + 1) / 2)) • 1
  | 0, _ => by simp [iProd]
  | m + 1, h => by
    have ih := sq_iProd Js m (isACFam_mono h)
    have hanti := anti_iProd Js (Js (m + 1)) m fun α h1 h2 =>
      h.2 (m + 1) α (by omega) le_rfl h1 (by omega) (by omega)
    have hJJ : Js (m + 1) * Js (m + 1) = -1 := (h.1 (m + 1) (by omega) le_rfl).2
    have hdiv : (m + 1) * (m + 1 + 1) / 2 = m * (m + 1) / 2 + (m + 1) := by
      rw [show (m + 1) * (m + 1 + 1) = m * (m + 1) + 2 * (m + 1) by ring,
        Nat.add_mul_div_left _ _ two_pos]
    rw [iProd_succ]
    calc iProd Js m * Js (m + 1) * (iProd Js m * Js (m + 1))
        = iProd Js m * (Js (m + 1) * iProd Js m) * Js (m + 1) := by simp only [Matrix.mul_assoc]
      _ = ((-1 : ℝ) ^ m) • ((iProd Js m * iProd Js m) * (Js (m + 1) * Js (m + 1))) := by
          rw [hanti, Matrix.mul_smul, Matrix.smul_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [ih, hJJ, hdiv, Matrix.smul_mul, Matrix.one_mul, smul_smul, smul_neg, ← neg_smul]
          congr 1
          ring

/-- `J_α (J_1 ⋯ J_m) = (−1)^{m+1} (J_1 ⋯ J_m) J_α` for `1 ≤ α ≤ m`. -/
theorem jcomm_iProd (Js : ℕ → Mat ι) :
    ∀ m, IsACFam Js m → ∀ α, 1 ≤ α → α ≤ m →
      Js α * iProd Js m = ((-1 : ℝ) ^ (m + 1)) • (iProd Js m * Js α)
  | 0, _, α, h1, h2 => absurd h2 (by omega)
  | m + 1, h, α, h1, h2 => by
    rw [iProd_succ]
    rcases (show α ≤ m ∨ α = m + 1 by omega) with hα | rfl
    · have ih := jcomm_iProd Js m (isACFam_mono h) α h1 hα
      have hanti : Js α * Js (m + 1) = -(Js (m + 1) * Js α) :=
        h.2 α (m + 1) h1 (by omega) (by omega) le_rfl (by omega)
      rw [← Matrix.mul_assoc, ih, Matrix.smul_mul, Matrix.mul_assoc, hanti, Matrix.mul_neg,
        ← Matrix.mul_assoc, smul_neg, ← neg_smul, pow_succ (-1 : ℝ) (m + 1), mul_neg_one]
    · have hanti := anti_iProd Js (Js (m + 1)) m fun β h1 h2 =>
        h.2 (m + 1) β (by omega) le_rfl h1 (by omega) (by omega)
      rw [← Matrix.mul_assoc, hanti, Matrix.smul_mul, Matrix.mul_assoc, pow_succ, pow_succ,
        mul_neg_one, mul_neg_one, neg_neg]

theorem transpose_eq_neg {J : Mat ι} (hJ : IsCplxStr J) : Jᵀ = -J := by
  have h1 : Jᵀ * J = 1 := by
    have := hJ.1
    rw [Matrix.mem_orthogonalGroup_iff'] at this
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using this
  calc Jᵀ = Jᵀ * (J * -J) := by rw [Matrix.mul_neg, hJ.2, neg_neg, Matrix.mul_one]
    _ = -J := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

/-- **Milnor's `i = J_1 ⋯ J_{k−1}` for every `k ≡ 2 (mod 4)`** satisfies the project's
`IsCentralI` (proved outright; A has it only for `k = 2, 6`). -/
theorem isCentralI_iProd {Js : ℕ → Mat ι} {k : ℕ} (hk : k % 4 = 2) (hJ : IsACFam Js (k - 1)) :
    Morse.IsCentralI Js k (iProd Js (k - 1)) := by
  obtain ⟨q, hq⟩ : ∃ q, k - 1 = 4 * q + 1 := ⟨k / 4, by omega⟩
  have hsq : iProd Js (k - 1) * iProd Js (k - 1) = -1 := by
    rw [sq_iProd Js (k - 1) hJ, hq]
    have : (4 * q + 1) * (4 * q + 1 + 1) / 2 = 2 * (4 * q * q + 3 * q) + 1 := by
      rw [show (4 * q + 1) * (4 * q + 1 + 1) = 2 * (2 * (4 * q * q + 3 * q) + 1) by ring]
      exact Nat.mul_div_cancel_left _ two_pos
    rw [this, pow_succ, pow_mul]
    simp
  have hcs : IsCplxStr (iProd Js (k - 1)) :=
    ⟨iProd_mem_orth Js _ fun α h1 h2 => (hJ.1 α h1 h2).1, hsq⟩
  refine ⟨hsq, transpose_eq_neg hcs, fun A hA => ?_, fun X hX => ?_, fun α h1 h2 => ?_⟩
  · exact (comm_iProd Js A (k - 1) fun α h1 h2 => hA α h1 (by omega)).eq
  · have hpow : ((-1 : ℝ)) ^ (4 * q + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    rw [anti_iProd Js X (k - 1) fun α h1 h2 => by rw [hX α h1 (by omega), neg_neg], hq, hpow,
      neg_one_smul]
  · rw [jcomm_iProd Js (k - 1) hJ α h1 (by omega), show k - 1 + 1 = 2 * (2 * q + 1) by omega,
      pow_mul]
    simp

theorem inv_eq_transpose {J : Mat ι} (hJ : J ∈ orthogonalGroup ι ℝ) : J⁻¹ = Jᵀ := by
  have h1 : Jᵀ * J = 1 := by
    rw [Matrix.mem_orthogonalGroup_iff'] at hJ
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using hJ
  exact Matrix.inv_eq_left_inv h1

theorem mem_orth_of_omegaK {Js : ℕ → Mat ι} {k : ℕ} {J : Mat ι} (hJ : J ∈ OmegaK Js k) :
    J ∈ orthogonalGroup ι ℝ := by
  cases k with
  | zero => exact hJ
  | succ k => exact hJ.1.1

/-- B's `f(X) = det_ℂ(J⁻¹X)` is the project's `omegaF i J X = det_ℂ(JᵀX)`. -/
theorem fJ_eq {Js : ℕ → Mat ι} {k : ℕ} {J : Mat ι} (hJ : J ∈ OmegaK Js k) (i X : Mat ι) :
    fJ i J X = Morse.omegaF i J X := by
  rw [fJ, cdet_eq, inv_eq_transpose (mem_orth_of_omegaK hJ)]
  rfl

end Vocab

/-! ### Glue: B's path space `OmIn` and its metric `d`

B's `rhoIn` is a real infimum (`0` for an empty set) and `d` a real supremum (`0` if unbounded),
so "`d(w, w')` small ⇒ `w, w'` uniformly close" needs, for paths `w, w'` from the same point,
an actual piecewise smooth path between `w(s)` and `w'(s)` (back along `w`, then along `w'`) with
length bounded uniformly in `s`. Built from the project's `IsPiecewiseSmooth` toolkit
(`reverse`, `translate`, `concat`, path lengths); B's subdivision form `IsPWOn` and the project's
break-point form are converted both ways (sorting the break points); B's `deriv` (elementwise
norm) is definitionally the project's (same topology), `ContDiffOn` is transported along the
identity. -/

section Glue
open Morse
open scoped Morse.MatrixInner RealInnerProductSpace
variable {ι : Type} [Fintype ι] [DecidableEq ι]
set_option linter.unusedSectionVars false

theorem contDiffOn_frob_of_elem {c : ℝ → Mat ι} {s : Set ℝ}
    (hc : @ContDiffOn ℝ _ ℝ _ _ (Mat ι) Matrix.normedAddCommGroup Matrix.normedSpace ∞ c s) :
    ContDiffOn ℝ ∞ c s :=
  @ContDiff.comp_contDiffOn ℝ ℝ (Mat ι) (Mat ι) _ _ _ Matrix.normedAddCommGroup
    Matrix.normedSpace _ _ ∞ s _ c
    (@ContinuousLinearMap.contDiff ℝ (Mat ι) (Mat ι) _ Matrix.normedAddCommGroup
      Matrix.normedSpace _ _ ∞ (ContinuousLinearMap.id ℝ (Mat ι))) hc

theorem contDiffOn_elem_of_frob {c : ℝ → Mat ι} {s : Set ℝ} (hc : ContDiffOn ℝ ∞ c s) :
    @ContDiffOn ℝ _ ℝ _ _ (Mat ι) Matrix.normedAddCommGroup Matrix.normedSpace ∞ c s :=
  @ContDiff.comp_contDiffOn ℝ ℝ (Mat ι) (Mat ι) _ _ _ _ _ Matrix.normedAddCommGroup
    Matrix.normedSpace ∞ s _ c
    (@ContinuousLinearMap.contDiff ℝ (Mat ι) (Mat ι) _ _ _ Matrix.normedAddCommGroup
      Matrix.normedSpace ∞ (ContinuousLinearMap.id ℝ (Mat ι))) hc

theorem frob_self (X : Mat ι) : frob X X = ‖X‖ ^ 2 := by
  have : frob X X = ⟪X, X⟫ := by
    rw [Morse.inner_def, frob, ← trace_transpose, transpose_mul, transpose_transpose,
      trace_mul_comm]
    rfl
  rw [this, real_inner_self_eq_norm_sq]

theorem sqrt_frob (X : Mat ι) : Real.sqrt (frob X X) = ‖X‖ := by
  rw [frob_self, Real.sqrt_sq (norm_nonneg _)]

theorem lenM_eq (w : ℝ → Mat ι) : lenM w = pathLength w 0 1 := by
  simp only [lenM, sqrt_frob]
  rfl

theorem lenM_nonneg (w : ℝ → Mat ι) : 0 ≤ lenM w :=
  intervalIntegral.integral_nonneg zero_le_one fun _ _ => Real.sqrt_nonneg _

/-- B's subdivision form gives the project's piecewise smoothness on `[0, 1]`. -/
theorem isPWS_of_isPWOn {f : ℝ → Mat ι} (h : IsPWOn f) : IsPiecewiseSmooth f 0 1 := by
  classical
  obtain ⟨k, t, ht0, htk, hmono, hsm⟩ := h
  have hsm' : ∀ i < k, ContDiffOn ℝ ∞ f (Icc (t i) (t (i + 1))) := fun i hi =>
    contDiffOn_frob_of_elem (hsm i hi)
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; rw [ht0] at htk; norm_num at htk
    · exact h0
  have hmon : ∀ i j, i ≤ j → j ≤ k → t i ≤ t j := by
    intro i j hij hjk
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih => exact (ih (by omega)).trans (hmono j (by omega)).le
  have hcont : ∀ j ≤ k, ContinuousOn f (Icc 0 (t j)) := by
    intro j
    induction j with
    | zero => intro _; rw [ht0, Icc_self]; exact continuousOn_singleton f 0
    | succ j ih =>
      intro hj
      have h0j : 0 ≤ t j := ht0 ▸ hmon 0 j (Nat.zero_le _) (by omega)
      rw [← Icc_union_Icc_eq_Icc h0j (hmono j (by omega)).le]
      exact (ih (by omega)).union_of_isClosed (hsm' j (by omega)).continuousOn isClosed_Icc
        isClosed_Icc
  refine ⟨zero_le_one, by simpa [htk] using hcont k le_rfl, (Finset.range (k + 1)).image t,
    fun s u hs hsu hu hB => ?_⟩
  have hex : ∃ i, s < t (i + 1) := ⟨k - 1, by rw [Nat.sub_add_cancel hk, htk]; linarith⟩
  have hi : s < t (Nat.find hex + 1) := Nat.find_spec hex
  have hik : Nat.find hex < k := by
    have := Nat.find_min' hex (show s < t (k - 1 + 1) by rw [Nat.sub_add_cancel hk, htk]; linarith)
    omega
  have hti : t (Nat.find hex) ≤ s := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0, ht0]; exact hs
    · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      push Not at this
      rwa [Nat.sub_add_cancel hpos] at this
  have hut : u ≤ t (Nat.find hex + 1) := by
    by_contra hcon
    push Not at hcon
    exact hB (t (Nat.find hex + 1))
      (Finset.mem_image.2 ⟨Nat.find hex + 1, Finset.mem_range.2 (by omega), rfl⟩) ⟨hi, hcon⟩
  exact (hsm' _ hik).mono (Icc_subset_Icc hti hut)

/-- The project's piecewise smoothness on `[0, 1]` gives B's subdivision form (sort the break
points in `(0, 1)` together with `0, 1`). -/
theorem isPWOn_of_isPWS {f : ℝ → Mat ι} (h : IsPiecewiseSmooth f 0 1) : IsPWOn f := by
  classical
  obtain ⟨-, -, B, hB⟩ := h
  set S : Finset ℝ := insert 0 (insert 1 (B.filter (fun x => 0 < x ∧ x < 1))) with hSdef
  have hS01 : ∀ x ∈ S, 0 ≤ x ∧ x ≤ 1 := by
    intro x hx
    simp only [hSdef, Finset.mem_insert, Finset.mem_filter] at hx
    rcases hx with rfl | rfl | ⟨-, h1, h2⟩
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨zero_le_one, le_rfl⟩
    · exact ⟨h1.le, h2.le⟩
  have h0S : (0 : ℝ) ∈ S := Finset.mem_insert_self _ _
  have h1S : (1 : ℝ) ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hm2 : 2 ≤ S.card := by
    have hsub : ({0, 1} : Finset ℝ) ⊆ S := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      exacts [h0S, h1S]
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair (by norm_num)] at this
  set e := S.orderEmbOfFin rfl with he
  have hmemS : ∀ j, e j ∈ S := fun j => by
    have := Set.mem_range_self (f := e) j
    rwa [he, Finset.range_orderEmbOfFin] at this
  set t : ℕ → ℝ := fun j => if hj : j < S.card then e ⟨j, hj⟩ else 1 with htdef
  have ht : ∀ j (hj : j < S.card), t j = e ⟨j, hj⟩ := fun j hj => dif_pos hj
  refine ⟨S.card - 1, t, ?_, ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [ht 0 (by omega), he, Finset.orderEmbOfFin_zero rfl (by omega)]
    exact le_antisymm (Finset.min'_le _ _ h0S) (hS01 _ (Finset.min'_mem _ _)).1
  · rw [ht _ (by omega), he, Finset.orderEmbOfFin_last rfl (by omega)]
    exact le_antisymm (hS01 _ (Finset.max'_mem _ _)).2 (Finset.le_max' _ _ h1S)
  · rw [ht i (by omega), ht (i + 1) (by omega)]
    exact e.strictMono (Fin.mk_lt_mk.2 (Nat.lt_succ_self i))
  · rw [ht i (by omega), ht (i + 1) (by omega)]
    apply contDiffOn_elem_of_frob
    refine hB _ _ (hS01 _ (hmemS _)).1 (e.strictMono (Fin.mk_lt_mk.2 (Nat.lt_succ_self i)))
      (hS01 _ (hmemS _)).2 fun x hx hxI => ?_
    have hx01 : 0 < x ∧ x < 1 :=
      ⟨(hS01 _ (hmemS _)).1.trans_lt hxI.1, hxI.2.trans_le (hS01 _ (hmemS _)).2⟩
    have hxS : x ∈ S :=
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hx, hx01⟩))
    have hxr : x ∈ Set.range e := by rw [he, Finset.range_orderEmbOfFin]; exact hxS
    obtain ⟨j, rfl⟩ := hxr
    have h1 := e.lt_iff_lt.1 hxI.1
    have h2 := e.lt_iff_lt.1 hxI.2
    rw [Fin.lt_def] at h1 h2
    simp only at h1 h2
    omega

/-- Rescaling `[0, L]` to `[0, 1]`. -/
theorem isPWS_scale {c : ℝ → Mat ι} {L : ℝ} (hL : 0 < L) (h : IsPiecewiseSmooth c 0 L) :
    IsPiecewiseSmooth (fun u => c (L * u)) 0 1 := by
  obtain ⟨-, hcont, B, hB⟩ := h
  refine ⟨zero_le_one, hcont.comp (continuous_const.mul continuous_id).continuousOn
    (fun x hx => ⟨by nlinarith [hx.1], by nlinarith [hx.2]⟩), B.image (fun x => x / L),
    fun s u hs hsu hu hB' => ?_⟩
  have hc := hB (L * s) (L * u) (by positivity) (by nlinarith) (by nlinarith)
    fun x hx hx' => hB' (x / L) (Finset.mem_image.2 ⟨x, hx, rfl⟩)
      ⟨by rw [lt_div_iff₀ hL]; linarith [hx'.1], by rw [div_lt_iff₀ hL]; linarith [hx'.2]⟩
  exact hc.comp (contDiff_const.mul contDiff_id).contDiffOn
    fun x hx => ⟨by nlinarith [hx.1], by nlinarith [hx.2]⟩

theorem pathLength_scale (c : ℝ → Mat ι) {L : ℝ} (hL : 0 < L) :
    pathLength (fun u => c (L * u)) 0 1 = pathLength c 0 L := by
  have hd : ∀ u, deriv (fun u => c (L * u)) u = L • deriv c (L * u) := fun u =>
    deriv_comp_mul_left L c u
  simp only [pathLength, hd, norm_smul, Real.norm_eq_abs, abs_of_pos hL]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun x => ‖deriv c x‖) hL.ne']
  simp only [mul_zero, mul_one, smul_eq_mul]
  field_simp

theorem isPathIn_const {N : Set (Mat ι)} {x : Mat ι} (hx : x ∈ N) :
    IsPathIn N (fun _ => x) :=
  ⟨isPWOn_of_isPWS (IsPiecewiseSmooth.of_contDiffOn (s := univ) contDiffOn_const zero_le_one
    (subset_univ _)), fun _ _ => hx⟩

theorem lenM_const (x : Mat ι) : lenM (fun _ : ℝ => x) = 0 := by
  rw [lenM_eq]
  simp [pathLength]

/-- **A path between `w(s)` and `w'(s)`** (back along `w`, then along `w'`), of length at most
`L(w) + L(w')`. -/
theorem exists_path_between {N : Set (Mat ι)} {p q : Mat ι} (w w' : OmIn N p q) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ sg : ℝ → Mat ι, IsPathIn N sg ∧ sg 0 = w.1 s ∧ sg 1 = w'.1 s ∧
      lenM sg ≤ lenM w.1 + lenM w'.1 := by
  have hw := isPWS_of_isPWOn w.2.1.1
  have hw' := isPWS_of_isPWOn w'.2.1.1
  have hwN := w.2.1.2
  have hwN' := w'.2.1.2
  have hw0 : w.1 0 = p := w.2.2.1
  have hw0' : w'.1 0 = p := w'.2.2.1
  rcases eq_or_lt_of_le hs.1 with h0 | hpos
  · subst h0
    refine ⟨fun _ => p, isPathIn_const (hw0 ▸ hwN 0 ⟨le_rfl, zero_le_one⟩), hw0.symm,
      hw0'.symm, ?_⟩
    rw [lenM_const]
    exact add_nonneg (lenM_nonneg _) (lenM_nonneg _)
  set c₁ : ℝ → Mat ι := fun u => w.1 (0 + s - u) with hc₁
  set c₂ : ℝ → Mat ι := fun u => w'.1 (u + -s) with hc₂
  have h₁ : IsPiecewiseSmooth c₁ 0 s := (hw.mono le_rfl hs.1 hs.2).reverse
  have h₂ : IsPiecewiseSmooth c₂ s (2 * s) := by
    have := (hw'.mono le_rfl hs.1 hs.2).translate (-s)
    rwa [show (0 : ℝ) - -s = s by ring, show s - -s = 2 * s by ring] at this
  have hm : c₁ s = c₂ s := by simp only [hc₁, hc₂]; rw [zero_add, sub_self, add_neg_cancel, hw0, hw0']
  have hc := h₁.concat h₂ hm
  set c : ℝ → Mat ι := fun u => if u ≤ s then c₁ u else c₂ u with hcdef
  have hsg := isPWS_scale (by positivity : (0 : ℝ) < 2 * s) hc
  refine ⟨fun u => c (2 * s * u), ⟨isPWOn_of_isPWS hsg, fun u hu => ?_⟩, ?_, ?_, ?_⟩
  · simp only [hcdef]
    split_ifs with h
    · exact hwN _ ⟨by nlinarith [hu.2], by nlinarith [hu.1, hs.2]⟩
    · push Not at h
      exact hwN' _ ⟨by linarith, by nlinarith [hu.2, hs.2]⟩
  · simp only [hcdef, mul_zero, if_pos hs.1, hc₁, zero_add, sub_zero]
  · simp only [hcdef, mul_one, if_neg (show ¬ 2 * s ≤ s by linarith), hc₂]
    rw [show 2 * s + -s = s by ring]
  · rw [lenM_eq, pathLength_scale c (by positivity : (0 : ℝ) < 2 * s), hcdef,
      pathLength_concat h₁.isAdmissible h₂.isAdmissible, hc₁, pathLength_reverse, hc₂]
    have htr := pathLength_translate w'.1 0 s (-s)
    rw [show (0 : ℝ) - -s = s by ring, show s - -s = 2 * s by ring] at htr
    rw [htr, lenM_eq, lenM_eq]
    exact add_le_add (hw.isAdmissible.pathLength_le le_rfl hs.1 hs.2)
      (hw'.isAdmissible.pathLength_le le_rfl hs.1 hs.2)

theorem rho_bounds {N : Set (Mat ι)} {p q : Mat ι} (w w' : OmIn N p q) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖w'.1 s - w.1 s‖ ≤ rhoIn N (w.1 s) (w'.1 s) ∧
      rhoIn N (w.1 s) (w'.1 s) ≤ lenM w.1 + lenM w'.1 := by
  obtain ⟨sg, hsg, hsg0, hsg1, hsglen⟩ := exists_path_between w w' hs
  have hbdd : BddBelow {L | ∃ v, IsPathIn N v ∧ v 0 = w.1 s ∧ v 1 = w'.1 s ∧ lenM v = L} :=
    ⟨0, by rintro L ⟨v, -, -, -, rfl⟩; exact lenM_nonneg v⟩
  refine ⟨le_csInf ⟨_, sg, hsg, hsg0, hsg1, rfl⟩ ?_,
    (csInf_le hbdd ⟨sg, hsg, hsg0, hsg1, rfl⟩).trans hsglen⟩
  rintro L ⟨v, hv, hv0, hv1, rfl⟩
  rw [← hv0, ← hv1, lenM_eq]
  exact (isPWS_of_isPWOn hv.1).isAdmissible.norm_sub_le_pathLength

/-- **Small `d` means uniformly close**: `‖w'(s) − w(s)‖ ≤ d(w, w')`. -/
theorem norm_sub_le_dOmIn {N : Set (Mat ι)} {p q : Mat ι} (w w' : OmIn N p q) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : ‖w'.1 s - w.1 s‖ ≤ dOmIn N w.1 w'.1 := by
  have hb : BddAbove (Set.range fun t : Icc (0 : ℝ) 1 => rhoIn N (w.1 t) (w'.1 t)) :=
    ⟨lenM w.1 + lenM w'.1, by rintro _ ⟨t, rfl⟩; exact (rho_bounds w w' t.2).2⟩
  calc ‖w'.1 s - w.1 s‖ ≤ rhoIn N (w.1 s) (w'.1 s) := (rho_bounds w w' hs).1
    _ ≤ ⨆ t : Icc (0 : ℝ) 1, rhoIn N (w.1 t) (w'.1 t) :=
        le_ciSup (f := fun t : Icc (0 : ℝ) 1 => rhoIn N (w.1 t) (w'.1 t)) hb ⟨s, hs⟩
    _ ≤ dOmIn N w.1 w'.1 := le_add_of_nonneg_right (Real.sqrt_nonneg _)

theorem dOmIn_self {N : Set (Mat ι)} {p q : Mat ι} (w : OmIn N p q) : dOmIn N w.1 w.1 = 0 := by
  have hr : ∀ t : Icc (0 : ℝ) 1, rhoIn N (w.1 t) (w.1 t) = 0 := by
    intro t
    have h := (rho_bounds w w t.2).1
    rw [sub_self, norm_zero] at h
    refine le_antisymm ?_ h
    exact csInf_le ⟨0, by rintro L ⟨v, -, -, -, rfl⟩; exact lenM_nonneg v⟩
      ⟨fun _ => w.1 t, isPathIn_const (w.2.1.2 t t.2), rfl, rfl, lenM_const _⟩
  have : Nonempty (Icc (0 : ℝ) 1) := ⟨⟨0, le_rfl, zero_le_one⟩⟩
  simp only [dOmIn, hr, ciSup_const, sub_self, zero_pow two_ne_zero,
    intervalIntegral.integral_zero, Real.sqrt_zero, add_zero]

/-- The winding of `F ∘ w` (B's `InClass`, for a general `F` and end value `x`). -/
def Wind (F : Mat ι → ℂ) (w : unitInterval → Mat ι) (x : ℝ) : Prop :=
  ∃ θ : unitInterval → ℝ, Continuous θ ∧ θ 0 = 0 ∧ θ 1 = x ∧
    ∀ t, F (w t) = Complex.exp ((θ t : ℂ) * Complex.I)

theorem continuous_path {N : Set (Mat ι)} {p q : Mat ι} (w : OmIn N p q) :
    Continuous fun t : unitInterval => w.1 t :=
  (isPWS_of_isPWOn w.2.1.1).2.1.comp_continuous continuous_subtype_val fun t => t.2

/-- **The winding is locally constant for B's metric.** -/
theorem exists_wind_congr {N K : Set (Mat ι)} (hNK : N ⊆ K) (hK : IsCompact K)
    {F : Mat ι → ℂ} (hF : Continuous F) (hF1 : ∀ x ∈ K, ‖F x‖ = 1) {p q : Mat ι} :
    ∃ δ > 0, ∀ w w' : OmIn N p q, dOmIn N w.1 w'.1 < δ → ∀ x : ℝ,
      (Wind F (fun t => w.1 t) x ↔ Wind F (fun t => w'.1 t) x) := by
  obtain ⟨δ, hδ, hδF⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous hF.continuousOn) 1 one_pos
  have key : ∀ w w' : OmIn N p q, (∀ t : unitInterval, ‖F (w'.1 t) - F (w.1 t)‖ < 1) →
      ∀ x, Wind F (fun t => w.1 t) x → Wind F (fun t => w'.1 t) x := by
    rintro w w' hclose x ⟨θ, hθc, hθ0, hθ1, hθF⟩
    have hlift : IsAngleLift F w.1 ⟨θ, hθc⟩ := ⟨hθ0, hθF⟩
    obtain ⟨θ', hθ', hθ'1⟩ := hlift.perturb (hF.comp (continuous_path w))
      (hF.comp (continuous_path w')) (fun t => hF1 _ (hNK (w.2.1.2 t t.2)))
      (fun t => hF1 _ (hNK (w'.2.1.2 t t.2))) hclose
      (by simp only [Set.Icc.coe_zero, w.2.2.1, w'.2.2.1])
    refine ⟨θ', θ'.continuous, hθ'.1, ?_, hθ'.2⟩
    rw [hθ'1 (by simp only [Set.Icc.coe_one, w.2.2.2.1, w'.2.2.2.1])]
    exact hθ1
  refine ⟨δ, hδ, fun w w' hd x => ⟨key w w' (fun t => ?_) x, key w' w (fun t => ?_) x⟩⟩
  · have := hδF _ (hNK (w'.2.1.2 t t.2)) _ (hNK (w.2.1.2 t t.2))
      (by rw [dist_eq_norm]; exact (norm_sub_le_dOmIn w w' t.2).trans_lt hd)
    rwa [dist_eq_norm] at this
  · have := hδF _ (hNK (w.2.1.2 t t.2)) _ (hNK (w'.2.1.2 t t.2))
      (by rw [dist_eq_norm, ← norm_neg, neg_sub]
          exact (norm_sub_le_dOmIn w w' t.2).trans_lt hd)
    rwa [dist_eq_norm] at this

/-- **The classes are open and closed in B's topology** (hence unions of path components). -/
theorem wind_iff_of_joined {N K : Set (Mat ι)} (hNK : N ⊆ K) (hK : IsCompact K)
    {F : Mat ι → ℂ} (hF : Continuous F) (hF1 : ∀ x ∈ K, ‖F x‖ = 1) {p q : Mat ι}
    {w w' : OmIn N p q} (h : Joined w w') (x : ℝ) :
    Wind F (fun t => w.1 t) x ↔ Wind F (fun t => w'.1 t) x := by
  obtain ⟨δ, hδ, hδw⟩ := exists_wind_congr (p := p) (q := q) hNK hK hF hF1
  set S : Set (OmIn N p q) := {v | Wind F (fun t => v.1 t) x} with hS
  have hball : ∀ v : OmIn N p q, IsOpen {v' : OmIn N p q | dOmIn N v.1 v'.1 < δ} := fun v =>
    TopologicalSpace.isOpen_generateFrom_of_mem ⟨v, δ, rfl⟩
  have hopen : ∀ (P : OmIn N p q → Prop), (∀ v v', dOmIn N v.1 v'.1 < δ → (P v ↔ P v')) →
      IsOpen {v | P v} := by
    intro P hP
    refine isOpen_iff_forall_mem_open.2 fun v hv => ⟨_, fun v' hv' => (hP v v' hv').1 hv,
      hball v, ?_⟩
    change dOmIn N v.1 v.1 < δ
    rw [dOmIn_self]
    exact hδ
  have hclopen : IsClopen S :=
    ⟨isOpen_compl_iff.1 (hopen (fun v => ¬ Wind F (fun t => v.1 t) x)
      fun v v' hd => not_congr (hδw v v' hd x)), hopen _ fun v v' hd => hδw v v' hd x⟩
  set γ := h.somePath
  have h0' : γ 0 = w := γ.source
  have h1' : γ 1 = w' := γ.target
  have hpre : IsClopen (γ ⁻¹' S) := hclopen.preimage γ.continuous
  rcases isClopen_iff.1 hpre with he | hu
  · constructor
    · intro hw
      have : (0 : unitInterval) ∈ γ ⁻¹' S := by rw [Set.mem_preimage, h0']; exact hw
      rw [he] at this; exact absurd this (Set.notMem_empty _)
    · intro hw
      have : (1 : unitInterval) ∈ γ ⁻¹' S := by rw [Set.mem_preimage, h1']; exact hw
      rw [he] at this; exact absurd this (Set.notMem_empty _)
  · have h0 : (0 : unitInterval) ∈ γ ⁻¹' S := hu ▸ Set.mem_univ _
    have h1 : (1 : unitInterval) ∈ γ ⁻¹' S := hu ▸ Set.mem_univ _
    rw [Set.mem_preimage, h0'] at h0
    rw [Set.mem_preimage, h1'] at h1
    exact ⟨fun _ => h1, fun _ => h0⟩

end Glue

/-! ### A ⇒ B -/

theorem A_to_B : A → B := by
  rintro ⟨-, -, hnorm, -, hgeo, -, -, -⟩
  intro n k Js hk hJs
  have hii := isCentralI_iProd hk hJs
  have hk0 : k ≠ 0 := by omega
  set i := iProd Js (k - 1) with hidef
  refine ⟨⟨hii.sq, fun α h1 h2 => hii.jcomm α h1 (by omega)⟩, fun J hJ => ?_⟩
  have hJo := mem_orth_of_omegaK hJ
  have hJΩ : J ∈ Morse.Omega Js k := omegaK_eq_omega Js k ▸ hJ
  have hF1 : ∀ X ∈ OmegaK Js k, ‖fJ i J X‖ = 1 := fun X hX => by
    rw [fJ_eq hJ]
    exact hnorm hii hk0 hJΩ (omegaK_eq_omega Js k ▸ hX)
  refine ⟨fun J' hJ' => ⟨?_, hF1 J' hJ'⟩, fun _ => ⟨fun c w w' hww' => ?_, ?_⟩⟩
  · rw [inv_eq_transpose hJo]
    exact hii.comm_transpose_mul hk0 hJΩ (omegaK_eq_omega Js k ▸ hJ')
  · -- the classes are unions of path components
    have hFc : Continuous (fJ i J) := by
      have : fJ i J = fun X => Morse.cdet i (J⁻¹ * X) := funext fun X => by rw [fJ, cdet_eq]
      rw [this]
      exact (Morse.continuous_cdet i).comp (continuous_const.mul continuous_id)
    have hK : IsCompact (OmegaK Js k) := omegaK_eq_omega Js k ▸ Morse.isCompact_omega Js k
    exact wind_iff_of_joined subset_rfl hK hFc hF1 hww' _
  · -- the geodesics
    intro A hA hAJ hAα hexp c
    have hAt : A ∈ Morse.tanAlg Js k J :=
      ⟨by rw [conjTranspose_eq_transpose_of_trivial]; exact hA, fun _ => hAJ,
        fun α h1 h2 => (hAα α h1 (by omega)).eq⟩
    have htr : trace A = 0 := by
      have h := congrArg trace hA
      rw [trace_transpose, trace_neg] at h
      linarith
    let θ₀ : C(unitInterval, ℝ) :=
      ⟨fun t => -((Real.pi * (t : ℝ)) * trace (A * i)) / 2, by fun_prop⟩
    have hθ₀ : Morse.IsAngleLift (fJ i J) (fun t : ℝ => J * mexp ((Real.pi * t) • A)) θ₀ :=
      ⟨by simp [θ₀], fun t => by
        rw [fJ_eq hJ]
        exact hgeo hii hJΩ hAt (Real.pi * t)⟩
    rw [ctr_eq i A htr]
    have hm : (0 : ℝ) < Real.pi := Real.pi_pos
    constructor
    · rintro ⟨θ, hθc, hθ0, hθ1, hθF⟩
      have hu := Morse.IsAngleLift.unique (θ₁ := ⟨θ, hθc⟩) ⟨hθ0, hθF⟩ hθ₀
      have h1 : θ 1 = θ₀ 1 := congrArg (fun φ : C(unitInterval, ℝ) => φ 1) hu
      rw [hθ1] at h1
      simp only [θ₀, ContinuousMap.coe_mk, Set.Icc.coe_one, mul_one] at h1
      have h2 : -(trace (A * i)) = (c : ℝ) * (mK k : ℝ) := by
        have := congrArg (fun x => x * 2 / Real.pi) h1
        field_simp at this
        linarith
      rw [show -(trace (A * i)) / 2 = (c : ℝ) * (mK k : ℝ) / 2 by rw [h2]]
      push_cast
      ring
    · intro hc
      refine ⟨θ₀, θ₀.continuous, hθ₀.1, ?_, hθ₀.2⟩
      have h2 : -(trace (A * i)) / 2 = (c : ℝ) * (mK k : ℝ) / 2 := by
        have := congrArg Complex.im hc
        simpa [Complex.mul_im] using this
      simp only [θ₀, ContinuousMap.coe_mk, Set.Icc.coe_one, mul_one]
      linear_combination Real.pi * h2

/-! ### B ⇒ A, only vacuously

A is about an ABSTRACT `ii` with `IsCentralI J k ii` for every `k ≠ 0`, on the project's path
space of the stratum of `J_k`; B is about `i = J_1⋯J_{k−1}`, `k ≡ 2 (mod 4)`, on the blind path
space with its own metric. Nothing of A is an instance of B; A is re-proved outright, by the
project's arguments (its lemmas `norm_cdet`, `cdet_one`, `cdet_exp`, `isClopen_windSet`,
`disjoint_windSet`, `IsAngleLift.unique`, the Clifford simp set; none of the item's theorems). -/

section Outright
open Morse
open scoped Morse.MatrixInner
variable {ι : Type} [Fintype ι] [DecidableEq ι] {J : ℕ → Matrix ι ι ℝ} {k : ℕ}

theorem isCentralI_two' (hJ : IsAnticommFamily J 1) : IsCentralI J 2 (J 1) where
  sq := (hJ.cs 1 le_rfl le_rfl).2
  skew := (hJ.cs 1 le_rfl le_rfl).transpose
  comm A hA := hA 1 le_rfl (by norm_num)
  anti X hX := by rw [hX 1 le_rfl (by norm_num), neg_neg]
  jcomm α h1 h2 := by
    obtain rfl : α = 1 := by omega
    rfl

theorem isCentralI_six' (hJ : IsAnticommFamily J 5) :
    IsCentralI J 6 (J 1 * J 2 * J 3 * J 4 * J 5) where
  sq := by
    have h := hJ.isClifford
    clifford_simp h
  skew := by
    have h := hJ.isClifford
    have ht : ∀ α, 1 ≤ α → α ≤ 5 → (J α)ᵀ = -J α := fun α h1 h2 => (hJ.cs α h1 h2).transpose
    simp only [transpose_mul, ht 1 le_rfl (by norm_num), ht 2 (by norm_num) (by norm_num),
      ht 3 (by norm_num) (by norm_num), ht 4 (by norm_num) (by norm_num),
      ht 5 (by norm_num) le_rfl]
    clifford_simp h
  comm A hA := by
    have hc : ∀ α, 1 ≤ α → α ≤ 5 → Commute A (J α) := fun α h1 h2 => hA α h1 (by omega)
    exact ((((hc 1 le_rfl (by norm_num)).mul_right (hc 2 (by norm_num) (by norm_num))).mul_right
      (hc 3 (by norm_num) (by norm_num))).mul_right (hc 4 (by norm_num) (by norm_num))).mul_right
      (hc 5 (by norm_num) le_rfl) |>.eq
  anti X hX := by
    have h1 : ∀ α, 1 ≤ α → α ≤ 5 → ∀ Y, X * (J α * Y) = -(J α * (X * Y)) := fun α h1 h2 Y => by
      rw [← Matrix.mul_assoc, show X * J α = -(J α * X) by rw [hX α h1 (by omega), neg_neg],
        Matrix.neg_mul, Matrix.mul_assoc]
    have h0 : X * J 5 = -(J 5 * X) := by rw [hX 5 (by norm_num) (by norm_num), neg_neg]
    simp only [Matrix.mul_assoc, h1 1 le_rfl (by norm_num), h1 2 (by norm_num) (by norm_num),
      h1 3 (by norm_num) (by norm_num), h1 4 (by norm_num) (by norm_num), h0, Matrix.mul_neg,
      neg_neg]
  jcomm α h1 h2 := by
    have h := hJ.isClifford
    interval_cases α <;> clifford_simp h

variable {ii p : Matrix ι ι ℝ}

theorem comm_transpose_mul' (hii : IsCentralI J k ii) (hk : k ≠ 0)
    (hp : p ∈ Omega J k) {X : Matrix ι ι ℝ} (hX : X ∈ Omega J k) :
    pᵀ * X * ii = ii * (pᵀ * X) := by
  have hpi := hii.anti p (anti_of_mem_omega hk hp)
  have hXi := hii.anti X (anti_of_mem_omega hk hX)
  have hpt : pᵀ * ii = -(ii * pᵀ) := by
    have := congrArg transpose hpi
    rw [transpose_mul, transpose_neg, transpose_mul, hii.skew, Matrix.mul_neg, Matrix.neg_mul,
      neg_inj] at this
    rw [this, neg_neg]
  rw [Matrix.mul_assoc, hXi, Matrix.mul_neg, ← Matrix.mul_assoc, hpt, Matrix.neg_mul, neg_neg,
    Matrix.mul_assoc]

theorem norm_omegaF' (hii : IsCentralI J k ii) (hk : k ≠ 0) (hp : p ∈ Omega J k)
    {X : Matrix ι ι ℝ} (hX : X ∈ Omega J k) : ‖omegaF ii p X‖ = 1 := by
  refine norm_cdet hii.sq hii.skew (comm_transpose_mul' hii hk hp hX) ?_
  have hpo := omega_orth hp
  have hXo : X * Xᴴ = 1 := mul_eq_one_comm.1 (omega_orth hX)
  rw [conjTranspose_real] at hpo hXo
  rw [transpose_mul, transpose_transpose]
  calc pᵀ * X * (Xᵀ * p) = pᵀ * (X * Xᵀ) * p := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hXo, Matrix.mul_one, hpo]

theorem omegaF_self' (hp : p ∈ Omega J k) : omegaF ii p p = 1 := by
  have hpo := omega_orth hp
  rw [conjTranspose_real] at hpo
  rw [omegaF, hpo, cdet_one]

theorem omegaF_geo' (hii : IsCentralI J k ii) (hp : p ∈ Omega J k) {V : Matrix ι ι ℝ}
    (hV : V ∈ tanAlg J k p) (t : ℝ) :
    omegaF ii p (p * NormedSpace.exp (t • V)) =
      Complex.exp (((-(t * trace (V * ii)) / 2 : ℝ) : ℂ) * Complex.I) := by
  have hpo := omega_orth hp
  rw [conjTranspose_real] at hpo
  rw [omegaF, ← Matrix.mul_assoc, hpo, Matrix.one_mul]
  exact cdet_exp hii.sq (hii.comm V hV.2.2) (trace_eq_zero_of_skew_real hV.1) t

theorem isClopen_omegaComp' (hJ : IsAnticommFamily J k) (hk : k ≠ 0) (hii : IsCentralI J k ii)
    (w : ℝ) : IsClopen (omegaComp J k ii w) :=
  isClopen_windSet (continuous_omegaF ii _) (isCompact_omega J k) (omegaStratum_subset _)
    (fun _ hX => norm_omegaF' hii hk (basePt_mem_omega hJ) hX) w

theorem mem_omegaComp_geo_iff' (hJ : IsAnticommFamily J k) (hii : IsCentralI J k ii)
    {γ : ℝ → Matrix ι ι ℝ}
    (hγ : γ ∈ pathSpace (omegaStratum J k (basePt J k)) (basePt J k) (-basePt J k))
    {V : Matrix ι ι ℝ} (hV : V ∈ tanAlg J k (basePt J k))
    (heq : EqOn γ (fun t => basePt J k * NormedSpace.exp (t • V)) (Icc 0 1)) (w : ℝ) :
    (⟨γ, hγ⟩ : PathSp _ _ _) ∈ omegaComp J k ii w ↔ w = -trace (V * ii) / 2 := by
  have hp := basePt_mem_omega hJ
  let θ : C(I, ℝ) := ⟨fun t => -((t : ℝ) * trace (V * ii)) / 2, by fun_prop⟩
  have hθ : IsAngleLift (omegaF ii (basePt J k)) γ θ :=
    ⟨by simp [θ], fun t => by
      rw [heq t.2, omegaF_geo' hii hp hV]
      rfl⟩
  constructor
  · rintro ⟨θ', hθ', hθ'w⟩
    rw [← hθ'w, hθ'.unique hθ]
    simp [θ]
  · intro hw
    exact ⟨θ, hθ, by simp [θ, hw]⟩

theorem disjoint_omegaComp' {w w' : ℝ} (h : w ≠ w') :
    Disjoint (omegaComp J k ii w) (omegaComp J k ii w') :=
  disjoint_windSet h

end Outright

theorem B_to_A : B → A := fun _ =>
  ⟨@isCentralI_two', @isCentralI_six', @norm_omegaF', @omegaF_self', @omegaF_geo',
    @isClopen_omegaComp', @disjoint_omegaComp',
    @mem_omegaComp_geo_iff'⟩

#rt_check RoundTrip.V15_35.A_to_B [Morse.isCentralI_two, Morse.isCentralI_six, Morse.norm_omegaF,
  Morse.omegaF_self, Morse.omegaF_geo, Morse.isClopen_omegaComp, Morse.disjoint_omegaComp,
  Morse.mem_omegaComp_geo_iff]
#rt_check RoundTrip.V15_35.B_to_A [Morse.isCentralI_two, Morse.isCentralI_six, Morse.norm_omegaF,
  Morse.omegaF_self, Morse.omegaF_geo, Morse.isClopen_omegaComp, Morse.disjoint_omegaComp,
  Morse.mem_omegaComp_geo_iff]

#rt_overlap RoundTrip.V15_35.B_to_A [Morse.isCentralI_two, Morse.isCentralI_six, Morse.norm_omegaF,
  Morse.omegaF_self, Morse.omegaF_geo, Morse.isClopen_omegaComp, Morse.disjoint_omegaComp,
  Morse.mem_omegaComp_geo_iff]

end RoundTrip.V15_35
