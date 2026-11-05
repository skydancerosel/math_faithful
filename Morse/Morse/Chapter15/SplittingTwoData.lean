import Morse.Chapter15.SplittingTwo
import Mathlib.Algebra.DirectSum.LinearMap

/-!
Milnor, *Morse Theory*, §24, pp. 147–148 (case `k ≡ 2 (mod 4)`); Exposition/Chapter15.md, §6.

# The splitting of a geodesic for `k ≡ 2 (mod 4)` and the data for the index bound

## Milnor's text, paraphrased

(p. 147) `ℝⁿ = M_1 ⊕ ⋯ ⊕ M_ν`, `A = a_h i` on `M_h` with `a_h` odd, `dim M_h = m_k`, and the
geodesic lies in `Ω^{(c)}` with `c = a_1 + ⋯ + a_ν`.  (p. 148) If some `a_{h₀} ≥ 3`, the pairs
`(h₀, j)` with `a_j < 0` give at least `(ν − c)/4` conjugate points, counted with multiplicity.

## What is formalized

* `Morse.exists_decomp_two`: the splitting, with `A = a_h i` on `M_h`, `a_h` odd,
  `ν · m_{k+1} = n`, and **`tr(A·i) = −m_{k+1} Σ_h a_h`** (the trace splits along the internal
  direct sum).
* `Morse.TwoPieceData` and `Morse.exists_twoPieceData_of_decomp`: from a piece `M₀` with
  `a₀ ≥ 3`, intertwiners `D_j` (`DA = a₀Di`, `AD = a_jiD`, `DJ = −JD`, `DJ_α = J_αD`, with the
  projections `R` onto `M₀` and `Q_j` onto `M_j`) to every piece with `a_j < 0`, and the count
  **`ν − Σ_h a_h ≤ 4 Σ_j ((a₀ − a_j)/2 − 1)`**.

## What Milnor leaves implicit

* The count: `Σ_j ((a₀ − a_j)/2 − 1) ≥ Σ_{a_j < 0} (|a_j| + 1)/2 ≥ q/2` with `q` the sum of the
  `|a_j|`, `a_j < 0`, and `2q = Σ|a_h| − Σa_h ≥ ν − c`.
-/

open Set Module

noncomputable section

namespace Morse

section TwoData

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {k : ℕ} {a q : E →L[ℝ] E} {j : ℕ → E →L[ℝ] E}

omit [FiniteDimensional ℝ E] in
theorem foldr_sup_le_iSup (L : List (Submodule ℝ E)) :
    L.foldr (· ⊔ ·) ⊥ ≤ ⨆ i : Fin L.length, L.get i := by
  have hfold : ∀ (L' : List (Submodule ℝ E)) (X : Submodule ℝ E), (∀ M ∈ L', M ≤ X) →
      L'.foldr (· ⊔ ·) ⊥ ≤ X := by
    intro L' X
    induction L' with
    | nil => intro _; exact bot_le
    | cons M L'' ih =>
      intro hL'
      rw [List.foldr_cons]
      exact sup_le (hL' M List.mem_cons_self) (ih fun M' hM' => hL' M' (List.mem_cons_of_mem _ hM'))
  exact hfold L _ fun M hM => by
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hM
    exact le_iSup (fun i : Fin L.length => L.get i) i

/-- **The splitting for `k ≡ 2 (mod 4)`** (Milnor p. 147): minimal pieces `M_h`, odd integers
`a_h` with `A = a_h i` on `M_h`, `ν · m_{k+1} = n`, and `tr(A·i) = −m_{k+1} Σ a_h`. -/
theorem exists_decomp_two (h : IsOmegaOps k a q j) (hI : IsIOps k a q j) (hk : k ≠ 0)
    (hk8 : k + 1 ≤ 8)
    (hodd : ∀ M : Submodule ℝ E, IsMinInvar (omegaGens k a q j) M → ∀ c : ℝ,
      (∀ v ∈ M, a v = c • iWord k j v) → ∃ n : ℤ, c = 2 * n + 1) :
    ∃ (L : List (Submodule ℝ E)) (cs : Fin L.length → ℤ),
      (∀ i, IsMinInvar (omegaGens k a q j) (L.get i)) ∧
      (∀ i i', i ≠ i' → L.get i ⟂ L.get i') ∧
      (∀ i, ∀ v ∈ L.get i, a v = (cs i : ℝ) • iWord k j v) ∧ (∀ i, Odd (cs i)) ∧
      L.length * milnorM (k + 1) = finrank ℝ E ∧
      LinearMap.trace ℝ E ((a * iWord k j : E →L[ℝ] E) : E →ₗ[ℝ] E) =
        -((milnorM (k + 1) : ℝ) * ∑ i, (cs i : ℝ)) ∧
      ((∀ i, cs i ^ 2 = 1) → a * a = -1) := by
  classical
  obtain ⟨L, hL1, hL2, hL3, hL4⟩ := exists_minInvar_decomp h.isStarSigned ⊤ isInvar_top
  have hmin : ∀ i : Fin L.length, IsMinInvar (omegaGens k a q j) (L.get i) := fun i =>
    (hL1 _ (List.get_mem L i)).1
  have hsc : ∀ i : Fin L.length, ∃ n : ℤ,
      ∀ v ∈ L.get i, a v = ((2 * n + 1 : ℤ) : ℝ) • iWord k j v := fun i => by
    obtain ⟨c, hc⟩ := h.exists_eq_smul_iWord hI hk (hmin i)
    obtain ⟨n, rfl⟩ := hodd _ (hmin i) c hc
    exact ⟨n, by push_cast; exact hc⟩
  choose n hn using hsc
  set cs : Fin L.length → ℤ := fun i => 2 * n i + 1 with hcsdef
  have hodd' : ∀ i, Odd (cs i) := fun i => ⟨n i, rfl⟩
  have hcs0 : ∀ i, (cs i : ℝ) ≠ 0 := fun i h0 => by
    have : cs i = 0 := by exact_mod_cast h0
    exact (Int.not_even_iff_odd.2 (hodd' i)) (this ▸ Even.zero)
  have hn' : ∀ i, ∀ v ∈ L.get i, a v = (cs i : ℝ) • iWord k j v := hn
  have horth : ∀ i i', i ≠ i' → L.get i ⟂ L.get i' := by
    intro i i' hii'
    have hp := List.pairwise_iff_get.1 hL2
    rcases lt_or_gt_of_ne hii' with hlt | hgt
    · exact hp i i' hlt
    · exact (hp i' i hgt).symm
  have hdimi : ∀ i : Fin L.length, finrank ℝ (L.get i) = milnorM (k + 1) := fun i =>
    finrank_eq_milnorM_of_isMinimal hk8
      (h.isClifford_cliffFam (hM := (hmin i).2.1) (s := (cs i : ℝ)⁻¹)
        (a_a_of_eq_smul hI (iWord_mem_of_isInvar (hmin i).2.1) (hn' i)) (by field_simp [hcs0 i]))
      (h.isMinimal_cliffFam (hmin i) (inv_ne_zero (hcs0 i)))
  have hdimM : ∀ M ∈ L, finrank ℝ M = milnorM (k + 1) := fun M hM => by
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hM
    exact hdimi i
  have hsum : L.length * milnorM (k + 1) = finrank ℝ E := by
    rw [← finrank_top ℝ E, ← hL3, List.map_congr_left hdimM, List.map_const', List.sum_replicate,
      smul_eq_mul]
  have hint : DirectSum.IsInternal (fun i : Fin L.length => L.get i) := by
    refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
    · exact OrthogonalFamily.independent
        (orthogonalFamily_iff_pairwise.2 fun i i' hii' => horth i i' hii')
    · exact eq_top_iff.2 (hL4.trans (foldr_sup_le_iSup L))
  set f : E →ₗ[ℝ] E := ((a * iWord k j : E →L[ℝ] E) : E →ₗ[ℝ] E) with hfdef
  have hf : ∀ i, MapsTo f (L.get i) (L.get i) := fun i v hv =>
    (hmin i).2.1 a IsOmegaOps.a_mem _ (iWord_mem_of_isInvar (hmin i).2.1 v hv)
  have hres : ∀ i, f.restrict (hf i) = (-(cs i : ℝ)) • LinearMap.id := fun i => by
    ext ⟨v, hv⟩
    have hee : iWord k j (iWord k j v) = -v := by
      have := congrArg (fun F : E →L[ℝ] E => F v) hI.sq
      simpa using this
    simp only [LinearMap.restrict_apply, LinearMap.smul_apply, LinearMap.id_apply,
      SetLike.val_smul, hfdef]
    change a (iWord k j v) = _
    rw [hn' i _ (iWord_mem_of_isInvar (hmin i).2.1 v hv), hee, smul_neg, ← neg_smul]
  refine ⟨L, cs, hmin, horth, hn', hodd', hsum, ?_, fun hall => ?_⟩
  swap
  · set K := LinearMap.ker (((a * a + 1 : E →L[ℝ] E)) : E →ₗ[ℝ] E) with hK
    have hle : ∀ i, L.get i ≤ K := fun i v hv => by
      change (a * a + 1 : E →L[ℝ] E) v = 0
      have h2 : ((cs i : ℝ)) ^ 2 = 1 := by exact_mod_cast hall i
      rw [add_apply, mul_apply_eq_comp, one_apply_eq_self,
        a_a_of_eq_smul hI (iWord_mem_of_isInvar (hmin i).2.1) (hn' i) v hv, h2, one_smul,
        neg_add_cancel]
    have htop : (⊤ : Submodule ℝ E) ≤ K := (hL4.trans (foldr_sup_le_iSup L)).trans (iSup_le hle)
    refine ContinuousLinearMap.ext fun v => ?_
    have hv : (a * a + 1 : E →L[ℝ] E) v = 0 := htop Submodule.mem_top
    rw [add_apply, one_apply_eq_self] at hv
    rw [neg_apply, one_apply_eq_self]
    exact eq_neg_of_add_eq_zero_left hv
  rw [LinearMap.trace_eq_sum_trace_restrict hint hf]
  simp only [hres, map_smul, LinearMap.trace_id, hdimi, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

variable (k a q j) in
/-- **The data for the index bound, `k ≡ 2 (mod 4)`** (Milnor p. 148): a piece `M₀` with
`A = a₀ i`, `a₀ ≥ 3`, and intertwiners `D_j : M₀ → M_j` to pieces with `A = b_j i`, `b_j < 0`. -/
structure TwoPieceData (κ : Type*) [DecidableEq κ] where
  a₀ : ℤ
  b : κ → ℤ
  d : κ → E →L[ℝ] E
  R : E →L[ℝ] E
  Q : κ → E →L[ℝ] E
  ha₀ : 3 ≤ a₀
  hb : ∀ i, b i < 0
  heven : ∀ i, Even (a₀ - b i)
  hq : ∀ i, d i * q = -(q * d i)
  hj : ∀ i α, 1 ≤ α → α < k → d i * j α = j α * d i
  da : ∀ i, d i * a = (a₀ : ℝ) • (d i * iWord k j)
  ad : ∀ i, a * d i = (b i : ℝ) • (iWord k j * d i)
  hR : ∀ i, d i * R = d i
  hR' : ∀ i, ContinuousLinearMap.adjoint (d i) * R = 0
  Ra : R * a = a * R
  Re : R * iWord k j = iWord k j * R
  hQ : ∀ j' i, Q j' * d i = if i = j' then d i else 0
  hne : ∀ i, d i ≠ 0

/-- **Building the data** from a piece with `a_{h₀} ≥ 3` (Milnor p. 148, with Lemma 24.8), and
**the count** `ν − Σ a_h ≤ 4 Σ_j ((a₀ − a_j)/2 − 1)`. -/
theorem exists_twoPieceData_of_decomp (h : IsOmegaOps k a q j) (hI : IsIOps k a q j)
    (hk : k ≠ 0) (hk8 : k ≤ 8) (hk3 : k % 4 ≠ 3) {L : List (Submodule ℝ E)}
    {cs : Fin L.length → ℤ} (hmin : ∀ i, IsMinInvar (omegaGens k a q j) (L.get i))
    (horth : ∀ i i', i ≠ i' → L.get i ⟂ L.get i')
    (hcs : ∀ i, ∀ v ∈ L.get i, a v = (cs i : ℝ) • iWord k j v) (hodd : ∀ i, Odd (cs i))
    {i₀ : Fin L.length} (h3 : 3 ≤ cs i₀) :
    ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (pd : TwoPieceData k a q j κ),
      (L.length : ℤ) - ∑ i, cs i ≤ 4 * ∑ i, ((pd.a₀ - pd.b i) / 2 - 1) := by
  classical
  set κ := {i : Fin L.length // cs i < 0}
  set M₀ := L.get i₀ with hM₀def
  have hM₀ := hmin i₀
  have hcsR : ∀ i, (cs i : ℝ) ≠ 0 := fun i h0 => by
    have : cs i = 0 := by exact_mod_cast h0
    exact (Int.not_even_iff_odd.2 (hodd i)) (this ▸ Even.zero)
  have hne₀ : ∀ i : κ, i₀ ≠ i.1 := fun i he => by
    have := i.2; rw [← he] at this; omega
  have hT : ∀ i : κ, ∃ T : M₀ ≃ₗ[ℝ] L.get i.1, (∀ α, 1 ≤ α → α < k → ∀ (x : M₀)
      (hx : j α x ∈ M₀), (T ⟨j α x, hx⟩ : E) = j α (T x)) ∧
      ∀ (x : M₀) (hx : q x ∈ M₀), (T ⟨q x, hx⟩ : E) = -q (T x) := fun i =>
    exists_inter_two h hI hk hk8 hk3 hM₀ (hmin i.1) (hcsR i₀) (hcsR i.1) (hcs i₀) (hcs i.1)
  choose T hTj hTq using hT
  -- the projection onto `M₀` commutes with `i`
  have hstar : IsStarSigned ({iWord k j} : Set (E →L[ℝ] E)) := by
    intro g hg; rw [Set.mem_singleton_iff.1 hg]; exact Or.inr hI.skew
  have hinv : IsInvar ({iWord k j} : Set (E →L[ℝ] E)) M₀ := by
    intro g hg w hw; rw [Set.mem_singleton_iff.1 hg]; exact iWord_mem_of_isInvar hM₀.2.1 w hw
  have hPe : ∀ v, (M₀.orthogonalProjectionOnto (iWord k j v) : E) =
      iWord k j (M₀.orthogonalProjectionOnto v) := fun v => by
    have := hinv.starProjection_comm hstar (Set.mem_singleton _) v
    simpa only [Submodule.starProjection_apply] using this
  have hPg : ∀ g ∈ omegaGens k a q j, ∀ v, (M₀.orthogonalProjectionOnto (g v) : E) =
      g (M₀.orthogonalProjectionOnto v) := fun g hg v =>
    hM₀.2.1.orthogonalProjectionOnto_comm h hg v
  set d : κ → E →L[ℝ] E := fun i => interOp ((T i : M₀ ≃ₗ[ℝ] L.get i.1) : M₀ →ₗ[ℝ] L.get i.1)
    with hddef
  have hdapp : ∀ i v, d i v = (T i (M₀.orthogonalProjectionOnto v) : E) := fun i v => rfl
  have fq : ∀ i, d i * q = -(q * d i) := fun i => by
    refine ContinuousLinearMap.ext fun v => ?_
    change d i (q v) = -(q (d i v))
    have e : M₀.orthogonalProjectionOnto (q v) =
        ⟨q (M₀.orthogonalProjectionOnto v), hM₀.2.1 q IsOmegaOps.q_mem _ (Submodule.coe_mem _)⟩ :=
      Subtype.ext (hPg q IsOmegaOps.q_mem v)
    rw [hdapp, hdapp, e, hTq]
  have fj : ∀ i α, 1 ≤ α → α < k → d i * j α = j α * d i := fun i α h1 h2 => by
    refine ContinuousLinearMap.ext fun v => ?_
    change d i (j α v) = j α (d i v)
    have e : M₀.orthogonalProjectionOnto (j α v) =
        ⟨j α (M₀.orthogonalProjectionOnto v),
          hM₀.2.1 (j α) (IsOmegaOps.j_mem h1 h2) _ (Submodule.coe_mem _)⟩ :=
      Subtype.ext (hPg _ (IsOmegaOps.j_mem h1 h2) v)
    rw [hdapp, hdapp, e, hTj i α h1 h2]
  have fda : ∀ i, d i * a = (cs i₀ : ℝ) • (d i * iWord k j) := fun i => by
    refine ContinuousLinearMap.ext fun v => ?_
    change d i (a v) = (cs i₀ : ℝ) • d i (iWord k j v)
    have e : M₀.orthogonalProjectionOnto (a v) =
        (cs i₀ : ℝ) • M₀.orthogonalProjectionOnto (iWord k j v) := Subtype.ext (by
      rw [hPg a IsOmegaOps.a_mem, hcs i₀ _ (Submodule.coe_mem _), Submodule.coe_smul, hPe])
    rw [hdapp, hdapp, e, map_smul, Submodule.coe_smul]
  have fad : ∀ i, a * d i = (cs i.1 : ℝ) • (iWord k j * d i) := fun i => by
    refine ContinuousLinearMap.ext fun v => ?_
    change a (d i v) = (cs i.1 : ℝ) • iWord k j (d i v)
    rw [hdapp]
    exact hcs i.1 _ (Submodule.coe_mem _)
  have fR : ∀ i, d i * M₀.starProjection = d i := fun i => interOp_starProjection
  have fR' : ∀ i, ContinuousLinearMap.adjoint (d i) * M₀.starProjection = 0 := fun i =>
    adjoint_interOp_starProjection (horth i₀ i.1 (hne₀ i))
  have fRa : M₀.starProjection * a = a * M₀.starProjection := ContinuousLinearMap.ext fun v =>
    hM₀.2.1.starProjection_comm h.isStarSigned IsOmegaOps.a_mem v
  have fRe : M₀.starProjection * iWord k j = iWord k j * M₀.starProjection :=
    ContinuousLinearMap.ext fun v => hinv.starProjection_comm hstar (Set.mem_singleton _) v
  have fQ : ∀ (j' i : κ), (L.get j'.1).starProjection * d i = if i = j' then d i else 0 := by
    intro j' i
    split_ifs with hij
    · subst hij
      refine ContinuousLinearMap.ext fun v => ?_
      change (L.get i.1).starProjection (d i v) = d i v
      rw [hdapp]
      exact Submodule.starProjection_eq_self_iff.2 (Submodule.coe_mem _)
    · refine ContinuousLinearMap.ext fun v => ?_
      change (L.get j'.1).starProjection (d i v) = 0
      rw [hdapp]
      have hne : j'.1 ≠ i.1 := fun e => hij (Subtype.ext e).symm
      exact (Submodule.starProjection_apply_eq_zero_iff _).2
        ((horth j'.1 i.1 hne).symm.le (Submodule.coe_mem _))
  have fne : ∀ i, d i ≠ 0 := fun i h0 => by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM₀.1
    have := congrArg (fun F : E →L[ℝ] E => F x) h0
    change d i x = 0 at this
    rw [hddef, interOp_apply_mem hx] at this
    have hT0 : T i ⟨x, hx⟩ = 0 := Subtype.ext this
    exact hx0 (congrArg Subtype.val ((T i).injective (hT0.trans (map_zero _).symm)))
  have heven : ∀ i : κ, Even (cs i₀ - cs i.1) := fun i => (hodd i₀).sub_odd (hodd i.1)
  refine ⟨κ, inferInstance, inferInstance,
    { a₀ := cs i₀, b := fun i => cs i.1, d := d, R := M₀.starProjection,
      Q := fun j' => (L.get j'.1).starProjection, ha₀ := h3, hb := fun i => i.2,
      heven := heven, hq := fq, hj := fj, da := fda, ad := fad, hR := fR, hR' := fR',
      Ra := fRa, Re := fRe, hQ := fQ, hne := fne }, ?_⟩
  -- the count
  change (L.length : ℤ) - ∑ i, cs i ≤ 4 * ∑ i : κ, ((cs i₀ - cs i.1) / 2 - 1)
  have h1 : ∀ i, 1 ≤ |cs i| := fun i =>
    Int.one_le_abs fun h0 => (Int.not_even_iff_odd.2 (hodd i)) (h0 ▸ Even.zero)
  have h2 : (L.length : ℤ) ≤ ∑ i, |cs i| := by
    calc (L.length : ℤ) = ∑ _i : Fin L.length, (1 : ℤ) := by simp
      _ ≤ ∑ i, |cs i| := Finset.sum_le_sum fun i _ => h1 i
  have h3' : ∑ i, (|cs i| - cs i) = ∑ i : κ, (-2 * cs i.1) := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun i => cs i < 0) (by simp)
      (fun i => -2 * cs i), Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hneg
    · rw [abs_of_neg hneg]; ring
    · rw [abs_of_nonneg (not_lt.1 hneg)]; ring
  have h4 : ∀ i : κ, -2 * cs i.1 ≤ 4 * ((cs i₀ - cs i.1) / 2 - 1) := fun i => by
    obtain ⟨m, hm⟩ := heven i
    rw [hm, show (m + m) / 2 = m by omega]
    have := i.2
    omega
  calc (L.length : ℤ) - ∑ i, cs i ≤ ∑ i, (|cs i| - cs i) := by
        rw [Finset.sum_sub_distrib]; linarith
    _ = ∑ i : κ, (-2 * cs i.1) := h3'
    _ ≤ ∑ i : κ, 4 * ((cs i₀ - cs i.1) / 2 - 1) := Finset.sum_le_sum fun i _ => h4 i
    _ = 4 * ∑ i : κ, ((cs i₀ - cs i.1) / 2 - 1) := by rw [Finset.mul_sum]

end TwoData

end Morse
