import Morse.Chapter14.MinimalPaths

/-!
Milnor, *Morse Theory*, §23, pp. 128–129 (Exposition/Chapter14.md, §2, proof of Theorem 23.3),
and §22, Theorem 22.1 (p. 118).

# `Ω^d(SU(2m); I, −I)` is a neighbourhood retract in `Ω`

## Milnor's text, paraphrased

(p. 118) Theorem 22.1 assumes that `Ω^d` is a topological manifold.  (p. 128) For `SU(2m)`,
`Ω^d ≅ G_m(ℂ^{2m})` by Lemma 23.1, a manifold; with Lemma 23.2 and Theorem 22.1 this gives
`π_i G_m(ℂ^{2m}) ≅ π_{i+1} SU(2m)` for `i ≤ 2m`.

## What is formalized

The project's Theorem 22.1 (`Morse.theorem_22_1`) uses, instead of "manifold", the hypothesis
that `Ω^d` be a retract of an open neighbourhood in `Ω` (which is what the proof needs; for a
manifold it is Hanner's theorem, not formalized).  Here that hypothesis is **proved for
`SU(2m)`** by an explicit retraction:

* `Morse.specProj H`: the spectral projection of a Hermitian `H` onto the eigenvalues `> 1/2`,
  `cfc 1_{(1/2, ∞)} H` (Mathlib's continuous functional calculus, for the `L²`-operator norm C⋆
  structure on matrices); `Morse.continuousOn_specProj`: it **depends continuously on `H` as long
  as `1/2` is not an eigenvalue** (`ContinuousOn.cfc_of_mem_nhdsSet`), a Hermitian projection, and
  the identity on Hermitian projections (`Morse.specProj_eq_self`).
* `Morse.hermOf X`: the Hermitian part of `½(I − iX)`; at `X = ω(1/2) = A/π = i(2P − I)` on a
  minimal geodesic it is `P` (`Morse.hermOf_of_mem_minVel`).
* `Morse.minNbhd ι m`: **the open neighbourhood `O`** of `Ω^d`, the paths `ω` such that `1/2` is
  not an eigenvalue of `hermOf ω(1/2)` and `Q(ω) = specProj (hermOf ω(1/2))` (`Morse.minProj`)
  has trace within `1/2` of `m`; then `Q(ω)` is a Hermitian projection of trace `m`
  (`Morse.minProj_mem`; the trace of a Hermitian projection is a natural number,
  `Morse.exists_trace_eq_natCast`).
* `Morse.retrPath`: `ω ↦ (t ↦ exp(t·iπ(2Q(ω) − I)))`, continuous on `O` (Lemma 23.1 and
  `Morse.continuous_expPath`), with values in `Ω^d`, agreeing on `[0, 1]` with `ω` for
  `ω ∈ Ω^d`.
* `Morse.exists_retraction_minPaths_su`: **the neighbourhood-retract hypothesis of Theorem 22.1
  for `SU(2m)`**, and `Morse.corollary_22_2_su'`: **`π_i(Ω^d, γ) ≃ π_{i+1}(SU(2m), I)` for
  `i ≤ 2m`, unconditionally** (`Morse.corollary_22_2_su` with this retraction).

## What Milnor leaves implicit

* **The neighbourhood retract.** Milnor's Theorem 22.1 needs, in its proof, that `Ω^d` be a
  retract of a neighbourhood (for a compact manifold, Hanner's theorem).  For `SU(2m)` the
  retraction can be written down: read off a matrix near the projection `P` from `ω(1/2)`, and
  project it to the nearest Hermitian projection by the functional calculus.  The trace is
  locally constant on projections, so the rank `m` is preserved near `Ω^d`.
* **Equality versus agreement on `[0, 1]`.** Theorem 22.1 here asks `ρ γ = γ` on `Ω^d`; since
  `retrPath ω` only agrees with `ω` on `[0, 1]`, the retraction is `ω ↦ ω` on `Ω^d` and
  `retrPath` elsewhere, which is still continuous on `O` because the two are at distance `0` on
  `Ω^d`.
-/

open Matrix Set Filter Topology

noncomputable section

namespace Morse

section CFC

open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The indicator of `(1/2, ∞)`. -/
def halfInd (x : ℝ) : ℝ := if 1 / 2 < x then 1 else 0

/-- The spectral projection of `H` onto the eigenvalues `> 1/2`. -/
def specProj (H : Matrix ι ι ℂ) : Matrix ι ι ℂ := cfc halfInd H

theorem continuousOn_halfInd : ContinuousOn halfInd {x | x ≠ 1 / 2} := by
  intro x hx
  refine ContinuousAt.continuousWithinAt ?_
  rcases lt_or_gt_of_ne hx with h | h
  · refine continuousAt_const (y := (0 : ℝ)) |>.congr ?_
    filter_upwards [Iio_mem_nhds h] with y hy
    have hy' : y < 1 / 2 := hy
    unfold halfInd
    split_ifs with h' <;> first | rfl | (exfalso; linarith)
  · refine continuousAt_const (y := (1 : ℝ)) |>.congr ?_
    filter_upwards [Ioi_mem_nhds h] with y hy
    have hy' : 1 / 2 < y := hy
    unfold halfInd
    split_ifs with h'
    · rfl
    · exact absurd hy' h'

theorem continuousOn_specProj {X : Type*} [TopologicalSpace X] {a : X → Matrix ι ι ℂ}
    {t : Set X} (ha : ContinuousOn a t) (hsa : ∀ x ∈ t, IsSelfAdjoint (a x))
    (hspec : ∀ x ∈ t, (1 / 2 : ℝ) ∉ spectrum ℝ (a x)) :
    ContinuousOn (fun x => specProj (a x)) t := by
  refine ContinuousOn.cfc_of_mem_nhdsSet (s := {x : ℝ | x ≠ 1 / 2}) halfInd ?_ ha hsa
    continuousOn_halfInd
  refine (isOpen_ne).mem_nhdsSet.2 ?_
  intro y hy
  simp only [mem_iUnion] at hy
  obtain ⟨x, hx, hy⟩ := hy
  rintro rfl
  exact hspec x hx hy

theorem specProj_isSelfAdjoint (H : Matrix ι ι ℂ) : IsSelfAdjoint (specProj H) :=
  cfc_predicate _ _

theorem specProj_mul_self (H : Matrix ι ι ℂ) : specProj H * specProj H = specProj H := by
  by_cases ha : IsSelfAdjoint H
  · by_cases hc : ContinuousOn halfInd (spectrum ℝ H)
    · rw [specProj, ← cfc_mul halfInd halfInd H hc hc]
      congr 1
      funext x
      unfold halfInd
      split_ifs <;> norm_num
    · rw [specProj, cfc_apply_of_not_continuousOn H hc, zero_mul]
  · rw [specProj, cfc_apply_of_not_predicate H ha, zero_mul]

/-- On a Hermitian projection, `specProj` is the identity. -/
theorem specProj_eq_self {P : Matrix ι ι ℂ} (hP : IsSelfAdjoint P) (hPP : P * P = P) :
    specProj P = P := by
  have hs : spectrum ℝ P ⊆ {0, 1} := IsIdempotentElem.spectrum_subset ℝ hPP
  rw [specProj, cfc_congr (g := id) fun x hx => ?_, cfc_id ℝ P hP]
  rcases hs hx with h | h <;> rw [h] <;> norm_num [halfInd]

theorem half_notMem_spectrum_of_idem {P : Matrix ι ι ℂ} (hPP : P * P = P) :
    (1 / 2 : ℝ) ∉ spectrum ℝ P := fun h => by
  rcases IsIdempotentElem.spectrum_subset ℝ hPP h with h | h <;> norm_num at h

theorem isOpen_half_notMem_spectrum {X : Type*} [TopologicalSpace X] {a : X → Matrix ι ι ℂ}
    (ha : Continuous a) : IsOpen {x | (1 / 2 : ℝ) ∉ spectrum ℝ (a x)} := by
  have : {x | (1 / 2 : ℝ) ∉ spectrum ℝ (a x)} =
      {x | (algebraMap ℝ (Matrix ι ι ℂ) (1 / 2) - a x).det ≠ 0} := by
    ext x
    simp only [mem_ofPred_eq, spectrum.mem_iff, not_not, Matrix.isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero]
  rw [this]
  exact isOpen_ne_fun (continuous_const.sub ha).matrix_det continuous_const

end CFC

section Trace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The trace of a Hermitian projection is a natural number. -/
theorem exists_trace_eq_natCast {Q : Matrix ι ι ℂ} (hQ : Q.IsHermitian) (hQQ : Q * Q = Q) :
    ∃ n : ℕ, Q.trace = n := by
  classical
  have h01 : ∀ j, hQ.eigenvalues j = 0 ∨ hQ.eigenvalues j = 1 := fun j =>
    IsIdempotentElem.spectrum_subset ℝ hQQ (hQ.eigenvalues_mem_spectrum_real j)
  refine ⟨(Finset.univ.filter fun j => hQ.eigenvalues j = 1).card, ?_⟩
  rw [hQ.trace_eq_sum_eigenvalues, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases h01 j with h | h <;> simp [h]

end Trace

section Retraction

open scoped Morse.MatrixInner

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {m : ℕ}

/-- The Hermitian part of `½(I − iX)`: for `X = ω(1/2) = i(2P − I)` on a minimal geodesic `ω`, this
is the projection `P`. -/
def hermOf (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (1 / 2 : ℂ) • ((1 / 2 : ℂ) • (1 - Complex.I • X) + ((1 / 2 : ℂ) • (1 - Complex.I • X))ᴴ)

omit [Fintype ι] [Nonempty ι] in
theorem hermOf_isSelfAdjoint (X : Matrix ι ι ℂ) : IsSelfAdjoint (hermOf X) := by
  rw [IsSelfAdjoint, star_eq_conjTranspose, hermOf, conjTranspose_smul, conjTranspose_add,
    conjTranspose_conjTranspose, add_comm]
  congr 1
  simp

omit [Fintype ι] [Nonempty ι] in
theorem continuous_hermOf : Continuous (hermOf (ι := ι)) := by
  unfold hermOf
  have h : Continuous fun X : Matrix ι ι ℂ => (1 / 2 : ℂ) • (1 - Complex.I • X) := by fun_prop
  exact (h.add h.matrix_conjTranspose).const_smul (1 / 2 : ℂ)

omit [Nonempty ι] in
theorem hermOf_of_mem_minVel {A : Matrix ι ι ℂ} (hA : A ∈ minVel ι) :
    hermOf ((Real.pi⁻¹ : ℝ) • A) = (1 / 2 : ℂ) • (1 - (Complex.I / Real.pi) • A) := by
  set P : Matrix ι ι ℂ := (1 / 2 : ℂ) • (1 - (Complex.I / Real.pi) • A) with hPdef
  have hPH : Pᴴ = P := by
    rw [hPdef, conjTranspose_smul, conjTranspose_sub, conjTranspose_one, conjTranspose_smul,
      hA.1.1]
    simp only [star_div₀, star_one, RCLike.star_def, Complex.conj_I, Complex.conj_ofReal,
      smul_neg, neg_div, neg_smul, neg_neg, map_ofNat]
  have hY : (1 / 2 : ℂ) • (1 - Complex.I • ((Real.pi⁻¹ : ℝ) • A)) = P := by
    rw [hPdef, ← Complex.coe_smul, smul_smul]
    congr 3
    push_cast
    ring
  rw [hermOf, hY, hPH, ← two_smul ℂ P, smul_smul]
  norm_num

/-- `Q(ω)`: the spectral projection of `hermOf ω(1/2)` onto the eigenvalues `> 1/2`. -/
def minProj (γ : PathSp (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1)) :
    Matrix ι ι ℂ :=
  specProj (hermOf ((γ : ℝ → Matrix ι ι ℂ) (1 / 2)))

variable (ι m) in
/-- **The neighbourhood `O` of `Ω^d`**: `1/2` is not an eigenvalue of `hermOf ω(1/2)`, and the
spectral projection `Q(ω)` has trace within `1/2` of `m`. -/
def minNbhd : Set (PathSp (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1)) :=
  {γ | (1 / 2 : ℝ) ∉ spectrum ℝ (hermOf ((γ : ℝ → Matrix ι ι ℂ) (1 / 2)))} ∩
    minProj ⁻¹' {Q | ‖Q.trace - (m : ℂ)‖ < 1 / 2}

omit [Nonempty ι] in
theorem continuousOn_minProj :
    ContinuousOn (minProj (ι := ι))
      {γ | (1 / 2 : ℝ) ∉ spectrum ℝ (hermOf ((γ : ℝ → Matrix ι ι ℂ) (1 / 2)))} :=
  continuousOn_specProj (continuous_hermOf.comp continuous_apply_half).continuousOn
    (fun _ _ => hermOf_isSelfAdjoint _) fun _ h => h

omit [Nonempty ι] in
theorem isOpen_minNbhd : IsOpen (minNbhd ι m) :=
  continuousOn_minProj.isOpen_inter_preimage
    (isOpen_half_notMem_spectrum (continuous_hermOf.comp continuous_apply_half))
    (isOpen_lt ((continuous_id.matrix_trace.sub continuous_const).norm) continuous_const)

omit [Nonempty ι] in
theorem minProj_mem {γ : PathSp (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1)}
    (hγ : γ ∈ minNbhd ι m) : minProj γ ∈ grassmannian ι m := by
  have hH : (minProj γ)ᴴ = minProj γ := by
    have := specProj_isSelfAdjoint (hermOf ((γ : ℝ → Matrix ι ι ℂ) (1 / 2)))
    rwa [IsSelfAdjoint, star_eq_conjTranspose] at this
  have hQQ := specProj_mul_self (hermOf ((γ : ℝ → Matrix ι ι ℂ) (1 / 2)))
  obtain ⟨n, hn⟩ := exists_trace_eq_natCast hH hQQ
  refine ⟨hH, hQQ, ?_⟩
  have h1 := hγ.2
  simp only [mem_preimage, mem_ofPred_eq] at h1
  rw [hn, show (n : ℂ) - (m : ℂ) = (((n : ℝ) - m : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_lt] at h1
  have h2 : (n : ℝ) < m + 1 := by linarith [h1.2]
  have h3 : (m : ℝ) < n + 1 := by linarith [h1.1]
  have h2' : n < m + 1 := by exact_mod_cast h2
  have h3' : m < n + 1 := by exact_mod_cast h3
  rw [hn, show n = m by omega]

open scoped Classical in
/-- **The retraction onto the minimal geodesics**: `ω ↦ (t ↦ exp(t iπ(2Q(ω) − I)))` on `O`. -/
def retrPath (hcard : Fintype.card ι = 2 * m)
    (γ : PathSp (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1)) :
    PathSp (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1) :=
  if h : γ ∈ minNbhd ι m then expPath ((lemma_23_1 hcard).symm ⟨minProj γ, minProj_mem h⟩)
  else γ

theorem continuousOn_retrPath (hcard : Fintype.card ι = 2 * m) :
    ContinuousOn (retrPath hcard) (minNbhd ι m) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have e : (minNbhd ι m).domRestrict (retrPath hcard) = fun γ : minNbhd ι m =>
      expPath ((lemma_23_1 hcard).symm ⟨minProj γ.1, minProj_mem γ.2⟩) :=
    funext fun γ => by simp only [Set.domRestrict_apply, retrPath, dif_pos γ.2]
  rw [e]
  have hQ : Continuous fun γ : minNbhd ι m => minProj γ.1 :=
    continuousOn_iff_continuous_domRestrict.1 (continuousOn_minProj.mono inter_subset_left)
  exact (continuous_expPath hcard).comp ((lemma_23_1 hcard).symm.continuous.comp
    (hQ.subtype_mk _))

theorem retrPath_mem_minPaths (hcard : Fintype.card ι = 2 * m)
    {γ : PathSp (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1)} (hγ : γ ∈ minNbhd ι m) :
    retrPath hcard γ ∈ minPaths (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1) := by
  rw [retrPath, dif_pos hγ]
  exact expPath_mem_minPaths hcard _

/-- On `Ω^d`: `ω ∈ O`, and the retraction agrees with `ω` on `[0, 1]`. -/
theorem mem_minNbhd_and_eqOn (hcard : Fintype.card ι = 2 * m)
    {γ : PathSp (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1)}
    (hγ : γ ∈ minPaths (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1)) :
    γ ∈ minNbhd ι m ∧ EqOn (retrPath hcard γ) γ (Icc 0 1) := by
  obtain ⟨A, hA, heq⟩ := exists_minVel_of_mem_minPaths hcard hγ
  have hhalf : (γ : ℝ → Matrix ι ι ℂ) (1 / 2) = (Real.pi⁻¹ : ℝ) • A := by
    rw [← pi_smul_apply_half hA heq, smul_smul, inv_mul_cancel₀ Real.pi_ne_zero, one_smul]
  have hP := projOf_mem hcard hA
  have hH : hermOf ((γ : ℝ → Matrix ι ι ℂ) (1 / 2)) =
      (1 / 2 : ℂ) • (1 - (Complex.I / Real.pi) • A) := by
    rw [hhalf, hermOf_of_mem_minVel hA]
  have hsa : IsSelfAdjoint ((1 / 2 : ℂ) • (1 - (Complex.I / Real.pi) • A)) := by
    rw [IsSelfAdjoint, star_eq_conjTranspose]; exact hP.1
  have hQ : minProj γ = (1 / 2 : ℂ) • (1 - (Complex.I / Real.pi) • A) := by
    rw [minProj, hH, specProj_eq_self hsa hP.2.1]
  have hmem : γ ∈ minNbhd ι m := by
    refine ⟨?_, ?_⟩
    · change (1 / 2 : ℝ) ∉ spectrum ℝ (hermOf ((γ : ℝ → Matrix ι ι ℂ) (1 / 2)))
      rw [hH]
      exact half_notMem_spectrum_of_idem hP.2.1
    · simp only [mem_preimage, mem_ofPred_eq]
      rw [hQ, hP.2.2, sub_self, norm_zero]
      norm_num
  refine ⟨hmem, fun t ht => ?_⟩
  rw [retrPath, dif_pos hmem]
  have : (lemma_23_1 hcard).symm ⟨minProj γ, minProj_mem hmem⟩ = ⟨A, hA⟩ := by
    rw [Homeomorph.symm_apply_eq]
    exact Subtype.ext hQ
  rw [this, expPath_apply]
  exact (heq ht).symm

/-- **The neighbourhood retract of Theorem 22.1 for `SU(2m)`**: `Ω^d` is a retract of the open
neighbourhood `O = Morse.minNbhd ι m` in `Ω(SU(2m); I, −I)`. -/
theorem exists_retraction_minPaths_su (hcard : Fintype.card ι = 2 * m) :
    ∃ O : Set (PathSp (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1)),
      IsOpen O ∧ minPaths _ 1 (-1) ⊆ O ∧
      ∃ ρ : PathSp (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1) →
          PathSp (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1),
        ContinuousOn ρ O ∧ (∀ γ ∈ O, ρ γ ∈ minPaths _ 1 (-1)) ∧
        ∀ γ ∈ minPaths _ 1 (-1), ρ γ = γ := by
  classical
  set S := minPaths (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1)
  refine ⟨minNbhd ι m, isOpen_minNbhd, fun γ hγ => (mem_minNbhd_and_eqOn hcard hγ).1,
    fun γ => if γ ∈ S then γ else retrPath hcard γ, ?_, fun γ hγ => ?_, fun γ hγ => if_pos hγ⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    refine PathSp.continuous_of_edist_eq_zero
      (continuousOn_iff_continuous_domRestrict.1 (continuousOn_retrPath hcard)) fun γ => ?_
    simp only [domRestrict_apply]
    split_ifs with h
    · rw [edist_comm]
      exact PathSp.edist_eq_zero_of_eqOn (mem_minNbhd_and_eqOn hcard h).2
    · exact edist_self _
  · simp only
    split_ifs with h
    · exact h
    · exact retrPath_mem_minPaths hcard hγ

/-- **Corollary 22.2 for `SU(2m)`, unconditionally** (Milnor pp. 128–129): for `i ≤ 2m` and every
minimal geodesic `γ` from `I` to `−I`, `π_i(Ω^d, γ) ≃ π_{i+1}(SU(2m), I)`. -/
theorem corollary_22_2_su' (hcard : Fintype.card ι = 2 * m) {i : ℕ} (hi : i ≤ 2 * m)
    (γ : minPaths (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1)) :
    Nonempty (HomotopyGroup.Pi i (minPaths (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1))
        γ ≃ HomotopyGroup.Pi (i + 1) (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ))
          ⟨1, (specialUnitaryGroup ι ℂ).one_mem⟩) :=
  corollary_22_2_su hcard (exists_retraction_minPaths_su hcard) hi γ

end Retraction

end Morse
