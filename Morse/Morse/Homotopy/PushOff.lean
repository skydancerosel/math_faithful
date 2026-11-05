import Mathlib
import Milnor.Chapter8.Approx

/-!
# The push-off lemma in coordinates

The key step of cellular approximation (Hatcher, *Algebraic Topology*, Lemma 4.10): a map from a
space of dimension `i` into a space with a cell of dimension `λ > i` can be deformed, relative to
the part mapped far from the centre of the cell, so as to miss a whole ball about the centre. This
file does it in the coordinates of the cell; `Morse/Homotopy/CellAttach.lean` transports it to an
attached cell and finishes with the radial deformation of the punctured cell onto its boundary.

## Statement

Let `P` be compact, with a continuous injection `ι : P → V` into a finite-dimensional real normed
space (a "finite-dimensional" domain, for instance the cube `I^N ⊆ ℝ^N`), and let `E` be the
coordinate space of the cell, with `dim V < dim E`. Let `h : P → E` be continuous on an open
`W ⊆ P` (the preimage of the open cell), with values in the open unit ball on `W`, and such that
`{p ∈ W | ‖h p‖ ≤ 3/4}` is closed in `P`. Then (`Morse.Homotopy.exists_pushOff`) there are a
homotopy `H : I × P → E`, continuous on `I × W`, from `h`, stationary where `‖h p‖ ≥ 3/4`, staying
in the open unit ball over `W`, and an `ε > 0` with `‖H(1, p)‖ ≥ ε` on `W`.

## Proof

* **Smooth approximation** (`Morse.Homotopy.exists_contDiff_near`): on the compact
  `C = {p ∈ W | ‖h p‖ ≤ 3/4}`, `h` is within `1/8` of `Q ∘ ι` for a smooth `Q : V → E`. This is
  the Stone–Weierstrass theorem for smooth maps of the companion project
  (`Milnor.Problems.exists_contDiff_approx_of_isCompact`), applied to `h ∘ ι⁻¹` on the compact
  `ι(C)`, on which `ι⁻¹` is continuous (`ι` is a closed embedding).
* **A missed point**: since `dim V < dim E`, the complement of the range of the `C¹` map `Q` is
  dense (Mathlib's `ContDiff.dense_compl_range_of_finrank_lt_finrank`, via Hausdorff dimension:
  every point is critical, Sard's theorem in its easiest case), so some `p₀` with `‖p₀‖ < 1/8` is
  not a value of `Q`; as `Q(ι(P))` is compact, a ball `B(p₀, ε₀)` misses it.
* **The homotopy** `H(t, p) = h p + t β(‖h p‖) (Q(ι p) - p₀ - h p)`, with the cut-off
  `β = 1` on `[0, 1/2]` and `β = 0` on `[3/4, ∞)` (`Morse.Homotopy.pushCutoff`). Where
  `‖h p‖ ≤ 1/2`, `H(1, p) = Q(ι p) - p₀` has norm `≥ ε₀`; where `1/2 < ‖h p‖ < 3/4`,
  `‖H(1, p)‖ > 1/2 - 1/8 - 1/8`; elsewhere `H(1, p) = h p`. The translation by `-p₀` moves the
  missed point to the centre.
-/

open Set Metric Function Module Topology
open scoped unitInterval ContDiff

noncomputable section

namespace Morse.Homotopy

/-! ### The cut-off -/

/-- The cut-off `β(r)`: `1` for `r ≤ 1/2`, `0` for `r ≥ 3/4`, linear in between. -/
def pushCutoff (r : ℝ) : ℝ :=
  max 0 (min 1 (3 - 4 * r))

theorem continuous_pushCutoff : Continuous pushCutoff :=
  continuous_const.max (continuous_const.min (continuous_const.sub
    (continuous_const.mul continuous_id)))

theorem pushCutoff_nonneg (r : ℝ) : 0 ≤ pushCutoff r :=
  le_max_left _ _

theorem pushCutoff_le_one (r : ℝ) : pushCutoff r ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem pushCutoff_of_le {r : ℝ} (h : r ≤ 1 / 2) : pushCutoff r = 1 := by
  unfold pushCutoff
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem pushCutoff_of_ge {r : ℝ} (h : 3 / 4 ≤ r) : pushCutoff r = 0 := by
  unfold pushCutoff
  exact max_eq_left (min_le_of_right_le (by linarith))

/-! ### Smooth approximation through an injection -/

variable {P : Type*} [TopologicalSpace P] [CompactSpace P]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Smooth approximation through an injection**: a map `h : P → E` continuous on a closed
`C ⊆ P` is, on `C`, uniformly within `δ` of `Q ∘ ι` for a smooth `Q : V → E`. -/
theorem exists_contDiff_near {ι : P → V} (hι : Continuous ι) (hinj : Injective ι) {C : Set P}
    (hC : IsClosed C) {h : P → E} (hh : ContinuousOn h C) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Q : V → E, ContDiff ℝ ∞ Q ∧ ∀ p ∈ C, ‖Q (ι p) - h p‖ < δ := by
  rcases isEmpty_or_nonempty P with hP | hP
  · exact ⟨0, contDiff_const, fun p => isEmptyElim p⟩
  have hemb : IsClosedEmbedding ι := hι.isClosedEmbedding hinj
  have hS : IsCompact (ι '' C) := hC.isCompact.image hι
  have hinv : ContinuousOn (invFun ι) (ι '' C) := by
    rw [hemb.isInducing.continuousOn_iff]
    refine continuousOn_id.congr fun v hv => ?_
    obtain ⟨p, -, rfl⟩ := hv
    simp [leftInverse_invFun hinj p]
  have hmaps : MapsTo (invFun ι) (ι '' C) C := by
    rintro _ ⟨p, hp, rfl⟩
    rwa [leftInverse_invFun hinj p]
  obtain ⟨Q, hQ, hQG⟩ :=
    Milnor.Problems.exists_contDiff_approx_of_isCompact hS (hh.comp hinv hmaps) hδ
  refine ⟨Q, hQ, fun p hp => ?_⟩
  have := hQG (ι p) ⟨p, hp, rfl⟩
  rwa [Function.comp_apply, leftInverse_invFun hinj p] at this

/-! ### The push-off -/

/-- **The push-off lemma in coordinates.** Let `P` be compact with a continuous injection into
`V`, `dim V < dim E`, and `h : P → E` continuous on an open `W ⊆ P`, with `‖h‖ < 1` on `W` and
`{p ∈ W | ‖h p‖ ≤ 3/4}` closed. Then there are a homotopy `H` from `h`, continuous on `I × W`,
stationary where `‖h‖ ≥ 3/4` and inside the open unit ball over `W`, and `ε > 0` such that
`H(1, ·)` misses the ball of radius `ε` about `0` on `W`. -/
theorem exists_pushOff (hV : finrank ℝ V < finrank ℝ E) {ι : P → V} (hι : Continuous ι)
    (hinj : Injective ι) {W : Set P} {h : P → E} (hh : ContinuousOn h W)
    (hlt : ∀ p ∈ W, ‖h p‖ < 1) (hC : IsClosed {p | p ∈ W ∧ ‖h p‖ ≤ 3 / 4}) :
    ∃ H : I × P → E, ContinuousOn H (univ ×ˢ W) ∧ (∀ p, H (0, p) = h p) ∧
      (∀ t p, 3 / 4 ≤ ‖h p‖ → H (t, p) = h p) ∧ (∀ t, ∀ p ∈ W, ‖H (t, p)‖ < 1) ∧
      ∃ ε > 0, ∀ p ∈ W, ε ≤ ‖H (1, p)‖ := by
  obtain ⟨Q, hQ, hQh⟩ := exists_contDiff_near hι hinj hC (hh.mono fun p hp => hp.1)
    (by norm_num : (0 : ℝ) < 1 / 8)
  -- a point `p₀` near the centre which is not a value of `Q`
  have hdense : Dense (range Q)ᶜ :=
    (hQ.of_le (by exact_mod_cast le_top)).dense_compl_range_of_finrank_lt_finrank hV
  obtain ⟨p₀, hp₀Q, hp₀⟩ := hdense.exists_mem_open isOpen_ball
    ⟨0, mem_ball_self (by norm_num : (0 : ℝ) < 1 / 8)⟩
  rw [mem_ball_zero_iff] at hp₀
  -- a ball about `p₀` missing `Q(ι(P))`
  have hK : IsClosed (range (Q ∘ ι)) := (isCompact_range (hQ.continuous.comp hι)).isClosed
  have hp₀K : p₀ ∈ (range (Q ∘ ι))ᶜ := fun ⟨p, hp⟩ => hp₀Q ⟨ι p, hp⟩
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.1 hK.isOpen_compl p₀ hp₀K
  have hfar : ∀ p, ε₀ ≤ ‖Q (ι p) - p₀‖ := by
    intro p
    by_contra hlt'
    exact hball (mem_ball.2 (by rwa [dist_eq_norm, not_le] at *)) ⟨p, rfl⟩
  -- the homotopy
  refine ⟨fun q => h q.2 + ((q.1 : ℝ) * pushCutoff ‖h q.2‖) • (Q (ι q.2) - p₀ - h q.2),
    ?_, ?_, ?_, ?_, min ε₀ (1 / 4), lt_min hε₀ (by norm_num), ?_⟩
  · have hh' : ContinuousOn (fun q : I × P => h q.2) (univ ×ˢ W) :=
      hh.comp continuousOn_snd fun q hq => hq.2
    refine hh'.add (ContinuousOn.smul ((continuous_subtype_val.comp continuous_fst).continuousOn.mul
      (continuous_pushCutoff.comp_continuousOn hh'.norm))
      ((((hQ.continuous.comp hι).comp continuous_snd).continuousOn.sub continuousOn_const).sub hh'))
  · intro p
    simp
  · intro t p hp
    simp [pushCutoff_of_ge hp]
  · intro t p hp
    by_cases h34 : 3 / 4 ≤ ‖h p‖
    · simpa [pushCutoff_of_ge h34] using hlt p hp
    · have hpC : p ∈ {p | p ∈ W ∧ ‖h p‖ ≤ 3 / 4} := ⟨hp, (not_le.1 h34).le⟩
      have hc0 : 0 ≤ (t : ℝ) * pushCutoff ‖h p‖ := mul_nonneg t.2.1 (pushCutoff_nonneg _)
      have hc1 : (t : ℝ) * pushCutoff ‖h p‖ ≤ 1 :=
        mul_le_one₀ t.2.2 (pushCutoff_nonneg _) (pushCutoff_le_one _)
      have hd : ‖Q (ι p) - p₀ - h p‖ < 1 / 4 := by
        calc ‖Q (ι p) - p₀ - h p‖ = ‖(Q (ι p) - h p) - p₀‖ := by congr 1; abel
          _ ≤ ‖Q (ι p) - h p‖ + ‖p₀‖ := norm_sub_le _ _
          _ < 1 / 8 + 1 / 8 := add_lt_add (hQh p hpC) hp₀
          _ = 1 / 4 := by norm_num
      calc ‖h p + ((t : ℝ) * pushCutoff ‖h p‖) • (Q (ι p) - p₀ - h p)‖
          ≤ ‖h p‖ + ‖((t : ℝ) * pushCutoff ‖h p‖) • (Q (ι p) - p₀ - h p)‖ := norm_add_le _ _
        _ ≤ ‖h p‖ + ‖Q (ι p) - p₀ - h p‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
          gcongr
          exact mul_le_of_le_one_left (norm_nonneg _) hc1
        _ < 3 / 4 + 1 / 4 := add_lt_add (not_le.1 h34) hd
        _ = 1 := by norm_num
  · intro p hp
    simp only [Set.Icc.coe_one, one_mul]
    by_cases h12 : ‖h p‖ ≤ 1 / 2
    · rw [pushCutoff_of_le h12, one_smul, show h p + (Q (ι p) - p₀ - h p) = Q (ι p) - p₀ by abel]
      exact (min_le_left _ _).trans (hfar p)
    · by_cases h34 : 3 / 4 ≤ ‖h p‖
      · rw [pushCutoff_of_ge h34, zero_smul, add_zero]
        exact (min_le_right _ _).trans (by linarith)
      · have hpC : p ∈ {p | p ∈ W ∧ ‖h p‖ ≤ 3 / 4} := ⟨hp, (not_le.1 h34).le⟩
        have hd : ‖Q (ι p) - p₀ - h p‖ < 1 / 4 := by
          calc ‖Q (ι p) - p₀ - h p‖ = ‖(Q (ι p) - h p) - p₀‖ := by congr 1; abel
            _ ≤ ‖Q (ι p) - h p‖ + ‖p₀‖ := norm_sub_le _ _
            _ < 1 / 8 + 1 / 8 := add_lt_add (hQh p hpC) hp₀
            _ = 1 / 4 := by norm_num
        have hsm : ‖pushCutoff ‖h p‖ • (Q (ι p) - p₀ - h p)‖ < 1 / 4 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pushCutoff_nonneg _)]
          exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (pushCutoff_le_one _)) hd
        have := norm_sub_norm_le (h p) (-(pushCutoff ‖h p‖ • (Q (ι p) - p₀ - h p)))
        rw [sub_neg_eq_add, norm_neg] at this
        refine (min_le_right _ _).trans ?_
        linarith [not_le.1 h12]

end Morse.Homotopy
