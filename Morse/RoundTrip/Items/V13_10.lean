import Morse
import RoundTrip.Check
import RoundTrip.Blind.V13_10

open scoped ContDiff Topology
open Set Filter

namespace RoundTrip.V13_10

/-- The project's statement: Lemma 22.4 in any finite-dimensional real normed space `E` (`f` only
`C²` on `U`, `g` arbitrary, closeness of `dg`, `d²g` to `df`, `d²f` in operator norm), its
variant for `g = f + h`, and the two linear-algebra lemmas behind it (a negative definite form has
a margin; forms near it keep index `≥ dim W`). Universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Morse.exists_negDef_margin.{0} ∧
  type_of% @Morse.le_index_of_norm_sub_lt.{0} ∧
  type_of% @Morse.lemma_22_4.{0} ∧
  type_of% @Morse.lemma_22_4_add.{0}

theorem A_holds : A :=
  ⟨@Morse.exists_negDef_margin, @Morse.le_index_of_norm_sub_lt, @Morse.lemma_22_4,
    @Morse.lemma_22_4_add⟩

/-! ### Dictionary -/

section Dict

variable {m : ℕ}

/-- The blind index of a continuous bilinear form on the whole space is the project's `index`. -/
theorem bIndex_univ_eq_index (H : Rn m →L[ℝ] Rn m →L[ℝ] ℝ) :
    bIndex (Set.univ : Set (Rn m)) (fun v w => H v w) = (Morse.index H : ℕ∞) := by
  refine le_antisymm (iSup₂_le fun S hS => ?_) ?_
  · exact_mod_cast Morse.finrank_le_index_of_negDef H hS.2.2
  · obtain ⟨W, hW, hneg⟩ := Morse.exists_negDef_finrank_eq_index H
    rw [← hW]
    exact le_iSup₂_of_le (f := fun (S : Submodule ℝ (Rn m))
      (_ : (S : Set (Rn m)) ⊆ Set.univ ∧ FiniteDimensional ℝ S ∧ IsNegDefSub (fun v w => H v w) S) =>
      (Module.finrank ℝ S : ℕ∞)) W ⟨subset_univ _, inferInstance, hneg⟩ le_rfl

theorem idx_eq_index (g : Rn m → ℝ) (x : Rn m) :
    idx g x = (Morse.index (Morse.hessian g x) : ℕ∞) :=
  bIndex_univ_eq_index _

/-- The operator norm on `ℝᵐ` is at most the sum of the norms on the coordinate vectors. -/
theorem opNorm_le_sum {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : Rn m →L[ℝ] F) :
    ‖L‖ ≤ ∑ i, ‖L (EuclideanSpace.single i (1 : ℝ))‖ := by
  refine L.opNorm_le_bound (Finset.sum_nonneg fun i _ => norm_nonneg _) fun v => ?_
  have hv : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr v]
    simp [EuclideanSpace.basisFun_apply]
  calc ‖L v‖ = ‖∑ i, v i • L (EuclideanSpace.single i (1 : ℝ))‖ := by
        conv_lhs => rw [hv]
        simp [map_sum]
    _ ≤ ∑ i, ‖v i • L (EuclideanSpace.single i (1 : ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖v‖ * ‖L (EuclideanSpace.single i (1 : ℝ))‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le v i) (norm_nonneg _)
    _ = (∑ i, ‖L (EuclideanSpace.single i (1 : ℝ))‖) * ‖v‖ := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- Entrywise `ε`-closeness bounds the operator norm by `m · ε`. -/
theorem opNorm_lt_of_entries {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Rn m →L[ℝ] F) {ε : ℝ} (h : ∀ i, ‖L (EuclideanSpace.single i (1 : ℝ))‖ < ε) :
    ‖L‖ ≤ m * ε := by
  refine (opNorm_le_sum L).trans ?_
  calc ∑ i, ‖L (EuclideanSpace.single i (1 : ℝ))‖ ≤ ∑ _i : Fin m, ε :=
        Finset.sum_le_sum fun i _ => (h i).le
    _ = m * ε := by simp

/-- `pd2` is the Hessian on coordinate vectors, wherever `g` is `C²`. -/
theorem pd2_eq {g : Rn m → ℝ} {x : Rn m} (hg : ContDiffAt ℝ 2 g x) (i j : Fin m) :
    pd2 g i j x = Morse.hessian g x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  have h1 : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  unfold pd2 pd
  rw [fderiv_clm_apply h1 (differentiableAt_const _)]
  simp [Morse.hessian]

end Dict

/-- `A ⇒ B`: `Morse.lemma_22_4` at `E = ℝⁿ`, with `ε_B = ε_A / (n² + n + 1)`. -/
theorem A_to_B : A → B := by
  rintro ⟨-, -, h22_4, -⟩ n U K f l0 hU hK hKU hf hidx
  have hf2 : ContDiffOn ℝ 2 f U := hf.of_le (by norm_cast)
  obtain ⟨ε, hε, H⟩ := h22_4 hU hK hKU hf2 (l₀ := l0) fun x hx hcrit => by
    have := hidx x hx hcrit.fderiv_eq
    rw [idx_eq_index] at this
    exact_mod_cast this
  have hN : (0 : ℝ) < n * n + n + 1 := by positivity
  refine ⟨ε / (n * n + n + 1), div_pos hε hN, fun g hg h1 h2 x hx hcrit => ?_⟩
  have hn1 : (n : ℝ) * (ε / (n * n + n + 1)) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ hN]; nlinarith
  have hn2 : (n : ℝ) * ((n + 1) * (ε / (n * n + n + 1))) < ε := by
    rw [mul_div_assoc', mul_div_assoc', div_lt_iff₀ hN]; nlinarith
  have hreg : ∀ y ∈ K, ContDiffAt ℝ 2 g y ∧ ContDiffAt ℝ 2 f y := fun y hy =>
    ⟨(hg.contDiffAt (hU.mem_nhds (hKU hy))).of_le (by norm_cast),
      (hf.contDiffAt (hU.mem_nhds (hKU hy))).of_le (by norm_cast)⟩
  have hA1 : ∀ y ∈ K, ‖fderiv ℝ g y - fderiv ℝ f y‖ < ε := fun y hy => by
    refine lt_of_le_of_lt (opNorm_lt_of_entries _ fun i => ?_) hn1
    have := h1 y hy i
    simpa [pd, Real.norm_eq_abs] using this
  have hA2 : ∀ y ∈ K, ‖Morse.hessian g y - Morse.hessian f y‖ < ε := fun y hy => by
    refine lt_of_le_of_lt (opNorm_lt_of_entries _ fun i => ?_) hn2
    refine lt_of_le_of_lt (opNorm_lt_of_entries _ fun j => ?_)
      (by nlinarith [div_pos hε hN] : (n : ℝ) * (ε / (n * n + n + 1)) < (n + 1) * (ε / (n * n + n + 1)))
    have := h2 y hy i j
    rw [pd2_eq (hreg y hy).1, pd2_eq (hreg y hy).2] at this
    simpa [Real.norm_eq_abs] using this
  have hcrit' : Morse.IsCriticalPoint g x :=
    (Morse.isCriticalPoint_iff ((hreg x hx).1.differentiableAt (by norm_num))).2 hcrit
  have := H g hA1 hA2 x hx hcrit'
  rw [idx_eq_index]
  exact_mod_cast this

/-! `B ⇒ A` is not proved: `A` is more general than `B`.
* `lemma_22_4` / `lemma_22_4_add` hold in any finite-dimensional normed space, for `f` only `C²`
  on `U` and for an arbitrary `g` (no regularity), while `B`'s hypotheses require `f` and `g`
  to be `C^∞` on `U` (so `B` cannot be applied to a `C²` `f`). Operator-norm closeness and
  partial-derivative closeness are equivalent up to constants (both directions used here).
* `exists_negDef_margin` and `le_index_of_norm_sub_lt` are linear-algebra lemmas, true outright
  but not consequences of `B`.
On the common domain (`E = ℝⁿ`, `f`, `g` smooth on `U`) the two agree: `B ⇒ A_smooth` below. -/

/-- `A`'s Lemma 22.4 on the common domain of `A` and `B`: `E = ℝⁿ`, `f` and `g` smooth on `U`. -/
def A_smooth : Prop :=
  ∀ (n : ℕ) (U K : Set (Rn n)) (f : Rn n → ℝ) (l0 : ℕ), IsOpen U → IsCompact K → K ⊆ U →
    ContDiffOn ℝ ∞ f U → (∀ x ∈ K, Morse.IsCriticalPoint f x → l0 ≤ Morse.index (Morse.hessian f x)) →
    ∃ ε > 0, ∀ g : Rn n → ℝ, ContDiffOn ℝ ∞ g U →
      (∀ x ∈ K, ‖fderiv ℝ g x - fderiv ℝ f x‖ < ε) →
      (∀ x ∈ K, ‖Morse.hessian g x - Morse.hessian f x‖ < ε) →
      ∀ x ∈ K, Morse.IsCriticalPoint g x → l0 ≤ Morse.index (Morse.hessian g x)

theorem A_to_A_smooth : A → A_smooth := fun hA n U K f l0 hU hK hKU hf hidx => by
  obtain ⟨ε, hε, H⟩ := hA.2.2.1 hU hK hKU (hf.of_le (by norm_cast)) hidx
  exact ⟨ε, hε, fun g _ => H g⟩

/-- **On the common domain `B` gives `A`**: operator-norm closeness bounds every partial derivative
(`‖eᵢ‖ = 1`), and the dictionary above translates critical points and indices. -/
theorem B_to_A_smooth : B → A_smooth := by
  intro hB n U K f l0 hU hK hKU hf hidx
  have hreg : ∀ (h : Rn n → ℝ), ContDiffOn ℝ ∞ h U → ∀ y ∈ K, ContDiffAt ℝ 2 h y := fun h hh y hy =>
    (hh.contDiffAt (hU.mem_nhds (hKU hy))).of_le (by norm_cast)
  obtain ⟨ε, hε, H⟩ := hB n U K f l0 hU hK hKU hf fun x hx hcrit => by
    rw [idx_eq_index]
    exact_mod_cast hidx x hx
      ((Morse.isCriticalPoint_iff ((hreg f hf x hx).differentiableAt (by norm_num))).2 hcrit)
  refine ⟨ε, hε, fun g hg h1 h2 x hx hcrit => ?_⟩
  have he : ∀ i : Fin n, ‖(EuclideanSpace.single i (1 : ℝ) : Rn n)‖ = 1 := fun i => by simp
  have hB1 : ∀ y ∈ K, ∀ i, |pd g i y - pd f i y| < ε := fun y hy i => by
    have := (fderiv ℝ g y - fderiv ℝ f y).le_opNorm (EuclideanSpace.single i (1 : ℝ))
    rw [he, mul_one] at this
    simpa [pd, Real.norm_eq_abs] using this.trans_lt (h1 y hy)
  have hB2 : ∀ y ∈ K, ∀ i j, |pd2 g i j y - pd2 f i j y| < ε := fun y hy i j => by
    rw [pd2_eq (hreg g hg y hy), pd2_eq (hreg f hf y hy)]
    have h3 := ((Morse.hessian g y - Morse.hessian f y) (EuclideanSpace.single i (1 : ℝ))).le_opNorm
      (EuclideanSpace.single j (1 : ℝ))
    have h4 := (Morse.hessian g y - Morse.hessian f y).le_opNorm (EuclideanSpace.single i (1 : ℝ))
    rw [he, mul_one] at h3 h4
    have := (h3.trans h4).trans_lt (h2 y hy)
    simpa [Real.norm_eq_abs] using this
  have := H g hg hB1 hB2 x hx hcrit.fderiv_eq
  rw [idx_eq_index] at this
  exact_mod_cast this

#rt_check RoundTrip.V13_10.B_to_A_smooth [Morse.exists_negDef_margin, Morse.le_index_of_norm_sub_lt,
  Morse.lemma_22_4, Morse.lemma_22_4_add]

#rt_check RoundTrip.V13_10.A_to_B [Morse.exists_negDef_margin, Morse.le_index_of_norm_sub_lt,
  Morse.lemma_22_4, Morse.lemma_22_4_add]

end RoundTrip.V13_10
