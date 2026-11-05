import Morse.Chapter15.SplittingData

/-!
Milnor, *Morse Theory*, §24, pp. 147–148 (case `k ≡ 2 (mod 4)`); Exposition/Chapter15.md, §6,
"The geodesics" and the index bound `λ ≥ (ν − |c|)/4`.

# The pieces of a geodesic for `k ≡ 2 (mod 4)`, and Lemma 24.8 between them

## Milnor's text, paraphrased

(p. 147) Make `ℝⁿ` complex by `i = J_1⋯J_{k−1}`.  For `A ∈ 𝒯` with `exp(πA) = −I`, split
`ℝⁿ = M_1 ⊕ ⋯ ⊕ M_ν` into minimal `(J_1, …, J_{k−1}, J, A)`-spaces; then `A = a_h i` on `M_h`,
`a_h` an odd integer, `dim M_h = m_k`, and `c = Σ a_h`.  (p. 148) For `h ≠ j`, Lemma 24.8 (for
`k` structures) gives `C : M_h → M_j` commuting with `J_1, …, J_{k−1}` and anticommuting with `J`;
`B = C − Cᵀ` is an eigenvector of `K_A` with eigenvalue `(a_h − a_j)²/4`.

## What is formalized

On a finite-dimensional inner product space with operators `a = A`, `q = J`, `j α = J_α`
(`Morse.IsOmegaOps`), `k ≠ 0`, and Milnor's `i` as the product `Morse.iWord k j = J_1⋯J_{k−1}`
with its relations (`Morse.IsIOps`):

* `Morse.IsOmegaOps.exists_eq_smul_iWord`: **`A = c·i` on a minimal piece** (`A·i` is
  self-adjoint and commutes with everything, hence scalar).
* `Morse.isMinimal_cliffFam_k`: a minimal piece is a minimal `(J_1, …, J_{k−1}, ±J)`-space;
  `Morse.exists_inter_two`: **Lemma 24.8 for `k` structures between two pieces**, `T : M₀ ≅ M₁`
  with `TJ_α = J_αT`, `TJ = −JT` (`k ≤ 8`, `k ≢ 3 (mod 4)`).
* `Morse.exists_decomp_two`: **the splitting**: pieces `M_h`, odd integers `a_h` with
  `A = a_h i` on `M_h`, `ν · m_{k+1} = n`, and `tr(A·i) = −m_{k+1} Σ a_h`.
* `Morse.exists_twoPieceData_of_decomp`: from a piece with `a_{h₀} ≥ 3`, intertwiners
  `D_j = ι_{M_j} T_j π_{M₀}` to the pieces with `a_j < 0` (`Morse.TwoPieceData`), with
  `ν − Σ a_h ≤ 4 Σ_j ((a_{h₀} − a_j)/2 − 1)`.

## What Milnor leaves implicit

* "`A = a_h i` on `M_h`": the eigenspaces of `A` over `ℂ` are not needed; `Ai` is a symmetric
  operator commuting with `J_α`, `J`, `A`, hence a scalar on a minimal space.
* Lemma 24.8 is applied to the `k` structures `(J_1, …, J_{k−1}, ±J)`; that the pieces are
  minimal for them uses that `A` is a multiple of `i`, a product of the `J_α`.
* For the bound only the pairs `(h₀, j)` with `a_j < 0` are used (or, after `A ↦ −A`, those with
  `a_j > 0`), as in Milnor's "suppose for example that some `a_h` is equal to `−3`".
-/

open Set Module

noncomputable section

namespace Morse

section Two

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {k : ℕ} {a q : E →L[ℝ] E} {j : ℕ → E →L[ℝ] E}

variable (k j) in
/-- **Milnor's `i = J_1⋯J_{k−1}`** as an operator. -/
def iWord : E →L[ℝ] E := ((List.range (k - 1)).map fun i => j (i + 1)).prod

theorem mem_iWord_list {g : E →L[ℝ] E} (hg : g ∈ (List.range (k - 1)).map fun i => j (i + 1)) :
    ∃ α, 1 ≤ α ∧ α < k ∧ g = j α := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
  exact ⟨i + 1, by omega, by have := List.mem_range.1 hi; omega, rfl⟩

/-- A subspace invariant under the `J_α` is invariant under `i`. -/
theorem iWord_mem {W : Submodule ℝ E} (hW : ∀ α, 1 ≤ α → α < k → ∀ w ∈ W, j α w ∈ W) :
    ∀ w ∈ W, iWord k j w ∈ W := by
  suffices h : ∀ l : List (E →L[ℝ] E), (∀ g ∈ l, ∀ w ∈ W, g w ∈ W) → ∀ w ∈ W, l.prod w ∈ W from
    h _ fun g hg => by
      obtain ⟨α, h1, h2, rfl⟩ := mem_iWord_list hg
      exact hW α h1 h2
  intro l
  induction l with
  | nil => intro _ w hw; simpa using hw
  | cons g l ih =>
    intro hl w hw
    rw [List.prod_cons, mul_apply_eq_comp]
    exact hl g List.mem_cons_self _ (ih (fun g' hg' => hl g' (List.mem_cons_of_mem _ hg')) w hw)

/-- An operator commuting with the `J_α` commutes with `i`. -/
theorem commute_iWord {D : E →L[ℝ] E} (hD : ∀ α, 1 ≤ α → α < k → D * j α = j α * D) :
    D * iWord k j = iWord k j * D :=
  (Commute.list_prod_right _ D fun g hg => by
    obtain ⟨α, h1, h2, rfl⟩ := mem_iWord_list hg
    exact hD α h1 h2).eq

variable [FiniteDimensional ℝ E]

variable (k a q j) in
/-- The relations of Milnor's `i` (Lemma 2.1 of the exposition, `k ≡ 2 (mod 4)`). -/
structure IsIOps : Prop where
  sq : iWord k j * iWord k j = -1
  skew : ContinuousLinearMap.adjoint (iWord k j) = -iWord k j
  ia : iWord k j * a = a * iWord k j
  iq : iWord k j * q = -(q * iWord k j)
  ij : ∀ α, 1 ≤ α → α < k → iWord k j * j α = j α * iWord k j

theorem IsIOps.neg_a (hI : IsIOps k a q j) : IsIOps k (-a) q j :=
  ⟨hI.sq, hI.skew, by rw [mul_neg, neg_mul, hI.ia], hI.iq, hI.ij⟩

theorem IsOmegaOps.neg_a (h : IsOmegaOps k a q j) : IsOmegaOps k (-a) q j where
  a_skew := by rw [map_neg, h.a_skew]
  q_zero := h.q_zero
  q_sq := h.q_sq
  q_skew := h.q_skew
  aq hk := by rw [neg_mul, mul_neg, h.aq hk]
  j_sq := h.j_sq
  j_skew := h.j_skew
  j_anti := h.j_anti
  jq := h.jq
  ja α h1 h2 := by rw [mul_neg, neg_mul, h.ja α h1 h2]

theorem IsOmegaOps.neg_q (h : IsOmegaOps k a q j) (hk : k ≠ 0) :
    IsOmegaOps k a ((-1 : ℝ) • q) j where
  a_skew := h.a_skew
  q_zero hk' := absurd hk' hk
  q_sq hk' := by rw [neg_one_smul, neg_mul_neg]; exact h.q_sq hk'
  q_skew hk' := by rw [neg_one_smul, map_neg, h.q_skew hk']
  aq hk' := by rw [neg_one_smul, mul_neg, neg_mul, h.aq hk']
  j_sq := h.j_sq
  j_skew := h.j_skew
  j_anti := h.j_anti
  jq α h1 h2 := by rw [neg_one_smul, mul_neg, neg_mul, h.jq α h1 h2]
  ja := h.ja

omit [FiniteDimensional ℝ E] in
theorem isInvar_omegaGens_neg_a {W : Submodule ℝ E} (hW : IsInvar (omegaGens k a q j) W) :
    IsInvar (omegaGens k (-a) q j) W := by
  rintro g ((hg | hg) | ⟨α, h1, h2, rfl⟩) w hw
  · rw [Set.mem_singleton_iff.1 (show g ∈ ({-a} : Set (E →L[ℝ] E)) from hg),
      neg_apply]
    exact W.neg_mem (hW a IsOmegaOps.a_mem w hw)
  · rw [Set.mem_singleton_iff.1 hg]; exact hW q IsOmegaOps.q_mem w hw
  · exact hW _ (IsOmegaOps.j_mem h1 h2) w hw

omit [FiniteDimensional ℝ E] in
theorem isInvar_omegaGens_of_neg_a {W : Submodule ℝ E} (hW : IsInvar (omegaGens k (-a) q j) W) :
    IsInvar (omegaGens k a q j) W := by
  have := isInvar_omegaGens_neg_a hW
  rwa [neg_neg] at this

omit [FiniteDimensional ℝ E] in
theorem isMinInvar_omegaGens_neg_a {M : Submodule ℝ E} (hM : IsMinInvar (omegaGens k a q j) M) :
    IsMinInvar (omegaGens k (-a) q j) M :=
  ⟨hM.1, isInvar_omegaGens_neg_a hM.2.1, fun W hW hWi =>
    hM.2.2 W hW (isInvar_omegaGens_of_neg_a hWi)⟩

omit [FiniteDimensional ℝ E] in
theorem isInvar_omegaGens_neg_q {W : Submodule ℝ E} (hW : IsInvar (omegaGens k a q j) W) :
    IsInvar (omegaGens k a ((-1 : ℝ) • q) j) W := by
  rintro g ((hg | hg) | ⟨α, h1, h2, rfl⟩) w hw
  · rw [Set.mem_singleton_iff.1 (show g ∈ ({a} : Set (E →L[ℝ] E)) from hg)]
    exact hW a IsOmegaOps.a_mem w hw
  · rw [Set.mem_singleton_iff.1 hg, smul_apply]
    exact W.smul_mem _ (hW q IsOmegaOps.q_mem w hw)
  · exact hW _ (IsOmegaOps.j_mem h1 h2) w hw

omit [FiniteDimensional ℝ E] in
theorem iWord_mem_of_isInvar {W : Submodule ℝ E} (hW : IsInvar (omegaGens k a q j) W) :
    ∀ w ∈ W, iWord k j w ∈ W :=
  iWord_mem fun _ h1 h2 w hw => hW _ (IsOmegaOps.j_mem h1 h2) w hw

/-- **`A = c·i` on a minimal piece** (Milnor p. 147). -/
theorem IsOmegaOps.exists_eq_smul_iWord (h : IsOmegaOps k a q j) (hI : IsIOps k a q j)
    (hk : k ≠ 0) {M : Submodule ℝ E} (hM : IsMinInvar (omegaGens k a q j) M) :
    ∃ c : ℝ, ∀ v ∈ M, a v = c • iWord k j v := by
  set e := iWord k j with he
  have heM := iWord_mem_of_isInvar hM.2.1
  have hS : ContinuousLinearMap.adjoint (a * e) = a * e := by
    rw [← ContinuousLinearMap.star_eq_adjoint, star_mul, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.star_eq_adjoint, hI.skew, h.a_skew, neg_mul_neg, hI.ia]
  have hSM : ∀ v ∈ M, (a * e) v ∈ M := fun v hv =>
    hM.2.1 a IsOmegaOps.a_mem _ (heM v hv)
  have hcomm : ∀ g ∈ omegaGens k a q j, ∀ v, (a * e) (g v) = g ((a * e) v) := by
    rintro g ((hg | hg) | ⟨α, h1, h2, rfl⟩) v
    · rw [Set.mem_singleton_iff.1 (show g ∈ ({a} : Set (E →L[ℝ] E)) from hg)]
      change a (e (a v)) = a (a (e v))
      rw [← mul_apply_eq_comp e a, hI.ia]; rfl
    · rw [Set.mem_singleton_iff.1 hg]
      change a (e (q v)) = q (a (e v))
      have h1 := congrArg (fun F : E →L[ℝ] E => F v) hI.iq
      have h2 := congrArg (fun F : E →L[ℝ] E => F (e v)) (h.aq hk)
      simp only [mul_apply_eq_comp, neg_apply] at h1 h2
      rw [h1, map_neg, h2, neg_neg]
    · change a (e (j α v)) = j α (a (e v))
      have h3 := congrArg (fun F : E →L[ℝ] E => F v) (hI.ij α h1 h2)
      have h4 := congrArg (fun F : E →L[ℝ] E => F (e v)) (h.ja α h1 h2)
      simp only [mul_apply_eq_comp] at h3 h4
      rw [h3, h4]
  obtain ⟨c₀, hc₀⟩ := hM.exists_scalar hS hSM hcomm
  refine ⟨-c₀, fun v hv => ?_⟩
  have h1 := hc₀ (e v) (heM v hv)
  have hee : e (e v) = -v := by
    have := congrArg (fun F : E →L[ℝ] E => F v) hI.sq
    simpa using this
  change a (e (e v)) = c₀ • e v at h1
  rw [hee, map_neg] at h1
  rw [neg_smul, ← h1, neg_neg]

theorem a_a_of_eq_smul (hI : IsIOps k a q j) {M : Submodule ℝ E}
    (hM : ∀ v ∈ M, iWord k j v ∈ M) {c : ℝ} (hc : ∀ v ∈ M, a v = c • iWord k j v) :
    ∀ v ∈ M, a (a v) = -((c ^ 2) • v) := fun v hv => by
  have hee : iWord k j (iWord k j v) = -v := by
    have := congrArg (fun F : E →L[ℝ] E => F v) hI.sq
    simpa using this
  rw [hc v hv, map_smul, hc _ (hM v hv), hee, smul_neg, smul_neg, smul_smul, sq]

omit [FiniteDimensional ℝ E] in
/-- **A minimal piece is a minimal space for the `k` structures `J_1, …, J_{k−1}, J'`** whenever
`J'`-invariance implies `J`-invariance (`J' = ±J`). -/
theorem isMinimal_cliffFam_k (hk : k ≠ 0) {q' : E →L[ℝ] E} {M : Submodule ℝ E}
    (hM : IsMinInvar (omegaGens k a q j) M) {c : ℝ} (hc : ∀ v ∈ M, a v = c • iWord k j v)
    (hq' : ∀ W : Submodule ℝ E, (∀ w ∈ W, q' w ∈ W) → ∀ w ∈ W, q w ∈ W)
    (hM' : IsInvar (omegaGens k a q' j) M) (s : ℝ) :
    IsMinimalCliffordModule (cliffFam k a q' j M hM' s) k := by
  refine ⟨Submodule.nontrivial_iff_ne_bot.2 hM.1, fun W hW => ?_⟩
  set W' := W.map M.subtype with hW'
  have hmem : ∀ x : M, x ∈ W → (x : E) ∈ W' := fun x hx => ⟨x, hx, rfl⟩
  have hj' : ∀ α, 1 ≤ α → α < k → ∀ y ∈ W', j α y ∈ W' := by
    rintro α h1 h2 _ ⟨x, hx, rfl⟩
    have := hmem _ (hW α h1 h2.le x hx)
    rwa [cliffFam_lt hM' s h1 h2] at this
  have hq'' : ∀ y ∈ W', q' y ∈ W' := by
    rintro _ ⟨x, hx, rfl⟩
    have := hmem _ (hW k (Nat.one_le_iff_ne_zero.2 hk) le_rfl x hx)
    rwa [cliffFam_k] at this
  have hqW := hq' W' hq''
  have he := iWord_mem hj'
  have hinv : IsInvar (omegaGens k a q j) W' := by
    rintro g ((hg | hg) | ⟨α, h1, h2, rfl⟩)
    · rw [Set.mem_singleton_iff.1 (show g ∈ ({a} : Set (E →L[ℝ] E)) from hg)]
      rintro _ ⟨x, hx, rfl⟩
      rw [Submodule.subtype_apply, hc x x.2]
      exact W'.smul_mem _ (he _ (hmem x hx))
    · rw [Set.mem_singleton_iff.1 hg]; exact hqW
    · exact hj' α h1 h2
  rcases hM.2.2 W' (by rintro _ ⟨x, -, rfl⟩; exact x.2) hinv with h0 | htop
  · left
    exact Submodule.map_injective_of_injective M.injective_subtype
      (h0.trans (Submodule.map_bot _).symm)
  · right
    rw [eq_top_iff]
    intro x _
    have : (x : E) ∈ W' := by rw [htop]; exact x.2
    obtain ⟨y, hy, hxy⟩ := this
    have hyx : y = x := Subtype.ext hxy
    exact hyx ▸ hy

/-- **Lemma 24.8 between two pieces, for `k` structures** (Milnor p. 148): an isomorphism
`T : M₀ ≅ M₁` commuting with `J_1, …, J_{k−1}` and anticommuting with `J`. -/
theorem exists_inter_two (h : IsOmegaOps k a q j) (hI : IsIOps k a q j) (hk : k ≠ 0)
    (hk8 : k ≤ 8) (hk3 : k % 4 ≠ 3) {M₀ M₁ : Submodule ℝ E}
    (hM₀ : IsMinInvar (omegaGens k a q j) M₀) (hM₁ : IsMinInvar (omegaGens k a q j) M₁)
    {c₀ c₁ : ℝ} (hc₀0 : c₀ ≠ 0) (hc₁0 : c₁ ≠ 0) (hc₀ : ∀ v ∈ M₀, a v = c₀ • iWord k j v)
    (hc₁ : ∀ v ∈ M₁, a v = c₁ • iWord k j v) :
    ∃ T : M₀ ≃ₗ[ℝ] M₁, (∀ α, 1 ≤ α → α < k → ∀ (x : M₀) (hx : j α x ∈ M₀),
      (T ⟨j α x, hx⟩ : E) = j α (T x)) ∧
      ∀ (x : M₀) (hx : q x ∈ M₀), (T ⟨q x, hx⟩ : E) = -q (T x) := by
  have h' := h.neg_q hk
  have hM₁' := isInvar_omegaGens_neg_q hM₁.2.1
  have hC₀ := (h.isClifford_cliffFam (hM := hM₀.2.1) (s := c₀⁻¹)
    (a_a_of_eq_smul hI (iWord_mem_of_isInvar hM₀.2.1) hc₀) (by field_simp)).mono (Nat.le_succ k)
  have hC₁ := (h'.isClifford_cliffFam (hM := hM₁') (s := c₁⁻¹)
    (a_a_of_eq_smul hI (iWord_mem_of_isInvar hM₁.2.1) hc₁) (by field_simp)).mono (Nat.le_succ k)
  have hm₀ := isMinimal_cliffFam_k hk hM₀ hc₀ (fun _ hW => hW) hM₀.2.1 c₀⁻¹
  have hm₁ := isMinimal_cliffFam_k hk hM₁ hc₁ (q' := (-1 : ℝ) • q) (fun W hW w hw => by
    have := W.smul_mem (-1 : ℝ) (hW w hw)
    rwa [smul_apply, smul_smul, neg_one_mul, neg_neg, one_smul] at this)
    hM₁' c₁⁻¹
  obtain ⟨T, hT⟩ := exists_iso_of_isMinimal hk8 hk3 hC₀ hC₁ hm₀ hm₁
  refine ⟨T, fun α h1 h2 x hx => ?_, fun x hx => ?_⟩
  · have e : (⟨j α x, hx⟩ : M₀) = cliffFam k a q j M₀ hM₀.2.1 c₀⁻¹ α x :=
      Subtype.ext (by rw [cliffFam_lt hM₀.2.1 c₀⁻¹ h1 h2])
    rw [e, hT α h1 h2.le, cliffFam_lt hM₁' c₁⁻¹ h1 h2]
  · have e : (⟨q x, hx⟩ : M₀) = cliffFam k a q j M₀ hM₀.2.1 c₀⁻¹ k x :=
      Subtype.ext (by rw [cliffFam_k])
    rw [e, hT k (Nat.one_le_iff_ne_zero.2 hk) le_rfl, cliffFam_k,
      smul_apply, neg_one_smul]

end Two

end Morse
