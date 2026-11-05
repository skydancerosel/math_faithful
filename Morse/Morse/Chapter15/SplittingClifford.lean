import Morse.Chapter15.InvariantSplitting
import Morse.Chapter15.MinimalModules

/-!
Milnor, *Morse Theory*, §24, pp. 144–145; Exposition/Chapter15.md, §6, Lemma 6.1 and the proof of
the index bound.

# The `k + 1` structures on a minimal piece, and Lemma 24.8 between two pieces

## Milnor's text, paraphrased

(pp. 144–145) On a minimal piece `M_h` (with `A² = −a_h²`), `J'_h = a_h⁻¹JA` is a complex
structure anticommuting with `J_1, …, J_{k−1}, J`, so `M_h` is a minimal space for `k + 1`
structures, of dimension `m_{k+1}`; by Lemma 24.8 there is an isomorphism `M_h → M̄_j`.

## What is formalized

On `E` (an inner product space; later `ℝⁿ`) with operators `a = A`, `q = J` (`q = 1` for `k = 0`),
`j α = J_α` satisfying Milnor's relations (`Morse.IsOmegaOps`), and the generators
`Morse.omegaGens = {A, J, J_1, …, J_{k−1}}`:

* `Morse.IsOmegaOps.exists_sq_eq`: **`A² = −c` on a minimal invariant piece** (Lemma 6.1).
* `Morse.cliffFam M s`: the restrictions of `J_1, …, J_{k−1}, J, s·JA` to `M`;
  `Morse.IsOmegaOps.isClifford_cliffFam` (**Clifford relations** when `s²c = 1`) and
  `Morse.IsOmegaOps.isMinimal_cliffFam` (**minimal**, since `A = s⁻¹Jᴴ(sJA)`).
* `Morse.IsInter`: an intertwiner `T : M₀ → M₁` of `cliffFam … s₀` with `cliffFam … s₁`;
  `Morse.IsInter.apply_a`: `T(Ax) = (s₁/s₀)A(Tx)`.
* `Morse.interOp T = ι_{M₁} ∘ T ∘ π_{M₀}` and its relations: it commutes with `J`, `J_α`
  (`Morse.interOp_comm_q`, `Morse.interOp_comm_j`), `DA = (s₁/s₀)AD` (`Morse.interOp_a`),
  `A²D = −c₁D`, `DA² = −c₀D`, the projections (`Morse.interOp_starProjection`,
  `Morse.adjoint_interOp_starProjection`, `Morse.starProjection_a_interOp`, …), `AD ≠ 0`, and
  `AD`, `ADA` independent (`Morse.linearIndependent_a_interOp`, the doubling for `k = 0`).

## What Milnor leaves implicit

* The isomorphism of Lemma 24.8 is only linear (`Morse.exists_iso_of_isMinimal`); Milnor asks for
  an isometry, but the construction never needs it: `B = D − Dᵀ` is skew for any `D`, and `Dᵀ`
  intertwines in the other direction because all structures are skew.
-/

open Set Module

noncomputable section

namespace Morse

section Ops

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The operators of §6 on `ℝⁿ`: `a = A` (the velocity of the geodesic, skew), `q = J` (the base
point; `q = 1` for `k = 0`), `j α = J_α` for `α < k`, with Milnor's relations. -/
structure IsOmegaOps (k : ℕ) (a q : E →L[ℝ] E) (j : ℕ → E →L[ℝ] E) : Prop where
  a_skew : ContinuousLinearMap.adjoint a = -a
  q_zero : k = 0 → q = 1
  q_sq : k ≠ 0 → q * q = -1
  q_skew : k ≠ 0 → ContinuousLinearMap.adjoint q = -q
  aq : k ≠ 0 → a * q = -(q * a)
  j_sq : ∀ α, 1 ≤ α → α < k → j α * j α = -1
  j_skew : ∀ α, 1 ≤ α → α < k → ContinuousLinearMap.adjoint (j α) = -(j α)
  j_anti : ∀ α β, 1 ≤ α → α < k → 1 ≤ β → β < k → α ≠ β → j α * j β = -(j β * j α)
  jq : ∀ α, 1 ≤ α → α < k → j α * q = -(q * j α)
  ja : ∀ α, 1 ≤ α → α < k → j α * a = a * j α

variable {k : ℕ} {a q : E →L[ℝ] E} {j : ℕ → E →L[ℝ] E}

variable (k a q j) in
/-- The generators `{A, J, J_1, …, J_{k−1}}` of Lemma 6.1. -/
def omegaGens : Set (E →L[ℝ] E) := {a, q} ∪ {g | ∃ α, 1 ≤ α ∧ α < k ∧ g = j α}

namespace IsOmegaOps

variable (h : IsOmegaOps k a q j)
include h

omit h [FiniteDimensional ℝ E] in
theorem a_mem : a ∈ omegaGens k a q j := Or.inl (Or.inl rfl)
omit h [FiniteDimensional ℝ E] in
theorem q_mem : q ∈ omegaGens k a q j := Or.inl (Or.inr rfl)
omit h [FiniteDimensional ℝ E] in
theorem j_mem {α : ℕ} (h1 : 1 ≤ α) (h2 : α < k) : j α ∈ omegaGens k a q j :=
  Or.inr ⟨α, h1, h2, rfl⟩

theorem isStarSigned : IsStarSigned (omegaGens k a q j) := by
  rintro g ((rfl | rfl) | ⟨α, h1, h2, rfl⟩)
  · exact Or.inr h.a_skew
  · rcases Nat.eq_zero_or_pos k with hk | hk
    · rw [h.q_zero hk, ← ContinuousLinearMap.star_eq_adjoint, star_one]; exact Or.inl rfl
    · exact Or.inr (h.q_skew hk.ne')
  · exact Or.inr (h.j_skew α h1 h2)

/-- `qᴴ q = 1`, and `qᴴ = ±q` commutes with everything commuting with `q`. -/
theorem adjoint_q_mul_q : ContinuousLinearMap.adjoint q * q = 1 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rw [h.q_zero hk, ← ContinuousLinearMap.star_eq_adjoint, star_one, mul_one]
  · rw [h.q_skew hk.ne', neg_mul, h.q_sq hk.ne', neg_neg]

theorem a_sq_comm {g : E →L[ℝ] E} (hg : g ∈ omegaGens k a q j) (v : E) :
    (-(a * a)) (g v) = g ((-(a * a)) v) := by
  rcases hg with ((rfl | rfl) | ⟨α, h1, h2, rfl⟩)
  · simp
  · rcases Nat.eq_zero_or_pos k with hk | hk
    · rw [h.q_zero hk]; simp
    · have e : a * a * g = g * (a * a) := by
        rw [mul_assoc, h.aq hk.ne', mul_neg, ← mul_assoc, h.aq hk.ne', neg_mul, neg_neg,
          mul_assoc]
      have := congrArg (fun T : E →L[ℝ] E => T v) e
      simpa using this
  · have e : a * a * j α = j α * (a * a) := by
      rw [mul_assoc, ← h.ja α h1 h2, ← mul_assoc, ← h.ja α h1 h2, mul_assoc]
    have := congrArg (fun T : E →L[ℝ] E => T v) e
    simpa using this

/-- **On a minimal invariant subspace, `A² = −c`** (Lemma 6.1). -/
theorem exists_sq_eq {M : Submodule ℝ E} (hM : IsMinInvar (omegaGens k a q j) M) :
    ∃ c : ℝ, ∀ v ∈ M, a (a v) = -(c • v) := by
  have hS : ContinuousLinearMap.adjoint (-(a * a)) = -(a * a) := by
    rw [← ContinuousLinearMap.star_eq_adjoint, star_neg, star_mul,
      ContinuousLinearMap.star_eq_adjoint, h.a_skew, neg_mul_neg]
  obtain ⟨c, hc⟩ := hM.exists_scalar hS (fun v hv => by
      simp only [neg_apply]
      exact M.neg_mem (hM.2.1 a a_mem _ (hM.2.1 a a_mem v hv)))
    (fun g hg v => h.a_sq_comm hg v)
  refine ⟨c, fun v hv => ?_⟩
  have := hc v hv
  simp only [neg_apply] at this
  rw [← this, neg_neg]
  rfl

/-- The relations among `j_α`, `q`, `qa` as operators on `E`. -/
theorem qa_qa_of_ne (hk : k ≠ 0) : (q * a) * (q * a) = a * a := by
  rw [mul_assoc, ← mul_assoc a, h.aq hk, neg_mul, mul_neg, ← mul_assoc, ← mul_assoc, h.q_sq hk,
    mul_assoc, neg_mul, one_mul, neg_neg]

theorem qa_qa : (q * a) * (q * a) = a * a := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rw [h.q_zero hk, one_mul]
  · exact h.qa_qa_of_ne hk.ne'

theorem j_qa {α : ℕ} (h1 : 1 ≤ α) (h2 : α < k) : j α * (q * a) = -((q * a) * j α) := by
  rw [← mul_assoc, h.jq α h1 h2, neg_mul, mul_assoc, h.ja α h1 h2, mul_assoc]

theorem q_qa (hk : k ≠ 0) : q * (q * a) = -((q * a) * q) := by
  rw [mul_assoc q a q, h.aq hk, mul_neg, neg_neg, ← mul_assoc]

end IsOmegaOps

variable (k a q j) in
/-- **The `k + 1` anticommuting structures of Lemma 6.1 on a minimal piece `M`**:
`J_1, …, J_{k−1}, J` and `s·JA` (`s = ±1/b`, `A² = −b²` on `M`), restricted to `M`. -/
def cliffFam (M : Submodule ℝ E) (hM : IsInvar (omegaGens k a q j) M) (s : ℝ) :
    ℕ → Module.End ℝ M := fun α =>
  if hα : 1 ≤ α ∧ α < k then
    (j α : E →ₗ[ℝ] E).restrict (fun v hv => hM _ (IsOmegaOps.j_mem hα.1 hα.2) v hv)
  else if α = k then (q : E →ₗ[ℝ] E).restrict (fun v hv => hM _ IsOmegaOps.q_mem v hv)
  else s • ((q * a : E →L[ℝ] E) : E →ₗ[ℝ] E).restrict
    (fun v hv => hM _ IsOmegaOps.q_mem _ (hM _ IsOmegaOps.a_mem v hv))

variable (k a q j) in
/-- The operators on `E` whose restrictions are `cliffFam`. -/
def cliffTop (s : ℝ) (α : ℕ) : E →L[ℝ] E :=
  if 1 ≤ α ∧ α < k then j α else if α = k then q else s • (q * a)

omit [FiniteDimensional ℝ E] in
theorem cliffTop_lt (s : ℝ) {α : ℕ} (h1 : 1 ≤ α) (h2 : α < k) : cliffTop k a q j s α = j α := by
  simp [cliffTop, h1, h2]

omit [FiniteDimensional ℝ E] in
theorem cliffTop_k (s : ℝ) : cliffTop k a q j s k = q := by
  simp [cliffTop]

omit [FiniteDimensional ℝ E] in
theorem cliffTop_succ (s : ℝ) : cliffTop k a q j s (k + 1) = s • (q * a) := by
  simp [cliffTop]

theorem IsOmegaOps.cliffTop_anti (h : IsOmegaOps k a q j) (s : ℝ) {α β : ℕ} (h1 : 1 ≤ α)
    (h2 : α ≤ k + 1) (h3 : 1 ≤ β) (h4 : β ≤ k + 1) (hαβ : α ≠ β) :
    cliffTop k a q j s α * cliffTop k a q j s β =
      -(cliffTop k a q j s β * cliffTop k a q j s α) := by
  have key : ∀ α β, 1 ≤ α → α ≤ k + 1 → 1 ≤ β → β ≤ k + 1 → α < β →
      cliffTop k a q j s α * cliffTop k a q j s β =
        -(cliffTop k a q j s β * cliffTop k a q j s α) := by
    intro α β h1 h2 h3 h4 hlt
    rcases lt_trichotomy β k with hβ | rfl | hβ
    · rw [cliffTop_lt s h1 (hlt.trans hβ), cliffTop_lt s h3 hβ]
      exact h.j_anti α β h1 (hlt.trans hβ) h3 hβ hlt.ne
    · rw [cliffTop_lt s h1 hlt, cliffTop_k]
      exact h.jq α h1 hlt
    · obtain rfl : β = k + 1 := by omega
      rw [cliffTop_succ, mul_smul_comm, smul_mul_assoc, ← smul_neg]
      congr 1
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hlt) with hα | rfl
      · rw [cliffTop_lt s h1 hα]
        exact h.j_qa h1 hα
      · rw [cliffTop_k]
        exact h.q_qa (by omega)
  rcases lt_or_gt_of_ne hαβ with hlt | hgt
  · exact key α β h1 h2 h3 h4 hlt
  · rw [key β α h3 h4 h1 h2 hgt, neg_neg]

section CliffFam

variable {M : Submodule ℝ E} (hM : IsInvar (omegaGens k a q j) M) (s : ℝ)

omit [FiniteDimensional ℝ E] in
theorem cliffFam_apply (α : ℕ) (w : M) :
    (cliffFam k a q j M hM s α w : E) = cliffTop k a q j s α w := by
  unfold cliffFam cliffTop
  split_ifs <;> simp

omit [FiniteDimensional ℝ E] in
theorem cliffFam_lt {α : ℕ} (h1 : 1 ≤ α) (h2 : α < k) (w : M) :
    (cliffFam k a q j M hM s α w : E) = j α w := by
  simp [cliffFam, h1, h2]

omit [FiniteDimensional ℝ E] in
theorem cliffFam_k (w : M) : (cliffFam k a q j M hM s k w : E) = q w := by
  simp [cliffFam]

omit [FiniteDimensional ℝ E] in
theorem cliffFam_succ (w : M) : (cliffFam k a q j M hM s (k + 1) w : E) = s • q (a w) := by
  simp [cliffFam]

variable {hM s}

/-- **The restricted structures satisfy the Clifford relations** when `s²c = 1`, `A² = −c` on
`M`. -/
theorem IsOmegaOps.isClifford_cliffFam (h : IsOmegaOps k a q j) {c : ℝ}
    (hc : ∀ v ∈ M, a (a v) = -(c • v)) (hs : s * s * c = 1) :
    IsClifford (cliffFam k a q j M hM s) (k + 1) := by
  have hap : ∀ (T : E →L[ℝ] E) (w : M), ((T : E →ₗ[ℝ] E) w : E) = T w := fun _ _ => rfl
  constructor
  · intro α h1 h2
    refine LinearMap.ext fun w => Subtype.ext ?_
    simp only [Module.End.mul_apply, LinearMap.neg_apply, Module.End.one_apply,
      Submodule.coe_neg]
    rcases lt_trichotomy α k with hlt | rfl | hgt
    · rw [cliffFam_lt hM s h1 hlt, cliffFam_lt hM s h1 hlt]
      have := congrArg (fun T : E →L[ℝ] E => T w) (h.j_sq α h1 hlt)
      simpa using this
    · rw [cliffFam_k, cliffFam_k]
      have := congrArg (fun T : E →L[ℝ] E => T w) (h.q_sq (by omega))
      simpa using this
    · have hα : α = k + 1 := by omega
      subst hα
      rw [cliffFam_succ, cliffFam_succ]
      have e : q (a (q (a (w : E)))) = a (a w) :=
        congrArg (fun T : E →L[ℝ] E => T w) h.qa_qa
      rw [map_smul, map_smul, e, hc w w.2, smul_neg, smul_smul, smul_neg, smul_smul,
        ← mul_assoc, hs, one_smul]
  · intro α β h1 h2 h3 h4 hαβ
    refine LinearMap.ext fun w => Subtype.ext ?_
    simp only [Module.End.mul_apply, LinearMap.neg_apply, Submodule.coe_neg, cliffFam_apply]
    have := congrArg (fun T : E →L[ℝ] E => T w) (h.cliffTop_anti s h1 h2 h3 h4 hαβ)
    simpa using this


/-- **A minimal invariant piece is a minimal `(J_1, …, J_{k−1}, J, s·JA)`-space** (Milnor
p. 145: "`M_h` is minimal for the `k + 1` structures"): a subspace invariant under them is
invariant under `A = s⁻¹ Jᴴ (s·JA)`. -/
theorem IsOmegaOps.isMinimal_cliffFam (h : IsOmegaOps k a q j) (hM' : IsMinInvar (omegaGens k a q j) M)
    (hs : s ≠ 0) : IsMinimalCliffordModule (cliffFam k a q j M hM s) (k + 1) := by
  refine ⟨Submodule.nontrivial_iff_ne_bot.2 hM'.1, fun W hW => ?_⟩
  set W' := W.map M.subtype with hW'
  have hmem : ∀ x : M, x ∈ W → (x : E) ∈ W' := fun x hx => ⟨x, hx, rfl⟩
  have hFW : ∀ α, 1 ≤ α → α ≤ k + 1 → ∀ x : M, x ∈ W →
      cliffTop k a q j s α x ∈ W' := fun α h1 h2 x hx => by
    rw [← cliffFam_apply hM s α x]; exact hmem _ (hW α h1 h2 x hx)
  have hq : ∀ y ∈ W', q y ∈ W' := by
    rintro _ ⟨x, hx, rfl⟩
    rcases Nat.eq_zero_or_pos k with hk | hk
    · rw [h.q_zero hk]; exact hmem x hx
    · have := hFW k hk (by omega) x hx
      rwa [cliffTop_k] at this
  have hinv : IsInvar (omegaGens k a q j) W' := by
    rintro g ((hg | hg) | ⟨α, h1, h2, rfl⟩)
    · rw [Set.mem_singleton_iff.1 (show g ∈ ({a} : Set (E →L[ℝ] E)) from hg)]
      rintro _ ⟨x, hx, rfl⟩
      have h3 := hFW (k + 1) (by omega) le_rfl x hx
      rw [cliffTop_succ] at h3
      have hqH : ∀ y ∈ W', ContinuousLinearMap.adjoint q y ∈ W' := fun y hy => by
        rcases Nat.eq_zero_or_pos k with hk | hk
        · rw [h.q_zero hk, ← ContinuousLinearMap.star_eq_adjoint, star_one]; exact hy
        · rw [h.q_skew hk.ne']; exact W'.neg_mem (hq y hy)
      have e : a (x : E) = s⁻¹ • ContinuousLinearMap.adjoint q ((s • (q * a)) x) := by
        have := congrArg (fun T : E →L[ℝ] E => T (a x)) h.adjoint_q_mul_q
        simp only [one_apply_eq_self] at this
        rw [smul_apply, map_smul, smul_smul, inv_mul_cancel₀ hs, one_smul]
        exact this.symm
      change a (x : E) ∈ W'
      rw [e]
      exact W'.smul_mem _ (hqH _ h3)
    · rw [Set.mem_singleton_iff.1 hg]; exact hq
    · rintro _ ⟨x, hx, rfl⟩
      have := hFW α h1 (by omega) x hx
      rwa [cliffTop_lt s h1 h2] at this
  rcases hM'.2.2 W' (by rintro _ ⟨x, -, rfl⟩; exact x.2) hinv with h0 | htop
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

end CliffFam

/-! ### Intertwiners between two pieces -/

section Inter

variable {M₀ M₁ : Submodule ℝ E} (hM₀ : IsInvar (omegaGens k a q j) M₀)
  (hM₁ : IsInvar (omegaGens k a q j) M₁) {s₀ s₁ : ℝ} {T : M₀ →ₗ[ℝ] M₁}

/-- `T` intertwines the structures `cliffFam … s₀` on `M₀` with `cliffFam … s₁` on `M₁`. -/
def IsInter (hM₀ : IsInvar (omegaGens k a q j) M₀) (hM₁ : IsInvar (omegaGens k a q j) M₁)
    (s₀ s₁ : ℝ) (T : M₀ →ₗ[ℝ] M₁) : Prop :=
  ∀ α, 1 ≤ α → α ≤ k + 1 → ∀ v, T (cliffFam k a q j M₀ hM₀ s₀ α v) =
    cliffFam k a q j M₁ hM₁ s₁ α (T v)

variable {hM₀ hM₁}

omit [FiniteDimensional ℝ E] in
theorem IsInter.apply_j (hT : IsInter hM₀ hM₁ s₀ s₁ T) {α : ℕ} (h1 : 1 ≤ α) (h2 : α < k) (x : M₀)
    (hx : j α x ∈ M₀) : (T ⟨j α x, hx⟩ : E) = j α (T x) := by
  have e : (⟨j α x, hx⟩ : M₀) = cliffFam k a q j M₀ hM₀ s₀ α x :=
    Subtype.ext (by rw [cliffFam_lt hM₀ s₀ h1 h2])
  rw [e, hT α h1 (by omega), cliffFam_lt hM₁ s₁ h1 h2]

theorem IsInter.apply_q (h : IsOmegaOps k a q j) (hT : IsInter hM₀ hM₁ s₀ s₁ T) (x : M₀)
    (hx : q x ∈ M₀) : (T ⟨q x, hx⟩ : E) = q (T x) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · have hq := h.q_zero hk
    have e : (⟨q x, hx⟩ : M₀) = x := Subtype.ext (by simp [hq])
    rw [e, hq]; rfl
  · have e : (⟨q x, hx⟩ : M₀) = cliffFam k a q j M₀ hM₀ s₀ k x :=
      Subtype.ext (by rw [cliffFam_k])
    rw [e, hT k hk (by omega), cliffFam_k]

/-- **`T` transports `A`** (Milnor p. 145): `T(Ax) = (s₁/s₀) A(Tx)`, since `A = s₀⁻¹ Jᴴ (s₀JA)`
and `T` intertwines `J` and `s₀JA ↦ s₁JA`. -/
theorem IsInter.apply_a (h : IsOmegaOps k a q j) (hT : IsInter hM₀ hM₁ s₀ s₁ T) (hs₀ : s₀ ≠ 0)
    (x : M₀) (hx : a x ∈ M₀) : (T ⟨a x, hx⟩ : E) = (s₀⁻¹ * s₁) • a (T x) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · have hq := h.q_zero hk
    subst hk
    have e : (⟨a x, hx⟩ : M₀) = s₀⁻¹ • cliffFam 0 a q j M₀ hM₀ s₀ 1 x := Subtype.ext (by
      rw [Submodule.coe_smul, cliffFam_succ, hq, smul_smul, inv_mul_cancel₀ hs₀, one_smul]
      rfl)
    rw [e, map_smul, hT 1 le_rfl le_rfl, Submodule.coe_smul, cliffFam_succ, hq, smul_smul]
    rfl
  · have hkk : k ≠ 0 := hk.ne'
    have hqq := h.q_sq hkk
    have hqqa : ∀ y : E, q (q y) = -y := fun y => by
      have := congrArg (fun F : E →L[ℝ] E => F y) hqq
      simp only [neg_apply, one_apply_eq_self] at this
      exact this
    have e : (⟨a x, hx⟩ : M₀) = (-s₀⁻¹) • cliffFam k a q j M₀ hM₀ s₀ k
        (cliffFam k a q j M₀ hM₀ s₀ (k + 1) x) := Subtype.ext (by
      rw [Submodule.coe_smul, cliffFam_k, cliffFam_succ, map_smul, smul_smul, hqqa, smul_neg,
        neg_mul, inv_mul_cancel₀ hs₀, neg_smul, one_smul, neg_neg])
    rw [e, map_smul, hT k hk (by omega), hT (k + 1) (by omega) le_rfl, Submodule.coe_smul,
      cliffFam_k, cliffFam_succ, map_smul, hqqa, smul_neg, smul_neg, smul_smul, neg_mul, neg_smul,
      neg_neg]

theorem IsInvar.orthogonalProjectionOnto_comm (h : IsOmegaOps k a q j)
    {M : Submodule ℝ E} (hM : IsInvar (omegaGens k a q j) M)
    {g : E →L[ℝ] E} (hg : g ∈ omegaGens k a q j) (v : E) :
    (M.orthogonalProjectionOnto (g v) : E) = g (M.orthogonalProjectionOnto v) := by
  have := hM.starProjection_comm h.isStarSigned hg v
  simpa only [Submodule.starProjection_apply] using this

variable (T) in
/-- **The operator `D = ι_{M₁} ∘ T ∘ π_{M₀}`** on `E` (Milnor's `B` restricted to one block). -/
def interOp : E →L[ℝ] E :=
  M₁.subtypeL ∘L (LinearMap.toContinuousLinearMap T) ∘L M₀.orthogonalProjectionOnto

theorem interOp_apply (v : E) :
    interOp T v = (T (M₀.orthogonalProjectionOnto v) : E) := rfl

theorem interOp_comm_q (h : IsOmegaOps k a q j) (hT : IsInter hM₀ hM₁ s₀ s₁ T) :
    interOp T * q = q * interOp T := by
  refine ContinuousLinearMap.ext fun v => ?_
  change interOp T (q v) = q (interOp T v)
  have e : M₀.orthogonalProjectionOnto (q v) =
      ⟨q (M₀.orthogonalProjectionOnto v), hM₀ q IsOmegaOps.q_mem _ (Submodule.coe_mem _)⟩ :=
    Subtype.ext (hM₀.orthogonalProjectionOnto_comm h IsOmegaOps.q_mem v)
  rw [interOp_apply, interOp_apply, e, hT.apply_q h]

theorem interOp_comm_j (h : IsOmegaOps k a q j) (hT : IsInter hM₀ hM₁ s₀ s₁ T) {α : ℕ}
    (h1 : 1 ≤ α) (h2 : α < k) : interOp T * j α = j α * interOp T := by
  refine ContinuousLinearMap.ext fun v => ?_
  change interOp T (j α v) = j α (interOp T v)
  have e : M₀.orthogonalProjectionOnto (j α v) =
      ⟨j α (M₀.orthogonalProjectionOnto v),
        hM₀ (j α) (IsOmegaOps.j_mem h1 h2) _ (Submodule.coe_mem _)⟩ :=
    Subtype.ext (hM₀.orthogonalProjectionOnto_comm h (IsOmegaOps.j_mem h1 h2) v)
  rw [interOp_apply, interOp_apply, e, hT.apply_j h1 h2]

theorem interOp_a (h : IsOmegaOps k a q j) (hT : IsInter hM₀ hM₁ s₀ s₁ T) (hs₀ : s₀ ≠ 0) :
    interOp T * a = (s₀⁻¹ * s₁) • (a * interOp T) := by
  refine ContinuousLinearMap.ext fun v => ?_
  change interOp T (a v) = (s₀⁻¹ * s₁) • a (interOp T v)
  have e : M₀.orthogonalProjectionOnto (a v) =
      ⟨a (M₀.orthogonalProjectionOnto v), hM₀ a IsOmegaOps.a_mem _ (Submodule.coe_mem _)⟩ :=
    Subtype.ext (hM₀.orthogonalProjectionOnto_comm h IsOmegaOps.a_mem v)
  rw [interOp_apply, interOp_apply, e, hT.apply_a h hs₀]

omit hM₀ hM₁ in
theorem a_a_interOp {c₁ : ℝ} (hc₁ : ∀ w ∈ M₁, a (a w) = -(c₁ • w)) :
    a * (a * interOp T) = -c₁ • interOp T := by
  refine ContinuousLinearMap.ext fun v => ?_
  change a (a (interOp T v)) = -c₁ • interOp T v
  rw [interOp_apply, hc₁ _ (Submodule.coe_mem _), neg_smul]

theorem interOp_a_a (h : IsOmegaOps k a q j) (hM₀ : IsInvar (omegaGens k a q j) M₀) {c₀ : ℝ}
    (hc₀ : ∀ v ∈ M₀, a (a v) = -(c₀ • v)) : interOp T * a * a = -c₀ • interOp T := by
  refine ContinuousLinearMap.ext fun v => ?_
  change interOp T (a (a v)) = -c₀ • interOp T v
  have e : M₀.orthogonalProjectionOnto (a (a v)) = -c₀ • M₀.orthogonalProjectionOnto v :=
    Subtype.ext (by
      rw [hM₀.orthogonalProjectionOnto_comm h IsOmegaOps.a_mem,
        hM₀.orthogonalProjectionOnto_comm h IsOmegaOps.a_mem, hc₀ _ (Submodule.coe_mem _),
        Submodule.coe_smul, neg_smul])
  rw [interOp_apply, interOp_apply, e, map_smul, Submodule.coe_smul]

omit hM₀ hM₁ in
theorem interOp_starProjection : interOp T * M₀.starProjection = interOp T := by
  refine ContinuousLinearMap.ext fun v => ?_
  change interOp T (M₀.starProjection v) = interOp T v
  rw [interOp_apply, interOp_apply, Submodule.starProjection_apply,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

omit hM₀ hM₁ in
theorem adjoint_interOp_starProjection (horth : M₀ ⟂ M₁) :
    ContinuousLinearMap.adjoint (interOp T) * M₀.starProjection = 0 := by
  refine ContinuousLinearMap.ext fun v => ?_
  change ContinuousLinearMap.adjoint (interOp T) (M₀.starProjection v) = 0
  refine ext_inner_right ℝ fun w => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, inner_zero_left, interOp_apply]
  exact horth.inner_eq (M₀.starProjection_apply_mem v) (Submodule.coe_mem _)

theorem starProjection_a_interOp (hM₁ : IsInvar (omegaGens k a q j) M₁) :
    M₁.starProjection * (a * interOp T) = a * interOp T := by
  refine ContinuousLinearMap.ext fun v => ?_
  change M₁.starProjection (a (interOp T v)) = a (interOp T v)
  exact Submodule.starProjection_eq_self_iff.2 (hM₁ a IsOmegaOps.a_mem _ (Submodule.coe_mem _))

theorem starProjection_a_interOp_of_orth (hM₁ : IsInvar (omegaGens k a q j) M₁)
    {N : Submodule ℝ E} (hN : N ⟂ M₁) :
    N.starProjection * (a * interOp T) = 0 := by
  refine ContinuousLinearMap.ext fun v => ?_
  change N.starProjection (a (interOp T v)) = 0
  exact (Submodule.starProjection_apply_eq_zero_iff N).2
    (hN.symm.le (hM₁ a IsOmegaOps.a_mem _ (Submodule.coe_mem _)))

omit hM₀ hM₁ in
theorem interOp_apply_mem {x : E} (hx : x ∈ M₀) : interOp T x = (T ⟨x, hx⟩ : E) := by
  rw [interOp_apply, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨x, hx⟩]

omit hM₀ hM₁ [FiniteDimensional ℝ E] in
theorem eq_zero_of_a_eq_zero {c₁ : ℝ} (hc₁ : ∀ w ∈ M₁, a (a w) = -(c₁ • w)) (hc₁0 : c₁ ≠ 0)
    {w : E} (hw : w ∈ M₁) (h0 : a w = 0) : w = 0 := by
  have := hc₁ w hw
  rw [h0, map_zero, eq_comm, neg_eq_zero] at this
  exact (smul_eq_zero.1 this).resolve_left hc₁0

omit hM₀ hM₁ in
/-- `AD ≠ 0`. -/
theorem a_interOp_ne_zero (hM₀ne : M₀ ≠ ⊥) (hT : Function.Injective T) {c₁ : ℝ}
    (hc₁ : ∀ w ∈ M₁, a (a w) = -(c₁ • w)) (hc₁0 : c₁ ≠ 0) : a * interOp T ≠ 0 := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM₀ne
  intro h0
  have := congrArg (fun F : E →L[ℝ] E => F x) h0
  change a (interOp T x) = 0 at this
  rw [interOp_apply_mem hx] at this
  have hT0 := eq_zero_of_a_eq_zero hc₁ hc₁0 (Submodule.coe_mem _) this
  have : T ⟨x, hx⟩ = 0 := Subtype.ext hT0
  exact hx0 (congrArg Subtype.val (hT (this.trans (map_zero T).symm)))

/-- **`AD` and `ADA` are independent** (the doubling for `k = 0`, Lemma 24.2's two eigenvectors
per pair). -/
theorem linearIndependent_a_interOp (hM₀ : IsInvar (omegaGens k a q j) M₀) (hM₀ne : M₀ ≠ ⊥)
    (hT : Function.Injective T) {c₀ c₁ : ℝ} (hc₀ : ∀ v ∈ M₀, a (a v) = -(c₀ • v)) (hc₀0 : 0 < c₀)
    (hc₁ : ∀ w ∈ M₁, a (a w) = -(c₁ • w)) (hc₁0 : c₁ ≠ 0) :
    LinearIndependent ℝ ![a * interOp T, a * interOp T * a] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM₀ne
  have hax : a x ∈ M₀ := hM₀ a IsOmegaOps.a_mem x hx
  have h1 := congrArg (fun F : E →L[ℝ] E => F x) hst
  change s • a (interOp T x) + t • a (interOp T (a x)) = 0 at h1
  rw [interOp_apply_mem hx, interOp_apply_mem hax, ← map_smul, ← map_smul, ← map_add,
    ← Submodule.coe_smul, ← Submodule.coe_smul, ← Submodule.coe_add, ← map_smul, ← map_smul,
    ← map_add] at h1
  have h2 := eq_zero_of_a_eq_zero hc₁ hc₁0 (Submodule.coe_mem _) h1
  have h3 : s • (⟨x, hx⟩ : M₀) + t • ⟨a x, hax⟩ = 0 :=
    hT ((Subtype.ext h2 : T _ = 0).trans (map_zero T).symm)
  have h4 : s • x + t • a x = 0 := congrArg Subtype.val h3
  have h5 : s • a x - t • (c₀ • x) = 0 := by
    have := congrArg a h4
    rw [map_add, map_smul, map_smul, hc₀ x hx, map_zero, smul_neg, ← sub_eq_add_neg] at this
    exact this
  -- `(s² + c₀t²) x = 0`
  have h6 : (s ^ 2 + c₀ * t ^ 2) • x = 0 := by
    have : s • (s • x + t • a x) - t • (s • a x - t • (c₀ • x)) = 0 := by rw [h4, h5]; simp
    rw [← this]
    simp only [smul_add, smul_sub, smul_smul]
    module
  have h7 := (smul_eq_zero.1 h6).resolve_right hx0
  have hs : s = 0 := by nlinarith [sq_nonneg s, sq_nonneg t, mul_nonneg hc₀0.le (sq_nonneg t)]
  have ht : t = 0 := by
    have : c₀ * t ^ 2 = 0 := by nlinarith [sq_nonneg s, sq_nonneg t, mul_nonneg hc₀0.le (sq_nonneg t)]
    have := (mul_eq_zero.1 this).resolve_left hc₀0.ne'
    exact pow_eq_zero_iff two_ne_zero |>.1 this
  exact ⟨hs, ht⟩

end Inter

end Ops

end Morse
