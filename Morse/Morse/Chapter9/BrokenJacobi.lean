import Morse.Chapter9.IndexForm
import Morse.Chapter9.FormIndex

/-!
Milnor, *Morse Theory*, §15, pp. 83–85: broken Jacobi fields, Lemma 15.3 (the splitting
`TΩ_γ = TΩ_γ(t₀, …, t_k) ⊕ T'`) and Lemma 15.4 (the index of `E_**` is the index on broken
Jacobi fields, hence finite), for a submanifold `N ⊆ ℝᴷ` with the induced metric.

# Broken Jacobi fields and the finite-dimensional reduction

## Milnor's text, paraphrased

(pp. 83–85) For a fine subdivision `0 = t₀ < ⋯ < t_k = 1`, `TΩ_γ(t₀, …, t_k)` is the space of
fields `W ∈ TΩ_γ` that are Jacobi fields on each `[t_{i−1}, t_i]` (broken Jacobi fields), a finite
dimensional space; `T'` is the space of `W ∈ TΩ_γ` vanishing at all `t_i`.  **Lemma 15.3**:
`TΩ_γ = TΩ_γ(t₀, …, t_k) ⊕ T'`, the two summands are perpendicular for `E_**`, and `E_**` is
positive definite on `T'`.  (Given `W`, "it follows from 14.5" that there is a unique broken
Jacobi field `W₁` with `W₁(t_i) = W(t_i)`, and `W − W₁ ∈ T'`.)  **Lemma 15.4**: the index (or the
nullity) of `E_**` equals the index (or the nullity) of `E_**` restricted to the broken Jacobi
fields; in particular the index is finite.  "The proof is straightforward."

## In the embedded setting

Everything is done along `γ|[0, τ]` for `0 < τ ≤ 1`, as Milnor needs for `λ(τ)` on p. 85:

* `Morse.fieldsUpTo τ`: the fields of `TΩ_γ` vanishing outside `[0, τ]`, i.e. the fields along
  `γ|[0, τ]` vanishing at the ends, extended by zero (Milnor's extension in Assertion (1)); by
  Proposition 13.A, `E_**` restricted to them is Milnor's `(E_0^τ)_**`.
* `Morse.IsFine hc B τ`: the finite set `B ⊆ (0, τ)` of interior division points cuts `[0, τ]`
  into pieces of length `≤ h₀` (`Morse.fineMesh`); `Morse.exists_isFine` provides one, with the
  last division point as close to `τ` as wanted.
* `Morse.IsBrokenJacobi`, `Morse.brokenSpace hc B τ` (Milnor's `TΩ_γ(t₀, …, t_k)`),
  `Morse.nodeZero B τ` (Milnor's `T'`).
* `Morse.exists_isBrokenJacobi` and `Morse.IsBrokenJacobi.eqOn_zero`: broken Jacobi fields with
  arbitrary prescribed tangent values at the division points exist and are unique (induction over
  the division points, gluing segment by segment; on each segment `Morse.exists_jacobi_ends` and
  `Morse.eq_zero_of_short`).
* **Lemma 15.3**: `Morse.isCompl_broken_nodeZero`, `Morse.energyHessian_broken_nodeZero`,
  `Morse.energyHessian_nodeZero_pos`.
* **Lemma 15.4**: `Morse.lemma_15_4` (index), `Morse.lemma_15_4_ker` (null space),
  `Morse.formIndex_fieldsUpTo_lt_top` (finiteness).
* `Morse.energyHessian_broken_eq`: for broken Jacobi `W` and `Y` vanishing outside `[0, τ]`,
  `E_**(W, Y) = −2 Σ_b ⟨Y(b), Δ_b DW/dt⟩` (Milnor p. 84).

## What Milnor leaves implicit

* "It follows from §14.5 that `W₁` exists and is unique": on each segment, Remark 14.5; the
  pieces then have to be glued (here by induction over the division points), and a broken Jacobi
  field vanishing at all `t_i` vanishes (each piece is a Jacobi field vanishing at both ends of a
  short segment).
* "The proof is straightforward" (Lemma 15.4) is Lemma 15.B of the exposition
  (`Morse.formIndex_eq_restrict_of_isCompl`).
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N} {γ : ℝ → V}

/-! ### Fields along `γ|[0, τ]` -/

variable (hN γ) in
/-- **The fields along `γ|[0, τ]`** vanishing at the ends, extended by `0`: the elements of
`TΩ_γ` vanishing outside `[0, τ]`. -/
def fieldsUpTo (τ : ℝ) : Submodule ℝ (pathTangent hN γ) where
  carrier := {X | ∀ t ∉ Icc (0 : ℝ) τ, (X : ℝ → V) t = 0}
  add_mem' hX hY t ht := by simp [hX t ht, hY t ht]
  zero_mem' _ _ := rfl
  smul_mem' c X hX t ht := by simp [hX t ht]

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem fieldsUpTo_mono {τ τ' : ℝ} (h : τ ≤ τ') : fieldsUpTo hN γ τ ≤ fieldsUpTo hN γ τ' :=
  fun _ hX t ht => hX t fun h' => ht ⟨h'.1, h'.2.trans h⟩

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- A field along `γ|[0, τ]` vanishes at `τ`. -/
theorem fieldsUpTo_apply_self {τ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) {X : pathTangent hN γ}
    (hX : X ∈ fieldsUpTo hN γ τ) : (X : ℝ → V) τ = 0 := by
  rcases eq_or_lt_of_le hτ1 with rfl | hlt
  · exact X.2.2.2.2
  have hcont : ContinuousWithinAt (X : ℝ → V) (Icc 0 1) τ := X.2.1.2.1 τ ⟨hτ, hτ1⟩
  have h1 : Tendsto (X : ℝ → V) (𝓝[Ioo τ 1] τ) (𝓝 ((X : ℝ → V) τ)) :=
    (hcont.mono fun t ht => ⟨by linarith [ht.1], ht.2.le⟩).tendsto
  have h2 : Tendsto (X : ℝ → V) (𝓝[Ioo τ 1] τ) (𝓝 0) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun t ht =>
      (hX t fun h => absurd h.2 (not_le.2 ht.1)).symm)
  have : (𝓝[Ioo τ 1] τ).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo hlt.ne]
    exact ⟨le_rfl, hlt.le⟩
  exact tendsto_nhds_unique h1 h2

/-! ### Fine subdivisions -/

variable (hc : IsSmoothCurveIn hN γ)

variable (hN γ) in
/-- **A fine subdivision of `[0, τ]`** (Milnor p. 83, "sufficiently fine"): the interior division
points `B ⊆ (0, τ)` cut `[0, τ]` into pieces of length at most `h₀ = Morse.fineMesh`. -/
def IsFine (hc : IsSmoothCurveIn hN γ) (B : Finset ℝ) (τ : ℝ) : Prop :=
  (∀ b ∈ B, b ∈ Ioo 0 τ) ∧ ∀ s s', 0 ≤ s → s < s' → s' ≤ τ → (∀ b ∈ B, b ∉ Ioo s s') →
    s' - s ≤ fineMesh hN γ hc

omit [FiniteDimensional ℝ V] in
/-- Every `t ∈ [0, τ]` lies in a piece `[s, s']` between consecutive division points. -/
theorem exists_node_piece (B : Finset ℝ) {τ : ℝ} (hτ : 0 < τ) (hB : ∀ b ∈ B, b ∈ Ioo 0 τ)
    {t : ℝ} (ht : t ∈ Icc 0 τ) :
    ∃ s s', (s = 0 ∨ s ∈ B) ∧ (s' = τ ∨ s' ∈ B) ∧ s ≤ t ∧ t ≤ s' ∧ s < s' ∧
      ∀ b ∈ B, b ∉ Ioo s s' := by
  classical
  -- the last division point `< t` (or `0`)
  set L := insert (0 : ℝ) (B.filter (· < t))
  have hL : L.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  set R := insert τ (B.filter (t < ·))
  have hR : R.Nonempty := ⟨τ, Finset.mem_insert_self _ _⟩
  rcases eq_or_lt_of_le ht.2 with htτ | htτ
  · -- `t = τ`: the piece `[s, τ]`
    refine ⟨L.max' hL, τ, ?_, Or.inl rfl, ?_, htτ.le, ?_, fun b hb hbI => ?_⟩
    · rcases Finset.mem_insert.1 (L.max'_mem hL) with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_filter.1 h).1
    · obtain ⟨y, hy, hy'⟩ := L.exists_max_image id hL
      have : L.max' hL = y := le_antisymm (L.max'_le _ _ fun z hz => hy' z hz) (L.le_max' _ hy)
      rw [this]
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact ht.1
      · exact (Finset.mem_filter.1 hy).2.le
    · obtain ⟨y, hy, hy'⟩ := L.exists_max_image id hL
      have : L.max' hL = y := le_antisymm (L.max'_le _ _ fun z hz => hy' z hz) (L.le_max' _ hy)
      rw [this]
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact hτ
      · rw [← htτ]; exact (Finset.mem_filter.1 hy).2
    · have hbt : b < t := htτ ▸ hbI.2
      have : b ∈ L := Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hb, hbt⟩)
      exact absurd (L.le_max' b this) (not_le.2 hbI.1)
  · -- `t < τ`: the last division point `≤ t` and the first one `> t`
    set L' := insert (0 : ℝ) (B.filter (· ≤ t))
    have hL' : L'.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
    refine ⟨L'.max' hL', R.min' hR, ?_, ?_, ?_, ?_, ?_, fun b hb hbI => ?_⟩
    · rcases Finset.mem_insert.1 (L'.max'_mem hL') with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_filter.1 h).1
    · rcases Finset.mem_insert.1 (R.min'_mem hR) with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_filter.1 h).1
    · exact L'.max'_le _ _ fun z hz => by
        rcases Finset.mem_insert.1 hz with rfl | hz
        · exact ht.1
        · exact (Finset.mem_filter.1 hz).2
    · exact ((R.lt_min'_iff hR).2 fun z hz => by
        rcases Finset.mem_insert.1 hz with rfl | hz
        · exact htτ
        · exact (Finset.mem_filter.1 hz).2).le
    · refine lt_of_le_of_lt (b := t) (L'.max'_le _ _ fun z hz => ?_)
        ((R.lt_min'_iff hR (x := t)).2 fun z hz => ?_)
      · rcases Finset.mem_insert.1 hz with rfl | hz
        · exact ht.1
        · exact (Finset.mem_filter.1 hz).2
      · rcases Finset.mem_insert.1 hz with rfl | hz
        · exact htτ
        · exact (Finset.mem_filter.1 hz).2
    · rcases le_or_gt b t with hbt | hbt
      · have : b ∈ L' := Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hb, hbt⟩)
        exact absurd (L'.le_max' b this) (not_le.2 hbI.1)
      · have : b ∈ R := Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hb, hbt⟩)
        exact absurd (R.min'_le b this) (not_le.2 hbI.2)

include hc in
/-- **Fine subdivisions exist**, with the last division point within `h₀ / 2` of `τ`: the points
`k h₀ / 2` in `(0, τ)`. -/
theorem exists_isFine {τ : ℝ} (_hτ : 0 < τ) :
    ∃ B : Finset ℝ, IsFine hN γ hc B τ ∧ ∀ b ∈ insert 0 B, b < τ ∧
      (∀ c ∈ B, c ≤ b) → τ - b ≤ fineMesh hN γ hc / 2 := by
  classical
  set h := fineMesh hN γ hc / 2
  have hh : 0 < h := half_pos (fineMesh_pos hc)
  set K := ⌈τ / h⌉₊
  set B : Finset ℝ := ((Finset.range (K + 1)).image fun k : ℕ => (k : ℝ) * h).filter
    (· ∈ Ioo 0 τ)
  -- every interval of length `> h` in `[0, τ]` contains a grid point in `(0, τ)`
  have key : ∀ s s', 0 ≤ s → s + h < s' → s' ≤ τ → ∃ b ∈ B, b ∈ Ioo s s' := by
    intro s s' hs hss' hs'
    set k := ⌊s / h⌋₊ + 1
    have hk1 : s < (k : ℝ) * h := by
      have := Nat.lt_floor_add_one (s / h)
      push_cast [k]
      rwa [div_lt_iff₀ hh] at this
    have hk2 : (k : ℝ) * h ≤ s + h := by
      have := Nat.floor_le (div_nonneg hs hh.le)
      push_cast [k]
      have := (le_div_iff₀ hh).1 this
      linarith
    refine ⟨(k : ℝ) * h, Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨k, Finset.mem_range.2 ?_, rfl⟩,
      ⟨by linarith, by linarith⟩⟩, hk1, by linarith⟩
    have hkτ : (k : ℝ) * h < τ := by linarith
    have hkK : (k : ℝ) < K := by
      have h3 : (k : ℝ) < τ / h := by rw [lt_div_iff₀ hh]; exact hkτ
      exact h3.trans_le (Nat.le_ceil _)
    exact Nat.lt_succ_of_lt (by exact_mod_cast hkK)
  refine ⟨B, ⟨fun b hb => (Finset.mem_filter.1 hb).2, fun s s' hs hss' hs' hB => ?_⟩, ?_⟩
  · by_contra hlt
    push Not at hlt
    have hhdef : h = fineMesh hN γ hc / 2 := rfl
    obtain ⟨b, hb, hbI⟩ := key s s' hs (by linarith [fineMesh_pos hc]) hs'
    exact hB b hb hbI
  · intro b hb ⟨hbτ, hmax⟩
    by_contra hlt
    push Not at hlt
    have hb0 : 0 ≤ b := by
      rcases Finset.mem_insert.1 hb with rfl | hb
      · exact le_rfl
      · exact (Finset.mem_filter.1 hb).2.1.le
    obtain ⟨c, hc, hcI⟩ := key b τ hb0 (by linarith) le_rfl
    exact absurd (hmax c hc) (not_le.2 hcI.1)

/-! ### Broken Jacobi fields -/

variable (hN γ) in
/-- **A broken Jacobi field on `[0, τ]`** for the division points `B`: on every piece it agrees
with a Jacobi field along `γ`. -/
def IsBrokenJacobi (hc : IsSmoothCurveIn hN γ) (B : Finset ℝ) (τ : ℝ) (X : ℝ → V) : Prop :=
  ∀ s s', 0 ≤ s → s < s' → s' ≤ τ → (∀ b ∈ B, b ∉ Ioo s s') →
    ∃ J ∈ jacobiSpace hN γ hc, EqOn X J (Icc s s')

include hc in
/-- **Uniqueness of broken Jacobi fields** ("it follows from §14.5 that `W₁` is unique"): a broken
Jacobi field vanishing at `0`, `τ` and all division points vanishes on `[0, τ]`. -/
theorem IsBrokenJacobi.eqOn_zero {B : Finset ℝ} {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hB : IsFine hN γ hc B τ) {X : ℝ → V} (hX : IsBrokenJacobi hN γ hc B τ X) (h0 : X 0 = 0)
    (hτ0 : X τ = 0) (hnodes : ∀ b ∈ B, X b = 0) : EqOn X 0 (Icc 0 τ) := by
  intro t ht
  obtain ⟨s, s', hs, hs', hst, hts', hss', hpiece⟩ := exists_node_piece B hτ hB.1 ht
  have hs0 : 0 ≤ s := by rcases hs with rfl | hs; exacts [le_rfl, (hB.1 s hs).1.le]
  have hs'τ : s' ≤ τ := by rcases hs' with rfl | hs'; exacts [le_rfl, (hB.1 s' hs').2.le]
  obtain ⟨J, hJ, hXJ⟩ := hX s s' hs0 hss' hs'τ hpiece
  have hJs : J s = 0 := by
    rw [← hXJ ⟨le_rfl, hss'.le⟩]
    rcases hs with rfl | hs; exacts [h0, hnodes s hs]
  have hJs' : J s' = 0 := by
    rw [← hXJ ⟨hss'.le, le_rfl⟩]
    rcases hs' with rfl | hs'; exacts [hτ0, hnodes s' hs']
  have := eq_zero_of_short hc hJ hs0 hss' (hs'τ.trans hτ1) (hB.2 s s' hs0 hss' hs'τ hpiece) hJs hJs'
  rw [hXJ ⟨hst, hts'⟩, this]

include hc in
/-- **Existence of broken Jacobi fields** with prescribed tangent values at `0`, `τ` and the
division points ("it follows from §14.5 that `W₁` exists"): glue, segment by segment, the Jacobi
fields of `Morse.exists_jacobi_ends`. -/
theorem exists_isBrokenJacobi (B : Finset ℝ) : ∀ τ, 0 < τ → τ ≤ 1 → IsFine hN γ hc B τ →
    ∀ x : ℝ → V, (∀ t ∈ insert 0 (insert τ B), prj hN (γ t) (x t) = x t) →
    ∃ X, IsBrokenJacobi hN γ hc B τ X ∧ ∀ t ∈ insert 0 (insert τ B), X t = x t := by
  classical
  induction B using Finset.induction_on_max with
  | empty =>
    intro τ hτ hτ1 hB x hx
    obtain ⟨J, hJ, hJ0, hJτ⟩ := exists_jacobi_ends hc (a := 0) (b := τ) ⟨le_rfl, zero_le_one⟩
      ⟨hτ.le, hτ1⟩ hτ (by simpa using hB.2 0 τ le_rfl hτ le_rfl (by simp)) (hx 0 (by simp))
      (hx τ (by simp))
    refine ⟨J, fun s s' _ _ _ _ => ⟨J, hJ, fun _ _ => rfl⟩, fun t ht => ?_⟩
    simp only [insert_empty_eq, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact hJ0
    · exact hJτ
  | insert m B hmB ih =>
    intro τ hτ hτ1 hB x hx
    have hm : m ∈ Ioo 0 τ := hB.1 m (Finset.mem_insert_self _ _)
    -- `B` is a fine subdivision of `[0, m]`
    have hBm : IsFine hN γ hc B m := by
      refine ⟨fun b hb => ⟨(hB.1 b (Finset.mem_insert_of_mem hb)).1, hmB b hb⟩,
        fun s s' hs hss' hs' hpiece => hB.2 s s' hs hss' (hs'.trans hm.2.le) fun b hb => ?_⟩
      rcases Finset.mem_insert.1 hb with rfl | hb
      · exact fun h => absurd hs' (not_le.2 h.2)
      · exact hpiece b hb
    obtain ⟨X₀, hX₀, hX₀x⟩ := ih m hm.1 (hm.2.le.trans hτ1) hBm x fun t ht => by
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact hx 0 (by simp)
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact hx t (by simp)
      · exact hx t (by simp [ht])
    -- the last segment `[m, τ]`
    have hlast : τ - m ≤ fineMesh hN γ hc := hB.2 m τ hm.1.le hm.2 le_rfl fun b hb hbI => by
      rcases Finset.mem_insert.1 hb with rfl | hb
      · exact lt_irrefl _ hbI.1
      · exact absurd (hmB b hb) (not_lt.2 hbI.1.le)
    obtain ⟨J, hJ, hJm, hJτ⟩ := exists_jacobi_ends hc (a := m) (b := τ)
      ⟨hm.1.le, hm.2.le.trans hτ1⟩ ⟨hτ.le, hτ1⟩ hm.2 hlast (hx m (by simp)) (hx τ (by simp))
    have hX₀m : X₀ m = x m := hX₀x m (by simp)
    refine ⟨fun t => if t ≤ m then X₀ t else J t, fun s s' hs hss' hs' hpiece => ?_,
      fun t ht => ?_⟩
    · by_cases hs'm : s' ≤ m
      · obtain ⟨J', hJ', hX₀J'⟩ := hX₀ s s' hs hss' hs'm fun b hb => hpiece b
          (Finset.mem_insert_of_mem hb)
        exact ⟨J', hJ', fun t ht => by simp only [if_pos (ht.2.trans hs'm)]; exact hX₀J' ht⟩
      · have hms : m ≤ s := by
          by_contra h
          exact hpiece m (Finset.mem_insert_self _ _) ⟨lt_of_not_ge h, lt_of_not_ge hs'm⟩
        refine ⟨J, hJ, fun t ht => ?_⟩
        by_cases htm : t ≤ m
        · have : t = m := le_antisymm htm (hms.trans ht.1)
          simp only [if_pos htm]
          rw [this, hX₀m, hJm]
        · simp only [if_neg htm]
    · simp only [Finset.mem_insert] at ht
      rcases ht with rfl | rfl | rfl | ht
      · simp only [if_pos hm.1.le]; exact hX₀x 0 (by simp)
      · simp only [if_neg (not_le.2 hm.2)]; exact hJτ
      · simp only [if_pos le_rfl]; exact hX₀m
      · simp only [if_pos (hmB t ht).le]; exact hX₀x t (by simp [ht])

/-- **The broken Jacobi fields** `TΩ_γ(t₀, …, t_k)` along `γ|[0, τ]` (Milnor p. 83), as fields of
`TΩ_γ` vanishing outside `[0, τ]`. -/
def brokenSpace (B : Finset ℝ) (τ : ℝ) : Submodule ℝ (pathTangent hN γ) where
  carrier := {X | (∀ t ∉ Icc (0 : ℝ) τ, (X : ℝ → V) t = 0) ∧ IsBrokenJacobi hN γ hc B τ X}
  add_mem' := by
    rintro X Y ⟨hX0, hX⟩ ⟨hY0, hY⟩
    refine ⟨fun t ht => by simp [hX0 t ht, hY0 t ht], fun s s' hs hss' hs' hp => ?_⟩
    obtain ⟨J, hJ, hXJ⟩ := hX s s' hs hss' hs' hp
    obtain ⟨J', hJ', hYJ'⟩ := hY s s' hs hss' hs' hp
    exact ⟨J + J', Submodule.add_mem _ hJ hJ', fun t ht => by simp [hXJ ht, hYJ' ht]⟩
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ _ _ _ _ => ⟨0, Submodule.zero_mem _, fun _ _ => rfl⟩⟩
  smul_mem' := by
    rintro c X ⟨hX0, hX⟩
    refine ⟨fun t ht => by simp [hX0 t ht], fun s s' hs hss' hs' hp => ?_⟩
    obtain ⟨J, hJ, hXJ⟩ := hX s s' hs hss' hs' hp
    exact ⟨c • J, Submodule.smul_mem _ c hJ, fun t ht => by simp [hXJ ht]⟩

/-- **The fields vanishing at the division points**, Milnor's `T'` (p. 84), along `γ|[0, τ]`. -/
def nodeZero (B : Finset ℝ) (τ : ℝ) : Submodule ℝ (pathTangent hN γ) where
  carrier := {X | (∀ t ∉ Icc (0 : ℝ) τ, (X : ℝ → V) t = 0) ∧ ∀ b ∈ B, (X : ℝ → V) b = 0}
  add_mem' := by
    rintro X Y ⟨hX0, hX⟩ ⟨hY0, hY⟩
    exact ⟨fun t ht => by simp [hX0 t ht, hY0 t ht], fun b hb => by simp [hX b hb, hY b hb]⟩
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  smul_mem' := by
    rintro c X ⟨hX0, hX⟩
    exact ⟨fun t ht => by simp [hX0 t ht], fun b hb => by simp [hX b hb]⟩

theorem brokenSpace_le_fieldsUpTo (B : Finset ℝ) (τ : ℝ) :
    brokenSpace hc B τ ≤ fieldsUpTo hN γ τ := fun _ hX => hX.1

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem nodeZero_le_fieldsUpTo (B : Finset ℝ) (τ : ℝ) :
    nodeZero (hN := hN) (γ := γ) B τ ≤ fieldsUpTo hN γ τ := fun _ hX => hX.1

include hc in
/-- A broken Jacobi field vanishing at `0`, at `τ` and outside `[0, τ]` lies in `TΩ_γ`. -/
theorem IsBrokenJacobi.mem_pathTangent {B : Finset ℝ} {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hB : IsFine hN γ hc B τ) {X : ℝ → V} (hX : IsBrokenJacobi hN γ hc B τ X) (h0 : X 0 = 0)
    (hτ0 : X τ = 0) (hout : ∀ t ∉ Icc (0 : ℝ) τ, X t = 0) : X ∈ pathTangent hN γ := by
  classical
  have hpiece : ∀ s t, 0 ≤ s → s < t → t ≤ 1 → (∀ b ∈ insert τ B, b ∉ Ioo s t) →
      ContDiffOn ℝ ∞ X (Icc s t) := by
    intro s t hs hst ht hp
    by_cases htτ : t ≤ τ
    · obtain ⟨J, hJ, hXJ⟩ := hX s t hs hst htτ fun b hb => hp b (Finset.mem_insert_of_mem hb)
      exact (hJ.1.contDiffOn.mono (Icc_subset_Icc hs ht)).congr fun x hx => hXJ hx
    · have hτs : τ ≤ s := by
        by_contra h
        exact hp τ (Finset.mem_insert_self _ _) ⟨lt_of_not_ge h, lt_of_not_ge htτ⟩
      refine contDiffOn_const (c := (0 : V)).congr fun x hx => ?_
      rcases eq_or_lt_of_le (hτs.trans hx.1) with h | h
      · rw [← h, hτ0]
      · exact hout x fun h' => absurd h'.2 (not_le.2 h)
  refine ⟨⟨zero_le_one, continuousOn_of_piecewise (B := insert τ B) fun s t hs hst ht hp =>
      (hpiece s t hs hst ht hp).continuousOn, insert τ B, hpiece⟩, fun t ht => ?_, h0, ?_⟩
  · by_cases htτ : t ≤ τ
    · obtain ⟨s, s', hs, hss', hs', hts, hp⟩ := exists_piece_mem B hτ ⟨ht.1, htτ⟩
      obtain ⟨J, hJ, hXJ⟩ := hX s s' hs hss' hs' hp
      rw [hXJ hts]
      exact hJ.1.tangent t ht
    · rw [hout t fun h => htτ h.2, map_zero]
  · rcases eq_or_lt_of_le hτ1 with rfl | h
    · exact hτ0
    · exact hout 1 fun h' => absurd h'.2 (not_le.2 h)

include hc in
/-- A broken Jacobi field agrees near every point of `(0, 1)` other than `τ` and the division
points with a Jacobi field (with `0` beyond `τ`). -/
theorem IsBrokenJacobi.eventuallyEq {B : Finset ℝ} {τ : ℝ} (_hτ : 0 < τ)
    (_hB : ∀ b ∈ B, b ∈ Ioo 0 τ) {X : ℝ → V} (hX : IsBrokenJacobi hN γ hc B τ X)
    (hout : ∀ t ∉ Icc (0 : ℝ) τ, X t = 0) :
    ∀ t ∈ Ioo (0 : ℝ) 1, t ∉ insert τ B → ∃ J, IsJacobiField hN γ J ∧ X =ᶠ[𝓝 t] J := by
  classical
  intro t ht htB
  have htτ : t ≠ τ := fun h => htB (h ▸ Finset.mem_insert_self _ _)
  have htB' : t ∉ B := fun h => htB (Finset.mem_insert_of_mem h)
  rcases lt_or_gt_of_ne htτ with h | h
  · obtain ⟨s, s', hs, hst, hts', hs', hp⟩ := exists_piece_around B ht.1 h htB'
    obtain ⟨J, hJ, hXJ⟩ := hX s s' hs (hst.trans hts') hs' hp
    exact ⟨J, hJ.1, eventually_of_mem (Icc_mem_nhds hst hts') hXJ⟩
  · refine ⟨0, isJacobiField_zero, ?_⟩
    filter_upwards [Ioi_mem_nhds h] with x hx
    exact hout x fun h' => absurd h'.2 (not_le.2 hx)

/-! ### The second variation formula on broken Jacobi fields -/

include hc in
/-- **The Hessian on broken Jacobi fields** (Milnor p. 84): for a broken Jacobi field `X` along
`γ|[0, τ]` and `Y` vanishing outside `[0, τ]`,
`E_**(X, Y) = −2 Σ_{b ∈ B} ⟨Y(b), Δ_b DX/dt⟩`. -/
theorem energyHessian_broken_eq {B : Finset ℝ} {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hB : IsFine hN γ hc B τ) {X Y : pathTangent hN γ} (hX : X ∈ brokenSpace hc B τ)
    (hY : Y ∈ fieldsUpTo hN γ τ) :
    energyHessian hN hc.mem_pathSpace X Y =
      -2 * ∑ b ∈ B, ⟪(Y : ℝ → V) b, prj hN (γ b) (jump X b)⟫ := by
  classical
  have hYτ : (Y : ℝ → V) τ = 0 := fieldsUpTo_apply_self hτ.le hτ1 hY
  rw [energyHessian_eq_jumps hc.mem_pathSpace X Y (hX.2.eventuallyEq hc hτ hB.1 hX.1)]
  congr 1
  have hBF : B ⊆ (insert τ B).filter (· ∈ Ioo (0 : ℝ) 1) := fun b hb =>
    Finset.mem_filter.2 ⟨Finset.mem_insert_of_mem hb, ⟨(hB.1 b hb).1, (hB.1 b hb).2.trans_le hτ1⟩⟩
  refine (Finset.sum_subset hBF fun x hx hx' => ?_).symm
  rcases Finset.mem_insert.1 (Finset.mem_filter.1 hx).1 with rfl | hx''
  · rw [hYτ, inner_zero_left]
  · exact absurd hx'' hx'

/-! ### Lemma 15.3 -/

include hc in
/-- **Lemma 15.3, perpendicularity** (Milnor p. 84). -/
theorem energyHessian_broken_nodeZero {B : Finset ℝ} {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hB : IsFine hN γ hc B τ) {X Y : pathTangent hN γ} (hX : X ∈ brokenSpace hc B τ)
    (hY : Y ∈ nodeZero B τ) : energyHessian hN hc.mem_pathSpace X Y = 0 := by
  rw [energyHessian_broken_eq hc hτ hτ1 hB hX (nodeZero_le_fieldsUpTo B τ hY)]
  rw [Finset.sum_eq_zero fun b hb => by rw [hY.2 b hb, inner_zero_left], mul_zero]

include hc in
/-- **Lemma 15.3, positivity** (Milnor pp. 84–85): `E_**` is positive definite on `T'`. -/
theorem energyHessian_nodeZero_pos {B : Finset ℝ} {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hB : IsFine hN γ hc B τ) {Y : pathTangent hN γ} (hY : Y ∈ nodeZero B τ) (hY0 : Y ≠ 0) :
    0 < energyHessian hN hc.mem_pathSpace Y Y := by
  by_contra hle
  push Not at hle
  apply hY0
  have hzero : ∀ t ∈ Icc (0 : ℝ) 1, ∃ s ∈ Icc 0 t, t - s ≤ fineMesh hN γ hc ∧
      (Y : ℝ → V) s = 0 := by
    intro t ht
    by_cases htτ : t ≤ τ
    · obtain ⟨s, s', hs, hs', hst, hts', hss', hp⟩ := exists_node_piece B hτ hB.1 ⟨ht.1, htτ⟩
      have hs0 : 0 ≤ s := by rcases hs with rfl | hs; exacts [le_rfl, (hB.1 s hs).1.le]
      have hs'τ : s' ≤ τ := by rcases hs' with rfl | hs'; exacts [le_rfl, (hB.1 s' hs').2.le]
      refine ⟨s, ⟨hs0, hst⟩, ?_, ?_⟩
      · have := hB.2 s s' hs0 hss' hs'τ hp
        linarith
      · rcases hs with rfl | hs
        · exact Y.2.2.2.1
        · exact hY.2 s hs
    · exact ⟨t, ⟨ht.1, le_rfl⟩, by rw [sub_self]; exact (fineMesh_pos hc).le,
        hY.1 t fun h => htτ h.2⟩
  have h0 : hessForm hN γ Y Y ≤ 0 := by
    rw [energyHessian_apply, secondVariation_eq_hessForm hN hc.mem_pathSpace Y.2 Y.2] at hle
    linarith
  have hY0 := eqOn_zero_of_hessForm hc hc.mem_pathSpace Y.2 hzero h0
  ext t
  by_cases ht : t ∈ Icc (0 : ℝ) τ
  · exact hY0 ⟨ht.1, ht.2.trans hτ1⟩
  · exact hY.1 t ht

end Morse
