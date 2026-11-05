import Morse.Chapter9.IndexAssertions

/-!
Milnor, *Morse Theory*, §15, pp. 83–87: **Theorem 15.1 (the Morse index theorem)** and
Corollary 15.2, for a submanifold `N ⊆ ℝᴷ` with the induced metric.

# The Morse index theorem

## Milnor's text, paraphrased

**Theorem 15.1** (Morse, p. 83): the index `λ` of `E_** : TΩ_γ × TΩ_γ → ℝ` (the maximum dimension
of a subspace of `TΩ_γ` on which `E_**` is negative definite) is equal to the number of points
`γ(t)`, `0 < t < 1`, such that `γ(t)` is conjugate to `γ(0)` along `γ`, each counted with its
multiplicity.  The index `λ` is always finite.  **Corollary 15.2**: a geodesic segment
`γ : [0, 1] → M` contains only finitely many points conjugate to `γ(0)` along `γ`.  (p. 87) "The
index theorem 15.1 clearly follows from the Assertions (2), (3), and (4)."

## In the embedded setting

* `Morse.theorem_15_1`: for a geodesic `γ ∈ Ω(N; p, q)`, the parameters `t ∈ (0, 1)` conjugate
  to `0` form a finite set, and `formIndex (energyHessian hN hγ)` (Milnor's `λ`, a priori in `ℕ∞`)
  equals `Σ_{0 < t < 1} conjMultiplicity 0 t`, the number of conjugate points counted with
  multiplicity (a `finsum`: the multiplicity is `0` off the conjugate points).
* `Morse.corollary_15_2`, `Morse.remark_14_6` (no conjugate points near `t = 0`).
* `Morse.eq_finsum_of_jumps`: the deduction of the theorem from the Assertions, as a statement
  about functions `λ, ν : ℝ → ℕ`.

## What Milnor leaves implicit

"Clearly follows" hides an argument with two steps.  **Finiteness first**: if
`τ₁ < ⋯ < τ_m` are conjugate in `(0, 1)`, Assertions (4) and (1) give
`λ(1) ≥ ν(τ₁) + ⋯ + ν(τ_m) ≥ m`; as `λ(1)` is finite (Lemma 15.4) there are finitely many conjugate
points.  **Then the sum**: `λ(τ) − Σ_{t < τ} ν(t)` is locally constant on `(0, 1]` (Assertions (3)
and (4)), hence constant, and it vanishes for small `τ` (Assertion (2), and Assertion (4) shows
that there are no conjugate points there either).  Without finiteness, the jumps could not be
added up.

Assertion (2) and the two properties of a fine subdivision are obtained here from the analytic
estimate `Morse.hessForm_ge` rather than from minimal geodesics (see
`Morse/Chapter9/IndexForm.lean`); otherwise the proof is Milnor's.  The geodesic hypothesis is used
by Milnor's statement (the Hessian of the energy at a critical point); the proof itself only uses
the index form `E_**` given by Proposition 13.A along the smooth curve `γ`.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

/-! ### From the Assertions to the theorem -/

/-- **The index theorem from the Assertions** (Milnor p. 87, "clearly follows"): let
`λ, ν : ℝ → ℕ` with `λ` monotone on `(0, 1]` (Assertion (1)), `0` on `(0, h₀]` (Assertion (2)),
continuous from the left (Assertion (3)), and jumping by `ν(τ)` just after `τ` (Assertion (4)).
Then `ν` is nonzero at finitely many points of `(0, 1)` and `λ(1) = Σ_{0 < t < 1} ν(t)`. -/
theorem eq_finsum_of_jumps {ℓ ν : ℝ → ℕ} {h₀ : ℝ} (hh₀ : 0 < h₀)
    (hmono : ∀ τ τ', 0 < τ → τ ≤ τ' → τ' ≤ 1 → ℓ τ ≤ ℓ τ')
    (hsmall : ∀ τ, 0 < τ → τ ≤ h₀ → ℓ τ = 0)
    (hleft : ∀ τ, 0 < τ → τ ≤ 1 → ∀ᶠ τ' in 𝓝[<] τ, ℓ τ' = ℓ τ)
    (hright : ∀ τ, 0 < τ → τ < 1 → ∀ᶠ τ' in 𝓝[>] τ, ℓ τ' = ℓ τ + ν τ) :
    {t | t ∈ Ioo (0 : ℝ) 1 ∧ ν t ≠ 0}.Finite ∧ ℓ 1 = ∑ᶠ t ∈ Ioo (0 : ℝ) 1, ν t := by
  classical
  -- the jumps before `τ` add up to at most `λ(τ)`
  have hbound : ∀ F : Finset ℝ, (∀ t ∈ F, t ∈ Ioo (0 : ℝ) 1) → ∀ τ, 0 < τ → τ ≤ 1 →
      (∀ t ∈ F, t < τ) → ∑ t ∈ F, ν t ≤ ℓ τ := by
    intro F
    induction F using Finset.induction_on_max with
    | empty => intros; simp
    | insert a F haF ih =>
      intro hF τ hτ hτ1 hlt
      have ha := hF a (Finset.mem_insert_self _ _)
      have haτ : a < τ := hlt a (Finset.mem_insert_self _ _)
      rw [Finset.sum_insert (fun h => lt_irrefl a (haF a h))]
      have h1 := ih (fun t ht => hF t (Finset.mem_insert_of_mem ht)) a ha.1 ha.2.le haF
      obtain ⟨τ', hτ'eq, hτ'mem⟩ := ((hright a ha.1 ha.2).and (Ioo_mem_nhdsGT haτ)).exists
      have h2 := hmono τ' τ (ha.1.trans hτ'mem.1) hτ'mem.2.le hτ1
      omega
  -- finiteness
  set C := {t | t ∈ Ioo (0 : ℝ) 1 ∧ ν t ≠ 0}
  have hC : C.Finite := by
    by_contra hinf
    obtain ⟨F, hFC, hFcard⟩ := Set.Infinite.exists_subset_card_eq hinf (ℓ 1 + 1)
    have h1 := hbound F (fun t ht => (hFC ht).1) 1 one_pos le_rfl fun t ht => (hFC ht).1.2
    have h2 : F.card ≤ ∑ t ∈ F, ν t := by
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum fun t ht => Nat.one_le_iff_ne_zero.2 (hFC ht).2
    omega
  set Cf := hC.toFinset
  have hCf : ∀ t, t ∈ Cf ↔ t ∈ Ioo (0 : ℝ) 1 ∧ ν t ≠ 0 := fun t => by simp [Cf, C]
  -- no jumps before `h₀`
  have hnone : ∀ t, 0 < t → t < min h₀ 1 → ν t = 0 := by
    intro t ht htm
    have ht1 : t < 1 := htm.trans_le (min_le_right _ _)
    have hth : t < h₀ := htm.trans_le (min_le_left _ _)
    obtain ⟨τ', hτ'eq, hτ'mem⟩ := ((hright t ht ht1).and (Ioo_mem_nhdsGT hth)).exists
    have h1 := hsmall τ' (ht.trans hτ'mem.1) hτ'mem.2.le
    have h2 := hsmall t ht hth.le
    omega
  -- `g(τ) = λ(τ) − Σ_{t < τ} ν(t)` is locally constant on `(0, 1]`
  set g : ℝ → ℤ := fun τ => (ℓ τ : ℤ) - ∑ t ∈ Cf with t < τ, (ν t : ℤ)
  have hleft' : ∀ τ, 0 < τ → τ ≤ 1 → ∀ᶠ τ' in 𝓝[<] τ, g τ' = g τ := by
    intro τ hτ hτ1
    have hall : ∀ᶠ τ' in 𝓝[<] τ, ∀ t ∈ Cf, (t < τ' ↔ t < τ) := by
      rw [Filter.eventually_all_finset]
      intro t _
      rcases lt_or_ge t τ with h | h
      · filter_upwards [Ioo_mem_nhdsLT h] with τ' hτ'
        exact ⟨fun _ => h, fun _ => hτ'.1⟩
      · filter_upwards [self_mem_nhdsWithin] with τ' hτ'
        exact ⟨fun h' => absurd (h'.trans hτ') (not_lt.2 h), fun h' => absurd h' (not_lt.2 h)⟩
    filter_upwards [hleft τ hτ hτ1, hall] with τ' h1 h2
    simp only [g, h1]
    congr 1
    exact Finset.sum_congr (Finset.filter_congr fun t ht => h2 t ht) fun _ _ => rfl
  have hright' : ∀ τ, 0 < τ → τ < 1 → ∀ᶠ τ' in 𝓝[>] τ, g τ' = g τ := by
    intro τ hτ hτ1
    have hall : ∀ᶠ τ' in 𝓝[>] τ, ∀ t ∈ Cf, (t < τ' ↔ t ≤ τ) := by
      rw [Filter.eventually_all_finset]
      intro t _
      rcases le_or_gt t τ with h | h
      · filter_upwards [self_mem_nhdsWithin] with τ' hτ'
        exact ⟨fun _ => h, fun _ => lt_of_le_of_lt h hτ'⟩
      · filter_upwards [Ioo_mem_nhdsGT h] with τ' hτ'
        exact ⟨fun h' => absurd (h'.trans hτ'.2) (lt_irrefl _), fun h' => absurd h' (not_le.2 h)⟩
    filter_upwards [hright τ hτ hτ1, hall] with τ' h1 h2
    have hsplit : ∑ t ∈ Cf with t < τ', (ν t : ℤ) =
        ∑ t ∈ Cf with t < τ, (ν t : ℤ) + (ν τ : ℤ) := by
      rw [Finset.filter_congr fun t ht => h2 t ht]
      by_cases hτC : τ ∈ Cf
      · have : Cf.filter (· ≤ τ) = insert τ (Cf.filter (· < τ)) := by
          ext t
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨ht, htτ⟩
            rcases eq_or_lt_of_le htτ with rfl | h
            · exact Or.inl rfl
            · exact Or.inr ⟨ht, h⟩
          · rintro (rfl | ⟨ht, h⟩)
            · exact ⟨hτC, le_rfl⟩
            · exact ⟨ht, h.le⟩
        rw [this, Finset.sum_insert (by simp), add_comm]
      · have hν : ν τ = 0 := by
          by_contra h
          exact hτC ((hCf τ).2 ⟨⟨hτ, hτ1⟩, h⟩)
        have : Cf.filter (· ≤ τ) = Cf.filter (· < τ) := Finset.filter_congr fun t ht =>
          ⟨fun h => lt_of_le_of_ne h fun h' => hτC (h' ▸ ht), le_of_lt⟩
        rw [this, hν]
        simp
    simp only [g, h1, hsplit]
    push_cast
    ring
  have hcont : ContinuousOn g (Ioc 0 1) := by
    intro τ hτ
    refine tendsto_nhds_of_eventually_eq ?_
    rw [eventually_nhdsWithin_iff]
    obtain ⟨l, hl, hlsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 (hleft' τ hτ.1 hτ.2)
    have hu : ∃ u > τ, ∀ τ' ∈ Ioo τ u, τ' ∈ Ioc (0 : ℝ) 1 → g τ' = g τ := by
      rcases eq_or_lt_of_le hτ.2 with h1 | h1
      · exact ⟨2, by linarith, fun τ' hτ' hτ'I => absurd hτ'I.2 (by linarith [hτ'.1])⟩
      · obtain ⟨u, hu, husub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hright' τ hτ.1 h1)
        exact ⟨u, hu, fun τ' hτ' _ => husub hτ'⟩
    obtain ⟨u, hu, husub⟩ := hu
    filter_upwards [Ioo_mem_nhds hl hu] with τ' hτ' hτ'I
    rcases lt_trichotomy τ' τ with h | rfl | h
    · exact hlsub ⟨hτ'.1, h⟩
    · rfl
    · exact husub τ' ⟨h, hτ'.2⟩ hτ'I
  -- `g` vanishes near `0`, hence on `(0, 1]`
  set τ₁ := min h₀ 1 / 2
  have hτ₁ : τ₁ ∈ Ioc (0 : ℝ) 1 := ⟨by positivity, by
    have := min_le_right h₀ 1; simp only [τ₁]; linarith⟩
  have hgτ₁ : g τ₁ = 0 := by
    have h1 : ℓ τ₁ = 0 := hsmall τ₁ hτ₁.1 (by
      have := min_le_left h₀ 1; have := lt_min hh₀ one_pos; simp only [τ₁]; linarith)
    have h2 : Cf.filter (· < τ₁) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro t ht htτ
      have := (hCf t).1 ht
      exact this.2 (hnone t this.1.1 (htτ.trans (half_lt_self (lt_min hh₀ one_pos))))
    simp [g, h1, h2]
  have hg1 : g 1 = 0 := by
    rw [← hgτ₁]
    exact isPreconnected_Ioc.constant hcont ⟨one_pos, le_rfl⟩ hτ₁
  refine ⟨hC, ?_⟩
  have hsum1 : Cf.filter (· < (1 : ℝ)) = Cf :=
    Finset.filter_true_of_mem fun t ht => ((hCf t).1 ht).1.2
  have hfin : ∑ᶠ t ∈ Ioo (0 : ℝ) 1, ν t = ∑ t ∈ Cf, ν t := by
    refine finsum_mem_eq_sum_of_inter_support_eq _ ?_
    ext t
    simp only [mem_inter_iff, mem_support, Finset.mem_coe, hCf]
    tauto
  simp only [g, hsum1] at hg1
  rw [hfin]
  have : (ℓ 1 : ℤ) = ∑ t ∈ Cf, (ν t : ℤ) := by linarith
  exact_mod_cast this

/-! ### Theorem 15.1 -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N} {γ : ℝ → V}

/-- `λ(τ)` as a natural number. -/
theorem indexUpTo_toNat (hc : IsSmoothCurveIn hN γ) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ((indexUpTo hN γ hc τ).toNat : ℕ∞) = indexUpTo hN γ hc τ :=
  ENat.natCast_toNat (indexUpTo_lt_top hc hτ hτ1).ne

/-- **Theorem 15.1, along any smooth curve**: the parameters `t ∈ (0, 1)` conjugate to `0` are
finitely many, and `λ(1) = Σ_{0 < t < 1} ν(t)`. -/
theorem indexUpTo_one_eq (hc : IsSmoothCurveIn hN γ) :
    {t | t ∈ Ioo (0 : ℝ) 1 ∧ conjMultiplicity hN γ hc 0 t ≠ 0}.Finite ∧
      indexUpTo hN γ hc 1 = ((∑ᶠ t ∈ Ioo (0 : ℝ) 1, conjMultiplicity hN γ hc 0 t : ℕ) : ℕ∞) := by
  set ℓ : ℝ → ℕ := fun τ => (indexUpTo hN γ hc τ).toNat
  have hℓ : ∀ τ, 0 < τ → τ ≤ 1 → (ℓ τ : ℕ∞) = indexUpTo hN γ hc τ := fun τ hτ hτ1 =>
    indexUpTo_toNat hc hτ hτ1
  have key := eq_finsum_of_jumps (ℓ := ℓ) (ν := fun t => conjMultiplicity hN γ hc 0 t)
    (fineMesh_pos hc)
    (fun τ τ' hτ hττ' hτ'1 => by
      have := indexUpTo_mono hc hττ'
      rw [← hℓ τ hτ (hττ'.trans hτ'1), ← hℓ τ' (hτ.trans_le hττ') hτ'1] at this
      exact_mod_cast this)
    (fun τ hτ hτh => by simp [ℓ, indexUpTo_eq_zero hc hτ hτh])
    (fun τ hτ hτ1 => by
      filter_upwards [assertion_3 hc hτ hτ1] with τ' h
      simp [ℓ, h])
    (fun τ hτ hτ1 => by
      filter_upwards [assertion_4 hc hτ hτ1, Ioo_mem_nhdsGT hτ1] with τ' h hτ'
      have h' : ((ℓ τ' : ℕ) : ℕ∞) = ((ℓ τ + conjMultiplicity hN γ hc 0 τ : ℕ) : ℕ∞) := by
        rw [hℓ τ' (hτ.trans hτ'.1) hτ'.2.le, h, Nat.cast_add, hℓ τ hτ hτ1.le]
      exact_mod_cast h')
  refine ⟨key.1, ?_⟩
  rw [← hℓ 1 one_pos le_rfl, key.2]

variable (hN) in
/-- **Theorem 15.1 (Morse; Milnor p. 83)**: let `γ ∈ Ω(N; p, q)` be a geodesic.  The index `λ`
of the Hessian `E_**` of the energy at `γ` (the supremum of the dimensions of the subspaces of
`TΩ_γ` on which `E_**` is negative definite) is equal to the number of parameters `t ∈ (0, 1)`
such that `γ(t)` is conjugate to `γ(0)` along `γ`, each counted with its multiplicity; there are
finitely many such `t`, and the index is finite. -/
theorem theorem_15_1 {p q : V} (hγ : γ ∈ pathSpace N p q) (hgeo : IsUnbrokenGeodesic hN γ) :
    {t | t ∈ Ioo (0 : ℝ) 1 ∧ IsConjugate hN γ 0 t}.Finite ∧
      formIndex (energyHessian hN hγ) =
        ((∑ᶠ t ∈ Ioo (0 : ℝ) 1,
          conjMultiplicity hN γ (hgeo.isSmoothCurveIn hN hγ) 0 t : ℕ) : ℕ∞) := by
  set hc := hgeo.isSmoothCurveIn hN hγ
  obtain ⟨hfin, heq⟩ := indexUpTo_one_eq hc
  have hset : {t | t ∈ Ioo (0 : ℝ) 1 ∧ IsConjugate hN γ 0 t} =
      {t | t ∈ Ioo (0 : ℝ) 1 ∧ conjMultiplicity hN γ hc 0 t ≠ 0} := by
    ext t
    simp only [mem_ofPred_eq, isConjugate_iff hc]
    constructor
    · rintro ⟨ht, -, -, -, h⟩
      exact ⟨ht, h.ne'⟩
    · rintro ⟨ht, h⟩
      exact ⟨ht, ⟨le_rfl, zero_le_one⟩, Ioo_subset_Icc_self ht, ht.1.ne,
        Nat.pos_of_ne_zero h⟩
  refine ⟨hset ▸ hfin, ?_⟩
  have hE : energyHessian hN hγ = energyHessian hN hc.mem_pathSpace := rfl
  rw [hE, ← indexUpTo_one hc, heq]

variable (hN) in
/-- **Corollary 15.2** (Milnor p. 83): a geodesic segment `γ : [0, 1] → N` contains only finitely
many points conjugate to `γ(0)` along `γ` (as parameter values). -/
theorem corollary_15_2 {p q : V} (hγ : γ ∈ pathSpace N p q) (hgeo : IsUnbrokenGeodesic hN γ) :
    {t | IsConjugate hN γ 0 t}.Finite := by
  refine ((theorem_15_1 hN hγ hgeo).1.union (finite_singleton (1 : ℝ))).subset fun t ht => ?_
  obtain ⟨-, ht1, ht0, -⟩ := id ht
  rcases eq_or_lt_of_le ht1.2 with h | h
  · exact Or.inr h
  · exact Or.inl ⟨⟨lt_of_le_of_ne ht1.1 ht0, h⟩, ht⟩

/-- **Remark 14.6** (Milnor p. 82): there is `δ > 0` such that no `t ∈ (0, δ)` is conjugate to
`0` along `γ` (along any smooth curve). -/
theorem remark_14_6 (hc : IsSmoothCurveIn hN γ) :
    ∃ δ > 0, ∀ t, 0 < t → t < δ → ¬ IsConjugate hN γ 0 t := by
  refine ⟨min (fineMesh hN γ hc) 1, lt_min (fineMesh_pos hc) one_pos, fun t ht htδ hconj => ?_⟩
  obtain ⟨-, ht01, -, hpos⟩ := (isConjugate_iff hc).1 hconj
  obtain ⟨⟨J, hJ⟩, hJ0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
  obtain ⟨hJs, hJa, hJb⟩ := (mem_conjSpace hc).1 hJ
  exact hJ0 (Subtype.ext (eq_zero_of_short hc hJs le_rfl ht ht01.2
    (by have := min_le_left (fineMesh hN γ hc) 1; linarith) hJa hJb))

end Morse
