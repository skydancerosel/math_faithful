import Morse.Chapter7.Shortest

/-!
Milnor, *Morse Theory*, §10, pp. 61–62 (Corollary 10.7), for a submanifold `N ⊆ ℝᴷ` with the
induced metric.

# Shortest paths are geodesics

## Milnor's text, paraphrased

**Corollary 10.7** (p. 61).  Suppose that a path `ω : [0, ℓ] → M`, parametrized by arc length, has
length less than or equal to the length of any other path from `ω(0)` to `ω(ℓ)`.  Then `ω` is a
geodesic.  Proof: a segment of `ω` lying in an open set `W` as in Lemma 10.3, of length `< ε`, is a
geodesic by Theorem 10.4; hence so is `ω`.

**Definition** (p. 61): a geodesic `γ : [a, b] → M` is *minimal* if its length is less than or equal
to the length of any other piecewise smooth path joining its endpoints.

## In the embedded setting

* `Morse.isGeodesicOn_of_locally`: being a geodesic is a local property.
* `Morse.minimal_segment`: a segment of such a path inside a uniformly normal neighbourhood `W` of
  Lemma 10.3 is the geodesic of Lemma 10.3 joining its endpoints.
* `Morse.corollary_10_7`: a piecewise smooth path `c : [0, ℓ] → N` with `‖c'‖ = 1` wherever `c` is
  differentiable, whose length is at most that of every piecewise smooth path in `N` with the same
  endpoints, is a geodesic on `(0, ℓ)`; `Morse.corollary_10_7_extend`: it is the restriction to
  `[0, ℓ]` of a geodesic on an open interval `(-δ, ℓ + δ)`.

## What Milnor leaves implicit

* **Equal images are not enough.**  Theorem 10.4 as stated only says that the segment and the
  geodesic `γ` have the same image; a path running along `γ` at variable speed has the same image
  without being a geodesic.  The proof needs the sharp equality case
  (`Morse.NormalCoord.eq_exp_of_pathLength_eq`: the segment is `γ ∘ ρ` with
  `ρ(t) = L(ω|[α, t])/L(γ)`) together with the parametrization by arc length, which forces `ρ` to be
  affine.
* **Minimality of segments.**  That a segment `ω|[α, β]` is itself not longer than the geodesic of
  Lemma 10.3 joining its endpoints uses the minimality of `ω` with the competitor obtained by
  replacing the segment by the geodesic (a piecewise smooth path: concatenation,
  `Morse.IsPiecewiseSmooth.concat`).
* **Break points.**  The segments must be chosen with the points of `(0, ℓ)` (in particular the
  break points of `ω`) in their interiors, so that `ω` is smooth and satisfies the geodesic
  equation near every point; "the entire path `ω` is a geodesic" is the locality
  `Morse.isGeodesicOn_of_locally`.
-/

open Set Filter Topology Function Module Metric MeasureTheory
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **Being a geodesic is a local property.** -/
theorem isGeodesicOn_of_locally {γ : ℝ → V} {s : Set ℝ} (hs : IsOpen s)
    (h : ∀ t ∈ s, ∃ s' : Set ℝ, t ∈ s' ∧ s' ⊆ s ∧ IsGeodesicOn hN γ s') :
    IsGeodesicOn hN γ s := by
  choose s' hts' hs's hgeo using h
  refine ⟨hs, fun t ht => (hgeo t ht).mem t (hts' t ht), ?_, fun t ht => ?_⟩
  · refine contDiffOn_of_locally_contDiffOn fun t ht => ⟨s' t ht, (hgeo t ht).isOpen,
      hts' t ht, ?_⟩
    exact (hgeo t ht).contDiffOn.mono inter_subset_right
  · exact (hgeo t ht).normal t (hts' t ht)

/-- **The segment lemma** behind Corollary 10.7.  Let `c : [0, ℓ] → N` be piecewise smooth,
parametrized by arc length and minimal among piecewise smooth paths with the same endpoints, and let
`[α, β] ⊆ [0, ℓ]` be mapped by `c` into the set `W = N ∩ O` of Lemma 10.3 (with its items (1) and
(3)).  Then on `[α, β]`, `c` is the geodesic `t ↦ exp_{c(α)}(((t − α)/(β − α)) v)` of Lemma 10.3
joining `c(α)` to `c(β)`, which is defined on an open interval containing `[α, β]`. -/
theorem minimal_segment {c : ℝ → V} {ℓ : ℝ} (hc : IsPiecewiseSmooth c 0 ℓ)
    (hcN : ∀ t ∈ Icc 0 ℓ, c t ∈ N)
    (hunit : ∀ t ∈ Ioo 0 ℓ, DifferentiableAt ℝ c t → ‖deriv c t‖ = 1)
    (hmin : ∀ (c' : ℝ → V) (a b : ℝ), IsPiecewiseSmooth c' a b → (∀ t ∈ Icc a b, c' t ∈ N) →
      c' a = c 0 → c' b = c ℓ → pathLength c 0 ℓ ≤ pathLength c' a b)
    {O : Set V} {ε : ℝ}
    (h1 : ∀ q₁ q₂ : N, (q₁ : V) ∈ O → (q₂ : V) ∈ O →
      ∃! v, v ∈ tangentSubspace hN q₁ ∧ ‖v‖ < ε ∧ exp hN q₁ v = q₂)
    (h3 : ∀ q : N, (q : V) ∈ O → IsNormalRadius hN q ε)
    {α β : ℝ} (hα0 : 0 ≤ α) (hαβ : α < β) (hβℓ : β ≤ ℓ) (hinO : ∀ t ∈ Icc α β, c t ∈ O) :
    ∃ s : Set ℝ, Icc α β ⊆ s ∧ ∃ γ : ℝ → V, IsGeodesicOn hN γ s ∧ EqOn γ c (Icc α β) := by
  have hca := hc.isAdmissible
  -- arc length
  have harc : ∀ s t, 0 ≤ s → s ≤ t → t ≤ ℓ → pathLength c s t = t - s := by
    intro s t hs hst ht
    rw [pathLength_eq_of_norm_deriv (hca.mono hs hst ht) fun x hx hd =>
      hunit x ⟨hs.trans_lt hx.1, hx.2.trans_le ht⟩ hd, one_mul]
  have hαN := hcN α ⟨hα0, by linarith⟩
  have hβN := hcN β ⟨by linarith, hβℓ⟩
  set q₁ : N := ⟨c α, hαN⟩
  set q₂ : N := ⟨c β, hβN⟩
  obtain ⟨v, ⟨hv, hvε, hexp⟩, -⟩ := h1 q₁ q₂ (hinO α ⟨le_rfl, hαβ.le⟩) (hinO β ⟨hαβ.le, le_rfl⟩)
  obtain ⟨nc⟩ := h3 q₁ (hinO α ⟨le_rfl, hαβ.le⟩)
  -- the geodesic segment `γ̃(t) = exp_{q₁}(((t − α)/(β − α)) v)`
  obtain ⟨δ, hδ, hgeo, hd0⟩ := nc.radial hv hvε
  set k := (β - α)⁻¹ with hk_def
  have hk : 0 < k := inv_pos.2 (by linarith)
  have hne : β - α ≠ 0 := sub_ne_zero.2 hαβ.ne'
  set γ : ℝ → V := fun t => exp hN q₁ ((k * t + -k * α) • v) with hγ_def
  have hγgeo : IsGeodesicOn hN γ ((fun t => k * t + -k * α) ⁻¹' Ioo (-δ) (1 + δ)) :=
    hgeo.comp_mul_add k (-k * α)
  have hτ : ∀ t ∈ Icc α β, k * t + -k * α ∈ Icc (0 : ℝ) 1 := by
    intro t ht
    have h1 : k * t + -k * α = (t - α) / (β - α) := by rw [hk_def, div_eq_inv_mul]; ring
    rw [h1]
    exact ⟨div_nonneg (by linarith [ht.1]) (by linarith),
      (div_le_one (by linarith)).2 (by linarith [ht.2])⟩
  have hsub : Icc α β ⊆ (fun t => k * t + -k * α) ⁻¹' Ioo (-δ) (1 + δ) := fun t ht =>
    ⟨by linarith [(hτ t ht).1], by linarith [(hτ t ht).2]⟩
  have hconv : Convex ℝ ((fun t => k * t + -k * α) ⁻¹' Ioo (-δ) (1 + δ)) := by
    intro x hx y hy a b ha hb hab
    have := convex_Ioo (-δ) (1 + δ) hx hy ha hb hab
    simp only [mem_preimage, smul_eq_mul] at this ⊢
    convert this using 1
    calc k * (a * x + b * y) + -k * α = k * (a * x + b * y) + -k * α * (a + b) := by
          rw [hab, mul_one]
      _ = a * (k * x + -k * α) + b * (k * y + -k * α) := by ring
  have hγα : γ α = c α := by
    simp only [hγ_def, show k * α + -k * α = 0 by ring, zero_smul, exp_zero q₁.2]
    rfl
  have hγβ : γ β = c β := by
    have h1 : k * β + -k * α = 1 := by
      rw [show k * β + -k * α = k * (β - α) by ring, hk_def, inv_mul_cancel₀ hne]
    simp only [hγ_def, h1, one_smul, hexp]
    rfl
  have hγN : ∀ t ∈ Icc α β, γ t ∈ N := by
    intro t ht
    have hτt := hτ t ht
    refine nc.exp_mem (Submodule.smul_mem _ _ hv) ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτt.1]
    calc (k * t + -k * α) * ‖v‖ ≤ 1 * ‖v‖ := by gcongr; exact hτt.2
      _ < ε := by linarith
  -- its length is `‖v‖`
  have hγlen : pathLength γ α β = ‖v‖ := by
    have hαm : α ∈ (fun t => k * t + -k * α) ⁻¹' Ioo (-δ) (1 + δ) := hsub ⟨le_rfl, hαβ.le⟩
    rw [hγgeo.pathLength_eq hconv.isPreconnected hαβ.le hsub hαm]
    have hd : HasDerivAt γ (k • v) α := by
      have h1 : HasDerivAt (fun t : ℝ => k * t + -k * α) k α := by
        simpa using ((hasDerivAt_id α).const_mul k).add_const (-k * α)
      have h2 := hgeo.hasDerivAt (t := 0) ⟨by linarith, by linarith⟩
      rw [hd0] at h2
      have h2' : HasDerivAt (fun t : ℝ => exp hN q₁ (t • v)) v (k * α + -k * α) := by
        rw [show k * α + -k * α = 0 by ring]; exact h2
      exact h2'.scomp α h1
    rw [hd.deriv, norm_smul, Real.norm_eq_abs, abs_of_pos hk, hk_def]
    field_simp
  -- the competitor: `c` on `[0, α]`, `γ̃` on `[α, β]`, `c` on `[β, ℓ]`
  set c₁ : ℝ → V := fun t => if t ≤ α then c t else γ t with hc₁_def
  set c₂ : ℝ → V := fun t => if t ≤ β then c₁ t else c t with hc₂_def
  have hγps : IsPiecewiseSmooth γ α β :=
    IsPiecewiseSmooth.of_contDiffOn hγgeo.contDiffOn hαβ.le hsub
  have hc₁ps : IsPiecewiseSmooth c₁ 0 β :=
    (hc.mono le_rfl hα0 (by linarith)).concat hγps hγα.symm
  have hc₁β : c₁ β = c β := by simp only [hc₁_def, if_neg (not_le.2 hαβ), hγβ]
  have hc₂ps : IsPiecewiseSmooth c₂ 0 ℓ :=
    hc₁ps.concat (hc.mono (by linarith) hβℓ le_rfl) hc₁β
  have hc₂N : ∀ t ∈ Icc 0 ℓ, c₂ t ∈ N := by
    intro t ht
    simp only [hc₂_def, hc₁_def]
    split_ifs with h1 h2
    · exact hcN t ⟨ht.1, h2.trans (by linarith)⟩
    · exact hγN t ⟨(not_le.1 h2).le, h1⟩
    · exact hcN t ht
  have hc₂0 : c₂ 0 = c 0 := by
    simp only [hc₂_def, hc₁_def, if_pos (by linarith : (0 : ℝ) ≤ β), if_pos hα0]
  have hc₂ℓ : c₂ ℓ = c ℓ := by
    rcases eq_or_lt_of_le hβℓ with h | h
    · simp only [hc₂_def, ← h, le_refl, if_true, hc₁β]
    · simp only [hc₂_def, if_neg (not_le.2 h)]
  have hlen₂ : pathLength c₂ 0 ℓ = pathLength c 0 α + ‖v‖ + pathLength c β ℓ := by
    rw [hc₂_def, pathLength_concat hc₁ps.isAdmissible (hca.mono (by linarith) hβℓ le_rfl),
      hc₁_def, pathLength_concat (hca.mono le_rfl hα0 (by linarith)) hγps.isAdmissible,
      hγlen]
  -- minimality: the segment `[α, β]` has length `≤ ‖v‖`, hence `= ‖v‖`
  have hmin' := hmin c₂ 0 ℓ hc₂ps hc₂N hc₂0 hc₂ℓ
  rw [hlen₂] at hmin'
  have hsplit₁ := hca.pathLength_add (m := α) ⟨hα0, by linarith⟩
  have hsplit₂ := (hca.mono hα0 (by linarith) le_rfl).pathLength_add (m := β) ⟨hαβ.le, hβℓ⟩
  have hseg : pathLength c α β = β - α := harc α β hα0 hαβ.le hβℓ
  have hcαβ : IsAdmissible c α β := hca.mono hα0 hαβ.le hβℓ
  have hcαβN : ∀ t ∈ Icc α β, c t ∈ N := fun t ht => hcN t ⟨hα0.trans ht.1, ht.2.trans hβℓ⟩
  have hlow := nc.norm_le_pathLength hcαβ hcαβN rfl hv hvε (by rw [hexp])
  have heq : pathLength c α β = ‖v‖ := by linarith
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, norm_zero, hseg] at heq
    linarith
  -- the equality case of Theorem 10.4: `c = γ̃` on `[α, β]`
  have hrep := nc.eq_exp_of_pathLength_eq hcαβ hcαβN rfl hv hvε (by rw [hexp]) hv0 heq
  refine ⟨_, hsub, γ, hγgeo, fun t ht => ?_⟩
  rw [hrep t ht, harc α t hα0 ht.1 (ht.2.trans hβℓ), ← heq, hseg]
  simp only [hγ_def, hk_def]
  congr 2
  field_simp
  ring

/-- **Corollary 10.7** (Milnor, p. 61).  Let `c : [0, ℓ] → N` be a piecewise smooth path
parametrized by arc length (`‖c'(t)‖ = 1` wherever `c` is differentiable) whose length is at most
the length of every piecewise smooth path in `N` with the same endpoints.  Then `c` is a geodesic
on `(0, ℓ)`; in particular it is smooth there, also at its break points.  (It even extends to a
geodesic on an open interval containing `[0, ℓ]`: `Morse.corollary_10_7_extend`.) -/
theorem corollary_10_7 {c : ℝ → V} {ℓ : ℝ} (hc : IsPiecewiseSmooth c 0 ℓ)
    (hcN : ∀ t ∈ Icc 0 ℓ, c t ∈ N)
    (hunit : ∀ t ∈ Ioo 0 ℓ, DifferentiableAt ℝ c t → ‖deriv c t‖ = 1)
    (hmin : ∀ (c' : ℝ → V) (a b : ℝ), IsPiecewiseSmooth c' a b → (∀ t ∈ Icc a b, c' t ∈ N) →
      c' a = c 0 → c' b = c ℓ → pathLength c 0 ℓ ≤ pathLength c' a b) :
    IsGeodesicOn hN c (Ioo 0 ℓ) := by
  refine isGeodesicOn_of_locally hN isOpen_Ioo fun t₀ ht₀ => ?_
  have ht₀N := hcN t₀ (Ioo_subset_Icc_self ht₀)
  obtain ⟨O, hO, hpO, ε, hε, h1, -, h3⟩ := lemma_10_3 hN ⟨c t₀, ht₀N⟩
  -- a segment around `t₀` inside `W = N ∩ O`
  have hcont : ContinuousAt c t₀ := hc.2.1.continuousAt (Icc_mem_nhds ht₀.1 ht₀.2)
  obtain ⟨η₀, hη₀, hball⟩ := Metric.mem_nhds_iff.1 (hcont.preimage_mem_nhds (hO.mem_nhds hpO))
  set η := min (η₀ / 2) (min (t₀ / 2) ((ℓ - t₀) / 2)) with hη_def
  have hη : 0 < η := by
    have := ht₀.1; have := ht₀.2
    positivity
  have hη₁ : η ≤ η₀ / 2 := min_le_left _ _
  have hη₃ : η ≤ t₀ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hη₄ : η ≤ (ℓ - t₀) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hinO : ∀ t ∈ Icc (t₀ - η) (t₀ + η), c t ∈ O := fun t ht => hball (by
    rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2])
  obtain ⟨s, hs, γ, hγ, hγc⟩ := minimal_segment hN hc hcN hunit hmin h1 h3 (by linarith)
    (by linarith) (by linarith) hinO
  refine ⟨Ioo (t₀ - η) (t₀ + η), ⟨by linarith, by linarith⟩, fun t ht => ⟨by linarith [ht.1], by
    linarith [ht.2]⟩, ?_⟩
  exact (hγ.mono isOpen_Ioo (Ioo_subset_Icc_self.trans hs)).congr
    fun t ht => hγc (Ioo_subset_Icc_self ht)

/-- **Corollary 10.7, on the closed interval**: under the hypotheses of `Morse.corollary_10_7`, `c`
is the restriction to `[0, ℓ]` of a geodesic defined on an open interval `(-δ, ℓ + δ)` (Milnor's
"`ω` is a geodesic", with `ω` defined on `[0, ℓ]`). -/
theorem corollary_10_7_extend {c : ℝ → V} {ℓ : ℝ} (hc : IsPiecewiseSmooth c 0 ℓ)
    (hcN : ∀ t ∈ Icc 0 ℓ, c t ∈ N)
    (hunit : ∀ t ∈ Ioo 0 ℓ, DifferentiableAt ℝ c t → ‖deriv c t‖ = 1)
    (hmin : ∀ (c' : ℝ → V) (a b : ℝ), IsPiecewiseSmooth c' a b → (∀ t ∈ Icc a b, c' t ∈ N) →
      c' a = c 0 → c' b = c ℓ → pathLength c 0 ℓ ≤ pathLength c' a b) :
    ∃ δ > 0, ∃ γ : ℝ → V, IsGeodesicOn hN γ (Ioo (-δ) (ℓ + δ)) ∧ EqOn γ c (Icc 0 ℓ) := by
  rcases eq_or_lt_of_le hc.1 with hℓ | hℓ
  · -- `ℓ = 0`: a point
    subst hℓ
    refine ⟨1, one_pos, fun _ => c 0, isGeodesicOn_const hN (hcN 0 ⟨le_rfl, le_rfl⟩) isOpen_Ioo,
      fun t ht => ?_⟩
    rw [le_antisymm ht.2 ht.1]
  have hint := corollary_10_7 hN hc hcN hunit hmin
  -- a geodesic segment at an endpoint `e`, on `[e, e + η]` or `[e − η, e]`
  have hend : ∀ e ∈ ({0, ℓ} : Set ℝ), ∃ η > 0, η ≤ ℓ ∧ ∃ s : Set ℝ,
      Icc (max 0 (e - η)) (min ℓ (e + η)) ⊆ s ∧ ∃ γ : ℝ → V, IsGeodesicOn hN γ s ∧
        EqOn γ c (Icc (max 0 (e - η)) (min ℓ (e + η))) := by
    intro e he
    have heI : e ∈ Icc 0 ℓ := by
      rcases he with rfl | rfl
      · exact ⟨le_rfl, hℓ.le⟩
      · exact ⟨hℓ.le, le_rfl⟩
    obtain ⟨O, hO, hpO, ε, hε, h1, -, h3⟩ := lemma_10_3 hN ⟨c e, hcN e heI⟩
    have hcont : ContinuousWithinAt c (Icc 0 ℓ) e := hc.2.1 e heI
    obtain ⟨η₀, hη₀, hball⟩ := Metric.mem_nhdsWithin_iff.1
      (hcont.preimage_mem_nhdsWithin (hO.mem_nhds hpO))
    set η := min (η₀ / 2) ℓ with hη_def
    have hη : 0 < η := lt_min (by linarith) hℓ
    have hηℓ : η ≤ ℓ := min_le_right _ _
    have hη₁ : η ≤ η₀ / 2 := min_le_left _ _
    have hlo : max 0 (e - η) < min ℓ (e + η) := by
      rcases he with rfl | rfl
      · simp only [zero_sub, zero_add]; rw [max_eq_left (by linarith), lt_min_iff]
        exact ⟨hℓ, hη⟩
      · rw [max_lt_iff, lt_min_iff, lt_min_iff]
        exact ⟨⟨hℓ, by linarith⟩, by linarith, by linarith⟩
    obtain ⟨s, hs, γ, hγ, hγc⟩ := minimal_segment hN hc hcN hunit hmin h1 h3 (le_max_left _ _)
      hlo (min_le_left _ _) fun t ht => hball ⟨by
        rw [mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [ht.1, ht.2, le_max_right 0 (e - η), min_le_right ℓ (e + η)],
        ⟨(le_max_left _ _).trans ht.1, ht.2.trans (min_le_left _ _)⟩⟩
    exact ⟨η, hη, hηℓ, s, hs, γ, hγ, hγc⟩
  obtain ⟨η₀, hη₀, hη₀ℓ, s₀, hs₀, γ₀, hγ₀, hγ₀c⟩ := hend 0 (by simp)
  obtain ⟨η₁, hη₁, hη₁ℓ, s₁, hs₁, γ₁, hγ₁, hγ₁c⟩ := hend ℓ (by simp)
  have hI₀ : Icc (max 0 (0 - η₀)) (min ℓ (0 + η₀)) = Icc 0 η₀ := by
    rw [zero_sub, zero_add, max_eq_left (by linarith), min_eq_right hη₀ℓ]
  have hI₁ : Icc (max 0 (ℓ - η₁)) (min ℓ (ℓ + η₁)) = Icc (ℓ - η₁) ℓ := by
    rw [max_eq_right (by linarith), min_eq_left (by linarith)]
  rw [hI₀] at hs₀ hγ₀c
  rw [hI₁] at hs₁ hγ₁c
  obtain ⟨δ₀, hδ₀, hb₀⟩ := Metric.isOpen_iff.1 hγ₀.isOpen 0 (hs₀ ⟨le_rfl, hη₀.le⟩)
  obtain ⟨δ₁, hδ₁, hb₁⟩ := Metric.isOpen_iff.1 hγ₁.isOpen ℓ (hs₁ ⟨by linarith, le_rfl⟩)
  set δ := min δ₀ δ₁ with hδ_def
  have hδ : 0 < δ := lt_min hδ₀ hδ₁
  set g : ℝ → V := fun t => if t < 0 then γ₀ t else if ℓ < t then γ₁ t else c t with hg_def
  have hgc : EqOn g c (Icc 0 ℓ) := fun t ht => by
    simp only [hg_def, if_neg (not_lt.2 ht.1), if_neg (not_lt.2 ht.2)]
  refine ⟨δ, hδ, g, isGeodesicOn_of_locally hN isOpen_Ioo fun t ht => ?_, hgc⟩
  -- near `0`, near the interior, near `ℓ`
  rcases lt_or_ge t η₀ with h0 | h0
  · have hsub : Ioo (-δ₀) η₀ ⊆ s₀ := fun τ hτ => by
      rcases lt_or_ge τ 0 with hτ0 | hτ0
      · exact hb₀ (by rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hτ.1])
      · exact hs₀ ⟨hτ0, hτ.2.le⟩
    have heq : EqOn γ₀ g (Ioo (-δ₀) η₀) := fun τ hτ => by
      rcases lt_or_ge τ 0 with hτ0 | hτ0
      · simp only [hg_def, if_pos hτ0]
      · rw [hgc ⟨hτ0, hτ.2.le.trans hη₀ℓ⟩]
        exact hγ₀c ⟨hτ0, hτ.2.le⟩
    refine ⟨Ioo (-δ₀) η₀ ∩ Ioo (-δ) (ℓ + δ), ⟨⟨by linarith [ht.1, min_le_left δ₀ δ₁], h0⟩, ht⟩,
      inter_subset_right, ?_⟩
    exact ((hγ₀.mono isOpen_Ioo hsub).congr heq).mono (isOpen_Ioo.inter isOpen_Ioo)
      inter_subset_left
  rcases le_or_gt t (ℓ - η₁) with h1 | h1
  · have htI : t ∈ Ioo 0 ℓ := ⟨by linarith, by linarith⟩
    refine ⟨Ioo 0 ℓ, htI, fun τ hτ => ⟨by linarith [hτ.1], by linarith [hτ.2]⟩, ?_⟩
    exact hint.congr fun τ hτ => (hgc (Ioo_subset_Icc_self hτ)).symm
  · have hsub : Ioo (ℓ - η₁) (ℓ + δ₁) ⊆ s₁ := fun τ hτ => by
      rcases le_or_gt τ ℓ with hτℓ | hτℓ
      · exact hs₁ ⟨hτ.1.le, hτℓ⟩
      · exact hb₁ (by rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hτ.2])
    have heq : EqOn γ₁ g (Ioo (ℓ - η₁) (ℓ + δ₁)) := fun τ hτ => by
      rcases le_or_gt τ ℓ with hτℓ | hτℓ
      · rw [hgc ⟨by linarith [hτ.1], hτℓ⟩]
        exact hγ₁c ⟨hτ.1.le, hτℓ⟩
      · simp only [hg_def, if_neg (not_lt.2 (by linarith : (0 : ℝ) ≤ τ)), if_pos hτℓ]
    refine ⟨Ioo (ℓ - η₁) (ℓ + δ₁) ∩ Ioo (-δ) (ℓ + δ),
      ⟨⟨h1, by linarith [ht.2, min_le_right δ₀ δ₁]⟩, ht⟩, inter_subset_right, ?_⟩
    exact ((hγ₁.mono isOpen_Ioo hsub).congr heq).mono (isOpen_Ioo.inter isOpen_Ioo)
      inter_subset_left

end Morse
