import Morse.Chapter13.Perturbation
import Morse.Chapter13.Compression
import Morse.Chapter4.Whitney

/-!
Milnor, *Morse Theory*, §22, Lemma 22.5 (pp. 121–122): a Morse theorem for a manifold of minima.

# Functions whose minimum set is a manifold

## Milnor's text, paraphrased

(p. 121) Let `f : M → ℝ` be smooth with minimum `0`, each `M^c = f⁻¹[0, c]` compact.
**Lemma 22.5**: if the set `M⁰` of minimal points is a manifold, and every critical point in
`M − M⁰` has index `≥ λ₀`, then `π_r(M, M⁰) = 0` for `0 ≤ r < λ₀`.  *Proof*: by Hanner, `M⁰` is
a retract of a neighbourhood `U`, and (for `U` small) `U` can be deformed into `M⁰` within `M`.
Let `h : (Iʳ, ∂Iʳ) → (M, M⁰)`, `c = max f∘h`, `4δ = min f` on `M^c − U`, `g` a smooth
approximation of `f` on `M^{c + 2δ}` with no degenerate critical points, `|g − f| < δ`, and first
and second derivatives so close that Lemma 22.4 applies.  Then `g⁻¹(−∞, c + δ]` has the homotopy
type of `g⁻¹(−∞, 2δ]` with cells of dimension `≥ λ₀` attached; since `r < λ₀`, `h` is homotopic
to a map into `g⁻¹(−∞, 2δ] ⊆ U`, hence into `M⁰`.

## What is formalized

For a slice submanifold `N ⊆ V` and `f = F|N`, `F : V → ℝ` smooth:

* `Morse.lemma_22_5_sublevel`: **Lemma 22.5, below a level `a₀`**: suppose `f ≥ d` on `N`,
  `N^{a₀}` is compact, every critical point `q` with `d < f(q) < a₀` has index `≥ λ₀`, and
  `M⁰ = f⁻¹(d)` has an open neighbourhood `U` such that `M⁰` pushes maps from `P` out of `U`
  (`Morse.PushesInto`).  Then for every `b < a₀`, every map `P → N^b` is homotopic in `N`,
  relative to the preimage of `M⁰`, to a map into `M⁰`; here `P` is any compact space embedded
  in a real vector space of dimension `< λ₀` (for instance `Iʳ` or `I × Iʳ`, `r < λ₀`, or
  `r + 1 < λ₀`).  This is the form used for Theorem 22.1, where `E` is only defined below a
  level `c`.
* `Morse.lemma_22_5`: **Lemma 22.5** with all sublevel sets compact: then `M⁰` pushes maps from
  `P` out of all of `N` (Milnor's `π_r(M, M⁰) = 0`, `r < λ₀`, relative to the boundary and at all
  base points at once).
* `Morse.pushesInto_of_deformation`: the neighbourhood hypothesis holds when `U` deforms into
  `M⁰` within `N`, fixing `M⁰` (Milnor's "`U` can be deformed into `M⁰` within `M`").

## Deviations from Milnor

* **Hanner's theorem is not formalized.**  Milnor deduces from "`M⁰` is a manifold" (via Hanner:
  a manifold is a neighbourhood retract) and the Riemannian convexity of small balls that a
  neighbourhood `U` of `M⁰` deforms into `M⁰`.  Here the conclusion of that step is the
  hypothesis (`hU`); for Theorem 22.1 it is derived from the hypothesis that `Ω^d` is a
  neighbourhood retract, with Milnor's short geodesics (`Morse/Chapter13/Theorem22.lean`).
* **The approximation `g`.**  `g = (F + ρ ℓ)|N` with `ℓ` a small linear form, chosen so that
  `(F + ℓ)|N` is a Morse function (`Morse.ae_isMorseFunction_add_inner_comp`, the proof of
  Corollary 6.8), and `ρ` a bump function equal to `1` near the compact `N^{a₀}`, which makes
  `|g − f|` uniformly small on all of `N` (Milnor's `g` lives only on the compact `M^{c + 2δ}`; a
  function on a compact set is not enough for Theorems 3.1 and 3.2).  Lemma 22.4 is used in the
  form `Morse.lemma_22_4_submanifold`.
* **Regular levels**: the lower level `α ∈ (d + 2δ, d + 3δ)` is chosen to be a regular value of
  `g` (there are finitely many critical values there); Milnor's `2δ` might be critical.
-/

open Set Filter Topology Function Module Metric MeasureTheory
open scoped ContDiff Manifold unitInterval RealInnerProductSpace

noncomputable section

namespace Morse

/-! ### Deformations of a neighbourhood -/

/-- **A neighbourhood which deforms into `A`, fixing `A`, pushes maps into `A`.** -/
theorem pushesInto_of_deformation {P T : Type*} [TopologicalSpace P] [TopologicalSpace T]
    {A U : Set T} (D : C(I × U, T)) (h0 : ∀ x, D (0, x) = x) (h1 : ∀ x, D (1, x) ∈ A)
    (hA : ∀ t (x : U), (x : T) ∈ A → D (t, x) = x) : PushesInto P A U := by
  intro h hU
  let k : C(P, U) := ⟨fun p => ⟨h p, hU p⟩, by fun_prop⟩
  let H : C(I × P, T) := D.comp ⟨fun z => (z.1, k z.2), by fun_prop⟩
  refine ⟨⟨fun p => D (1, k p), by fun_prop⟩, fun p => h1 _,
    ⟨Morse.Homotopy.homotopyRelOfFun H (fun p => h0 (k p)) (fun p => rfl)
      fun t p hp => hA t (k p) hp⟩⟩

/-! ### Germs -/

section Germ

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

/-- Critical points and Hessians of restrictions only depend on the germ of the ambient
function. -/
theorem criticalPoint_hessianM_congr {F G : V → ℝ} {q : N} (h : F =ᶠ[𝓝 (q : V)] G) :
    letI := hN.chartedSpace
    (IsCriticalPointM Z (F ∘ Subtype.val) q ↔ IsCriticalPointM Z (G ∘ Subtype.val) q) ∧
      hessianM Z (F ∘ Subtype.val) q = hessianM Z (G ∘ Subtype.val) q := by
  let _ := hN.chartedSpace
  have h' : (F ∘ Subtype.val : N → ℝ) =ᶠ[𝓝 q] (G ∘ Subtype.val) :=
    h.comp_tendsto (continuous_subtype_val.tendsto q)
  have hm : mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) (F ∘ Subtype.val) q =
      mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) (G ∘ Subtype.val) q := h'.mfderiv_eq
  refine ⟨by rw [IsCriticalPointM, IsCriticalPointM, hm]; exact Iff.rfl, ?_⟩
  rw [hessianM, hessianM, localRep_eq, localRep_eq, extChartAt_self_coe]
  apply hessian_congr
  have ht : Tendsto (chartAt Z q).symm (𝓝 (chartAt Z q q)) (𝓝 q) := by
    have := (chartAt Z q).continuousAt_symm (mem_chart_target Z q)
    rw [ContinuousAt, (chartAt Z q).left_inv (mem_chart_source Z q)] at this
    exact this
  exact h'.comp_tendsto ht

end Germ

/-! ### Lemma 22.5 -/

section Lemma225

universe u

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set V}

/-- **Lemma 22.5 below a level `a₀`** (Milnor, p. 121): see the module docstring. -/
theorem lemma_22_5_sublevel (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {F : V → ℝ}
    (hF : ContDiff ℝ ∞ F) {d a₀ : ℝ} (hmin : ∀ q : N, d ≤ F q)
    (hK : IsCompact ((F ∘ Subtype.val : N → ℝ) ⁻¹' Iic a₀)) {l₀ : ℕ}
    (hidx : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      d < F q → F q < a₀ → l₀ ≤ indexM Z (F ∘ Subtype.val) q)
    {P : Type*} [TopologicalSpace P] [CompactSpace P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hE : finrank ℝ E < l₀) {ι : P → E} (hι : Continuous ι) (hιinj : Injective ι)
    (hU : ∃ U : Set N, IsOpen U ∧ sublevel (F ∘ Subtype.val : N → ℝ) d ⊆ U ∧
      PushesInto P (sublevel (F ∘ Subtype.val : N → ℝ) d) U)
    {b : ℝ} (hb : b < a₀) :
    PushesInto P (sublevel (F ∘ Subtype.val : N → ℝ) d) (sublevel (F ∘ Subtype.val) b) := by
  classical
  let _ := hN.chartedSpace
  have := hN.isManifold
  set f : N → ℝ := F ∘ Subtype.val with hf_def
  have hfc : Continuous f := hF.continuous.comp continuous_subtype_val
  obtain ⟨U, hUo, hMU, hpush⟩ := hU
  by_cases hbd : b < d
  · intro h hX
    refine ⟨h, fun p => absurd (hX p) fun hp => ?_, ContinuousMap.HomotopicRel.refl h⟩
    have := hmin (h p)
    exact absurd (lt_of_le_of_lt (le_trans this hp) hbd) (lt_irrefl _)
  push Not at hbd
  have hda₀ : d < a₀ := lt_of_le_of_lt hbd hb
  -- Step 1: `f ≥ m₁ > d` off `U` (below `a₀`)
  obtain ⟨m₁, hdm₁, hm₁a₀, hm₁U⟩ : ∃ m₁, d < m₁ ∧ m₁ ≤ a₀ ∧ ∀ q, f q < m₁ → q ∈ U := by
    set Kout := f ⁻¹' Iic a₀ ∩ Uᶜ with hKout
    have hKc : IsCompact Kout := hK.inter_right hUo.isClosed_compl
    rcases Kout.eq_empty_or_nonempty with he | hne
    · refine ⟨a₀, hda₀, le_rfl, fun q hq => ?_⟩
      by_contra hqU
      have : q ∈ Kout := ⟨mem_Iic.2 hq.le, hqU⟩
      rw [he] at this
      exact this
    · obtain ⟨q₀, hq₀, hmin₀⟩ := hKc.exists_isMinOn hne hfc.continuousOn
      refine ⟨f q₀, lt_of_le_of_ne (hmin q₀) fun h => hq₀.2 (hMU ?_), hq₀.1, fun q hq => ?_⟩
      · exact (show f q₀ ≤ d from h.symm.le)
      · by_contra hqU
        have := hmin₀ (show q ∈ Kout from ⟨mem_Iic.2 (hq.le.trans hq₀.1), hqU⟩)
        exact absurd this (not_le.2 hq)
  set δ := min ((m₁ - d) / 4) ((a₀ - b) / 5) with hδ_def
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ1 : δ ≤ (m₁ - d) / 4 := min_le_left _ _
  have hδ2 : δ ≤ (a₀ - b) / 5 := min_le_right _ _
  -- the compact region where Lemma 22.4 is applied
  set Kst : Set N := f ⁻¹' Icc (d + δ) (b + 4 * δ) with hKst_def
  have hKstc : IsCompact Kst := hK.of_isClosed_subset (isClosed_Icc.preimage hfc)
    fun q hq => mem_Iic.2 (hq.2.trans (by linarith))
  obtain ⟨δ₄, hδ₄, H4⟩ := lemma_22_4_submanifold hN hF hKstc (l₀ := l₀) fun q hq hc =>
    hidx q hc (by have h1 : d + δ ≤ F q := hq.1; linarith)
      (by have h1 : F q ≤ b + 4 * δ := hq.2; linarith)
  -- a bound for `‖x‖` on `N^{a₀}`, and a bump function equal to `1` near it
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn continuous_subtype_val.continuousOn
  set R₀ := max R 0 with hR₀_def
  have hR₀ : 0 ≤ R₀ := le_max_right _ _
  have hRq : ∀ q : N, f q ≤ a₀ → ‖(q : V)‖ ≤ R₀ := fun q hq =>
    (hR q (mem_Iic.2 hq)).trans (le_max_left _ _)
  let ρ : ContDiffBump (0 : V) := ⟨R₀ + 1, R₀ + 2, by positivity, by linarith⟩
  -- a small linear form `ℓ` with `(F + ℓ)|N` a Morse function
  let L := toEuclidean (E := V)
  have he : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ V))) ∞
      (L ∘ (Subtype.val : N → V)) := L.contDiff.contMDiff.comp hN.contMDiff_val
  have hemb : Topology.IsEmbedding (L ∘ (Subtype.val : N → V)) :=
    L.toHomeomorph.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have hinj : ∀ x : N, Injective (mfderiv 𝓘(ℝ, Z)
      𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ V))) (L ∘ (Subtype.val : N → V)) x) := by
    intro x
    rw [mfderiv_comp x ((L.contDiff (n := 1)).contMDiff.mdifferentiableAt one_ne_zero)
      (hN.contMDiff_val.mdifferentiableAt (by simp)), mfderiv_eq_fderiv, L.fderiv]
    exact L.injective.comp (Milnor.injective_mfderiv_val hN x)
  set η := min δ₄ (δ / (R₀ + 3)) / (‖L.toContinuousLinearMap‖ + 1) with hη_def
  have hη : 0 < η := div_pos (lt_min hδ₄ (div_pos hδ (by linarith))) (by positivity)
  obtain ⟨a, ha, hmorse⟩ : ∃ a ∈ ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ V))) η,
      IsMorseFunction Z (fun x : N => f x + ⟪a, (L ∘ Subtype.val) x⟫) := by
    have hpos : (volume : Measure (EuclideanSpace ℝ (Fin (finrank ℝ V)))) (ball 0 η) ≠ 0 :=
      (isOpen_ball.measure_pos volume (nonempty_ball.2 hη)).ne'
    exact Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae
      (ae_isMorseFunction_add_inner_comp he hemb hinj volume (contMDiff_comp_val hN hF)))
  set ℓ : V →L[ℝ] ℝ := (innerSL ℝ a).comp L.toContinuousLinearMap with hℓ_def
  have hℓ : ‖ℓ‖ < min δ₄ (δ / (R₀ + 3)) := by
    have h1 : ‖ℓ‖ ≤ ‖a‖ * ‖L.toContinuousLinearMap‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (innerSL_apply_norm (𝕜 := ℝ) a).le (norm_nonneg _))
    have h2 : ‖a‖ < η := by rwa [mem_ball, dist_zero_right] at ha
    have h3 : ‖a‖ * ‖L.toContinuousLinearMap‖ ≤ η * ‖L.toContinuousLinearMap‖ :=
      mul_le_mul_of_nonneg_right h2.le (norm_nonneg _)
    have h4 : η * ‖L.toContinuousLinearMap‖ < min δ₄ (δ / (R₀ + 3)) := by
      rw [hη_def, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      have : 0 < min δ₄ (δ / (R₀ + 3)) := lt_min hδ₄ (div_pos hδ (by linarith))
      nlinarith
    linarith
  have hmorse' : IsMorseFunction Z ((fun x => F x + ℓ x) ∘ (Subtype.val : N → V)) := by
    convert hmorse using 1
    funext x
    simp [ℓ, hf_def, innerSL_apply_apply]
  -- the approximation `g = (F + ρ ℓ)|N`
  set G : V → ℝ := fun x => F x + ρ x * ℓ x with hG_def
  have hG : ContDiff ℝ ∞ G := hF.add (ρ.contDiff.mul ℓ.contDiff)
  set g : N → ℝ := G ∘ Subtype.val with hg_def
  have hgc : Continuous g := hG.continuous.comp continuous_subtype_val
  have hGloc : ∀ q : N, ‖(q : V)‖ < R₀ + 1 → G =ᶠ[𝓝 (q : V)] fun x => F x + ℓ x := by
    intro q hq
    filter_upwards [ρ.eventuallyEq_one_of_mem_ball (by rwa [mem_ball, dist_zero_right])]
      with x hx
    simp only [hG_def, hx, Pi.one_apply, one_mul]
  have hgf : ∀ q : N, |g q - f q| < δ := by
    intro q
    have hsub : g q - f q = ρ q * ℓ q := by simp [hg_def, hf_def, hG_def]
    rw [hsub, abs_mul, abs_of_nonneg ρ.nonneg]
    have hℓq : |ℓ q| ≤ ‖ℓ‖ * ‖(q : V)‖ := by
      rw [← Real.norm_eq_abs]; exact ℓ.le_opNorm _
    have hℓ' : ‖ℓ‖ * (R₀ + 2) < δ := by
      have h1 : ‖ℓ‖ < δ / (R₀ + 3) := hℓ.trans_le (min_le_right _ _)
      have h2 : ‖ℓ‖ * (R₀ + 3) < δ := by rwa [lt_div_iff₀ (by linarith)] at h1
      nlinarith [norm_nonneg ℓ]
    by_cases hq : ‖(q : V)‖ < R₀ + 2
    · calc ρ q * |ℓ q| ≤ 1 * (‖ℓ‖ * ‖(q : V)‖) :=
            mul_le_mul ρ.le_one hℓq (abs_nonneg _) zero_le_one
        _ ≤ ‖ℓ‖ * (R₀ + 2) := by
            rw [one_mul]; exact mul_le_mul_of_nonneg_left hq.le (norm_nonneg _)
        _ < δ := hℓ'
    · have : ρ q = 0 := ρ.zero_of_le_dist (by rw [dist_zero_right]; exact not_lt.1 hq)
      rw [this, zero_mul]
      exact hδ
  have hgf1 : ∀ q : N, g q < f q + δ := fun q => by linarith [(abs_lt.1 (hgf q)).2]
  have hgf2 : ∀ q : N, f q < g q + δ := fun q => by linarith [(abs_lt.1 (hgf q)).1]
  -- the top level `b + 3δ` of `g`: compact sublevel inside `N^{a₀}`
  set a₁ := b + 3 * δ with ha₁_def
  have hga₁ : ∀ q : N, g q ≤ a₁ → f q ≤ a₀ := fun q hq => by linarith [hgf2 q]
  have hgK : IsCompact (g ⁻¹' Iic a₁) :=
    hK.of_isClosed_subset (isClosed_Iic.preimage hgc) fun q hq => mem_Iic.2 (hga₁ q hq)
  -- critical points of `g` below `a₁` are those of `(F + ℓ)|N`
  have hloc : ∀ q : N, g q ≤ a₁ →
      (IsCriticalPointM Z g q ↔ IsCriticalPointM Z ((fun x => F x + ℓ x) ∘ Subtype.val) q) ∧
      hessianM Z g q = hessianM Z ((fun x => F x + ℓ x) ∘ Subtype.val) q := fun q hq =>
    criticalPoint_hessianM_congr hN (hGloc q (by linarith [hRq q (hga₁ q hq)]))
  have hnd : ∀ q : N, g q ≤ a₁ → IsCriticalPointM Z g q → IsNondegenerate (hessianM Z g q) :=
    fun q hq hc => by
      rw [(hloc q hq).2]
      exact hmorse'.isNondegenerate q ((hloc q hq).1.1 hc)
  -- a regular value `α ∈ (d + 2δ, d + 3δ)` of `g`
  have hfin : (g ⁻¹' Iic a₁ ∩ {q | IsCriticalPointM Z g q}).Finite := by
    have hgs : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) ∞ g := contMDiff_comp_val hN hG
    have hC : IsCompact (g ⁻¹' Iic a₁ ∩ {x | IsCriticalPointM Z g x}) :=
      hgK.inter_right (isClosed_setOf_isCriticalPointM (hgs.of_le (by norm_cast)))
    exact hC.finite (isDiscrete_inter_setOf_isCriticalPointM
      (fun x _ => (hgs x).of_le (by norm_cast)) fun x hx hc => hnd x hx hc)
  obtain ⟨α, hαI, hαreg⟩ : ∃ α ∈ Ioo (d + 2 * δ) (d + 3 * δ),
      α ∉ g '' (g ⁻¹' Iic a₁ ∩ {q | IsCriticalPointM Z g q}) :=
    ((Ioo_infinite (by linarith)).sdiff (hfin.image g)).nonempty
  have ha : ∀ q : N, IsCriticalPointM Z g q → G q ≠ α := fun q hc heq => by
    refine hαreg ⟨q, ⟨show g q ≤ a₁ from ?_, hc⟩, heq⟩
    change G q ≤ a₁
    rw [heq]
    linarith [hαI.2, ha₁_def, hbd]
  set β := max (b + δ) α with hβ_def
  have hD := lemma_D hN hG (a := α) (a₀ := a₁) hgK (l₀ := l₀) ha (fun q hc hαq hqa₁ =>
      ⟨hnd q hqa₁ hc, by
        have hc' := (hloc q hqa₁).1.1 hc
        have hqK : q ∈ Kst := by
          have h1 := hgf1 q
          have h2 := hgf2 q
          have h3 : α < g q := hαq
          have h4 : g q ≤ a₁ := hqa₁
          have h5 := hαI.1
          change d + δ ≤ f q ∧ f q ≤ b + 4 * δ
          constructor <;> linarith
        have := H4 ℓ (hℓ.trans_le (min_le_left _ _)) q hqK hc'
        rw [indexM, (hloc q hqa₁).2]
        exact this⟩)
    hE hι hιinj (b := β) (le_max_right _ _) (max_lt (by linarith) (by linarith [hαI.2, hbd]))
  -- the chain `M⁰ ⊆ g^α ⊆ U`, `f^b ⊆ g^β`
  have h1 : sublevel f d ⊆ sublevel g α := fun q hq => by
    have h := mem_sublevel.1 hq
    have h' := hgf1 q
    have h'' := hαI.1
    change g q ≤ α
    linarith
  have h2 : sublevel g α ⊆ U := fun q hq => hm₁U q (by
    have h := mem_sublevel.1 hq
    have h' := hgf2 q
    have h'' := hαI.2
    linarith)
  have h3 : sublevel f b ⊆ sublevel g β := fun q hq => by
    have h := mem_sublevel.1 hq
    have h' := hgf1 q
    have h'' := le_max_left (b + δ) α
    change g q ≤ β
    linarith
  exact ((hpush.mono h2).trans h1 hD).mono h3

/-- **Lemma 22.5** (Milnor, p. 121), for a slice submanifold `N ⊆ V` and `f = F|N` with minimum
value `d` and all sublevel sets compact: if every critical point of `f` outside the minimum set
`M⁰ = f⁻¹(d)` has index `≥ λ₀`, and `M⁰` has an open neighbourhood `U` from which it pushes maps
(e.g. one deforming into `M⁰` within `N`, `Morse.pushesInto_of_deformation`; Milnor obtains it
from Hanner's theorem), then every map from a compact `P` embedded in a real vector space of
dimension `< λ₀` into `N` is homotopic, relative to the preimage of `M⁰`, to a map into `M⁰`
(Milnor: `π_r(N, M⁰) = 0` for `r < λ₀`). -/
theorem lemma_22_5 (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {F : V → ℝ}
    (hF : ContDiff ℝ ∞ F) {d : ℝ} (hmin : ∀ q : N, d ≤ F q)
    (hK : ∀ c, IsCompact ((F ∘ Subtype.val : N → ℝ) ⁻¹' Iic c)) {l₀ : ℕ}
    (hidx : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      d < F q → l₀ ≤ indexM Z (F ∘ Subtype.val) q)
    {P : Type*} [TopologicalSpace P] [CompactSpace P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hE : finrank ℝ E < l₀) {ι : P → E} (hι : Continuous ι) (hιinj : Injective ι)
    (hU : ∃ U : Set N, IsOpen U ∧ sublevel (F ∘ Subtype.val : N → ℝ) d ⊆ U ∧
      PushesInto P (sublevel (F ∘ Subtype.val : N → ℝ) d) U) :
    PushesInto P (sublevel (F ∘ Subtype.val : N → ℝ) d) univ := by
  intro h _
  obtain ⟨b, hb⟩ := (isCompact_range h.continuous).bddAbove_image
    (hF.continuous.comp continuous_subtype_val).continuousOn
  exact lemma_22_5_sublevel hN hF hmin (hK (b + 1)) (fun q hc hd _ => hidx q hc hd) hE hι hιinj
    hU (lt_add_one b) h fun p => hb ⟨h p, mem_range_self p, rfl⟩

end Lemma225

end Morse
