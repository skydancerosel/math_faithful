import Morse.Chapter13.MinimalDeform

/-!
Milnor, *Morse Theory*, §22, Theorem 22.1 (pp. 118, 122–123), with the proof of
Exposition/Chapter13.md, §4.

# Theorem 22.1: the path space is highly connected to the space of minimal geodesics

## Milnor's text, paraphrased

(p. 118) **Theorem 22.1**: if the space `Ω^d` of minimal geodesics from `p` to `q` is a
topological manifold, and if every non-minimal geodesic from `p` to `q` has index `≥ λ₀`, then
`π_i(Ω, Ω^d) = 0` for `0 ≤ i < λ₀`.  (pp. 122–123) *Proof*: a map `(Iⁱ, ∂Iⁱ) → (Ω, Ω^d)` lands in
some `Int Ω^c`, which deformation retracts onto the manifold `B = Int Ω^c(t₀, …, t_k)` of broken
geodesics, fixing `B ⊇ Ω^d`; on `B` the function `F ∘ E` (`F : [d, c) → [0, ∞)` a
diffeomorphism) satisfies the hypotheses of Lemma 22.5.

## What is formalized

For a slice submanifold `N` of a finite-dimensional inner product space `V` (the setting of
Chapter 10), `p, q ∈ N`, `Ω = Ω(N; p, q)` with Milnor's metric (`Morse.PathSp`):

* `Morse.minPaths N p q`: `Ω^d`, the paths of least energy (by Lemma 12.1 these are the minimal
  geodesics, parametrized proportionally to arc length, and `d = ρ(p, q)²`; here `d` is just the
  least energy, which exists by Hopf–Rinow, and the minimal paths are unbroken geodesics,
  `Morse.isUnbrokenGeodesic_of_minimal`).
* `Morse.theorem_22_1`: **Theorem 22.1**.  Suppose the closed balls about `p` are compact
  (completeness, via Hopf–Rinow), every geodesic from `p` to `q` which is not of least energy has
  index `≥ λ₀`, and `Ω^d` is a retract of an open neighbourhood in `Ω`.  Then every map `h` from a
  compact `P` embedded in a real vector space of dimension `< λ₀` into `Ω` is homotopic, relative
  to `h⁻¹(Ω^d)`, to a map into `Ω^d`.  With `P = Iⁱ`, `i < λ₀`, this is `π_i(Ω, Ω^d) = 0` in the
  strong form (H1) of the exposition (relative to `∂Iⁱ`, at all base points).
* `Morse.compresses_minPaths`: the same as `Morse.Homotopy.Compresses` for the inclusion
  `Ω^d → Ω`.
* `Morse.theorem_22_1_bijective`, `Morse.theorem_22_1_surjective` (**Milnor's corollary on
  p. 118**): the inclusion `Ω^d → Ω` induces bijections `π_i(Ω^d, γ) → π_i(Ω, γ)` for
  `i ≤ λ₀ − 2` and surjections for `i = λ₀ − 1`, at every `γ ∈ Ω^d`.

## Deviations from Milnor, and what Milnor leaves implicit

* **Hanner's theorem** (a topological manifold is a neighbourhood retract) is not formalized:
  the hypothesis "`Ω^d` is a topological manifold" is replaced by its consequence that `Ω^d` is a
  retract of a neighbourhood in `Ω` (Hanner: in the metrizable `B`; a retraction of a
  neighbourhood in `B` composed with Milnor's `r_1` is one in `Ω`, and conversely).  The
  retraction is turned into Milnor's deformation along short geodesics in
  `Morse.BrokenSetup.exists_pushesInto_nodes`.
* **No reparametrization `F`**: Lemma 22.5 is used in the form `Morse.lemma_22_5_sublevel`, which
  only needs a compact sublevel set `B^{a₀}` (Theorem 16.2), so `E'` (extended smoothly from
  `B^{c₁}`) is used directly instead of `F ∘ E'`.
* **`Ω` is not Hausdorff** (paths are functions on `ℝ`), and the broken geodesic with the break
  points of `ω ∈ B` agrees with `ω` only on `[0, 1]`; the final homotopy is corrected on the
  points at distance `0` (`Morse.PathSp.continuous_of_edist_eq_zero`).
* "It is sufficient to prove `π_i(Int Ω^c, Ω^d) = 0` for large `c`": `E ∘ h` is bounded on the
  compact `P`; `Ω^d ⊆ B` because the minimal paths are unbroken geodesics of energy `d < c`, so
  Milnor's `r_u` fixes them.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold unitInterval ENNReal

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V}

/-- **`Ω^d`: the paths of least energy** from `p` to `q` (Milnor's space of minimal geodesics,
p. 118). -/
def minPaths (N : Set V) (p q : V) : Set (PathSp N p q) :=
  {γ | ∀ γ' : PathSp N p q, energy γ 0 1 ≤ energy γ' 0 1}

/-- **Theorem 22.1** (Milnor, p. 118): see the module docstring. -/
theorem theorem_22_1 (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {p q : V} (hp : p ∈ N)
    (hq : q ∈ N) (hball : ∀ r : ℝ, IsCompact (closedRiemBall N p r)) {l₀ : ℕ}
    (hidx : ∀ γ (hγ : γ ∈ pathSpace N p q), IsUnbrokenGeodesic hN γ →
      (∃ γ' ∈ pathSpace N p q, energy γ' 0 1 < energy γ 0 1) →
      (l₀ : ℕ∞) ≤ formIndex (energyHessian hN hγ))
    (hretr : ∃ O : Set (PathSp N p q), IsOpen O ∧ minPaths N p q ⊆ O ∧
      ∃ ρ : PathSp N p q → PathSp N p q, ContinuousOn ρ O ∧ (∀ γ ∈ O, ρ γ ∈ minPaths N p q) ∧
        ∀ γ ∈ minPaths N p q, ρ γ = γ)
    {P : Type*} [TopologicalSpace P] [CompactSpace P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hE : finrank ℝ E < l₀) {ι : P → E} (hι : Continuous ι) (hιinj : Injective ι) :
    PushesInto P (minPaths N p q) univ := by
  classical
  intro h _
  by_cases hP : IsEmpty P
  · exact ⟨h, fun x => isEmptyElim x, ContinuousMap.HomotopicRel.refl h⟩
  rw [not_isEmpty_iff] at hP
  obtain ⟨x₀⟩ := hP
  -- Step 1: a bound for the energy along `h`
  have hEc : Continuous fun γ : PathSp N p q => energy γ 0 1 :=
    PathSp.continuous_energy le_rfl zero_le_one le_rfl
  obtain ⟨c₀, hc₀⟩ := (isCompact_range h.continuous).bddAbove_image hEc.continuousOn
  have hhc₀ : ∀ x, energy (h x) 0 1 ≤ c₀ := fun x => hc₀ ⟨h x, mem_range_self x, rfl⟩
  have hc₀0 : 0 ≤ c₀ := (PathSp.energy_nonneg_of_le zero_le_one).trans (hhc₀ x₀)
  set c := c₀ + 3 with hc_def
  obtain ⟨m, ⟨B⟩⟩ := exists_brokenSetup_uniform hN hp hq (by linarith : 0 < c) (hball √c)
  -- a path of least energy, and `d`
  obtain ⟨y₀, hy₀, -, hy₀min⟩ := B.exists_energy_minimizing (h x₀).mem (by linarith [hhc₀ x₀])
  set d := B.energy' y₀ with hd_def
  have hdmin : ∀ γ ∈ pathSpace N p q, d ≤ energy γ 0 1 := fun γ hγ => by
    rw [hd_def, ← B.energy_path hy₀]; exact hy₀min γ hγ
  have hdc₀ : d ≤ c₀ := (hdmin _ (h x₀).mem).trans (hhc₀ x₀)
  have hmin_iff : ∀ γ : PathSp N p q, γ ∈ minPaths N p q ↔ energy γ 0 1 ≤ d := fun γ =>
    ⟨fun hγ => by
      have := hγ (B.pathP ⟨y₀, hy₀⟩)
      rwa [show energy (B.pathP ⟨y₀, hy₀⟩ : ℝ → V) 0 1 = d from B.energy_path hy₀] at this,
     fun hγ γ' => hγ.trans (hdmin _ γ'.mem)⟩
  have hminB : ∀ γ ∈ minPaths N p q, (γ : ℝ → V) ∈ B.brokenPaths := fun γ hγ =>
    ⟨γ.mem, B.isBroken_of_isUnbrokenGeodesic (isUnbrokenGeodesic_of_minimal γ.mem
      fun γ' hγ' => hγ ⟨γ', hγ'⟩), by linarith [(hmin_iff γ).1 hγ]⟩
  -- Step 2: Milnor's deformation `r_u` of `Int Ω^c` onto `B`
  let K₁ : C(I × P, PathSp N p q) := ⟨fun z => B.deform z.1 (h z.2),
    B.continuousOn_deform.comp_continuous (f := fun z : I × P => ((z.1 : ℝ), h z.2))
      (by fun_prop) fun z => ⟨z.1.2, show energy (h z.2) 0 1 < c by linarith [hhc₀ z.2]⟩⟩
  have hK₁E : ∀ x, energy (K₁ (1, x)) 0 1 ≤ c₀ := fun x =>
    (B.energy_deform_le _ _).trans (hhc₀ x)
  have hK₁B : ∀ x, (K₁ (1, x) : ℝ → V) ∈ B.brokenPaths := fun x =>
    B.deform_one_mem_brokenPaths (show energy (h x) 0 1 < c by linarith [hhc₀ x])
  have hK₁fix : ∀ t x, h x ∈ minPaths N p q → K₁ (t, x) = h x := fun t x hx =>
    B.deform_of_mem_brokenPaths t.2 (hminB _ hx)
  -- Step 3: the manifold `S = {y ∈ U : E'(y) < c₁}` of break points
  set c₁ := c₀ + 2 with hc₁_def
  obtain ⟨F, hF, hFE⟩ := B.exists_contDiff_eq_energy' (b := c₁ + 1 / 2) (by linarith)
  obtain ⟨O, hO, hOeq⟩ := B.exists_isOpen_sublevel_lt c₁
  set S := (Set.pi univ fun _ => N) ∩ O with hS_def
  have hSmem : ∀ y, y ∈ S ↔ y ∈ B.nodes ∧ B.energy' y < c₁ := fun y =>
    (Set.ext_iff.1 hOeq y).symm
  have hOU : S ⊆ B.nodes := fun y hy => ((hSmem y).1 hy).1
  have hFE' : ∀ y ∈ S, F y = B.energy' y := fun y hy =>
    hFE y ⟨((hSmem y).1 hy).1, by linarith [((hSmem y).1 hy).2]⟩
  set hSm := isSliceSubmanifold_pi_inter hN hO
  let _ := hSm.chartedSpace
  set f : S → ℝ := F ∘ Subtype.val with hf_def
  have hfE : ∀ y : S, f y = B.energy' y := fun y => hFE' y y.2
  have hnodes : ∀ x, B.nodeVal (K₁ (1, x)) ∈ S := fun x => by
    obtain ⟨h1, h2⟩ := B.nodeVal_mem_nodes_of_energy_lt (K₁ (1, x)).mem
      (show energy (K₁ (1, x)) 0 1 < c by linarith [hK₁E x])
    exact (hSmem _).2 ⟨h1, by linarith [hK₁E x]⟩
  let h₂ : C(P, S) := ⟨fun x => ⟨B.nodeVal (K₁ (1, x)), hnodes x⟩,
    (B.continuous_nodeVal.comp (K₁.continuous.comp (continuous_const.prodMk continuous_id))
      ).subtype_mk _⟩
  have hh₂E : ∀ x, B.energy' (h₂ x) ≤ energy (K₁ (1, x)) 0 1 := fun x =>
    (B.nodeVal_mem_nodes_of_energy_lt (K₁ (1, x)).mem
      (show energy (K₁ (1, x)) 0 1 < c by linarith [hK₁E x])).2
  -- Step 4: Lemma 22.5 on `S`
  have hmin : ∀ y : S, d ≤ F y := fun y => by
    rw [show F y = f y from rfl, hfE, ← B.energy_path (hOU y.2)]
    exact hdmin _ (B.path_mem_pathSpace (hOU y.2))
  set a₀ := c₀ + 1 with ha₀_def
  have hK : IsCompact (f ⁻¹' Iic a₀) := by
    have hBa : Subtype.val '' (f ⁻¹' Iic a₀) = {y | y ∈ B.nodes ∧ B.energy' y ≤ a₀} := by
      ext y
      simp only [mem_image, mem_preimage, mem_Iic, mem_ofPred_eq]
      constructor
      · rintro ⟨y', hy', rfl⟩
        exact ⟨hOU y'.2, by rw [← hfE]; exact hy'⟩
      · rintro ⟨hy, hya⟩
        have hyS : y ∈ S := (hSmem y).2 ⟨hy, by linarith⟩
        exact ⟨⟨y, hyS⟩, by rw [hfE]; exact hya, rfl⟩
    rw [Topology.IsInducing.subtypeVal.isCompact_iff, hBa]
    exact B.isCompact_sublevel (by linarith)
  have hidx' : ∀ y : S, IsCriticalPointM (Fin m → Z) f y → d < F y → F y < a₀ →
      l₀ ≤ indexM (Fin m → Z) f y := by
    intro y hc hdy _
    have hgeo := (B.isCriticalPointM_iff hO hOU hF hFE' y).1 hc
    have hidxeq := (B.theorem_16_2_index hO hOU hF hFE' y hgeo).1
    have hnonmin : ∃ γ' ∈ pathSpace N p q, energy γ' 0 1 < energy (B.path y) 0 1 :=
      ⟨B.path y₀, B.path_mem_pathSpace hy₀, by
        rw [B.energy_path hy₀, B.energy_path (hOU y.2), ← hfE]; exact hdy⟩
    have := hidx _ (B.path_mem_pathSpace (hOU y.2)) hgeo hnonmin
    rw [← hidxeq] at this
    exact_mod_cast this
  obtain ⟨Ωr, hΩr, hΩOr, ρ, hρc, hρ, hρid⟩ := hretr
  obtain ⟨U, hUo, hMU, hpushU⟩ := B.exists_pushesInto_nodes hO hOU (d := d) (by linarith) hΩr
    (fun γ hγ => hΩOr ((hmin_iff γ).2 hγ)) hρc (fun γ hγ => (hmin_iff _).1 (hρ γ hγ))
    (fun γ hγ => hρid γ ((hmin_iff γ).2 hγ)) P
  have hsl : sublevel f d = {y : S | B.energy' y ≤ d} := by
    ext y; simp only [mem_sublevel, hfE, mem_ofPred_eq]
  have hpush := lemma_22_5_sublevel hSm hF hmin hK hidx' hE hι hιinj
    ⟨U, hUo, hsl ▸ hMU, hsl ▸ hpushU⟩ (b := c₀) (by linarith)
  obtain ⟨h₃, hh₃, ⟨G₂⟩⟩ := hpush h₂ fun x => by
    change f (h₂ x) ≤ c₀
    rw [hfE]
    exact (hh₂E x).trans (hK₁E x)
  -- Step 5: back to `Ω`
  let pS : C(S, PathSp N p q) :=
    ⟨fun y => B.pathP ⟨y.1, hOU y.2⟩, B.continuous_pathP.comp (continuous_inclusion hOU)⟩
  let K₂ : C(I × P, PathSp N p q) := pS.comp G₂.toContinuousMap
  have hpSh₂ : ∀ x, EqOn (K₁ (1, x) : ℝ → V) (pS (h₂ x)) (Icc 0 1) := fun x =>
    ((B.lemma_16_1).2 _ (hK₁B x)).2.symm
  have hfixed : ∀ x, h x ∈ minPaths N p q → h₂ x ∈ sublevel f d := fun x hx => by
    change f (h₂ x) ≤ d
    rw [hfE]
    refine (hh₂E x).trans ?_
    rw [hK₁fix 1 x hx]
    exact (hmin_iff _).1 hx
  let K₂' : I × P → PathSp N p q := fun z =>
    if z.1 = 0 ∨ h z.2 ∈ minPaths N p q then K₁ (1, z.2) else K₂ z
  have hK₂' : ∀ z, edist (K₂' z) (K₂ z) = 0 := by
    rintro ⟨t, x⟩
    by_cases hcond : t = 0 ∨ h x ∈ minPaths N p q
    · have hK₂ : K₂ (t, x) = pS (h₂ x) := by
        change pS (G₂ (t, x)) = pS (h₂ x)
        rcases hcond with rfl | hx
        · rw [G₂.apply_zero]
        · rw [G₂.eq_fst t (show x ∈ h₂ ⁻¹' sublevel f d from hfixed x hx)]
      simp only [K₂', if_pos hcond]
      rw [hK₂]
      exact PathSp.edist_eq_zero_of_eqOn (hpSh₂ x)
    · simp only [K₂', if_neg hcond]
      exact edist_self _
  have hK₂'c : Continuous K₂' := PathSp.continuous_of_edist_eq_zero K₂.continuous hK₂'
  let f₁ : C(P, PathSp N p q) := ⟨fun x => K₁ (1, x), by fun_prop⟩
  let h' : C(P, PathSp N p q) := ⟨fun x => K₂' (1, x), by fun_prop⟩
  have H₁ : h.HomotopyRel f₁ (h ⁻¹' minPaths N p q) :=
    Morse.Homotopy.homotopyRelOfFun K₁ (fun x => B.deform_zero (h x)) (fun x => rfl)
      fun t x hx => hK₁fix t x hx
  have H₂ : f₁.HomotopyRel h' (h ⁻¹' minPaths N p q) :=
    Morse.Homotopy.homotopyRelOfFun ⟨K₂', hK₂'c⟩
      (fun x => if_pos (Or.inl rfl)) (fun x => rfl) fun t x hx => if_pos (Or.inr hx)
  refine ⟨h', fun x => ?_, ⟨H₁.trans H₂⟩⟩
  change K₂' (1, x) ∈ minPaths N p q
  by_cases hx : h x ∈ minPaths N p q
  · simp only [K₂', if_pos (Or.inr hx)]
    rw [hK₁fix 1 x hx]
    exact hx
  · have hne : ¬((1 : I) = 0 ∨ h x ∈ minPaths N p q) := by
      rintro (h1 | h1)
      · exact one_ne_zero h1
      · exact hx h1
    simp only [K₂', if_neg hne]
    change pS (G₂ (1, x)) ∈ minPaths N p q
    rw [G₂.apply_one, hmin_iff]
    change energy (B.path (h₃ x).1) 0 1 ≤ d
    rw [B.energy_path (hOU (h₃ x).2), ← hfE]
    exact hh₃ x

/-- The inclusion `Ω^d → Ω`. -/
def minPathsIncl (N : Set V) (p q : V) : C(minPaths N p q, PathSp N p q) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- **Theorem 22.1 as a compression**: under the hypotheses of `Morse.theorem_22_1`, the inclusion
`Ω^d → Ω` compresses maps from every compact `P` embedded in a real vector space of dimension
`< λ₀` (`Morse.Homotopy.Compresses`). -/
theorem compresses_minPaths (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {p q : V}
    (hp : p ∈ N) (hq : q ∈ N) (hball : ∀ r : ℝ, IsCompact (closedRiemBall N p r)) {l₀ : ℕ}
    (hidx : ∀ γ (hγ : γ ∈ pathSpace N p q), IsUnbrokenGeodesic hN γ →
      (∃ γ' ∈ pathSpace N p q, energy γ' 0 1 < energy γ 0 1) →
      (l₀ : ℕ∞) ≤ formIndex (energyHessian hN hγ))
    (hretr : ∃ O : Set (PathSp N p q), IsOpen O ∧ minPaths N p q ⊆ O ∧
      ∃ ρ : PathSp N p q → PathSp N p q, ContinuousOn ρ O ∧ (∀ γ ∈ O, ρ γ ∈ minPaths N p q) ∧
        ∀ γ ∈ minPaths N p q, ρ γ = γ)
    {P : Type*} [TopologicalSpace P] [CompactSpace P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hE : finrank ℝ E < l₀) {ι : P → E} (hι : Continuous ι) (hιinj : Injective ι) :
    Morse.Homotopy.Compresses (minPathsIncl N p q) P := by
  intro f
  obtain ⟨g, hg, hfg⟩ := theorem_22_1 hN hp hq hball hidx hretr hE hι hιinj f fun _ => trivial
  have hr : range (minPathsIncl N p q) = minPaths N p q := Subtype.range_coe
  rw [hr]
  exact ⟨g, hg, hfg⟩

/-- **Milnor's corollary of Theorem 22.1** (p. 118): the inclusion `Ω^d → Ω` induces a bijection
`π_i(Ω^d, γ) → π_i(Ω, γ)` for `i ≤ λ₀ − 2` (`i = |K|`), at every `γ ∈ Ω^d`. -/
theorem theorem_22_1_bijective (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {p q : V}
    (hp : p ∈ N) (hq : q ∈ N) (hball : ∀ r : ℝ, IsCompact (closedRiemBall N p r)) {l₀ : ℕ}
    (hidx : ∀ γ (hγ : γ ∈ pathSpace N p q), IsUnbrokenGeodesic hN γ →
      (∃ γ' ∈ pathSpace N p q, energy γ' 0 1 < energy γ 0 1) →
      (l₀ : ℕ∞) ≤ formIndex (energyHessian hN hγ))
    (hretr : ∃ O : Set (PathSp N p q), IsOpen O ∧ minPaths N p q ⊆ O ∧
      ∃ ρ : PathSp N p q → PathSp N p q, ContinuousOn ρ O ∧ (∀ γ ∈ O, ρ γ ∈ minPaths N p q) ∧
        ∀ γ ∈ minPaths N p q, ρ γ = γ)
    {K : Type*} [Fintype K] (hK : Fintype.card K + 2 ≤ l₀) (γ : minPaths N p q) :
    Bijective (Morse.Homotopy.homotopyGroupMap (N := K) (minPathsIncl N p q) γ) := by
  refine ⟨Morse.Homotopy.injective_homotopyGroupMap_of_compresses
    Topology.IsEmbedding.subtypeVal ?_ γ, Morse.Homotopy.surjective_homotopyGroupMap_of_compresses
    Topology.IsEmbedding.subtypeVal ?_ γ⟩
  · exact compresses_minPaths hN hp hq hball hidx hretr (E := ℝ × (K → ℝ))
      (by rw [Module.finrank_prod, Module.finrank_self, Module.finrank_fintype_fun_eq_card]
          omega) Morse.Homotopy.continuous_cylEmb Morse.Homotopy.injective_cylEmb
  · exact compresses_minPaths hN hp hq hball hidx hretr (E := K → ℝ)
      (by rw [Module.finrank_fintype_fun_eq_card]; omega) Morse.Homotopy.continuous_cubeEmb
      Morse.Homotopy.injective_cubeEmb

/-- **Milnor's corollary, surjectivity**: `π_i(Ω^d, γ) → π_i(Ω, γ)` is onto for `i ≤ λ₀ − 1`. -/
theorem theorem_22_1_surjective (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {p q : V}
    (hp : p ∈ N) (hq : q ∈ N) (hball : ∀ r : ℝ, IsCompact (closedRiemBall N p r)) {l₀ : ℕ}
    (hidx : ∀ γ (hγ : γ ∈ pathSpace N p q), IsUnbrokenGeodesic hN γ →
      (∃ γ' ∈ pathSpace N p q, energy γ' 0 1 < energy γ 0 1) →
      (l₀ : ℕ∞) ≤ formIndex (energyHessian hN hγ))
    (hretr : ∃ O : Set (PathSp N p q), IsOpen O ∧ minPaths N p q ⊆ O ∧
      ∃ ρ : PathSp N p q → PathSp N p q, ContinuousOn ρ O ∧ (∀ γ ∈ O, ρ γ ∈ minPaths N p q) ∧
        ∀ γ ∈ minPaths N p q, ρ γ = γ)
    {K : Type*} [Fintype K] (hK : Fintype.card K < l₀) (γ : minPaths N p q) :
    Surjective (Morse.Homotopy.homotopyGroupMap (N := K) (minPathsIncl N p q) γ) :=
  Morse.Homotopy.surjective_homotopyGroupMap_of_compresses Topology.IsEmbedding.subtypeVal
    (compresses_minPaths hN hp hq hball hidx hretr (E := K → ℝ)
      (by rw [Module.finrank_fintype_fun_eq_card]; omega) Morse.Homotopy.continuous_cubeEmb
      Morse.Homotopy.injective_cubeEmb) γ

end Morse
