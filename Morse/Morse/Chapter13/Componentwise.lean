import Morse.Chapter13.Theorem22
import Morse.Homotopy.BundlesUnitary

/-!
Milnor, *Morse Theory*, §22, Theorem 22.1 (pp. 118, 122–123), as used one component at a time in
§24 (p. 147); Exposition/Chapter15.md, §6, Lemma 6.2.

# Theorem 22.1 componentwise (Lemma 6.2)

## Milnor's text, paraphrased

(p. 147, case `k ≡ 2 (mod 4)`) "We will need a variant of Theorem 22.1 for the component
`Ω^{(c)}` of the path space": the proof of Theorem 22.1 applies verbatim to an open and closed
subset `Ω'` of `Ω(M; p, q)`, provided the index hypothesis holds for the non-minimal geodesics in
`Ω'`.  (Exposition, Lemma 6.2: `π_i(Ω', Ω' ∩ Ω^d) = 0` for `0 ≤ i < λ₀`.)

## What is formalized

In the setting of `Morse.theorem_22_1` (a slice submanifold `N`, compact closed balls about `p`,
`Ω^d` a neighbourhood retract), for an open and closed `Ω' ⊆ Ω = Ω(N; p, q)`:

* `Morse.PathSp.mem_of_edist_eq_zero`: open sets of `Ω` are saturated for Milnor's pseudometric.
* **`Morse.theorem_22_1_clopen`** (Lemma 6.2): if every geodesic in `Ω'` which is not of least
  energy has index `≥ λ₀`, then every map from a compact `P` embedded in a real vector space of
  dimension `< λ₀` into `Ω'` is homotopic, relative to the preimage of `Ω^d ∩ Ω'`, to a map into
  `Ω^d ∩ Ω'`.
* `Morse.theorem_22_1_clopen_bijective` (**the corollary on p. 118, componentwise**): the inclusion
  `Ω^d ∩ Ω' → Ω'` is bijective on `π_i` for `i ≤ λ₀ − 2` (including `π_0`), at every point;
  `Morse.theorem_22_1_clopen_bijective_minPathsIncl`: the inclusion `Ω^d → Ω` is bijective on
  `π_i`, `1 ≤ i ≤ λ₀ − 2`, at the points of `Ω^d ∩ Ω'`.

## What Milnor leaves implicit

* The three places where the proof of Theorem 22.1 has to see `Ω'`: (1) Milnor's deformation
  `r_u` moves each path continuously, so keeps it in `Ω'`; (2) the manifold `B` of broken
  geodesics is cut down to the open set of break points whose broken geodesic lies in `Ω'` (the
  broken geodesic depends continuously on its break points), still a slice submanifold of
  `N^m`, with compact sublevel sets since `Ω'` is closed; (3) the last homotopy, inside this
  manifold, stays in `Ω'`.
* `d` is the least energy on all of `Ω`; no hypothesis "`Ω'` contains a minimal geodesic" is
  needed (if it contains none, its minimum is a non-minimal geodesic of index `0`, so the index
  hypothesis forces `λ₀ = 0` and the statement is empty).
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold unitInterval ENNReal

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V}

omit [FiniteDimensional ℝ V] in
/-- **Open sets of `Ω` are saturated** for Milnor's pseudometric. -/
theorem PathSp.mem_of_edist_eq_zero {p q : V} {U : Set (PathSp N p q)} (hU : IsOpen U)
    {α β : PathSp N p q} (h : edist α β = 0) (hα : α ∈ U) : β ∈ U := by
  obtain ⟨ε, hε, hball⟩ := EMetric.isOpen_iff.1 hU α hα
  exact hball (by rw [Metric.mem_eball, edist_comm, h]; exact hε)

/-- A path in a space stays in an open and closed set containing its start. -/
theorem mem_of_isClopen_of_continuous {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsClopen s) {f : I → X} (hf : Continuous f) (h0 : f 0 ∈ s) (t : I) : f t ∈ s :=
  Morse.Homotopy.range_subset_of_isClopen hs ⟨f, hf⟩ 0 h0 (mem_range_self t)

/-- **Lemma 6.2: Theorem 22.1 for an open and closed set of paths** (Milnor p. 147, with
pp. 122–123): see the module docstring. -/
theorem theorem_22_1_clopen (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {p q : V}
    (hp : p ∈ N) (hq : q ∈ N) (hball : ∀ r : ℝ, IsCompact (closedRiemBall N p r))
    {Ω' : Set (PathSp N p q)} (hΩ' : IsClopen Ω') {l₀ : ℕ}
    (hidx : ∀ γ (hγ : γ ∈ pathSpace N p q), (⟨γ, hγ⟩ : PathSp N p q) ∈ Ω' →
      IsUnbrokenGeodesic hN γ →
      (∃ γ' ∈ pathSpace N p q, energy γ' 0 1 < energy γ 0 1) →
      (l₀ : ℕ∞) ≤ formIndex (energyHessian hN hγ))
    (hretr : ∃ O : Set (PathSp N p q), IsOpen O ∧ minPaths N p q ⊆ O ∧
      ∃ ρ : PathSp N p q → PathSp N p q, ContinuousOn ρ O ∧ (∀ γ ∈ O, ρ γ ∈ minPaths N p q) ∧
        ∀ γ ∈ minPaths N p q, ρ γ = γ)
    {P : Type*} [TopologicalSpace P] [CompactSpace P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hE : finrank ℝ E < l₀) {ι : P → E} (hι : Continuous ι) (hιinj : Injective ι) :
    PushesInto P (minPaths N p q ∩ Ω') Ω' := by
  classical
  intro h hhΩ
  have hpre : h ⁻¹' (minPaths N p q ∩ Ω') = h ⁻¹' minPaths N p q := by
    ext x; exact ⟨fun hx => hx.1, fun hx => ⟨hx, hhΩ x⟩⟩
  rw [hpre]
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
  -- Step 2: Milnor's deformation `r_u`, which keeps paths in `Ω'`
  let K₁ : C(I × P, PathSp N p q) := ⟨fun z => B.deform z.1 (h z.2),
    B.continuousOn_deform.comp_continuous (f := fun z : I × P => ((z.1 : ℝ), h z.2))
      (by fun_prop) fun z => ⟨z.1.2, show energy (h z.2) 0 1 < c by linarith [hhc₀ z.2]⟩⟩
  have hK₁Ω : ∀ t x, K₁ (t, x) ∈ Ω' := fun t x =>
    mem_of_isClopen_of_continuous hΩ' (f := fun t => K₁ (t, x)) (by fun_prop)
      (by change B.deform ((0 : I) : ℝ) (h x) ∈ Ω'; rw [Set.Icc.coe_zero, B.deform_zero]
          exact hhΩ x) t
  have hK₁E : ∀ x, energy (K₁ (1, x)) 0 1 ≤ c₀ := fun x =>
    (B.energy_deform_le _ _).trans (hhc₀ x)
  have hK₁B : ∀ x, (K₁ (1, x) : ℝ → V) ∈ B.brokenPaths := fun x =>
    B.deform_one_mem_brokenPaths (show energy (h x) 0 1 < c by linarith [hhc₀ x])
  have hK₁fix : ∀ t x, h x ∈ minPaths N p q → K₁ (t, x) = h x := fun t x hx =>
    B.deform_of_mem_brokenPaths t.2 (hminB _ hx)
  -- Step 3: the manifold `S` of break points with energy `< c₁` and broken geodesic in `Ω'`
  set c₁ := c₀ + 2 with hc₁_def
  obtain ⟨F, hF, hFE⟩ := B.exists_contDiff_eq_energy' (b := c₁ + 1 / 2) (by linarith)
  obtain ⟨O, hO, hOeq⟩ := B.exists_isOpen_sublevel_lt c₁
  obtain ⟨O'', hO'', hO''eq⟩ := isOpen_induced_iff.1 (hΩ'.isOpen.preimage B.continuous_pathP)
  have hO''mem : ∀ y (hy : y ∈ B.nodes), y ∈ O'' ↔ B.pathP ⟨y, hy⟩ ∈ Ω' := fun y hy =>
    Set.ext_iff.1 hO''eq ⟨y, hy⟩
  set S := (Set.pi univ fun _ => N) ∩ (O ∩ O'') with hS_def
  have hSmem : ∀ y, y ∈ S ↔ ∃ hy : y ∈ B.nodes, B.energy' y < c₁ ∧ B.pathP ⟨y, hy⟩ ∈ Ω' := by
    intro y
    have h1 := Set.ext_iff.1 hOeq y
    simp only [mem_ofPred_eq, mem_inter_iff] at h1
    constructor
    · rintro ⟨hpi, hyO, hyO''⟩
      obtain ⟨hy, hyc⟩ := h1.2 ⟨hpi, hyO⟩
      exact ⟨hy, hyc, (hO''mem y hy).1 hyO''⟩
    · rintro ⟨hy, hyc, hyΩ⟩
      obtain ⟨hpi, hyO⟩ := h1.1 ⟨hy, hyc⟩
      exact ⟨hpi, hyO, (hO''mem y hy).2 hyΩ⟩
  have hO : IsOpen (O ∩ O'') := hO.inter hO''
  have hOU : S ⊆ B.nodes := fun y hy => ((hSmem y).1 hy).1
  have hSΩ : ∀ y : S, B.pathP ⟨y.1, hOU y.2⟩ ∈ Ω' := fun y => ((hSmem y).1 y.2).2.2
  have hFE' : ∀ y ∈ S, F y = B.energy' y := fun y hy =>
    hFE y ⟨((hSmem y).1 hy).1, by linarith [((hSmem y).1 hy).2.1]⟩
  set hSm := isSliceSubmanifold_pi_inter hN hO
  let _ := hSm.chartedSpace
  set f : S → ℝ := F ∘ Subtype.val with hf_def
  have hfE : ∀ y : S, f y = B.energy' y := fun y => hFE' y y.2
  have hnodes : ∀ x, B.nodeVal (K₁ (1, x)) ∈ S := fun x => by
    obtain ⟨h1, h2⟩ := B.nodeVal_mem_nodes_of_energy_lt (K₁ (1, x)).mem
      (show energy (K₁ (1, x)) 0 1 < c by linarith [hK₁E x])
    refine (hSmem _).2 ⟨h1, by linarith [hK₁E x], ?_⟩
    refine PathSp.mem_of_edist_eq_zero hΩ'.isOpen ?_ (hK₁Ω 1 x)
    rw [edist_comm]
    exact PathSp.edist_eq_zero_of_eqOn ((B.lemma_16_1).2 _ (hK₁B x)).2
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
    set Ka := {y | y ∈ B.nodes ∧ B.energy' y ≤ a₀} with hKa_def
    have hKa : IsCompact Ka := B.isCompact_sublevel (by linarith)
    have : CompactSpace Ka := isCompact_iff_compactSpace.1 hKa
    let g : Ka → PathSp N p q := fun y => B.pathP ⟨y.1, y.2.1⟩
    have hg : Continuous g :=
      B.continuous_pathP.comp (continuous_subtype_val.subtype_mk _)
    have hc : IsCompact (Subtype.val '' (g ⁻¹' Ω')) :=
      ((hΩ'.isClosed.preimage hg).isCompact).image continuous_subtype_val
    have hBa : Subtype.val '' (f ⁻¹' Iic a₀) = Subtype.val '' (g ⁻¹' Ω') := by
      ext y
      simp only [mem_image, mem_preimage, mem_Iic]
      constructor
      · rintro ⟨y', hy', rfl⟩
        exact ⟨⟨y'.1, hOU y'.2, by rw [← hfE]; exact hy'⟩, hSΩ y', rfl⟩
      · rintro ⟨y', hy', rfl⟩
        have hyS : y'.1 ∈ S := (hSmem _).2 ⟨y'.2.1, by linarith [y'.2.2], hy'⟩
        exact ⟨⟨y'.1, hyS⟩, by rw [hfE]; exact y'.2.2, rfl⟩
    rw [Topology.IsInducing.subtypeVal.isCompact_iff, hBa]
    exact hc
  have hidx' : ∀ y : S, IsCriticalPointM (Fin m → Z) f y → d < F y → F y < a₀ →
      l₀ ≤ indexM (Fin m → Z) f y := by
    intro y hc hdy _
    have hgeo := (B.isCriticalPointM_iff hO hOU hF hFE' y).1 hc
    have hidxeq := (B.theorem_16_2_index hO hOU hF hFE' y hgeo).1
    have hnonmin : ∃ γ' ∈ pathSpace N p q, energy γ' 0 1 < energy (B.path y) 0 1 :=
      ⟨B.path y₀, B.path_mem_pathSpace hy₀, by
        rw [B.energy_path hy₀, B.energy_path (hOU y.2), ← hfE]; exact hdy⟩
    have := hidx _ (B.path_mem_pathSpace (hOU y.2)) (hSΩ y) hgeo hnonmin
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
  change K₂' (1, x) ∈ minPaths N p q ∩ Ω'
  by_cases hx : h x ∈ minPaths N p q
  · simp only [K₂', if_pos (Or.inr hx)]
    rw [hK₁fix 1 x hx]
    exact ⟨hx, hhΩ x⟩
  · have hne : ¬((1 : I) = 0 ∨ h x ∈ minPaths N p q) := by
      rintro (h1 | h1)
      · exact one_ne_zero h1
      · exact hx h1
    simp only [K₂', if_neg hne]
    change pS (G₂ (1, x)) ∈ minPaths N p q ∩ Ω'
    refine ⟨?_, hSΩ _⟩
    rw [G₂.apply_one, hmin_iff]
    change energy (B.path (h₃ x).1) 0 1 ≤ d
    rw [B.energy_path (hOU (h₃ x).2), ← hfE]
    exact hh₃ x

/-! ### Homotopy groups -/

section Generic

variable {X : Type*} [TopologicalSpace X] {A Ω' : Set X}

variable (A Ω') in
/-- The inclusion `A ∩ Ω' → Ω'`. -/
def clopenIncl : C({y : A | (y : X) ∈ Ω'}, Ω') :=
  ⟨fun y => ⟨y.1.1, y.2⟩, (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

theorem isEmbedding_clopenIncl : Topology.IsEmbedding (clopenIncl A Ω') := by
  have h : Topology.IsEmbedding ((Subtype.val : Ω' → X) ∘ clopenIncl A Ω') :=
    (Topology.IsEmbedding.subtypeVal (p := (· ∈ A))).comp
      (Topology.IsEmbedding.subtypeVal (p := fun y : A => (y : X) ∈ Ω'))
  exact (Topology.IsEmbedding.of_comp_iff Topology.IsEmbedding.subtypeVal).1 h

theorem mem_range_clopenIncl {x : Ω'} : x ∈ range (clopenIncl A Ω') ↔ (x : X) ∈ A :=
  ⟨fun ⟨y, hy⟩ => hy ▸ y.1.2, fun hx => ⟨⟨⟨x.1, hx⟩, x.2⟩, rfl⟩⟩

/-- Pushing maps into `A ∩ Ω'` inside `X` is compressing them along `A ∩ Ω' → Ω'`: the
homotopies start in the open and closed `Ω'` and stay there. -/
theorem compresses_clopenIncl (hΩ' : IsClopen Ω') {P : Type*} [TopologicalSpace P]
    (h : PushesInto P (A ∩ Ω') Ω') : Morse.Homotopy.Compresses (clopenIncl A Ω') P := by
  intro f
  obtain ⟨g, hg, ⟨F⟩⟩ := h ((ContinuousMap.mk Subtype.val continuous_subtype_val).comp f)
    fun x => (f x).2
  have hF : ∀ t x, F (t, x) ∈ Ω' := fun t x =>
    mem_of_isClopen_of_continuous hΩ' (f := fun t => F (t, x)) (by fun_prop)
      (by rw [F.apply_zero]; exact (f x).2) t
  let G : C(P, Ω') := ⟨fun x => ⟨g x, (hg x).2⟩, g.continuous.subtype_mk _⟩
  refine ⟨G, fun x => mem_range_clopenIncl.2 (hg x).1, ⟨Morse.Homotopy.homotopyRelOfFun
    ⟨fun z => ⟨F z, hF z.1 z.2⟩, F.continuous.subtype_mk _⟩
    (fun x => Subtype.ext (F.apply_zero x)) (fun x => Subtype.ext (F.apply_one x))
    fun t x hx => Subtype.ext (F.eq_fst t ⟨mem_range_clopenIncl.1 hx, (f x).2⟩)⟩⟩

variable {N : Type*}

/-- **Pushing gives bijections** of `π_N(A ∩ Ω') → π_N(Ω')`. -/
theorem bijective_clopenIncl (hΩ' : IsClopen Ω') (h₁ : PushesInto (I^N) (A ∩ Ω') Ω')
    (h₂ : PushesInto (I × I^N) (A ∩ Ω') Ω') (y : {y : A | (y : X) ∈ Ω'}) :
    Bijective (Morse.Homotopy.homotopyGroupMap (N := N) (clopenIncl A Ω') y) :=
  ⟨Morse.Homotopy.injective_homotopyGroupMap_of_compresses isEmbedding_clopenIncl
    (compresses_clopenIncl hΩ' h₂) y,
   Morse.Homotopy.surjective_homotopyGroupMap_of_compresses isEmbedding_clopenIncl
    (compresses_clopenIncl hΩ' h₁) y⟩

/-- **Pushing gives bijections** of `π_N(A) → π_N(X)` at the points of `A ∩ Ω'`, for `N`
nonempty (`Ω'` carries the homotopy groups of `X` at its points). -/
theorem bijective_val_of_pushesInto [Nonempty N] (hΩ' : IsClopen Ω')
    (h₁ : PushesInto (I^N) (A ∩ Ω') Ω') (h₂ : PushesInto (I × I^N) (A ∩ Ω') Ω') (y : A)
    (hy : (y : X) ∈ Ω') :
    Bijective (Morse.Homotopy.homotopyGroupMap (N := N)
      (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)) y) := by
  have hY : IsClopen {y : A | (y : X) ∈ Ω'} := hΩ'.preimage continuous_subtype_val
  have hb : Bijective (Morse.Homotopy.homotopyGroupMap (N := N)
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C({y : A | (y : X) ∈ Ω'}, A))) ⟨y, hy⟩) := by
    have h3 : Bijective (Morse.Homotopy.homotopyGroupMap (N := N)
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(Ω', X)).comp (clopenIncl A Ω')) ⟨y, hy⟩) := by
      rw [Morse.Homotopy.homotopyGroupMap_comp]
      exact (Morse.Homotopy.bijective_homotopyGroupMap_clopen hΩ' (x := (y : X)) hy).comp
        (bijective_clopenIncl hΩ' h₁ h₂ ⟨y, hy⟩)
    exact h3
  rw [Morse.Homotopy.homotopyGroupMap_comp] at hb
  exact (Bijective.of_comp_iff _
    (Morse.Homotopy.bijective_homotopyGroupMap_clopen hY (x := y) hy)).1 hb

end Generic

section Minimal

variable (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {p q : V} (hp : p ∈ N) (hq : q ∈ N)
  (hball : ∀ r : ℝ, IsCompact (closedRiemBall N p r))
  {Ω' : Set (PathSp N p q)} (hΩ' : IsClopen Ω') {l₀ : ℕ}
  (hidx : ∀ γ (hγ : γ ∈ pathSpace N p q), (⟨γ, hγ⟩ : PathSp N p q) ∈ Ω' →
      IsUnbrokenGeodesic hN γ →
      (∃ γ' ∈ pathSpace N p q, energy γ' 0 1 < energy γ 0 1) →
      (l₀ : ℕ∞) ≤ formIndex (energyHessian hN hγ))
  (hretr : ∃ O : Set (PathSp N p q), IsOpen O ∧ minPaths N p q ⊆ O ∧
      ∃ ρ : PathSp N p q → PathSp N p q, ContinuousOn ρ O ∧ (∀ γ ∈ O, ρ γ ∈ minPaths N p q) ∧
        ∀ γ ∈ minPaths N p q, ρ γ = γ)
  {K : Type*} [Fintype K] (hK : Fintype.card K + 2 ≤ l₀)
include hp hq hball hΩ' hidx hretr hK

theorem pushesInto_cube_clopen : PushesInto (I^K) (minPaths N p q ∩ Ω') Ω' :=
  theorem_22_1_clopen hN hp hq hball hΩ' hidx hretr (E := K → ℝ)
    (by rw [Module.finrank_fintype_fun_eq_card]; omega) Morse.Homotopy.continuous_cubeEmb
    Morse.Homotopy.injective_cubeEmb

theorem pushesInto_cyl_clopen : PushesInto (I × I^K) (minPaths N p q ∩ Ω') Ω' :=
  theorem_22_1_clopen hN hp hq hball hΩ' hidx hretr (E := ℝ × (K → ℝ))
    (by rw [Module.finrank_prod, Module.finrank_self, Module.finrank_fintype_fun_eq_card]
        omega) Morse.Homotopy.continuous_cylEmb Morse.Homotopy.injective_cylEmb

/-- **Milnor's corollary of Theorem 22.1, componentwise** (Lemma 6.2): the inclusion
`Ω^d ∩ Ω' → Ω'` induces bijections on `π_i` for `i ≤ λ₀ − 2` (including `π_0`). -/
theorem theorem_22_1_clopen_bijective
    (γ : {γ : minPaths N p q | (γ : PathSp N p q) ∈ Ω'}) :
    Bijective (Morse.Homotopy.homotopyGroupMap (N := K) (clopenIncl (minPaths N p q) Ω') γ) :=
  bijective_clopenIncl hΩ' (pushesInto_cube_clopen hN hp hq hball hΩ' hidx hretr hK)
    (pushesInto_cyl_clopen hN hp hq hball hΩ' hidx hretr hK) γ

/-- **Lemma 6.2 in `Ω`**: the inclusion `Ω^d → Ω` induces bijections on `π_i`,
`1 ≤ i ≤ λ₀ − 2`, at every minimal geodesic in `Ω'`. -/
theorem theorem_22_1_clopen_bijective_minPathsIncl [Nonempty K] (γ : minPaths N p q)
    (hγ : (γ : PathSp N p q) ∈ Ω') :
    Bijective (Morse.Homotopy.homotopyGroupMap (N := K) (minPathsIncl N p q) γ) :=
  bijective_val_of_pushesInto hΩ' (pushesInto_cube_clopen hN hp hq hball hΩ' hidx hretr hK)
    (pushesInto_cyl_clopen hN hp hq hball hΩ' hidx hretr hK) γ hγ

end Minimal

end Morse
