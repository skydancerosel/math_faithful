import Morse.Chapter1.ManifoldMorse

/-!
Milnor, *Morse Theory*, §4, p. 25 (proof of Theorem 4.1, Reeb), with §2, Lemma 2.2 (p. 6).

# Morse charts at a minimum and at a maximum; small sublevel sets are closed balls

## Milnor's text, paraphrased

In the proof of Reeb's theorem Milnor says that the two critical points must be the minimum and
the maximum, normalizes `f(p) = 0` at the minimum `p` and `f(q) = 1` at the maximum `q`, and
asserts that for `ε` small enough the sets `M^ε = f⁻¹[0, ε]` and `f⁻¹[1 - ε, 1]` are closed
`n`-cells by the Lemma of Morse (Lemma 2.2).

## What is proved here

For a manifold `M` modelled on a finite-dimensional real normed space `E`, `n = dim E`:

* `Morse.isCriticalPointM_of_isLocalMin`, `Morse.isCriticalPointM_of_isLocalMax`: extrema are
  critical points (Fermat; read in a chart).  No differentiability is needed.
* `Morse.indexM_eq_zero_of_isLocalMin`, `Morse.indexM_eq_finrank_of_isLocalMax`: **a
  non-degenerate local minimum has index `0`, a non-degenerate local maximum index `n`.**  In a
  Morse chart, along an axis with a minus sign `f(y⁻¹(s eᵢ)) = f(p) - s²`, and along an axis
  with a plus sign `f(p) + s²` (`Morse.tendsto_and_eventually_morse_axis`).
* `Morse.exists_morse_chart_of_isLocalMin`, `Morse.exists_morse_chart_of_isLocalMax`: hence
  Lemma 2.2 gives smooth coordinates `y` with values in `EuclideanSpace ℝ (Fin n)`, `y(p) = 0`, in
  which `f = f(p) + ‖y‖²` (at a minimum), resp. `f = f(p) - ‖y‖²` (at a maximum).
* `Morse.exists_image_closedBall_eq_sublevel` (point-set topology): if the space is compact, `f`
  is continuous, `p` is the **unique** minimum and `f = f(p) + ‖y‖²` in a chart `y` around `p`,
  then for every small `ε > 0` the map `v ↦ y⁻¹(√ε v)` is continuous and injective on the closed
  unit ball, maps it onto the whole sublevel set `{f ≤ f(p) + ε}`, and maps the unit sphere onto
  the level set `{f = f(p) + ε}`.  (Applied to `-f`, the same holds for `{f ≥ f(q) - ε}` at the
  maximum.)

## What Milnor leaves implicit

* **The indices.**  Lemma 2.2 writes `f = f(p) - y₁² - ⋯ - y_λ² + y_{λ+1}² + ⋯ + yₙ²` with `λ` the
  index; the set `f ≤ f(p) + ε` is a cell near `p` only for `λ = 0`.  That a minimum has index `0`
  and a maximum index `n` is used without comment.
* **The whole sublevel set lies in the chart.**  Lemma 2.2 only describes `f` near `p`; that
  *all* of `f⁻¹[0, ε]` is the small coordinate ball needs compactness and the uniqueness of the
  minimum: off a coordinate ball of radius `r`, `f ≥ f(p) + η` for some `η > 0`, and then any
  `ε < min(r², η)` will do.  This is Milnor's "if `ε` is small enough".
* **The boundary.**  The gluing at the end of the proof needs more than "closed `n`-cell": the
  parametrization of the cell carries the boundary sphere onto the level set `f⁻¹(ε)`.
* **Round balls.**  Lemma 2.2 is formalized with coordinates in `ℝⁿ = Fin n → ℝ`, whose Mathlib
  norm is the sup norm; the sublevel sets are round balls for the Euclidean norm, so the
  coordinates are composed with the identification `Fin n → ℝ ≃ EuclideanSpace ℝ (Fin n)`.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold

noncomputable section

namespace Morse

/-! ### Extrema are critical points -/

section Extremum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

variable (E) in
/-- A local minimum of `f` is a local minimum of its local representative. -/
theorem isLocalMin_localRep {f : M → ℝ} {p : M} (h : IsLocalMin f p) :
    IsLocalMin (localRep E f p) (extChartAt 𝓘(ℝ, E) p p) := by
  have ht : Tendsto (extChartAt 𝓘(ℝ, E) p).symm (𝓝 (extChartAt 𝓘(ℝ, E) p p)) (𝓝 p) := by
    have := continuousAt_extChartAt_symm (I := 𝓘(ℝ, E)) p
    rwa [ContinuousAt, extChartAt_to_inv] at this
  have hval : localRep E f p (extChartAt 𝓘(ℝ, E) p p) = f p := by
    simp only [localRep, comp_apply, extChartAt_to_inv]
  change ∀ᶠ u in 𝓝 _, _ ≤ _
  filter_upwards [ht.eventually h] with u hu
  rw [hval]
  exact hu

variable (E) in
/-- A local maximum of `f` is a local maximum of its local representative. -/
theorem isLocalMax_localRep {f : M → ℝ} {p : M} (h : IsLocalMax f p) :
    IsLocalMax (localRep E f p) (extChartAt 𝓘(ℝ, E) p p) := by
  have ht : Tendsto (extChartAt 𝓘(ℝ, E) p).symm (𝓝 (extChartAt 𝓘(ℝ, E) p p)) (𝓝 p) := by
    have := continuousAt_extChartAt_symm (I := 𝓘(ℝ, E)) p
    rwa [ContinuousAt, extChartAt_to_inv] at this
  have hval : localRep E f p (extChartAt 𝓘(ℝ, E) p p) = f p := by
    simp only [localRep, comp_apply, extChartAt_to_inv]
  change ∀ᶠ u in 𝓝 _, _ ≤ _
  filter_upwards [ht.eventually h] with u hu
  rw [hval]
  exact hu

/-- **A local minimum is a critical point** (Fermat).  No differentiability is needed: where `f`
is not differentiable its derivative is `0` by convention. -/
theorem isCriticalPointM_of_isLocalMin {f : M → ℝ} {p : M} (h : IsLocalMin f p) :
    IsCriticalPointM E f p :=
  isCriticalPointM_iff_fderiv.2 (isLocalMin_localRep E h).fderiv_eq_zero

/-- **A local maximum is a critical point** (Fermat). -/
theorem isCriticalPointM_of_isLocalMax {f : M → ℝ} {p : M} (h : IsLocalMax f p) :
    IsCriticalPointM E f p :=
  isCriticalPointM_iff_fderiv.2 (isLocalMax_localRep E h).fderiv_eq_zero

end Extremum

/-! ### The index at a non-degenerate minimum or maximum -/

section Index

/-- Milnor's normal form along the `i`-th coordinate axis: `c - s²` if the `i`-th square has a
minus sign, `c + s²` otherwise. -/
theorem morseNormalForm_single {n : ℕ} (c : ℝ) (k : ℕ) (i : Fin n) (s : ℝ) :
    morseNormalForm c k (Pi.single i s) = if (i : ℕ) < k then c - s ^ 2 else c + s ^ 2 := by
  have hsq : ∀ j, (Pi.single i s : Fin n → ℝ) j ^ 2 = (Pi.single i (s ^ 2) : Fin n → ℝ) j := by
    intro j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Pi.single_eq_of_ne hj]
  simp only [morseNormalForm, hsq, Finset.sum_pi_single', Finset.mem_filter, Finset.mem_univ,
    true_and]
  split_ifs with h1 h2 <;> first | omega | ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- **Along a coordinate axis of a Morse chart.**  If `f = f(p) − y₀² − ⋯ − y_{k−1}² + y_k² + ⋯`
on the source of `y`, `y(p) = 0`, then `y⁻¹(s eᵢ) → p` as `s → 0`, and for small `s`,
`f(y⁻¹(s eᵢ)) = f(p) − s²` if `i < k` and `f(p) + s²` otherwise. -/
theorem tendsto_and_eventually_morse_axis {f : M → ℝ} {p : M} {n : ℕ}
    (y : OpenPartialHomeomorph M (Fin n → ℝ)) (hp : p ∈ y.source) (hy0 : y p = 0) {k : ℕ}
    (hfy : ∀ x ∈ y.source, f x = morseNormalForm (f p) k (y x)) (i : Fin n) :
    Tendsto (fun s : ℝ => y.symm (Pi.single i s)) (𝓝 0) (𝓝 p) ∧
      ∀ᶠ s in 𝓝 (0 : ℝ), f (y.symm (Pi.single i s)) =
        if (i : ℕ) < k then f p - s ^ 2 else f p + s ^ 2 := by
  have h0 : (0 : Fin n → ℝ) ∈ y.target := hy0 ▸ y.map_source hp
  have hT : Tendsto (fun s : ℝ => (Pi.single i s : Fin n → ℝ)) (𝓝 0) (𝓝 0) := by
    have : Continuous fun s : ℝ => (Pi.single i s : Fin n → ℝ) :=
      continuous_single (A := fun _ => ℝ) i
    simpa using this.tendsto 0
  have hTt : ∀ᶠ s in 𝓝 (0 : ℝ), (Pi.single i s : Fin n → ℝ) ∈ y.target :=
    hT.eventually (y.open_target.mem_nhds h0)
  refine ⟨?_, ?_⟩
  · have h := (y.continuousAt_symm h0).tendsto.comp hT
    rwa [← hy0, y.left_inv hp] at h
  · filter_upwards [hTt] with s hs
    rw [hfy _ (y.map_target hs), y.right_inv hs, morseNormalForm_single]

/-- The Euclidean norm on `ℝⁿ = Fin n → ℝ`. -/
theorem norm_sq_toLp {n : ℕ} (v : Fin n → ℝ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ ^ 2 = ∑ i, v i ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]

/-- A Morse chart followed by the identification `ℝⁿ ≃ EuclideanSpace ℝ (Fin n)` is a smooth
coordinate system. -/
theorem IsSmoothCoord.transHomeomorph_euclidean {n : ℕ}
    {y : OpenPartialHomeomorph M (Fin n → ℝ)} (hy : IsSmoothCoord E y) :
    IsSmoothCoord E (y.transHomeomorph (EuclideanSpace.equiv (Fin n) ℝ).symm.toHomeomorph) := by
  rw [OpenPartialHomeomorph.transHomeomorph_eq_trans]
  set e := (EuclideanSpace.equiv (Fin n) ℝ).symm
  refine hy.trans ?_ ?_
  · simpa using e.contDiff.contDiffOn
  · simpa using e.symm.contDiff.contDiffOn

variable [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E]

/-- **A non-degenerate local minimum has index `0`** (used by Milnor without comment in the proof
of Theorem 4.1).  In a Morse chart, if `λ ≥ 1`, then `f(y⁻¹(s e₀)) = f(p) − s² < f(p)` for small
`s ≠ 0`. -/
theorem indexM_eq_zero_of_isLocalMin {f : M → ℝ} {p : M} {U : Set M} (hU : IsOpen U)
    (hpU : p ∈ U) (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f U)
    (hp : IsNondegenerateCriticalPointM E f p) (hmin : IsLocalMin f p) : indexM E f p = 0 := by
  obtain ⟨y, -, hpy, -, hy0, hfy⟩ := morse_lemmaM hU hpU hf hp
  by_contra hk
  have hkn := indexM_le_finrank (E := E) f p
  set i : Fin (finrank ℝ E) := ⟨0, by omega⟩ with hi_def
  have hi : (i : ℕ) < indexM E f p := by
    rw [hi_def]
    simp only
    omega
  obtain ⟨ht, hev⟩ := tendsto_and_eventually_morse_axis y hpy hy0 (k := indexM E f p)
    (fun x hx => by rw [morseNormalForm]; exact hfy x hx) i
  have h1 : ∀ᶠ s in 𝓝 (0 : ℝ), f p ≤ f (y.symm (Pi.single i s)) := ht.eventually hmin
  have hfalse : ∀ᶠ s in 𝓝[≠] (0 : ℝ), False := by
    filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds hev, self_mem_nhdsWithin]
      with s hs1 hs2 hs3
    rw [hs2, if_pos hi] at hs1
    have hs : s ≠ 0 := hs3
    have : 0 < s ^ 2 := by positivity
    linarith
  obtain ⟨_, h⟩ := hfalse.exists
  exact h

/-- **A non-degenerate local maximum has index `n = dim M`** (used by Milnor without comment in
the proof of Theorem 4.1).  In a Morse chart, if `λ < n`, then `f(y⁻¹(s eₙ₋₁)) = f(p) + s² > f(p)`
for small `s ≠ 0`. -/
theorem indexM_eq_finrank_of_isLocalMax {f : M → ℝ} {p : M} {U : Set M} (hU : IsOpen U)
    (hpU : p ∈ U) (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f U)
    (hp : IsNondegenerateCriticalPointM E f p) (hmax : IsLocalMax f p) :
    indexM E f p = finrank ℝ E := by
  obtain ⟨y, -, hpy, -, hy0, hfy⟩ := morse_lemmaM hU hpU hf hp
  have hkn := indexM_le_finrank (E := E) f p
  by_contra hk
  set i : Fin (finrank ℝ E) := ⟨finrank ℝ E - 1, by omega⟩ with hi_def
  have hi : ¬ (i : ℕ) < indexM E f p := by
    rw [hi_def]
    simp only
    omega
  obtain ⟨ht, hev⟩ := tendsto_and_eventually_morse_axis y hpy hy0 (k := indexM E f p)
    (fun x hx => by rw [morseNormalForm]; exact hfy x hx) i
  have h1 : ∀ᶠ s in 𝓝 (0 : ℝ), f (y.symm (Pi.single i s)) ≤ f p := ht.eventually hmax
  have hfalse : ∀ᶠ s in 𝓝[≠] (0 : ℝ), False := by
    filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds hev, self_mem_nhdsWithin]
      with s hs1 hs2 hs3
    rw [hs2, if_neg hi] at hs1
    have hs : s ≠ 0 := hs3
    have : 0 < s ^ 2 := by positivity
    linarith
  obtain ⟨_, h⟩ := hfalse.exists
  exact h

/-! ### Morse charts at a minimum and at a maximum, in Euclidean coordinates -/

/-- **The Morse chart at a non-degenerate local minimum** (Lemma 2.2 with `λ = 0`): Euclidean
coordinates `y` around `p`, `y(p) = 0`, in which `f = f(p) + ‖y‖²`. -/
theorem exists_morse_chart_of_isLocalMin {f : M → ℝ} {p : M} {U : Set M} (hU : IsOpen U)
    (hpU : p ∈ U) (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f U)
    (hp : IsNondegenerateCriticalPointM E f p) (hmin : IsLocalMin f p) :
    ∃ y : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (finrank ℝ E))),
      IsSmoothCoord E y ∧ p ∈ y.source ∧ y.source ⊆ U ∧ y p = 0 ∧
        ∀ x ∈ y.source, f x = f p + ‖y x‖ ^ 2 := by
  obtain ⟨y, hys, hpy, hyU, hy0, hfy⟩ := morse_lemmaM hU hpU hf hp
  have hk := indexM_eq_zero_of_isLocalMin hU hpU hf hp hmin
  refine ⟨y.transHomeomorph (EuclideanSpace.equiv (Fin (finrank ℝ E)) ℝ).symm.toHomeomorph,
    hys.transHomeomorph_euclidean, hpy, hyU, ?_, fun x hx => ?_⟩
  · simp [hy0]
  · rw [hfy x hx, hk]
    simp [norm_sq_toLp]

/-- **The Morse chart at a non-degenerate local maximum** (Lemma 2.2 with `λ = n`): Euclidean
coordinates `y` around `p`, `y(p) = 0`, in which `f = f(p) − ‖y‖²`. -/
theorem exists_morse_chart_of_isLocalMax {f : M → ℝ} {p : M} {U : Set M} (hU : IsOpen U)
    (hpU : p ∈ U) (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f U)
    (hp : IsNondegenerateCriticalPointM E f p) (hmax : IsLocalMax f p) :
    ∃ y : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (finrank ℝ E))),
      IsSmoothCoord E y ∧ p ∈ y.source ∧ y.source ⊆ U ∧ y p = 0 ∧
        ∀ x ∈ y.source, f x = f p - ‖y x‖ ^ 2 := by
  obtain ⟨y, hys, hpy, hyU, hy0, hfy⟩ := morse_lemmaM hU hpU hf hp
  have hk := indexM_eq_finrank_of_isLocalMax hU hpU hf hp hmax
  refine ⟨y.transHomeomorph (EuclideanSpace.equiv (Fin (finrank ℝ E)) ℝ).symm.toHomeomorph,
    hys.transHomeomorph_euclidean, hpy, hyU, ?_, fun x hx => ?_⟩
  · simp [hy0]
  · rw [hfy x hx, hk, Finset.filter_true_of_mem fun i _ => i.2,
      Finset.filter_false_of_mem fun i _ => not_le.2 i.2]
    simp [norm_sq_toLp]

end Index

/-! ### A small sublevel set around a strict minimum is a closed ball -/

section SublevelBall

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The sublevel set `f ≤ f(p) + ε` is a closed ball for small `ε`.**  Let `X` be compact,
`f : X → ℝ` continuous with a strict global minimum at `p`, and `y` a chart around `p`
(`y(p) = 0`) in which `f = f(p) + ‖y‖²`.  Then for all small `ε > 0` the map
`v ↦ y⁻¹(√ε v)` is a homeomorphism of the closed unit ball onto `{f ≤ f(p) + ε}` (continuous and
injective on the ball, with that image) which carries the unit sphere onto the level set
`{f = f(p) + ε}`.  The point is that *the whole* sublevel set lies in the chart: off a small
coordinate ball, `f` is bounded below by `f(p) + η`, `η > 0`, by compactness and uniqueness of the
minimum. -/
theorem exists_image_closedBall_eq_sublevel {f : X → ℝ} (hf : Continuous f) {p : X}
    (hmin : ∀ x, x ≠ p → f p < f x) (y : OpenPartialHomeomorph X F) (hp : p ∈ y.source)
    (hy0 : y p = 0) (hfy : ∀ x ∈ y.source, f x = f p + ‖y x‖ ^ 2) :
    ∃ δ > 0, ∀ ε, 0 < ε → ε < δ →
      ContinuousOn (fun v => y.symm (√ε • v)) (closedBall 0 1) ∧
      InjOn (fun v => y.symm (√ε • v)) (closedBall 0 1) ∧
      (fun v => y.symm (√ε • v)) '' closedBall 0 1 = {x | f x ≤ f p + ε} ∧
      (fun v => y.symm (√ε • v)) '' sphere 0 1 = {x | f x = f p + ε} := by
  have h0 : (0 : F) ∈ y.target := hy0 ▸ y.map_source hp
  obtain ⟨r, hr, hrT⟩ := Metric.isOpen_iff.1 y.open_target 0 h0
  set U := y.source ∩ y ⁻¹' ball 0 r with hU
  have hUo : IsOpen U := y.isOpen_inter_preimage isOpen_ball
  have hpU : p ∈ U := ⟨hp, by simp [hy0, hr]⟩
  -- off `U`, `f ≥ f(p) + η`
  obtain ⟨η, hη, hηU⟩ : ∃ η > 0, ∀ x, x ∉ U → f p + η ≤ f x := by
    rcases (Uᶜ).eq_empty_or_nonempty with h | h
    · refine ⟨1, one_pos, fun x hx => ?_⟩
      have : x ∈ Uᶜ := hx
      rw [h] at this
      exact absurd this (notMem_empty x)
    · obtain ⟨x₁, hx₁, hmin₁⟩ :=
        hUo.isClosed_compl.isCompact.exists_isMinOn h hf.continuousOn
      have hx₁p : x₁ ≠ p := fun h' => hx₁ (h' ▸ hpU)
      refine ⟨f x₁ - f p, sub_pos.2 (hmin x₁ hx₁p), fun x hx => ?_⟩
      have := isMinOn_iff.1 hmin₁ x hx
      linarith
  refine ⟨min (r ^ 2) η, lt_min (by positivity) hη, fun ε hε hεδ => ?_⟩
  have hεr : √ε < r := (Real.sqrt_lt' hr).2 (lt_of_lt_of_le hεδ (min_le_left _ _))
  have hεη : ε < η := lt_of_lt_of_le hεδ (min_le_right _ _)
  have hsq : 0 < √ε := Real.sqrt_pos.2 hε
  have hmapsT : ∀ v ∈ closedBall (0 : F) 1, √ε • v ∈ y.target := by
    intro v hv
    apply hrT
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hsq.le]
    calc √ε * ‖v‖ ≤ √ε * 1 := mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hv) hsq.le
      _ < r := by rwa [mul_one]
  -- the value of `f` on the image of the ball
  have hval : ∀ v ∈ closedBall (0 : F) 1, f (y.symm (√ε • v)) = f p + ε * ‖v‖ ^ 2 := by
    intro v hv
    rw [hfy _ (y.map_target (hmapsT v hv)), y.right_inv (hmapsT v hv), norm_smul,
      Real.norm_of_nonneg hsq.le, mul_pow, Real.sq_sqrt hε.le]
  -- a point of the sublevel set is the image of `(√ε)⁻¹ y(x)`
  have hpre : ∀ x, f x ≤ f p + ε →
      (√ε)⁻¹ • y x ∈ closedBall (0 : F) 1 ∧ y.symm (√ε • ((√ε)⁻¹ • y x)) = x ∧
        ε * ‖(√ε)⁻¹ • y x‖ ^ 2 = f x - f p := by
    intro x hx
    have hxU : x ∈ U := by
      by_contra hxU
      linarith [hηU x hxU]
    have hxs : x ∈ y.source := hxU.1
    have hfx := hfy x hxs
    have hnorm : ε * ‖(√ε)⁻¹ • y x‖ ^ 2 = ‖y x‖ ^ 2 := by
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hsq.le, mul_pow, inv_pow,
        Real.sq_sqrt hε.le, ← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul]
    refine ⟨?_, ?_, by rw [hnorm]; linarith⟩
    · rw [mem_closedBall_zero_iff]
      have h1 : ε * ‖(√ε)⁻¹ • y x‖ ^ 2 ≤ ε * 1 ^ 2 := by rw [hnorm]; linarith
      have h2 : ‖(√ε)⁻¹ • y x‖ ^ 2 ≤ 1 ^ 2 := le_of_mul_le_mul_left h1 hε
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) zero_le_one two_ne_zero).1 h2
    · rw [smul_smul, mul_inv_cancel₀ hsq.ne', one_smul, y.left_inv hxs]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact y.continuousOn_symm.comp (continuous_const_smul _).continuousOn hmapsT
  · intro v hv w hw hvw
    have h1 : √ε • v ∈ y.symm.source := by rw [y.symm_source]; exact hmapsT v hv
    have h2 : √ε • w ∈ y.symm.source := by rw [y.symm_source]; exact hmapsT w hw
    exact smul_right_injective F hsq.ne' (y.symm.injOn h1 h2 hvw)
  · ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [mem_ofPred_eq, hval v hv]
      have : ‖v‖ ^ 2 ≤ 1 := by
        have := mem_closedBall_zero_iff.1 hv
        nlinarith [norm_nonneg v]
      nlinarith
    · intro hx
      obtain ⟨h1, h2, -⟩ := hpre x hx
      exact ⟨_, h1, h2⟩
  · ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [mem_ofPred_eq, hval v (sphere_subset_closedBall hv), mem_sphere_zero_iff_norm.1 hv]
      ring
    · intro hx
      have hx' : f x = f p + ε := hx
      obtain ⟨-, h2, h3⟩ := hpre x hx'.le
      refine ⟨_, ?_, h2⟩
      rw [mem_sphere_zero_iff_norm]
      have h4 : ε * ‖(√ε)⁻¹ • y x‖ ^ 2 = ε * 1 ^ 2 := by rw [h3]; linarith
      have h5 := mul_left_cancel₀ hε.ne' h4
      exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 h5

end SublevelBall

end Morse
