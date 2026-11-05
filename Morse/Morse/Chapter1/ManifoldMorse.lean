import Morse.Chapter1.Manifold
import Morse.Chapter1.MorseLemma

/-!
Milnor, *Morse Theory*, §2, pp. 6–8, on a manifold.

# Non-degenerate critical points are isolated; the Lemma of Morse on a manifold

Setting as in `Morse/Chapter1/Manifold.lean`: `M` is a smooth manifold without boundary modelled
on a finite-dimensional real normed space `E`, `f : M → ℝ`.

## Corollary 2.3 and its consequences

**Corollary 2.3** (Milnor, p. 8): *non-degenerate critical points are isolated*.
`Morse.IsNondegenerateCriticalPointM.exists_nhds_isCriticalPointM_eq`: a non-degenerate critical
point `p` of a function `C²` at `p` has a neighbourhood in which it is the only critical point.  As
in the Euclidean case (`Morse.eventually_not_isCriticalPoint`) only the non-degeneracy of the
Hessian is used, not the Morse lemma; the transfer to `M` uses that criticality of points `x` near
`p` can be read in the chart at `p` (`Morse.eventually_isCriticalPointM_iff`), which is the
coordinate independence of `Morse/Chapter1/Manifold.lean` applied at the points `x ≠ p`.

Milnor does not state the global consequence, but uses it repeatedly: in the proof of Theorem 3.5
(p. 23) the critical values have no cluster point because each `M^a` is compact; in §5 (p. 29) a
compact manifold carries only finitely many critical points, arranged in levels `a₁ < ⋯ < a_k`
(Milnor assumes there that the critical points are "isolated, non-degenerate"; isolatedness is
redundant by Corollary 2.3); in Application 2 of §6 (p. 36) one sums over the critical points.

* `Morse.isClosed_setOf_isCriticalPointM`: the critical set of a `C¹` function is closed;
* `Morse.isDiscrete_inter_setOf_isCriticalPointM`: if all critical points in a set `V` are
  non-degenerate, the critical points in `V` form a discrete set;
* `Morse.finite_inter_setOf_isCriticalPointM`,
  `Morse.IsMorseFunction.finite_setOf_isCriticalPointM`: a compact set contains only finitely many
  critical points of such a function; in particular a Morse function on a compact manifold has
  finitely many critical points.

Hausdorffness is not needed for these statements (a closed subset of a compact set is compact,
and a compact discrete set is finite, in any topological space).

## The Lemma of Morse on a manifold

**Lemma 2.2** (Milnor, p. 6), on `M`: `Morse.morse_lemmaM`.  Around a non-degenerate critical
point `p` of index `λ` of a function smooth on an open set `U ∋ p` there is a smooth coordinate
system `y : M → ℝⁿ` (`n = dim E`; an open partial homeomorphism, smooth with smooth inverse,
`Morse.IsSmoothCoord`), with source in `U`, `y p = 0` and
`f = f(p) − (y⁰)² − ⋯ − (y^{λ−1})² + (y^λ)² + ⋯ + (yⁿ⁻¹)²` on its source.  The coordinate-free
form `f = f(p) + ½ f_**(φ, φ)`, with `φ` a chart of the maximal atlas, is
`Morse.exists_morse_chartM`.
Both are obtained by applying the Euclidean statements (`Morse.morse_lemma`,
`Morse.exists_morse_chart`) to the local representative in the preferred chart at `p` and composing
with that chart.

**Conversely** (Milnor, p. 6, first paragraph of the proof), *any* such coordinate system forces
`λ` to be the index: `Morse.isNondegenerateCriticalPointM_of_morse_chart`.  Here no hypothesis on
`f` is needed: the normal form itself shows that `f` is smooth near `p`, that `p` is a
non-degenerate critical point, and that its index is the number of minus signs.  The proof is
Milnor's: in the coordinates `y` the Hessian is `diag(−2, …, −2, 2, …, 2)`, and the index and the
non-degeneracy can be computed in any coordinate system (`Morse.IsSmoothCoord.index_eq`).

Milnor's coordinates are numbered `1, …, n`; ours are `0, …, n − 1`, so the negative squares are
those with index `i < λ`.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold

noncomputable section

namespace Morse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-! ### Critical points near a point, read in one chart -/

section Near

/-- **Criticality of the points near `p` can be read in the chart at `p`**: for `f` of class `C¹`
at `p`, every `x` close to `p` is a critical point of `f` iff its image is a critical point of the
local representative `Morse.localRep E f p`. -/
theorem eventually_isCriticalPointM_iff {f : M → ℝ} {p : M}
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 1 f p) :
    ∀ᶠ x in 𝓝 p, IsCriticalPointM E f x ↔
      IsCriticalPoint (localRep E f p) (extChartAt 𝓘(ℝ, E) p x) := by
  have hev : ∀ᶠ x in 𝓝 p, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 1 f x :=
    (contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hf
  filter_upwards [hev, (chartAt E p).open_source.mem_nhds (mem_chart_source E p)] with x hx hxs
  rw [(isSmoothCoord_chartAt p).isCriticalPointM_iff hxs (hx.mdifferentiableAt (by simp)),
    localRep_eq, extChartAt_self_coe]

variable [FiniteDimensional ℝ E]

/-- **No critical points near a point with non-degenerate Hessian**: if `f` is `C²` at `p` and
`f_**` is non-degenerate at `p`, then no point `x ≠ p` close to `p` is a critical point of `f`.
(That `p` itself is critical is not needed.) -/
theorem eventually_not_isCriticalPointM {f : M → ℝ} {p : M}
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 f p) (hnd : IsNondegenerate (hessianM E f p)) :
    ∀ᶠ x in 𝓝[≠] p, ¬ IsCriticalPointM E f x := by
  set a := extChartAt 𝓘(ℝ, E) p p with ha
  have hE := eventually_not_isCriticalPoint (contMDiffAt_iff_contDiffAt_localRep.1 hf) hnd
  -- the chart maps a punctured neighbourhood of `p` into a punctured neighbourhood of `a`
  have htend : Tendsto (extChartAt 𝓘(ℝ, E) p) (𝓝[≠] p) (𝓝[≠] a) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((continuousAt_extChartAt p).tendsto.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [nhdsWithin_le_nhds
      ((chartAt E p).open_source.mem_nhds (mem_chart_source E p)), self_mem_nhdsWithin]
      with x hx hxp
    intro hxa
    apply hxp
    have h : chartAt E p x = chartAt E p p := by
      rw [← extChartAt_self_coe, ← ha]
      exact hxa
    exact (chartAt E p).injOn hx (mem_chart_source E p) h
  filter_upwards [htend.eventually hE, nhdsWithin_le_nhds
    (eventually_isCriticalPointM_iff (hf.of_le (by norm_num)))] with x hx hx'
  rwa [hx']

/-- **Corollary 2.3** (Milnor, p. 8): *non-degenerate critical points are isolated.*  A
non-degenerate critical point `p` of a function `f` of class `C²` at `p` has a neighbourhood in
which it is the only critical point of `f`. -/
theorem IsNondegenerateCriticalPointM.exists_nhds_isCriticalPointM_eq {f : M → ℝ} {p : M}
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 f p) (hp : IsNondegenerateCriticalPointM E f p) :
    ∃ U ∈ 𝓝 p, ∀ x ∈ U, IsCriticalPointM E f x ↔ x = p := by
  have h := eventually_nhdsWithin_iff.1 (eventually_not_isCriticalPointM hf hp.2)
  refine ⟨_, h, fun x hx => ⟨fun hcrit => ?_, fun hxp => hxp ▸ hp.1⟩⟩
  by_contra hxp
  exact hx hxp hcrit

end Near

/-! ### The critical set -/

section CriticalSet

/-- **The critical set of a `C¹` function is closed.** -/
theorem isClosed_setOf_isCriticalPointM {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 1 f) : IsClosed {x | IsCriticalPointM E f x} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x₀ hx₀
  set g := localRep E f x₀ with hg
  set a := extChartAt 𝓘(ℝ, E) x₀ x₀ with ha
  -- `dg` is continuous at `a` and nonzero there
  have hgC : ContDiffAt ℝ 1 g a := contMDiffAt_iff_contDiffAt_localRep.1 (hf x₀)
  have hcont : ContinuousAt (fderiv ℝ g) a :=
    (hgC.fderiv_right (m := 0) (by norm_num)).continuousAt
  have hne : fderiv ℝ g a ≠ 0 := fun h => hx₀ (isCriticalPointM_iff_fderiv.2 h)
  have hev : ∀ᶠ u in 𝓝 a, fderiv ℝ g u ≠ 0 :=
    hcont.eventually (isOpen_ne.mem_nhds hne)
  have hev' : ∀ᶠ x in 𝓝 x₀, fderiv ℝ g (extChartAt 𝓘(ℝ, E) x₀ x) ≠ 0 :=
    (continuousAt_extChartAt x₀).eventually hev
  filter_upwards [hev', eventually_isCriticalPointM_iff (hf x₀)] with x hx hx'
  intro hcrit
  exact hx (IsCriticalPoint.fderiv_eq (hx'.1 hcrit))

variable [FiniteDimensional ℝ E]

/-- **If all critical points of `f` in a set `V` are non-degenerate, the critical points in `V`
form a discrete set.** -/
theorem isDiscrete_inter_setOf_isCriticalPointM {f : M → ℝ} {V : Set M}
    (hf : ∀ x ∈ V, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 f x)
    (hnd : ∀ x ∈ V, IsCriticalPointM E f x → IsNondegenerate (hessianM E f x)) :
    IsDiscrete (V ∩ {x | IsCriticalPointM E f x}) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  rintro x ⟨hxV, hx⟩
  obtain ⟨U, hU, hUx⟩ :=
    IsNondegenerateCriticalPointM.exists_nhds_isCriticalPointM_eq (hf x hxV) ⟨hx, hnd x hxV hx⟩
  refine ⟨interior U, isOpen_interior, ?_⟩
  ext z
  simp only [mem_inter_iff, mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨hzU, -, hz⟩
    exact (hUx z (interior_subset hzU)).1 hz
  · rintro rfl
    exact ⟨mem_interior_iff_mem_nhds.2 hU, hxV, hx⟩

/-- **A compact set contains only finitely many critical points** of a `C²` function all of whose
critical points are non-degenerate. -/
theorem finite_inter_setOf_isCriticalPointM {f : M → ℝ} {K : Set M} (hK : IsCompact K)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 f)
    (hnd : ∀ x, IsCriticalPointM E f x → IsNondegenerate (hessianM E f x)) :
    (K ∩ {x | IsCriticalPointM E f x}).Finite := by
  have hC : IsCompact (K ∩ {x | IsCriticalPointM E f x}) :=
    hK.inter_right (isClosed_setOf_isCriticalPointM (hf.of_le (by norm_num)))
  have hD : IsDiscrete (univ ∩ {x | IsCriticalPointM E f x}) :=
    isDiscrete_inter_setOf_isCriticalPointM (fun x _ => hf x) fun x _ => hnd x
  exact hC.finite (hD.mono fun x hx => ⟨mem_univ x, hx.2⟩)

/-- **A Morse function on a compact manifold has only finitely many critical points.** -/
theorem IsMorseFunction.finite_setOf_isCriticalPointM [CompactSpace M] {f : M → ℝ}
    (hf : IsMorseFunction E f) : {x | IsCriticalPointM E f x}.Finite := by
  have h := finite_inter_setOf_isCriticalPointM isCompact_univ
    (hf.contMDiff.of_le (by norm_cast)) hf.isNondegenerate
  rwa [univ_inter] at h

/-- The critical points of a Morse function in a compact set are finitely many. -/
theorem IsMorseFunction.finite_inter_setOf_isCriticalPointM {f : M → ℝ}
    (hf : IsMorseFunction E f) {K : Set M} (hK : IsCompact K) :
    (K ∩ {x | IsCriticalPointM E f x}).Finite :=
  Morse.finite_inter_setOf_isCriticalPointM hK (hf.contMDiff.of_le (by norm_cast))
    hf.isNondegenerate

end CriticalSet

/-! ### The Lemma of Morse on a manifold -/

section MorseLemma

variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- The data needed to apply the Euclidean Morse lemma to the local representative in the
preferred chart at `p`: on the open set `(chartAt E p).target ∩ (chartAt E p)⁻¹ ⁻¹' U`, the function
`f ∘ (chartAt E p)⁻¹` is smooth, and `chartAt E p p` is a non-degenerate critical point of it, with
Hessian `f_**`. -/
theorem morse_lemmaM_aux {f : M → ℝ} {p : M} {U : Set M} (hU : IsOpen U) (hpU : p ∈ U)
    (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f U) (hp : IsNondegenerateCriticalPointM E f p) :
    IsOpen ((chartAt E p).target ∩ (chartAt E p).symm ⁻¹' U) ∧
      chartAt E p p ∈ (chartAt E p).target ∩ (chartAt E p).symm ⁻¹' U ∧
      ContDiffOn ℝ ∞ (f ∘ (chartAt E p).symm)
        ((chartAt E p).target ∩ (chartAt E p).symm ⁻¹' U) ∧
      IsCriticalPoint (f ∘ (chartAt E p).symm) (chartAt E p p) ∧
      hessian (f ∘ (chartAt E p).symm) (chartAt E p p) = hessianM E f p := by
  have hfp : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f p := hf.contMDiffAt (hU.mem_nhds hpU)
  refine ⟨(chartAt E p).isOpen_inter_preimage_symm hU,
    ⟨(chartAt E p).map_source (mem_chart_source E p), by
      rw [mem_preimage, (chartAt E p).left_inv (mem_chart_source E p)]; exact hpU⟩, ?_, ?_,
    (hessianM_eq_chartAt f p).symm⟩
  · rw [← contMDiffOn_iff_contDiffOn]
    exact hf.comp (contMDiffOn_chart_symm.mono inter_subset_left) fun u hu => hu.2
  · exact ((isSmoothCoord_chartAt p).isCriticalPointM_iff (mem_chart_source E p)
      (hfp.mdifferentiableAt (by simp))).1 hp.1

/-- **The Lemma of Morse on a manifold, coordinate free.**  Let `f` be smooth on an open set
`U ∋ p` and `p` a non-degenerate critical point of `f`.  Then there is a chart `φ : M → E` of the
maximal atlas, with `p` in its source, its source contained in `U`, `φ p = 0`, and
`f = f(p) + ½ f_**(φ, φ)` on its source. -/
theorem exists_morse_chartM {f : M → ℝ} {p : M} {U : Set M} (hU : IsOpen U) (hpU : p ∈ U)
    (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f U) (hp : IsNondegenerateCriticalPointM E f p) :
    ∃ φ : OpenPartialHomeomorph M E, φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧
      p ∈ φ.source ∧ φ.source ⊆ U ∧ φ p = 0 ∧
      ∀ x ∈ φ.source, f x = f p + (2 : ℝ)⁻¹ * hessianM E f p (φ x) (φ x) := by
  obtain ⟨hU'o, haU', hg, hcrit, hH⟩ := morse_lemmaM_aux hU hpU hf hp
  obtain ⟨φ₀, haφ₀, hφ₀U, hφ₀a, -, hφ₀s, hφ₀t, hfφ₀⟩ :=
    exists_morse_chart hU'o haU' hg hcrit (by rw [hH]; exact hp.2)
  set φ := (chartAt E p).trans φ₀ with hφ
  have hφsrc : φ.source = (chartAt E p).source ∩ chartAt E p ⁻¹' φ₀.source := by
    rw [hφ, OpenPartialHomeomorph.trans_source]
  refine ⟨φ, isSmoothCoord_iff_mem_maximalAtlas φ |>.1 ((isSmoothCoord_chartAt p).trans hφ₀s hφ₀t),
    ?_, ?_, ?_, ?_⟩
  · rw [hφsrc]
    exact ⟨mem_chart_source E p, haφ₀⟩
  · intro x hx
    rw [hφsrc] at hx
    have h := (hφ₀U hx.2).2
    rwa [mem_preimage, (chartAt E p).left_inv hx.1] at h
  · rw [hφ, OpenPartialHomeomorph.coe_trans, comp_apply, hφ₀a]
  · intro x hx
    rw [hφsrc] at hx
    have h := hfφ₀ _ hx.2
    rw [comp_apply, (chartAt E p).left_inv hx.1, comp_apply,
      (chartAt E p).left_inv (mem_chart_source E p), hH] at h
    rw [h, hφ, OpenPartialHomeomorph.coe_trans, comp_apply]

/-- **Lemma 2.2 (Lemma of Morse) on a manifold** (Milnor, p. 6).  Let `f` be smooth on an open
set `U ∋ p` of `M` (`n = dim E`), and `p` a non-degenerate critical point of `f` of index `λ`.
Then there is a local coordinate system `y = (y⁰, …, yⁿ⁻¹) : M → ℝⁿ`, smooth with smooth inverse,
whose source is a neighbourhood of `p` contained in `U`, with `y(p) = 0` and
`f = f(p) − (y⁰)² − ⋯ − (y^{λ−1})² + (y^λ)² + ⋯ + (yⁿ⁻¹)²` throughout its source. -/
theorem morse_lemmaM {f : M → ℝ} {p : M} {U : Set M} (hU : IsOpen U) (hpU : p ∈ U)
    (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f U) (hp : IsNondegenerateCriticalPointM E f p) :
    ∃ y : OpenPartialHomeomorph M (Fin (finrank ℝ E) → ℝ),
      IsSmoothCoord E y ∧ p ∈ y.source ∧ y.source ⊆ U ∧ y p = 0 ∧
      ∀ x ∈ y.source, f x = f p
        - ∑ i ∈ Finset.univ.filter (fun i : Fin (finrank ℝ E) => (i : ℕ) < indexM E f p),
            y x i ^ 2
        + ∑ i ∈ Finset.univ.filter (fun i : Fin (finrank ℝ E) => indexM E f p ≤ (i : ℕ)),
            y x i ^ 2 := by
  obtain ⟨hU'o, haU', hg, hcrit, hH⟩ := morse_lemmaM_aux hU hpU hf hp
  obtain ⟨y₀, hay₀, hy₀U, hy₀a, hy₀s, hy₀t, hfy₀⟩ :=
    morse_lemma hU'o haU' hg hcrit (by rw [hH]; exact hp.2)
  rw [hH, ← indexM] at hfy₀
  set y := (chartAt E p).trans y₀ with hy
  have hysrc : y.source = (chartAt E p).source ∩ chartAt E p ⁻¹' y₀.source := by
    rw [hy, OpenPartialHomeomorph.trans_source]
  refine ⟨y, (isSmoothCoord_chartAt p).trans hy₀s hy₀t, ?_, ?_, ?_, ?_⟩
  · rw [hysrc]
    exact ⟨mem_chart_source E p, hay₀⟩
  · intro x hx
    rw [hysrc] at hx
    have h := (hy₀U hx.2).2
    rwa [mem_preimage, (chartAt E p).left_inv hx.1] at h
  · rw [hy, OpenPartialHomeomorph.coe_trans, comp_apply, hy₀a]
  · intro x hx
    rw [hysrc] at hx
    have h := hfy₀ _ hx.2
    rw [comp_apply, (chartAt E p).left_inv hx.1, comp_apply,
      (chartAt E p).left_inv (mem_chart_source E p)] at h
    rw [h, hy, OpenPartialHomeomorph.coe_trans, comp_apply]

end MorseLemma

/-! ### Conversely: the normal form determines the index -/

section Converse

variable {n : ℕ}

/-- `diag(−1, …, −1, 1, …, 1)` is non-degenerate. -/
theorem isNondegenerate_diagForm_morseSign (k : ℕ) :
    IsNondegenerate (diagForm (morseSign (n := n) k)) := by
  rw [isNondegenerate_iff]
  intro v hv
  funext i
  have h := hv (Pi.single i 1)
  rw [diagForm_apply, Finset.sum_eq_single i (fun j _ hji => by simp [hji])
    (fun hi => absurd (Finset.mem_univ i) hi)] at h
  have hs : morseSign k i ≠ 0 := by
    unfold morseSign
    split_ifs <;> norm_num
  simpa [hs] using h

/-- Milnor's normal form `w ↦ c − w₀² − ⋯ − w_{k−1}² + w_k² + ⋯ + w_{n−1}²`. -/
def morseNormalForm (c : ℝ) (k : ℕ) (w : Fin n → ℝ) : ℝ :=
  c - ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), w i ^ 2
    + ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ (i : ℕ)), w i ^ 2

theorem morseNormalForm_eq (c : ℝ) (k : ℕ) :
    morseNormalForm (n := n) c k = fun w => c + diagForm (morseSign k) w w := by
  funext w
  rw [morseNormalForm, diagForm_morseSign_apply_self]
  ring

theorem contDiff_morseNormalForm (c : ℝ) (k : ℕ) : ContDiff ℝ ∞ (morseNormalForm (n := n) c k) := by
  rw [morseNormalForm_eq]
  exact contDiff_const.add
    ((diagForm (morseSign k)).isBoundedBilinearMap.contDiff.comp (contDiff_id.prodMk contDiff_id))

/-- The normal form has a critical point at `0`. -/
theorem isCriticalPoint_morseNormalForm (c : ℝ) (k : ℕ) :
    IsCriticalPoint (morseNormalForm (n := n) c k) 0 := by
  rw [morseNormalForm_eq]
  set D := diagForm (morseSign (n := n) k)
  have h := D.hasFDerivAt_of_bilinear (hasFDerivAt_id (0 : Fin n → ℝ))
    (hasFDerivAt_id (0 : Fin n → ℝ))
  have h0 : D.precompR (Fin n → ℝ) (id 0) (ContinuousLinearMap.id ℝ (Fin n → ℝ)) +
      D.precompL (Fin n → ℝ) (ContinuousLinearMap.id ℝ (Fin n → ℝ)) (id 0) = 0 := by
    ext v; simp
  rw [h0] at h
  exact h.const_add c

/-- The Hessian of the normal form at `0` is `2 · diag(−1, …, −1, 1, …, 1)`. -/
theorem hessian_morseNormalForm (c : ℝ) (k : ℕ) :
    hessian (morseNormalForm (n := n) c k) 0 = (2 : ℝ) • diagForm (morseSign k) := by
  rw [morseNormalForm_eq]
  set D := diagForm (morseSign (n := n) k) with hD
  have hc : fderiv ℝ (fun w => c + D w w) = fderiv ℝ (fun w => D w w) := by
    funext w
    exact fderiv_const_add c
  ext u v
  rw [hessian, hc, ← hessian, hessian_bilinear, hD, diagForm_symm (morseSign k) v u]
  simp only [smul_apply, smul_eq_mul]
  ring

/-- **The normal form determines the index** (Milnor, p. 6, first paragraph of the proof of
Lemma 2.2: "if there is any such expression for `f`, then `λ` must be the index of `f` at `p`").
If `y : M → ℝⁿ` is a smooth coordinate system around `p` with `y(p) = 0` and
`f = f(p) − (y⁰)² − ⋯ − (y^{k−1})² + (y^k)² + ⋯ + (yⁿ⁻¹)²` on its source, `k ≤ n`, then `p` is a
non-degenerate critical point of `f` of index `k`.  (No smoothness hypothesis on `f` is needed:
the normal form shows that `f` is smooth near `p`.) -/
theorem isNondegenerateCriticalPointM_of_morse_chart {f : M → ℝ} {p : M}
    (y : OpenPartialHomeomorph M (Fin n → ℝ)) (hy : IsSmoothCoord E y) (hp : p ∈ y.source)
    (hyp : y p = 0) {k : ℕ} (hk : k ≤ n)
    (hfy : ∀ x ∈ y.source, f x = f p
        - ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), y x i ^ 2
        + ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ (i : ℕ)), y x i ^ 2) :
    IsNondegenerateCriticalPointM E f p ∧ indexM E f p = k := by
  set Q := morseNormalForm (n := n) (f p) k with hQ
  have hfQ : ∀ x ∈ y.source, f x = Q (y x) := fun x hx => hfy x hx
  -- `f` is smooth near `p`
  have hyC : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, Fin n → ℝ) ∞ y p :=
    (hy.contMDiffOn p hp).contMDiffAt (y.open_source.mem_nhds hp)
  have hfC : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f p := by
    have h : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (Q ∘ y) p :=
      (contDiff_morseNormalForm (f p) k).contMDiff.contMDiffAt.comp p hyC
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [y.open_source.mem_nhds hp] with x hx
    exact hfQ x hx
  have hf2 : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 f p := hfC.of_le (by norm_cast)
  -- in the coordinates `y`, `f` is the normal form near `0`
  have h0t : (0 : Fin n → ℝ) ∈ y.target := hyp ▸ y.map_source hp
  have hev : f ∘ y.symm =ᶠ[𝓝 (y p)] Q := by
    rw [hyp]
    filter_upwards [y.open_target.mem_nhds h0t] with w hw
    rw [comp_apply, hfQ _ (y.map_target hw), y.right_inv hw]
  have hcrit : IsCriticalPointM E f p := by
    rw [hy.isCriticalPointM_iff hp (hfC.mdifferentiableAt (by simp))]
    have h := isCriticalPoint_morseNormalForm (n := n) (f p) k
    rw [← hyp] at h
    exact h.congr_of_eventuallyEq hev
  have hH : hessian (f ∘ y.symm) (y p) = (2 : ℝ) • diagForm (morseSign k) := by
    rw [hessian_congr hev, hyp, hessian_morseNormalForm]
  refine ⟨⟨hcrit, ?_⟩, ?_⟩
  · rw [← hy.isNondegenerate_iff hp hf2 hcrit, hH, isNondegenerate_smul_iff (by norm_num)]
    exact isNondegenerate_diagForm_morseSign k
  · rw [← hy.index_eq hp hf2 hcrit, hH, index_smul (by norm_num), index_diagForm_morseSign hk]

/-- **The index is forced by the normal form**, in the form of `Morse.morse_lemmaM`. -/
theorem indexM_eq_of_morse_chart {f : M → ℝ} {p : M}
    (y : OpenPartialHomeomorph M (Fin n → ℝ)) (hy : IsSmoothCoord E y) (hp : p ∈ y.source)
    (hyp : y p = 0) {k : ℕ} (hk : k ≤ n)
    (hfy : ∀ x ∈ y.source, f x = f p
        - ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), y x i ^ 2
        + ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ (i : ℕ)), y x i ^ 2) :
    indexM E f p = k :=
  (isNondegenerateCriticalPointM_of_morse_chart y hy hp hyp hk hfy).2

end Converse

end Morse
