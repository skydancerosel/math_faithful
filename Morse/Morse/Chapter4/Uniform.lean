import Morse.Chapter4.Approximation
import Milnor.Chapter2.Corestrict

/-!
Milnor, *Morse Theory*, §6, p. 37.

# Corollary 6.8 on a non-compact submanifold: uniform approximation by Morse functions

Milnor, p. 37, paraphrased.  **Corollary 6.8.**  *Every bounded smooth function `f : M → ℝ` can be
uniformly approximated by a smooth function `g` without degenerate critical points; moreover `g`
can be chosen so that on a given compact set `K` its derivatives of order `≤ k` uniformly
approximate those of `f`.*  (For Milnor's proof, by `L_p` on an embedding `h` with `h₁ = f`, see
`Morse/Chapter4/Approximation.lean`.)

`Morse/Chapter4/Approximation.lean` proves that `f + ⟪a, ·⟫` is a Morse function for almost every
`a`; since `⟪a, ·⟫` is unbounded on an unbounded `M`, this gives the uniform approximation only
for compact `M`.  Here the perturbation is made bounded by composing with the diffeomorphism
`β(y) = y / √(1 + ‖y‖²)` of `ℝⁿ` onto its open unit ball (`Morse.ballDiffeo`, Mathlib's
`OpenPartialHomeomorph.univUnitBall`): `g = f + ⟪a, β(·)⟫` satisfies `|g − f| ≤ ‖a‖`.

## Main results

* `Morse.isSliceSubmanifold_ballImage`: `β(M)` is a slice submanifold of `ℝⁿ` (slice charts
  `σ ∘ β⁻¹`, `Morse.ballSliceChart`); `Morse.toBall`, `Morse.fromBall`: `β` and `β⁻¹` between `M`
  and `β(M)`, with `β⁻¹` smooth (`Morse.contMDiff_fromBall`);
* `Morse.isMorseFunction_of_ballImage`: if `g' ∘ β = g` and `g'` is a Morse function on `β(M)`,
  then `g` is a Morse function on `M` (in the charts `σ` of `M` and `σ ∘ β⁻¹` of `β(M)` the two
  functions have the same local representative);
* `Morse.ae_isMorseFunction_add_inner_ballDiffeo`: for every smooth `f : M → ℝ` and almost every
  `a ∈ ℝⁿ`, `f + ⟪a, β(·)⟫` is a Morse function on `M` (apply
  `Morse.ae_isMorseFunction_add_inner` to `β(M)` and `f ∘ β⁻¹`);
* `Morse.exists_isMorseFunction_approx_uniform` (**Corollary 6.8**, for any slice submanifold
  `M ⊆ ℝⁿ`): for every smooth `f : M → ℝ`, every `ε > 0`, every finite family of smooth coordinate
  systems `y_j` of `M` with compact sets `K_j` in their domains, and every `r ∈ ℕ`, there is a
  Morse function `g` with `|g − f| < ε` on all of `M` and every derivative of order `≤ r` of
  `(g − f) ∘ y_j⁻¹` of norm `< ε` on `K_j`.

## Gaps in Milnor's text

* **"Bounded" is not needed.**  Boundedness of `f` is used by Milnor only to make his embedding
  `h = (f, …)` bounded; with the bounded perturbation `⟪a, β(·)⟫` every smooth `f` on a submanifold
  of `ℝⁿ` (hence, granting Whitney's embedding theorem for non-compact manifolds, on any manifold)
  is a uniform limit of Morse functions.
* **Derivatives in charts**: as in `Morse/Chapter4/Approximation.lean`, "the `i`-th derivatives of
  `g` on `K` approximate those of `f`" is read in fixed coordinate systems covering `K`.
* **Abstract manifolds.**  Compact ones are covered in `Morse/Chapter4/Whitney.lean`, through
  Mathlib's Whitney embedding for compact manifolds
  (`Morse.exists_isMorseFunction_approx_of_compactSpace`; there `f` is bounded and the
  perturbation `⟪a, e(·)⟫` of a Whitney embedding `e` is already bounded).  Non-compact ones are
  not: Mathlib has no embedding into a Euclidean space for an arbitrary (second countable,
  Hausdorff) manifold.  Given one, its image is a slice submanifold diffeomorphic to the manifold
  (`Morse.exists_diffeomorph_range`), to which the result here applies.
-/

open Set Filter Topology Function Module MeasureTheory Metric
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)

namespace Morse

/-! ### The diffeomorphism of `ℝⁿ` onto its open unit ball -/

section Ball

variable (n : ℕ)

/-- `β(y) = y / √(1 + ‖y‖²)`, a diffeomorphism of `ℝⁿ` onto its open unit ball (Mathlib's
`OpenPartialHomeomorph.univUnitBall`), as a partial diffeomorphism of `ℝⁿ`. -/
def ballDiffeo : PartialDiffeomorph 𝓘(ℝ, 𝔼 n) 𝓘(ℝ, 𝔼 n) (𝔼 n) (𝔼 n) ∞ where
  toPartialEquiv := OpenPartialHomeomorph.univUnitBall.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_ball
  contMDiffOn_toFun :=
    (OpenPartialHomeomorph.contDiff_univUnitBall (n := ⊤)).contMDiff.contMDiffOn
  contMDiffOn_invFun :=
    contMDiffOn_iff_contDiffOn.2 (OpenPartialHomeomorph.contDiffOn_univUnitBall_symm (n := ⊤))

variable {n}

@[simp] theorem ballDiffeo_source : (ballDiffeo n).source = univ := rfl

@[simp] theorem ballDiffeo_target : (ballDiffeo n).target = ball 0 1 := rfl

theorem ballDiffeo_coe : ⇑(ballDiffeo n) = OpenPartialHomeomorph.univUnitBall := rfl

theorem contDiff_ballDiffeo : ContDiff ℝ ∞ (ballDiffeo n) :=
  OpenPartialHomeomorph.contDiff_univUnitBall (n := ⊤)

theorem contDiffOn_ballDiffeo_symm : ContDiffOn ℝ ∞ (ballDiffeo n).symm (ball 0 1) :=
  OpenPartialHomeomorph.contDiffOn_univUnitBall_symm (n := ⊤)

theorem ballDiffeo_mem_ball (y : 𝔼 n) : ballDiffeo n y ∈ ball (0 : 𝔼 n) 1 :=
  (ballDiffeo n).toPartialEquiv.map_source (mem_univ y)

theorem norm_ballDiffeo_lt_one (y : 𝔼 n) : ‖ballDiffeo n y‖ < 1 :=
  mem_ball_zero_iff.1 (ballDiffeo_mem_ball y)

theorem ballDiffeo_symm_apply_apply (y : 𝔼 n) : (ballDiffeo n).symm (ballDiffeo n y) = y :=
  (ballDiffeo n).toPartialEquiv.left_inv (mem_univ y)

theorem ballDiffeo_apply_symm_apply {z : 𝔼 n} (hz : z ∈ ball (0 : 𝔼 n) 1) :
    ballDiffeo n ((ballDiffeo n).symm z) = z :=
  (ballDiffeo n).toPartialEquiv.right_inv hz

end Ball

/-! ### The image of a submanifold in the unit ball -/

section Image

variable {n k w : ℕ} {M : Set (𝔼 n)}

/-- The slice chart of `β(M)` obtained from a slice chart `σ` of `M`: `σ ∘ β⁻¹`. -/
def ballSliceChart (σ : Milnor.SliceChart 𝓘(ℝ, 𝔼 n) (𝔼 k) (𝔼 w) M) :
    Milnor.SliceChart 𝓘(ℝ, 𝔼 n) (𝔼 k) (𝔼 w) (ballDiffeo n '' M) where
  φ := (ballDiffeo n).symm.trans σ.φ
  x₀ := ballDiffeo n σ.x₀
  x₀_mem := ⟨σ.x₀, σ.x₀_mem, rfl⟩
  x₀_source := ⟨ballDiffeo_mem_ball _, by
    change (ballDiffeo n).symm (ballDiffeo n σ.x₀) ∈ σ.φ.source
    rw [ballDiffeo_symm_apply_apply]
    exact σ.x₀_source⟩
  slice := by
    rintro z ⟨hz, hzσ⟩
    have hz' : z ∈ ball (0 : 𝔼 n) 1 := hz
    have hzσ' : (ballDiffeo n).symm z ∈ σ.φ.source := hzσ
    change z ∈ ballDiffeo n '' M ↔ (σ.φ ((ballDiffeo n).symm z)).2 = 0
    rw [← σ.slice _ hzσ']
    constructor
    · rintro ⟨x, hx, rfl⟩
      rwa [ballDiffeo_symm_apply_apply]
    · intro h
      exact ⟨_, h, ballDiffeo_apply_symm_apply hz'⟩

theorem ballSliceChart_φ_apply (σ : Milnor.SliceChart 𝓘(ℝ, 𝔼 n) (𝔼 k) (𝔼 w) M) (z : 𝔼 n) :
    (ballSliceChart σ).φ z = σ.φ ((ballDiffeo n).symm z) := rfl

theorem mem_ballSliceChart_source (σ : Milnor.SliceChart 𝓘(ℝ, 𝔼 n) (𝔼 k) (𝔼 w) M) {x : 𝔼 n}
    (hx : x ∈ σ.φ.source) : ballDiffeo n x ∈ (ballSliceChart σ).φ.source :=
  ⟨ballDiffeo_mem_ball x, by
    change (ballDiffeo n).symm (ballDiffeo n x) ∈ σ.φ.source
    rwa [ballDiffeo_symm_apply_apply]⟩

variable (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, 𝔼 n) (𝔼 k) (𝔼 w) M)

include hM in
/-- **The image `β(M)` of a slice submanifold in the unit ball is a slice submanifold.** -/
theorem isSliceSubmanifold_ballImage :
    Milnor.IsSliceSubmanifold 𝓘(ℝ, 𝔼 n) (𝔼 k) (𝔼 w) (ballDiffeo n '' M) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨σ, hσ⟩ := hM x hx
  exact ⟨ballSliceChart σ, mem_ballSliceChart_source σ hσ⟩

end Image

/-! ### Transporting the Morse property from `β(M)` to `M` -/

section Transport

variable {n k w : ℕ} {M : Set (𝔼 n)}
  (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, 𝔼 n) (𝔼 k) (𝔼 w) M)

/-- `β` restricted to `M`, as a map `M → β(M)`. -/
def toBall (x : M) : ballDiffeo n '' M := ⟨ballDiffeo n x, x, x.2, rfl⟩

theorem symm_mem_of_mem_ballImage {z : 𝔼 n} (hz : z ∈ ballDiffeo n '' M) :
    (ballDiffeo n).symm z ∈ M := by
  obtain ⟨x, hx, rfl⟩ := hz
  rwa [ballDiffeo_symm_apply_apply]

theorem mem_ball_of_mem_ballImage {z : 𝔼 n} (hz : z ∈ ballDiffeo n '' M) :
    z ∈ ball (0 : 𝔼 n) 1 := by
  obtain ⟨x, -, rfl⟩ := hz
  exact ballDiffeo_mem_ball x

/-- `β⁻¹` restricted to `β(M)`, as a map `β(M) → M`. -/
def fromBall (z : ballDiffeo n '' M) : M :=
  ⟨(ballDiffeo n).symm z, symm_mem_of_mem_ballImage z.2⟩

theorem fromBall_toBall (x : M) : fromBall (toBall x) = x :=
  Subtype.ext (ballDiffeo_symm_apply_apply (x : 𝔼 n))

/-- `β⁻¹ : β(M) → M` is smooth. -/
theorem contMDiff_fromBall :
    letI := hM.chartedSpace
    letI := (isSliceSubmanifold_ballImage hM).chartedSpace
    ContMDiff 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, 𝔼 k) ∞ (fromBall (M := M)) := by
  let := hM.chartedSpace
  have hM' := isSliceSubmanifold_ballImage hM
  let := hM'.chartedSpace
  have := hM'.isManifold
  have hF : ContMDiff 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, 𝔼 n) ∞
      (fun z : ballDiffeo n '' M => (ballDiffeo n).symm (z : 𝔼 n)) :=
    (ballDiffeo n).contMDiffOn_invFun.comp_contMDiff hM'.contMDiff_val
      fun z => mem_ball_of_mem_ballImage z.2
  exact hM.contMDiff_codRestrict hF fun z => symm_mem_of_mem_ballImage z.2

/-- The chart of `β(M)` built from the slice chart `σ` of `M`, read through `β`. -/
theorem ballSliceChart_toChart_toBall (σ : Milnor.SliceChart 𝓘(ℝ, 𝔼 n) (𝔼 k) (𝔼 w) M)
    (x : M) : (ballSliceChart σ).toChart (toBall x) = σ.toChart x := by
  change (σ.φ ((ballDiffeo n).symm (ballDiffeo n (x : 𝔼 n)))).1 = (σ.φ x).1
  rw [ballDiffeo_symm_apply_apply]

theorem ballSliceChart_toChart_symm (σ : Milnor.SliceChart 𝓘(ℝ, 𝔼 n) (𝔼 k) (𝔼 w) M)
    {u : 𝔼 k} (hu : u ∈ σ.toChart.target) :
    ((ballSliceChart σ).toChart.symm u : 𝔼 n) = ballDiffeo n (σ.toChart.symm u : 𝔼 n) := by
  have hu' : (u, (0 : 𝔼 w)) ∈ (ballSliceChart σ).φ.target := ⟨hu, mem_univ _⟩
  rw [(ballSliceChart σ).toChart_symm_apply hu', σ.toChart_symm_apply hu]
  rfl

theorem fromBall_ballSliceChart_toChart_symm
    (σ : Milnor.SliceChart 𝓘(ℝ, 𝔼 n) (𝔼 k) (𝔼 w) M) {u : 𝔼 k} (hu : u ∈ σ.toChart.target) :
    fromBall ((ballSliceChart σ).toChart.symm u) = σ.toChart.symm u := by
  apply Subtype.ext
  change (ballDiffeo n).symm ((ballSliceChart σ).toChart.symm u : 𝔼 n) = _
  rw [ballSliceChart_toChart_symm σ hu, ballDiffeo_symm_apply_apply]

/-- Local functions agreeing near a point have the same non-degenerate critical points there. -/
theorem isNondegenerateCriticalPoint_iff_of_eventuallyEq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f g : E → ℝ} {p : E} (h : f =ᶠ[𝓝 p] g) :
    IsNondegenerateCriticalPoint f p ↔ IsNondegenerateCriticalPoint g p := by
  unfold IsNondegenerateCriticalPoint IsCriticalPoint
  rw [hessian_congr h]
  exact and_congr_left' ⟨fun hf => hf.congr_of_eventuallyEq h.symm,
    fun hg => hg.congr_of_eventuallyEq h⟩

theorem isCriticalPoint_iff_of_eventuallyEq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {p : E} (h : f =ᶠ[𝓝 p] g) : IsCriticalPoint f p ↔ IsCriticalPoint g p :=
  ⟨fun hf => hf.congr_of_eventuallyEq h.symm, fun hg => hg.congr_of_eventuallyEq h⟩

/-- **Transport of the Morse property along `β : M → β(M)`**: if `g = g' ∘ β` on `M` and `g'` is a
Morse function on `β(M)`, then `g` is a Morse function on `M`. -/
theorem isMorseFunction_of_ballImage {g : M → ℝ} {g' : ballDiffeo n '' M → ℝ}
    (hg : letI := hM.chartedSpace; ContMDiff 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, ℝ) ∞ g)
    (hgg : ∀ x, g' (toBall x) = g x)
    (hmorse : letI := (isSliceSubmanifold_ballImage hM).chartedSpace;
      IsMorseFunction (𝔼 k) g') :
    letI := hM.chartedSpace
    IsMorseFunction (𝔼 k) g := by
  let := hM.chartedSpace
  have := hM.isManifold
  have hM' := isSliceSubmanifold_ballImage hM
  refine ⟨hg, fun x hcrit => ?_⟩
  set σ := Milnor.Tub.σ hM x with hσ
  have hxσ : x ∈ σ.toChart.source := Milnor.Tub.mem_source hM x
  have hy := isSmoothCoord_toChart hM σ
  have hzσ : σ.toChart x ∈ σ.toChart.target := σ.toChart.map_source hxσ
  -- the two local representatives agree near `σ x`
  have heq : g ∘ σ.toChart.symm =ᶠ[𝓝 (σ.toChart x)] g' ∘ (ballSliceChart σ).toChart.symm := by
    filter_upwards [σ.toChart.open_target.mem_nhds hzσ] with u hu
    simp only [comp_apply]
    rw [← hgg, ← fromBall_ballSliceChart_toChart_symm σ hu]
    congr 1
    apply Subtype.ext
    change ballDiffeo n ((ballDiffeo n).symm _) = _
    exact ballDiffeo_apply_symm_apply (mem_ball_of_mem_ballImage
      ((ballSliceChart σ).toChart.symm u).2)
  let := hM'.chartedSpace
  have := hM'.isManifold
  have hy' := isSmoothCoord_toChart hM' (ballSliceChart σ)
  have hxσ' : toBall x ∈ (ballSliceChart σ).toChart.source :=
    mem_ballSliceChart_source σ hxσ
  have hz : (ballSliceChart σ).toChart (toBall x) = σ.toChart x :=
    ballSliceChart_toChart_toBall σ x
  have hg'x : ContMDiffAt 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, ℝ) 2 g' (toBall x) :=
    (hmorse.contMDiff _).of_le (by norm_cast)
  have hgx : ContMDiffAt 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, ℝ) 2 g x := (hg x).of_le (by norm_cast)
  -- `toBall x` is a critical point of `g'`
  have hcrit' : IsCriticalPointM (𝔼 k) g' (toBall x) := by
    rw [hy'.isCriticalPointM_iff hxσ' (hg'x.mdifferentiableAt (by simp)), hz,
      ← isCriticalPoint_iff_of_eventuallyEq heq]
    exact (hy.isCriticalPointM_iff hxσ (hgx.mdifferentiableAt (by simp))).1 hcrit
  have hnd := (hy'.isNondegenerateCriticalPointM_iff hxσ' hg'x).1
    (hmorse.isNondegenerateCriticalPointM hcrit')
  rw [hz, ← isNondegenerateCriticalPoint_iff_of_eventuallyEq heq] at hnd
  exact ((hy.isNondegenerateCriticalPointM_iff hxσ hgx).2 hnd).2

end Transport

/-! ### Corollary 6.8 -/

section Corollary68

variable {n k w : ℕ} {M : Set (𝔼 n)}
  (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, 𝔼 n) (𝔼 k) (𝔼 w) M)

theorem contDiff_inner_ballDiffeo (a : 𝔼 n) : ContDiff ℝ ∞ (fun y => ⟪a, ballDiffeo n y⟫) :=
  (innerBilin n a).contDiff.comp contDiff_ballDiffeo

/-- **`f + ⟪a, β(·)⟫` is a Morse function for almost every `a ∈ ℝⁿ`**, `β` the diffeomorphism of
`ℝⁿ` onto its open unit ball: apply `Morse.ae_isMorseFunction_add_inner` to the submanifold
`β(M)` and the function `f ∘ β⁻¹`, and transport the Morse property back along `β`. -/
theorem ae_isMorseFunction_add_inner_ballDiffeo (μ : Measure (𝔼 n)) [μ.IsAddHaarMeasure]
    {f : M → ℝ} (hf : letI := hM.chartedSpace; ContMDiff 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, ℝ) ∞ f) :
    letI := hM.chartedSpace
    ∀ᵐ a ∂μ, IsMorseFunction (𝔼 k) (fun x : M => f x + ⟪a, ballDiffeo n x⟫) := by
  let := hM.chartedSpace
  have := hM.isManifold
  have hM' := isSliceSubmanifold_ballImage hM
  have hf' : letI := hM'.chartedSpace; ContMDiff 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, ℝ) ∞ (f ∘ fromBall) := by
    let := hM'.chartedSpace
    exact hf.comp (contMDiff_fromBall hM)
  filter_upwards [ae_isMorseFunction_add_inner hM' μ hf'] with a ha
  refine isMorseFunction_of_ballImage hM
    (hf.add (contMDiff_comp_val hM (contDiff_inner_ballDiffeo a))) (fun x => ?_) ha
  change f (fromBall (toBall x)) + ⟪a, ballDiffeo n x⟫ = f x + ⟪a, ballDiffeo n x⟫
  rw [fromBall_toBall]

/-- **Corollary 6.8** (Milnor, p. 37) for a slice submanifold `M ⊆ ℝⁿ`: *every smooth
`f : M → ℝ` can be uniformly approximated by a smooth function `g` without degenerate critical
points, and `g` can be chosen so that its derivatives of order `≤ r` on given compact sets
uniformly approximate those of `f`*.  Derivatives are taken in finitely many given coordinate
systems `y_j` of `M`, on compact sets `K_j` of their domains.  One can take
`g = f + ⟪a, β(·)⟫` with `a` small, `β` the diffeomorphism of `ℝⁿ` onto its open unit ball.
Neither boundedness of `f` nor compactness of `M` is needed. -/
theorem exists_isMorseFunction_approx_uniform {f : M → ℝ}
    (hf : letI := hM.chartedSpace; ContMDiff 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, ℝ) ∞ f)
    {ι : Type*} [Finite ι] (y : ι → OpenPartialHomeomorph M (𝔼 k))
    (hy : letI := hM.chartedSpace; ∀ j, IsSmoothCoord (𝔼 k) (y j)) (K : ι → Set (𝔼 k))
    (hK : ∀ j, IsCompact (K j)) (hKy : ∀ j, K j ⊆ (y j).target) (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    letI := hM.chartedSpace
    ∃ g : M → ℝ, IsMorseFunction (𝔼 k) g ∧ (∀ x, |g x - f x| < ε) ∧
      ∀ j, ∀ i ≤ r, ∀ u ∈ K j,
        ‖iteratedFDeriv ℝ i ((fun x => g x - f x) ∘ (y j).symm) u‖ < ε := by
  let := hM.chartedSpace
  have := hM.isManifold
  have := Fintype.ofFinite ι
  -- `h = β ∘ val`, smooth in every coordinate system
  have hsm : ∀ j, ContDiffOn ℝ ∞ (ballDiffeo n ∘ (Subtype.val : M → 𝔼 n) ∘ (y j).symm)
      (y j).target := fun j => by
    rw [← contMDiffOn_iff_contDiffOn]
    exact contDiff_ballDiffeo.contMDiff.comp_contMDiffOn
      (hM.contMDiff_val.comp_contMDiffOn (hy j).contMDiffOn_symm)
  have hbound : ∀ j i, ∃ C, ∀ u ∈ K j,
      ‖iteratedFDeriv ℝ i (ballDiffeo n ∘ (Subtype.val : M → 𝔼 n) ∘ (y j).symm) u‖ ≤ C :=
    fun j i => (hK j).exists_bound_of_continuousOn
      ((((hsm j).continuousOn_iteratedFDerivWithin (m := i) (by exact_mod_cast le_top)
        (y j).open_target.uniqueDiffOn).congr fun u hu =>
        (iteratedFDerivWithin_of_isOpen i (y j).open_target hu).symm).mono (hKy j))
  choose C hC using hbound
  obtain ⟨D, hD0, hCD⟩ : ∃ D : ℝ, 1 ≤ D ∧ ∀ j, ∀ i ≤ r, C j i ≤ D := by
    refine ⟨1 + ∑ j, ∑ i ∈ Finset.range (r + 1), |C j i|, by
      have : 0 ≤ ∑ j, ∑ i ∈ Finset.range (r + 1), |C j i| := by positivity
      linarith, fun j i hi => ?_⟩
    have h1 : |C j i| ≤ ∑ i ∈ Finset.range (r + 1), |C j i| :=
      Finset.single_le_sum (f := fun i => |C j i|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
    have h2 : ∑ i ∈ Finset.range (r + 1), |C j i| ≤
        ∑ j, ∑ i ∈ Finset.range (r + 1), |C j i| :=
      Finset.single_le_sum (f := fun j => ∑ i ∈ Finset.range (r + 1), |C j i|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    linarith [le_abs_self (C j i)]
  obtain ⟨δ, hδ0, hδD⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * D < ε := by
    refine ⟨ε / (D + 1), div_pos hε (by linarith), ?_⟩
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  -- a small `a` with `f + ⟪a, β⟫` Morse
  have hpos : (volume : Measure (𝔼 n)) (ball 0 δ) ≠ 0 :=
    (isOpen_ball.measure_pos volume (nonempty_ball.2 hδ0)).ne'
  obtain ⟨a, ha, hmorse⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
    (ae_restrict_of_ae (ae_isMorseFunction_add_inner_ballDiffeo hM volume hf))
  have ha' : ‖a‖ < δ := by
    rw [mem_ball, dist_zero_right] at ha
    exact ha
  have hdiff : ∀ x : M, (f x + ⟪a, ballDiffeo n x⟫) - f x = innerBilin n a (ballDiffeo n x) :=
    fun x => by
      rw [innerBilin_apply]
      ring
  have hnorm : ‖innerBilin n a‖ ≤ ‖a‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) fun v => by
      rw [innerBilin_apply]
      exact norm_inner_le_norm a v
  refine ⟨fun x => f x + ⟪a, ballDiffeo n x⟫, hmorse, fun x => ?_, fun j i hi u hu => ?_⟩
  · rw [hdiff, innerBilin_apply, ← Real.norm_eq_abs]
    calc ‖⟪a, ballDiffeo n (x : 𝔼 n)⟫‖ ≤ ‖a‖ * ‖ballDiffeo n (x : 𝔼 n)‖ :=
          norm_inner_le_norm _ _
      _ ≤ δ * D := mul_le_mul ha'.le ((norm_ballDiffeo_lt_one _).le.trans hD0)
          (norm_nonneg _) hδ0.le
      _ < ε := hδD
  · have hfun : (fun x : M => (f x + ⟪a, ballDiffeo n x⟫) - f x) ∘ (y j).symm =
        innerBilin n a ∘ (ballDiffeo n ∘ (Subtype.val : M → 𝔼 n) ∘ (y j).symm) := by
      funext u
      exact hdiff _
    rw [hfun, (innerBilin n a).iteratedFDeriv_comp_left
      ((hsm j).contDiffAt ((y j).open_target.mem_nhds (hKy j hu))) (by exact_mod_cast le_top)]
    calc _ ≤ ‖innerBilin n a‖ *
          ‖iteratedFDeriv ℝ i (ballDiffeo n ∘ (Subtype.val : M → 𝔼 n) ∘ (y j).symm) u‖ :=
          ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
      _ ≤ δ * D := mul_le_mul (hnorm.trans ha'.le) ((hC j i u hu).trans (hCD j i hi))
          (norm_nonneg _) hδ0.le
      _ < ε := hδD

end Corollary68

end Morse
