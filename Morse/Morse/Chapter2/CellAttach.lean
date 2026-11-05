import Morse.Chapter2.CellModel
import Morse.Chapter2.Regular
import Morse.Chapter1.MorseLemma

/-!
Milnor, *Morse Theory*, §3, pp. 14–19.

# Theorem 3.2 (passing a non-degenerate critical point attaches a `λ`-cell) on a Euclidean space

**Theorem 3.2** (p. 14), paraphrased: let `f : M → ℝ` be smooth and `p` a non-degenerate critical
point of index `λ`, `c = f(p)`, such that `f⁻¹[c - ε, c + ε]` is compact and contains no critical
point other than `p`, for some `ε > 0`. Then for all sufficiently small `ε`, `M^{c+ε}` has the
homotopy type of `M^{c-ε}` with a `λ`-cell attached. (The text as reproduced in the scan reads
"a `k`-cell", probably a defect of the scan; see `Exposition/Findings.md`, "About the scan".)

This file proves it for `M = E` a finite-dimensional real inner product space (Milnor's `ℝⁿ`; the
inner product is needed for Theorem 3.1), following Milnor's proof (pp. 15–19) step by step. The
computations in Morse coordinates are in `Morse/Chapter2/CellModel.lean`; Theorem 3.1 is
`Morse.theorem_3_1` (`Morse/Chapter2/Regular.lean`), used read-only.

## Milnor's proof, and where each step is

1. *Morse coordinates* (p. 15). Lemma 2.2 (`Morse.morse_lemma`) gives coordinates
   `u = (u¹, …, uⁿ)` around `p`, `u(p) = 0`, with `f = c - ∑_{i ≤ λ} (uⁱ)² + ∑_{i > λ} (uⁱ)²`.
   Splitting `u = (x, y) ∈ ℝ^λ × ℝ^{n-λ}` (`Morse.splitCoord`) turns this into a chart `φ` with
   `f = c - ‖x‖² + ‖y‖²` (`Morse.IsSplitMorseChart`, `Morse.exists_isSplitMorseChart`).
2. *Choice of `ε`* (p. 15): (1) `f⁻¹[c - ε, c + ε]` compact without critical points but `p`; (2)
   the image of the chart contains the ball `ξ + η ≤ 2ε` (`Morse.exists_morseChart_forall_small`).
3. *The function `F = f - μ(ξ + 2η)`* (p. 16), `Morse.milnorF`, with `μ = Morse.milnorMu ε`.
   It is smooth (`Morse.contDiff_milnorF`). **Assertion 1**: `F⁻¹(-∞, c+ε] = M^{c+ε}`
   (`Morse.sublevel_milnorF_add`). **Assertion 2**: `F` and `f` have the same critical points
   (`Morse.isCriticalPoint_milnorF_iff`). **Assertion 3**: `F⁻¹(-∞, c-ε]` is a strong deformation
   retract of `M^{c+ε}`, by Theorem 3.1 applied to `F` (`Morse.isStrongDeformationRetract_milnorF`).
4. *The handle* (pp. 17–18): `H` is the closure of `F⁻¹(-∞, c-ε] - M^{c-ε}` (`Morse.handleE`),
   `F⁻¹(-∞, c-ε] = M^{c-ε} ∪ H` (`Morse.sublevel_milnorF_eq_union`), the cell
   `e^λ = {ξ ≤ ε, η = 0}` (`Morse.cellE`) lies in `H` (`Morse.cellE_subset_handleE`) and meets
   `M^{c-ε}` in its boundary sphere (`Morse.cellE_inter_sublevel`).
5. **Assertion 4** (pp. 18–19): Milnor's three-case deformation `r_t` (`Morse.handleRetract`)
   shows that `M^{c-ε} ∪ e^λ` is a strong deformation retract of `M^{c-ε} ∪ H`
   (`Morse.isStrongDeformationRetract_handle`).
6. *Conclusion*: composing the deformations of steps 3 and 5,
   `Morse.isStrongDeformationRetract_union_cellE`; with the cell parametrized by the closed unit
   ball `D^λ` of `ℝ^λ`, `Morse.theorem_3_2`, and the homotopy equivalence
   `Morse.theorem_3_2_homotopyEquiv`. Remark 3.4 (the level `M^c`) is
   `Morse/Chapter2/CriticalLevel.lean`.

## What Milnor's text leaves implicit

* **"Choose `ε > 0` sufficiently small"** (p. 15). Both conditions persist for smaller `ε`:
  (1) because `f⁻¹[c - ε, c + ε]` is closed in the compact `f⁻¹[c - ε₀, c + ε₀]`, (2) because the
  image of the chart is open and contains `0` (`Morse.exists_forall_ball_subset_target`). This is
  how "for all sufficiently small `ε`" is formalized: `∃ ε₁ > 0, ∀ ε ∈ (0, ε₁], …`.
* **"It is easily verified that `F` is a well defined smooth function"** (p. 16). Outside the
  ellipsoid `ξ + 2η ≤ 2ε` the correction `μ(ξ + 2η)` vanishes. The ellipsoid lies in the ball of
  condition (2), hence in the image of the chart, and is compact; so its preimage in `M` is
  compact, hence closed (`M` is Hausdorff). The chart domain and the complement of that closed set
  are open, cover `M`, and `F` is smooth on each (`Morse.contDiff_milnorF`).
* **Assertion 3** uses Assertion 2 in the direction "a critical point of `F` is one of `f`", and
  needs `F⁻¹[c - ε, c + ε]` to be closed (as well as contained in the compact
  `f⁻¹[c - ε, c + ε]`) to be compact.
* **"Let `r_t` be the identity outside of `U`"** (p. 18). This pastes continuously with the three
  cases because on `F⁻¹(-∞, c-ε]`, `r_t` moves only points of the ellipsoid (closed in `M`) and
  keeps them in it; in particular it never leaves the chart, where `φ⁻¹` is defined. This is a
  second use of condition (2), not mentioned by Milnor (`Morse.retractModel_mem_target`,
  `Morse.handleRetract_of_notMem_ellipsoidE`, `Morse.continuous_handleRetract`).
* **"Together with Assertion 3, it completes the proof"** (p. 19): the two deformations are
  composed, first that of Theorem 3.1 for `F`, then Milnor's `r_t` (Lemma A(i) of the
  exposition, `Morse.IsStrongDeformationRetract.trans`). Both are strong deformation retractions,
  hence so is the composite.
* **"`e^λ` is attached to `M^{c-ε}` as required"** (p. 16). The cell is the image of the closed
  disk `D^λ` under the continuous injective map `χ(z) = φ⁻¹(√ε z, 0)`, hence homeomorphic to it
  (compact to Hausdorff), and `χ(z) ∈ M^{c-ε}` exactly when `‖z‖ = 1`, as
  `f(χ(z)) = c - ε‖z‖²` (`Morse.cellE_parametrization`). That the subspace `M^{c-ε} ∪ e^λ` of `M`
  is then the abstract space obtained by attaching `D^λ` to `M^{c-ε}` along `χ|S^{λ-1}` (Lemma D
  of the exposition) is `Morse/Chapter2/CellAdjunction.lean`, which states Theorem 3.2 literally
  (`Morse.theorem_3_2_attach`).
* **The index.** `λ` is `index (hessian f p)`, Mathlib's `sigNeg` of the Hessian
  (`Morse/Chapter1/Nondegenerate.lean`); the Morse lemma puts the `λ` negative squares first.

## Setting

`E` is a finite-dimensional real inner product space, `f : E → ℝ` is `C^∞`, and the chart takes
values in `X × Y` with `X = ℝ^λ`, `Y = ℝ^{n-λ}` realized as `EuclideanSpace`s indexed by the
first `λ` and the last `n - λ` coordinates; the cell is parametrized by the unit ball of
`EuclideanSpace ℝ (Fin λ)` through the evident isometry. Everything except the final assembly is
stated for an arbitrary split Morse chart `φ : E → X × Y` (`Morse.IsSplitMorseChart`), so that it
can be reused for charts of a manifold.
-/

open Set Filter Topology Function Module
open scoped ContDiff unitInterval

noncomputable section

namespace Morse

open CellModel

/-! ### Lemma A(i): strong deformation retractions compose -/

/-- A homotopy rel `S` is a homotopy rel every subset of `S`. -/
def homotopyRelMono {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f₀ f₁ : C(X, Y)}
    {S S' : Set X} (F : f₀.HomotopyRel f₁ S) (h : S' ⊆ S) : f₀.HomotopyRel f₁ S' where
  toHomotopy := F.toHomotopy
  prop' t x hx := F.prop' t x (h hx)

/-- **Lemma A(i) of the exposition**: if `A ⊆ B ⊆ C`, `A` is a strong deformation retract of `B`
and `B` one of `C`, then `A` is one of `C`: first deform `C` onto `B`, then `B` onto `A`. -/
theorem IsStrongDeformationRetract.trans {T : Type*} [TopologicalSpace T] {A B C : Set T}
    (hAB : A ⊆ B) (hBC : B ⊆ C)
    (hA : IsStrongDeformationRetract ((↑) ⁻¹' A : Set B))
    (hB : IsStrongDeformationRetract ((↑) ⁻¹' B : Set C)) :
    IsStrongDeformationRetract ((↑) ⁻¹' A : Set C) := by
  obtain ⟨r, hr, ⟨H⟩⟩ := hA
  obtain ⟨s, hs, ⟨G⟩⟩ := hB
  let s' : C(C, B) := ⟨fun x => ⟨s x, hs x⟩, (s.continuous.subtype_val).subtype_mk _⟩
  let i : C(B, C) := ⟨Set.inclusion hBC, continuous_inclusion hBC⟩
  have hsB : ∀ x : C, (x : T) ∈ B → s x = x := fun x hx => (G.fst_eq_snd hx).symm
  have hs_eq : i.comp s' = s := by ext x; rfl
  let K : (i.comp s').HomotopyRel (i.comp (r.comp s')) ((↑) ⁻¹' A) :=
    { toFun := fun p => i (H (p.1, s' p.2))
      continuous_toFun := i.continuous.comp (H.continuous.comp
        (continuous_fst.prodMk (s'.continuous.comp continuous_snd)))
      map_zero_left := fun x => by simp
      map_one_left := fun x => by simp
      prop' := fun t x hx => by
        have hxB : (x : T) ∈ B := hAB hx
        have h1 : s' x = ⟨x, hxB⟩ :=
          Subtype.ext (show ((s x : C) : T) = (x : T) from congrArg Subtype.val (hsB x hxB))
        change i (H (t, s' x)) = i (s' x)
        rw [h1, H.eq_fst t (show ((⟨x, hxB⟩ : B) : T) ∈ A from hx)]
        rfl }
  exact ⟨i.comp (r.comp s'), fun x => hr (s' x),
    ⟨(homotopyRelMono G (preimage_mono hAB)).trans (K.cast hs_eq rfl)⟩⟩

/-- Critical points only depend on the germ of the function. -/
theorem isCriticalPoint_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g h : E → ℝ}
    {q : E} (hgh : g =ᶠ[𝓝 q] h) : IsCriticalPoint g q ↔ IsCriticalPoint h q :=
  ⟨fun hg => HasFDerivAt.congr_of_eventuallyEq hg hgh.symm,
    fun hh => HasFDerivAt.congr_of_eventuallyEq hh hgh⟩

/-! ### Splitting the coordinates of `ℝⁿ` -/

/-- Milnor's splitting `u = (x, y)` of the coordinates of `ℝⁿ`, `x = (u¹, …, u^k)`,
`y = (u^{k+1}, …, uⁿ)` (`0`-based here: `i < k` and `k ≤ i`), with the Euclidean norm on each
factor. -/
def splitCoord (n k : ℕ) :
    (Fin n → ℝ) ≃L[ℝ] EuclideanSpace ℝ {i : Fin n // (i : ℕ) < k} ×
      EuclideanSpace ℝ {i : Fin n // k ≤ (i : ℕ)} :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun u => (WithLp.toLp 2 fun i => u i, WithLp.toLp 2 fun i => u i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun v i => if h : (i : ℕ) < k then v.1 ⟨i, h⟩ else v.2 ⟨i, not_lt.1 h⟩
      left_inv := fun u => by
        funext i
        by_cases h : (i : ℕ) < k <;> simp [h]
      right_inv := fun v => by
        refine Prod.ext ?_ ?_
        · ext i
          simp [i.2]
        · ext i
          simp [not_lt.2 i.2] }

/-- `ξ = (u¹)² + ⋯ + (u^k)²`. -/
theorem norm_sq_splitCoord_fst {n k : ℕ} (u : Fin n → ℝ) :
    ‖(splitCoord n k u).1‖ ^ 2 =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), u i ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  exact (Finset.sum_subtype _ (fun i => by simp) (fun i => u i ^ 2)).symm

/-- `η = (u^{k+1})² + ⋯ + (uⁿ)²`. -/
theorem norm_sq_splitCoord_snd {n k : ℕ} (u : Fin n → ℝ) :
    ‖(splitCoord n k u).2‖ ^ 2 =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ (i : ℕ)), u i ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  exact (Finset.sum_subtype _ (fun i => by simp) (fun i => u i ^ 2)).symm

/-- The first `k` of `n` coordinates are indexed by `Fin k`. -/
def negIdxEquiv {n k : ℕ} (hk : k ≤ n) : {i : Fin n // (i : ℕ) < k} ≃ Fin k where
  toFun i := ⟨i.1, i.2⟩
  invFun j := ⟨⟨j, lt_of_lt_of_le j.2 hk⟩, j.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### Morse charts in split form -/

section Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- A **Morse chart** at `p` (Lemma 2.2, as used on p. 15), with the coordinates split as
`(x, y) ∈ X × Y`: a smooth chart `φ` with smooth inverse, `p` in its source, `φ(p) = 0`, and
`f = f(p) - ‖x‖² + ‖y‖²` throughout the source. -/
structure IsSplitMorseChart (f : E → ℝ) (p : E) (φ : OpenPartialHomeomorph E (X × Y)) :
    Prop where
  mem_source : p ∈ φ.source
  apply_self : φ p = 0
  contDiffOn : ContDiffOn ℝ ∞ φ φ.source
  contDiffOn_symm : ContDiffOn ℝ ∞ φ.symm φ.target
  apply_eq : ∀ q ∈ φ.source, f q = morseQuad (f p) (φ q)

/-- **The lemma of Morse in split form**: a non-degenerate critical point of index `λ` has a Morse
chart with values in `ℝ^λ × ℝ^{n-λ}` (`Morse.morse_lemma` followed by `splitCoord`). -/
theorem exists_isSplitMorseChart [FiniteDimensional ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    {p : E} (hcrit : IsCriticalPoint f p) (hnd : IsNondegenerate (hessian f p)) :
    ∃ φ : OpenPartialHomeomorph E
        (EuclideanSpace ℝ {i : Fin (finrank ℝ E) // (i : ℕ) < index (hessian f p)} ×
          EuclideanSpace ℝ {i : Fin (finrank ℝ E) // index (hessian f p) ≤ (i : ℕ)}),
      IsSplitMorseChart f p φ := by
  obtain ⟨y, hpy, -, hyp, hys, hyt, hfy⟩ :=
    morse_lemma isOpen_univ (mem_univ p) hf.contDiffOn hcrit hnd
  refine ⟨y.transHomeomorph (splitCoord (finrank ℝ E) (index (hessian f p))).toHomeomorph,
    ⟨hpy, ?_, ?_, ?_, ?_⟩⟩
  · change splitCoord _ _ (y p) = 0
    rw [hyp, map_zero]
  · exact (splitCoord (finrank ℝ E) (index (hessian f p))).contDiff.comp_contDiffOn hys
  · change ContDiffOn ℝ ∞ (fun z => y.symm ((splitCoord _ _).symm z))
      ((splitCoord _ _).symm ⁻¹' y.target)
    exact hyt.comp (splitCoord (finrank ℝ E) (index (hessian f p))).symm.contDiff.contDiffOn
      fun z hz => hz
  · intro q hq
    rw [hfy q hq]
    change _ = morseQuad (f p) (splitCoord _ _ (y q))
    simp only [morseQuad, xi, eta, norm_sq_splitCoord_fst, norm_sq_splitCoord_snd]

variable {f : E → ℝ} {p : E} {φ : OpenPartialHomeomorph E (X × Y)}

theorem IsSplitMorseChart.contDiffAt (hφ : IsSplitMorseChart f p φ) {q : E}
    (hq : q ∈ φ.source) : ContDiffAt ℝ ∞ φ q :=
  hφ.contDiffOn.contDiffAt (φ.open_source.mem_nhds hq)

theorem IsSplitMorseChart.contDiffAt_symm (hφ : IsSplitMorseChart f p φ) {v : X × Y}
    (hv : v ∈ φ.target) : ContDiffAt ℝ ∞ φ.symm v :=
  hφ.contDiffOn_symm.contDiffAt (φ.open_target.mem_nhds hv)

/-- Critical points correspond under a Morse chart. -/
theorem IsSplitMorseChart.isCriticalPoint_comp_iff (hφ : IsSplitMorseChart f p φ)
    {g : X × Y → ℝ} {q : E} (hq : q ∈ φ.source) :
    IsCriticalPoint (g ∘ φ) q ↔ IsCriticalPoint g (φ q) := by
  refine ⟨fun h => ?_, fun h => h.comp ((hφ.contDiffAt hq).differentiableAt (by simp))⟩
  have h1 : IsCriticalPoint (g ∘ φ) (φ.symm (φ q)) := by rwa [φ.left_inv hq]
  have h2 := h1.comp ((hφ.contDiffAt_symm (φ.map_source hq)).differentiableAt (by simp))
  refine (isCriticalPoint_congr ?_).1 h2
  filter_upwards [φ.eventually_right_inverse' hq] with v hv
  simp [hv]

end Chart

/-! ### Milnor's function `F` on `E` (p. 16) -/

section Global

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- The correction term `μ(ξ + 2η)` of Milnor's `F`, transported by the chart and extended by
`0` outside its source. -/
def milnorBump (φ : OpenPartialHomeomorph E (X × Y)) (μ : ℝ → ℝ) : E → ℝ :=
  φ.source.indicator fun q => μ (xi (φ q) + 2 * eta (φ q))

/-- **Milnor's `F`** (p. 16): `F = f - μ(ξ + 2η)` within the coordinate neighbourhood, `F = f`
outside it. -/
def milnorF (f : E → ℝ) (φ : OpenPartialHomeomorph E (X × Y)) (μ : ℝ → ℝ) (q : E) : ℝ :=
  f q - milnorBump φ μ q

/-- The ellipsoid `ξ + 2η ≤ 2ε` in `E`, outside of which `F = f`. -/
def ellipsoidE (φ : OpenPartialHomeomorph E (X × Y)) (ε : ℝ) : Set E :=
  φ.symm '' ellipsoid ε

/-- **Milnor's cell** `e^λ = {ξ ≤ ε, η = 0}` in `E` (p. 15). -/
def cellE (φ : OpenPartialHomeomorph E (X × Y)) (ε : ℝ) : Set E :=
  φ.symm '' cellModel ε

/-- **Milnor's handle** `H` (p. 17): the closure of `F⁻¹(-∞, c-ε] - M^{c-ε}`. -/
def handleE (f : E → ℝ) (φ : OpenPartialHomeomorph E (X × Y)) (μ : ℝ → ℝ) (c ε : ℝ) : Set E :=
  closure (sublevel (milnorF f φ μ) (c - ε) \ sublevel f (c - ε))

variable {f : E → ℝ} {p : E} {φ : OpenPartialHomeomorph E (X × Y)} {ε : ℝ} {μ : ℝ → ℝ}

theorem isCompact_ellipsoid [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] (ε : ℝ) :
    IsCompact (ellipsoid ε : Set (X × Y)) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_ellipsoid ε)
    ((Metric.isBounded_closedBall (x := (0 : X × Y)) (r := |ε| + 1)).subset fun v hv => ?_)
  simp only [ellipsoid, mem_ofPred_eq, xi, eta] at hv
  rw [mem_closedBall_zero_iff, norm_prod_le_iff]
  have h1 := sq_nonneg ‖v.1‖
  have h2 := sq_nonneg ‖v.2‖
  have h3 := le_abs_self ε
  constructor <;> nlinarith [norm_nonneg v.1, norm_nonneg v.2, sq_nonneg (‖v.1‖ - 1),
    sq_nonneg (‖v.2‖ - 1)]

variable (hball : {v : X × Y | xi v + eta v ≤ 2 * ε} ⊆ φ.target)
include hball

omit [NormedSpace ℝ E] [InnerProductSpace ℝ X] [InnerProductSpace ℝ Y] in
theorem ellipsoid_subset_target : (ellipsoid ε : Set (X × Y)) ⊆ φ.target :=
  (ellipsoid_subset_ball ε).trans hball

omit [NormedSpace ℝ E] [InnerProductSpace ℝ X] [InnerProductSpace ℝ Y] in
theorem ellipsoidE_subset_source : ellipsoidE φ ε ⊆ φ.source := by
  rintro _ ⟨v, hv, rfl⟩
  exact φ.map_target (ellipsoid_subset_target hball hv)

omit [NormedSpace ℝ E] [InnerProductSpace ℝ X] [InnerProductSpace ℝ Y] in
theorem mem_ellipsoidE_iff {q : E} (hq : q ∈ φ.source) :
    q ∈ ellipsoidE φ ε ↔ φ q ∈ ellipsoid ε := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    rwa [φ.right_inv (ellipsoid_subset_target hball hv)]
  · exact fun h => ⟨φ q, h, φ.left_inv hq⟩

omit [NormedSpace ℝ E] in
theorem isCompact_ellipsoidE [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] :
    IsCompact (ellipsoidE φ ε) :=
  (isCompact_ellipsoid ε).image_of_continuousOn
    (φ.continuousOn_symm.mono (ellipsoid_subset_target hball))

omit [NormedSpace ℝ E] in
theorem isClosed_ellipsoidE [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] :
    IsClosed (ellipsoidE φ ε) :=
  (isCompact_ellipsoidE hball).isClosed

omit [NormedSpace ℝ E] [InnerProductSpace ℝ X] [InnerProductSpace ℝ Y] in
theorem milnorBump_eq_zero (hμ : IsMilnorMu ε μ) {q : E} (hq : q ∉ ellipsoidE φ ε) :
    milnorBump φ μ q = 0 := by
  by_cases hs : q ∈ φ.source
  · have h : φ q ∉ ellipsoid ε := fun h => hq ((mem_ellipsoidE_iff hball hs).2 h)
    rw [milnorBump, indicator_of_mem hs, hμ.eq_zero _ (le_of_lt (not_le.1 h))]
  · rw [milnorBump, indicator_of_notMem hs]

/-- **Milnor's `F` is smooth** ("it is easily verified", p. 16): on the source of the chart it is
`f - μ(ξ + 2η)`, and outside the compact, hence closed, ellipsoid `ξ + 2η ≤ 2ε` it is `f`. -/
theorem contDiff_milnorBump [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    (hφ : IsSplitMorseChart f p φ) (hμ : IsMilnorMu ε μ) : ContDiff ℝ ∞ (milnorBump φ μ) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  by_cases hs : q ∈ φ.source
  · have heq : milnorBump φ μ =ᶠ[𝓝 q] fun q => μ (xi (φ q) + 2 * eta (φ q)) := by
      filter_upwards [φ.open_source.mem_nhds hs] with q' hq'
      rw [milnorBump, indicator_of_mem hq']
    have hxi : ContDiff ℝ ∞ (xi : X × Y → ℝ) := (contDiff_norm_sq ℝ).comp contDiff_fst
    have heta : ContDiff ℝ ∞ (eta : X × Y → ℝ) := (contDiff_norm_sq ℝ).comp contDiff_snd
    refine ContDiffAt.congr_of_eventuallyEq ?_ heq
    exact hμ.contDiff.contDiffAt.comp q
      ((hxi.contDiffAt.comp q (hφ.contDiffAt hs)).add
        (contDiffAt_const.mul (heta.contDiffAt.comp q (hφ.contDiffAt hs))))
  · have hq : q ∉ ellipsoidE φ ε := fun h => hs (ellipsoidE_subset_source hball h)
    refine ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (0 : ℝ))) ?_
    filter_upwards [(isClosed_ellipsoidE hball).isOpen_compl.mem_nhds hq] with q' hq'
    exact milnorBump_eq_zero hball hμ hq'

theorem contDiff_milnorF [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] (hf : ContDiff ℝ ∞ f)
    (hφ : IsSplitMorseChart f p φ) (hμ : IsMilnorMu ε μ) : ContDiff ℝ ∞ (milnorF f φ μ) :=
  hf.sub (contDiff_milnorBump hball hφ hμ)

omit hball in
theorem milnorF_eq (hφ : IsSplitMorseChart f p φ) {q : E} (hq : q ∈ φ.source) :
    milnorF f φ μ q = morseF μ (f p) (φ q) := by
  rw [milnorF, milnorBump, indicator_of_mem hq, hφ.apply_eq q hq]
  rfl

omit [NormedSpace ℝ E] [InnerProductSpace ℝ X] [InnerProductSpace ℝ Y] in
theorem milnorF_eq_of_notMem (hμ : IsMilnorMu ε μ) {q : E} (hq : q ∉ ellipsoidE φ ε) :
    milnorF f φ μ q = f q := by
  rw [milnorF, milnorBump_eq_zero hball hμ hq, sub_zero]

omit hball [NormedSpace ℝ E] [InnerProductSpace ℝ X] [InnerProductSpace ℝ Y] in
theorem milnorF_le (hμ : IsMilnorMu ε μ) (q : E) : milnorF f φ μ q ≤ f q :=
  sub_le_self _ (indicator_nonneg (fun _ _ => hμ.nonneg _) _)

omit hball in
/-- `F(p) = c - μ(0)`. -/
theorem milnorF_apply_self (hφ : IsSplitMorseChart f p φ) : milnorF f φ μ p = f p - μ 0 := by
  rw [milnorF_eq hφ hφ.mem_source, hφ.apply_self]
  simp [morseF, xi, eta]

omit hball in
/-- **Assertion 1** (p. 16): `F⁻¹(-∞, c+ε] = M^{c+ε}`. -/
theorem sublevel_milnorF_add (hφ : IsSplitMorseChart f p φ) (hμ : IsMilnorMu ε μ) :
    sublevel (milnorF f φ μ) (f p + ε) = sublevel f (f p + ε) := by
  ext q
  by_cases hs : q ∈ φ.source
  · rw [mem_sublevel, mem_sublevel, milnorF_eq hφ hs, hφ.apply_eq q hs]
    exact morseF_le_iff hμ _ _
  · rw [mem_sublevel, mem_sublevel, milnorF, milnorBump, indicator_of_notMem hs, sub_zero]

/-- **Assertion 2** (p. 17): `F` and `f` have the same critical points. In the chart both have
only the origin (`CellModel.hasFDerivAt_morseF_zero_iff`); outside the ellipsoid they agree. -/
theorem isCriticalPoint_milnorF_iff [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    (hφ : IsSplitMorseChart f p φ) (hμ : IsMilnorMu ε μ) (q : E) :
    IsCriticalPoint (milnorF f φ μ) q ↔ IsCriticalPoint f q := by
  by_cases hs : q ∈ φ.source
  · have h1 : milnorF f φ μ =ᶠ[𝓝 q] morseF μ (f p) ∘ φ := by
      filter_upwards [φ.open_source.mem_nhds hs] with q' hq'
      exact milnorF_eq hφ hq'
    have h2 : f =ᶠ[𝓝 q] morseQuad (f p) ∘ φ := by
      filter_upwards [φ.open_source.mem_nhds hs] with q' hq'
      exact hφ.apply_eq q' hq'
    rw [isCriticalPoint_congr h1, isCriticalPoint_congr h2, hφ.isCriticalPoint_comp_iff hs,
      hφ.isCriticalPoint_comp_iff hs]
    exact (hasFDerivAt_morseF_zero_iff hμ _ _).trans (hasFDerivAt_morseQuad_zero_iff _ _).symm
  · have hq : q ∉ ellipsoidE φ ε := fun h => hs (ellipsoidE_subset_source hball h)
    refine isCriticalPoint_congr ?_
    filter_upwards [(isClosed_ellipsoidE hball).isOpen_compl.mem_nhds hq] with q' hq'
    exact milnorF_eq_of_notMem hball hμ hq'

/-- `F⁻¹(-∞, c-ε] = M^{c-ε} ∪ H` (p. 17). -/
theorem sublevel_milnorF_eq_union [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    (hf : ContDiff ℝ ∞ f) (hφ : IsSplitMorseChart f p φ) (hμ : IsMilnorMu ε μ) :
    sublevel (milnorF f φ μ) (f p - ε) = sublevel f (f p - ε) ∪ handleE f φ μ (f p) ε :=
  eq_union_closure_diff (fun q hq => (milnorF_le hμ q).trans hq)
    (isClosed_le (contDiff_milnorF hball hf hφ hμ).continuous continuous_const)

/-- **`e^λ ⊆ H`** (p. 18). -/
theorem cellE_subset_handleE (hφ : IsSplitMorseChart f p φ) (hμ : IsMilnorMu ε μ)
    (hε : 0 < ε) : cellE φ ε ⊆ handleE f φ μ (f p) ε := by
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨h1, h2⟩ := tendsto_smul_cellModel hε hv
  have hvt : v ∈ φ.target := ellipsoid_subset_target hball (cellModel_subset_ellipsoid hv)
  refine mem_closure_of_tendsto ((φ.continuousAt_symm hvt).tendsto.comp h1) (h2.mono fun s hs => ?_)
  have hwt := ellipsoid_subset_target hball (cellModel_subset_ellipsoid hs.1)
  have hd := mem_diff_of_mem_cellModel hμ (f p) hs.1 hs.2
  refine ⟨?_, fun h => hd.2 ?_⟩
  · rw [comp_apply, mem_sublevel, milnorF_eq hφ (φ.map_target hwt), φ.right_inv hwt]
    exact hd.1
  · rw [comp_apply, mem_sublevel, hφ.apply_eq _ (φ.map_target hwt), φ.right_inv hwt] at h
    exact h

/-- The cell lies in `F⁻¹(-∞, c-ε]`. -/
theorem cellE_subset_sublevel_milnorF (hφ : IsSplitMorseChart f p φ) (hμ : IsMilnorMu ε μ) :
    cellE φ ε ⊆ sublevel (milnorF f φ μ) (f p - ε) := by
  rintro _ ⟨v, hv, rfl⟩
  have hvt : v ∈ φ.target := ellipsoid_subset_target hball (cellModel_subset_ellipsoid hv)
  rw [mem_sublevel, milnorF_eq hφ (φ.map_target hvt), φ.right_inv hvt]
  exact (morseF_lt_of_mem_cellModel hμ _ hv).le

/-- `e^λ ∩ M^{c-ε}` is the boundary sphere `ξ = ε`, `η = 0` of the cell (p. 16: "`e^λ` is attached
to `M^{c-ε}` as required"). -/
theorem cellE_inter_sublevel (hφ : IsSplitMorseChart f p φ) :
    cellE φ ε ∩ sublevel f (f p - ε) = φ.symm '' {v | xi v = ε ∧ v.2 = 0} := by
  rw [← cellModel_inter_sublevel (f p) ε]
  ext q
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, hM⟩
    have hvt : v ∈ φ.target := ellipsoid_subset_target hball (cellModel_subset_ellipsoid hv)
    rw [mem_sublevel, hφ.apply_eq _ (φ.map_target hvt), φ.right_inv hvt] at hM
    exact ⟨v, ⟨hv, hM⟩, rfl⟩
  · rintro ⟨v, ⟨hv, hM⟩, rfl⟩
    have hvt : v ∈ φ.target := ellipsoid_subset_target hball (cellModel_subset_ellipsoid hv)
    refine ⟨⟨v, hv, rfl⟩, ?_⟩
    rw [mem_sublevel, hφ.apply_eq _ (φ.map_target hvt), φ.right_inv hvt]
    exact hM

/-! ### Milnor's deformation `r_t` on `E` (Assertion 4)

The deformation is built with a level `δ`: `δ = ε` for Assertion 4, `δ = 0` for Remark 3.4
(`Morse/Chapter2/CriticalLevel.lean`). The chart, `μ` and the ellipsoid keep their `ε`. -/

omit hball in
open Classical in
/-- **Milnor's deformation `r_t`** on `E` (Assertion 4, p. 18): `φ⁻¹ ∘ r_t ∘ φ` within the
coordinate neighbourhood, the identity outside it. -/
def handleRetract (φ : OpenPartialHomeomorph E (X × Y)) (δ t : ℝ) (q : E) : E :=
  if q ∈ φ.source then φ.symm (retractModel δ t (φ q)) else q

omit hball [NormedSpace ℝ E] [InnerProductSpace ℝ X] in
theorem handleRetract_of_mem {δ t : ℝ} {q : E} (hq : q ∈ φ.source) :
    handleRetract φ δ t q = φ.symm (retractModel δ t (φ q)) :=
  if_pos hq

omit hball [NormedSpace ℝ E] [InnerProductSpace ℝ X] in
theorem handleRetract_of_notMem {δ t : ℝ} {q : E} (hq : q ∉ φ.source) :
    handleRetract φ δ t q = q :=
  if_neg hq

/-- On `F⁻¹(-∞, c-δ]`, `r_t` does not leave the chart: it moves only points of the ellipsoid,
and keeps them there. -/
theorem retractModel_mem_target (hφ : IsSplitMorseChart f p φ) (hμ : IsMilnorMu ε μ)
    {δ t : ℝ} {q : E} (hq : q ∈ φ.source) (hF : milnorF f φ μ q ≤ f p - δ)
    (ht : t ∈ Icc (0 : ℝ) 1) : retractModel δ t (φ q) ∈ φ.target := by
  by_cases hE : φ q ∈ ellipsoid ε
  · exact ellipsoid_subset_target hball (retractModel_mem_ellipsoid ht hE)
  · rw [retractModel_of_notMem_ellipsoid hμ t (by rwa [← milnorF_eq hφ hq]) hE]
    exact φ.map_source hq

/-- `r_t` maps `F⁻¹(-∞, c-δ]` into itself (p. 19). -/
theorem milnorF_handleRetract_le (hφ : IsSplitMorseChart f p φ) (hμ : IsMilnorMu ε μ)
    {δ t : ℝ} {q : E} (hF : milnorF f φ μ q ≤ f p - δ) (ht : t ∈ Icc (0 : ℝ) 1) :
    milnorF f φ μ (handleRetract φ δ t q) ≤ milnorF f φ μ q := by
  by_cases hs : q ∈ φ.source
  · rw [handleRetract_of_mem hs]
    have hw := retractModel_mem_target hball hφ hμ hs hF ht
    rw [milnorF_eq hφ (φ.map_target hw), φ.right_inv hw, milnorF_eq hφ hs]
    exact morseF_retractModel_le hμ _ ht _
  · rw [handleRetract_of_notMem hs]

omit hball [NormedSpace ℝ E] [InnerProductSpace ℝ X] in
/-- `r_0 = id`. -/
theorem handleRetract_zero (δ : ℝ) (q : E) : handleRetract φ δ 0 q = q := by
  by_cases hs : q ∈ φ.source
  · rw [handleRetract_of_mem hs, retractModel_zero, φ.left_inv hs]
  · rw [handleRetract_of_notMem hs]

omit hball in
/-- `r_t` fixes `M^{c-δ}`. -/
theorem handleRetract_of_mem_sublevel (hφ : IsSplitMorseChart f p φ) {δ : ℝ} {q : E}
    (hq : f q ≤ f p - δ) (t : ℝ) : handleRetract φ δ t q = q := by
  by_cases hs : q ∈ φ.source
  · rw [handleRetract_of_mem hs, retractModel_of_morseQuad_le t (by rwa [← hφ.apply_eq q hs]),
      φ.left_inv hs]
  · rw [handleRetract_of_notMem hs]

omit [NormedSpace ℝ E] [InnerProductSpace ℝ X] in
/-- `r_t` fixes `e^λ`. -/
theorem handleRetract_of_mem_cellE {δ : ℝ} {q : E} (hq : q ∈ cellE φ ε) (t : ℝ) :
    handleRetract φ δ t q = q := by
  obtain ⟨v, hv, rfl⟩ := hq
  have hvt : v ∈ φ.target := ellipsoid_subset_target hball (cellModel_subset_ellipsoid hv)
  rw [handleRetract_of_mem (φ.map_target hvt), φ.right_inv hvt,
    retractModel_of_snd_eq_zero δ t hv.2]

/-- On `F⁻¹(-∞, c-δ]`, `r_t` is the identity outside the ellipsoid. -/
theorem handleRetract_of_notMem_ellipsoidE (hφ : IsSplitMorseChart f p φ)
    (hμ : IsMilnorMu ε μ) {δ : ℝ} {q : E} (hF : milnorF f φ μ q ≤ f p - δ)
    (hq : q ∉ ellipsoidE φ ε) (t : ℝ) : handleRetract φ δ t q = q := by
  by_cases hs : q ∈ φ.source
  · have hE : φ q ∉ ellipsoid ε := fun h => hq ((mem_ellipsoidE_iff hball hs).2 h)
    rw [handleRetract_of_mem hs,
      retractModel_of_notMem_ellipsoid hμ t (by rwa [← milnorF_eq hφ hs]) hE, φ.left_inv hs]
  · rw [handleRetract_of_notMem hs]

/-- `r_1` maps `F⁻¹(-∞, c-δ]` into `M^{c-δ} ∪ e^λ_δ`, where `e^λ_δ = {ξ ≤ δ, η = 0}`
(p. 19: Case 1 goes into the cell, Case 2 into `f⁻¹(c - δ)`, Case 3 is in `M^{c-δ}`). -/
theorem handleRetract_one_mem (hφ : IsSplitMorseChart f p φ) (hμ : IsMilnorMu ε μ) {δ : ℝ}
    {q : E} (hF : milnorF f φ μ q ≤ f p - δ) :
    handleRetract φ δ 1 q ∈ sublevel f (f p - δ) ∪ cellE φ δ := by
  by_cases hs : q ∈ φ.source
  · rw [handleRetract_of_mem hs]
    have hw := retractModel_mem_target hball hφ hμ hs hF ⟨zero_le_one, le_rfl⟩
    rcases retractModel_one_mem (f p) (φ q) with h | h
    · left
      rw [mem_sublevel, hφ.apply_eq _ (φ.map_target hw), φ.right_inv hw]
      exact h
    · exact Or.inr ⟨_, h, rfl⟩
  · left
    rw [handleRetract_of_notMem hs, mem_sublevel,
      ← milnorF_eq_of_notMem (f := f) hball hμ (fun h => hs (ellipsoidE_subset_source hball h))]
    exact hF

/-- **The continuity of `r_t`** on `[0, 1] × F⁻¹(-∞, c-δ]` ("let `r_t` be the identity outside of
`U`", p. 18): near a point of the chart it is `φ⁻¹ ∘ r_t ∘ φ`, continuous by
`CellModel.continuous_retractModel`; near a point outside the chart, which lies outside the closed
ellipsoid, it is the identity. -/
theorem continuous_handleRetract [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    (hφ : IsSplitMorseChart f p φ) (hμ : IsMilnorMu ε μ) (δ : ℝ) :
    Continuous fun z : I × sublevel (milnorF f φ μ) (f p - δ) => handleRetract φ δ z.1 z.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t₀, ⟨q₀, hq₀⟩⟩
  by_cases hs : q₀ ∈ φ.source
  · have hev : (fun z : I × sublevel (milnorF f φ μ) (f p - δ) => handleRetract φ δ z.1 z.2)
        =ᶠ[𝓝 (t₀, ⟨q₀, hq₀⟩)] fun z => φ.symm (retractModel δ z.1 (φ z.2)) := by
      have ho : IsOpen {z : I × sublevel (milnorF f φ μ) (f p - δ) | (z.2 : E) ∈ φ.source} :=
        φ.open_source.preimage (continuous_subtype_val.comp continuous_snd)
      filter_upwards [ho.mem_nhds hs] with z hz
      exact handleRetract_of_mem hz
    refine ContinuousAt.congr ?_ hev.symm
    have hw := retractModel_mem_target hball hφ hμ hs hq₀ t₀.2
    have h1 : ContinuousAt (fun z : I × sublevel (milnorF f φ μ) (f p - δ) => (z.1, φ z.2))
        (t₀, ⟨q₀, hq₀⟩) :=
      continuousAt_fst.prodMk
        ((φ.continuousAt hs).comp (continuous_subtype_val.comp continuous_snd).continuousAt)
    have h2 : ContinuousAt
        (fun z : I × sublevel (milnorF f φ μ) (f p - δ) => retractModel δ z.1 (φ z.2))
        (t₀, ⟨q₀, hq₀⟩) :=
      (continuous_retractModel δ).continuousAt.comp h1
    exact ContinuousAt.comp
      (f := fun z : I × sublevel (milnorF f φ μ) (f p - δ) => retractModel δ z.1 (φ z.2))
      (φ.continuousAt_symm hw) h2
  · have hq : q₀ ∉ ellipsoidE φ ε := fun h => hs (ellipsoidE_subset_source hball h)
    have hev : (fun z : I × sublevel (milnorF f φ μ) (f p - δ) => handleRetract φ δ z.1 z.2)
        =ᶠ[𝓝 (t₀, ⟨q₀, hq₀⟩)] fun z => (z.2 : E) := by
      have ho : IsOpen {z : I × sublevel (milnorF f φ μ) (f p - δ) | (z.2 : E) ∉ ellipsoidE φ ε} :=
        (isClosed_ellipsoidE hball).isOpen_compl.preimage
          (continuous_subtype_val.comp continuous_snd)
      filter_upwards [ho.mem_nhds hq] with z hz
      exact handleRetract_of_notMem_ellipsoidE hball hφ hμ z.2.2 hz z.1
    exact ContinuousAt.congr (continuous_subtype_val.comp continuous_snd).continuousAt hev.symm

/-- `r_t` as a map of `F⁻¹(-∞, c-δ]` into itself. -/
theorem handleRetract_mem (hφ : IsSplitMorseChart f p φ) (hμ : IsMilnorMu ε μ) {δ t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (q : sublevel (milnorF f φ μ) (f p - δ)) :
    handleRetract φ δ t q ∈ sublevel (milnorF f φ μ) (f p - δ) :=
  (milnorF_handleRetract_le hball hφ hμ q.2 ht).trans q.2

variable [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]

/-- Milnor's retraction `r_1` (his `r_0`) of `F⁻¹(-∞, c-δ]`. -/
def handleRetractOne (hφ : IsSplitMorseChart f p φ) (hμ : IsMilnorMu ε μ) (δ : ℝ) :
    C(sublevel (milnorF f φ μ) (f p - δ), sublevel (milnorF f φ μ) (f p - δ)) where
  toFun q := ⟨handleRetract φ δ 1 q, handleRetract_mem hball hφ hμ ⟨zero_le_one, le_rfl⟩ q⟩
  continuous_toFun := ((continuous_handleRetract hball hφ hμ δ).comp
    ((continuous_const : Continuous fun _ : sublevel (milnorF f φ μ) (f p - δ) =>
      (1 : I)).prodMk continuous_id)).subtype_mk _

/-- **Milnor's deformation retraction** (Assertion 4, p. 18) on `E`, as a homotopy of
`F⁻¹(-∞, c-δ]` from the identity to `r_1`, fixing pointwise any set `S` that `r_t` fixes. -/
def handleHomotopy (hφ : IsSplitMorseChart f p φ) (hμ : IsMilnorMu ε μ) (δ : ℝ) (S : Set E)
    (hS : ∀ q ∈ S, ∀ t, handleRetract φ δ t q = q) :
    (ContinuousMap.id (sublevel (milnorF f φ μ) (f p - δ))).HomotopyRel
      (handleRetractOne hball hφ hμ δ)
      ((↑) ⁻¹' S : Set (sublevel (milnorF f φ μ) (f p - δ))) where
  toFun z := ⟨handleRetract φ δ z.1 z.2, handleRetract_mem hball hφ hμ z.1.2 z.2⟩
  continuous_toFun := (continuous_handleRetract hball hφ hμ δ).subtype_mk _
  map_zero_left q := Subtype.ext (handleRetract_zero δ (q : E))
  map_one_left _ := rfl
  prop' t q hq := Subtype.ext (hS q hq t)

/-- **Assertion 4** (p. 18): `M^{c-ε} ∪ e^λ` is a strong deformation retract of
`M^{c-ε} ∪ H = F⁻¹(-∞, c-ε]`. -/
theorem isStrongDeformationRetract_handle (hφ : IsSplitMorseChart f p φ) (hμ : IsMilnorMu ε μ) :
    IsStrongDeformationRetract
      ((↑) ⁻¹' (sublevel f (f p - ε) ∪ cellE φ ε) :
        Set (sublevel (milnorF f φ μ) (f p - ε))) :=
  ⟨handleRetractOne hball hφ hμ ε, fun q => handleRetract_one_mem hball hφ hμ q.2,
    ⟨handleHomotopy hball hφ hμ ε _ fun q hq t => by
      rcases hq with hq | hq
      · exact handleRetract_of_mem_sublevel hφ hq t
      · exact handleRetract_of_mem_cellE hball hq t⟩⟩

end Global

/-! ### Assertion 3 and the conclusion -/

section Conclusion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  {f : E → ℝ} {p : E} {φ : OpenPartialHomeomorph E (X × Y)} {ε : ℝ} {μ : ℝ → ℝ}
  (hball : {v : X × Y | xi v + eta v ≤ 2 * ε} ⊆ φ.target)
include hball

/-- **Assertion 3** (p. 17): `F⁻¹(-∞, c-ε]` is a strong deformation retract of `M^{c+ε}`.
`F⁻¹[c-ε, c+ε]` lies in `f⁻¹[c-ε, c+ε]` (Assertion 1 and `F ≤ f`), so it is compact; a critical
point of `F` in it would be one of `f` (Assertion 2), hence `p`; but `F(p) = c - μ(0) < c - ε`.
So Theorem 3.1 applies to `F` (`Morse.theorem_3_1`). -/
theorem isStrongDeformationRetract_milnorF (hf : ContDiff ℝ ∞ f) (hφ : IsSplitMorseChart f p φ)
    (hμ : IsMilnorMu ε μ) (hε : 0 < ε) (hK : IsCompact (f ⁻¹' Icc (f p - ε) (f p + ε)))
    (honly : ∀ q ∈ f ⁻¹' Icc (f p - ε) (f p + ε), IsCriticalPoint f q → q = p) :
    IsStrongDeformationRetract
      ((↑) ⁻¹' sublevel (milnorF f φ μ) (f p - ε) : Set (sublevel f (f p + ε))) := by
  have hF := contDiff_milnorF hball hf hφ hμ
  have hsub : milnorF f φ μ ⁻¹' Icc (f p - ε) (f p + ε) ⊆ f ⁻¹' Icc (f p - ε) (f p + ε) :=
    fun q hq => ⟨hq.1.trans (milnorF_le hμ q),
      show q ∈ sublevel f (f p + ε) from sublevel_milnorF_add hφ hμ ▸ hq.2⟩
  have hK' : IsCompact (milnorF f φ μ ⁻¹' Icc (f p - ε) (f p + ε)) :=
    hK.of_isClosed_subset (isClosed_Icc.preimage hF.continuous) hsub
  have hcrit : ∀ q ∈ milnorF f φ μ ⁻¹' Icc (f p - ε) (f p + ε),
      ¬IsCriticalPoint (milnorF f φ μ) q := by
    intro q hq hc
    have hqp := honly q (hsub hq) ((isCriticalPoint_milnorF_iff hball hφ hμ q).1 hc)
    subst hqp
    have := hq.1
    rw [milnorF_apply_self hφ] at this
    linarith [hμ.lt_apply_zero]
  have h := (theorem_3_1 hF (by linarith) hK' hcrit).2.1
  rwa [sublevel_milnorF_add hφ hμ] at h

/-- **Theorem 3.2, given a Morse chart** (pp. 15–19): if the chart contains the ball
`ξ + η ≤ 2ε` and `f⁻¹[c-ε, c+ε]` is compact with no critical point but `p`, then
`M^{c-ε} ∪ e^λ` is a strong deformation retract of `M^{c+ε}` (Assertions 3 and 4, and
Lemma A(i)). -/
theorem isStrongDeformationRetract_union_cellE (hf : ContDiff ℝ ∞ f)
    (hφ : IsSplitMorseChart f p φ) (hμ : IsMilnorMu ε μ) (hε : 0 < ε)
    (hK : IsCompact (f ⁻¹' Icc (f p - ε) (f p + ε)))
    (honly : ∀ q ∈ f ⁻¹' Icc (f p - ε) (f p + ε), IsCriticalPoint f q → q = p) :
    IsStrongDeformationRetract
      ((↑) ⁻¹' (sublevel f (f p - ε) ∪ cellE φ ε) : Set (sublevel f (f p + ε))) := by
  have h1 : sublevel f (f p - ε) ∪ cellE φ ε ⊆ sublevel (milnorF f φ μ) (f p - ε) :=
    union_subset (fun q hq => (milnorF_le hμ q).trans hq)
      (cellE_subset_sublevel_milnorF hball hφ hμ)
  have h2 : sublevel (milnorF f φ μ) (f p - ε) ⊆ sublevel f (f p + ε) := by
    rw [← sublevel_milnorF_add hφ hμ]
    exact sublevel_mono _ (by linarith)
  exact IsStrongDeformationRetract.trans h1 h2 (isStrongDeformationRetract_handle hball hφ hμ)
    (isStrongDeformationRetract_milnorF hball hf hφ hμ hε hK honly)

end Conclusion

section Disk

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-! ### The cell as an embedded disk -/

omit [NormedSpace ℝ E] [InnerProductSpace ℝ X] [InnerProductSpace ℝ Y] in
/-- The ball `ξ + η ≤ 2ε` lies in the target of the chart for all small `ε` (Milnor's
condition (2), p. 15, "for all sufficiently small `ε`"). -/
theorem exists_forall_ball_subset_target {φ : OpenPartialHomeomorph E (X × Y)}
    (h0 : (0 : X × Y) ∈ φ.target) :
    ∃ ε₁ > 0, ∀ ε ≤ ε₁, {v : X × Y | xi v + eta v ≤ 2 * ε} ⊆ φ.target := by
  obtain ⟨r, hr, hrt⟩ := Metric.isOpen_iff.1 φ.open_target 0 h0
  refine ⟨r ^ 2 / 4, by positivity, fun ε hε v hv => hrt ?_⟩
  simp only [mem_ofPred_eq, xi, eta] at hv
  have h1 : ‖v.1‖ ^ 2 < r ^ 2 := by nlinarith [sq_nonneg ‖v.2‖, sq_nonneg r]
  have h2 : ‖v.2‖ ^ 2 < r ^ 2 := by nlinarith [sq_nonneg ‖v.1‖, sq_nonneg r]
  rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, max_lt_iff]
  exact ⟨lt_of_pow_lt_pow_left₀ 2 hr.le h1, lt_of_pow_lt_pow_left₀ 2 hr.le h2⟩

/-- A parametrization of Milnor's cell by the closed unit ball of `Z ≅ X`:
`χ(z) = φ⁻¹(√ε z, 0)`. -/
theorem cellE_parametrization {φ : OpenPartialHomeomorph E (X × Y)} {f : E → ℝ} {p : E} {ε : ℝ}
    (hball : {v : X × Y | xi v + eta v ≤ 2 * ε} ⊆ φ.target) (hφ : IsSplitMorseChart f p φ)
    (hε : 0 < ε) {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] (ι : X ≃ₗᵢ[ℝ] Z) :
    let χ : Z → E := fun z => φ.symm (Real.sqrt ε • ι.symm z, 0)
    χ '' Metric.closedBall 0 1 = cellE φ ε ∧ ContinuousOn χ (Metric.closedBall 0 1) ∧
      InjOn χ (Metric.closedBall 0 1) ∧
      (∀ z ∈ Metric.closedBall (0 : Z) 1, f (χ z) = f p - ε * ‖z‖ ^ 2) := by
  intro χ
  have hs : Real.sqrt ε ≠ 0 := (Real.sqrt_pos.2 hε).ne'
  have hss : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
  have hxi : ∀ z : Z, xi ((Real.sqrt ε • ι.symm z, (0 : Y)) : X × Y) = ε * ‖z‖ ^ 2 := by
    intro z
    simp only [xi, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hss,
      LinearIsometryEquiv.norm_map]
  have hmem : ∀ z ∈ Metric.closedBall (0 : Z) 1,
      ((Real.sqrt ε • ι.symm z, (0 : Y)) : X × Y) ∈ cellModel ε := by
    intro z hz
    rw [mem_closedBall_zero_iff] at hz
    refine ⟨?_, rfl⟩
    rw [hxi]
    have : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
    nlinarith
  have htgt : ∀ z ∈ Metric.closedBall (0 : Z) 1,
      ((Real.sqrt ε • ι.symm z, (0 : Y)) : X × Y) ∈ φ.target := fun z hz =>
    ellipsoid_subset_target hball (cellModel_subset_ellipsoid (hmem z hz))
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨_, hmem z hz, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      refine ⟨ι ((Real.sqrt ε)⁻¹ • v.1), ?_, ?_⟩
      · rw [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map, norm_smul, norm_inv,
          Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.2 hε), inv_mul_le_iff₀ (Real.sqrt_pos.2 hε),
          mul_one]
        have h1 : ‖v.1‖ ^ 2 ≤ ε := hv.1
        rw [← Real.sqrt_sq (norm_nonneg v.1)]
        exact Real.sqrt_le_sqrt h1
      · simp only [χ, LinearIsometryEquiv.symm_apply_apply, smul_smul, mul_inv_cancel₀ hs,
          one_smul]
        rw [show ((v.1, (0 : Y)) : X × Y) = v from Prod.ext rfl hv.2.symm]
  · refine φ.continuousOn_symm.comp (Continuous.continuousOn (by fun_prop)) htgt
  · intro z hz z' hz' h
    have h1 := φ.symm.injOn (htgt z hz) (htgt z' hz') h
    simp only [Prod.mk.injEq, and_true] at h1
    exact ι.symm.injective (smul_right_injective X hs h1)
  · intro z hz
    rw [hφ.apply_eq _ (φ.map_target (htgt z hz)), φ.right_inv (htgt z hz), morseQuad, hxi]
    simp [eta]

end Disk

/-! ### Theorem 3.2 -/

section Theorem32

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Milnor's choice of `ε`** (p. 15): around a non-degenerate critical point `p` of index `λ`
with `f⁻¹[c - ε₀, c + ε₀]` compact and free of other critical points, there is a Morse chart `φ`
with values in `ℝ^λ × ℝ^{n-λ}` such that, for all sufficiently small `ε > 0`, (1)
`f⁻¹[c - ε, c + ε]` is compact and contains no critical point other than `p`, and (2) the image of
`φ` contains the ball `ξ + η ≤ 2ε`. -/
theorem exists_morseChart_forall_small {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {p : E}
    (hcrit : IsCriticalPoint f p) (hnd : IsNondegenerate (hessian f p)) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hK : IsCompact (f ⁻¹' Icc (f p - ε₀) (f p + ε₀)))
    (honly : ∀ q ∈ f ⁻¹' Icc (f p - ε₀) (f p + ε₀), IsCriticalPoint f q → q = p) :
    ∃ φ : OpenPartialHomeomorph E
        (EuclideanSpace ℝ {i : Fin (finrank ℝ E) // (i : ℕ) < index (hessian f p)} ×
          EuclideanSpace ℝ {i : Fin (finrank ℝ E) // index (hessian f p) ≤ (i : ℕ)}),
      IsSplitMorseChart f p φ ∧ ∃ ε₁ > 0, ∀ ε, 0 < ε → ε ≤ ε₁ →
        {v | xi v + eta v ≤ 2 * ε} ⊆ φ.target ∧ IsCompact (f ⁻¹' Icc (f p - ε) (f p + ε)) ∧
          ∀ q ∈ f ⁻¹' Icc (f p - ε) (f p + ε), IsCriticalPoint f q → q = p := by
  obtain ⟨φ, hφ⟩ := exists_isSplitMorseChart hf hcrit hnd
  have h0 : (0 : _) ∈ φ.target := hφ.apply_self ▸ φ.map_source hφ.mem_source
  obtain ⟨ε₂, hε₂, hball⟩ := exists_forall_ball_subset_target h0
  refine ⟨φ, hφ, min ε₀ ε₂, lt_min hε₀ hε₂, fun ε hε hε₁ => ?_⟩
  have hsub : f ⁻¹' Icc (f p - ε) (f p + ε) ⊆ f ⁻¹' Icc (f p - ε₀) (f p + ε₀) :=
    preimage_mono (Icc_subset_Icc (by linarith [min_le_left ε₀ ε₂])
      (by linarith [min_le_left ε₀ ε₂]))
  exact ⟨hball ε (hε₁.trans (min_le_right _ _)),
    hK.of_isClosed_subset (isClosed_Icc.preimage hf.continuous) hsub,
    fun q hq => honly q (hsub hq)⟩

/-- **Theorem 3.2** (Milnor, p. 14) on a finite-dimensional real inner product space `E`
(`ℝⁿ`). Let `f : E → ℝ` be smooth and `p` a non-degenerate critical point of index
`λ = index (hessian f p)`, `c = f(p)`, and suppose that for some `ε₀ > 0`, `f⁻¹[c - ε₀, c + ε₀]` is
compact and contains no critical point of `f` other than `p`. Then for all sufficiently small
`ε > 0` there is a map `χ` from the closed unit ball `D^λ` of `ℝ^λ` to `E` (the cell `e^λ`) which
is continuous and injective (hence a homeomorphism onto its image), meets `M^{c-ε}` exactly in the
image of the boundary sphere `S^{λ-1}`, lies in `M^{c+ε}`, and such that `M^{c-ε} ∪ e^λ` is a
strong deformation retract of `M^{c+ε}`. In particular `M^{c+ε}` has the homotopy type of
`M^{c-ε} ∪ e^λ` (`Morse.theorem_3_2_homotopyEquiv`), which is `M^{c-ε}` with a `λ`-cell attached
along `χ|S^{λ-1}` (`Morse.theorem_3_2_attach`). -/
theorem theorem_3_2 {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {p : E} (hcrit : IsCriticalPoint f p)
    (hnd : IsNondegenerate (hessian f p)) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hK : IsCompact (f ⁻¹' Icc (f p - ε₀) (f p + ε₀)))
    (honly : ∀ q ∈ f ⁻¹' Icc (f p - ε₀) (f p + ε₀), IsCriticalPoint f q → q = p) :
    ∃ ε₁ > 0, ∀ ε, 0 < ε → ε ≤ ε₁ →
      ∃ χ : EuclideanSpace ℝ (Fin (index (hessian f p))) → E,
        ContinuousOn χ (Metric.closedBall 0 1) ∧ InjOn χ (Metric.closedBall 0 1) ∧
        (∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (index (hessian f p)))) 1,
          χ z ∈ sublevel f (f p - ε) ↔ ‖z‖ = 1) ∧
        χ '' Metric.closedBall 0 1 ⊆ sublevel f (f p + ε) ∧
        IsStrongDeformationRetract
          ((↑) ⁻¹' (sublevel f (f p - ε) ∪ χ '' Metric.closedBall 0 1) :
            Set (sublevel f (f p + ε))) := by
  obtain ⟨φ, hφ, ε₁, hε₁, H⟩ := exists_morseChart_forall_small hf hcrit hnd hε₀ hK honly
  have hk : index (hessian f p) ≤ finrank ℝ E := sigPos_le_finrank _
  refine ⟨ε₁, hε₁, fun ε hε hεε₁ => ?_⟩
  obtain ⟨hball, hKε, honlyε⟩ := H ε hε hεε₁
  obtain ⟨himage, hcont, hinj, hval⟩ := cellE_parametrization hball hφ hε
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (negIdxEquiv hk))
  refine ⟨_, hcont, hinj, fun z hz => ?_, ?_, ?_⟩
  · rw [mem_sublevel, hval z hz]
    rw [mem_closedBall_zero_iff] at hz
    constructor
    · intro h
      have : 1 ≤ ‖z‖ ^ 2 := by
        by_contra h'
        nlinarith
      nlinarith [norm_nonneg z]
    · intro h
      rw [h]
      linarith
  · rintro _ ⟨z, hz, rfl⟩
    rw [mem_sublevel, hval z hz]
    nlinarith [sq_nonneg ‖z‖]
  · rw [himage]
    exact isStrongDeformationRetract_union_cellE hball hf hφ (isMilnorMu_milnorMu hε) hε hKε
      honlyε

/-- **Theorem 3.2, homotopy type** (Milnor, p. 14): under the hypotheses of `theorem_3_2`, for all
sufficiently small `ε > 0` the inclusion `M^{c-ε} ∪ e^λ → M^{c+ε}` is a homotopy equivalence,
where `e^λ = χ(D^λ)` is a `λ`-cell meeting `M^{c-ε}` exactly in `χ(S^{λ-1})`. -/
theorem theorem_3_2_homotopyEquiv {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {p : E}
    (hcrit : IsCriticalPoint f p) (hnd : IsNondegenerate (hessian f p)) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hK : IsCompact (f ⁻¹' Icc (f p - ε₀) (f p + ε₀)))
    (honly : ∀ q ∈ f ⁻¹' Icc (f p - ε₀) (f p + ε₀), IsCriticalPoint f q → q = p) :
    ∃ ε₁ > 0, ∀ ε, 0 < ε → ε ≤ ε₁ →
      ∃ χ : EuclideanSpace ℝ (Fin (index (hessian f p))) → E,
        ContinuousOn χ (Metric.closedBall 0 1) ∧ InjOn χ (Metric.closedBall 0 1) ∧
        (∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (index (hessian f p)))) 1,
          χ z ∈ sublevel f (f p - ε) ↔ ‖z‖ = 1) ∧
        ∃ h : sublevel f (f p - ε) ∪ χ '' Metric.closedBall 0 1 ⊆ sublevel f (f p + ε),
          ∃ e : ContinuousMap.HomotopyEquiv
              ↥(sublevel f (f p - ε) ∪ χ '' Metric.closedBall 0 1) ↥(sublevel f (f p + ε)),
            ⇑e = Set.inclusion h := by
  obtain ⟨ε₁, hε₁, H⟩ := theorem_3_2 hf hcrit hnd hε₀ hK honly
  refine ⟨ε₁, hε₁, fun ε hε hεε₁ => ?_⟩
  obtain ⟨χ, hcont, hinj, hbdry, hsub, hsdr⟩ := H ε hε hεε₁
  have h : sublevel f (f p - ε) ∪ χ '' Metric.closedBall 0 1 ⊆ sublevel f (f p + ε) :=
    union_subset (sublevel_mono f (by linarith)) hsub
  exact ⟨χ, hcont, hinj, hbdry, h, hsdr.exists_homotopyEquiv h⟩

end Theorem32

end Morse
