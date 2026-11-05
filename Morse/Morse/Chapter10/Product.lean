import Morse.Chapter1.ManifoldSubmanifold
import Morse.Chapter2.Submanifold

/-!
Milnor, *Morse Theory*, §16, p. 89: the manifold `M × ⋯ × M` (`k − 1` factors) in which the break
points of a broken geodesic live, for a submanifold `N ⊆ ℝᴷ`.

# Finite products and open subsets of slice submanifolds

Milnor identifies the broken geodesics of energy `< c` with "a certain open subset of the
`(k−1)`-fold product `M × ⋯ × M`" and "takes over the differentiable structure from this product"
(p. 89).  For a slice submanifold `N ⊆ V` (the companion project's `Milnor.IsSliceSubmanifold`)
this needs two facts which are evident for subsets of Euclidean space but must be built for
Mathlib's charted spaces:

* `Morse.SliceChart.pi`, `Morse.isSliceSubmanifold_pi`: **the product `N^ι = ∏_{j ∈ ι} N`** (`ι`
  finite) is a slice submanifold of `ι → V`, modelled on `ι → Z`, with the product slice charts;
* `Morse.SliceChart.inter`, `Morse.IsSliceSubmanifold.inter_isOpen`: **an open part `S ∩ O`** of a
  slice submanifold `S` (`O` open in the ambient space) is a slice submanifold;
* `Morse.tangentSubspace_pi_inter`: the tangent space of `N^ι ∩ O` at `y` is the product
  `∏_j T_{y_j}N` of the tangent spaces of the factors;
* `Morse.contMDiffAt_of_locally_eq`: a function on a slice submanifold which is, near a point, the
  restriction of a smooth function on an open set of the ambient space, is smooth there (Milnor's
  notion of smoothness for subsets of Euclidean space).
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set V} {ι : Type*} [Fintype ι]

/-! ### Products of slice charts -/

/-- **The product of slice charts** `σ_j` of `N`, a slice chart of `N^ι ⊆ (ι → V)`:
`y ↦ ((σ_j.φ (y j)).1, (σ_j.φ (y j)).2)_j`. -/
def SliceChart.pi (σ : ι → Milnor.SliceChart 𝓘(ℝ, V) Z W N) :
    Milnor.SliceChart 𝓘(ℝ, ι → V) (ι → Z) (ι → W) (Set.pi (univ : Set ι) fun _ => N) where
  φ :=
    { toFun := fun y => (fun j => ((σ j).φ (y j)).1, fun j => ((σ j).φ (y j)).2)
      invFun := fun zw j => (σ j).φ.invFun (zw.1 j, zw.2 j)
      source := Set.pi univ fun j => (σ j).φ.source
      target := {zw | ∀ j, (zw.1 j, zw.2 j) ∈ (σ j).φ.target}
      map_source' := fun y hy j => by
        simpa using (σ j).φ.apply_mem (hy j trivial)
      map_target' := fun zw hzw j _ => (σ j).φ.invFun_mem (hzw j)
      left_inv' := fun y hy => funext fun j => by
        simpa using (σ j).φ.invFun_apply (hy j trivial)
      right_inv' := fun zw hzw => by
        refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
        · simp only [(σ j).φ.apply_invFun (hzw j)]
        · simp only [(σ j).φ.apply_invFun (hzw j)]
      open_source := isOpen_set_pi finite_univ fun j _ => (σ j).φ.open_source
      open_target := by
        have : {zw : (ι → Z) × (ι → W) | ∀ j, (zw.1 j, zw.2 j) ∈ (σ j).φ.target} =
            ⋂ j, (fun zw : (ι → Z) × (ι → W) => (zw.1 j, zw.2 j)) ⁻¹' (σ j).φ.target := by
          ext zw; simp
        rw [this]
        exact isOpen_iInter_of_finite fun j => (σ j).φ.open_target.preimage (by fun_prop)
      contMDiffOn_toFun := by
        rw [contMDiffOn_iff_contDiffOn]
        refine ContDiffOn.prodMk (contDiffOn_pi.2 fun j => ?_) (contDiffOn_pi.2 fun j => ?_)
        · exact contDiff_fst.comp_contDiffOn ((contDiffOn_sliceChart (σ j)).comp
            (contDiff_apply ℝ V j).contDiffOn fun y hy => hy j trivial)
        · exact contDiff_snd.comp_contDiffOn ((contDiffOn_sliceChart (σ j)).comp
            (contDiff_apply ℝ V j).contDiffOn fun y hy => hy j trivial)
      contMDiffOn_invFun := by
        rw [contMDiffOn_iff_contDiffOn]
        refine contDiffOn_pi.2 fun j => ?_
        exact (contDiffOn_sliceChart_invFun (σ j)).comp
          (((contDiff_apply ℝ Z j).comp contDiff_fst).prodMk
            ((contDiff_apply ℝ W j).comp contDiff_snd)).contDiffOn fun zw hzw => hzw j }
  x₀ := fun j => (σ j).x₀
  x₀_mem := fun j _ => (σ j).x₀_mem
  x₀_source := fun j _ => (σ j).x₀_source
  slice := fun y hy => by
    change (∀ j ∈ univ, y j ∈ N) ↔ (fun j => ((σ j).φ (y j)).2) = 0
    rw [funext_iff]
    exact ⟨fun h j => ((σ j).slice _ (hy j trivial)).1 (h j trivial),
      fun h j _ => ((σ j).slice _ (hy j trivial)).2 (h j)⟩

@[simp] theorem SliceChart.pi_source (σ : ι → Milnor.SliceChart 𝓘(ℝ, V) Z W N) :
    (SliceChart.pi σ).φ.source = Set.pi univ fun j => (σ j).φ.source := rfl

theorem SliceChart.pi_apply_fst (σ : ι → Milnor.SliceChart 𝓘(ℝ, V) Z W N) (y : ι → V) :
    ((SliceChart.pi σ).φ y).1 = fun j => ((σ j).φ (y j)).1 := rfl

/-- The parametrization of the product chart is the product of the parametrizations. -/
theorem sliceParam_pi (σ : ι → Milnor.SliceChart 𝓘(ℝ, V) Z W N) (z : ι → Z) :
    sliceParam (SliceChart.pi σ) z = fun j => sliceParam (σ j) (z j) := rfl

/-- **`N^ι` is a slice submanifold** of `ι → V`, modelled on `ι → Z`. -/
theorem isSliceSubmanifold_pi (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) :
    Milnor.IsSliceSubmanifold 𝓘(ℝ, ι → V) (ι → Z) (ι → W) (Set.pi univ fun _ : ι => N) :=
  fun y hy => ⟨SliceChart.pi fun j => (hN (y j) (hy j trivial)).choose,
    fun j _ => (hN (y j) (hy j trivial)).choose_spec⟩

/-! ### Open subsets -/

/-- **Restricting a slice chart of `S` to an open set `O`** gives a slice chart of `S ∩ O`, with
base point any point of `S ∩ O` in its domain. -/
def SliceChart.inter {S : Set V} (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W S) {O : Set V}
    (hO : IsOpen O) {x₀ : V} (hx₀ : x₀ ∈ S ∩ O) (hx₀σ : x₀ ∈ σ.φ.source) :
    Milnor.SliceChart 𝓘(ℝ, V) Z W (S ∩ O) where
  φ := σ.φ.restrOpen O hO
  x₀ := x₀
  x₀_mem := hx₀
  x₀_source := ⟨hx₀σ, hx₀.2⟩
  slice := fun y hy => by
    change y ∈ S ∩ O ↔ (σ.φ y).2 = 0
    rw [← σ.slice y hy.1]
    exact ⟨fun h => h.1, fun h => ⟨h, hy.2⟩⟩

@[simp] theorem SliceChart.inter_source {S : Set V} (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W S)
    {O : Set V} (hO : IsOpen O) {x₀ : V} (hx₀ : x₀ ∈ S ∩ O) (hx₀σ : x₀ ∈ σ.φ.source) :
    (SliceChart.inter σ hO hx₀ hx₀σ).φ.source = σ.φ.source ∩ O := rfl

theorem sliceParam_inter {S : Set V} (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W S) {O : Set V}
    (hO : IsOpen O) {x₀ : V} (hx₀ : x₀ ∈ S ∩ O) (hx₀σ : x₀ ∈ σ.φ.source) (z : Z) :
    sliceParam (SliceChart.inter σ hO hx₀ hx₀σ) z = sliceParam σ z := rfl

/-- **An open part of a slice submanifold is a slice submanifold.** -/
theorem IsSliceSubmanifold.inter_isOpen {S : Set V} (hS : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W S)
    {O : Set V} (hO : IsOpen O) : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W (S ∩ O) :=
  fun y hy => ⟨SliceChart.inter (hS y hy.1).choose hO hy (hS y hy.1).choose_spec,
    (hS y hy.1).choose_spec, hy.2⟩

/-- **An open part `N^ι ∩ O` of a product** is a slice submanifold of `ι → V`. -/
theorem isSliceSubmanifold_pi_inter (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    {O : Set (ι → V)} (hO : IsOpen O) :
    Milnor.IsSliceSubmanifold 𝓘(ℝ, ι → V) (ι → Z) (ι → W) ((Set.pi univ fun _ : ι => N) ∩ O) :=
  IsSliceSubmanifold.inter_isOpen (isSliceSubmanifold_pi hN) hO

/-- The product chart at `y`, restricted to `O`: a slice chart of `N^ι ∩ O` at `y`. -/
def piInterChart (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {O : Set (ι → V)}
    (hO : IsOpen O) {y : ι → V} (hy : y ∈ (Set.pi univ fun _ : ι => N) ∩ O) :
    Milnor.SliceChart 𝓘(ℝ, ι → V) (ι → Z) (ι → W) ((Set.pi univ fun _ : ι => N) ∩ O) :=
  SliceChart.inter (SliceChart.pi fun j => (hN (y j) (hy.1 j trivial)).choose) hO hy
    fun j _ => (hN (y j) (hy.1 j trivial)).choose_spec

theorem mem_piInterChart_source (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {O : Set (ι → V)}
    (hO : IsOpen O) {y : ι → V} (hy : y ∈ (Set.pi univ fun _ : ι => N) ∩ O) :
    y ∈ (piInterChart hN hO hy).φ.source :=
  ⟨fun j _ => (hN (y j) (hy.1 j trivial)).choose_spec, hy.2⟩

/-! ### Tangent spaces of products -/

section Tangent

/-- **The tangent space of `N^ι ∩ O` at `y` is `∏_j T_{y_j}N`.** -/
theorem tangentSubspace_pi_inter (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    {O : Set (ι → V)} (hO : IsOpen O) (y : ↥((Set.pi univ fun _ : ι => N) ∩ O)) :
    tangentSubspace (isSliceSubmanifold_pi_inter hN hO) y =
      Submodule.pi univ fun j => tangentSubspace hN ⟨(y : ι → V) j, y.2.1 j trivial⟩ := by
  set σ : ι → Milnor.SliceChart 𝓘(ℝ, V) Z W N :=
    fun j => (hN ((y : ι → V) j) (y.2.1 j trivial)).choose
  have hσ : ∀ j, (y : ι → V) j ∈ (σ j).φ.source :=
    fun j => (hN ((y : ι → V) j) (y.2.1 j trivial)).choose_spec
  rw [tangentSubspace_eq_range_fderiv_sliceParam (isSliceSubmanifold_pi_inter hN hO)
    (piInterChart hN hO y.2) (mem_piInterChart_source hN hO y.2)]
  -- the parametrization is the product of the parametrizations of the factors
  set z₀ : ι → Z := ((piInterChart hN hO y.2).φ y).1
  have hz₀ : ∀ j, z₀ j = ((σ j).φ ((y : ι → V) j)).1 := fun j => rfl
  have hparam : sliceParam (piInterChart hN hO y.2) = fun z j => sliceParam (σ j) (z j) := rfl
  have hd : ∀ j, HasFDerivAt (fun z : ι → Z => sliceParam (σ j) (z j))
      ((fderiv ℝ (sliceParam (σ j)) (z₀ j)).comp (ContinuousLinearMap.proj j)) z₀ := by
    intro j
    have hm : z₀ j ∈ (σ j).toChart.target := by
      rw [hz₀]
      exact toChart_apply_mem_target (σ j) (q := ⟨(y : ι → V) j, y.2.1 j trivial⟩) (hσ j)
    exact ((contDiffAt_sliceParam (σ j) hm).differentiableAt (by simp)).hasFDerivAt.comp z₀
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => Z) j).hasFDerivAt
  have hD := hasFDerivAt_pi.2 hd
  rw [hparam, hD.fderiv]
  ext w
  simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe, Submodule.mem_pi, mem_univ,
    true_implies]
  constructor
  · rintro ⟨z, rfl⟩ j
    rw [tangentSubspace_eq_range_fderiv_sliceParam hN (σ j)
      (q := ⟨(y : ι → V) j, y.2.1 j trivial⟩) (hσ j)]
    exact ⟨z j, by simp [hz₀]⟩
  · intro hw
    have : ∀ j, ∃ z : Z, fderiv ℝ (sliceParam (σ j)) (z₀ j) z = w j := by
      intro j
      have h := hw j
      rw [tangentSubspace_eq_range_fderiv_sliceParam hN (σ j)
        (q := ⟨(y : ι → V) j, y.2.1 j trivial⟩) (hσ j)] at h
      obtain ⟨z, hz⟩ := h
      exact ⟨z, by rw [hz₀]; exact hz⟩
    choose z hz using this
    exact ⟨z, funext fun j => by simpa using hz j⟩

end Tangent

/-! ### Smooth functions on slice submanifolds -/

/-- **A function on a slice submanifold `S ⊆ V` which near `y` is the restriction of a smooth
function on an open set of `V` is smooth at `y`** (Milnor's notion of smoothness for subsets of
Euclidean space). -/
theorem contMDiffAt_of_locally_eq {S : Set V} (hS : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W S)
    {f : S → ℝ} {y : S} {O : Set V} (hO : IsOpen O) (hyO : (y : V) ∈ O) {F : V → ℝ}
    (hF : ContDiffOn ℝ ∞ F O) (hfF : ∀ x : S, (x : V) ∈ O → f x = F x) :
    letI := hS.chartedSpace
    ContMDiffAt 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) ∞ f y := by
  let _ := hS.chartedSpace
  have h1 := contMDiffAt_comp_val hS (q := y) le_rfl (hF.contDiffAt (hO.mem_nhds hyO))
  refine h1.congr_of_eventuallyEq ?_
  have hnhds : {x : S | (x : V) ∈ O} ∈ 𝓝 y :=
    (hO.preimage continuous_subtype_val).mem_nhds hyO
  filter_upwards [hnhds] with x hx
  exact hfF x hx

end Morse
