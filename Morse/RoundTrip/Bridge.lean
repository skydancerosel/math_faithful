import RoundTrip.BridgePrelude
import RoundTrip.Blind.V8_13

/-! Bridge between the project's slice submanifolds `N ⊆ V` (induced metric and connection) and the
abstract Mathlib vocabulary of the blind files (namespace `RoundTrip.Bridge`). See the end of the
file for a summary. -/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace RoundTrip.Bridge

/-- `ℝⁿ`, as in the blind files. -/
abbrev Rn (k : ℕ) := EuclideanSpace ℝ (Fin k)

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {n : ℕ} {N : Set V}

/-- The slice submanifold `N`, as a type carrying the project's manifold structure
(`hN.chartedSpace`). It is definitionally the subtype `↥N`. -/
def Sub (_hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) : Type := N

variable (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)

instance : TopologicalSpace (Sub hN) := inferInstanceAs (TopologicalSpace N)
instance : ChartedSpace (Rn n) (Sub hN) := hN.chartedSpace
instance : IsManifold 𝓘(ℝ, Rn n) ∞ (Sub hN) := hN.isManifold
instance : T2Space (Sub hN) := inferInstanceAs (T2Space N)

/-- The inclusion `N → V`. -/
def incl : Sub hN → V := Subtype.val

/-- The derivative of the inclusion: `T_xN = ℝⁿ → V` (chart coordinates to ambient vectors). -/
def D (x : Sub hN) : Rn n →L[ℝ] V := mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, V) (incl hN) x

/-- Its left inverse on `T_xN`: the chart coordinates of an ambient vector (`Morse.tanCoord`). -/
def L (x : Sub hN) : V →L[ℝ] Rn n := Morse.tanCoord hN x

/-- The tangential projection `P_x` (`Morse.tanProj`). -/
def P (x : Sub hN) : V →L[ℝ] V := Morse.tanProj hN x

variable {hN}

theorem contMDiff_incl : ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, V) ∞ (incl hN) := hN.contMDiff_val

theorem L_D (x : Sub hN) (z : Rn n) : L hN x (D hN x z) = z := Morse.tanCoord_mfderiv_val hN x z

theorem D_mem (x : Sub hN) (z : Rn n) : D hN x z ∈ Morse.tangentSubspace hN x := ⟨z, rfl⟩

theorem D_L {x : Sub hN} {v : V} (hv : v ∈ Morse.tangentSubspace hN x) : D hN x (L hN x v) = v :=
  Morse.mfderiv_val_tanCoord hN hv

theorem D_injective (x : Sub hN) : Injective (D hN x) := fun a b h => by
  rw [← L_D x a, h, L_D]

theorem P_D (x : Sub hN) (z : Rn n) : P hN x (D hN x z) = D hN x z :=
  Morse.tanProj_eq_self hN (D_mem x z)

theorem D_L_P (x : Sub hN) (v : V) : D hN x (L hN x (P hN x v)) = P hN x v :=
  D_L (Morse.tanProj_apply_mem hN x v)

theorem inner_P_left (x : Sub hN) (v w : V) : ⟪P hN x v, w⟫ = ⟪v, P hN x w⟫ :=
  Morse.inner_tanProj_left hN x v w

theorem L_P_D (x : Sub hN) (z : Rn n) : L hN x (P hN x (D hN x z)) = z := by
  rw [P_D, L_D]

/-! ### Charts -/

/-- The derivative of the first component of the slice chart chosen at `x₀`, at an ambient point. -/
def A (x₀ : Sub hN) (y : V) : V →L[ℝ] Rn n :=
  (ContinuousLinearMap.fst ℝ (Rn n) W).comp (fderiv ℝ (Morse.sliceAt hN x₀).φ y)

/-- The derivative of the parametrization of the slice chart chosen at `x₀`. -/
def B (x₀ : Sub hN) (u : Rn n) : Rn n →L[ℝ] V :=
  fderiv ℝ (Morse.sliceParam (Morse.sliceAt hN x₀)) u

theorem mem_chart_source_iff {x₀ x : Sub hN} :
    x ∈ (chartAt (Rn n) x₀).source ↔ (incl hN x) ∈ (Morse.sliceAt hN x₀).φ.source := Iff.rfl

theorem chartAt_apply (x₀ x : Sub hN) :
    chartAt (Rn n) x₀ x = ((Morse.sliceAt hN x₀).φ (incl hN x)).1 := rfl

theorem mfderiv_chartAt {x₀ x : Sub hN} (hx : x ∈ (chartAt (Rn n) x₀).source) :
    mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) (chartAt (Rn n) x₀) x = (A x₀ (incl hN x)).comp (D hN x) := by
  set σ := Morse.sliceAt hN x₀
  have hφ : HasFDerivAt σ.φ (fderiv ℝ σ.φ (incl hN x)) (incl hN x) :=
    (Milnor.Problems.sliceChart_differentiableAt σ hx).hasFDerivAt
  have hg : HasFDerivAt (fun y => (σ.φ y).1) (A x₀ (incl hN x)) (incl hN x) := hφ.fst
  have hval : MDifferentiableAt 𝓘(ℝ, Rn n) 𝓘(ℝ, V) (incl hN) x :=
    contMDiff_incl.mdifferentiableAt (by simp)
  have hcomp : mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) ((fun y => (σ.φ y).1) ∘ incl hN) x =
      (A x₀ (incl hN x)).comp (D hN x) := by
    rw [mfderiv_comp x hg.differentiableAt.mdifferentiableAt hval, mfderiv_eq_fderiv, hg.fderiv]
    rfl
  exact hcomp

/-- The fibre coordinate of `(x, v) ∈ TN` in the trivialization at `x₀`. -/
theorem trivializationAt_snd {x₀ x : Sub hN} (hx : x ∈ (chartAt (Rn n) x₀).source)
    (v : TangentSpace 𝓘(ℝ, Rn n) x) :
    (trivializationAt (Rn n) (TangentSpace 𝓘(ℝ, Rn n)) x₀ ⟨x, v⟩).2 = A x₀ (incl hN x) (D hN x v) := by
  rw [TangentBundle.trivializationAt_apply]
  change tangentCoordChange 𝓘(ℝ, Rn n) x x₀ x v = _
  rw [← mfderiv_chartAt_eq_tangentCoordChange hx, mfderiv_chartAt hx]
  rfl

theorem D_eq_B {x₀ x : Sub hN} (hx : x ∈ (chartAt (Rn n) x₀).source) :
    D hN x = (B x₀ (chartAt (Rn n) x₀ x)).comp ((A x₀ (incl hN x)).comp (D hN x)) := by
  set σ := Morse.sliceAt hN x₀
  have hu : chartAt (Rn n) x₀ x ∈ σ.toChart.target := Morse.toChart_apply_mem_target σ hx
  have hev : incl hN =ᶠ[𝓝 x] Morse.sliceParam σ ∘ chartAt (Rn n) x₀ := by
    filter_upwards [σ.toChart.open_source.mem_nhds hx] with y hy
    exact (Morse.sliceParam_toChart σ hy).symm
  have hp : MDifferentiableAt 𝓘(ℝ, Rn n) 𝓘(ℝ, V) (Morse.sliceParam σ) (chartAt (Rn n) x₀ x) :=
    ((Morse.contDiffAt_sliceParam σ hu).differentiableAt (by simp)).mdifferentiableAt
  have hc : MDifferentiableAt 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) (chartAt (Rn n) x₀) x :=
    mdifferentiableAt_atlas (ChartedSpace.chart_mem_atlas _) hx
  rw [← mfderiv_chartAt hx]
  unfold D
  rw [hev.mfderiv_eq, mfderiv_comp x hp hc, mfderiv_eq_fderiv]
  rfl

theorem D_apply_eq_B {x₀ x : Sub hN} (hx : x ∈ (chartAt (Rn n) x₀).source)
    (v : TangentSpace 𝓘(ℝ, Rn n) x) :
    D hN x v = B x₀ (chartAt (Rn n) x₀ x)
      ((trivializationAt (Rn n) (TangentSpace 𝓘(ℝ, Rn n)) x₀ ⟨x, v⟩).2) := by
  rw [trivializationAt_snd hx]
  exact DFunLike.congr_fun (D_eq_B hx) v

theorem contMDiffOn_A (x₀ : Sub hN) :
    ContMDiffOn 𝓘(ℝ, Rn n) 𝓘(ℝ, V →L[ℝ] Rn n) ∞ (fun x : Sub hN => A x₀ (incl hN x))
      (chartAt (Rn n) x₀).source := by
  set σ := Morse.sliceAt hN x₀
  have h1 : ContDiffOn ℝ ∞ (fun y => A x₀ y) σ.φ.source := by
    have := ((Milnor.Problems.sliceChart_contDiffOn σ).fderiv_of_isOpen σ.φ.open_source
      (m := ∞) (by simp))
    exact (ContinuousLinearMap.contDiff (ContinuousLinearMap.compL ℝ V (Rn n × W) (Rn n)
      (ContinuousLinearMap.fst ℝ (Rn n) W))).comp_contDiffOn this
  exact (contMDiffOn_iff_contDiffOn.2 h1).comp contMDiff_incl.contMDiffOn (fun x hx => hx)

theorem contMDiffOn_B (x₀ : Sub hN) :
    ContMDiffOn 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n →L[ℝ] V) ∞ (fun x : Sub hN => B x₀ (chartAt (Rn n) x₀ x))
      (chartAt (Rn n) x₀).source := by
  set σ := Morse.sliceAt hN x₀
  have h1 : ContDiffOn ℝ ∞ (B x₀) σ.toChart.target :=
    (Morse.contDiffOn_sliceParam σ).fderiv_of_isOpen (Morse.isOpen_toChart_target σ) (by simp)
  exact (contMDiffOn_iff_contDiffOn.2 h1).comp contMDiffOn_chart
    (fun x hx => σ.toChart.map_source hx)

theorem trivializationAt_snd' {x₀ : Sub hN} {z : TangentBundle 𝓘(ℝ, Rn n) (Sub hN)}
    (hz : z.proj ∈ (chartAt (Rn n) x₀).source) :
    (trivializationAt (Rn n) (TangentSpace 𝓘(ℝ, Rn n)) x₀ z).2 =
      A x₀ (incl hN z.proj) (D hN z.proj z.2) :=
  trivializationAt_snd hz z.2

theorem D_apply_eq_B' {x₀ : Sub hN} {z : TangentBundle 𝓘(ℝ, Rn n) (Sub hN)}
    (hz : z.proj ∈ (chartAt (Rn n) x₀).source) :
    D hN z.proj z.2 = B x₀ (chartAt (Rn n) x₀ z.proj)
      ((trivializationAt (Rn n) (TangentSpace 𝓘(ℝ, Rn n)) x₀ z).2) :=
  D_apply_eq_B hz z.2

/-! ### Smoothness of maps into `TN`, read in `V` -/

section TangentSmooth

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} {MB : Type*} [TopologicalSpace MB] [ChartedSpace HB MB]

/-- A map into `TN` is smooth iff its base point is smooth and its ambient vector is smooth. -/
theorem contMDiffWithinAt_tangent_iff {F : MB → TangentBundle 𝓘(ℝ, Rn n) (Sub hN)} {s : Set MB}
    {b : MB} :
    ContMDiffWithinAt IB (𝓘(ℝ, Rn n)).tangent ∞ F s b ↔
      ContMDiffWithinAt IB 𝓘(ℝ, Rn n) ∞ (fun b => (F b).proj) s b ∧
      ContMDiffWithinAt IB 𝓘(ℝ, V) ∞ (fun b => D hN (F b).proj (F b).2) s b := by
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine and_congr_right fun hp => ?_
  set x₀ := (F b).proj
  have hx₀ : x₀ ∈ (chartAt (Rn n) x₀).source := mem_chart_source _ _
  have hev : ∀ᶠ b' in 𝓝[s] b, (F b').proj ∈ (chartAt (Rn n) x₀).source :=
    hp.continuousWithinAt.preimage_mem_nhdsWithin ((chartAt (Rn n) x₀).open_source.mem_nhds hx₀)
  constructor
  · intro h
    have hB : ContMDiffWithinAt IB 𝓘(ℝ, Rn n →L[ℝ] V) ∞
        (fun b' => B x₀ (chartAt (Rn n) x₀ (F b').proj)) s b :=
      ((contMDiffOn_B x₀).contMDiffAt ((chartAt (Rn n) x₀).open_source.mem_nhds hx₀)).comp_contMDiffWithinAt
        (f := fun b' => (F b').proj) b hp
    refine (hB.clm_apply h).congr_of_eventuallyEq ?_ (D_apply_eq_B' hx₀)
    filter_upwards [hev] with b' hb'
    exact D_apply_eq_B' hb'
  · intro h
    have hA : ContMDiffWithinAt IB 𝓘(ℝ, V →L[ℝ] Rn n) ∞
        (fun b' => A x₀ (incl hN (F b').proj)) s b :=
      ((contMDiffOn_A x₀).contMDiffAt ((chartAt (Rn n) x₀).open_source.mem_nhds hx₀)).comp_contMDiffWithinAt
        (f := fun b' => (F b').proj) b hp
    refine (hA.clm_apply h).congr_of_eventuallyEq ?_ (trivializationAt_snd' hx₀)
    filter_upwards [hev] with b' hb'
    exact trivializationAt_snd' hb'

/-- A map into `TN` is differentiable iff its base point and its ambient vector are. -/
theorem mdifferentiableWithinAt_tangent_iff {F : MB → TangentBundle 𝓘(ℝ, Rn n) (Sub hN)}
    {s : Set MB} {b : MB} :
    MDifferentiableWithinAt IB (𝓘(ℝ, Rn n)).tangent F s b ↔
      MDifferentiableWithinAt IB 𝓘(ℝ, Rn n) (fun b => (F b).proj) s b ∧
      MDifferentiableWithinAt IB 𝓘(ℝ, V) (fun b => D hN (F b).proj (F b).2) s b := by
  rw [mdifferentiableWithinAt_totalSpace]
  refine and_congr_right fun hp => ?_
  set x₀ := (F b).proj
  have hx₀ : x₀ ∈ (chartAt (Rn n) x₀).source := mem_chart_source _ _
  have hev : ∀ᶠ b' in 𝓝[s] b, (F b').proj ∈ (chartAt (Rn n) x₀).source :=
    hp.continuousWithinAt.preimage_mem_nhdsWithin ((chartAt (Rn n) x₀).open_source.mem_nhds hx₀)
  constructor
  · intro h
    have hB : MDifferentiableWithinAt IB 𝓘(ℝ, Rn n →L[ℝ] V)
        (fun b' => B x₀ (chartAt (Rn n) x₀ (F b').proj)) s b :=
      (((contMDiffOn_B x₀).contMDiffAt ((chartAt (Rn n) x₀).open_source.mem_nhds hx₀)).mdifferentiableAt
        (by simp)).comp_mdifferentiableWithinAt (f := fun b' => (F b').proj) (x := b) hp
    refine (hB.clm_apply h).congr_of_eventuallyEq ?_ (D_apply_eq_B' hx₀)
    filter_upwards [hev] with b' hb'
    exact D_apply_eq_B' hb'
  · intro h
    have hA : MDifferentiableWithinAt IB 𝓘(ℝ, V →L[ℝ] Rn n)
        (fun b' => A x₀ (incl hN (F b').proj)) s b :=
      (((contMDiffOn_A x₀).contMDiffAt ((chartAt (Rn n) x₀).open_source.mem_nhds hx₀)).mdifferentiableAt
        (by simp)).comp_mdifferentiableWithinAt (f := fun b' => (F b').proj) (x := b) hp
    refine (hA.clm_apply h).congr_of_eventuallyEq ?_ (trivializationAt_snd' hx₀)
    filter_upwards [hev] with b' hb'
    exact trivializationAt_snd' hb'

end TangentSmooth

/-! ### The induced metric -/

/-- `T ↦ ⟪T ·, T ·⟫`, the pull-back of the inner product by an operator. -/
def pullInner (T : Rn n →L[ℝ] V) : Rn n →L[ℝ] Rn n →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ (Rn n) V ℝ).flip T).comp ((innerSL ℝ (E := V)).comp T)

theorem pullInner_apply (T : Rn n →L[ℝ] V) (v w : Rn n) : pullInner T v w = ⟪T v, T w⟫ := rfl

theorem contDiff_pullInner : ContDiff ℝ ∞ (pullInner (V := V) (n := n)) := by
  rw [contDiff_clm_apply_iff]
  intro v
  rw [contDiff_clm_apply_iff]
  intro w
  simp only [pullInner_apply]
  exact (contDiff_id.clm_apply contDiff_const).inner ℝ (contDiff_id.clm_apply contDiff_const)

/-- The induced metric on `T_xN`: `⟨v, w⟩ = ⟪D_x v, D_x w⟫`. -/
def gInner (x : Sub hN) :
    TangentSpace 𝓘(ℝ, Rn n) x →L[ℝ] TangentSpace 𝓘(ℝ, Rn n) x →L[ℝ] ℝ :=
  pullInner (D hN x)

theorem gInner_apply (x : Sub hN) (v w : TangentSpace 𝓘(ℝ, Rn n) x) :
    gInner x v w = ⟪D hN x v, D hN x w⟫ := rfl

theorem isVonNBounded_gInner (x : Sub hN) :
    Bornology.IsVonNBounded ℝ {v : TangentSpace 𝓘(ℝ, Rn n) x | gInner x v v < 1} := by
  change Bornology.IsVonNBounded ℝ {v : Rn n | ⟪D hN x v, D hN x v⟫ < 1}
  rw [NormedSpace.isVonNBounded_iff]
  obtain ⟨K, -, hK⟩ := ((D hN x : Rn n →L[ℝ] V) : Rn n →ₗ[ℝ] V).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.2 (D_injective x))
  refine (hK.isBounded_preimage (Metric.isBounded_ball (x := (0 : V)) (r := 1))).subset ?_
  intro v hv
  simp only [mem_ofPred_eq] at hv
  simp only [mem_preimage, Metric.mem_ball, dist_zero_right, ContinuousLinearMap.coe_coe]
  rw [real_inner_self_eq_norm_sq] at hv
  nlinarith [norm_nonneg (D hN x v)]

theorem coord_gInner {x₀ x : Sub hN} (hx : x ∈ (chartAt (Rn n) x₀).source) :
    (trivializationAt (Rn n →L[ℝ] Rn n →L[ℝ] ℝ)
      (fun x : Sub hN => TangentSpace 𝓘(ℝ, Rn n) x →L[ℝ] TangentSpace 𝓘(ℝ, Rn n) x →L[ℝ] ℝ) x₀
      ⟨x, gInner x⟩).2 = pullInner (B x₀ (chartAt (Rn n) x₀ x)) := by
  rw [hom_trivializationAt_apply]
  ext v w
  have hx' : x ∈ (trivializationAt (Rn n) (TangentSpace 𝓘(ℝ, Rn n)) x₀).baseSet := hx
  rw [inCoordinates_apply_eq₂ hx' hx' (Set.mem_univ _)]
  rw [gInner_apply, pullInner_apply, D_apply_eq_B hx, D_apply_eq_B hx,
    Bundle.Trivialization.apply_mk_symm _ hx', Bundle.Trivialization.apply_mk_symm _ hx']
  simp

/-- **The induced Riemannian metric on `N`**, a smooth Riemannian metric on `TN`. -/
def metric : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, Rn n) ∞ (Rn n)
    (fun x : Sub hN => TangentSpace 𝓘(ℝ, Rn n) x) where
  inner := gInner
  symm x v w := real_inner_comm _ _
  pos x v hv := real_inner_self_pos.2 fun h => hv (D_injective x (h.trans (map_zero _).symm))
  isVonNBounded := isVonNBounded_gInner
  contMDiff := by
    intro x₀
    rw [Bundle.contMDiffAt_section]
    have hx₀ : x₀ ∈ (chartAt (Rn n) x₀).source := mem_chart_source _ _
    have h1 : ContMDiffAt 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n →L[ℝ] Rn n →L[ℝ] ℝ) ∞
        (fun x => pullInner (B x₀ (chartAt (Rn n) x₀ x))) x₀ :=
      contDiff_pullInner.contMDiff.contMDiffAt.comp x₀
        ((contMDiffOn_B x₀).contMDiffAt ((chartAt (Rn n) x₀).open_source.mem_nhds hx₀))
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [(chartAt (Rn n) x₀).open_source.mem_nhds hx₀] with x hx
    exact coord_gInner hx

instance : Bundle.RiemannianBundle (fun x : Sub hN => TangentSpace 𝓘(ℝ, Rn n) x) :=
  ⟨(metric (hN := hN)).toRiemannianMetric⟩

open Bundle in
/-- The Riemannian inner product of `T_xN` is the ambient inner product of `D_x v, D_x w`. -/
theorem inner_eq (x : Sub hN) (v w : TangentSpace 𝓘(ℝ, Rn n) x) :
    inner ℝ v w = ⟪D hN x v, D hN x w⟫ := rfl

open Bundle in
theorem norm_eq (x : Sub hN) (v : TangentSpace 𝓘(ℝ, Rn n) x) : ‖v‖ = ‖D hN x v‖ := by
  rw [norm_eq_sqrt_real_inner v, inner_eq, ← norm_eq_sqrt_real_inner]

open Bundle in
instance : IsContMDiffRiemannianBundle 𝓘(ℝ, Rn n) ∞ (Rn n)
    (fun x : Sub hN => TangentSpace 𝓘(ℝ, Rn n) x) :=
  ⟨⟨gInner, (metric (hN := hN)).contMDiff, fun _ _ _ => rfl⟩⟩

/-! ### Vector fields read in `V` -/

/-- The ambient field `p ↦ D_p (X p) ∈ V` of a vector field `X` on `N`. -/
def amb (X : (p : Sub hN) → TangentSpace 𝓘(ℝ, Rn n) p) (p : Sub hN) : V := D hN p (X p)

theorem amb_mem (X : (p : Sub hN) → TangentSpace 𝓘(ℝ, Rn n) p) (p : Sub hN) :
    amb X p ∈ Morse.tangentSubspace hN p := D_mem p (X p)

theorem L_P_amb (X : (p : Sub hN) → TangentSpace 𝓘(ℝ, Rn n) p) (p : Sub hN) :
    L hN p (P hN p (amb X p)) = X p := L_P_D p (X p)

theorem contMDiff_section_iff {X : (p : Sub hN) → TangentSpace 𝓘(ℝ, Rn n) p} :
    ContMDiff 𝓘(ℝ, Rn n) (𝓘(ℝ, Rn n)).tangent ∞
      (fun p => (⟨p, X p⟩ : TangentBundle 𝓘(ℝ, Rn n) (Sub hN))) ↔
      ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, V) ∞ (amb X) := by
  simp only [← contMDiffWithinAt_univ, ContMDiff]
  refine forall_congr' fun p => ?_
  rw [contMDiffWithinAt_tangent_iff]
  exact ⟨fun h => h.2, fun h => ⟨contMDiffWithinAt_id, h⟩⟩

theorem contMDiffAt_section_iff {X : (p : Sub hN) → TangentSpace 𝓘(ℝ, Rn n) p} {p : Sub hN} :
    ContMDiffAt 𝓘(ℝ, Rn n) (𝓘(ℝ, Rn n)).tangent ∞
      (fun p => (⟨p, X p⟩ : TangentBundle 𝓘(ℝ, Rn n) (Sub hN))) p ↔
      ContMDiffAt 𝓘(ℝ, Rn n) 𝓘(ℝ, V) ∞ (amb X) p := by
  simp only [← contMDiffWithinAt_univ]
  rw [contMDiffWithinAt_tangent_iff]
  exact ⟨fun h => h.2, fun h => ⟨contMDiffWithinAt_id, h⟩⟩

theorem mdifferentiableAt_section_iff {X : (p : Sub hN) → TangentSpace 𝓘(ℝ, Rn n) p}
    {p : Sub hN} :
    MDifferentiableAt 𝓘(ℝ, Rn n) (𝓘(ℝ, Rn n)).tangent
      (fun p => (⟨p, X p⟩ : TangentBundle 𝓘(ℝ, Rn n) (Sub hN))) p ↔
      MDifferentiableAt 𝓘(ℝ, Rn n) 𝓘(ℝ, V) (amb X) p := by
  simp only [← mdifferentiableWithinAt_univ]
  rw [mdifferentiableWithinAt_tangent_iff]
  exact ⟨fun h => h.2, fun h => ⟨mdifferentiableWithinAt_id, h⟩⟩

/-- The derivative of a map `N → V`, as a linear map `ℝⁿ → V`. -/
def dV (F : Sub hN → V) (x : Sub hN) : Rn n →L[ℝ] V := mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, V) F x

/-! ### The induced connection -/

/-- The induced covariant derivative: `(∇_v Y)(p) = P_p (dŶ_p v)`, read in chart coordinates. -/
def covFun (Y : (p : Sub hN) → TangentSpace 𝓘(ℝ, Rn n) p) (p : Sub hN) :
    TangentSpace 𝓘(ℝ, Rn n) p →L[ℝ] TangentSpace 𝓘(ℝ, Rn n) p :=
  (L hN p).comp ((P hN p).comp (mvfderiv 𝓘(ℝ, Rn n) (amb Y) p))

theorem covFun_apply (Y : (p : Sub hN) → TangentSpace 𝓘(ℝ, Rn n) p) (p : Sub hN)
    (v : TangentSpace 𝓘(ℝ, Rn n) p) :
    covFun Y p v = L hN p (P hN p (mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, V) (amb Y) p v)) := rfl

theorem D_covFun (Y : (p : Sub hN) → TangentSpace 𝓘(ℝ, Rn n) p) (p : Sub hN)
    (v : TangentSpace 𝓘(ℝ, Rn n) p) :
    D hN p (covFun Y p v) = P hN p (mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, V) (amb Y) p v) := D_L_P _ _

theorem isCovariantDerivativeOn_covFun :
    IsCovariantDerivativeOn (Rn n) (covFun (hN := hN)) Set.univ where
  add {σ σ' x} hσ hσ' _ := by
    have h1 := mdifferentiableAt_section_iff.1 hσ
    have h2 := mdifferentiableAt_section_iff.1 hσ'
    have : amb (σ + σ') = amb σ + amb σ' := by
      funext p; exact map_add (D hN p) _ _
    simp only [covFun, this, mvfderiv_add h1 h2, ContinuousLinearMap.comp_add]
    rfl
  leibniz {σ g x} hσ hg _ := by
    have h1 := mdifferentiableAt_section_iff.1 hσ
    have : amb (g • σ) = g • amb σ := by
      funext p; exact map_smul (D hN p) _ _
    simp only [covFun, this, mvfderiv_smul hg h1]
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, map_add, map_smul]
    rw [L_P_amb]
    rfl

/-- **The induced (Levi-Civita) connection of `N`**, as a Mathlib covariant derivative on `TN`. -/
def conn : CovariantDerivative 𝓘(ℝ, Rn n) (Rn n) (TangentSpace 𝓘(ℝ, Rn n) : Sub hN → Type) :=
  ⟨covFun, isCovariantDerivativeOn_covFun⟩

theorem conn_apply (Y : (p : Sub hN) → TangentSpace 𝓘(ℝ, Rn n) p) (p : Sub hN)
    (v : TangentSpace 𝓘(ℝ, Rn n) p) :
    conn Y p v = L hN p (P hN p (mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, V) (amb Y) p v)) := rfl

theorem contMDiff_P : ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, V →L[ℝ] V) ∞ (P hN) := Morse.contMDiff_tanProj hN

theorem tangentCoordChange_eq {x₀ x : Sub hN} (hx : x ∈ (chartAt (Rn n) x₀).source) :
    tangentCoordChange 𝓘(ℝ, Rn n) x x₀ x = (A x₀ (incl hN x)).comp (D hN x) := by
  rw [← mfderiv_chartAt_eq_tangentCoordChange hx, mfderiv_chartAt hx]

theorem inCoordinates_conn {x₀ x : Sub hN} (hx : x ∈ (chartAt (Rn n) x₀).source)
    (σ : (p : Sub hN) → TangentSpace 𝓘(ℝ, Rn n) p) :
    ContinuousLinearMap.inCoordinates (Rn n) (TangentSpace 𝓘(ℝ, Rn n)) (Rn n)
      (TangentSpace 𝓘(ℝ, Rn n)) x₀ x x₀ x (conn σ x) =
      (A x₀ (incl hN x)).comp ((P hN x).comp
        (inTangentCoordinates 𝓘(ℝ, Rn n) 𝓘(ℝ, V) id (amb σ)
          (fun y => mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, V) (amb σ) y) x₀ x)) := by
  have h1 := inTangentCoordinates_eq (I := 𝓘(ℝ, Rn n)) (I' := 𝓘(ℝ, Rn n)) id id
    (fun y => (conn σ y : Rn n →L[ℝ] Rn n)) (x₀ := x₀) (x := x) hx hx
  have h2 := inTangentCoordinates_eq (I := 𝓘(ℝ, Rn n)) (I' := 𝓘(ℝ, V)) id (amb σ)
    (fun y => mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, V) (amb σ) y) (x₀ := x₀) (x := x) hx (mem_univ _)
  change inTangentCoordinates 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) id id
      (fun y => (conn σ y : Rn n →L[ℝ] Rn n)) x₀ x = _
  rw [h1, h2]
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [id, TangentBundle.coordChange_model_space, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.one_apply]
  change tangentCoordChange 𝓘(ℝ, Rn n) x x₀ x _ = _
  rw [tangentCoordChange_eq hx, ContinuousLinearMap.comp_apply]
  exact congrArg (A x₀ (incl hN x)) (D_L_P x _)

/-- The induced connection is smooth (`C^∞`), in the sense of the blind files' `IsGlobalConn`. -/
theorem conn_contMDiff :
    ContMDiffCovariantDerivativeOn (Rn n) ∞ (conn (hN := hN)).toFun Set.univ := by
  refine ⟨fun {σ} hσ => ?_⟩
  intro x₀ _
  have hσ' : ContMDiff 𝓘(ℝ, Rn n) (𝓘(ℝ, Rn n)).tangent ∞
      (fun p => (⟨p, σ p⟩ : TangentBundle 𝓘(ℝ, Rn n) (Sub hN))) := by
    rw [← contMDiffOn_univ]
    exact hσ.of_le (by simp)
  have hamb : ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, V) ∞ (amb σ) := contMDiff_section_iff.1 hσ'
  have hG := (hamb x₀).mfderiv_const (m := ∞) (by simp)
  apply ContMDiffAt.contMDiffWithinAt
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  have hx₀ : x₀ ∈ (chartAt (Rn n) x₀).source := mem_chart_source _ _
  have hA := (contMDiffOn_A x₀).contMDiffAt ((chartAt (Rn n) x₀).open_source.mem_nhds hx₀)
  refine (hA.clm_comp ((contMDiff_P x₀).clm_comp hG)).congr_of_eventuallyEq ?_
  filter_upwards [(chartAt (Rn n) x₀).open_source.mem_nhds hx₀] with x hx
  exact inCoordinates_conn hx σ

/-! ### Symmetry: the Lie bracket in a chart -/

section Bracket

open VectorField

theorem range_I : range (𝓘(ℝ, Rn n) : Rn n → Rn n) = univ := by simp

theorem mfderiv_extChartAt_self (x₀ : Sub hN) :
    mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) (extChartAt 𝓘(ℝ, Rn n) x₀) x₀ =
      ContinuousLinearMap.id ℝ (Rn n) := by
  change mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) (chartAt (Rn n) x₀) x₀ = _
  rw [mfderiv_chartAt_eq_tangentCoordChange (mem_chart_source _ x₀)]
  refine ContinuousLinearMap.ext fun v => ?_
  exact tangentCoordChange_self (mem_extChartAt_source x₀)

/-- The derivative of the inverse chart. -/
abbrev J (x₀ : Sub hN) (u : Rn n) :=
  mfderivWithin 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) (extChartAt 𝓘(ℝ, Rn n) x₀).symm
    (range 𝓘(ℝ, Rn n)) u

theorem J_self (x₀ : Sub hN) :
    J x₀ (extChartAt 𝓘(ℝ, Rn n) x₀ x₀) = ContinuousLinearMap.id ℝ (Rn n) := by
  have h := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := 𝓘(ℝ, Rn n))
    (mem_extChartAt_source (I := 𝓘(ℝ, Rn n)) x₀)
  rw [mfderiv_extChartAt_self] at h
  exact h

theorem D_comp_J (x₀ : Sub hN) {u : Rn n} (hu : u ∈ (extChartAt 𝓘(ℝ, Rn n) x₀).target) :
    (D hN ((extChartAt 𝓘(ℝ, Rn n) x₀).symm u)).comp (J x₀ u) = B x₀ u := by
  set q := (extChartAt 𝓘(ℝ, Rn n) x₀).symm u
  have hq : q ∈ (chartAt (Rn n) x₀).source := by
    have := (extChartAt 𝓘(ℝ, Rn n) x₀).map_target hu
    rwa [extChartAt_source] at this
  have hcq : chartAt (Rn n) x₀ q = u := (extChartAt 𝓘(ℝ, Rn n) x₀).right_inv hu
  have h1 := D_eq_B hq
  have h2 := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := 𝓘(ℝ, Rn n)) hu
  refine ContinuousLinearMap.ext fun v => ?_
  have e1 : D hN q (J x₀ u v) =
      B x₀ (chartAt (Rn n) x₀ q) (A x₀ (incl hN q) (D hN q (J x₀ u v))) :=
    DFunLike.congr_fun h1 (J x₀ u v)
  have e3 : A x₀ (incl hN q) (D hN q (J x₀ u v)) =
      mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) (chartAt (Rn n) x₀) q (J x₀ u v) :=
    (DFunLike.congr_fun (mfderiv_chartAt hq) (J x₀ u v)).symm
  have e2 : mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) (chartAt (Rn n) x₀) q (J x₀ u v) = v :=
    DFunLike.congr_fun h2 v
  show D hN q (J x₀ u v) = B x₀ u v
  rw [e1, e3, e2, hcq]

/-- The chart expression of a vector field (Mathlib's pull-back by the inverse chart). -/
abbrev Xc (x₀ : Sub hN) (X : (p : Sub hN) → TangentSpace 𝓘(ℝ, Rn n) p) : Rn n → Rn n :=
  mpullbackWithin 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) (extChartAt 𝓘(ℝ, Rn n) x₀).symm X (range 𝓘(ℝ, Rn n))

theorem amb_extChartAt_symm (x₀ : Sub hN) (X : (p : Sub hN) → TangentSpace 𝓘(ℝ, Rn n) p)
    {u : Rn n} (hu : u ∈ (extChartAt 𝓘(ℝ, Rn n) x₀).target) :
    amb X ((extChartAt 𝓘(ℝ, Rn n) x₀).symm u) = B x₀ u (Xc x₀ X u) := by
  have hJ := isInvertible_mfderivWithin_extChartAt_symm (I := 𝓘(ℝ, Rn n)) hu
  have e := DFunLike.congr_fun (D_comp_J x₀ hu) (Xc x₀ X u)
  refine Eq.trans ?_ e
  show D hN _ (X _) = D hN _ (J x₀ u ((J x₀ u).inverse (X _)))
  rw [← (hJ.inverse_apply_eq (x := (J x₀ u).inverse (X _))).1 rfl]

theorem Xc_self (x₀ : Sub hN) (X : (p : Sub hN) → TangentSpace 𝓘(ℝ, Rn n) p) :
    Xc x₀ X (extChartAt 𝓘(ℝ, Rn n) x₀ x₀) = X x₀ := by
  have h : (J x₀ (extChartAt 𝓘(ℝ, Rn n) x₀ x₀)).inverse = ContinuousLinearMap.id ℝ (Rn n) := by
    rw [J_self]
    exact ContinuousLinearMap.inverse_id ..
  show (J x₀ _).inverse (X _) = X x₀
  rw [h]
  exact congrArg (fun a => (X a : Rn n)) (extChartAt_to_inv x₀)

theorem mlieBracket_eq (x₀ : Sub hN) (X Y : (p : Sub hN) → TangentSpace 𝓘(ℝ, Rn n) p) :
    mlieBracket 𝓘(ℝ, Rn n) X Y x₀ =
      lieBracket ℝ (Xc x₀ X) (Xc x₀ Y) (extChartAt 𝓘(ℝ, Rn n) x₀ x₀) := by
  have h : (mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) (extChartAt 𝓘(ℝ, Rn n) x₀) x₀).inverse =
      ContinuousLinearMap.id ℝ (Rn n) := by
    rw [mfderiv_extChartAt_self]
    exact ContinuousLinearMap.inverse_id ..
  have hs : (extChartAt 𝓘(ℝ, Rn n) x₀).symm ⁻¹' univ ∩ range 𝓘(ℝ, Rn n) = univ := by
    simp
  rw [mlieBracket, mlieBracketWithin_apply, h, hs]
  exact congrFun (lieBracketWithin_univ (𝕜 := ℝ) (V := Xc x₀ X) (W := Xc x₀ Y)) _

theorem mfderiv_amb_eq (x₀ : Sub hN) (X : (p : Sub hN) → TangentSpace 𝓘(ℝ, Rn n) p)
    (hX : MDifferentiableAt 𝓘(ℝ, Rn n) 𝓘(ℝ, V) (amb X) x₀) (v : Rn n) :
    mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, V) (amb X) x₀ v =
      fderiv ℝ (amb X ∘ (extChartAt 𝓘(ℝ, Rn n) x₀).symm) (extChartAt 𝓘(ℝ, Rn n) x₀ x₀) v := by
  set u₀ := extChartAt 𝓘(ℝ, Rn n) x₀ x₀
  have hx : (extChartAt 𝓘(ℝ, Rn n) x₀).symm u₀ = x₀ := extChartAt_to_inv x₀
  have hf : HasMFDerivWithinAt 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) (extChartAt 𝓘(ℝ, Rn n) x₀).symm
      (range 𝓘(ℝ, Rn n)) u₀ (J x₀ u₀) :=
    (mdifferentiableWithinAt_extChartAt_symm (mem_extChartAt_target x₀)).hasMFDerivWithinAt
  have hg : HasMFDerivAt 𝓘(ℝ, Rn n) 𝓘(ℝ, V) (amb X) ((extChartAt 𝓘(ℝ, Rn n) x₀).symm u₀)
      (mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, V) (amb X) x₀) := by
    rw [hx]; exact hX.hasMFDerivAt
  have h := HasMFDerivAt.comp_hasMFDerivWithinAt (f := (extChartAt 𝓘(ℝ, Rn n) x₀).symm) u₀ hg hf
  rw [range_I, hasMFDerivWithinAt_univ] at h
  rw [← mfderiv_eq_fderiv, h.mfderiv]
  show _ = mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, V) (amb X) x₀ (J x₀ u₀ v)
  rw [J_self]
  rfl

theorem amb_comp_eventuallyEq (x₀ : Sub hN) (X : (p : Sub hN) → TangentSpace 𝓘(ℝ, Rn n) p) :
    amb X ∘ (extChartAt 𝓘(ℝ, Rn n) x₀).symm =ᶠ[𝓝 (extChartAt 𝓘(ℝ, Rn n) x₀ x₀)]
      fun u => B x₀ u (Xc x₀ X u) := by
  filter_upwards [(isOpen_extChartAt_target x₀).mem_nhds (mem_extChartAt_target x₀)] with u hu
  exact amb_extChartAt_symm x₀ X hu

theorem differentiableAt_Xc (x₀ : Sub hN) (X : (p : Sub hN) → TangentSpace 𝓘(ℝ, Rn n) p)
    (hX : MDifferentiableAt 𝓘(ℝ, Rn n) (𝓘(ℝ, Rn n)).tangent
      (fun p => (⟨p, X p⟩ : TangentBundle 𝓘(ℝ, Rn n) (Sub hN))) x₀) :
    DifferentiableAt ℝ (Xc x₀ X) (extChartAt 𝓘(ℝ, Rn n) x₀ x₀) := by
  have := MDifferentiableWithinAt.differentiableWithinAt_mpullbackWithin_vectorField (s := univ)
    hX.mdifferentiableWithinAt
  have hs : (extChartAt 𝓘(ℝ, Rn n) x₀).symm ⁻¹' univ ∩ range 𝓘(ℝ, Rn n) = univ := by
    simp
  exact this.differentiableAt (by rw [hs]; exact Filter.univ_mem)

theorem mem_target_self (x₀ : Sub hN) :
    extChartAt 𝓘(ℝ, Rn n) x₀ x₀ ∈ (Morse.sliceAt hN x₀).toChart.target :=
  Morse.toChart_apply_mem_target _ (Morse.mem_sliceAt_source hN x₀)

theorem differentiableAt_B (x₀ : Sub hN) :
    DifferentiableAt ℝ (B x₀) (extChartAt 𝓘(ℝ, Rn n) x₀ x₀) :=
  ((Morse.contDiffAt_sliceParam _ (mem_target_self x₀)).fderiv_right (m := 1)
    (WithTop.coe_le_coe.2 le_top)).differentiableAt (by simp)

theorem fderiv_B_symm (x₀ : Sub hN) (v w : Rn n) :
    fderiv ℝ (B x₀) (extChartAt 𝓘(ℝ, Rn n) x₀ x₀) v w =
      fderiv ℝ (B x₀) (extChartAt 𝓘(ℝ, Rn n) x₀ x₀) w v :=
  ((Morse.contDiffAt_sliceParam _ (mem_target_self x₀)).isSymmSndFDerivAt
    (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)) v w

theorem D_eq_B_self (x₀ : Sub hN) (z : Rn n) :
    D hN x₀ z = B x₀ (extChartAt 𝓘(ℝ, Rn n) x₀ x₀) z := by
  set u₀ := extChartAt 𝓘(ℝ, Rn n) x₀ x₀
  have hx : (extChartAt 𝓘(ℝ, Rn n) x₀).symm u₀ = x₀ := extChartAt_to_inv x₀
  calc D hN x₀ z = D hN ((extChartAt 𝓘(ℝ, Rn n) x₀).symm u₀) z := by rw [hx]
    _ = D hN ((extChartAt 𝓘(ℝ, Rn n) x₀).symm u₀) (J x₀ u₀ z) := by rw [J_self]; rfl
    _ = B x₀ u₀ z := DFunLike.congr_fun (D_comp_J x₀ (mem_extChartAt_target x₀)) z

theorem mfderiv_amb_apply (x₀ : Sub hN) (X Y : (p : Sub hN) → TangentSpace 𝓘(ℝ, Rn n) p)
    (hY : MDifferentiableAt 𝓘(ℝ, Rn n) (𝓘(ℝ, Rn n)).tangent
      (fun p => (⟨p, Y p⟩ : TangentBundle 𝓘(ℝ, Rn n) (Sub hN))) x₀) :
    dV (amb Y) x₀ (X x₀) =
      B x₀ (extChartAt 𝓘(ℝ, Rn n) x₀ x₀) (fderiv ℝ (Xc x₀ Y) (extChartAt 𝓘(ℝ, Rn n) x₀ x₀)
        (Xc x₀ X (extChartAt 𝓘(ℝ, Rn n) x₀ x₀))) +
      fderiv ℝ (B x₀) (extChartAt 𝓘(ℝ, Rn n) x₀ x₀) (Xc x₀ X (extChartAt 𝓘(ℝ, Rn n) x₀ x₀))
        (Xc x₀ Y (extChartAt 𝓘(ℝ, Rn n) x₀ x₀)) := by
  refine (mfderiv_amb_eq x₀ Y (mdifferentiableAt_section_iff.1 hY) (X x₀)).trans ?_
  have e1 := (amb_comp_eventuallyEq x₀ Y).fderiv_eq (𝕜 := ℝ)
  have e2 := fderiv_clm_apply (𝕜 := ℝ) (differentiableAt_B x₀) (differentiableAt_Xc x₀ Y hY)
  have e3 : (X x₀ : Rn n) = Xc x₀ X (extChartAt 𝓘(ℝ, Rn n) x₀ x₀) := (Xc_self x₀ X).symm
  rw [e1, e2, e3]
  rfl

/-- **The bracket in `V`**: `D_p [X, Y]_p = dŶ_p(X_p) − dX̂_p(Y_p)`. -/
theorem D_mlieBracket (x₀ : Sub hN) (X Y : (p : Sub hN) → TangentSpace 𝓘(ℝ, Rn n) p)
    (hX : MDifferentiableAt 𝓘(ℝ, Rn n) (𝓘(ℝ, Rn n)).tangent
      (fun p => (⟨p, X p⟩ : TangentBundle 𝓘(ℝ, Rn n) (Sub hN))) x₀)
    (hY : MDifferentiableAt 𝓘(ℝ, Rn n) (𝓘(ℝ, Rn n)).tangent
      (fun p => (⟨p, Y p⟩ : TangentBundle 𝓘(ℝ, Rn n) (Sub hN))) x₀) :
    D hN x₀ (mlieBracket 𝓘(ℝ, Rn n) X Y x₀) = dV (amb Y) x₀ (X x₀) - dV (amb X) x₀ (Y x₀) := by
  rw [mfderiv_amb_apply x₀ X Y hY, mfderiv_amb_apply x₀ Y X hX, mlieBracket_eq, D_eq_B_self,
    fderiv_B_symm x₀ (Xc x₀ X _)]
  simp only [lieBracket, map_sub]
  abel

end Bracket

/-! ### Curves and fields along curves -/

section Curves

/-- The ambient field `t ↦ D_{c t} (U t) ∈ V` of a field `U` along a curve `c` in `N`. -/
def ambA (c : ℝ → Sub hN) (U : (t : ℝ) → TangentSpace 𝓘(ℝ, Rn n) (c t)) (t : ℝ) : V :=
  D hN (c t) (U t)

theorem contMDiffOn_along_iff {c : ℝ → Sub hN} {s : Set ℝ}
    {U : (t : ℝ) → TangentSpace 𝓘(ℝ, Rn n) (c t)} :
    ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, Rn n)).tangent ∞
      (fun t => (⟨c t, U t⟩ : TangentBundle 𝓘(ℝ, Rn n) (Sub hN))) s ↔
      ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) ∞ c s ∧ ContDiffOn ℝ ∞ (ambA c U) s := by
  rw [← contMDiffOn_iff_contDiffOn]
  constructor
  · intro h
    exact ⟨fun t ht => (contMDiffWithinAt_tangent_iff.1 (h t ht)).1,
      fun t ht => (contMDiffWithinAt_tangent_iff.1 (h t ht)).2⟩
  · rintro ⟨h1, h2⟩ t ht
    exact contMDiffWithinAt_tangent_iff.2 ⟨h1 t ht, h2 t ht⟩

/-- The chain rule along a curve, read in `V`. -/
theorem hasDerivWithinAt_comp_curve {c : ℝ → Sub hN} {s : Set ℝ} {t : ℝ} {F : Sub hN → V}
    (hF : MDifferentiableAt 𝓘(ℝ, Rn n) 𝓘(ℝ, V) F (c t))
    (hc : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) c s t) :
    HasDerivWithinAt (F ∘ c)
      (dV F (c t) (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) c s t 1)) s t := by
  have h := HasMFDerivAt.comp_hasMFDerivWithinAt (f := c) t hF.hasMFDerivAt hc.hasMFDerivWithinAt
  have h' : HasFDerivWithinAt (F ∘ c) ((dV F (c t)).comp
      (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) c s t : ℝ →L[ℝ] Rn n)) s t :=
    hasMFDerivWithinAt_iff_hasFDerivWithinAt.1 h
  exact h'.hasDerivWithinAt

/-- The velocity of a curve in `N`, read in `V`, is the derivative of the curve in `V`. -/
theorem hasDerivWithinAt_incl_comp {c : ℝ → Sub hN} {s : Set ℝ} {t : ℝ}
    (hc : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) c s t) :
    HasDerivWithinAt (incl hN ∘ c) (D hN (c t) (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) c s t 1)) s t :=
  hasDerivWithinAt_comp_curve ((contMDiff_incl (c t)).mdifferentiableAt (by simp)) hc

/-- The induced covariant derivative along a curve: `DU/dt = P(dÛ/dt)` (derivative within `s`). -/
def covA (c : ℝ → Sub hN) (s : Set ℝ) (U : (t : ℝ) → TangentSpace 𝓘(ℝ, Rn n) (c t)) (t : ℝ) :
    TangentSpace 𝓘(ℝ, Rn n) (c t) :=
  L hN (c t) (P hN (c t) (derivWithin (ambA c U) s t))

theorem D_covA (c : ℝ → Sub hN) (s : Set ℝ) (U : (t : ℝ) → TangentSpace 𝓘(ℝ, Rn n) (c t))
    (t : ℝ) : D hN (c t) (covA c s U t) = P hN (c t) (derivWithin (ambA c U) s t) :=
  D_L_P _ _

/-- A curve in `N` is smooth (as a map into the manifold `N`) iff it is smooth in `V`. -/
theorem contMDiffWithinAt_curve_iff {c : ℝ → Sub hN} {s : Set ℝ} {t : ℝ} :
    ContMDiffWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) ∞ c s t ↔ ContDiffWithinAt ℝ ∞ (incl hN ∘ c) s t := by
  constructor
  · intro h
    exact contMDiffWithinAt_iff_contDiffWithinAt.1
      ((contMDiff_incl (c t)).comp_contMDiffWithinAt t h)
  · intro h
    have hcont : ContinuousWithinAt c s t :=
      (Topology.IsInducing.subtypeVal.continuousWithinAt_iff (f := c)).2 h.continuousWithinAt
    rw [contMDiffWithinAt_iff_target]
    refine ⟨hcont, ?_⟩
    set σ := Morse.sliceAt hN (c t)
    have hφ : ContDiffAt ℝ ∞ (fun y => (σ.φ y).1) (incl hN (c t)) :=
      contDiff_fst.contDiffAt.comp _ ((Milnor.Problems.sliceChart_contDiffOn σ).contDiffAt
        (σ.φ.open_source.mem_nhds (Morse.mem_sliceAt_source hN (c t))))
    have e : (extChartAt 𝓘(ℝ, Rn n) (c t) ∘ c) = (fun y => (σ.φ y).1) ∘ (incl hN ∘ c) := rfl
    rw [e]
    exact contMDiffWithinAt_iff_contDiffWithinAt.2 (hφ.comp_contDiffWithinAt t h)

theorem contMDiffOn_curve_iff {c : ℝ → Sub hN} {s : Set ℝ} :
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) ∞ c s ↔ ContDiffOn ℝ ∞ (incl hN ∘ c) s :=
  forall₂_congr fun _ _ => contMDiffWithinAt_curve_iff

/-- A curve in `N` is differentiable (as a map into the manifold `N`) iff it is differentiable in
`V`. -/
theorem mdifferentiableWithinAt_curve_iff {c : ℝ → Sub hN} {s : Set ℝ} {t : ℝ} :
    MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) c s t ↔
      DifferentiableWithinAt ℝ (incl hN ∘ c) s t := by
  constructor
  · intro h
    exact mdifferentiableWithinAt_iff_differentiableWithinAt.1
      (((contMDiff_incl (c t)).mdifferentiableAt (by simp)).comp_mdifferentiableWithinAt
        (x := t) h)
  · intro h
    have hcont : ContinuousWithinAt c s t :=
      (Topology.IsInducing.subtypeVal.continuousWithinAt_iff (f := c)).2 h.continuousWithinAt
    rw [mdifferentiableWithinAt_iff_target]
    refine ⟨hcont, ?_⟩
    set σ := Morse.sliceAt hN (c t)
    have hφ : DifferentiableAt ℝ (fun y => (σ.φ y).1) (incl hN (c t)) :=
      (Milnor.Problems.sliceChart_differentiableAt σ (Morse.mem_sliceAt_source hN (c t))).fst
    have e : (extChartAt 𝓘(ℝ, Rn n) (c t) ∘ c) = (fun y => (σ.φ y).1) ∘ (incl hN ∘ c) := rfl
    rw [e]
    exact mdifferentiableWithinAt_iff_differentiableWithinAt.2 (hφ.comp_differentiableWithinAt t h)

theorem mdifferentiableAt_curve_iff {c : ℝ → Sub hN} {t : ℝ} :
    MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) c t ↔ DifferentiableAt ℝ (incl hN ∘ c) t := by
  rw [← mdifferentiableWithinAt_univ, mdifferentiableWithinAt_curve_iff,
    differentiableWithinAt_univ]

/-- The (two-sided) velocity of a curve in `N`, read in `V`, is its derivative in `V`
(both sides are `0` where the curve is not differentiable). -/
theorem D_mfderiv_curve (c : ℝ → Sub hN) (t : ℝ) :
    D hN (c t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) c t 1) = deriv (incl hN ∘ c) t := by
  by_cases h : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) c t
  · have := hasDerivWithinAt_incl_comp (s := univ) h.mdifferentiableWithinAt
    rw [hasDerivWithinAt_univ, mfderivWithin_univ] at this
    exact this.deriv.symm
  · rw [mfderiv_zero_of_not_mdifferentiableAt h,
      deriv_zero_of_not_differentiableAt (mt mdifferentiableAt_curve_iff.2 h)]
    exact map_zero _

end Curves

/-! ### The blind vocabulary: the induced connection is symmetric and smooth -/

section Blind

open RoundTrip.BridgePrelude

theorem conn_isGlobalConn : IsGlobalConn (conn (hN := hN)) := conn_contMDiff

theorem conn_isSymm : IsSymm (conn (hN := hN)) := by
  intro X Y hX hY p
  have hXp := (hX p).mdifferentiableAt (by simp)
  have hYp := (hY p).mdifferentiableAt (by simp)
  apply D_injective p
  have h1 : D hN p (conn Y p (X p)) = P hN p (dV (amb Y) p (X p)) := D_covFun Y p (X p)
  have h2 : D hN p (conn X p (Y p)) = P hN p (dV (amb X) p (Y p)) := D_covFun X p (Y p)
  calc D hN p (conn Y p (X p) - conn X p (Y p))
      = D hN p (conn Y p (X p)) - D hN p (conn X p (Y p)) := map_sub (D hN p) _ _
    _ = P hN p (dV (amb Y) p (X p)) - P hN p (dV (amb X) p (Y p)) := by rw [h1, h2]
    _ = P hN p (dV (amb Y) p (X p) - dV (amb X) p (Y p)) := (map_sub _ _ _).symm
    _ = P hN p (D hN p (VectorField.mlieBracket 𝓘(ℝ, Rn n) X Y p)) := by rw [D_mlieBracket p X Y hXp hYp]
    _ = D hN p (VectorField.mlieBracket 𝓘(ℝ, Rn n) X Y p) := P_D p _

variable {c : ℝ → Sub hN} {s : Set ℝ}

theorem isSmoothAlong_iff {U : FA n c} :
    IsSmoothAlong c s U ↔ IsSmoothCurve (n := n) c s ∧ ContDiffOn ℝ ∞ (ambA c U) s :=
  contMDiffOn_along_iff

theorem IsSmoothAlong.differentiableOn {U : FA n c} (hU : IsSmoothAlong c s U) :
    DifferentiableOn ℝ (ambA c U) s :=
  (isSmoothAlong_iff.1 hU).2.differentiableOn (by simp)

/-- The velocity, read in `V`, is the derivative (within `s`) of the curve in `V`. -/
theorem D_vel {t : ℝ} (hc : IsSmoothCurve (n := n) c s) (hs : UniqueDiffOn ℝ s) (ht : t ∈ s) :
    D hN (c t) (vel (n := n) c s t) = derivWithin (incl hN ∘ c) s t :=
  ((hasDerivWithinAt_incl_comp ((hc t ht).mdifferentiableWithinAt (by simp))).derivWithin
    (hs t ht)).symm

/-- `P(dÛ/dt)` satisfies Milnor's axioms (a), (b), (c) for the induced connection. -/
theorem isCovDerivAlong_covA (hs : IsIntv s) (hc : IsSmoothCurve (n := n) c s) :
    IsCovDerivAlong (conn (hN := hN)) c s (covA c s) := by
  refine ⟨?_, ?_, ?_⟩
  · intro U W hU hW t ht
    have e : ambA c (fun t => U t + W t) = fun t => ambA c U t + ambA c W t :=
      funext fun t => map_add (D hN (c t)) _ _
    simp only [covA]
    rw [e, derivWithin_fun_add (IsSmoothAlong.differentiableOn hU t ht)
      (IsSmoothAlong.differentiableOn hW t ht), map_add, map_add]
    rfl
  · intro f hf U hU t ht
    have e : ambA c (fun t => f t • U t) = fun t => f t • ambA c U t :=
      funext fun t => map_smul (D hN (c t)) _ _
    have hf' : DifferentiableWithinAt ℝ f s t := (hf.differentiableOn (by simp)) t ht
    simp only [covA]
    rw [e, derivWithin_fun_smul hf' (IsSmoothAlong.differentiableOn hU t ht), map_add, map_add, map_smul,
      map_smul, map_smul, map_smul]
    have : L hN (c t) (P hN (c t) (ambA c U t)) = U t := L_P_D _ _
    rw [this, add_comm]
    rfl
  · intro Y hY t ht
    have hd := hasDerivWithinAt_comp_curve (F := amb Y)
      (((contMDiff_section_iff.1 hY) (c t)).mdifferentiableAt (by simp))
      ((hc t ht).mdifferentiableWithinAt (by simp))
    show L hN (c t) (P hN (c t) (derivWithin (amb Y ∘ c) s t)) = _
    rw [hd.derivWithin (hs.2 t ht)]
    rfl

/-! #### Uniqueness of `D/dt`, via a global frame -/

theorem D_tsum (x : Sub hN) {ι : Type*} (S : Finset ι) (v : ι → TangentSpace 𝓘(ℝ, Rn n) x) :
    D hN x (∑ i ∈ S, v i) = ∑ i ∈ S, D hN x (v i) := map_sum (D hN x) v S

theorem D_tsmul (x : Sub hN) (a : ℝ) (v : TangentSpace 𝓘(ℝ, Rn n) x) :
    D hN x (a • v) = a • D hN x v := map_smul (D hN x) a v

theorem D_tadd (x : Sub hN) (v w : TangentSpace 𝓘(ℝ, Rn n) x) :
    D hN x (v + w) = D hN x v + D hN x w := map_add (D hN x) v w

theorem D_tsub_aux (x : Sub hN) (v w : TangentSpace 𝓘(ℝ, Rn n) x) :
    D hN x (v - w) = D hN x v - D hN x w := map_sub (D hN x) v w

theorem D_tzero (x : Sub hN) : D hN x (0 : TangentSpace 𝓘(ℝ, Rn n) x) = 0 := map_zero (D hN x)

/-- An orthonormal basis of `V`. -/
abbrev bV : OrthonormalBasis (Fin (finrank ℝ V)) ℝ V := stdOrthonormalBasis ℝ V

/-- The global fields `p ↦ P_p eᵢ` (tangential parts of the constant fields of a basis of `V`);
they span `T_pN` at every point. -/
def frame (i : Fin (finrank ℝ V)) : VF n (Sub hN) := fun p => L hN p (P hN p (bV i))

theorem amb_frame (i : Fin (finrank ℝ V)) (p : Sub hN) : amb (frame i) p = P hN p (bV i) :=
  D_L_P _ _

theorem isSmoothVF_frame (i : Fin (finrank ℝ V)) : IsSmoothVF (frame (hN := hN) i) := by
  rw [IsSmoothVF, contMDiff_section_iff]
  have : amb (frame (hN := hN) i) = fun p => P hN p (bV i) := funext fun p => amb_frame i p
  rw [this]
  exact contMDiff_P.clm_apply contMDiff_const

/-- Coefficients of a field along `c` in the frame. -/
def coef (U : FA n c) (i : Fin (finrank ℝ V)) (t : ℝ) : ℝ := ⟪bV i, ambA c U t⟫

theorem expand (U : FA n c) (t : ℝ) : U t = ∑ i, coef U i t • frame i (c t) := by
  apply D_injective (c t)
  have h1 : D hN (c t) (∑ i, coef U i t • frame (hN := hN) i (c t)) =
      ∑ i, coef U i t • P hN (c t) (bV i) := by
    rw [D_tsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [D_tsmul]
    exact congrArg (coef U i t • ·) (amb_frame i (c t))
  have h2 : ∑ i, coef U i t • P hN (c t) (bV i) = P hN (c t) (∑ i, coef U i t • bV i) := by
    rw [map_sum]; simp only [map_smul]
  have h3 : ∑ i, coef U i t • bV i = ambA c U t := OrthonormalBasis.sum_repr' _ _
  calc D hN (c t) (U t) = P hN (c t) (D hN (c t) (U t)) := (P_D (c t) (U t)).symm
    _ = P hN (c t) (ambA c U t) := rfl
    _ = P hN (c t) (∑ i, coef U i t • bV i) := by rw [h3]
    _ = ∑ i, coef U i t • P hN (c t) (bV i) := h2.symm
    _ = _ := h1.symm

theorem contDiffOn_coef {U : FA n c} (hU : IsSmoothAlong c s U) (i : Fin (finrank ℝ V)) :
    ContDiffOn ℝ ∞ (coef U i) s :=
  contDiffOn_const.inner ℝ (isSmoothAlong_iff.1 hU).2

theorem isSmoothAlong_frame (hc : IsSmoothCurve (n := n) c s) (i : Fin (finrank ℝ V)) :
    IsSmoothAlong c s (fun t => frame (hN := hN) i (c t)) :=
  (isSmoothVF_frame i).comp_contMDiffOn hc

theorem isSmoothAlong_smul (hc : IsSmoothCurve (n := n) c s) {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f s)
    {U : FA n c} (hU : IsSmoothAlong c s U) : IsSmoothAlong c s (fun t => f t • U t) := by
  rw [isSmoothAlong_iff] at hU ⊢
  refine ⟨hc, ?_⟩
  have : ambA c (fun t => f t • U t) = fun t => f t • ambA c U t :=
    funext fun t => map_smul (D hN (c t)) _ _
  rw [this]
  exact hf.smul hU.2

theorem isSmoothAlong_sum (hc : IsSmoothCurve (n := n) c s) {ι : Type*} (S : Finset ι)
    {G : ι → FA n c} (hG : ∀ i, IsSmoothAlong c s (G i)) :
    IsSmoothAlong c s (fun t => ∑ i ∈ S, G i t) := by
  rw [isSmoothAlong_iff]
  refine ⟨hc, ?_⟩
  have : ambA c (fun t => ∑ i ∈ S, G i t) = fun t => ∑ i ∈ S, ambA c (G i) t :=
    funext fun t => map_sum (D hN (c t)) _ _
  rw [this]
  exact ContDiffOn.sum fun i _ => (isSmoothAlong_iff.1 (hG i)).2

theorem IsCovDerivAlong.zero {D' : FA n c → FA n c} (hD : IsCovDerivAlong (conn (hN := hN)) c s D')
    (hc : IsSmoothCurve (n := n) c s) {t : ℝ} (ht : t ∈ s) : D' (fun _ => 0) t = 0 := by
  have h0 : IsSmoothAlong c s (fun t => (0 : TangentSpace 𝓘(ℝ, Rn n) (c t))) := by
    refine isSmoothAlong_iff.2 ⟨hc, ?_⟩
    have : ambA c (fun t => (0 : TangentSpace 𝓘(ℝ, Rn n) (c t))) = fun _ => 0 :=
      funext fun t => D_tzero (c t)
    rw [this]; exact contDiffOn_const
  have := hD.2.1 (fun _ => 0) contDiffOn_const _ h0 t ht
  simp only [zero_smul, add_zero, smul_zero] at this
  exact this

theorem IsCovDerivAlong.sum {D' : FA n c → FA n c} (hD : IsCovDerivAlong (conn (hN := hN)) c s D')
    (hc : IsSmoothCurve (n := n) c s) {ι : Type*} [DecidableEq ι] (S : Finset ι)
    {G : ι → FA n c} (hG : ∀ i, IsSmoothAlong c s (G i)) {t : ℝ} (ht : t ∈ s) :
    D' (fun t => ∑ i ∈ S, G i t) t = ∑ i ∈ S, D' (G i) t := by
  induction S using Finset.induction_on with
  | empty => simpa using IsCovDerivAlong.zero hD hc ht
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    rw [hD.1 (G a) (fun t => ∑ i ∈ S, G i t) (hG a) (isSmoothAlong_sum hc S hG) t ht, ih]

/-- **Expansion of any `D/dt` in the frame**: every operation satisfying Milnor's axioms is given by
the same formula on smooth fields. -/
theorem IsCovDerivAlong.eq_expand {D' : FA n c → FA n c}
    (hD : IsCovDerivAlong (conn (hN := hN)) c s D') (hc : IsSmoothCurve (n := n) c s)
    {U : FA n c} (hU : IsSmoothAlong c s U) {t : ℝ} (ht : t ∈ s) :
    D' U t = ∑ i, (derivWithin (coef U i) s t • frame i (c t) +
      coef U i t • conn (frame i) (c t) (vel (n := n) c s t)) := by
  have hUe : U = fun t => ∑ i, coef U i t • frame (hN := hN) i (c t) := funext (expand U)
  have hG : ∀ i, IsSmoothAlong c s (fun t => coef U i t • frame (hN := hN) i (c t)) := fun i =>
    isSmoothAlong_smul hc (contDiffOn_coef hU i) (isSmoothAlong_frame hc i)
  calc D' U t = D' (fun t => ∑ i, coef U i t • frame (hN := hN) i (c t)) t :=
        congrFun (congrArg D' hUe) t
    _ = ∑ i, D' (fun t => coef U i t • frame (hN := hN) i (c t)) t := IsCovDerivAlong.sum hD hc _ hG ht
    _ = _ := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hD.2.1 _ (contDiffOn_coef hU i) _ (isSmoothAlong_frame hc i) t ht,
        hD.2.2 _ (isSmoothVF_frame i) t ht]

/-- **Uniqueness of `D/dt`** (Milnor's Lemma 8.1, induced connection): two operations satisfying
the axioms agree on smooth fields. -/
theorem IsCovDerivAlong.eq {D₁ D₂ : FA n c → FA n c}
    (h₁ : IsCovDerivAlong (conn (hN := hN)) c s D₁) (h₂ : IsCovDerivAlong (conn (hN := hN)) c s D₂)
    (hc : IsSmoothCurve (n := n) c s) {U : FA n c} (hU : IsSmoothAlong c s U) {t : ℝ}
    (ht : t ∈ s) : D₁ U t = D₂ U t := by
  rw [IsCovDerivAlong.eq_expand h₁ hc hU ht, IsCovDerivAlong.eq_expand h₂ hc hU ht]

/-- **Dictionary: `HasCovDeriv` for the induced connection.** On an interval, for a smooth curve,
`DU/dt = W` iff `U` is smooth along `c` and `W = P(dÛ/dt)` (derivative of the ambient field
within `s`, projected to `T_{c t}N`). -/
theorem hasCovDeriv_iff (hs : IsIntv s) (hc : IsSmoothCurve (n := n) c s) {U W : FA n c} :
    HasCovDeriv (conn (hN := hN)) c s U W ↔
      IsSmoothAlong c s U ∧ ∀ t ∈ s, W t = covA c s U t := by
  constructor
  · rintro ⟨hU, D', hD', hDU⟩
    exact ⟨hU, fun t ht => (hDU t ht).symm.trans (IsCovDerivAlong.eq hD' (isCovDerivAlong_covA hs hc) hc hU ht)⟩
  · rintro ⟨hU, h⟩
    exact ⟨hU, covA c s, isCovDerivAlong_covA hs hc, fun t ht => (h t ht).symm⟩

/-- **Dictionary, ambient form**: `DU/dt = W` iff `U` is smooth along `c` and
`D_{c t}(W t) = P_{c t}(dÛ/dt)`. -/
theorem hasCovDeriv_iff' (hs : IsIntv s) (hc : IsSmoothCurve (n := n) c s) {U W : FA n c} :
    HasCovDeriv (conn (hN := hN)) c s U W ↔
      IsSmoothAlong c s U ∧ ∀ t ∈ s, ambA c W t = P hN (c t) (derivWithin (ambA c U) s t) := by
  rw [hasCovDeriv_iff hs hc]
  refine and_congr_right fun _ => forall₂_congr fun t _ => ?_
  rw [← D_covA]
  exact (D_injective (c t)).eq_iff.symm

theorem IsParallel.tangential {U : FA n c} (hs : IsIntv s) (hc : IsSmoothCurve (n := n) c s)
    (hU : IsParallel (conn (hN := hN)) c s U) {t : ℝ} (ht : t ∈ s) :
    P hN (c t) (derivWithin (ambA c U) s t) = 0 := by
  have := ((hasCovDeriv_iff' hs hc).1 hU).2 t ht
  rw [← this]
  exact D_tzero (c t)

open Bundle in
/-- **The induced connection is compatible with the induced metric** (parallel transport preserves
inner products, in the blind files' sense). -/
theorem conn_isCompat : IsCompat (conn (hN := hN)) := by
  intro s hs c hc U U' hU hU' t ht t' ht'
  rw [inner_eq, inner_eq]
  change ⟪ambA c U t, ambA c U' t⟫ = ⟪ambA c U t', ambA c U' t'⟫
  have hd := IsSmoothAlong.differentiableOn hU.1
  have hd' := IsSmoothAlong.differentiableOn hU'.1
  refine (hs.1.convex.is_const_of_fderivWithin_eq_zero (hd.inner ℝ hd') (fun x hx => ?_) ht ht')
  have h1 := (hd x hx).hasDerivWithinAt.inner ℝ (hd' x hx).hasDerivWithinAt
  have e1 : ⟪derivWithin (ambA c U) s x, ambA c U' x⟫ = 0 := by
    have : ambA c U' x = P hN (c x) (ambA c U' x) := (P_D (c x) (U' x)).symm
    rw [this, ← inner_P_left]
    change ⟪P hN (c x) (derivWithin (ambA c U) s x), _⟫ = 0
    rw [IsParallel.tangential hs hc hU hx, inner_zero_left]
  have e2 : ⟪ambA c U x, derivWithin (ambA c U') s x⟫ = 0 := by
    have : ambA c U x = P hN (c x) (ambA c U x) := (P_D (c x) (U x)).symm
    rw [this, inner_P_left]
    change ⟪_, P hN (c x) (derivWithin (ambA c U') s x)⟫ = 0
    rw [IsParallel.tangential hs hc hU' hx, inner_zero_right]
  rw [e1, e2, add_zero] at h1
  rw [h1.hasFDerivWithinAt.fderivWithin (hs.2 x hx)]
  ext; simp

/-- **The induced connection is the Levi-Civita connection** in the blind files' sense. -/
theorem conn_isLC : IsLC (conn (hN := hN)) := ⟨conn_isGlobalConn, conn_isSymm, conn_isCompat⟩

/-! #### Geodesics -/

theorem isSmoothCurve_iff : IsSmoothCurve (n := n) c s ↔ ContDiffOn ℝ ∞ (incl hN ∘ c) s :=
  contMDiffOn_curve_iff

theorem ambA_vel_eqOn (hs : UniqueDiffOn ℝ s) (hc : IsSmoothCurve (n := n) c s) :
    EqOn (ambA c (vel (n := n) c s)) (derivWithin (incl hN ∘ c) s) s :=
  fun _ ht => D_vel hc hs ht

/-- **Dictionary: geodesics on an interval.** A curve `c` in `N` is a blind geodesic of the
induced connection on `s` iff `s` is an interval, `c` is smooth in `V` on `s`, and its
acceleration (second derivative within `s`) is normal to `N`. -/
theorem isGeodesic_iff :
    IsGeodesic (conn (hN := hN)) c s ↔ IsIntv s ∧ ContDiffOn ℝ ∞ (incl hN ∘ c) s ∧
      ∀ t ∈ s, P hN (c t) (derivWithin (derivWithin (incl hN ∘ c) s) s t) = 0 := by
  constructor
  · rintro ⟨hs, hc, -, hv⟩
    refine ⟨hs, isSmoothCurve_iff.1 hc, fun t ht => ?_⟩
    have h := ((hasCovDeriv_iff' hs hc).1 hv).2 t ht
    rw [derivWithin_congr (ambA_vel_eqOn hs.2 hc) (ambA_vel_eqOn hs.2 hc ht)] at h
    rw [← h]
    exact D_tzero (c t)
  · rintro ⟨hs, hc', h⟩
    have hc : IsSmoothCurve (n := n) c s := isSmoothCurve_iff.2 hc'
    have hv : IsSmoothAlong c s (vel (n := n) c s) := by
      refine isSmoothAlong_iff.2 ⟨hc, ?_⟩
      exact (hc'.derivWithin hs.2 (by simp)).congr (ambA_vel_eqOn hs.2 hc)
    refine ⟨hs, hc, hv, (hasCovDeriv_iff' hs hc).2 ⟨hv, fun t ht => ?_⟩⟩
    rw [derivWithin_congr (ambA_vel_eqOn hs.2 hc) (ambA_vel_eqOn hs.2 hc ht), h t ht]
    exact D_tzero (c t)

/-- **Dictionary: geodesics on an open interval** — the blind `IsGeodesic` of the induced
connection is the project's `Morse.IsGeodesicOn`. -/
theorem isGeodesic_iff_isGeodesicOn (hso : IsOpen s) (hsc : s.OrdConnected) :
    IsGeodesic (conn (hN := hN)) c s ↔ Morse.IsGeodesicOn hN (incl hN ∘ c) s := by
  have hs : IsIntv s := ⟨hsc, hso.uniqueDiffOn⟩
  have hdd : ∀ t ∈ s, derivWithin (derivWithin (incl hN ∘ c) s) s t =
      deriv (deriv (incl hN ∘ c)) t := by
    intro t ht
    rw [derivWithin_of_isOpen hso ht]
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [hso.mem_nhds ht] with u hu
    exact derivWithin_of_isOpen hso hu
  rw [isGeodesic_iff]
  constructor
  · rintro ⟨-, hc, h⟩
    refine ⟨hso, fun t _ => (c t).2, hc, fun t ht => ?_⟩
    rw [← Morse.tanProj_eq_zero_iff, ← hdd t ht]
    exact h t ht
  · intro h
    refine ⟨hs, h.contDiffOn, fun t ht => ?_⟩
    rw [hdd t ht]
    exact (Morse.tanProj_eq_zero_iff hN).2 (h.normal t ht)

/-! #### Curvature -/

theorem D_conn' (Y : VF n (Sub hN)) (q : Sub hN) (v : TangentSpace 𝓘(ℝ, Rn n) q) :
    D hN q (conn Y q v) = P hN q (dV (amb Y) q v) := D_L_P _ _

theorem dN_D (F : Sub hN → V) (q : Sub hN) (v : TangentSpace 𝓘(ℝ, Rn n) q) :
    Morse.dN hN F q (D hN q v) = dV F q v := by
  show dV F q (L hN q (D hN q v)) = dV F q v
  exact congrArg (dV F q) (L_D q v)

theorem D_conn_apply (Y : VF n (Sub hN)) (q : Sub hN) (v : TangentSpace 𝓘(ℝ, Rn n) q) :
    D hN q (conn Y q v) = Morse.covAt hN q (D hN q v) (amb Y) := by
  refine (D_conn' Y q v).trans ?_
  show P hN q (dV (amb Y) q v) = P hN q (Morse.dN hN (amb Y) q (D hN q v))
  rw [dN_D]

/-- The induced connection, read in `V`, is the project's `Morse.leviCivita`. -/
theorem D_conn (X Y : VF n (Sub hN)) (q : Sub hN) :
    D hN q (conn Y q (X q)) = Morse.leviCivita hN (amb X) (amb Y) q :=
  D_conn_apply Y q (X q)

theorem amb_conn (X Y : VF n (Sub hN)) :
    amb (fun q => conn Y q (X q)) = Morse.leviCivita hN (amb X) (amb Y) :=
  funext fun q => D_conn X Y q

theorem isTangentField_amb (X : VF n (Sub hN)) : Morse.IsTangentField hN (amb X) :=
  fun q => amb_mem X q

theorem contMDiff_amb {X : VF n (Sub hN)} (hX : IsSmoothVF X) :
    ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, V) ∞ (amb X) :=
  contMDiff_section_iff.1 hX

/-- The extension `q ↦ L_q(P_q u)` of an ambient vector `u` to a smooth vector field. -/
def ext (u : V) : VF n (Sub hN) := fun q => L hN q (P hN q u)

theorem amb_ext (u : V) : amb (ext (hN := hN) u) = fun q => P hN q u := funext fun _ => D_L_P _ _

theorem isSmoothVF_ext (u : V) : IsSmoothVF (ext (hN := hN) u) := by
  rw [IsSmoothVF, contMDiff_section_iff, amb_ext]
  exact contMDiff_P.clm_apply contMDiff_const

theorem ext_apply_D (p : Sub hN) (x : TangentSpace 𝓘(ℝ, Rn n) p) :
    ext (hN := hN) (D hN p x) p = x := L_P_D p x

/-- The blind curvature expression, read in `V`, is the project's curvature. -/
theorem D_curvExpr [FiniteDimensional ℝ W] {X Y Z : VF n (Sub hN)} (hX : IsSmoothVF X)
    (hY : IsSmoothVF Y) (hZ : IsSmoothVF Z) (p : Sub hN) :
    D hN p (conn (fun q => conn Z q (X q)) p (Y p) - conn (fun q => conn Z q (Y q)) p (X p) +
      conn Z p (VectorField.mlieBracket 𝓘(ℝ, Rn n) X Y p)) =
      Morse.curvOp hN p (amb X p) (amb Y p) (amb Z p) := by
  have hXp := (hX p).mdifferentiableAt (by simp)
  have hYp := (hY p).mdifferentiableAt (by simp)
  have hA : D hN p (conn (fun q => conn Z q (X q)) p (Y p)) =
      Morse.leviCivita hN (amb Y) (Morse.leviCivita hN (amb X) (amb Z)) p := by
    rw [D_conn, amb_conn]
  have hB : D hN p (conn (fun q => conn Z q (Y q)) p (X p)) =
      Morse.leviCivita hN (amb X) (Morse.leviCivita hN (amb Y) (amb Z)) p := by
    rw [D_conn, amb_conn]
  have hbr : D hN p (VectorField.mlieBracket 𝓘(ℝ, Rn n) X Y p) =
      Morse.bracket hN (amb X) (amb Y) p := by
    rw [D_mlieBracket p X Y hXp hYp]
    show _ = Morse.dN hN (amb Y) p (amb X p) - Morse.dN hN (amb X) p (amb Y p)
    exact congrArg₂ (· - ·) (dN_D (amb Y) p (X p)).symm (dN_D (amb X) p (Y p)).symm
  have hC : D hN p (conn Z p (VectorField.mlieBracket 𝓘(ℝ, Rn n) X Y p)) =
      Morse.leviCivita hN (Morse.bracket hN (amb X) (amb Y)) (amb Z) p := by
    rw [D_conn_apply, hbr]
    rfl
  rw [D_tadd, D_tsub_aux, hA, hB, hC,
    ← Morse.curvature_eq hN (contMDiff_amb hX) (contMDiff_amb hY) (contMDiff_amb hZ)
    (isTangentField_amb X) (isTangentField_amb Y) (isTangentField_amb Z) p]
  unfold Morse.curvature
  abel

/-- **Dictionary: curvature.** For the induced connection, `r` is the blind curvature value
`R(x, y)z` at `p` iff `D_p r = Morse.curvR (p : V) (D_p x) (D_p y) (D_p z)`. -/
theorem isCurvVal_iff [FiniteDimensional ℝ W] (p : Sub hN) (x y z r : TangentSpace 𝓘(ℝ, Rn n) p) :
    RoundTrip.V8_13.IsCurvVal (conn (hN := hN)) p x y z r ↔
      D hN p r = Morse.curvR hN (incl hN p) (D hN p x) (D hN p y) (D hN p z) := by
  have hR : ∀ a b c : V, Morse.curvR hN (incl hN p) a b c = Morse.curvOp hN p a b c :=
    fun a b c => Morse.curvR_of_mem hN p.2 a b c
  have hE : ∀ x : TangentSpace 𝓘(ℝ, Rn n) p, amb (ext (hN := hN) (D hN p x)) p = D hN p x :=
    fun x => (congrFun (amb_ext (D hN p x)) p).trans (P_D p x)
  constructor
  · intro h
    have := h _ _ _ (isSmoothVF_ext (D hN p x)) (isSmoothVF_ext (D hN p y))
      (isSmoothVF_ext (D hN p z)) (ext_apply_D p x) (ext_apply_D p y) (ext_apply_D p z)
    refine (congrArg (D hN p) this).trans ?_
    rw [D_curvExpr (isSmoothVF_ext _) (isSmoothVF_ext _) (isSmoothVF_ext _) p, hR, hE, hE, hE]
  · intro h X Y Z hX hY hZ hXp hYp hZp
    apply D_injective p
    rw [h, hR, D_curvExpr hX hY hZ p]
    subst hXp hYp hZp
    rfl

example : RoundTrip.V8_13.IsLC (conn (hN := hN)) := conn_isLC

/-! #### Arc length -/

open Bundle in
theorem norm_mfderiv_curve (c : ℝ → Sub hN) (t : ℝ) :
    ‖(mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) c t (1 : ℝ) : TangentSpace 𝓘(ℝ, Rn n) (c t))‖ =
      ‖deriv (incl hN ∘ c) t‖ := by
  rw [norm_eq]
  exact congrArg (‖·‖) (D_mfderiv_curve c t)

/-- **Dictionary: arc length.** The blind arc length of a curve in `N` is the project's
`Morse.pathLength` of the curve in `V` (no regularity needed). -/
theorem arcLen_eq (c : ℝ → Sub hN) (a b : ℝ) :
    arcLen (n := n) c a b = Morse.pathLength (incl hN ∘ c) a b := by
  unfold arcLen Morse.pathLength
  congr 1
  funext t
  exact norm_mfderiv_curve c t

/-- **Dictionary: energy** (blind file `V8_13`'s `energy`, shared verbatim by the later files). -/
theorem energy_eq (c : ℝ → Sub hN) (a b : ℝ) :
    RoundTrip.V8_13.energy (n := n) c a b = Morse.energy (incl hN ∘ c) a b := by
  unfold RoundTrip.V8_13.energy Morse.energy
  congr 1
  funext t
  rw [norm_mfderiv_curve c t]

/-! #### Uniqueness of geodesics on a closed interval, and `exp` -/

/-- A blind geodesic on `[a, b]` is a project geodesic on `(a, b)`. -/
theorem isGeodesicOn_Ioo {a b : ℝ} (h : IsGeodesic (conn (hN := hN)) c (Icc a b)) :
    Morse.IsGeodesicOn hN (incl hN ∘ c) (Ioo a b) := by
  obtain ⟨-, hc, hP⟩ := isGeodesic_iff.1 h
  refine ⟨isOpen_Ioo, fun t _ => (c t).2, hc.mono Ioo_subset_Icc_self, fun t ht => ?_⟩
  have h1 : deriv (incl hN ∘ c) =ᶠ[𝓝 t] derivWithin (incl hN ∘ c) (Icc a b) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
    exact (derivWithin_of_mem_nhds (Icc_mem_nhds hτ.1 hτ.2)).symm
  have e : deriv (deriv (incl hN ∘ c)) t =
      derivWithin (derivWithin (incl hN ∘ c) (Icc a b)) (Icc a b) t := by
    rw [h1.deriv_eq, derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
  refine (Morse.tanProj_eq_zero_iff hN).1 ?_
  rw [e]
  exact hP t (Ioo_subset_Icc_self ht)

/-- The geodesic equation within `[a, b]`, in a slice chart `σ`: `γ'' = dQ_γ(γ')γ'`,
`Q = Morse.projRep σ` the local extension of `x ↦ P_x`. -/
theorem derivWithin_derivWithin_eq {a b : ℝ} (hab : a < b)
    (h : IsGeodesic (conn (hN := hN)) c (Icc a b)) {t : ℝ} (ht : t ∈ Icc a b)
    (σ : Milnor.SliceChart 𝓘(ℝ, V) (Rn n) W N) (hσ : incl hN (c t) ∈ σ.φ.source) :
    derivWithin (derivWithin (incl hN ∘ c) (Icc a b)) (Icc a b) t =
      fderiv ℝ (Morse.projRep σ) (incl hN (c t)) (derivWithin (incl hN ∘ c) (Icc a b) t)
        (derivWithin (incl hN ∘ c) (Icc a b) t) := by
  obtain ⟨-, hc, hP⟩ := isGeodesic_iff.1 h
  set I := Icc a b
  set f := incl hN ∘ c
  set g := derivWithin f I
  have uI : UniqueDiffOn ℝ I := uniqueDiffOn_Icc hab
  have hg : ContDiffOn ℝ ∞ g I := hc.derivWithin uI (by simp)
  have hf' : HasDerivWithinAt f (g t) I t := ((hc.differentiableOn (by simp)) t ht).hasDerivWithinAt
  have hg' : HasDerivWithinAt g (derivWithin g I t) I t :=
    ((hg.differentiableOn (by simp)) t ht).hasDerivWithinAt
  have hQ : ContDiffAt ℝ ∞ (Morse.projRep σ) (f t) := Morse.contDiffAt_projRep σ (q := c t) hσ
  have h1 : HasDerivWithinAt (fun τ => Morse.projRep σ (f τ) (g τ))
      (fderiv ℝ (Morse.projRep σ) (f t) (g t) (g t) + Morse.projRep σ (f t) (derivWithin g I t))
      I t :=
    (((hQ.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivWithinAt t hf')).clm_apply hg'
  have hsrc : ∀ᶠ τ in 𝓝[I] t, incl hN (c τ) ∈ σ.φ.source :=
    hf'.continuousWithinAt.preimage_mem_nhdsWithin (σ.φ.open_source.mem_nhds hσ)
  have htan : ∀ τ ∈ I, P hN (c τ) (g τ) = g τ := fun τ hτ => by
    have e : D hN (c τ) (vel (n := n) c I τ) = g τ := D_vel (isSmoothCurve_iff.2 hc) uI hτ
    rw [← e]
    exact P_D _ _
  have hQP : ∀ τ, incl hN (c τ) ∈ σ.φ.source → Morse.projRep σ (f τ) = P hN (c τ) :=
    fun τ hτ => Morse.projRep_eq hN σ (x := c τ) hτ
  have hev : g =ᶠ[𝓝[I] t] fun τ => Morse.projRep σ (f τ) (g τ) := by
    filter_upwards [hsrc, self_mem_nhdsWithin] with τ hτ hτI
    rw [hQP τ hτ, htan τ hτI]
  have h2 := (h1.congr_of_eventuallyEq hev (hev.self_of_nhdsWithin ht)).derivWithin (uI t ht)
  rw [h2, hQP t hσ, hP t ht, add_zero]
  rfl

/-- **Uniqueness of geodesics on a closed interval** (from the initial point): two blind
geodesics of the induced connection on `[a, b]` with the same initial point and initial velocity
(read in `V`) coincide on `[a, b]`. -/
theorem eqOn_Icc_of_isGeodesic [FiniteDimensional ℝ W] {c₁ c₂ : ℝ → Sub hN} {a b : ℝ} (hab : a < b)
    (h₁ : IsGeodesic (conn (hN := hN)) c₁ (Icc a b)) (h₂ : IsGeodesic (conn (hN := hN)) c₂ (Icc a b))
    (h0 : c₁ a = c₂ a)
    (h0' : derivWithin (incl hN ∘ c₁) (Icc a b) a = derivWithin (incl hN ∘ c₂) (Icc a b) a) :
    EqOn c₁ c₂ (Icc a b) := by
  obtain ⟨-, hc₁, -⟩ := isGeodesic_iff.1 h₁
  obtain ⟨-, hc₂, -⟩ := isGeodesic_iff.1 h₂
  set I := Icc a b
  have uI : UniqueDiffOn ℝ I := uniqueDiffOn_Icc hab
  have haI : a ∈ I := left_mem_Icc.2 hab.le
  set F₁ : ℝ → V × V := fun t => (incl hN (c₁ t), derivWithin (incl hN ∘ c₁) I t)
  set F₂ : ℝ → V × V := fun t => (incl hN (c₂ t), derivWithin (incl hN ∘ c₂) I t)
  have hF₁ : ContinuousOn F₁ I :=
    hc₁.continuousOn.prodMk (hc₁.derivWithin uI (m := 0) (by simp)).continuousOn
  have hF₂ : ContinuousOn F₂ I :=
    hc₂.continuousOn.prodMk (hc₂.derivWithin uI (m := 0) (by simp)).continuousOn
  have hFa : F₁ a = F₂ a := by
    show (incl hN (c₁ a), _) = (incl hN (c₂ a), _)
    rw [h0, h0']
  -- the geodesic spray in the slice chart at the initial point
  set σ := Morse.sliceAt hN (c₁ a)
  have hσ : incl hN (c₁ a) ∈ σ.φ.source := Morse.mem_sliceAt_source hN (c₁ a)
  set G : V × V → V × V := fun z => (z.2, fderiv ℝ (Morse.projRep σ) z.1 z.2 z.2)
  have hG : ContDiffAt ℝ 1 G (F₁ a) := by
    have hQ : ContDiffAt ℝ ∞ (fderiv ℝ (Morse.projRep σ)) (incl hN (c₁ a)) :=
      (Morse.contDiffAt_projRep σ (q := c₁ a) hσ).fderiv_right (m := ∞) (by simp)
    have h1 : ContDiffAt ℝ ∞ (fun z : V × V => fderiv ℝ (Morse.projRep σ) z.1) (F₁ a) :=
      ContDiffAt.comp (F₁ a) hQ contDiffAt_fst
    exact (contDiffAt_snd.prodMk ((h1.clm_apply contDiffAt_snd).clm_apply contDiffAt_snd)).of_le
      (by exact_mod_cast le_top)
  obtain ⟨K, U₀, hU₀, hK⟩ := hG.exists_lipschitzOnWith
  set U := U₀ ∩ σ.φ.source ×ˢ (univ : Set V)
  have hU : U ∈ 𝓝 (F₁ a) :=
    Filter.inter_mem hU₀ (prod_mem_nhds (σ.φ.open_source.mem_nhds hσ) univ_mem)
  have hU₂ : U ∈ 𝓝 (F₂ a) := hFa ▸ hU
  have e₁ : ∀ᶠ t in 𝓝[I] a, F₁ t ∈ U := (hF₁ a haI).preimage_mem_nhdsWithin hU
  have e₂ : ∀ᶠ t in 𝓝[I] a, F₂ t ∈ U := (hF₂ a haI).preimage_mem_nhdsWithin hU₂
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhdsWithin_iff.1 (e₁.and e₂)
  set ε := min (a + δ / 2) b
  have haε : a < ε := lt_min (by linarith) hab
  have hεb : ε ≤ b := min_le_right _ _
  have hεa : ε ≤ a + δ / 2 := min_le_left _ _
  have hsub : Icc a ε ⊆ Metric.ball a δ ∩ I := fun t ht => by
    refine ⟨?_, ht.1, ht.2.trans hεb⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  -- the lifts solve `F' = G(F)` from the right
  have hlift : ∀ {c : ℝ → Sub hN}, IsGeodesic (conn (hN := hN)) c I →
      ∀ t ∈ Ico a ε, incl hN (c t) ∈ σ.φ.source →
      HasDerivWithinAt (fun τ => (incl hN (c τ), derivWithin (incl hN ∘ c) I τ))
        (G (incl hN (c t), derivWithin (incl hN ∘ c) I t)) (Ici t) t := by
    intro c h t ht hsrc
    obtain ⟨-, hc, -⟩ := isGeodesic_iff.1 h
    have htI : t ∈ Ico a b := ⟨ht.1, ht.2.trans_le hεb⟩
    have hf' : HasDerivWithinAt (incl hN ∘ c) (derivWithin (incl hN ∘ c) I t) I t :=
      ((hc.differentiableOn (by simp)) t (Ico_subset_Icc_self htI)).hasDerivWithinAt
    have hg' : HasDerivWithinAt (derivWithin (incl hN ∘ c) I)
        (derivWithin (derivWithin (incl hN ∘ c) I) I t) I t :=
      (((hc.derivWithin uI (m := 1) (WithTop.coe_le_coe.2 le_top)).differentiableOn (by simp)) t
        (Ico_subset_Icc_self htI)).hasDerivWithinAt
    rw [derivWithin_derivWithin_eq hab h (Ico_subset_Icc_self htI) σ hsrc] at hg'
    exact (hf'.prodMk hg').mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem htI)
  have hloc : EqOn F₁ F₂ (Icc a ε) := by
    refine ODE_solution_unique_of_mem_Icc_right (v := fun _ => G) (s := fun _ => U) (K := K)
      (fun _ _ => hK.mono inter_subset_left) (hF₁.mono fun t ht => (hsub ht).2)
      (fun t ht => hlift h₁ t ht ((hδs (hsub (Ico_subset_Icc_self ht))).1).2.1)
      (fun t ht => (hδs (hsub (Ico_subset_Icc_self ht))).1)
      (hF₂.mono fun t ht => (hsub ht).2)
      (fun t ht => hlift h₂ t ht ((hδs (hsub (Ico_subset_Icc_self ht))).2).2.1)
      (fun t ht => (hδs (hsub (Ico_subset_Icc_self ht))).2) hFa
  -- propagate along the open interval
  have hg₁ := isGeodesicOn_Ioo h₁
  have hg₂ := isGeodesicOn_Ioo h₂
  have ht₀ : (a + ε) / 2 ∈ Ioo a ε := ⟨by linarith, by linarith⟩
  set t₀ := (a + ε) / 2
  have hev : incl hN ∘ c₁ =ᶠ[𝓝 t₀] incl hN ∘ c₂ := by
    filter_upwards [isOpen_Ioo.mem_nhds ht₀] with τ hτ
    exact congrArg Prod.fst (hloc (Ioo_subset_Icc_self hτ))
  have hopen : EqOn (incl hN ∘ c₁) (incl hN ∘ c₂) (Ioo a b) :=
    hg₁.eqOn hg₂ isPreconnected_Ioo ⟨ht₀.1, ht₀.2.trans_le hεb⟩ hev.self_of_nhds hev.deriv_eq
  intro t ht
  apply Subtype.ext
  change (incl hN ∘ c₁) t = (incl hN ∘ c₂) t
  rcases eq_or_lt_of_le ht.1 with rfl | hat
  · exact congrArg (incl hN) h0
  rcases eq_or_lt_of_le ht.2 with rfl | htb
  · have hne : (𝓝[Ioo a t] t).NeBot := by rw [nhdsWithin_Ioo_eq_nhdsLT hab]; infer_instance
    have t₁ := ((hc₁.continuousOn t ht).mono Ioo_subset_Icc_self).tendsto
    have t₂ := ((hc₂.continuousOn t ht).mono Ioo_subset_Icc_self).tendsto
    exact tendsto_nhds_unique t₁ (t₂.congr' (eventually_nhdsWithin_of_forall
      fun τ hτ => (hopen hτ).symm))
  · exact hopen ⟨hat, htb⟩

open Classical in
/-- Lift a curve in `V` to a curve in `N` (junk value `q` where it leaves `N`). -/
def lift (γ : ℝ → V) (q : Sub hN) (t : ℝ) : Sub hN :=
  if h : γ t ∈ N then (⟨γ t, h⟩ : N) else q

theorem lift_of_mem {γ : ℝ → V} (q : Sub hN) {t : ℝ} (h : γ t ∈ N) :
    lift γ q t = (⟨γ t, h⟩ : N) := by
  unfold lift; exact dif_pos h

theorem incl_lift {γ : ℝ → V} (q : Sub hN) {t : ℝ} (h : γ t ∈ N) : incl hN (lift γ q t) = γ t := by
  rw [lift_of_mem q h]; rfl

/-- `vel`, read in `V`, determines the initial data of `InitData`. -/
theorem initData_iff {γ : ℝ → Sub hN} {s : Set ℝ} {q : Sub hN} {w : TangentSpace 𝓘(ℝ, Rn n) q}
    (h0 : γ 0 = q) : InitData (n := n) γ s q w ↔ D hN (γ 0) (vel (n := n) γ s 0) = D hN q w := by
  constructor
  · rintro ⟨-, hv⟩
    have : (vel (n := n) γ s 0 : Rn n) = (w : Rn n) := eq_of_heq hv
    rw [this, h0]
  · intro h
    refine ⟨h0, heq_of_eq ?_⟩
    have h' : D hN q (vel (n := n) γ s 0) = D hN q w := by rwa [h0] at h
    exact D_injective q h'

/-- A project geodesic on `(-δ, 1 + δ)` restricts to a blind geodesic on `[0, 1]`. -/
theorem isGeodesic_lift_of_isGeodesicFrom {γ : ℝ → V} {q : Sub hN}
    {w : TangentSpace 𝓘(ℝ, Rn n) q} (h : Morse.IsGeodesicFrom hN γ (incl hN q) (D hN q w)) :
    IsGeodesic (conn (hN := hN)) (lift γ q) (Icc 0 1) ∧
      InitData (n := n) (lift γ q) (Icc 0 1) q w ∧ ∀ t ∈ Icc (0 : ℝ) 1, incl hN (lift γ q t) = γ t := by
  obtain ⟨δ, hδ, hγ, hγ0, hγ0'⟩ := h
  set I := Icc (0 : ℝ) 1
  set J := Ioo (-δ) (1 + δ)
  have hIJ : I ⊆ J := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have uI : UniqueDiffOn ℝ I := uniqueDiffOn_Icc zero_lt_one
  have heq : EqOn (incl hN ∘ lift γ q) γ I := fun t ht => incl_lift q (hγ.mem t (hIJ ht))
  have hd : EqOn (derivWithin (incl hN ∘ lift γ q) I) (deriv γ) I := fun t ht => by
    rw [derivWithin_congr heq (heq ht)]
    exact (hγ.hasDerivAt (hIJ ht)).hasDerivWithinAt.derivWithin (uI t ht)
  have hdd : ∀ t ∈ I, derivWithin (derivWithin (incl hN ∘ lift γ q) I) I t =
      deriv (deriv γ) t := fun t ht => by
    rw [derivWithin_congr hd (hd ht)]
    exact (hγ.hasDerivAt_deriv (hIJ ht)).hasDerivWithinAt.derivWithin (uI t ht)
  have hgeo : IsGeodesic (conn (hN := hN)) (lift γ q) I := by
    refine isGeodesic_iff.2 ⟨⟨ordConnected_Icc, uI⟩, (hγ.contDiffOn.mono hIJ).congr heq,
      fun t ht => ?_⟩
    rw [hdd t ht, lift_of_mem q (hγ.mem t (hIJ ht))]
    exact hγ.tanProj_deriv_deriv (hIJ ht)
  have h0I : (0 : ℝ) ∈ I := ⟨le_rfl, zero_le_one⟩
  have hl0 : lift γ q 0 = q := by
    apply Subtype.ext
    exact (incl_lift q (hγ.mem 0 (hIJ h0I))).trans hγ0
  refine ⟨hgeo, (initData_iff hl0).2 ?_, heq⟩
  rw [D_vel (isSmoothCurve_iff.2 (isGeodesic_iff.1 hgeo).2.1) uI h0I, hd h0I, hγ0']

theorem expDefined_of_mem_expDom {q : Sub hN} {w : TangentSpace 𝓘(ℝ, Rn n) q}
    (h : (incl hN q, D hN q w) ∈ Morse.expDom hN) : ExpDefined (conn (hN := hN)) q w := by
  obtain ⟨γ, hγ⟩ := h
  obtain ⟨h1, h2, -⟩ := isGeodesic_lift_of_isGeodesicFrom (w := w) hγ
  exact ⟨_, h1, h2⟩

/-- **Dictionary: the exponential map.** Where the project's `exp` is defined (a geodesic on an
open interval containing `[0, 1]`), the blind `exp` is defined and agrees with it. (The converse,
that a geodesic on `[0, 1]` extends past the endpoints, is not formalized in the project.) -/
theorem expMap_eq [FiniteDimensional ℝ W] {q : Sub hN} {w : TangentSpace 𝓘(ℝ, Rn n) q}
    (h : (incl hN q, D hN q w) ∈ Morse.expDom hN) :
    incl hN (expMap (conn (hN := hN)) q w) = Morse.exp hN (incl hN q) (D hN q w) := by
  obtain ⟨γ, hγ⟩ := h
  obtain ⟨h1, h2, h3⟩ := isGeodesic_lift_of_isGeodesicFrom (w := w) hγ
  have hex : ExpDefined (conn (hN := hN)) q w := ⟨_, h1, h2⟩
  rw [Morse.IsGeodesicFrom.exp_eq hγ, expMap, dif_pos hex]
  obtain ⟨hc1, hc2⟩ := hex.choose_spec
  have uI : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have e0 : hex.choose 0 = lift γ q 0 := hc2.1.trans h2.1.symm
  have e0' : derivWithin (incl hN ∘ hex.choose) (Icc 0 1) 0 =
      derivWithin (incl hN ∘ lift γ q) (Icc 0 1) 0 := by
    rw [← D_vel (isSmoothCurve_iff.2 (isGeodesic_iff.1 hc1).2.1) uI h0I,
      ← D_vel (isSmoothCurve_iff.2 (isGeodesic_iff.1 h1).2.1) uI h0I,
      (initData_iff hc2.1).1 hc2, (initData_iff h2.1).1 h2]
  have := eqOn_Icc_of_isGeodesic zero_lt_one hc1 h1 e0 e0' ⟨zero_le_one, le_rfl⟩
  rw [this]
  exact h3 1 ⟨zero_le_one, le_rfl⟩

/-! #### Piecewise smooth paths and the distance -/

theorem le_of_strictSeq {t : ℕ → ℝ} {k : ℕ} (ht : ∀ i < k, t i < t (i + 1)) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ k) : t i ≤ t j := by
  induction j with
  | zero => rw [Nat.le_zero.1 hij]
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · exact (ih (Nat.lt_succ_iff.1 h) (by omega)).trans (ht j (by omega)).le
    · rw [le_antisymm hij h]

theorem lt_of_strictSeq {t : ℕ → ℝ} {k : ℕ} (ht : ∀ i < k, t i < t (i + 1)) {i j : ℕ}
    (hij : i < j) (hj : j ≤ k) : t i < t j :=
  (ht i (by omega)).trans_le (le_of_strictSeq ht hij (by omega) |>.trans_eq' rfl |> fun h =>
    le_of_strictSeq ht (Nat.succ_le_of_lt hij) hj)

/-- A blind piecewise smooth path in `N` is a project piecewise smooth path in `V`. -/
theorem isPiecewiseSmooth_of_isPW {pth : ℝ → Sub hN} {a b : ℝ} (h : IsPW (n := n) pth a b) :
    Morse.IsPiecewiseSmooth (incl hN ∘ pth) a b := by
  obtain ⟨k, t, h0, hk, hlt, hsm⟩ := h
  have hsm' : ∀ i < k, ContDiffOn ℝ ∞ (incl hN ∘ pth) (Icc (t i) (t (i + 1))) :=
    fun i hi => contMDiffOn_curve_iff.1 (hsm i hi)
  have hab : a ≤ b := h0 ▸ hk ▸ le_of_strictSeq hlt (Nat.zero_le k) le_rfl
  refine ⟨hab, ?_, (Finset.range (k + 1)).image t, ?_⟩
  · have key : ∀ j ≤ k, ContinuousOn (incl hN ∘ pth) (Icc (t 0) (t j)) := by
      intro j
      induction j with
      | zero => intro _; rw [Icc_self]; exact continuousOn_singleton _ _
      | succ j ih =>
        intro hj
        rw [← Icc_union_Icc_eq_Icc (le_of_strictSeq hlt (Nat.zero_le j) (by omega))
          (hlt j (by omega)).le]
        exact (ih (by omega)).union_of_isClosed (hsm' j (by omega)).continuousOn isClosed_Icc
          isClosed_Icc
    rw [← h0, ← hk]
    exact key k le_rfl
  · intro s u has hsu hub hB
    have hP : ∃ j, s < t j ∧ j ≤ k := ⟨k, by rw [hk]; linarith, le_rfl⟩
    classical
    set m := Nat.find hP
    have hm : s < t m ∧ m ≤ k := Nat.find_spec hP
    have hm0 : m ≠ 0 := by
      intro h; have := hm.1; rw [h, h0] at this; linarith
    have hi : t (m - 1) ≤ s := by
      by_contra hcon
      exact Nat.find_min hP (Nat.sub_lt (Nat.pos_of_ne_zero hm0) one_pos)
        ⟨lt_of_not_ge hcon, by omega⟩
    have hu : u ≤ t m := by
      by_contra hcon
      exact hB (t m) (Finset.mem_image.2 ⟨m, Finset.mem_range.2 (by omega), rfl⟩)
        ⟨hm.1, lt_of_not_ge hcon⟩
    have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)
    refine (hsm' (m - 1) (by omega)).mono ?_
    rw [hm1]
    exact Icc_subset_Icc hi hu

/-- A project piecewise smooth path with values in `N` lifts to a blind piecewise smooth path. -/
theorem isPW_lift {c : ℝ → V} {a b : ℝ} (hc : Morse.IsPiecewiseSmooth c a b)
    (hcN : ∀ t ∈ Icc a b, c t ∈ N) (p₀ : Sub hN) : IsPW (n := n) (lift c p₀) a b := by
  obtain ⟨hab, -, B, hB⟩ := hc
  have heq : EqOn (incl hN ∘ lift c p₀) c (Icc a b) := fun t ht => incl_lift p₀ (hcN t ht)
  -- it suffices to find a subdivision avoiding `B`
  suffices hsub : ∃ (k : ℕ) (t : ℕ → ℝ), t 0 = a ∧ t k = b ∧ (∀ i < k, t i < t (i + 1)) ∧
      ∀ i < k, a ≤ t i ∧ t (i + 1) ≤ b ∧ ∀ x ∈ B, x ∉ Ioo (t i) (t (i + 1)) by
    obtain ⟨k, t, h0, hk, hlt, hgood⟩ := hsub
    refine ⟨k, t, h0, hk, hlt, fun i hi => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hgood i hi
    refine contMDiffOn_curve_iff.2 ((hB _ _ h1 (hlt i hi) h2 h3).congr ?_)
    exact heq.mono (Icc_subset_Icc h1 h2)
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact ⟨0, fun _ => a, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _),
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  classical
  set S : Finset ℝ := insert a (insert b (B.filter (· ∈ Ioo a b)))
  have hS : ∀ x ∈ S, a ≤ x ∧ x ≤ b := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_filter] at hx
    rcases hx with rfl | rfl | ⟨-, hx⟩
    · exact ⟨le_rfl, hlt.le⟩
    · exact ⟨hlt.le, le_rfl⟩
    · exact ⟨hx.1.le, hx.2.le⟩
  have haS : a ∈ S := Finset.mem_insert_self _ _
  have hbS : b ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  set m := S.card
  have hm : 1 < m := Finset.one_lt_card.2 ⟨a, haS, b, hbS, hlt.ne⟩
  set e := S.orderEmbOfFin rfl
  set t : ℕ → ℝ := fun j => if h : j < m then e ⟨j, h⟩ else b
  have ht : ∀ j (h : j < m), t j = e ⟨j, h⟩ := fun j h => dif_pos h
  refine ⟨m - 1, t, ?_, ?_, ?_, ?_⟩
  · rw [ht 0 (by omega), Finset.orderEmbOfFin_zero rfl (by omega)]
    exact le_antisymm (Finset.min'_le _ _ haS) ((hS _ (Finset.min'_mem _ _)).1)
  · rw [ht (m - 1) (by omega), Finset.orderEmbOfFin_last rfl (by omega)]
    exact le_antisymm ((hS _ (Finset.max'_mem _ _)).2) (Finset.le_max' _ _ hbS)
  · intro i hi
    rw [ht i (by omega), ht (i + 1) (by omega)]
    exact e.strictMono (Fin.mk_lt_mk.2 (Nat.lt_succ_self i))
  · intro i hi
    rw [ht i (by omega), ht (i + 1) (by omega)]
    refine ⟨(hS _ (Finset.orderEmbOfFin_mem _ _ _)).1, (hS _ (Finset.orderEmbOfFin_mem _ _ _)).2,
      fun x hx hxi => ?_⟩
    have hxS : x ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_filter.2 ⟨hx, (hS _ (Finset.orderEmbOfFin_mem _ _ _)).1.trans_lt hxi.1,
        hxi.2.trans_le (hS _ (Finset.orderEmbOfFin_mem _ _ _)).2⟩))
    obtain ⟨j, rfl⟩ : x ∈ Set.range e := by
      rw [Finset.range_orderEmbOfFin]; exact hxS
    have h1 := e.lt_iff_lt.1 hxi.1
    have h2 := e.lt_iff_lt.1 hxi.2
    rw [Fin.lt_def] at h1 h2
    simp only at h1 h2
    omega

theorem pathLength_congr {c c' : ℝ → V} {a b : ℝ} (hab : a ≤ b) (h : EqOn c c' (Icc a b)) :
    Morse.pathLength c a b = Morse.pathLength c' a b := by
  unfold Morse.pathLength
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.1
    (MeasureTheory.measure_singleton (μ := MeasureTheory.volume) b)] with x hx hxab
  rw [uIoc_of_le hab] at hxab
  have hxb : x < b := lt_of_le_of_ne hxab.2 hx
  have hev : c =ᶠ[𝓝 x] c' := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hxab.1, hxb⟩] with y hy
    exact h (Ioo_subset_Icc_self hy)
  rw [hev.deriv_eq]

open Bundle in
theorem arcLen_nonneg {pth : ℝ → Sub hN} {a b : ℝ} (hab : a ≤ b) : 0 ≤ arcLen (n := n) pth a b :=
  intervalIntegral.integral_nonneg hab fun _ _ => norm_nonneg _

/-- The blind lengths of paths from `p` to `q` are the project's lengths (`Morse.pathLengths`). -/
theorem pathLengths_eq (p q : Sub hN) :
    Morse.pathLengths (N := N) (incl hN p) (incl hN q) = ENNReal.ofReal ''
      {L | ∃ (pth : ℝ → Sub hN) (a b : ℝ), a ≤ b ∧ IsPW (n := n) pth a b ∧ pth a = p ∧
        pth b = q ∧ arcLen (n := n) pth a b = L} := by
  ext L
  constructor
  · rintro ⟨c, a, b, hc, hcN, ha, hb, rfl⟩
    have hab := hc.1
    have heq : EqOn (incl hN ∘ lift c p) c (Icc a b) := fun t ht => incl_lift p (hcN t ht)
    refine ⟨arcLen (n := n) (lift c p) a b, ⟨lift c p, a, b, hab, isPW_lift hc hcN p, ?_, ?_, rfl⟩,
      ?_⟩
    · apply Subtype.ext; exact (heq ⟨le_rfl, hab⟩).trans ha
    · apply Subtype.ext; exact (heq ⟨hab, le_rfl⟩).trans hb
    · rw [arcLen_eq, pathLength_congr hab heq]
  · rintro ⟨L', ⟨pth, a, b, hab, hpw, ha, hb, rfl⟩, rfl⟩
    refine ⟨incl hN ∘ pth, a, b, isPiecewiseSmooth_of_isPW hpw, fun t _ => (pth t).2,
      congrArg (incl hN) ha, congrArg (incl hN) hb, ?_⟩
    rw [arcLen_eq]

/-- **Dictionary: the distance.** The blind `ρ(p, q)` is the project's `riemDist`, as a real
number (both are `0`/`∞` exactly when no piecewise smooth path joins `p` and `q`). -/
theorem rho_eq (p q : Sub hN) :
    rho (n := n) p q = (Morse.riemDist (N := N) (incl hN p) (incl hN q)).toReal := by
  rw [Morse.riemDist, pathLengths_eq, ENNReal.toReal_sInf _ ?_]
  · rw [rho, Set.image_image]
    congr 1
    ext L
    constructor
    · intro hL
      refine ⟨L, hL, ?_⟩
      obtain ⟨pth, a, b, hab, -, -, -, rfl⟩ := hL
      exact ENNReal.toReal_ofReal (arcLen_nonneg hab)
    · rintro ⟨L', hL', rfl⟩
      obtain ⟨pth, a, b, hab, hpw, ha, hb, rfl⟩ := hL'
      show (ENNReal.ofReal (arcLen (n := n) pth a b)).toReal ∈ _
      rw [ENNReal.toReal_ofReal (arcLen_nonneg hab)]
      exact ⟨pth, a, b, hab, hpw, ha, hb, rfl⟩
  · rintro _ ⟨L, -, rfl⟩
    exact ENNReal.ofReal_ne_top

end Blind

end RoundTrip.Bridge
