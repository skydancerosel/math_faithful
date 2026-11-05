import Morse
import RoundTrip.Check
import RoundTrip.Blind.V2_5

open scoped ContDiff Manifold unitInterval
open TopologicalSpace

noncomputable section

namespace RoundTrip.V2_5

/-- The project's statement: the types of the six listed theorems about the concrete example
`Morse.RemarkP13.F` (the bowl `‖z‖²` on `ℂ \ {i}`). -/
def A : Prop :=
  (type_of% @Morse.RemarkP13.remark_p13) ∧
  (type_of% @Morse.RemarkP13.remark_p13_not_isStrongDeformationRetract) ∧
  (type_of% @Morse.RemarkP13.remark_p13_not_homeomorph) ∧
  (type_of% @Morse.RemarkP13.remark_p13_not_isCompact) ∧
  (type_of% @Morse.RemarkP13.remark_p13_not_isCriticalPoint) ∧
  (type_of% @Morse.RemarkP13.remark_p13_plane)

theorem A_holds : A :=
  ⟨Morse.RemarkP13.remark_p13, Morse.RemarkP13.remark_p13_not_isStrongDeformationRetract,
    Morse.RemarkP13.remark_p13_not_homeomorph, Morse.RemarkP13.remark_p13_not_isCompact,
    Morse.RemarkP13.remark_p13_not_isCriticalPoint, Morse.RemarkP13.remark_p13_plane⟩

/-! ### Glue -/

/-- Milnor's `r_t` gives the project's strong deformation retract. -/
theorem isSDR_of_defRetract {Y : Type} [TopologicalSpace Y] {S : Set Y} (h : DefRetract S) :
    Morse.IsStrongDeformationRetract S := by
  obtain ⟨r, hc, h0, h1, hS⟩ := h
  refine ⟨⟨r 1, hc.comp (continuous_const.prodMk continuous_id)⟩, h1,
    ⟨{ toFun := fun z => r z.1 z.2
       continuous_toFun := hc
       map_zero_left := h0
       map_one_left := fun _ => rfl
       prop' := ?_ }⟩⟩
  intro t x hx
  simp [hS x hx t]

/-- Deformation retracts transport along homeomorphisms. -/
theorem defRetract_transport {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (Ψ : X ≃ₜ Y)
    (S : Set X) (T : Set Y) (hST : ∀ x, x ∈ S ↔ Ψ x ∈ T) (h : DefRetract T) : DefRetract S := by
  obtain ⟨r, hc, h0, h1, hT⟩ := h
  refine ⟨fun t x => Ψ.symm (r t (Ψ x)),
    Ψ.symm.continuous.comp (hc.comp (continuous_fst.prodMk (Ψ.continuous.comp continuous_snd))),
    fun x => by simp [h0], fun x => ?_, fun x hx t => ?_⟩
  · rw [hST, Homeomorph.apply_symm_apply]; exact h1 _
  · simp [hT _ ((hST x).1 hx) t]

/-- The plane `ℂ` as `ℝ²`. -/
abbrev P := EuclideanSpace ℝ (Fin 2)

/-- The isometry `ℂ ≃ ℝ²`. -/
def e : ℂ ≃ₗᵢ[ℝ] P := Complex.orthonormalBasisOneI.repr

/-- The punctured plane `ℝ² \ {e i}`, an open subset of `ℝ²`, hence a smooth surface. -/
def U : Opens P := ⟨{e Complex.I}ᶜ, isOpen_compl_singleton⟩

/-- The height function on `U`. -/
def f (x : U) : ℝ := ‖(x : P)‖ ^ 2

/-- `ℂ \ {i} ≃ₜ U`. -/
def Φ : Morse.RemarkP13.M ≃ₜ U :=
  e.toHomeomorph.subtype fun z => by
    change z ≠ Complex.I ↔ e z ≠ e Complex.I
    exact e.injective.ne_iff.symm

theorem f_Φ (z : Morse.RemarkP13.M) : f (Φ z) = Morse.RemarkP13.F z := by
  change ‖e z‖ ^ 2 = ‖(z : ℂ)‖ ^ 2
  rw [e.norm_map]

/-- `M^4 ≃ₜ U^4` (sublevel sets). -/
def Ψ : Morse.sublevel Morse.RemarkP13.F 4 ≃ₜ {x : U | f x ≤ 4} :=
  Φ.subtype fun z => by
    change Morse.RemarkP13.F z ≤ 4 ↔ f (Φ z) ≤ 4
    rw [f_Φ]

theorem contMDiff_f : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ) ∞ f :=
  (contDiff_norm_sq ℝ).contMDiff.comp contMDiff_subtype_val

theorem not_crit (x : U) (hx : f x ∈ Set.Icc (1 / 4 : ℝ) 4) :
    ¬ Morse.IsCriticalPointM P f x := by
  rw [Morse.isCriticalPointM_iff_fderiv]
  have hloc : Morse.localRep P f x =ᶠ[nhds (extChartAt 𝓘(ℝ, P) x x)] fun u : P => ‖u‖ ^ 2 := by
    have h := Opens.chartAt_subtype_val_symm_eventuallyEq (H := P) U (x := x)
    simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply,
      id_eq] at h
    rw [Morse.localRep_eq]
    have hx0 : extChartAt 𝓘(ℝ, P) x x = (x : P) := by
      rw [Morse.extChartAt_self_coe]; rfl
    rw [hx0]
    filter_upwards [h] with u hu
    simp only [Function.comp_apply, f]
    simp only [id_eq, Function.comp_apply] at hu
    rw [← hu]
  rw [hloc.fderiv_eq]
  have hx0 : extChartAt 𝓘(ℝ, P) x x = (x : P) := by
    rw [Morse.extChartAt_self_coe]; rfl
  rw [hx0]
  intro h0
  have hd := ((hasStrictFDerivAt_norm_sq (x : P)).hasFDerivAt).fderiv
  rw [hd] at h0
  have := congrArg (fun L : P →L[ℝ] ℝ => L (x : P)) h0
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, real_inner_self_eq_norm_sq,
    ContinuousLinearMap.zero_apply] at this
  have hpos : 0 < ‖(x : P)‖ ^ 2 := by
    have : (1 / 4 : ℝ) ≤ f x := hx.1
    simp only [f] at this; linarith
  norm_num at this
  rw [this, norm_zero] at hpos
  norm_num at hpos

theorem A_to_B : A → B := by
  intro hA
  refine ⟨U, inferInstance, inferInstance, inferInstance, inferInstance, f, 1 / 4, 4,
    contMDiff_f, by norm_num, not_crit, ?_, ?_⟩
  · -- not compact: transport `remark_p13_not_isCompact` along `Φ`
    intro hc
    apply hA.2.2.2.1
    have : Morse.RemarkP13.F ⁻¹' Set.Icc (1 / 4) 4 = Φ ⁻¹' (f ⁻¹' Set.Icc (1 / 4) 4) := by
      ext z
      simp only [Set.mem_preimage, f_Φ]
    rw [this, Φ.isCompact_preimage]
    exact hc
  · -- not a deformation retract: transport `remark_p13_not_isStrongDeformationRetract`
    intro hdr
    apply hA.2.1
    refine isSDR_of_defRetract (defRetract_transport Ψ _ _ (fun z => ?_) hdr)
    change Morse.RemarkP13.F z.1 ≤ 1 / 4 ↔ f (Φ z.1) ≤ 1 / 4
    rw [f_Φ]

#rt_check RoundTrip.V2_5.A_to_B [Morse.RemarkP13.remark_p13,
  Morse.RemarkP13.remark_p13_not_isStrongDeformationRetract, Morse.RemarkP13.remark_p13_not_homeomorph,
  Morse.RemarkP13.remark_p13_not_isCompact, Morse.RemarkP13.remark_p13_not_isCriticalPoint,
  Morse.RemarkP13.remark_p13_plane]

end RoundTrip.V2_5
