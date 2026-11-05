import Morse
import RoundTrip.L2.Blind.Morse_IsFocalPoint

/-! Layer-2 check of `Morse.IsFocalPoint` (`∃ μ, IsFocalPointMult …`) against the blind textbook
definition.

Project: `(q, e − q)` lies in the normal bundle `Milnor.Problems.normalBundleSet hM` (normality to
the tangent space `range (d val)`), and `Morse.endpointNullity` (the dimension of the kernel of
`mfderiv` of `E(q, v) = q + v` on the normal bundle `N`, for the manifold structure of `N` as a
slice submanifold of `ℝⁿ × ℝⁿ` modelled on `ℝⁿ`) is positive.

Blind: tangent spaces of `M` and of `N` built from scratch as spans of velocities of smooth curves,
and the nullity is the dimension of the kernel of `(a, b) ↦ a + b` on `T_{(q,v)}N ⊆ ℝⁿ × ℝⁿ`.

Equal for every slice submanifold `M ⊆ ℝⁿ` (with `k + w = n`, as in the signature):
* the two tangent spaces agree on `M` and on `N` (`tangentSubspace_eq_span`, as in the
  `Morse_tangentSubspace` item), so the normal bundles agree (`normalBundle_eq`);
* `mfderiv E = (a, b) ↦ a + b` composed with `D = mfderiv val`, which is injective
  (`Milnor.injective_mfderiv_val`) with range `T_xN`, so the kernels have the same dimension
  (`finrank_ker_comp_eq`, `nullity_eq`). -/

namespace RoundTrip.L2.Morse_IsFocalPoint

open Filter Topology
open scoped ContDiff Manifold

section Tangent

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}

/-- Every vector of the project tangent space is a velocity. -/
theorem exists_curve (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N) {q : N} (hq : q.1 ∈ σ.φ.source)
    (a : Z) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → V, ContDiffOn ℝ ∞ γ (Set.Ioo (-ε) ε) ∧
      Set.MapsTo γ (Set.Ioo (-ε) ε) N ∧ γ 0 = q ∧
      HasDerivAt γ (fderiv ℝ (Morse.sliceParam σ) (σ.φ q).1 a) 0 := by
  set z₀ : Z := (σ.φ q).1 with hz₀
  have hz₀mem : z₀ ∈ σ.toChart.target := Morse.toChart_apply_mem_target σ hq
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (Morse.isOpen_toChart_target σ) z₀ hz₀mem
  set ε : ℝ := r / (‖a‖ + 1) with hε
  have hε0 : 0 < ε := div_pos hr (by positivity)
  have hmaps : Set.MapsTo (fun t : ℝ => z₀ + t • a) (Set.Ioo (-ε) ε) σ.toChart.target := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    have ht' : |t| < ε := abs_lt.2 ht
    have h1 : |t| * (‖a‖ + 1) < r := by
      rw [hε, lt_div_iff₀ (by positivity)] at ht'
      exact ht'
    nlinarith [abs_nonneg t, norm_nonneg a]
  refine ⟨ε, hε0, fun t => Morse.sliceParam σ (z₀ + t • a), ?_, ?_, ?_, ?_⟩
  · exact (Morse.contDiffOn_sliceParam σ).comp
      (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffOn hmaps
  · exact fun t ht => Morse.sliceParam_mem σ (hmaps ht)
  · simpa using Morse.sliceParam_toChart σ hq
  · have hd : HasDerivAt (fun t : ℝ => z₀ + t • a) a 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add z₀
    have hx : HasFDerivAt (Morse.sliceParam σ) (fderiv ℝ (Morse.sliceParam σ) z₀) (z₀ + (0:ℝ) • a) := by
      rw [zero_smul, add_zero]
      exact ((Morse.contDiffAt_sliceParam σ hz₀mem).differentiableAt (by simp)).hasFDerivAt
    exact hx.comp_hasDerivAt 0 hd

/-- Every velocity lies in the project tangent space. -/
theorem mem_of_velocity (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (q : N) {v : V}
    (hv : ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → V, ContDiffOn ℝ ∞ γ (Set.Ioo (-ε) ε) ∧
      Set.MapsTo γ (Set.Ioo (-ε) ε) N ∧ γ 0 = q ∧ HasDerivAt γ v 0) :
    v ∈ Morse.tangentSubspace hN q := by
  obtain ⟨ε, hε, γ, -, hγN, hγ0, hγv⟩ := hv
  obtain ⟨σ, hσ⟩ := hN q.1 q.2
  rw [Morse.tangentSubspace_eq_range_fderiv_sliceParam hN σ hσ]
  -- `φ` is differentiable at `q`
  have hφ : DifferentiableAt ℝ σ.φ q := by
    have h1 := σ.φ.contMDiffOn_toFun
    rw [contMDiffOn_iff_contDiffOn] at h1
    exact (h1.contDiffAt (σ.φ.open_source.mem_nhds hσ)).differentiableAt (by simp)
  set c : ℝ → Z := fun t => (σ.φ (γ t)).1 with hc_def
  have hc : HasDerivAt c (fderiv ℝ (fun x => (σ.φ x).1) q v) 0 := by
    have hfst : DifferentiableAt ℝ (fun x => (σ.φ x).1) (γ 0) := by
      rw [hγ0]
      exact differentiableAt_fst.comp _ hφ
    exact hγ0 ▸ hfst.hasFDerivAt.comp_hasDerivAt 0 hγv
  have hc0 : c 0 = (σ.φ q).1 := by simp [hc_def, hγ0]
  -- near `0`, `γ = x ∘ c`
  have hev : γ =ᶠ[𝓝 0] Morse.sliceParam σ ∘ c := by
    have h1 : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ σ.φ.source :=
      hγv.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact σ.φ.open_source.mem_nhds hσ)
    have h2 : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Set.Ioo (-ε) ε :=
      Ioo_mem_nhds (by linarith) hε
    filter_upwards [h1, h2] with t ht1 ht2
    have hs : (σ.φ (γ t)).2 = 0 := (σ.slice _ ht1).1 (hγN ht2)
    have : ((σ.φ (γ t)).1, (0 : W)) = σ.φ (γ t) := Prod.ext rfl hs.symm
    simp only [Function.comp_apply, hc_def, Morse.sliceParam]
    rw [this, σ.φ.invFun_apply ht1]
  have hx : HasFDerivAt (Morse.sliceParam σ) (fderiv ℝ (Morse.sliceParam σ) (σ.φ q).1) (c 0) := by
    rw [hc0]
    exact ((Morse.contDiffAt_sliceParam σ (Morse.toChart_apply_mem_target σ hσ)).differentiableAt
      (by simp)).hasFDerivAt
  have hγ' := (hx.comp_hasDerivAt 0 hc).congr_of_eventuallyEq hev
  exact ⟨_, (hγv.unique hγ').symm⟩

/-- The project tangent space is the span of the velocities. -/
theorem tangentSubspace_eq_span (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (q : N) :
    Morse.tangentSubspace hN q = Submodule.span ℝ {v | ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → V,
      ContDiffOn ℝ ∞ γ (Set.Ioo (-ε) ε) ∧ Set.MapsTo γ (Set.Ioo (-ε) ε) N ∧ γ 0 = q ∧
        HasDerivAt γ v 0} := by
  apply le_antisymm
  · obtain ⟨σ, hσ⟩ := hN q.1 q.2
    rw [Morse.tangentSubspace_eq_range_fderiv_sliceParam hN σ hσ]
    rintro _ ⟨a, rfl⟩
    exact Submodule.subset_span (exists_curve σ hσ a)
  · exact Submodule.span_le.2 fun v hv => mem_of_velocity hN q hv

end Tangent

/-- Linear algebra: for an injective `D`, the kernel of `L ∘ D` is the kernel of `L` restricted to
the range of `D`. -/
theorem finrank_ker_comp_eq {A B C : Type*} [AddCommGroup A] [Module ℝ A] [AddCommGroup B]
    [Module ℝ B] [AddCommGroup C] [Module ℝ C] (L : B →ₗ[ℝ] C) (D : A →ₗ[ℝ] B)
    (hD : Function.Injective D) :
    Module.finrank ℝ (LinearMap.ker (L ∘ₗ D)) =
      Module.finrank ℝ (LinearMap.ker (L.domRestrict (LinearMap.range D))) := by
  refine LinearEquiv.finrank_eq (LinearEquiv.ofBijective
    (D.rangeRestrict.restrict (p := LinearMap.ker (L ∘ₗ D))
      (q := LinearMap.ker (L.domRestrict (LinearMap.range D))) fun a ha => ha) ⟨?_, ?_⟩)
  · intro a b hab
    apply Subtype.ext
    apply hD
    exact congrArg (fun x : LinearMap.ker (L.domRestrict (LinearMap.range D)) =>
      ((x : LinearMap.range D) : B)) hab
  · rintro ⟨⟨y, ⟨a, rfl⟩⟩, hy⟩
    exact ⟨⟨a, hy⟩, rfl⟩

local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)

variable {n k w : ℕ} {M : Set (𝔼 n)}
  (hM : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ (𝔼 n)) (𝔼 k) (𝔼 w) M)

include hM in
/-- The blind normal bundle is the project's. -/
theorem normalBundle_eq : normalBundle M = Milnor.Problems.normalBundleSet hM := by
  ext ⟨x, v⟩
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, fun t ht => h t ?_⟩
    change t ∈ Morse.tangentSubspace hM ⟨x, hx⟩ at ht
    rw [tangentSubspace_eq_span] at ht
    exact ht
  · rintro ⟨hx, h⟩
    refine ⟨hx, fun u hu => h u ?_⟩
    change u ∈ Morse.tangentSubspace hM ⟨x, hx⟩
    rw [tangentSubspace_eq_span]
    exact hu

/-- The blind nullity of the Jacobian of `E` is the project's `endpointNullity`. -/
theorem nullity_eq (hkw : k + w = n) (x : Milnor.Problems.normalBundleSet hM) :
    nullity M x.1 = Morse.endpointNullity hM hkw x := by
  have hN := Milnor.Problems.isSliceSubmanifold_normalBundle hM hkw
  let _ := hN.chartedSpace
  set D := Milnor.mfd 𝓘(ℝ, 𝔼 n) 𝓘(ℝ, 𝔼 n × 𝔼 n)
    (Subtype.val : Milnor.Problems.normalBundleSet hM → 𝔼 n × 𝔼 n) x with hD
  have hDinj : Function.Injective D := Milnor.injective_mfderiv_val hN x
  have htan : tangentSpace (normalBundle M) x.1 = LinearMap.range (D : 𝔼 n →ₗ[ℝ] 𝔼 n × 𝔼 n) := by
    have h1 := tangentSubspace_eq_span hN x
    rw [normalBundle_eq hM]
    exact h1.symm
  have hcomp : (Milnor.mfd 𝓘(ℝ, 𝔼 n) 𝓘(ℝ, 𝔼 n) (Milnor.Problems.normalSum hM) x :
      𝔼 n →ₗ[ℝ] 𝔼 n) = dEndpoint ∘ₗ (D : 𝔼 n →ₗ[ℝ] 𝔼 n × 𝔼 n) := by
    refine LinearMap.ext fun z => ?_
    exact Milnor.Problems.mfd_normalSum_apply hM hkw x z
  rw [nullity, Morse.endpointNullity, hcomp, htan, finrank_ker_comp_eq _ _ hDinj]

/-- **Agreement** for every slice submanifold `M ⊆ ℝⁿ`. -/
theorem agree (hkw : k + w = n) (q : ↑M) (e : 𝔼 n) :
    Morse.IsFocalPoint hM hkw q e ↔ T hM hkw q e := by
  constructor
  · rintro ⟨μ, h, hμ, hpos⟩
    refine ⟨(normalBundle_eq hM).symm ▸ h, ?_⟩
    rw [nullity_eq hM hkw ⟨_, h⟩, hμ]
    exact hpos
  · rintro ⟨h, hpos⟩
    have h' : ((q : 𝔼 n), e - q) ∈ Milnor.Problems.normalBundleSet hM := normalBundle_eq hM ▸ h
    refine ⟨_, h', rfl, ?_⟩
    rw [← nullity_eq hM hkw ⟨_, h'⟩]
    exact hpos

end RoundTrip.L2.Morse_IsFocalPoint
