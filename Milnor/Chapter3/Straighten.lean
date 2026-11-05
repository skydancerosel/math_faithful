import Milnor.Chapter1.InverseFunction
import Milnor.Chapter3.Basic

/-!
Milnor, *Topology from the Differentiable Viewpoint*, §3, pp. 17–18.

# The coordinate change `h(x) = (w(x), x₂, …, xₙ)`

Both Step 1 and Step 2 of Milnor's proof use the same device. Given a smooth real function `w`
on `U` with `∂w/∂x₁ ≠ 0` at `x̄`, the map

  `h(x) = (w(x), x₂, …, xₙ)`

has nonsingular derivative at `x̄`, so by the inverse function theorem it maps a neighbourhood
`V` of `x̄` diffeomorphically onto an open set `V' ⊆ ℝ × ℝⁿ⁻¹`, and it carries the level set
`{w = 0}` into the hyperplane `0 × ℝⁿ⁻¹`. (In Step 1, `w = f₁`; in Step 2, `w` is a `k`-th partial
derivative of some component of `f`.)

Coordinate-free version: let `ℓ = dw_x̄ ≠ 0`, choose `v` with `ℓ(v) = 1`, let `K = ker ℓ`
(dimension `n - 1`), and let `P : E → K`, `P(x) = x - ℓ(x) v` be the projection along `v`. Then

  `H(x) = (w(x), P(x)) : E → ℝ × K`

has derivative `(ℓ, P)` at `x̄`, which is invertible with inverse `(t, z) ↦ z + t v`. The
inverse function theorem on manifolds (`Milnor.isLocalDiffeomorphAt_of_isInvertible_mfderiv`,
chapter 1) gives the local inverse `G`.

`Straightening U w x₀` packages exactly the data the two steps use.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

namespace Sard

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The data produced by straightening a function `w : E → ℝ` with `dw_{x₀} ≠ 0` near `x₀`:
a subspace `K` of codimension one, an open neighbourhood `V ⊆ U` of `x₀`, an open set
`V' ⊆ ℝ × K`, and mutually inverse smooth maps `H : V → V'`, `G : V' → V` with
`H(x) = (w(x), …)`. -/
structure Straightening (U : Set E) (w : E → ℝ) (x₀ : E) where
  /-- The subspace `ker dw_{x₀}`. -/
  K : Submodule ℝ E
  finrank_K : finrank ℝ K + 1 = finrank ℝ E
  V : Set E
  isOpen_V : IsOpen V
  V_subset : V ⊆ U
  mem_V : x₀ ∈ V
  V' : Set (ℝ × K)
  isOpen_V' : IsOpen V'
  H : E → ℝ × K
  G : ℝ × K → E
  H_fst : ∀ x, (H x).1 = w x
  contDiffOn_H : ContDiffOn ℝ ∞ H U
  contDiffOn_G : ContDiffOn ℝ ∞ G V'
  mapsTo_H : MapsTo H V V'
  mapsTo_G : MapsTo G V' V
  left_inv : ∀ x ∈ V, G (H x) = x
  right_inv : ∀ y ∈ V', H (G y) = y

/-- Milnor pp. 17–18: "Since `dh_x̄` is nonsingular, `h` maps some neighborhood `V` of `x̄`
diffeomorphically onto an open set `V'`." -/
theorem exists_straightening {U : Set E} (hU : IsOpen U) {w : E → ℝ} (hw : ContDiffOn ℝ ∞ w U)
    {x₀ : E} (hx₀ : x₀ ∈ U) (hℓ : fderiv ℝ w x₀ ≠ 0) :
    Nonempty (Straightening U w x₀) := by
  have := FiniteDimensional.complete ℝ E
  set ℓ := fderiv ℝ w x₀ with hℓ_def
  -- A vector `v` with `ℓ v = 1`.
  obtain ⟨u, hu⟩ : ∃ u, ℓ u ≠ 0 := by
    by_contra h
    push Not at h
    exact hℓ (ContinuousLinearMap.ext fun u => by simp [h u])
  set v : E := (ℓ u)⁻¹ • u with hv_def
  have hℓv : ℓ v = 1 := by
    simp [hv_def, inv_mul_cancel₀ hu]
  -- The kernel `K` and the projection `P`.
  set K : Submodule ℝ E := LinearMap.ker (ℓ : E →ₗ[ℝ] ℝ) with hK_def
  have hmemK : ∀ z : K, ℓ z = 0 := fun z => LinearMap.mem_ker.1 z.2
  have hPmem : ∀ x, (ContinuousLinearMap.id ℝ E - ℓ.smulRight v) x ∈ K := fun x => by
    simp [hK_def, LinearMap.mem_ker, hℓv]
  set P : E →L[ℝ] K := (ContinuousLinearMap.id ℝ E - ℓ.smulRight v).codRestrict K hPmem with hP_def
  have hP_apply : ∀ x, (P x : E) = x - ℓ x • v := fun x => by
    simp [hP_def]
  -- Dimension count: `dim K + 1 = dim E`.
  have hfinrank : finrank ℝ K + 1 = finrank ℝ E := by
    have h := LinearMap.finrank_range_add_finrank_ker (ℓ : E →ₗ[ℝ] ℝ)
    have hrange : LinearMap.range (ℓ : E →ₗ[ℝ] ℝ) = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro t
      exact ⟨t • v, by simp [hℓv]⟩
    rw [hrange, finrank_top, Module.finrank_self] at h
    rw [add_comm]
    exact h
  -- The map `H` and its derivative at `x₀`.
  set Hf : E → ℝ × K := fun x => (w x, P x) with hHf_def
  have hH_smooth : ContDiffOn ℝ ∞ Hf U := hw.prodMk P.contDiff.contDiffOn
  have hw_deriv : HasFDerivAt w ℓ x₀ :=
    ((hw.contDiffAt (hU.mem_nhds hx₀)).differentiableAt (by simp)).hasFDerivAt
  have hH_deriv : HasFDerivAt Hf (ℓ.prod P) x₀ := hw_deriv.prodMk P.hasFDerivAt
  -- The inverse of the derivative.
  let Rinv : ℝ × K →L[ℝ] E :=
    K.subtypeL.comp (ContinuousLinearMap.snd ℝ ℝ K) + (ContinuousLinearMap.fst ℝ ℝ K).smulRight v
  have hRinv : ∀ p : ℝ × K, Rinv p = (p.2 : E) + p.1 • v := fun p => by simp [Rinv]
  let e : E ≃L[ℝ] ℝ × K :=
    ContinuousLinearEquiv.equivOfInverse (ℓ.prod P) Rinv
      (fun x => by
        rw [hRinv]
        simp only [ContinuousLinearMap.prod_apply, hP_apply]
        abel)
      (fun p => by
        rw [hRinv]
        have h1 : ℓ ((p.2 : E) + p.1 • v) = p.1 := by simp [hmemK p.2, hℓv]
        have h2 : P ((p.2 : E) + p.1 • v) = p.2 := by
          apply Subtype.ext
          rw [hP_apply, h1]
          simp
        simp only [ContinuousLinearMap.prod_apply, h1, h2])
  have he : (e : E →L[ℝ] ℝ × K) = ℓ.prod P := rfl
  -- The inverse function theorem on manifolds (chapter 1).
  have hloc : IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × K) ∞ Hf x₀ := by
    refine Milnor.isLocalDiffeomorphAt_of_isInvertible_mfderiv ?_ (by simp) ?_
    · filter_upwards [hU.mem_nhds hx₀] with y hy
      rw [contMDiffAt_iff_contDiffAt]
      exact hH_smooth.contDiffAt (hU.mem_nhds hy)
    · refine ⟨e, ?_⟩
      rw [mfderiv_eq_fderiv, hH_deriv.fderiv]
      rfl
  obtain ⟨Φ, hx₀Φ, hΦ⟩ := hloc
  -- Assemble the data.
  have hleft' : ∀ x ∈ Φ.source, Φ.invFun (Φ.toPartialEquiv x) = x := fun x hx =>
    Φ.toPartialEquiv.left_inv hx
  have hV_open : IsOpen (Φ.source ∩ U) := Φ.open_source.inter hU
  have hV'_open : IsOpen (Φ.toFun '' (Φ.source ∩ U)) :=
    (Φ.toOpenPartialHomeomorph.isOpen_image_iff_of_subset_source inter_subset_left).2 hV_open
  have hG_smooth : ContDiffOn ℝ ∞ Φ.invFun (Φ.toFun '' (Φ.source ∩ U)) := by
    refine (contMDiffOn_iff_contDiffOn.1 Φ.contMDiffOn_invFun).mono ?_
    rintro _ ⟨x, hx, rfl⟩
    exact Φ.map_source hx.1
  have hmapsH : MapsTo Hf (Φ.source ∩ U) (Φ.toFun '' (Φ.source ∩ U)) := by
    intro x hx
    rw [hΦ hx.1]
    exact mem_image_of_mem _ hx
  have hmapsG : MapsTo Φ.invFun (Φ.toFun '' (Φ.source ∩ U)) (Φ.source ∩ U) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hleft' x hx.1]
    exact hx
  have hleft : ∀ x ∈ Φ.source ∩ U, Φ.invFun (Hf x) = x := by
    intro x hx
    rw [hΦ hx.1]
    exact hleft' x hx.1
  have hright : ∀ y ∈ Φ.toFun '' (Φ.source ∩ U), Hf (Φ.invFun y) = y := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hleft' x hx.1, hΦ hx.1]
  exact ⟨{ K := K
           finrank_K := hfinrank
           V := Φ.source ∩ U
           isOpen_V := hV_open
           V_subset := inter_subset_right
           mem_V := ⟨hx₀Φ, hx₀⟩
           V' := Φ.toFun '' (Φ.source ∩ U)
           isOpen_V' := hV'_open
           H := Hf
           G := Φ.invFun
           H_fst := fun _ => rfl
           contDiffOn_H := hH_smooth
           contDiffOn_G := hG_smooth
           mapsTo_H := hmapsH
           mapsTo_G := hmapsG
           left_inv := hleft
           right_inv := hright }⟩

end Sard

end Milnor
