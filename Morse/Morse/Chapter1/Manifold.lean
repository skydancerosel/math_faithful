import Morse.Chapter1.Nondegenerate
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Milnor.Chapter1.RegularValue

/-!
Milnor, *Morse Theory*, §2, pp. 4–5.

# Critical points, the Hessian and the index on a manifold

## Setting

`M` is a smooth manifold without boundary modelled on a real normed space `E`
(`[ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]`; the model `𝓘(ℝ, E)` is boundaryless), and
`f : M → ℝ`.  `E` is finite-dimensional wherever dimensions are counted.  The Euclidean theory of
`Morse/Chapter1/Nondegenerate.lean` is transported to `M` through charts.  This file is the
interface used by the later files on manifolds (the Morse lemma and the finiteness of the critical
set, `Morse/Chapter1/ManifoldMorse.lean`; functions on submanifolds of `ℝᴷ`,
`Morse/Chapter1/ManifoldSubmanifold.lean`).

## Milnor's definitions (pp. 4–5), and how they are formalized

Milnor, p. 4, paraphrased: `p ∈ M` is a *critical point* of a smooth `f : M → ℝ` if the induced
map `f_* : TM_p → TR_{f(p)}` is zero; in a local coordinate system `(x¹, …, xⁿ)` this means
`∂f/∂x¹(p) = ⋯ = ∂f/∂xⁿ(p) = 0`.  A critical point is *non-degenerate* iff the matrix
`(∂²f/∂xⁱ∂xʲ(p))` is non-singular; "it can be checked directly that non-degeneracy does not depend
on the coordinate system", which also follows from the intrinsic definition of the *Hessian*
`f_**(v, w) = ṽ_p(w̃(f))`, a symmetric bilinear functional on `TM_p` whose matrix in the basis
`∂/∂x¹|_p, …, ∂/∂xⁿ|_p` is `(∂²f/∂xⁱ∂xʲ(p))`.  The *index* of `f` at `p` is the index of `f_**`,
and `p` is non-degenerate iff `f_**` has nullity `0` (p. 5).

* **Critical point.**  `Morse.IsCriticalPointM E f p` is `mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p = 0`.  (At a
  point where `f` is not differentiable Mathlib's `mfderiv` is `0`, so such a point counts as
  critical; Milnor's `f` is smooth, so this never matters.)  This agrees with the companion
  project's critical points, the points where `df` is not surjective
  (`Morse.isCriticalPointM_iff_milnor`).
* **The local representative.**  We fix Mathlib's preferred chart at `p` and call
  `Morse.localRep E f p = f ∘ (extChartAt 𝓘(ℝ, E) p)⁻¹`, a function on (an open subset of) `E`, the
  *local representative* of `f` at `p`.  The tangent space `TangentSpace 𝓘(ℝ, E) p` is, by
  definition, `E`, identified with `TM_p` through the same chart; so `mfderiv f p` is the
  derivative of `localRep E f p` at the image of `p` (`Morse.mfderiv_eq_fderiv_localRep`).
* **The Hessian.**  `Morse.hessianM E f p` is the second derivative of the local representative at
  the image of `p`, a continuous bilinear form on `TangentSpace 𝓘(ℝ, E) p = E`.  With the constant
  extensions `ṽ = v`, `w̃ = w` in the preferred chart, Milnor's `ṽ_p(w̃(f))` is exactly this second
  derivative (see the module docstring of `Morse/Chapter1/Nondegenerate.lean`).  Like
  `Morse.hessian`, `Morse.hessianM E f p` is defined at every point, but it is only meaningful at
  critical points, the only points where it does not depend on the chart.
* `Morse.IsNondegenerateCriticalPointM`, `Morse.indexM`, `Morse.nullityM`: Milnor's non-degenerate
  critical point, index and nullity.
* `Morse.IsMorseFunction E f`: `f` is smooth and all its critical points are non-degenerate
  (Milnor's "differentiable function with no degenerate critical points", §3 and §6).

**The model space is an explicit argument** (`IsCriticalPointM E f p`, `hessianM E f p`, …):
Mathlib's `ChartedSpace E M` does not determine `E` from `M`, just as `mfderiv I I' f p` takes
the models explicitly.

## Independence of the coordinate system

Milnor gives no argument for the independence of the coordinates.  In this formalization `f_**` is
*defined* in one chart, so its well-definedness *is* the chart independence; the check is the
transformation rule of second derivatives at a critical point, `Morse.hessian_comp`, applied to
the transition map between two coordinate systems, whose derivative is invertible.  A coordinate
system here is any `y : OpenPartialHomeomorph M E'` which is smooth on its source with smooth
inverse on its target (`Morse.IsSmoothCoord`); for `E' = E` these are exactly the charts of the
maximal smooth atlas (`Morse.isSmoothCoord_iff_mem_maximalAtlas`), but `E'` may be any real
normed space, for instance `ℝⁿ = Fin n → ℝ` as in Milnor's statement of the Morse lemma.  Main
results:

* `Morse.IsSmoothCoord.isCriticalPointM_iff`: `p` is critical iff `y p` is a critical point of the
  representative `f ∘ y⁻¹`; for `y` with values in `ℝⁿ`, this is Milnor's definition,
  `∂f/∂y¹(p) = ⋯ = ∂f/∂yⁿ(p) = 0` (`Morse.IsSmoothCoord.isCriticalPointM_iff_forall_partial`);
* `Morse.IsSmoothCoord.hessian_comp_symm`: at a critical point the Hessian of `f ∘ y⁻¹` at `y p` is
  `f_**` pulled back by the derivative of the parametrization `y⁻¹`; in Milnor's words, the matrix
  `(∂²f/∂yⁱ∂yʲ(p))` represents `f_**` in the basis `∂/∂y¹|_p, …, ∂/∂yⁿ|_p`;
* `Morse.IsSmoothCoord.isNondegenerate_iff`, `Morse.IsSmoothCoord.index_eq`,
  `Morse.IsSmoothCoord.nullity_eq`, `Morse.IsSmoothCoord.isNondegenerateCriticalPointM_iff`:
  non-degeneracy, index and nullity can be computed in any coordinate system; for `y` with values
  in `ℝⁿ`, non-degeneracy is Milnor's definition, `det (∂²f/∂yⁱ∂yʲ(p)) ≠ 0`
  (`Morse.IsSmoothCoord.isNondegenerate_iff_det_ne_zero`);
* the same for the charts of the maximal atlas: `Morse.isCriticalPointM_iff_of_mem_maximalAtlas`,
  `Morse.hessian_comp_symm_of_mem_maximalAtlas`, `Morse.isNondegenerate_iff_of_mem_maximalAtlas`,
  `Morse.indexM_eq_of_mem_maximalAtlas`, `Morse.nullityM_eq_of_mem_maximalAtlas`;
* two arbitrary coordinate systems compared with each other: `Morse.IsSmoothCoord.hessian_trans`,
  `Morse.IsSmoothCoord.isNondegenerate_trans_iff`, `Morse.IsSmoothCoord.index_trans_eq`,
  `Morse.IsSmoothCoord.nullity_trans_eq`.

## What Milnor leaves implicit

* **Smoothness of the transition maps, and invertibility of their derivatives.**  A transition map
  `z ∘ y⁻¹` between two coordinate systems is smooth on the open set where it is defined
  (`Morse.IsSmoothCoord.contDiffOn_trans`), and its derivative is a linear isomorphism, the inverse
  being the derivative of `y ∘ z⁻¹` (`Morse.IsSmoothCoord.exists_fderiv_trans_eq`); likewise the
  derivatives of `y` and of `y⁻¹` are isomorphisms between `TM_p` and `E'`
  (`Morse.IsSmoothCoord.exists_mfderiv_eq`, `Morse.IsSmoothCoord.exists_mfderiv_symm_eq`).
* **Nullity under a change of variables** (`Morse.nullity_bilinearComp`), which Milnor uses when
  he says that `p` is non-degenerate iff `f_**` has nullity `0` "obviously".
* **Only `C²` is used.**  All statements about the Hessian assume only that `f` is `C²` at `p`
  (`ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 f p`).
* **The second-order chain rule away from critical points** (`Morse.hessian_comp_apply`), which
  Milnor uses without comment in §6 (p. 36) to compute the Hessian of `L_p` on a submanifold.

## Not done here

Milnor's remark on p. 4 that, for a regular value `a`, `M^a = f⁻¹(-∞, a]` is a smooth manifold
with boundary `f⁻¹(a)` ("it follows from the implicit function theorem") is not restated here: it
is the companion project's `Milnor.isHalfSliceSubmanifold_of_regularValue`, applied to `a − f`.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold

noncomputable section

namespace Morse

/-! ### A lemma of calculus: local inverses have invertible derivatives -/

section Calculus

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- If `ψ` and `χ` are inverse to each other near `a` and `ψ a`, and differentiable there, then
`dψ_a` is a continuous linear isomorphism with inverse `dχ_{ψ a}`. -/
theorem exists_fderiv_eq_of_localInverse {ψ : E₁ → E₂} {χ : E₂ → E₁} {a : E₁}
    (hψ : DifferentiableAt ℝ ψ a) (hχ : DifferentiableAt ℝ χ (ψ a))
    (h₁ : ∀ᶠ u in 𝓝 a, χ (ψ u) = u) (h₂ : ∀ᶠ w in 𝓝 (ψ a), ψ (χ w) = w) :
    ∃ L : E₁ ≃L[ℝ] E₂, fderiv ℝ ψ a = L ∧ fderiv ℝ χ (ψ a) = L.symm := by
  have hχψa : χ (ψ a) = a := h₁.self_of_nhds
  have hψ' : DifferentiableAt ℝ ψ (χ (ψ a)) := by rwa [hχψa]
  have hLM : (fderiv ℝ χ (ψ a)).comp (fderiv ℝ ψ a) = ContinuousLinearMap.id ℝ E₁ := by
    have h1 : fderiv ℝ (χ ∘ ψ) a = (fderiv ℝ χ (ψ a)).comp (fderiv ℝ ψ a) := fderiv_comp a hχ hψ
    have h2 : fderiv ℝ (χ ∘ ψ) a = ContinuousLinearMap.id ℝ E₁ := by
      have hev : (χ ∘ ψ) =ᶠ[𝓝 a] id := h₁
      rw [hev.fderiv_eq, fderiv_id]
    rw [← h1, h2]
  have hML : (fderiv ℝ ψ a).comp (fderiv ℝ χ (ψ a)) = ContinuousLinearMap.id ℝ E₂ := by
    have h1 : fderiv ℝ (ψ ∘ χ) (ψ a) = (fderiv ℝ ψ (χ (ψ a))).comp (fderiv ℝ χ (ψ a)) :=
      fderiv_comp (ψ a) hψ' hχ
    have h2 : fderiv ℝ (ψ ∘ χ) (ψ a) = ContinuousLinearMap.id ℝ E₂ := by
      have hev : (ψ ∘ χ) =ᶠ[𝓝 (ψ a)] id := h₂
      rw [hev.fderiv_eq, fderiv_id]
    rw [← h2, h1, hχψa]
  refine ⟨ContinuousLinearEquiv.equivOfInverse (fderiv ℝ ψ a) (fderiv ℝ χ (ψ a))
    (fun v => by simpa using congrArg (fun T => T v) hLM)
    (fun w => by simpa using congrArg (fun T => T w) hML), rfl, rfl⟩

/-- **The second-order chain rule.**  If `ψ` is `C²` at `q` and `f` is `C²` at `ψ q`, then
`d²(f ∘ ψ)_q(v, w) = d²f_{ψ q}(dψ_q v, dψ_q w) + df_{ψ q}(d²ψ_q(v, w))`.  At a critical point of
`f` the second term vanishes (`Morse.hessian_comp`); in general it does not, and Milnor's
computation of the Hessian of `L_p(x) = ‖x − p‖²` on a submanifold (§6, p. 36) is this formula with
`ψ` a local parametrization. -/
theorem hessian_comp_apply {f : E₂ → ℝ} {ψ : E₁ → E₂} {q : E₁} (hf : ContDiffAt ℝ 2 f (ψ q))
    (hψ : ContDiffAt ℝ 2 ψ q) (v w : E₁) :
    hessian (f ∘ ψ) q v w = hessian f (ψ q) (fderiv ℝ ψ q v) (fderiv ℝ ψ q w) +
      fderiv ℝ f (ψ q) (fderiv ℝ (fderiv ℝ ψ) q v w) := by
  have hψev : ∀ᶠ x in 𝓝 q, ContDiffAt ℝ 2 ψ x := hψ.eventually (by simp)
  have hfev : ∀ᶠ x in 𝓝 q, ContDiffAt ℝ 2 f (ψ x) :=
    hψ.continuousAt.tendsto.eventually (hf.eventually (by simp))
  have heq : fderiv ℝ (f ∘ ψ) =ᶠ[𝓝 q] fun x => (fderiv ℝ f (ψ x)).comp (fderiv ℝ ψ x) := by
    filter_upwards [hψev, hfev] with x hx1 hx2
    exact fderiv_comp x (hx2.differentiableAt (by simp)) (hx1.differentiableAt (by simp))
  have h1 : HasFDerivAt (fderiv ℝ f) (hessian f (ψ q)) (ψ q) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have h2 : HasFDerivAt ψ (fderiv ℝ ψ q) q := (hψ.differentiableAt (by simp)).hasFDerivAt
  have h3 : HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) q) q :=
    ((hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have h4 : HasFDerivAt (fun x => (fderiv ℝ f (ψ x)).comp (fderiv ℝ ψ x)) _ q :=
    (h1.comp q h2).clm_comp h3
  rw [hessian, heq.fderiv_eq, h4.fderiv]
  simp only [add_apply, ContinuousLinearMap.coe_comp, comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
  ring

end Calculus

/-! ### Null spaces and nullity under a linear change of variables -/

section Nullity

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- The null space of the pull-back `H(L ·, L ·)` is the preimage of the null space of `H`. -/
theorem nullSpace_bilinearComp (H : E₂ →L[ℝ] E₂ →L[ℝ] ℝ) (L : E₁ ≃L[ℝ] E₂) :
    nullSpace (H.bilinearComp (L : E₁ →L[ℝ] E₂) (L : E₁ →L[ℝ] E₂)) =
      (nullSpace H).comap (L : E₁ →ₗ[ℝ] E₂) := by
  ext v
  simp only [mem_nullSpace, Submodule.mem_comap, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearEquiv.coe_coe, LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv]
  constructor
  · intro h w
    simpa using h (L.symm w)
  · intro h w
    exact h (L w)

/-- The nullity is invariant under a linear change of variables. -/
theorem nullity_bilinearComp (H : E₂ →L[ℝ] E₂ →L[ℝ] ℝ) (L : E₁ ≃L[ℝ] E₂) :
    nullity (H.bilinearComp (L : E₁ →L[ℝ] E₂) (L : E₁ →L[ℝ] E₂)) = nullity H := by
  rw [nullity, nullSpace_bilinearComp, nullity,
    Submodule.comap_equiv_eq_map_symm (L.toLinearEquiv : E₁ ≃ₗ[ℝ] E₂)]
  exact LinearEquiv.finrank_map_eq _ _

/-- The index of a bilinear form is at most the dimension. -/
theorem index_le_finrank (H : E₁ →L[ℝ] E₁ →L[ℝ] ℝ) : index H ≤ finrank ℝ E₁ :=
  sigPos_le_finrank _

end Nullity

/-! ### Definitions

The model space `E` is an explicit argument of all definitions: Mathlib's `ChartedSpace E M` does
not determine `E` from `M` (it is not an `outParam`), just as `mfderiv I I' f x` takes the models
explicitly. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

section Defs

variable (E)

/-- **The local representative** of `f : M → ℝ` at `p`: `f` read in the preferred chart at `p`,
`f ∘ (extChartAt 𝓘(ℝ, E) p)⁻¹`, a function on `E` which is meaningful on the target of the chart
(an open neighbourhood of `extChartAt 𝓘(ℝ, E) p p`). -/
def localRep (f : M → ℝ) (p : M) : E → ℝ :=
  f ∘ (extChartAt 𝓘(ℝ, E) p).symm

/-- **Critical point** (Milnor, p. 4): `p` is a critical point of `f` if `f_* : TM_p → TR_{f(p)}`
is zero. -/
def IsCriticalPointM (f : M → ℝ) (p : M) : Prop :=
  mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p = 0

/-- **The Hessian** `f_**` of `f` at `p` (Milnor, pp. 4–5), as a continuous bilinear form on
`TM_p = TangentSpace 𝓘(ℝ, E) p = E`: the second derivative of the local representative
`Morse.localRep E f p` at the image of `p` in the preferred chart.  It is chart independent at
critical points (`Morse.IsSmoothCoord.hessian_comp_symm`). -/
def hessianM (f : M → ℝ) (p : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  hessian (localRep E f p) (extChartAt 𝓘(ℝ, E) p p)

/-- **Non-degenerate critical point** (Milnor, p. 4). -/
def IsNondegenerateCriticalPointM (f : M → ℝ) (p : M) : Prop :=
  IsCriticalPointM E f p ∧ IsNondegenerate (hessianM E f p)

/-- **The index of `f` at `p`** (Milnor, p. 5): the index of the Hessian `f_**` on `TM_p`. -/
def indexM (f : M → ℝ) (p : M) : ℕ :=
  index (hessianM E f p)

/-- **The nullity of `f` at `p`** (Milnor, p. 5): the nullity of the Hessian `f_**` on `TM_p`. -/
def nullityM (f : M → ℝ) (p : M) : ℕ :=
  nullity (hessianM E f p)

/-- **Morse function**: a smooth function all of whose critical points are non-degenerate
(Milnor's "differentiable function with no degenerate critical points", §3, §6). -/
structure IsMorseFunction (f : M → ℝ) : Prop where
  contMDiff : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f
  isNondegenerate : ∀ p, IsCriticalPointM E f p → IsNondegenerate (hessianM E f p)

end Defs

theorem IsMorseFunction.isNondegenerateCriticalPointM {f : M → ℝ} (hf : IsMorseFunction E f)
    {p : M} (hp : IsCriticalPointM E f p) : IsNondegenerateCriticalPointM E f p :=
  ⟨hp, hf.isNondegenerate p hp⟩

/-! ### The local representative -/

section LocalRep

theorem extChartAt_self_coe (p : M) : ⇑(extChartAt 𝓘(ℝ, E) p) = ⇑(chartAt E p) := by
  rw [extChartAt_coe]
  rfl

theorem extChartAt_self_coe_symm (p : M) :
    ⇑(extChartAt 𝓘(ℝ, E) p).symm = ⇑(chartAt E p).symm := by
  rw [extChartAt_coe_symm]
  rfl

theorem extChartAt_self_target (p : M) :
    (extChartAt 𝓘(ℝ, E) p).target = (chartAt E p).target := by
  simp

theorem localRep_eq (f : M → ℝ) (p : M) : localRep E f p = f ∘ (chartAt E p).symm := by
  rw [localRep, extChartAt_self_coe_symm]

@[simp] theorem localRep_apply (f : M → ℝ) (p : M) (u : E) :
    localRep E f p u = f ((chartAt E p).symm u) := by
  rw [localRep_eq]
  rfl

theorem localRep_chartAt (f : M → ℝ) {p x : M} (hx : x ∈ (chartAt E p).source) :
    localRep E f p (chartAt E p x) = f x := by
  rw [localRep_apply, (chartAt E p).left_inv hx]

theorem localRep_self (f : M → ℝ) (p : M) : localRep E f p (extChartAt 𝓘(ℝ, E) p p) = f p := by
  rw [extChartAt_self_coe]
  exact localRep_chartAt f (mem_chart_source E p)

theorem writtenInExtChartAt_eq_localRep (f : M → ℝ) (p : M) :
    writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) p f = localRep E f p := by
  funext u
  simp [writtenInExtChartAt, chartAt_self_eq]

/-- Near `p`, `f` is its local representative read through the chart. -/
theorem eventuallyEq_localRep_comp (f : M → ℝ) (p : M) :
    f =ᶠ[𝓝 p] localRep E f p ∘ extChartAt 𝓘(ℝ, E) p := by
  filter_upwards [(chartAt E p).open_source.mem_nhds (mem_chart_source E p)] with x hx
  rw [comp_apply, extChartAt_self_coe, localRep_chartAt f hx]

/-- `f` is differentiable at `p` iff its local representative is differentiable at the image of
`p`. -/
theorem mdifferentiableAt_iff_differentiableAt_localRep {f : M → ℝ} {p : M} :
    MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p ↔
      DifferentiableAt ℝ (localRep E f p) (extChartAt 𝓘(ℝ, E) p p) := by
  rw [mdifferentiableAt_iff, writtenInExtChartAt_eq_localRep, modelWithCornersSelf_coe,
    range_id, differentiableWithinAt_univ]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  have hc : ContinuousAt (localRep E f p ∘ extChartAt 𝓘(ℝ, E) p) p :=
    ContinuousAt.comp (f := extChartAt 𝓘(ℝ, E) p) h.continuousAt (continuousAt_extChartAt p)
  exact hc.congr (eventuallyEq_localRep_comp f p).symm

/-- `f` is `Cⁿ` at `p` iff its local representative is `Cⁿ` at the image of `p`. -/
theorem contMDiffAt_iff_contDiffAt_localRep {f : M → ℝ} {p : M} {n : WithTop ℕ∞} :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) n f p ↔
      ContDiffAt ℝ n (localRep E f p) (extChartAt 𝓘(ℝ, E) p p) := by
  rw [contMDiffAt_iff]
  have hw : (extChartAt 𝓘(ℝ, ℝ) (f p) ∘ f ∘ (extChartAt 𝓘(ℝ, E) p).symm) = localRep E f p :=
    writtenInExtChartAt_eq_localRep f p
  rw [hw, modelWithCornersSelf_coe, range_id, contDiffWithinAt_univ]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  have hc : ContinuousAt (localRep E f p ∘ extChartAt 𝓘(ℝ, E) p) p :=
    ContinuousAt.comp (f := extChartAt 𝓘(ℝ, E) p) h.continuousAt (continuousAt_extChartAt p)
  exact hc.congr (eventuallyEq_localRep_comp f p).symm

/-- **The derivative of `f` at `p` is the derivative of its local representative** (the
identification `TM_p = E` being the one given by the preferred chart).  No differentiability
hypothesis is needed: both sides vanish when `f` is not differentiable at `p`. -/
theorem mfderiv_eq_fderiv_localRep (f : M → ℝ) (p : M) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p = fderiv ℝ (localRep E f p) (extChartAt 𝓘(ℝ, E) p p) := by
  by_cases h : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p
  · rw [h.mfderiv, writtenInExtChartAt_eq_localRep, modelWithCornersSelf_coe, range_id,
      fderivWithin_univ]
  · rw [mfderiv_zero_of_not_mdifferentiableAt h, fderiv_zero_of_not_differentiableAt
      (fun h' => h (mdifferentiableAt_iff_differentiableAt_localRep.2 h'))]
    rfl

end LocalRep

/-! ### Critical points -/

section Critical

theorem isCriticalPointM_iff_fderiv {f : M → ℝ} {p : M} :
    IsCriticalPointM E f p ↔ fderiv ℝ (localRep E f p) (extChartAt 𝓘(ℝ, E) p p) = 0 := by
  rw [IsCriticalPointM, mfderiv_eq_fderiv_localRep]
  exact Iff.rfl

/-- For `f` differentiable at `p`: `p` is a critical point of `f` iff the image of `p` is a
critical point of the local representative. -/
theorem isCriticalPointM_iff {f : M → ℝ} {p : M} (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p) :
    IsCriticalPointM E f p ↔ IsCriticalPoint (localRep E f p) (extChartAt 𝓘(ℝ, E) p p) := by
  rw [isCriticalPointM_iff_fderiv,
    isCriticalPoint_iff (mdifferentiableAt_iff_differentiableAt_localRep.1 hf)]

theorem isCriticalPointM_iff_hasMFDerivAt {f : M → ℝ} {p : M}
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p) :
    IsCriticalPointM E f p ↔ HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p 0 :=
  ⟨fun h => h ▸ hf.hasMFDerivAt, fun h => h.mfderiv⟩

/-- A linear functional is surjective iff it is nonzero. -/
theorem surjective_iff_ne_zero {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    (ℓ : V →L[ℝ] ℝ) : Surjective ℓ ↔ ℓ ≠ 0 := by
  constructor
  · intro h h0
    obtain ⟨v, hv⟩ := h 1
    rw [h0] at hv
    simp at hv
  · intro h t
    obtain ⟨v, hv⟩ : ∃ v, ℓ v ≠ 0 := by
      by_contra hcon
      exact h (ContinuousLinearMap.ext fun v => by_contra fun hv => hcon ⟨v, hv⟩)
    refine ⟨(t / ℓ v) • v, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]

/-- **Agreement with the companion project**: `p` is a critical point in Milnor's sense (`f_* = 0`)
iff it is a critical point in the sense of *Topology from the Differentiable Viewpoint*
(`df_p` not surjective), `Milnor.IsCriticalPoint`. -/
theorem isCriticalPointM_iff_milnor {f : M → ℝ} {p : M} :
    IsCriticalPointM E f p ↔ Milnor.IsCriticalPoint 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p := by
  rw [Milnor.IsCriticalPoint, Milnor.IsRegularPoint, IsCriticalPointM]
  have h := surjective_iff_ne_zero (V := E) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p)
  constructor
  · intro h0 hs
    exact (h.1 hs) h0
  · intro hns
    by_contra h0
    exact hns (h.2 h0)

end Critical

/-! ### The Hessian -/

section Hessian

/-- The Hessian is symmetric wherever `f` is `C²`. -/
theorem hessianM_symm {f : M → ℝ} {p : M} (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 f p) (v w : E) :
    hessianM E f p v w = hessianM E f p w v :=
  hessian_symm (contMDiffAt_iff_contDiffAt_localRep.1 hf) v w

/-- The index of `f` at `p` is at most the dimension of `M`. -/
theorem indexM_le_finrank (f : M → ℝ) (p : M) : indexM E f p ≤ finrank ℝ E :=
  index_le_finrank _

theorem isNondegenerate_hessianM_iff_nullityM_eq_zero [FiniteDimensional ℝ E] {f : M → ℝ}
    {p : M} : IsNondegenerate (hessianM E f p) ↔ nullityM E f p = 0 :=
  isNondegenerate_iff_nullity_eq_zero

/-- On the model space itself (`M = E`, with its standard chart), the local representative of `f`
is `f`. -/
theorem localRep_model (f : E → ℝ) (p : E) : localRep E f p = f := by
  funext u
  simp [localRep, chartAt_self_eq]

theorem extChartAt_model_apply (p : E) : extChartAt 𝓘(ℝ, E) p p = p := by
  simp [chartAt_self_eq]

/-- On the model space itself, the manifold notions are the Euclidean ones. -/
theorem hessianM_model (f : E → ℝ) (p : E) : hessianM E f p = hessian f p := by
  rw [hessianM, localRep_model, extChartAt_model_apply]

theorem isCriticalPointM_model_iff {f : E → ℝ} {p : E} (hf : DifferentiableAt ℝ f p) :
    IsCriticalPointM E f p ↔ IsCriticalPoint f p := by
  rw [isCriticalPointM_iff_fderiv, localRep_model, isCriticalPoint_iff hf,
    extChartAt_model_apply]

theorem indexM_model (f : E → ℝ) (p : E) : indexM E f p = index (hessian f p) := by
  rw [indexM, hessianM_model]

end Hessian

/-! ### Smooth coordinate systems -/

section Coord

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']

variable (E) in
/-- **A smooth (local) coordinate system** on `M` with values in a real normed space `E'`: an open
partial homeomorphism `y` from `M` to `E'` which is smooth on its source and whose inverse is
smooth on its target.  (Milnor's "local coordinate system" `(y¹, …, yⁿ)`, with `E' = ℝⁿ`.)  For
`E' = E` these are exactly the charts of the maximal atlas
(`Morse.isSmoothCoord_iff_mem_maximalAtlas`). -/
structure IsSmoothCoord (y : OpenPartialHomeomorph M E') : Prop where
  contMDiffOn : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E') ∞ y y.source
  contMDiffOn_symm : ContMDiffOn 𝓘(ℝ, E') 𝓘(ℝ, E) ∞ y.symm y.target

/-- A smooth coordinate system is a partial diffeomorphism from `M` onto an open subset of `E'`
(Mathlib's `PartialDiffeomorph`, used for the slice charts of the companion project). -/
def IsSmoothCoord.toPartialDiffeomorph {y : OpenPartialHomeomorph M E'} (hy : IsSmoothCoord E y) :
    PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E') M E' ∞ where
  toPartialEquiv := y.toPartialEquiv
  open_source := y.open_source
  open_target := y.open_target
  contMDiffOn_toFun := hy.contMDiffOn
  contMDiffOn_invFun := hy.contMDiffOn_symm

@[simp] theorem IsSmoothCoord.toPartialDiffeomorph_coe {y : OpenPartialHomeomorph M E'}
    (hy : IsSmoothCoord E y) : ⇑hy.toPartialDiffeomorph = ⇑y := rfl

/-- Conversely, a partial diffeomorphism from `M` onto an open subset of a normed space is a smooth
coordinate system. -/
theorem isSmoothCoord_toOpenPartialHomeomorph
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E') M E' ∞) :
    IsSmoothCoord E Φ.toOpenPartialHomeomorph :=
  ⟨Φ.contMDiffOn_toFun, Φ.contMDiffOn_invFun⟩

section Atlas

variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The smooth coordinate systems with values in the model space `E` are exactly the charts of
the maximal smooth atlas of `M`. -/
theorem isSmoothCoord_iff_mem_maximalAtlas (y : OpenPartialHomeomorph M E) :
    IsSmoothCoord E y ↔ y ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := by
  rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

theorem isSmoothCoord_of_mem_maximalAtlas {y : OpenPartialHomeomorph M E}
    (hy : y ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) : IsSmoothCoord E y :=
  (isSmoothCoord_iff_mem_maximalAtlas y).2 hy

/-- The preferred chart at `p` is a smooth coordinate system. -/
theorem isSmoothCoord_chartAt (p : M) : IsSmoothCoord E (chartAt E p) :=
  isSmoothCoord_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p)

end Atlas

namespace IsSmoothCoord

variable {y : OpenPartialHomeomorph M E'} {z : OpenPartialHomeomorph M E''} {p : M}

/-- **A smooth coordinate system followed by a diffeomorphism of open subsets of the model
spaces** is a smooth coordinate system. -/
theorem trans (hy : IsSmoothCoord E y) {φ : OpenPartialHomeomorph E' E''}
    (hφ : ContDiffOn ℝ ∞ φ φ.source) (hφs : ContDiffOn ℝ ∞ φ.symm φ.target) :
    IsSmoothCoord E (y.trans φ) := by
  refine ⟨?_, ?_⟩
  · rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.coe_trans]
    exact (contMDiffOn_iff_contDiffOn.2 hφ).comp (hy.contMDiffOn.mono inter_subset_left)
      fun x hx => hx.2
  · rw [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.coe_trans_symm]
    exact hy.contMDiffOn_symm.comp ((contMDiffOn_iff_contDiffOn.2 hφs).mono inter_subset_left)
      fun x hx => hx.2

omit [NormedSpace ℝ E'] [NormedSpace ℝ E''] in
/-- The domain `y(y.source ∩ z.source)` of the transition map `z ∘ y⁻¹` is open. -/
theorem isOpen_trans_source (y : OpenPartialHomeomorph M E') (z : OpenPartialHomeomorph M E'') :
    IsOpen (y.target ∩ y.symm ⁻¹' z.source) :=
  y.isOpen_inter_preimage_symm z.open_source

omit [NormedSpace ℝ E'] [NormedSpace ℝ E''] in
theorem mem_trans_source (hp : p ∈ y.source) (hpz : p ∈ z.source) :
    y p ∈ y.target ∩ y.symm ⁻¹' z.source :=
  ⟨y.map_source hp, by rw [mem_preimage, y.left_inv hp]; exact hpz⟩

/-- **Transition maps are smooth** on their (open) domain. -/
theorem contDiffOn_trans (hy : IsSmoothCoord E y) (hz : IsSmoothCoord E z) :
    ContDiffOn ℝ ∞ (z ∘ y.symm) (y.target ∩ y.symm ⁻¹' z.source) := by
  rw [← contMDiffOn_iff_contDiffOn]
  exact hz.contMDiffOn.comp (hy.contMDiffOn_symm.mono inter_subset_left) fun u hu => hu.2

theorem contDiffAt_trans (hy : IsSmoothCoord E y) (hz : IsSmoothCoord E z) (hp : p ∈ y.source)
    (hpz : p ∈ z.source) : ContDiffAt ℝ ∞ (z ∘ y.symm) (y p) :=
  (hy.contDiffOn_trans hz).contDiffAt
    ((isOpen_trans_source y z).mem_nhds (mem_trans_source hp hpz))

omit [NormedSpace ℝ E'] [NormedSpace ℝ E''] in
theorem trans_apply_self (hp : p ∈ y.source) : (z ∘ y.symm) (y p) = z p := by
  rw [comp_apply, y.left_inv hp]

/-- **Transition maps have invertible derivatives**: the derivative at `y p` of `z ∘ y⁻¹` is a
linear isomorphism, with inverse the derivative of `y ∘ z⁻¹` at `z p`. -/
theorem exists_fderiv_trans_eq (hy : IsSmoothCoord E y) (hz : IsSmoothCoord E z)
    (hp : p ∈ y.source) (hpz : p ∈ z.source) :
    ∃ L : E' ≃L[ℝ] E'', fderiv ℝ (z ∘ y.symm) (y p) = L := by
  have hψ : DifferentiableAt ℝ (z ∘ y.symm) (y p) :=
    (hy.contDiffAt_trans hz hp hpz).differentiableAt (by simp)
  have hχ : DifferentiableAt ℝ (y ∘ z.symm) ((z ∘ y.symm) (y p)) := by
    rw [trans_apply_self hp]
    exact (hz.contDiffAt_trans hy hpz hp).differentiableAt (by simp)
  have h₁ : ∀ᶠ u in 𝓝 (y p), (y ∘ z.symm) ((z ∘ y.symm) u) = u := by
    filter_upwards [(isOpen_trans_source y z).mem_nhds (mem_trans_source hp hpz)] with u hu
    simp only [comp_apply]
    rw [z.left_inv hu.2, y.right_inv hu.1]
  have h₂ : ∀ᶠ w in 𝓝 ((z ∘ y.symm) (y p)), (z ∘ y.symm) ((y ∘ z.symm) w) = w := by
    rw [trans_apply_self hp]
    filter_upwards [(isOpen_trans_source z y).mem_nhds (mem_trans_source hpz hp)] with w hw
    simp only [comp_apply]
    rw [y.left_inv hw.2, z.right_inv hw.1]
  obtain ⟨L, hL, -⟩ := exists_fderiv_eq_of_localInverse hψ hχ h₁ h₂
  exact ⟨L, hL⟩

omit [NormedSpace ℝ E'] [NormedSpace ℝ E''] in
/-- Near `y p`, `f` read in the coordinates `y` is `f` read in the coordinates `z`, composed with
the transition map. -/
theorem comp_symm_eventuallyEq (hp : p ∈ y.source) (hpz : p ∈ z.source) (f : M → ℝ) :
    f ∘ y.symm =ᶠ[𝓝 (y p)] (f ∘ z.symm) ∘ (z ∘ y.symm) := by
  filter_upwards [(isOpen_trans_source y z).mem_nhds (mem_trans_source hp hpz)] with u hu
  simp only [comp_apply]
  rw [z.left_inv hu.2]

/-- **Critical points do not depend on the coordinate system** (comparison of two coordinate
systems). -/
theorem isCriticalPoint_trans_iff (hy : IsSmoothCoord E y) (hz : IsSmoothCoord E z)
    (hp : p ∈ y.source) (hpz : p ∈ z.source) {f : M → ℝ}
    (hf : DifferentiableAt ℝ (f ∘ z.symm) (z p)) :
    IsCriticalPoint (f ∘ y.symm) (y p) ↔ IsCriticalPoint (f ∘ z.symm) (z p) := by
  obtain ⟨L, hL⟩ := hy.exists_fderiv_trans_eq hz hp hpz
  have hψ : HasFDerivAt (z ∘ y.symm) (L : E' →L[ℝ] E'') (y p) := by
    rw [← hL]
    exact ((hy.contDiffAt_trans hz hp hpz).differentiableAt (by simp)).hasFDerivAt
  have hf' : HasFDerivAt (f ∘ z.symm) (fderiv ℝ (f ∘ z.symm) ((z ∘ y.symm) (y p)))
      ((z ∘ y.symm) (y p)) := by
    rw [trans_apply_self hp]
    exact hf.hasFDerivAt
  have hcomp : HasFDerivAt (f ∘ y.symm)
      ((fderiv ℝ (f ∘ z.symm) (z p)).comp (L : E' →L[ℝ] E'')) (y p) := by
    have := (hf'.comp (y p) hψ).congr_of_eventuallyEq (comp_symm_eventuallyEq hp hpz f)
    rwa [trans_apply_self hp] at this
  rw [isCriticalPoint_iff hcomp.differentiableAt, isCriticalPoint_iff hf, hcomp.fderiv]
  constructor
  · intro h
    ext v
    have := congrArg (fun T : E' →L[ℝ] ℝ => T (L.symm v)) h
    simpa using this
  · intro h
    rw [h, ContinuousLinearMap.zero_comp]

/-- **The Hessian at a critical point transforms as a bilinear form under a change of
coordinates.** -/
theorem hessian_trans (hy : IsSmoothCoord E y) (hz : IsSmoothCoord E z) (hp : p ∈ y.source)
    (hpz : p ∈ z.source) {f : M → ℝ} (hf : ContDiffAt ℝ 2 (f ∘ z.symm) (z p))
    (hcrit : fderiv ℝ (f ∘ z.symm) (z p) = 0) (v w : E') :
    hessian (f ∘ y.symm) (y p) v w = hessian (f ∘ z.symm) (z p)
      (fderiv ℝ (z ∘ y.symm) (y p) v) (fderiv ℝ (z ∘ y.symm) (y p) w) := by
  rw [hessian_congr (comp_symm_eventuallyEq hp hpz f)]
  have hf' : ContDiffAt ℝ 2 (f ∘ z.symm) ((z ∘ y.symm) (y p)) := by
    rwa [trans_apply_self hp]
  have hcrit' : fderiv ℝ (f ∘ z.symm) ((z ∘ y.symm) (y p)) = 0 := by
    rwa [trans_apply_self hp]
  rw [hessian_comp hf' ((hy.contDiffAt_trans hz hp hpz).of_le (by norm_cast)) hcrit',
    trans_apply_self hp]

/-- The Hessian in the coordinates `y` is the pull-back of the Hessian in the coordinates `z` by
the derivative of the transition map. -/
theorem exists_hessian_trans_eq_bilinearComp (hy : IsSmoothCoord E y) (hz : IsSmoothCoord E z)
    (hp : p ∈ y.source) (hpz : p ∈ z.source) {f : M → ℝ}
    (hf : ContDiffAt ℝ 2 (f ∘ z.symm) (z p)) (hcrit : fderiv ℝ (f ∘ z.symm) (z p) = 0) :
    ∃ L : E' ≃L[ℝ] E'', hessian (f ∘ y.symm) (y p) =
      (hessian (f ∘ z.symm) (z p)).bilinearComp (L : E' →L[ℝ] E'') (L : E' →L[ℝ] E'') := by
  obtain ⟨L, hL⟩ := hy.exists_fderiv_trans_eq hz hp hpz
  refine ⟨L, ?_⟩
  ext v w
  rw [hy.hessian_trans hz hp hpz hf hcrit, hL]
  rfl

/-- **Non-degeneracy does not depend on the coordinate system** (Milnor, p. 4). -/
theorem isNondegenerate_trans_iff (hy : IsSmoothCoord E y) (hz : IsSmoothCoord E z)
    (hp : p ∈ y.source) (hpz : p ∈ z.source) {f : M → ℝ}
    (hf : ContDiffAt ℝ 2 (f ∘ z.symm) (z p)) (hcrit : fderiv ℝ (f ∘ z.symm) (z p) = 0) :
    IsNondegenerate (hessian (f ∘ y.symm) (y p)) ↔
      IsNondegenerate (hessian (f ∘ z.symm) (z p)) := by
  obtain ⟨L, hL⟩ := hy.exists_hessian_trans_eq_bilinearComp hz hp hpz hf hcrit
  rw [hL, isNondegenerate_bilinearComp_iff]

/-- **The index does not depend on the coordinate system.** -/
theorem index_trans_eq (hy : IsSmoothCoord E y) (hz : IsSmoothCoord E z)
    (hp : p ∈ y.source) (hpz : p ∈ z.source) {f : M → ℝ}
    (hf : ContDiffAt ℝ 2 (f ∘ z.symm) (z p)) (hcrit : fderiv ℝ (f ∘ z.symm) (z p) = 0) :
    index (hessian (f ∘ y.symm) (y p)) = index (hessian (f ∘ z.symm) (z p)) := by
  obtain ⟨L, hL⟩ := hy.exists_hessian_trans_eq_bilinearComp hz hp hpz hf hcrit
  rw [hL, index_bilinearComp]

/-- **The nullity does not depend on the coordinate system.** -/
theorem nullity_trans_eq (hy : IsSmoothCoord E y) (hz : IsSmoothCoord E z)
    (hp : p ∈ y.source) (hpz : p ∈ z.source) {f : M → ℝ}
    (hf : ContDiffAt ℝ 2 (f ∘ z.symm) (z p)) (hcrit : fderiv ℝ (f ∘ z.symm) (z p) = 0) :
    nullity (hessian (f ∘ y.symm) (y p)) = nullity (hessian (f ∘ z.symm) (z p)) := by
  obtain ⟨L, hL⟩ := hy.exists_hessian_trans_eq_bilinearComp hz hp hpz hf hcrit
  rw [hL, nullity_bilinearComp]

end IsSmoothCoord

end Coord

/-! ### Critical points, Hessian, index and nullity in an arbitrary coordinate system -/

section AnyCoord

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [IsManifold 𝓘(ℝ, E) ∞ M] {y : OpenPartialHomeomorph M E'} {p : M} {f : M → ℝ}

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem hessianM_eq_chartAt (f : M → ℝ) (p : M) :
    hessianM E f p = hessian (f ∘ (chartAt E p).symm) (chartAt E p p) := by
  rw [hessianM, localRep_eq, extChartAt_self_coe]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem contDiffAt_comp_chartAt_symm (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 f p) :
    ContDiffAt ℝ 2 (f ∘ (chartAt E p).symm) (chartAt E p p) := by
  have h := contMDiffAt_iff_contDiffAt_localRep.1 hf
  rwa [localRep_eq, extChartAt_self_coe] at h

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem fderiv_comp_chartAt_symm_eq_zero (hcrit : IsCriticalPointM E f p) :
    fderiv ℝ (f ∘ (chartAt E p).symm) (chartAt E p p) = 0 := by
  have h := isCriticalPointM_iff_fderiv.1 hcrit
  rwa [localRep_eq, extChartAt_self_coe] at h

namespace IsSmoothCoord

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The derivative of the parametrization `y⁻¹` at `y p`, read in the preferred chart at `p`, is the
derivative of the transition map `chart_p ∘ y⁻¹`. -/
theorem mfderiv_symm_eq (hy : IsSmoothCoord E y) (hp : p ∈ y.source) :
    mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E) y.symm (y p) = fderiv ℝ (chartAt E p ∘ y.symm) (y p) := by
  have hmd : MDifferentiableAt 𝓘(ℝ, E') 𝓘(ℝ, E) y.symm (y p) :=
    ((hy.contMDiffOn_symm (y p) (y.map_source hp)).contMDiffAt
      (y.open_target.mem_nhds (y.map_source hp))).mdifferentiableAt (by simp)
  rw [hmd.mfderiv]
  have hw : writtenInExtChartAt 𝓘(ℝ, E') 𝓘(ℝ, E) (y p) y.symm = chartAt E p ∘ y.symm := by
    funext u
    simp [writtenInExtChartAt, y.left_inv hp, chartAt_self_eq]
  rw [hw, modelWithCornersSelf_coe, range_id, fderivWithin_univ]
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq]
  rfl

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem mdifferentiableAt (hy : IsSmoothCoord E y) (hp : p ∈ y.source) :
    MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E') y p :=
  ((hy.contMDiffOn p hp).contMDiffAt (y.open_source.mem_nhds hp)).mdifferentiableAt (by simp)

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The derivative of a coordinate system `y` at `p`, read in the preferred chart at `p`, is the
derivative of the transition map `y ∘ chart_p⁻¹`. -/
theorem mfderiv_eq (hy : IsSmoothCoord E y) (hp : p ∈ y.source) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E') y p = fderiv ℝ (y ∘ (chartAt E p).symm) (chartAt E p p) := by
  rw [(hy.mdifferentiableAt hp).mfderiv]
  have hw : writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, E') p y = y ∘ (chartAt E p).symm := by
    funext u
    simp [writtenInExtChartAt, chartAt_self_eq]
  rw [hw, modelWithCornersSelf_coe, range_id, fderivWithin_univ, extChartAt_self_coe]

/-- **The derivative of a coordinate system is a linear isomorphism** `TM_p ≃ E'`. -/
theorem exists_mfderiv_eq (hy : IsSmoothCoord E y) (hp : p ∈ y.source) :
    ∃ L : E ≃L[ℝ] E', mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E') y p = (L : E →L[ℝ] E') := by
  obtain ⟨L, hL⟩ := (isSmoothCoord_chartAt p).exists_fderiv_trans_eq hy (mem_chart_source E p) hp
  exact ⟨L, by rw [hy.mfderiv_eq hp, hL]⟩

/-- **The derivative of the parametrization `y⁻¹` is a linear isomorphism** `E' ≃ TM_p`. -/
theorem exists_mfderiv_symm_eq (hy : IsSmoothCoord E y) (hp : p ∈ y.source) :
    ∃ L : E' ≃L[ℝ] E, mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E) y.symm (y p) = (L : E' →L[ℝ] E) := by
  obtain ⟨L, hL⟩ := hy.exists_fderiv_trans_eq (isSmoothCoord_chartAt p) hp (mem_chart_source E p)
  exact ⟨L, by rw [hy.mfderiv_symm_eq hp, hL]⟩

/-- **Critical points can be computed in any coordinate system** (Milnor, p. 4: "If we choose a
local coordinate system `(x¹, …, xⁿ)` in a neighborhood `U` of `p` this means that
`∂f/∂x¹(p) = ⋯ = ∂f/∂xⁿ(p) = 0`"). -/
theorem isCriticalPointM_iff (hy : IsSmoothCoord E y) (hp : p ∈ y.source)
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p) :
    IsCriticalPointM E f p ↔ IsCriticalPoint (f ∘ y.symm) (y p) := by
  have hd : DifferentiableAt ℝ (f ∘ (chartAt E p).symm) (chartAt E p p) := by
    have h := mdifferentiableAt_iff_differentiableAt_localRep.1 hf
    rwa [localRep_eq, extChartAt_self_coe] at h
  rw [hy.isCriticalPoint_trans_iff (isSmoothCoord_chartAt p) hp (mem_chart_source E p) hd,
    Morse.isCriticalPointM_iff hf, localRep_eq, extChartAt_self_coe]

/-- **The Hessian in an arbitrary coordinate system** (Milnor, p. 5).  At a critical point `p`,
the Hessian of the representative `f ∘ y⁻¹` at `y p` is the Hessian `f_**` of `f` at `p` pulled
back by the derivative of the parametrization `y⁻¹`.  In Milnor's words: the matrix
`(∂²f/∂yⁱ∂yʲ(p))` represents `f_**` with respect to the basis `∂/∂y¹|_p, …, ∂/∂yⁿ|_p`, where
`∂/∂yⁱ|_p = d(y⁻¹)(eᵢ)`. -/
theorem hessian_comp_symm (hy : IsSmoothCoord E y) (hp : p ∈ y.source)
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 f p) (hcrit : IsCriticalPointM E f p) (v w : E') :
    hessian (f ∘ y.symm) (y p) v w =
      hessianM E f p (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E) y.symm (y p) v)
        (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E) y.symm (y p) w) := by
  rw [hy.hessian_trans (isSmoothCoord_chartAt p) hp (mem_chart_source E p)
      (contDiffAt_comp_chartAt_symm hf) (fderiv_comp_chartAt_symm_eq_zero hcrit),
    hessianM_eq_chartAt, hy.mfderiv_symm_eq hp]
  rfl

/-- **Non-degeneracy can be computed in any coordinate system** (Milnor, p. 4: "It can be checked
directly that non-degeneracy does not depend on the coordinate system"). -/
theorem isNondegenerate_iff (hy : IsSmoothCoord E y) (hp : p ∈ y.source)
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 f p) (hcrit : IsCriticalPointM E f p) :
    IsNondegenerate (hessian (f ∘ y.symm) (y p)) ↔ IsNondegenerate (hessianM E f p) := by
  rw [hy.isNondegenerate_trans_iff (isSmoothCoord_chartAt p) hp (mem_chart_source E p)
      (contDiffAt_comp_chartAt_symm hf) (fderiv_comp_chartAt_symm_eq_zero hcrit),
    hessianM_eq_chartAt]

/-- **The index can be computed in any coordinate system.** -/
theorem index_eq (hy : IsSmoothCoord E y) (hp : p ∈ y.source)
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 f p) (hcrit : IsCriticalPointM E f p) :
    index (hessian (f ∘ y.symm) (y p)) = indexM E f p := by
  rw [hy.index_trans_eq (isSmoothCoord_chartAt p) hp (mem_chart_source E p)
      (contDiffAt_comp_chartAt_symm hf) (fderiv_comp_chartAt_symm_eq_zero hcrit),
    indexM, hessianM_eq_chartAt]

/-- **The nullity can be computed in any coordinate system.** -/
theorem nullity_eq (hy : IsSmoothCoord E y) (hp : p ∈ y.source)
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 f p) (hcrit : IsCriticalPointM E f p) :
    nullity (hessian (f ∘ y.symm) (y p)) = nullityM E f p := by
  rw [hy.nullity_trans_eq (isSmoothCoord_chartAt p) hp (mem_chart_source E p)
      (contDiffAt_comp_chartAt_symm hf) (fderiv_comp_chartAt_symm_eq_zero hcrit),
    nullityM, hessianM_eq_chartAt]

/-- **Non-degenerate critical points can be recognized in any coordinate system.** -/
theorem isNondegenerateCriticalPointM_iff (hy : IsSmoothCoord E y) (hp : p ∈ y.source)
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 f p) :
    IsNondegenerateCriticalPointM E f p ↔ IsNondegenerateCriticalPoint (f ∘ y.symm) (y p) := by
  have hcrit := hy.isCriticalPointM_iff hp (hf.mdifferentiableAt (by simp))
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨hcrit.1 h1, (hy.isNondegenerate_iff hp hf h1).2 h2⟩
  · rintro ⟨h1, h2⟩
    have h1' := hcrit.2 h1
    exact ⟨h1', (hy.isNondegenerate_iff hp hf h1').1 h2⟩

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The representative of a function `Cⁿ` at `p` in a coordinate system is `Cⁿ` at `y p`. -/
theorem contDiffAt_comp_symm (hy : IsSmoothCoord E y) (hp : p ∈ y.source) {n : WithTop ℕ∞}
    (hn : n ≤ ∞) (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) n f p) :
    ContDiffAt ℝ n (f ∘ y.symm) (y p) := by
  have hs : ContMDiffAt 𝓘(ℝ, E') 𝓘(ℝ, E) n y.symm (y p) :=
    ((hy.contMDiffOn_symm (y p) (y.map_source hp)).contMDiffAt
      (y.open_target.mem_nhds (y.map_source hp))).of_le hn
  have hf' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) n f (y.symm (y p)) := by rwa [y.left_inv hp]
  exact contMDiffAt_iff_contDiffAt.1 (hf'.comp (y p) hs)

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem differentiableAt_comp_symm (hy : IsSmoothCoord E y) (hp : p ∈ y.source)
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p) :
    DifferentiableAt ℝ (f ∘ y.symm) (y p) := by
  have hs : MDifferentiableAt 𝓘(ℝ, E') 𝓘(ℝ, E) y.symm (y p) :=
    ((hy.contMDiffOn_symm (y p) (y.map_source hp)).contMDiffAt
      (y.open_target.mem_nhds (y.map_source hp))).mdifferentiableAt (by simp)
  have hf' : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (y.symm (y p)) := by rwa [y.left_inv hp]
  exact mdifferentiableAt_iff_differentiableAt.1 (hf'.comp (y p) hs)

/-- **Milnor's definition of a critical point in coordinates** (p. 4): in a coordinate system
`(y¹, …, yⁿ)` around `p`, `p` is a critical point of `f` iff `∂f/∂y¹(p) = ⋯ = ∂f/∂yⁿ(p) = 0`. -/
theorem isCriticalPointM_iff_forall_partial {n : ℕ} {y : OpenPartialHomeomorph M (Fin n → ℝ)}
    (hy : IsSmoothCoord E y) (hp : p ∈ y.source) (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p) :
    IsCriticalPointM E f p ↔ ∀ i, fderiv ℝ (f ∘ y.symm) (y p) (Pi.single i 1) = 0 := by
  rw [hy.isCriticalPointM_iff hp hf, isCriticalPoint_iff (hy.differentiableAt_comp_symm hp hf)]
  constructor
  · intro h i
    rw [h, zero_apply]
  · intro h
    refine ContinuousLinearMap.coe_injective (LinearMap.pi_ext fun i t => ?_)
    have hsingle : (Pi.single i t : Fin n → ℝ) = t • Pi.single i 1 := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    simp [hsingle, h i]

/-- **Milnor's definition of non-degeneracy in coordinates** (p. 4): in a coordinate system
`(y¹, …, yⁿ)` around a critical point `p`, `p` is non-degenerate iff the matrix
`(∂²f/∂yⁱ∂yʲ(p))` is non-singular. -/
theorem isNondegenerate_iff_det_ne_zero {n : ℕ} {y : OpenPartialHomeomorph M (Fin n → ℝ)}
    (hy : IsSmoothCoord E y) (hp : p ∈ y.source) (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 f p)
    (hcrit : IsCriticalPointM E f p) :
    IsNondegenerate (hessianM E f p) ↔
      (Matrix.of fun i j =>
        hessian (f ∘ y.symm) (y p) (Pi.single i 1) (Pi.single j 1)).det ≠ 0 := by
  rw [← hy.isNondegenerate_iff hp hf hcrit]
  exact isNondegenerate_hessian_iff_det_ne_zero (hy.contDiffAt_comp_symm hp (by norm_cast) hf)

end IsSmoothCoord

/-! #### The charts of the maximal atlas

The statements of the previous section for the charts `e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M`,
which are exactly the smooth coordinate systems with values in `E`. -/

theorem isCriticalPointM_iff_of_mem_maximalAtlas {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (hp : p ∈ e.source)
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p) :
    IsCriticalPointM E f p ↔ IsCriticalPoint (f ∘ e.symm) (e p) :=
  (isSmoothCoord_of_mem_maximalAtlas he).isCriticalPointM_iff hp hf

theorem hessian_comp_symm_of_mem_maximalAtlas {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (hp : p ∈ e.source)
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 f p) (hcrit : IsCriticalPointM E f p) (v w : E) :
    hessian (f ∘ e.symm) (e p) v w =
      hessianM E f p (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e p) v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e p) w) :=
  (isSmoothCoord_of_mem_maximalAtlas he).hessian_comp_symm hp hf hcrit v w

theorem isNondegenerate_iff_of_mem_maximalAtlas {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (hp : p ∈ e.source)
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 f p) (hcrit : IsCriticalPointM E f p) :
    IsNondegenerate (hessian (f ∘ e.symm) (e p)) ↔ IsNondegenerate (hessianM E f p) :=
  (isSmoothCoord_of_mem_maximalAtlas he).isNondegenerate_iff hp hf hcrit

theorem indexM_eq_of_mem_maximalAtlas {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (hp : p ∈ e.source)
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 f p) (hcrit : IsCriticalPointM E f p) :
    indexM E f p = index (hessian (f ∘ e.symm) (e p)) :=
  ((isSmoothCoord_of_mem_maximalAtlas he).index_eq hp hf hcrit).symm

theorem nullityM_eq_of_mem_maximalAtlas {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (hp : p ∈ e.source)
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 f p) (hcrit : IsCriticalPointM E f p) :
    nullityM E f p = nullity (hessian (f ∘ e.symm) (e p)) :=
  ((isSmoothCoord_of_mem_maximalAtlas he).nullity_eq hp hf hcrit).symm

end AnyCoord

end Morse
