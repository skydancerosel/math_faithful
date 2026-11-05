import Morse.Chapter3.EulerChar
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
Milnor, *Morse Theory*, §2, pp. 4–5 (critical points, Hessian, index), as used after an embedding
in §6, p. 36.

# Invariance of the Morse notions under diffeomorphisms

## Milnor's text, paraphrased

Milnor defines critical points, their non-degeneracy and their index intrinsically (pp. 4–5), and
then in §6 replaces a manifold by its image under Whitney's embedding without comment: a
function on the manifold and the corresponding function on the image are treated as the same
function, with the same critical points and indices.  The justification is the invariance of
these notions under diffeomorphisms, which the book never states.

## What is proved here

Let `g : M ≃ M'` be a smooth diffeomorphism (Mathlib's `Diffeomorph`) between smooth manifolds
without boundary modelled on real normed spaces `E` and `E'`, and `f : M → ℝ`.  Then `f` on `M`
corresponds to `f ∘ g⁻¹` on `M'`, and:

* `Morse.isCriticalPointM_comp_symm_iff`: `q` is a critical point of `f ∘ g⁻¹` iff `g⁻¹ q` is a
  critical point of `f` (for every `f`: where `f` is not differentiable neither is `f ∘ g⁻¹`);
* `Morse.hessianM_comp_symm_apply`: at a critical point the Hessian of `f ∘ g⁻¹` at `q` is the
  Hessian of `f` at `g⁻¹ q` pulled back by `d(g⁻¹)_q`;
* `Morse.isNondegenerate_hessianM_comp_symm_iff`,
  `Morse.isNondegenerateCriticalPointM_comp_symm_iff`, `Morse.indexM_comp_symm`,
  `Morse.nullityM_comp_symm`: non-degeneracy, index and nullity correspond;
* `Morse.IsMorseFunction.comp_diffeomorph_symm`, `Morse.isMorseFunction_comp_symm_iff`: `f` is a
  Morse function iff `f ∘ g⁻¹` is;
* `Morse.setOf_isCriticalPointM_comp_symm`, `Morse.ncard_setOf_isCriticalPointM_comp_symm`,
  `Morse.critCount_comp_symm`: `g` maps the critical set of `f` onto that of `f ∘ g⁻¹`, and the
  number of critical points and the Morse numbers `C_λ` agree.

The proof uses the chart independence of `Morse/Chapter1/Manifold.lean`: `chart_q ∘ g` is a
smooth coordinate system on `M` around `g⁻¹ q` (`Morse.isSmoothCoord_diffeoCoord`), and reading
`f` in it is the same as reading `f ∘ g⁻¹` in the chart of `M'` at `q`
(`Morse.hessianM_comp_symm_eq`).

## What Milnor leaves implicit

* **The statement itself**, as explained above.
* **Only `C²` at the point is used** for the Hessian statements, as in `Manifold.lean`; criticality
  needs no regularity at all.
* **The model spaces may differ**: `E` and `E'` are any real normed spaces (for a diffeomorphism
  they have the same dimension when finite-dimensional, but this is not needed).  In
  `Morse/Chapter4/Whitney.lean` `M` is modelled on `E` and its image in Euclidean space on
  `ℝᵈ⁺¹`.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold

noncomputable section

namespace Morse

section Invariance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace E' M'] [IsManifold 𝓘(ℝ, E') ∞ M']
  (g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E') M M' ∞)

/-! ### Critical points -/

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, E') ∞ M'] in
/-- **Critical points correspond under a diffeomorphism**: `q` is a critical point of `f ∘ g⁻¹`
iff `g⁻¹ q` is a critical point of `f`.  (No smoothness of `f` is needed: where `f` is not
differentiable, neither is `f ∘ g⁻¹`, and both derivatives are `0` by Mathlib's convention.) -/
theorem isCriticalPointM_comp_symm_iff {f : M → ℝ} {q : M'} :
    IsCriticalPointM E' (f ∘ g.symm) q ↔ IsCriticalPointM E f (g.symm q) := by
  by_cases hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (g.symm q)
  · have hg : MDifferentiableAt 𝓘(ℝ, E') 𝓘(ℝ, E) g.symm q := g.symm.mdifferentiable (by simp) q
    unfold IsCriticalPointM
    rw [mfderiv_comp q hf hg]
    -- `d(g⁻¹)_q` is onto
    have hA : Surjective (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E) g.symm q) :=
      (g.symm.mfderivToContinuousLinearEquiv (by simp) q).surjective
    constructor
    · intro h
      refine ContinuousLinearMap.ext fun v => ?_
      obtain ⟨u, rfl⟩ := hA v
      exact congrArg (fun L : TangentSpace 𝓘(ℝ, E') q →L[ℝ] ℝ => L u) h
    · intro h
      rw [h, ContinuousLinearMap.zero_comp]
  · have hf' : ¬MDifferentiableAt 𝓘(ℝ, E') 𝓘(ℝ, ℝ) (f ∘ g.symm) q := by
      intro h
      apply hf
      have h' : MDifferentiableAt 𝓘(ℝ, E') 𝓘(ℝ, ℝ) (f ∘ g.symm) (g (g.symm q)) := by
        rwa [g.apply_symm_apply]
      have h'' := h'.comp (g.symm q) (g.mdifferentiable (by simp) (g.symm q))
      have hfg : (f ∘ g.symm) ∘ g = f := funext fun x => by simp
      rwa [hfg] at h''
    unfold IsCriticalPointM
    rw [mfderiv_zero_of_not_mdifferentiableAt hf, mfderiv_zero_of_not_mdifferentiableAt hf']
    exact ⟨fun _ => rfl, fun _ => rfl⟩

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, E') ∞ M'] in
/-- **`g` maps the critical set of `f` onto the critical set of `f ∘ g⁻¹`.** -/
theorem setOf_isCriticalPointM_comp_symm (f : M → ℝ) :
    {q : M' | IsCriticalPointM E' (f ∘ g.symm) q} = g '' {p : M | IsCriticalPointM E f p} := by
  ext q
  constructor
  · intro hq
    exact ⟨g.symm q, (isCriticalPointM_comp_symm_iff g).1 hq, g.apply_symm_apply q⟩
  · rintro ⟨p, hp, rfl⟩
    change IsCriticalPointM E' (f ∘ g.symm) (g p)
    rw [isCriticalPointM_comp_symm_iff, g.symm_apply_apply]
    exact hp

/-! ### The coordinate system `chart_q ∘ g` -/

/-- The coordinate system `chart_q ∘ g` on `M`, defined near `g⁻¹ q`, with values in `E'`. -/
def diffeoCoord (q : M') : OpenPartialHomeomorph M E' :=
  g.toHomeomorph.toOpenPartialHomeomorph.trans (chartAt E' q)

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, E') ∞ M'] in
theorem diffeoCoord_coe (q : M') : ⇑(diffeoCoord g q) = chartAt E' q ∘ g := rfl

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, E') ∞ M'] in
theorem diffeoCoord_symm_coe (q : M') :
    ⇑(diffeoCoord g q).symm = g.symm ∘ (chartAt E' q).symm :=
  rfl

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, E') ∞ M'] in
theorem mem_diffeoCoord_source (q : M') : g.symm q ∈ (diffeoCoord g q).source := by
  simp [diffeoCoord, mem_chart_source]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- `chart_q ∘ g` is a smooth coordinate system on `M` (in the sense of `Morse.IsSmoothCoord`). -/
theorem isSmoothCoord_diffeoCoord (q : M') : IsSmoothCoord E (diffeoCoord g q) := by
  constructor
  · rw [diffeoCoord_coe]
    refine (contMDiffOn_chart (x := q)).comp g.contMDiff.contMDiffOn ?_
    intro x hx
    simpa [diffeoCoord] using hx
  · rw [diffeoCoord_symm_coe]
    refine g.symm.contMDiff.comp_contMDiffOn (contMDiffOn_chart_symm.mono ?_)
    intro u hu
    simpa [diffeoCoord] using hu.1

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, E') ∞ M'] in
/-- The Hessian of `f ∘ g⁻¹` at `q` (computed in the chart of `M'` at `q`) is the Hessian of the
representative of `f` in the coordinate system `chart_q ∘ g`. -/
theorem hessianM_comp_symm_eq (f : M → ℝ) (q : M') :
    hessianM E' (f ∘ g.symm) q =
      hessian (f ∘ (diffeoCoord g q).symm) (diffeoCoord g q (g.symm q)) := by
  rw [hessianM_eq_chartAt, diffeoCoord_symm_coe, diffeoCoord_coe, comp_apply,
    g.apply_symm_apply]
  rfl

/-! ### Hessian, non-degeneracy, index and nullity -/

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The derivative of the inverse chart at the centre of the chart is the identity (with Mathlib's
identification of the tangent spaces of `M'` with `E'`). -/
theorem mfderiv_chartAt_symm_self_apply (q : M') (v : E') :
    mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E') (chartAt E' q).symm (chartAt E' q q) v = v := by
  rw [(isSmoothCoord_chartAt q).mfderiv_symm_eq (mem_chart_source E' q)]
  have hev : (chartAt E' q ∘ (chartAt E' q).symm) =ᶠ[𝓝 (chartAt E' q q)] id := by
    filter_upwards [(chartAt E' q).open_target.mem_nhds (mem_chart_target E' q)] with u hu
    exact (chartAt E' q).right_inv hu
  rw [hev.fderiv_eq, fderiv_id]
  rfl

/-- **The Hessian is pulled back by the diffeomorphism** (at a critical point):
`(f ∘ g⁻¹)_**(v, w) = f_**(d(g⁻¹)_q v, d(g⁻¹)_q w)`. -/
theorem hessianM_comp_symm_apply {f : M → ℝ} {q : M'}
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 f (g.symm q))
    (hcrit : IsCriticalPointM E f (g.symm q)) (v w : E') :
    hessianM E' (f ∘ g.symm) q v w =
      hessianM E f (g.symm q) (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E) g.symm q v)
        (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E) g.symm q w) := by
  rw [hessianM_comp_symm_eq, (isSmoothCoord_diffeoCoord g q).hessian_comp_symm
    (mem_diffeoCoord_source g q) hf hcrit]
  have hy : diffeoCoord g q (g.symm q) = chartAt E' q q := by
    rw [diffeoCoord_coe, comp_apply, g.apply_symm_apply]
  have hq : (chartAt E' q).symm (chartAt E' q q) = q :=
    (chartAt E' q).left_inv (mem_chart_source E' q)
  have key : ∀ u : E', mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E) (diffeoCoord g q).symm
      (diffeoCoord g q (g.symm q)) u = mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E) g.symm q u := by
    intro u
    have hg : MDifferentiableAt 𝓘(ℝ, E') 𝓘(ℝ, E) g.symm q := g.symm.mdifferentiable (by simp) _
    have hc : MDifferentiableAt 𝓘(ℝ, E') 𝓘(ℝ, E') (chartAt E' q).symm (chartAt E' q q) :=
      ((contMDiffOn_chart_symm (n := ∞) _ (mem_chart_target E' q)).contMDiffAt
        ((chartAt E' q).open_target.mem_nhds (mem_chart_target E' q))).mdifferentiableAt
        (by simp)
    rw [hy, diffeoCoord_symm_coe]
    exact (mfderiv_comp_apply_of_eq _ hg hc hq u).trans
      (congrArg _ (mfderiv_chartAt_symm_self_apply q u))
  rw [key, key]

/-- **Non-degeneracy corresponds under a diffeomorphism.** -/
theorem isNondegenerate_hessianM_comp_symm_iff {f : M → ℝ} {q : M'}
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 f (g.symm q))
    (hcrit : IsCriticalPointM E f (g.symm q)) :
    IsNondegenerate (hessianM E' (f ∘ g.symm) q) ↔ IsNondegenerate (hessianM E f (g.symm q)) := by
  rw [hessianM_comp_symm_eq]
  exact (isSmoothCoord_diffeoCoord g q).isNondegenerate_iff (mem_diffeoCoord_source g q) hf hcrit

/-- **Non-degenerate critical points correspond under a diffeomorphism.** -/
theorem isNondegenerateCriticalPointM_comp_symm_iff {f : M → ℝ} {q : M'}
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 f (g.symm q)) :
    IsNondegenerateCriticalPointM E' (f ∘ g.symm) q ↔
      IsNondegenerateCriticalPointM E f (g.symm q) := by
  constructor
  · rintro ⟨h1, h2⟩
    have h1' := (isCriticalPointM_comp_symm_iff g).1 h1
    exact ⟨h1', (isNondegenerate_hessianM_comp_symm_iff g hf h1').1 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(isCriticalPointM_comp_symm_iff g).2 h1,
      (isNondegenerate_hessianM_comp_symm_iff g hf h1).2 h2⟩

/-- **The index is invariant under diffeomorphisms.** -/
theorem indexM_comp_symm {f : M → ℝ} {q : M'}
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 f (g.symm q))
    (hcrit : IsCriticalPointM E f (g.symm q)) :
    indexM E' (f ∘ g.symm) q = indexM E f (g.symm q) := by
  rw [indexM, hessianM_comp_symm_eq]
  exact (isSmoothCoord_diffeoCoord g q).index_eq (mem_diffeoCoord_source g q) hf hcrit

/-- **The nullity is invariant under diffeomorphisms.** -/
theorem nullityM_comp_symm {f : M → ℝ} {q : M'}
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 f (g.symm q))
    (hcrit : IsCriticalPointM E f (g.symm q)) :
    nullityM E' (f ∘ g.symm) q = nullityM E f (g.symm q) := by
  rw [nullityM, hessianM_comp_symm_eq]
  exact (isSmoothCoord_diffeoCoord g q).nullity_eq (mem_diffeoCoord_source g q) hf hcrit

/-! ### Morse functions and Morse numbers -/

/-- **A Morse function composed with a diffeomorphism is a Morse function.** -/
theorem IsMorseFunction.comp_diffeomorph_symm {f : M → ℝ} (hf : IsMorseFunction E f) :
    IsMorseFunction E' (f ∘ g.symm) where
  contMDiff := hf.contMDiff.comp g.symm.contMDiff
  isNondegenerate q hq := by
    have hcrit := (isCriticalPointM_comp_symm_iff g).1 hq
    exact (isNondegenerate_hessianM_comp_symm_iff g
      (hf.contMDiff.contMDiffAt.of_le (by norm_cast)) hcrit).2 (hf.isNondegenerate _ hcrit)

/-- **`f` is a Morse function iff `f ∘ g⁻¹` is.** -/
theorem isMorseFunction_comp_symm_iff {f : M → ℝ} :
    IsMorseFunction E' (f ∘ g.symm) ↔ IsMorseFunction E f := by
  refine ⟨fun h => ?_, fun h => h.comp_diffeomorph_symm g⟩
  have h' := h.comp_diffeomorph_symm g.symm
  have hfg : (f ∘ g.symm) ∘ g.symm.symm = f := funext fun x => by simp
  rwa [hfg] at h'

/-- **The Morse numbers `C_λ` are invariant under diffeomorphisms**: `f` and `f ∘ g⁻¹` have the
same number of critical points of each index. -/
theorem critCount_comp_symm {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 f) (k : ℕ) :
    critCount E' (f ∘ g.symm) k = critCount E f k := by
  unfold critCount
  have : {q : M' | IsCriticalPointM E' (f ∘ g.symm) q ∧ indexM E' (f ∘ g.symm) q = k} =
      g '' {p : M | IsCriticalPointM E f p ∧ indexM E f p = k} := by
    ext q
    constructor
    · rintro ⟨hq, hk⟩
      have hcrit := (isCriticalPointM_comp_symm_iff g).1 hq
      refine ⟨g.symm q, ⟨hcrit, ?_⟩, g.apply_symm_apply q⟩
      rw [← indexM_comp_symm g (hf _) hcrit, hk]
    · rintro ⟨p, ⟨hp, hk⟩, rfl⟩
      have hcrit : IsCriticalPointM E f (g.symm (g p)) := by rwa [g.symm_apply_apply]
      refine ⟨(isCriticalPointM_comp_symm_iff g).2 hcrit, ?_⟩
      rw [indexM_comp_symm g (hf _) hcrit, g.symm_apply_apply, hk]
  have hinj : Injective g := fun a b hab => by simpa using congrArg g.symm hab
  rw [this, Set.ncard_image_of_injective _ hinj]

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, E') ∞ M'] in
/-- **The number of critical points is invariant under diffeomorphisms.** -/
theorem ncard_setOf_isCriticalPointM_comp_symm (f : M → ℝ) :
    {q : M' | IsCriticalPointM E' (f ∘ g.symm) q}.ncard =
      {p : M | IsCriticalPointM E f p}.ncard := by
  have hinj : Injective g := fun a b hab => by simpa using congrArg g.symm hab
  rw [setOf_isCriticalPointM_comp_symm, Set.ncard_image_of_injective _ hinj]

end Invariance

end Morse
