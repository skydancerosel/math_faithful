import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
Milnor, *Morse Theory*, §2, pp. 4–5 and p. 8.

# Critical points, the Hessian, the index; non-degenerate critical points are isolated

Milnor's definitions (pp. 4–5), paraphrased, for a smooth `f : M → ℝ`:

* `p` is a *critical point* of `f` if `f_* : TM_p → TR_{f(p)}` is zero;
* a critical point is *non-degenerate* if the matrix `(∂²f/∂xⁱ∂xʲ(p))` in some (any) coordinate
  system is non-singular;
* at a critical point, the *Hessian* `f_**` is the symmetric bilinear form on `TM_p` given by
  `f_**(v, w) = ṽ_p(w̃(f))`, `ṽ`, `w̃` being vector fields extending `v`, `w`;
* the *index* of a bilinear form `H` on a vector space `V` is the largest dimension of a subspace
  of `V` on which `H` is negative definite, and its *nullity* is the dimension of its null space
  `{v | H(v, w) = 0 for all w}`; `p` is a non-degenerate critical point iff `f_**` has nullity
  `0`.

**Corollary 2.3** (p. 8): non-degenerate critical points are isolated.

## Setting

Everything here is on a real normed space `E` (finite-dimensional wherever dimensions are
counted).  This is Milnor's situation after choosing a coordinate system `(x¹, …, xⁿ)` around
`p`; his manifold-level definitions are not formalized here.

* `Morse.IsCriticalPoint f p`: `f` has derivative `0` at `p`.
* `Morse.hessian f p = d²f_p`, i.e. `fderiv ℝ (fderiv ℝ f) p`, a continuous bilinear form.
  Milnor's `f_**(v, w) = ṽ_p(w̃(f))`, computed with the constant extensions `ṽ = v`, `w̃ = w`, is
  `d(x ↦ df_x(w))_p(v) = d²f_p(v)(w)`.  Milnor defines `f_**` only at critical points, the
  points where it does not depend on the coordinates; `Morse.hessian f p` is defined at every
  point (it is just the second derivative), but is only used at critical points.
* `Morse.nullSpace`, `Morse.nullity`, `Morse.index`, `Morse.IsNondegenerate` as in Milnor.  The
  index is Mathlib's `sigNeg` of the quadratic form `v ↦ H(v, v)` (the maximal dimension of a
  subspace on which that form is negative definite); `Morse.index_isGreatest` restates this in
  Milnor's words.

## What Milnor leaves implicit, and how it is handled

* **Symmetry of the Hessian.**  Milnor proves symmetry by
  `ṽ_p(w̃(f)) − w̃_p(ṽ(f)) = [ṽ, w̃]_p(f) = 0`, which uses that `p` is critical.  In a
  normed space the Hessian is the second derivative and its symmetry is the symmetry of second
  derivatives, valid at every point where `f` is `C²`, critical or not (`Morse.hessian_symm`).
  The critical-point hypothesis is what makes the Hessian independent of coordinates; that is
  where it is used here (`Morse.hessian_comp`).
* **Independence of the coordinate system.**  Milnor remarks (p. 4) that one can check directly
  that non-degeneracy does not depend on the coordinates.  This is `Morse.hessian_comp`: if `ψ`
  is `C²` at `q`, `f` is `C²` at `p = ψ q` and `df_p = 0`, then
  `d²(f ∘ ψ)_q(v, w) = d²f_p(dψ_q v, dψ_q w)`.  The other term of the chain rule,
  `df_p(d²ψ_q(v, w))`, vanishes exactly because `p` is critical.  Hence a change of coordinates
  (`dψ_q` invertible) preserves non-degeneracy and the index
  (`Morse.isNondegenerate_hessian_comp_iff`, `Morse.index_hessian_comp`).
* **Matrix criterion.**  Milnor's first definition (the matrix `(∂²f/∂xⁱ∂xʲ(p))` is
  non-singular) agrees with the intrinsic one (nullity `0`):
  `Morse.isNondegenerate_hessian_iff_det_ne_zero`.
* **Corollary 2.3** is stated right after the Morse lemma, from which it follows (in Morse
  coordinates `f = f(p) − ∑ (yⁱ)² + ∑ (yʲ)²`, whose only critical point is `y = 0`), but Milnor
  gives no argument.  We prove it directly, assuming only that `f` is `C²` at `p`: the map
  `x ↦ df_x` has derivative `d²f_p` at `p`, which is injective by non-degeneracy, so `x ↦ df_x`
  does not take the value `0` at points `x ≠ p` near `p` (the injectivity half of the inverse
  function theorem, `HasFDerivAt.eventually_ne`): `Morse.eventually_not_isCriticalPoint`,
  `Morse.IsNondegenerateCriticalPoint.exists_nhds_isCriticalPoint_eq`.  (The sister project
  proves the analogous statement for vector fields, `Milnor.Sphere.exists_radius_of_nondegenerate`:
  a zero `z` of `v` with `dv_z` bijective is isolated.  In coordinates on `ℝⁿ` Corollary 2.3 is
  its case `v = grad f`; working with `x ↦ df_x ∈ E*` avoids choosing an inner product.)
-/

open Set Filter Topology
open scoped ContDiff

noncomputable section

namespace Morse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-! ### Critical points and the Hessian -/

/-- **Critical point** (Milnor, p. 4): `p` is a critical point of `f : E → ℝ` if `f` is
differentiable at `p` with derivative `0`. -/
def IsCriticalPoint (f : E → ℝ) (p : E) : Prop :=
  HasFDerivAt f (0 : E →L[ℝ] ℝ) p

theorem IsCriticalPoint.fderiv_eq {f : E → ℝ} {p : E} (h : IsCriticalPoint f p) :
    fderiv ℝ f p = 0 :=
  HasFDerivAt.fderiv h

theorem isCriticalPoint_iff {f : E → ℝ} {p : E} (hf : DifferentiableAt ℝ f p) :
    IsCriticalPoint f p ↔ fderiv ℝ f p = 0 := by
  refine ⟨fun h => h.fderiv_eq, fun h => ?_⟩
  have := hf.hasFDerivAt
  rwa [h] at this

/-- A critical point stays critical after a differentiable change of variables. -/
theorem IsCriticalPoint.comp {f : E → ℝ} {ψ : E' → E} {q : E'}
    (hf : IsCriticalPoint f (ψ q)) (hψ : DifferentiableAt ℝ ψ q) :
    IsCriticalPoint (f ∘ ψ) q := by
  have h := HasFDerivAt.comp q hf hψ.hasFDerivAt
  rwa [ContinuousLinearMap.zero_comp] at h

/-- **The Hessian** (Milnor, pp. 4–5): the second derivative `d²f_p`, as a continuous bilinear
form, `hessian f p v w = d(x ↦ df_x(w))_p(v)`. -/
def hessian (f : E → ℝ) (p : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ f) p

/-- **The Hessian is symmetric** wherever `f` is `C²`. -/
theorem hessian_symm {f : E → ℝ} {p : E} (hf : ContDiffAt ℝ 2 f p) (v w : E) :
    hessian f p v w = hessian f p w v :=
  (hf.isSymmSndFDerivAt (by simp)) v w

/-- The Hessian only depends on the germ of `f`. -/
theorem hessian_congr {f g : E → ℝ} {p : E} (h : f =ᶠ[𝓝 p] g) : hessian f p = hessian g p :=
  h.fderiv.fderiv_eq

/-- The Hessian of a function of the form `x ↦ B(x, x)`, `B` continuous bilinear, is
`(v, w) ↦ B(v, w) + B(w, v)` at every point. -/
theorem hessian_bilinear (B : E →L[ℝ] E →L[ℝ] ℝ) (p v w : E) :
    hessian (fun x => B x x) p v w = B v w + B w v := by
  have h1 : fderiv ℝ (fun x => B x x) = fun x => B x + B.flip x := by
    funext x
    have h := B.hasFDerivAt_of_bilinear (hasFDerivAt_id x) (hasFDerivAt_id x)
    have heq : B.precompR E (id x) (ContinuousLinearMap.id ℝ E) +
        B.precompL E (ContinuousLinearMap.id ℝ E) (id x) = B x + B.flip x := by
      ext v; simp
    rw [heq] at h
    exact HasFDerivAt.fderiv h
  have h2 : HasFDerivAt (fun x => B x + B.flip x) (B + B.flip) p :=
    B.hasFDerivAt.add B.flip.hasFDerivAt
  rw [hessian, h1, h2.fderiv]
  simp

/-! ### Bilinear functionals: null space, nullity, index -/

/-- The quadratic form `v ↦ H(v, v)` of a continuous bilinear form. -/
def quadForm (H : E →L[ℝ] E →L[ℝ] ℝ) : QuadraticForm ℝ E :=
  LinearMap.BilinMap.toQuadraticMap (ContinuousLinearMap.toLinearMap₁₂ H)

@[simp] theorem quadForm_apply (H : E →L[ℝ] E →L[ℝ] ℝ) (v : E) : quadForm H v = H v v :=
  rfl

/-- **Null space** (Milnor, p. 5): the subspace of all `v` with `H(v, w) = 0` for every `w`. -/
def nullSpace (H : E →L[ℝ] E →L[ℝ] ℝ) : Submodule ℝ E :=
  LinearMap.ker (H : E →ₗ[ℝ] E →L[ℝ] ℝ)

theorem mem_nullSpace {H : E →L[ℝ] E →L[ℝ] ℝ} {v : E} : v ∈ nullSpace H ↔ ∀ w, H v w = 0 := by
  simp [nullSpace, ContinuousLinearMap.ext_iff]

/-- **Nullity** (Milnor, p. 5): the dimension of the null space. -/
def nullity (H : E →L[ℝ] E →L[ℝ] ℝ) : ℕ :=
  Module.finrank ℝ (nullSpace H)

/-- **Index** (Milnor, p. 5): the maximal dimension of a subspace on which `H` is negative
definite.  This is Mathlib's `sigNeg` of the quadratic form `v ↦ H(v, v)`; see
`Morse.index_isGreatest` for the characterization in Milnor's words. -/
def index (H : E →L[ℝ] E →L[ℝ] ℝ) : ℕ :=
  sigNeg (quadForm H)

/-- **Non-degenerate** bilinear functional: nullity `0`, i.e. trivial null space. -/
def IsNondegenerate (H : E →L[ℝ] E →L[ℝ] ℝ) : Prop :=
  nullSpace H = ⊥

theorem isNondegenerate_iff {H : E →L[ℝ] E →L[ℝ] ℝ} :
    IsNondegenerate H ↔ ∀ v, (∀ w, H v w = 0) → v = 0 := by
  simp [IsNondegenerate, Submodule.eq_bot_iff, mem_nullSpace]

theorem isNondegenerate_iff_nullity_eq_zero [FiniteDimensional ℝ E]
    {H : E →L[ℝ] E →L[ℝ] ℝ} : IsNondegenerate H ↔ nullity H = 0 := by
  simp [IsNondegenerate, nullity, Submodule.finrank_eq_zero]

/-- **Non-degenerate critical point** (Milnor, pp. 4–5). -/
def IsNondegenerateCriticalPoint (f : E → ℝ) (p : E) : Prop :=
  IsCriticalPoint f p ∧ IsNondegenerate (hessian f p)

theorem negDef_iff_posDef_restrict {H : E →L[ℝ] E →L[ℝ] ℝ} {W : Submodule ℝ E} :
    (∀ v ∈ W, v ≠ 0 → H v v < 0) ↔ ((-quadForm H).restrict W).PosDef := by
  constructor
  · rintro h ⟨v, hv⟩ hv0
    have hv0' : v ≠ 0 := fun h' => hv0 (Subtype.ext h')
    simpa using h v hv hv0'
  · intro h v hv hv0
    have := h ⟨v, hv⟩ (fun h' => hv0 (congrArg Subtype.val h'))
    simpa using this

/-- **The index in Milnor's words**: `index H` is the largest dimension of a subspace `W` on
which `H` is negative definite (`H(v, v) < 0` for `0 ≠ v ∈ W`). -/
theorem index_isGreatest [FiniteDimensional ℝ E] (H : E →L[ℝ] E →L[ℝ] ℝ) :
    IsGreatest {k | ∃ W : Submodule ℝ E, Module.finrank ℝ W = k ∧ ∀ v ∈ W, v ≠ 0 → H v v < 0}
      (index H) := by
  have key := sigNeg_isGreatest (quadForm H)
  have hset : {k | ∃ W : Submodule ℝ E, Module.finrank ℝ W = k ∧ ∀ v ∈ W, v ≠ 0 → H v v < 0} =
      {r | ∃ V : Submodule ℝ E, Module.finrank ℝ V = r ∧ ((-quadForm H).restrict V).PosDef} := by
    ext k
    simp only [Set.mem_ofPred_eq, negDef_iff_posDef_restrict]
  rw [hset]
  exact key

theorem exists_negDef_finrank_eq_index [FiniteDimensional ℝ E] (H : E →L[ℝ] E →L[ℝ] ℝ) :
    ∃ W : Submodule ℝ E, Module.finrank ℝ W = index H ∧ ∀ v ∈ W, v ≠ 0 → H v v < 0 :=
  (index_isGreatest H).1

theorem finrank_le_index_of_negDef [FiniteDimensional ℝ E] (H : E →L[ℝ] E →L[ℝ] ℝ)
    {W : Submodule ℝ E} (hW : ∀ v ∈ W, v ≠ 0 → H v v < 0) : Module.finrank ℝ W ≤ index H :=
  (index_isGreatest H).2 ⟨W, rfl, hW⟩

/-! ### Invariance under linear changes of variables -/

/-- The quadratic forms of `H` and of its pull-back `H(L ·, L ·)` by a linear isomorphism `L` are
equivalent. -/
theorem quadForm_bilinearComp_equivalent (H : E →L[ℝ] E →L[ℝ] ℝ) (L : E' ≃L[ℝ] E) :
    (quadForm (H.bilinearComp (L : E' →L[ℝ] E) (L : E' →L[ℝ] E))).Equivalent (quadForm H) :=
  ⟨{ toLinearEquiv := L.toLinearEquiv
     map_app' := fun m => by simp }⟩

/-- The index is invariant under a linear change of variables. -/
theorem index_bilinearComp (H : E →L[ℝ] E →L[ℝ] ℝ) (L : E' ≃L[ℝ] E) :
    index (H.bilinearComp (L : E' →L[ℝ] E) (L : E' →L[ℝ] E)) = index H :=
  (quadForm_bilinearComp_equivalent H L).sigNeg_eq

/-- Non-degeneracy is invariant under a linear change of variables. -/
theorem isNondegenerate_bilinearComp_iff (H : E →L[ℝ] E →L[ℝ] ℝ) (L : E' ≃L[ℝ] E) :
    IsNondegenerate (H.bilinearComp (L : E' →L[ℝ] E) (L : E' →L[ℝ] E)) ↔ IsNondegenerate H := by
  simp only [isNondegenerate_iff, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearEquiv.coe_coe]
  constructor
  · intro h u hu
    have := h (L.symm u) (fun w => by simpa using hu (L w))
    simpa using congrArg L this
  · intro h v hv
    have : L v = 0 := h (L v) (fun z => by simpa using hv (L.symm z))
    simpa using congrArg L.symm this

/-- The index of a bilinear form is unchanged by a positive scalar factor. -/
theorem index_smul {c : ℝ} (hc : 0 < c) (H : E →L[ℝ] E →L[ℝ] ℝ) : index (c • H) = index H := by
  have hs : Real.sqrt c ≠ 0 := (Real.sqrt_pos.2 hc).ne'
  refine QuadraticMap.Equivalent.sigNeg_eq ⟨{ toLinearEquiv := LinearEquiv.smulOfNeZero ℝ E _ hs
                                              map_app' := fun m => ?_ }⟩
  have h2 : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
  change H ((LinearEquiv.smulOfNeZero ℝ E _ hs) m) ((LinearEquiv.smulOfNeZero ℝ E _ hs) m) =
    (c • H) m m
  simp only [LinearEquiv.smulOfNeZero_apply, map_smul, smul_apply, smul_eq_mul]
  rw [← mul_assoc, h2]

/-- Non-degeneracy is unchanged by a nonzero scalar factor. -/
theorem isNondegenerate_smul_iff {c : ℝ} (hc : c ≠ 0) (H : E →L[ℝ] E →L[ℝ] ℝ) :
    IsNondegenerate (c • H) ↔ IsNondegenerate H := by
  simp only [isNondegenerate_iff, smul_apply, smul_eq_mul, mul_eq_zero, hc, false_or]

/-! ### Independence of the coordinate system -/

/-- **The Hessian at a critical point transforms as a bilinear form.**  If `ψ` is `C²` at `q`,
`f` is `C²` at `ψ q` and `ψ q` is a critical point of `f`, then
`d²(f ∘ ψ)_q(v, w) = d²f_{ψ q}(dψ_q v, dψ_q w)`.  (The second term of the chain rule,
`df_{ψ q}(d²ψ_q(v, w))`, vanishes because `df_{ψ q} = 0`.) -/
theorem hessian_comp {f : E → ℝ} {ψ : E' → E} {q : E'} (hf : ContDiffAt ℝ 2 f (ψ q))
    (hψ : ContDiffAt ℝ 2 ψ q) (hcrit : fderiv ℝ f (ψ q) = 0) (v w : E') :
    hessian (f ∘ ψ) q v w = hessian f (ψ q) (fderiv ℝ ψ q v) (fderiv ℝ ψ q w) := by
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
  simp [hcrit]

/-- **Non-degeneracy does not depend on the coordinate system** (Milnor, p. 4): if `ψ` is `C²`
at `q` with invertible derivative `L = dψ_q`, then `q` is a non-degenerate critical point of
`f ∘ ψ` iff `ψ q` is one of `f`. -/
theorem isNondegenerate_hessian_comp_iff {f : E → ℝ} {ψ : E' → E} {q : E'}
    (hf : ContDiffAt ℝ 2 f (ψ q)) (hψ : ContDiffAt ℝ 2 ψ q) (hcrit : fderiv ℝ f (ψ q) = 0)
    (L : E' ≃L[ℝ] E) (hL : fderiv ℝ ψ q = L) :
    IsNondegenerate (hessian (f ∘ ψ) q) ↔ IsNondegenerate (hessian f (ψ q)) := by
  have : hessian (f ∘ ψ) q = (hessian f (ψ q)).bilinearComp (L : E' →L[ℝ] E) (L : E' →L[ℝ] E) := by
    ext v w
    rw [hessian_comp hf hψ hcrit, hL]
    rfl
  rw [this, isNondegenerate_bilinearComp_iff]

/-- **The index does not depend on the coordinate system.** -/
theorem index_hessian_comp {f : E → ℝ} {ψ : E' → E} {q : E'}
    (hf : ContDiffAt ℝ 2 f (ψ q)) (hψ : ContDiffAt ℝ 2 ψ q) (hcrit : fderiv ℝ f (ψ q) = 0)
    (L : E' ≃L[ℝ] E) (hL : fderiv ℝ ψ q = L) :
    index (hessian (f ∘ ψ) q) = index (hessian f (ψ q)) := by
  have : hessian (f ∘ ψ) q = (hessian f (ψ q)).bilinearComp (L : E' →L[ℝ] E) (L : E' →L[ℝ] E) := by
    ext v w
    rw [hessian_comp hf hψ hcrit, hL]
    rfl
  rw [this, index_bilinearComp]

/-! ### The matrix criterion -/

/-- **Milnor's matrix criterion** (p. 4): in coordinates on `ℝⁿ`, a symmetric bilinear form `H`
is non-degenerate iff its matrix `(H(eᵢ, eⱼ))` is non-singular. -/
theorem isNondegenerate_iff_det_ne_zero {n : ℕ}
    (H : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) (hH : ∀ v w, H v w = H w v) :
    IsNondegenerate H ↔ (Matrix.of fun i j => H (Pi.single i 1) (Pi.single j 1)).det ≠ 0 := by
  set B : LinearMap.BilinForm ℝ (Fin n → ℝ) := ContinuousLinearMap.toLinearMap₁₂ H
  have hmat : LinearMap.BilinForm.toMatrix (Pi.basisFun ℝ (Fin n)) B =
      Matrix.of fun i j => H (Pi.single i 1) (Pi.single j 1) := by
    ext i j
    simp [B, LinearMap.BilinForm.toMatrix_apply]
  rw [← hmat, ← LinearMap.BilinForm.nondegenerate_iff_det_ne_zero]
  have hsep : IsNondegenerate H ↔ B.SeparatingLeft := by
    rw [isNondegenerate_iff]
    rfl
  rw [hsep]
  constructor
  · intro h
    refine ⟨h, fun y hy => h y fun x => ?_⟩
    have := hy x
    change H x y = 0 at this
    change H y x = 0
    rwa [hH]
  · exact fun h => h.1

/-- **Milnor's definition of a non-degenerate critical point** (p. 4), for `f` of class `C²` on
`ℝⁿ`: the matrix `(∂²f/∂xⁱ∂xʲ(p)) = (d²f_p(eᵢ, eⱼ))` is non-singular. -/
theorem isNondegenerate_hessian_iff_det_ne_zero {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    {p : Fin n → ℝ} (hf : ContDiffAt ℝ 2 f p) :
    IsNondegenerate (hessian f p) ↔
      (Matrix.of fun i j => hessian f p (Pi.single i 1) (Pi.single j 1)).det ≠ 0 :=
  isNondegenerate_iff_det_ne_zero _ (hessian_symm hf)

/-! ### Corollary 2.3 -/

/-- **Non-degenerate critical points are isolated**, general form: if `f` is `C²` at `p` and the
Hessian `d²f_p` is non-degenerate (`E` finite-dimensional), then no point `x ≠ p` close enough to
`p` is a critical point of `f`.  (That `p` itself is critical is not needed.) -/
theorem eventually_not_isCriticalPoint [FiniteDimensional ℝ E] {f : E → ℝ} {p : E}
    (hf : ContDiffAt ℝ 2 f p) (hnd : IsNondegenerate (hessian f p)) :
    ∀ᶠ x in 𝓝[≠] p, ¬ IsCriticalPoint f x := by
  have hd : HasFDerivAt (fderiv ℝ f) (hessian f p) p :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  obtain ⟨K, -, hK⟩ :=
    LinearMap.exists_antilipschitzWith (hessian f p : E →ₗ[ℝ] E →L[ℝ] ℝ) hnd
  filter_upwards [hd.eventually_ne (c := 0) ⟨K, hK⟩] with x hx hcrit
  exact hx hcrit.fderiv_eq

/-- **Corollary 2.3** (Milnor, p. 8): *non-degenerate critical points are isolated.*  A
non-degenerate critical point `p` of a function `f` of class `C²` at `p` (`E` finite-dimensional)
has a neighbourhood in which it is the only critical point. -/
theorem IsNondegenerateCriticalPoint.exists_nhds_isCriticalPoint_eq [FiniteDimensional ℝ E]
    {f : E → ℝ} {p : E} (hf : ContDiffAt ℝ 2 f p) (hp : IsNondegenerateCriticalPoint f p) :
    ∃ U ∈ 𝓝 p, ∀ x ∈ U, IsCriticalPoint f x ↔ x = p := by
  have h := eventually_nhdsWithin_iff.1 (eventually_not_isCriticalPoint hf hp.2)
  refine ⟨_, h, fun x hx => ⟨fun hcrit => ?_, fun hxp => hxp ▸ hp.1⟩⟩
  by_contra hxp
  exact hx hxp hcrit

end Morse
