import Milnor.Chapter1.InverseFunction
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas
import Morse.Chapter1.Nondegenerate

/-!
Milnor, *Morse Theory*, §2, pp. 6–8 (infrastructure for the proof of Lemma 2.2).

# A smooth "square root" of a family of bilinear forms

The heart of Milnor's proof of the Morse lemma (p. 7) is the inductive step: given
`f = ±(u₁)² ± ⋯ ± (u_{r-1})² + ∑_{i,j ≥ r} uᵢ uⱼ Hᵢⱼ(u)` with `(Hᵢⱼ)` symmetric, he makes
`H_rr(0) ≠ 0` by a linear change of the last coordinates, takes `g = √|H_rr|`, completes the
square with `v_r = g · [u_r + ∑_{i>r} uᵢ H_ir/H_rr]`, and invokes the inverse function theorem to
see that the `vᵢ` are coordinates near `0`.  This is the classical diagonalization of a quadratic
form (he cites Birkhoff–MacLane), performed with coefficients that are smooth functions.

We do not follow the induction.  We do the whole diagonalization at once, by a single application
of the inverse function theorem in the finite-dimensional space of linear maps `E →L[ℝ] E`:

> Let `B₀` be a symmetric non-degenerate bilinear form on `E`.  For every smooth family
> `x ↦ B x` of bilinear forms with `B 0 = B₀` there is a smooth family `x ↦ C x` of linear maps,
> defined near `0`, with `C 0 = id` and `B x (v, v) = B₀ (C x v, C x v)` for all `v`.
> (`Morse.exists_sqrt_family`)

When `B x` is symmetric, `C x` is a "square root" of `B x` relative to `B₀`.  Applied to the
`B` of Hadamard's lemma (`f x = B x (x, x)`) it gives Milnor's coordinates at one stroke:
`f x = B₀ (C x x, C x x)`, and `x ↦ C x x` has derivative `C 0 = id` at `0`
(see `Morse/Chapter1/MorseLemma.lean`).

**The map.**  Consider `Ψ : (E →L[ℝ] E) → {bilinear forms on E}`,
`Ψ(T) = B₀(T·, T·) + B₀(T·, ·) − B₀(·, T·)`.  It is polynomial, `Ψ(id) = B₀`, and its derivative
at `id` is `H ↦ 2 B₀(H·, ·)`, which is an isomorphism because `B₀` is non-degenerate (both spaces
have dimension `n²`).  By the inverse function theorem `Ψ` has a smooth local inverse near `B₀`,
and `C x = Ψ⁻¹(B x)` works: on the diagonal the last two terms of `Ψ` cancel (`B₀` is
symmetric), so `B x (v, v) = Ψ(C x)(v, v) = B₀(C x v, C x v)`.  The added term
`B₀(T·, ·) − B₀(·, T·)` (skew-symmetric, invisible on the diagonal) is there only to make the
derivative invertible; without it the derivative `H ↦ B₀(H·, ·) + B₀(·, H·)` would kill every
`B₀`-skew `H`.

## Main results

* `Morse.exists_openPartialHomeomorph_of_contDiffOn`: the inverse function theorem in the form
  used twice in this project: a map `C^n` on an open set with invertible derivative at `a`
  restricts to a partial homeomorphism around `a` which is `C^n` with `C^n` inverse.  (Mathlib's
  `ContDiffAt.toOpenPartialHomeomorph` only gives smoothness of the inverse at `f a`.  The proof
  follows the Euclidean core of the sister project's manifold inverse function theorem
  `Milnor.isLocalDiffeomorphAt_of_isInvertible_mfderiv`, and uses its lemma
  `Milnor.eventually_isInvertible_fderiv`.)
* `Morse.dualEquiv`: a non-degenerate bilinear form on a finite-dimensional space as an
  isomorphism `E ≃L[ℝ] (E →L[ℝ] ℝ)`.
* `Morse.exists_sqrt_family`: the statement above.
-/

open Set Filter Topology
open scoped ContDiff

noncomputable section

namespace Morse

/-! ### The inverse function theorem with a smooth inverse on the whole target -/

section IFT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Inverse function theorem, with a smooth inverse on the whole target.**  If `f` is `C^n`
(`n ≠ 0`) on an open set `U ∋ a` and has an invertible derivative `f'` at `a`, then `f`
restricts to a partial homeomorphism `Φ` with `a ∈ Φ.source ⊆ U`, `Φ` of class `C^n` on its
source and `Φ.symm` of class `C^n` on its target. -/
theorem exists_openPartialHomeomorph_of_contDiffOn {f : E → F} {U : Set E} (hU : IsOpen U)
    {a : E} (ha : a ∈ U) {n : WithTop ℕ∞} (hn : n ≠ 0) (hf : ContDiffOn ℝ n f U)
    {f' : E ≃L[ℝ] F} (hf' : HasFDerivAt f (f' : E →L[ℝ] F) a) :
    ∃ Φ : OpenPartialHomeomorph E F, (Φ : E → F) = f ∧ a ∈ Φ.source ∧ Φ.source ⊆ U ∧
      ContDiffOn ℝ n Φ Φ.source ∧ ContDiffOn ℝ n Φ.symm Φ.target := by
  have hfa : ContDiffAt ℝ n f a := hf.contDiffAt (hU.mem_nhds ha)
  set Φ₀ := hfa.toOpenPartialHomeomorph f hf' hn with hΦ₀
  have hinv : (fderiv ℝ f a).IsInvertible := ⟨f', hf'.fderiv.symm⟩
  have hev := Milnor.eventually_isInvertible_fderiv hfa hn hinv
  set V := U ∩ Φ₀.source ∩ interior {x | (fderiv ℝ f x).IsInvertible} with hV
  have hVo : IsOpen V := (hU.inter Φ₀.open_source).inter isOpen_interior
  have haV : a ∈ V :=
    ⟨⟨ha, hfa.mem_toOpenPartialHomeomorph_source hf' hn⟩, mem_interior_iff_mem_nhds.2 hev⟩
  have hsrc : (Φ₀.restrOpen V hVo).source = Φ₀.source ∩ V := Φ₀.restrOpen_source V hVo
  refine ⟨Φ₀.restrOpen V hVo, rfl, ?_, ?_, ?_, ?_⟩
  · rw [hsrc]
    exact ⟨haV.1.2, haV⟩
  · rw [hsrc]
    exact fun x hx => hx.2.1.1
  · rw [hsrc]
    exact hf.mono fun x hx => hx.2.1.1
  · intro b hb
    set Φ := Φ₀.restrOpen V hVo
    have hxs : Φ.symm b ∈ Φ.source := Φ.map_target hb
    rw [hsrc] at hxs
    have hsymm : Φ.symm b = Φ₀.symm b := rfl
    rw [hsymm] at hxs
    have hbΦ₀ : b ∈ Φ₀.target := by
      have h1 : Φ₀ (Φ₀.symm b) = b := Φ.right_inv hb
      rw [← h1]
      exact Φ₀.map_source hxs.1
    have hxU : Φ₀.symm b ∈ U := hxs.2.1.1
    have hfx : ContDiffAt ℝ n f (Φ₀.symm b) := hf.contDiffAt (hU.mem_nhds hxU)
    have hI : Φ₀.symm b ∈ {x | (fderiv ℝ f x).IsInvertible} := interior_subset hxs.2.2
    obtain ⟨e, he⟩ := hI
    have hd : HasFDerivAt f (e : E →L[ℝ] F) (Φ₀.symm b) := by
      rw [he]; exact (hfx.differentiableAt hn).hasFDerivAt
    exact (Φ₀.contDiffAt_symm hbΦ₀ hd hfx).contDiffWithinAt

end IFT

/-! ### The map `Ψ` -/

section SquareRoot

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Precomposition `T ↦ (φ ↦ φ ∘ T)`, the transpose map `E →L[ℝ] E → (E* →L[ℝ] E*)`. -/
def precomp : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ E E ℝ).flip

/-- The auxiliary map `Ψ(T) = B₀(T·, T·) + B₀(T·, ·) − B₀(·, T·)`, written with compositions of
linear maps (`Tᵀ ∘ B₀ ∘ T + B₀ ∘ T − Tᵀ ∘ B₀`, where `B₀` is viewed as a map `E → E*` and
`Tᵀ = precomp T`) so that its smoothness is immediate. -/
def sqrtAux (B₀ : E →L[ℝ] E →L[ℝ] ℝ) (T : E →L[ℝ] E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (precomp T).comp (B₀.comp T) + B₀.comp T - (precomp T).comp B₀

variable (B₀ : E →L[ℝ] E →L[ℝ] ℝ)

theorem sqrtAux_apply (T : E →L[ℝ] E) (u v : E) :
    sqrtAux B₀ T u v = B₀ (T u) (T v) + B₀ (T u) v - B₀ u (T v) := by
  simp [sqrtAux, precomp]

/-- On the diagonal, `Ψ(T)(v, v) = B₀(T v, T v)` (`B₀` symmetric). -/
theorem sqrtAux_apply_self {B₀ : E →L[ℝ] E →L[ℝ] ℝ} (hsymm : ∀ u v, B₀ u v = B₀ v u)
    (T : E →L[ℝ] E) (v : E) : sqrtAux B₀ T v v = B₀ (T v) (T v) := by
  rw [sqrtAux_apply, hsymm v (T v)]
  ring

theorem sqrtAux_id : sqrtAux B₀ (ContinuousLinearMap.id ℝ E) = B₀ := by
  ext u v
  simp [sqrtAux_apply]

theorem contDiff_sqrtAux : ContDiff ℝ ∞ (sqrtAux B₀) := by
  have hP : ContDiff ℝ ∞ (fun T : E →L[ℝ] E => precomp T) := (precomp (E := E)).contDiff
  have hA : ContDiff ℝ ∞ (fun T : E →L[ℝ] E => B₀.comp T) :=
    (ContinuousLinearMap.compL ℝ E E (E →L[ℝ] ℝ) B₀).contDiff
  exact ((hP.clm_comp hA).add hA).sub (hP.clm_comp contDiff_const)

/-- The derivative of `Ψ` at `id`: `H ↦ 2 B₀(H·, ·)`. -/
def sqrtAuxDeriv : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
  (2 : ℝ) • ContinuousLinearMap.compL ℝ E E (E →L[ℝ] ℝ) B₀

theorem sqrtAuxDeriv_apply (H : E →L[ℝ] E) (u v : E) :
    sqrtAuxDeriv B₀ H u v = 2 * B₀ (H u) v := by
  simp [sqrtAuxDeriv]

theorem hasFDerivAt_sqrtAux :
    HasFDerivAt (sqrtAux B₀) (sqrtAuxDeriv B₀) (ContinuousLinearMap.id ℝ E) := by
  set I := ContinuousLinearMap.id ℝ E with hI
  have hP : HasFDerivAt (fun T : E →L[ℝ] E => precomp T) (precomp (E := E)) I :=
    (precomp (E := E)).hasFDerivAt
  have hA : HasFDerivAt (fun T : E →L[ℝ] E => B₀.comp T)
      (ContinuousLinearMap.compL ℝ E E (E →L[ℝ] ℝ) B₀) I :=
    (ContinuousLinearMap.compL ℝ E E (E →L[ℝ] ℝ) B₀).hasFDerivAt
  have h := ((hP.clm_comp hA).add hA).sub (hP.clm_comp (hasFDerivAt_const B₀ I))
  refine h.congr_fderiv ?_
  ext H u v
  simp [sqrtAuxDeriv, precomp, hI]
  ring

/-! ### The derivative of `Ψ` is invertible -/

variable [FiniteDimensional ℝ E]

theorem finrank_dual_eq : Module.finrank ℝ (E →L[ℝ] ℝ) = Module.finrank ℝ E := by
  rw [← (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] E →L[ℝ] ℝ).finrank_eq]
  exact Subspace.dual_finrank_eq

variable {B₀}

/-- A non-degenerate bilinear form `B₀` on a finite-dimensional space, as an isomorphism
`v ↦ B₀ v` from `E` onto its dual. -/
def dualEquiv (hnd : IsNondegenerate B₀) : E ≃L[ℝ] (E →L[ℝ] ℝ) :=
  (LinearEquiv.ofBijective (B₀ : E →ₗ[ℝ] E →L[ℝ] ℝ)
    ⟨LinearMap.ker_eq_bot.1 hnd,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank finrank_dual_eq.symm).1
        (LinearMap.ker_eq_bot.1 hnd)⟩).toContinuousLinearEquiv

@[simp] theorem dualEquiv_apply (hnd : IsNondegenerate B₀) (v : E) : dualEquiv hnd v = B₀ v :=
  rfl

/-- The derivative `H ↦ 2 B₀(H·, ·)` of `Ψ` at `id`, as an isomorphism; its inverse is
`S ↦ ½ B₀⁻¹ ∘ S`. -/
def sqrtAuxDerivEquiv (hnd : IsNondegenerate B₀) :
    (E →L[ℝ] E) ≃L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearEquiv.equivOfInverse (sqrtAuxDeriv B₀)
    ((2 : ℝ)⁻¹ • ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E
      ((dualEquiv hnd).symm : (E →L[ℝ] ℝ) →L[ℝ] E))
    (fun H => by
      ext u
      have h : (dualEquiv hnd).symm (B₀ (H u)) = H u := by
        rw [← dualEquiv_apply hnd (H u), ContinuousLinearEquiv.symm_apply_apply]
      simp [sqrtAuxDeriv, h])
    (fun S => by
      ext u v
      have h : B₀ ((dualEquiv hnd).symm (S u)) = S u := by
        rw [← dualEquiv_apply hnd, ContinuousLinearEquiv.apply_symm_apply]
      simp [sqrtAuxDeriv, h])

@[simp] theorem coe_sqrtAuxDerivEquiv (hnd : IsNondegenerate B₀) :
    (sqrtAuxDerivEquiv hnd : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ)) = sqrtAuxDeriv B₀ :=
  rfl

/-! ### The square root -/

/-- **A smooth "square root" of a family of bilinear forms.**  Let `B₀` be a symmetric
non-degenerate bilinear form on a finite-dimensional space `E`, and `x ↦ B x` a family of
bilinear forms, smooth on an open set `U ∋ 0`, with `B 0 = B₀`.  Then there are an open
`W ∋ 0`, `W ⊆ U`, and a family `x ↦ C x` of linear maps, smooth on `W`, with `C 0 = id` and
`B x (v, v) = B₀ (C x v, C x v)` for `x ∈ W` and all `v`. -/
theorem exists_sqrt_family (hsymm : ∀ u v, B₀ u v = B₀ v u) (hnd : IsNondegenerate B₀)
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {U : Set E} (hU : IsOpen U) (h0U : (0 : E) ∈ U)
    (hB : ContDiffOn ℝ ∞ B U) (hB0 : B 0 = B₀) :
    ∃ C : E → E →L[ℝ] E, ∃ W : Set E, IsOpen W ∧ (0 : E) ∈ W ∧ W ⊆ U ∧
      ContDiffOn ℝ ∞ C W ∧ C 0 = ContinuousLinearMap.id ℝ E ∧
      ∀ x ∈ W, ∀ v, B x v v = B₀ (C x v) (C x v) := by
  obtain ⟨Φ, hΦ, hidΦ, -, -, hΦs⟩ := exists_openPartialHomeomorph_of_contDiffOn isOpen_univ
    (mem_univ (ContinuousLinearMap.id ℝ E)) (by simp) (contDiff_sqrtAux B₀).contDiffOn
    (f' := sqrtAuxDerivEquiv hnd) (by simpa using hasFDerivAt_sqrtAux B₀)
  have hB₀ : Φ (ContinuousLinearMap.id ℝ E) = B₀ := by rw [hΦ, sqrtAux_id]
  have hB₀t : B₀ ∈ Φ.target := hB₀ ▸ Φ.map_source hidΦ
  set W := U ∩ B ⁻¹' Φ.target with hW
  have hWo : IsOpen W := hB.continuousOn.isOpen_inter_preimage hU Φ.open_target
  refine ⟨fun x => Φ.symm (B x), W, hWo, ⟨h0U, by simpa [hB0] using hB₀t⟩, inter_subset_left,
    ?_, ?_, ?_⟩
  · exact hΦs.comp (hB.mono inter_subset_left) fun x hx => hx.2
  · change Φ.symm (B 0) = _
    rw [hB0, ← hB₀]
    exact Φ.left_inv hidΦ
  · intro x hx v
    have h : Φ (Φ.symm (B x)) = B x := Φ.right_inv hx.2
    rw [hΦ] at h
    rw [← sqrtAux_apply_self hsymm, h]

end SquareRoot

end Morse
