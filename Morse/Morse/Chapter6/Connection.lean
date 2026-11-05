import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric

/-!
Milnor, *Morse Theory*, §8 (Covariant differentiation), pp. 43–49, and the definition of the
curvature tensor in §9, p. 51.

# Milnor's connections in Mathlib's language

Mathlib (v4.33.1) has covariant derivatives on vector bundles
(`Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/{Basic,Torsion,Metric}.lean`):
`CovariantDerivative I F V`, its torsion `CovariantDerivative.torsion` (on the tangent bundle) and
the predicate `CovariantDerivative.IsMetricCompatible` (on a Riemannian bundle).  It has no
curvature, no Christoffel symbols, no covariant derivative along curves, no parallel transport
and no Levi-Civita connection.  This file matches Milnor's §8 definitions with that API where
this is cheap.

## Milnor's text (pp. 43–49, 51), paraphrased, and its Mathlib counterpart

* **Affine connection** (pp. 43–44).  An affine connection at `p` assigns to `X_p ∈ TM_p` and a
  vector field `Y` a vector `X_p ⊢ Y ∈ TM_p`, bilinear, with
  `X_p ⊢ (fY) = (X_p f)Y_p + f(p) X_p ⊢ Y`.
  A global one is a smooth family of these; then (2) `X ⊢ Y` is bilinear, (3) `(fX) ⊢ Y =
  f(X ⊢ Y)`, (4) `X ⊢ (fY) = (Xf)Y + f(X ⊢ Y)`, and Milnor remarks that (1)–(4) can be taken as
  the definition.  (Milnor's footnote: `X ⊢ Y` is Nomizu's `∇_X Y`.)
  *Mathlib*: `cov : CovariantDerivative I E (TangentSpace I : M → Type _)`, with
  `X ⊢ Y` at `x` written `cov Y x (X x)` (note the argument order).  Since `cov Y x` is a
  continuous linear map `T_xM → T_xM`, dependence on `X_p` only, linearity in `X_p` and (3) are
  built in (`Morse.cov_smul_left`); additivity in `Y` and the Leibniz rule (4) are required at
  points where the sections are differentiable (`Morse.cov_add_right`, `Morse.cov_smul_right`);
  smoothness (1) is the separate class `ContMDiffCovariantDerivative cov ∞`.
* **Christoffel symbols** (p. 44, formulas (5), (6)), **covariant derivative along a curve**
  (Lemma 8.1, p. 46) and **parallel transport** (Lemma 8.2, p. 47): not in Mathlib; not
  formalized.
* **Compatibility with the metric** (p. 47).  Milnor's definition: parallel translation preserves
  inner products.  This cannot be stated without parallel transport.  Its consequence
  **Corollary 8.4** (p. 48), `X_p⟨Y, Y'⟩ = ⟨X_p ⊢ Y, Y'_p⟩ + ⟨Y_p, X_p ⊢ Y'⟩`, is Mathlib's
  definition: `Morse.IsCompatible` (Milnor's formula for vector fields differentiable at the
  point) is equivalent to `CovariantDerivative.IsMetricCompatible`
  (`Morse.isCompatible_iff_isMetricCompatible`).
* **Symmetric connection** (Definition 8.5, p. 48): `X ⊢ Y − Y ⊢ X = [X, Y]`.  Mathlib's Lie
  bracket `VectorField.mlieBracket` has Milnor's sign (`[X, Y]f = X(Yf) − Y(Xf)`), and its torsion
  is `T(X, Y) = ∇_X Y − ∇_Y X − [X, Y]`, so `Morse.IsSymmetric cov ↔ cov.torsion = 0`
  (`Morse.isSymmetric_iff_torsion_eq_zero`).
* **Lemma 8.6** (fundamental lemma, p. 48): a Riemannian manifold has one and only one symmetric
  connection compatible with its metric.  *Uniqueness* is proved here
  (`Morse.cov_eq_of_isSymmetric_of_isCompatible`), via the Koszul formula
  `2⟨∇_X Y, Z⟩ = X⟨Y, Z⟩ + Y⟨X, Z⟩ − Z⟨X, Y⟩ + ⟨[X, Y], Z⟩ − ⟨[X, Z], Y⟩ − ⟨[Y, Z], X⟩`
  (`Morse.two_mul_inner_cov_eq_koszul`), the coordinate-free form of Milnor's first Christoffel
  identity (take `X, Y, Z` coordinate fields, whose brackets vanish).  *Existence* is not proved:
  Mathlib has no Levi-Civita connection, and building it needs either Christoffel symbols in
  charts with patching (Milnor's route) or the Koszul formula with tensoriality in `Z`.
* **The curvature tensor** (p. 51): `R(X, Y)Z = −X ⊢ (Y ⊢ Z) + Y ⊢ (X ⊢ Z) + [X, Y] ⊢ Z`
  (`Morse.milnorCurvature`), the negative of Nomizu's
  `∇_X∇_Y Z − ∇_Y∇_X Z − ∇_{[X,Y]}Z` (`Morse.nomizuCurvature`, `Morse.milnorCurvature_eq_neg`).
  Only Lemma 9.3 (1) is proved at the level of vector fields (`Morse.milnorCurvature_swap`); the
  tensor property (Lemma 9.1) and (2)–(4) of Lemma 9.3 are not (for (4) and the sectional
  curvature, see the algebra in `Morse/Chapter6/CurvatureAlgebra.lean`).

## What Milnor leaves implicit (recorded here; see the exposition, Chapter 6)

* The uniqueness in Lemma 8.6 is for sections differentiable at the point: a Mathlib
  `CovariantDerivative` is a function on *all* sections and is unconstrained on non-differentiable
  ones, so two Levi-Civita connections agree on differentiable sections (which is all Milnor
  uses), not as functions.
* Milnor's misprint on p. 49: the three unknowns of the linear system are
  `⟨∂_i ⊢ ∂_j, ∂_k⟩`, `⟨∂_i ⊢ ∂_k, ∂_j⟩`, `⟨∂_j ⊢ ∂_k, ∂_i⟩` (the printed second one equals the
  first by symmetry).  The Koszul formula avoids coordinates.
* Milnor's "Conversely ... the resulting connection is compatible with the metric" (p. 49) needs
  the converse of Lemma 8.3, which he does not state; it is part of the missing existence half.
-/

open Bundle Manifold VectorField FiberBundle
open scoped ContDiff

noncomputable section

namespace Morse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### Milnor's rules (2)–(4) for Mathlib's covariant derivatives -/

section Rules

variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

/-- **Milnor's rule (3)** (p. 44): `(fX) ⊢ Y = f (X ⊢ Y)`. -/
theorem cov_smul_left (f : M → ℝ) (X Y : Π x : M, TangentSpace I x) (x : M) :
    cov Y x (f x • X x) = f x • cov Y x (X x) :=
  map_smul _ _ _

/-- **Milnor's rule (2)**, additivity in `Y`, for vector fields differentiable at the point. -/
theorem cov_add_right {Y Y' : Π x : M, TangentSpace I x} {x : M} (hY : MDiffAt (T% Y) x)
    (hY' : MDiffAt (T% Y') x) (X : Π x : M, TangentSpace I x) :
    cov (Y + Y') x (X x) = cov Y x (X x) + cov Y' x (X x) := by
  rw [cov.isCovariantDerivativeOnUniv.add hY hY']
  rfl

/-- **Milnor's rule (4)** (p. 44), the Leibniz rule: `X ⊢ (fY) = (Xf) Y + f (X ⊢ Y)`, for `f` and
`Y` differentiable at the point. -/
theorem cov_smul_right {f : M → ℝ} {Y : Π x : M, TangentSpace I x} {x : M}
    (hf : MDiffAt f x) (hY : MDiffAt (T% Y) x) (X : Π x : M, TangentSpace I x) :
    cov (f • Y) x (X x) = mvfderiv I f x (X x) • Y x + f x • cov Y x (X x) := by
  rw [cov.isCovariantDerivativeOnUniv.leibniz hY hf]
  simp [add_comm]

end Rules

/-! ### Symmetric connections -/

section Symmetric

variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

/-- **Symmetric connection** (Milnor, Definition 8.5, p. 48): `X ⊢ Y − Y ⊢ X = [X, Y]` for all
vector fields `X, Y` (differentiable at the point where the identity is evaluated). -/
def IsSymmetric : Prop :=
  ∀ (X Y : Π x : M, TangentSpace I x) (x : M), MDiffAt (T% X) x → MDiffAt (T% Y) x →
    cov Y x (X x) - cov X x (Y x) = mlieBracket I X Y x

/-- Milnor's symmetric connections are Mathlib's torsion-free ones. -/
theorem isSymmetric_iff_torsion_eq_zero [FiniteDimensional ℝ E] :
    IsSymmetric cov ↔ cov.torsion = 0 := by
  rw [CovariantDerivative.torsion_eq_zero_iff]
  exact ⟨fun h X Y x hX hY => h X Y x hX hY, fun h X Y x hX hY => h hX hY⟩

end Symmetric

/-! ### The curvature tensor and its sign -/

section Curvature

variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

/-- **Milnor's curvature** (p. 51), on vector fields:
`R(X, Y)Z = −X ⊢ (Y ⊢ Z) + Y ⊢ (X ⊢ Z) + [X, Y] ⊢ Z`. -/
def milnorCurvature (X Y Z : Π x : M, TangentSpace I x) (x : M) : TangentSpace I x :=
  -cov (fun y => cov Z y (Y y)) x (X x) + cov (fun y => cov Z y (X y)) x (Y x) +
    cov Z x (mlieBracket I X Y x)

/-- **Nomizu's curvature** (the common modern convention):
`∇_X∇_Y Z − ∇_Y∇_X Z − ∇_{[X,Y]}Z`. -/
def nomizuCurvature (X Y Z : Π x : M, TangentSpace I x) (x : M) : TangentSpace I x :=
  cov (fun y => cov Z y (Y y)) x (X x) - cov (fun y => cov Z y (X y)) x (Y x) -
    cov Z x (mlieBracket I X Y x)

/-- **Milnor's footnote on p. 51**: Nomizu gives `R` the opposite sign. -/
theorem milnorCurvature_eq_neg (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    milnorCurvature cov X Y Z x = -nomizuCurvature cov X Y Z x := by
  simp only [milnorCurvature, nomizuCurvature]
  abel

/-- **Lemma 9.3 (1)** (p. 53), for vector fields: `R(Y, X)Z = −R(X, Y)Z`. -/
theorem milnorCurvature_swap (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    milnorCurvature cov Y X Z x = -milnorCurvature cov X Y Z x := by
  simp only [milnorCurvature]
  rw [mlieBracket_swap]
  simp only [Pi.neg_apply, map_neg]
  abel

end Curvature

/-! ### Riemannian manifolds: compatibility and the uniqueness half of Lemma 8.6 -/

section Riemannian

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

/-- **Compatibility with the metric, in the form of Milnor's Corollary 8.4** (p. 48):
`X_p⟨Y, Y'⟩ = ⟨X_p ⊢ Y, Y'_p⟩ + ⟨Y_p, X_p ⊢ Y'⟩`, for vector fields differentiable at `p`.
(Milnor's definition, "parallel translation preserves inner products" (p. 47), needs parallel
transport, which Mathlib does not have.) -/
def IsCompatible : Prop :=
  ∀ (X Y Y' : Π x : M, TangentSpace I x) (x : M),
    MDiffAt (T% X) x → MDiffAt (T% Y) x → MDiffAt (T% Y') x →
      mvfderiv I (fun y => inner ℝ (Y y) (Y' y)) x (X x) =
        inner ℝ (cov Y x (X x)) (Y' x) + inner ℝ (Y x) (cov Y' x (X x))

/-- Milnor's Corollary 8.4 is Mathlib's definition of a metric connection. -/
theorem isCompatible_iff_isMetricCompatible [FiniteDimensional ℝ E]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] :
    IsCompatible cov ↔ cov.IsMetricCompatible (F := E) (V := fun x : M ↦ TangentSpace I x) := by
  rw [CovariantDerivative.isMetricCompatible_iff]
  exact ⟨fun h x X σ τ hX hσ hτ => h X σ τ x hX hσ hτ, fun h X Y Y' x hX hY hY' => h hX hY hY'⟩

/-- The right-hand side of the Koszul formula,
`X⟨Y, Z⟩ + Y⟨X, Z⟩ − Z⟨X, Y⟩ + ⟨[X, Y], Z⟩ − ⟨[X, Z], Y⟩ − ⟨[Y, Z], X⟩` at `x`.  It involves only
the metric and the Lie bracket. -/
def koszul (X Y Z : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  mvfderiv I (fun y => inner ℝ (Y y) (Z y)) x (X x) +
    mvfderiv I (fun y => inner ℝ (X y) (Z y)) x (Y x) -
    mvfderiv I (fun y => inner ℝ (X y) (Y y)) x (Z x) +
    inner ℝ (mlieBracket I X Y x) (Z x) - inner ℝ (mlieBracket I X Z x) (Y x) -
    inner ℝ (mlieBracket I Y Z x) (X x)

/-- **The Koszul formula**: for a symmetric connection compatible with the metric,
`2⟨X ⊢ Y, Z⟩ = koszul X Y Z` at every point where `X, Y, Z` are differentiable.  With coordinate
fields it is Milnor's first Christoffel identity (p. 49). -/
theorem two_mul_inner_cov_eq_koszul (hS : IsSymmetric cov) (hC : IsCompatible cov)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    2 * inner ℝ (cov Y x (X x)) (Z x) = koszul X Y Z x := by
  rw [koszul, hC X Y Z x hX hY hZ, hC Y X Z x hY hX hZ, hC Z X Y x hZ hX hY,
    ← hS X Y x hX hY, ← hS X Z x hX hZ, ← hS Y Z x hY hZ]
  simp only [inner_sub_left, inner_sub_right, real_inner_comm (Y x), real_inner_comm (X x)]
  ring

/-- **Lemma 8.6, uniqueness** (p. 48): a Riemannian manifold has at most one symmetric connection
compatible with its metric.  Two such connections agree on every vector field differentiable at
the point. -/
theorem cov_eq_of_isSymmetric_of_isCompatible
    (cov' : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hS : IsSymmetric cov) (hC : IsCompatible cov) (hS' : IsSymmetric cov')
    (hC' : IsCompatible cov') {Y : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) : cov Y x = cov' Y x := by
  ext X₀
  have hX := mdifferentiableAt_extend I E X₀
  have hZ := mdifferentiableAt_extend I E (cov Y x X₀ - cov' Y x X₀)
  have h1 := two_mul_inner_cov_eq_koszul cov hS hC hX hY hZ
  have h2 := two_mul_inner_cov_eq_koszul cov' hS' hC' hX hY hZ
  simp only [extend_apply_self] at h1 h2
  have h3 : inner ℝ (cov Y x X₀ - cov' Y x X₀) (cov Y x X₀ - cov' Y x X₀) = 0 := by
    rw [inner_sub_left]
    linarith
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h3)

/-- **Lemma 8.6, uniqueness**, with Mathlib's predicates: two torsion-free metric connections
agree on every vector field differentiable at the point. -/
theorem cov_eq_of_torsion_eq_zero_of_isMetricCompatible [FiniteDimensional ℝ E]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (cov' : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hT : cov.torsion = 0)
    (hm : cov.IsMetricCompatible (F := E) (V := fun x : M ↦ TangentSpace I x))
    (hT' : cov'.torsion = 0)
    (hm' : cov'.IsMetricCompatible (F := E) (V := fun x : M ↦ TangentSpace I x))
    {Y : Π x : M, TangentSpace I x} {x : M} (hY : MDiffAt (T% Y) x) : cov Y x = cov' Y x :=
  cov_eq_of_isSymmetric_of_isCompatible cov cov' ((isSymmetric_iff_torsion_eq_zero cov).2 hT)
    ((isCompatible_iff_isMetricCompatible cov).2 hm) ((isSymmetric_iff_torsion_eq_zero cov').2 hT')
    ((isCompatible_iff_isMetricCompatible cov').2 hm') hY

end Riemannian

end Morse
