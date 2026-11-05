import Morse
/-! Blind formalization of V13_10 (Milnor §22, Lemma 22.4, p. 120). Choices:
- Setting (finite-dimensional Morse theory, no Riemannian metric): `Rn m = EuclideanSpace ℝ (Fin m)`; abstract smooth manifolds `M : Type` (Hausdorff, `IsManifold 𝓘(ℝ, ℝᵐ) ∞`, no second countability or connectedness assumed, `m = 0` allowed), as in the earlier blind files. Critical point `IsCritM` (`df_x = 0`); Hessian `hessM` = second derivative of `f` in the preferred chart at `x`; index `idxM` = `bIndex` (maximal dimension of a negative definite subspace, Milnor's definition p. 5, `ℕ∞`-valued, defined also at degenerate critical points); `IsNondegM` = trivial null space. In `ℝᵐ`: `pd`, `pd2` (first and second partials), `hess`, `idx`. Own definitions (not the project's `indexM`, whose treatment of degenerate points is unknown to me).
- `U ⊆ ℝⁿ` open, `K ⊆ U` compact, `f, g` smooth on `U` (functions `ℝⁿ → ℝ` that are `C^∞` on `U`; values off `U` are irrelevant since all derivatives are taken at points of `K ⊆ U`), `λ₀ : ℕ` arbitrary (written `l0`), all `n` (also `n = 0`).
- Hypothesis: every critical point (`fderiv f x = 0`) of `f` in `K` has index `≥ λ₀` (index of the Hessian matrix, possibly degenerate). Conclusion: there is a constant `ε > 0` (depending on `f, K, λ₀`, not on `g`) such that every smooth `g` with `|∂g/∂x_i − ∂f/∂x_i| < ε` and `|∂²g/∂x_i∂x_j − ∂²f/∂x_i∂x_j| < ε` at every point of `K` (all `i, j`) has all its critical points in `K` of index `≥ λ₀`.
- The proof's ingredient (continuity of the `λ`-th eigenvalue of the Hessian) is not stated as a separate claim.
-/
open scoped ContDiff Manifold unitInterval
open Topology
namespace RoundTrip.V13_10

abbrev Rn (k : ℕ) := EuclideanSpace ℝ (Fin k)

section Forms
/-- `H` is negative definite on the subspace `S` (copied from the earlier blind files). -/
def IsNegDefSub {V : Type} [AddCommGroup V] [Module ℝ V] (H : V → V → ℝ) (S : Submodule ℝ V) : Prop :=
  ∀ v ∈ S, v ≠ 0 → H v v < 0

/-- Index of the form `H` on `A`: the maximal dimension of a subspace of `A` on which `H` is negative definite
(`⊤` if unbounded; copied from the earlier blind files). -/
noncomputable def bIndex {V : Type} [AddCommGroup V] [Module ℝ V] (A : Set V) (H : V → V → ℝ) : ℕ∞ :=
  ⨆ (S : Submodule ℝ V) (_ : (S : Set V) ⊆ A ∧ FiniteDimensional ℝ S ∧ IsNegDefSub H S), (Module.finrank ℝ S : ℕ∞)
end Forms

section Euclid
variable {m : ℕ}

/-- The partial derivative `∂g/∂x_i (x)`. -/
noncomputable def pd (g : Rn m → ℝ) (i : Fin m) (x : Rn m) : ℝ :=
  fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))

/-- The second partial derivative `∂²g/∂x_i∂x_j (x) = ∂/∂x_i (∂g/∂x_j) (x)`. -/
noncomputable def pd2 (g : Rn m → ℝ) (i j : Fin m) (x : Rn m) : ℝ :=
  fderiv ℝ (fun y => pd g j y) x (EuclideanSpace.single i (1 : ℝ))

/-- The Hessian of `g` at `x` as a bilinear form, `(v, w) ↦ D²g(x)(v, w)` (matrix `(∂²g/∂x_i∂x_j)`). -/
noncomputable def hess (g : Rn m → ℝ) (x : Rn m) (v w : Rn m) : ℝ :=
  fderiv ℝ (fderiv ℝ g) x v w

/-- The index of `g` at `x`: the index of its Hessian (number of negative eigenvalues of `(∂²g/∂x_i∂x_j)`),
defined also at degenerate critical points. -/
noncomputable def idx (g : Rn m → ℝ) (x : Rn m) : ℕ∞ := bIndex Set.univ (hess g x)
end Euclid

section Mfd
variable {m : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn m) M]

/-- Critical point of `f : M → ℝ` (Milnor p. 4): `df_x = 0`. -/
def IsCritM (f : M → ℝ) (x : M) : Prop := mfderiv 𝓘(ℝ, Rn m) 𝓘(ℝ, ℝ) f x = 0

/-- The Hessian of `f` at `x`, computed in the preferred chart at `x` (chart-independent at critical points up to
congruence, so its index and nondegeneracy are well defined there). -/
noncomputable def hessM (f : M → ℝ) (x : M) : Rn m → Rn m → ℝ :=
  hess (f ∘ (extChartAt 𝓘(ℝ, Rn m) x).symm) (extChartAt 𝓘(ℝ, Rn m) x x)

/-- Non-degenerate (Hessian has trivial null space). -/
def IsNondegM (f : M → ℝ) (x : M) : Prop := ∀ v : Rn m, (∀ w : Rn m, hessM (m := m) f x v w = 0) → v = 0

/-- The index of `f` at `x` (Milnor p. 5: maximal dimension of a subspace on which `f_**` is negative definite). -/
noncomputable def idxM (f : M → ℝ) (x : M) : ℕ∞ := bIndex Set.univ (hessM (m := m) f x)
end Mfd

section Htpy
/-- A topological manifold: a Hausdorff space in which every point has an open neighbourhood homeomorphic to an open
subset of some `ℝ^m` (the dimension `m` may depend on the point; no second countability is required).
(Copied from the parallel blind file V13_2.) -/
def IsTopMfd (X : Type) [TopologicalSpace X] : Prop :=
  T2Space X ∧ ∀ x : X, ∃ (m : ℕ) (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin m))), x ∈ e.source

/-- `π_i(X, A) = 0` for every base point in `A` (for `i = 0`: every path component of `X` meets `A`), in the form of the
compression criterion: every map `(I^i, ∂I^i) → (X, A)` is homotopic rel `∂I^i` to a map into `A`.
(Copied from the parallel blind file V13_2.) -/
def RelPiTrivial (X : Type) [TopologicalSpace X] (A : Set X) (i : ℕ) : Prop :=
  ∀ f : C(Fin i → unitInterval, X), (∀ y ∈ Cube.boundary (Fin i), f y ∈ A) →
    ∃ g : C(Fin i → unitInterval, X), (∀ y, g y ∈ A) ∧ f.HomotopicRel g (Cube.boundary (Fin i))

/-- `f : C(X,Y)` maps into `K ⊆ Y` and is a homotopy equivalence `X → K` (copied from the earlier blind files). -/
def IsHEOnto {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (K : Set Y) : Prop :=
  ∃ hK : ∀ x, f x ∈ K, ∃ g : C(K, X),
    (g.comp (ContinuousMap.mk (Set.codRestrict f K hK) (f.continuous.subtype_mk hK))).Homotopic (ContinuousMap.id X) ∧
    ((ContinuousMap.mk (Set.codRestrict f K hK) (f.continuous.subtype_mk hK)).comp g).Homotopic (ContinuousMap.id K)
end Htpy

/-- Lemma 22.4: if all critical points of `f` in the compact `K ⊆ U` have index `≥ λ₀`, then so do those of every smooth
`g` whose first and second partial derivatives are uniformly `ε`-close to those of `f` on `K`, for some `ε > 0`. -/
def B : Prop :=
  ∀ (n : ℕ) (U K : Set (Rn n)) (f : Rn n → ℝ) (l0 : ℕ), IsOpen U → IsCompact K → K ⊆ U → ContDiffOn ℝ ∞ f U →
    (∀ x ∈ K, fderiv ℝ f x = 0 → (l0 : ℕ∞) ≤ idx f x) →
    ∃ ε : ℝ, 0 < ε ∧ ∀ g : Rn n → ℝ, ContDiffOn ℝ ∞ g U →
      (∀ x ∈ K, ∀ i, |pd g i x - pd f i x| < ε) →
      (∀ x ∈ K, ∀ i j, |pd2 g i j x - pd2 f i j x| < ε) →
      ∀ x ∈ K, fderiv ℝ g x = 0 → (l0 : ℕ∞) ≤ idx g x

end RoundTrip.V13_10
