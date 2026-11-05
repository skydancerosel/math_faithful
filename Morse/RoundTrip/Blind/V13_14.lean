import Morse
/-! Blind formalization of V13_14 (Milnor §22, Lemma 22.5, p. 121). Choices:
- Setting (finite-dimensional Morse theory, no Riemannian metric): `Rn m = EuclideanSpace ℝ (Fin m)`; abstract smooth manifolds `M : Type` (Hausdorff, `IsManifold 𝓘(ℝ, ℝᵐ) ∞`, no second countability or connectedness assumed, `m = 0` allowed), as in the earlier blind files. Critical point `IsCritM` (`df_x = 0`); Hessian `hessM` = second derivative of `f` in the preferred chart at `x`; index `idxM` = `bIndex` (maximal dimension of a negative definite subspace, Milnor's definition p. 5, `ℕ∞`-valued, defined also at degenerate critical points); `IsNondegM` = trivial null space. In `ℝᵐ`: `pd`, `pd2` (first and second partials), `hess`, `idx`. Own definitions (not the project's `indexM`, whose treatment of degenerate points is unknown to me).
- Hypotheses: `f : M → ℝ` smooth with minimum `0` (`f ≥ 0` and `f = 0` somewhere); each `M^c = f⁻¹[0,c]` compact (all `c : ℝ`; `= {f ≤ c}` since `f ≥ 0`); the set `M⁰ = f⁻¹(0)` of minimal points is a manifold, read as a topological manifold in the subspace topology (`IsTopMfd`, copied from V13_2: Hausdorff, locally Euclidean, dimension may vary from point to point; the proof only uses Hanner's theorem, a topological statement); every critical point `x ∈ M − M⁰` (`f x ≠ 0`) has index `≥ λ₀` (`l0 : ℕ`, possibly degenerate critical points: index = maximal dimension of a negative definite subspace of the Hessian).
- Conclusion: `π_r(M, M⁰) = 0` for `0 ≤ r < λ₀`, by the same compression criterion `RelPiTrivial` as in the parallel blind file V13_2 (every map `(I^r, ∂I^r) → (M, M⁰)` is homotopic rel `∂I^r` to a map into `M⁰`; for `r = 0`: every path component of `M` meets `M⁰`).
- The proof sketch in the md (Hanner, approximation `g`) is not formalized here (its steps are V13_11, V13_13, V13_15).
-/
open scoped ContDiff Manifold unitInterval
open Topology
namespace RoundTrip.V13_14

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

/-- Lemma 22.5: `f` smooth with minimum `0`, all `M^c` compact, `M⁰` a manifold, every critical point in `M − M⁰` of
index `≥ λ₀` ⟹ `π_r(M, M⁰) = 0` for `0 ≤ r < λ₀`. -/
def B : Prop :=
  ∀ (m : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (Rn m) M] [IsManifold 𝓘(ℝ, Rn m) ∞ M]
    (f : M → ℝ) (l0 : ℕ), ContMDiff 𝓘(ℝ, Rn m) 𝓘(ℝ, ℝ) ∞ f →
    (∀ x, 0 ≤ f x) → (∃ x, f x = 0) → (∀ c : ℝ, IsCompact {x | f x ≤ c}) →
    IsTopMfd ↥{x : M | f x = 0} →
    (∀ x, f x ≠ 0 → IsCritM (m := m) f x → (l0 : ℕ∞) ≤ idxM (m := m) f x) →
    ∀ r : ℕ, r < l0 → RelPiTrivial M {x | f x = 0} r

end RoundTrip.V13_14
