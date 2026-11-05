import Morse
/-! Blind formalization of V13_11 (Milnor §22, proof of Lemma 22.5, p. 122: Lemma 22.4 in coordinate neighbourhoods). Choices:
- Setting (finite-dimensional Morse theory, no Riemannian metric): `Rn m = EuclideanSpace ℝ (Fin m)`; abstract smooth manifolds `M : Type` (Hausdorff, `IsManifold 𝓘(ℝ, ℝᵐ) ∞`, no second countability or connectedness assumed, `m = 0` allowed), as in the earlier blind files. Critical point `IsCritM` (`df_x = 0`); Hessian `hessM` = second derivative of `f` in the preferred chart at `x`; index `idxM` = `bIndex` (maximal dimension of a negative definite subspace, Milnor's definition p. 5, `ℕ∞`-valued, defined also at degenerate critical points); `IsNondegM` = trivial null space. In `ℝᵐ`: `pd`, `pd2` (first and second partials), `hess`, `idx`. Own definitions (not the project's `indexM`, whose treatment of degenerate points is unknown to me).
- Claim (Lemma 22.4 transplanted to a manifold, as used in the proof of 22.5): `f : M → ℝ` smooth, `K ⊆ M` compact, every critical point of `f` in `K` of index `≥ λ₀` (`l0`). Then for EVERY covering of `K` by finitely many compact sets `K_i`, each inside the domain of a coordinate chart `e_i` (any chart of the maximal `C^∞` atlas, `IsManifold.maximalAtlas`), there is `ε > 0` such that every smooth `g : M → ℝ` whose first and second partial derivatives in each chart `e_i` (of `g ∘ e_i⁻¹`) are within `ε` of those of `f ∘ e_i⁻¹` at every point of `e_i(K_i)` has all its critical points in `K` of index `≥ λ₀`. ("Lemma 22.4 applies in a coordinate neighbourhood of each point of the compact set"; the `∀` covering form is the strongest reading of "choose `g` so close that 22.4 applies".)
- "For linear perturbations" (item title): the perturbations Milnor uses (`f` plus small linear functions of the coordinates, cut off inside the charts) are special cases of such `g` (smallness of the coefficients gives `ε`-closeness); they are not stated as a separate conjunct. "On a submanifold" (title) is not imposed: `M` is an abstract manifold (Milnor's generality).
-/
open scoped ContDiff Manifold unitInterval
open Topology
namespace RoundTrip.V13_11

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

/-- Lemma 22.4 in coordinate neighbourhoods: for any finite cover of `K` by compact sets in chart domains, `g` with first
and second derivatives `ε`-close to those of `f` in these charts has all critical points in `K` of index `≥ λ₀`. -/
def B : Prop :=
  ∀ (m : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (Rn m) M] [IsManifold 𝓘(ℝ, Rn m) ∞ M]
    (f : M → ℝ) (K : Set M) (l0 : ℕ), ContMDiff 𝓘(ℝ, Rn m) 𝓘(ℝ, ℝ) ∞ f → IsCompact K →
    (∀ x ∈ K, IsCritM (m := m) f x → (l0 : ℕ∞) ≤ idxM (m := m) f x) →
    ∀ (k : ℕ) (e : Fin k → OpenPartialHomeomorph M (Rn m)) (Kc : Fin k → Set M),
      (∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℝ, Rn m) ∞ M) → (∀ i, IsCompact (Kc i)) →
      (∀ i, Kc i ⊆ (e i).source) → K ⊆ ⋃ i, Kc i →
      ∃ ε : ℝ, 0 < ε ∧ ∀ g : M → ℝ, ContMDiff 𝓘(ℝ, Rn m) 𝓘(ℝ, ℝ) ∞ g →
        (∀ i, ∀ y ∈ (e i) '' (Kc i), ∀ a, |pd (g ∘ (e i).symm) a y - pd (f ∘ (e i).symm) a y| < ε) →
        (∀ i, ∀ y ∈ (e i) '' (Kc i), ∀ a b, |pd2 (g ∘ (e i).symm) a b y - pd2 (f ∘ (e i).symm) a b y| < ε) →
        ∀ x ∈ K, IsCritM (m := m) g x → (l0 : ℕ∞) ≤ idxM (m := m) g x

end RoundTrip.V13_11
