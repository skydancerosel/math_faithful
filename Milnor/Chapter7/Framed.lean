import Milnor.Chapter6.PoincareHopf

/-!
# Framed submanifolds and framed cobordism (Milnor §7, pp. 42–43)

Throughout, `M ⊆ ℝᵏ` is a compact submanifold of dimension `m` (a slice submanifold of
`ℝᵏ`, as in Chapter 6), given the manifold structure of Chapter 2. Tangent spaces of `M` and of
submanifolds `N ⊆ M` are subspaces of `ℝᵏ` (ranges of derivatives of inclusions).

* A **framed submanifold** of codimension `p` is a compact submanifold `N ⊆ M` together with
  `p` smooth vector fields along `N`, tangent to `M`, orthogonal to `N`, linearly independent
  at each point (hence a basis of the normal space of `N` in `M`).
* A **framed cobordism** between two framed submanifolds is a compact manifold with boundary
  `X ⊆ M × [0,1]` which is a product `N₀ × [0, ε)` near `t = 0` and `N₁ × (1 - ε, 1]` near
  `t = 1`, with a framing of `X` in `M × ℝ` restricting to the given framings at the ends.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

namespace Framed

variable {k m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin k))}
  (hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M)

/-- The tangent space `T_x M ⊆ ℝᵏ`. -/
def tangentM (x : M) : Submodule ℝ (EuclideanSpace ℝ (Fin k)) :=
  letI := hM.chartedSpace
  haveI := hM.isManifold
  LinearMap.range ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin k))
    (Subtype.val : M → EuclideanSpace ℝ (Fin k)) x :
      EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k)) :
      EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))

variable {n p : ℕ}

/-- The tangent space `T_x N ⊆ ℝᵏ` of a submanifold `N ⊆ M`. -/
def tangentN {N : Set M} (hN : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))
        (EuclideanSpace ℝ (Fin p)) N) (x : N) : Submodule ℝ (EuclideanSpace ℝ (Fin k)) :=
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := hN.chartedSpace
  LinearMap.range ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin k))
    (fun q : N => (q.1.1 : EuclideanSpace ℝ (Fin k))) x :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin k)) :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))

/-- **A framed submanifold of `M` of dimension `n` and codimension `p`.** -/
structure FramedSub (n p : ℕ) where
  N : Set M
  hN : letI := hM.chartedSpace; haveI := hM.isManifold;
    IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin p)) N
  dim : n + p = m
  compact : IsCompact N
  v : Fin p → N → EuclideanSpace ℝ (Fin k)
  smooth : ∀ i, letI := hM.chartedSpace; haveI := hM.isManifold; letI := hN.chartedSpace;
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ (v i)
  tangent : ∀ i x, v i x ∈ tangentM hM x.1
  normal : ∀ i x, ∀ w ∈ tangentN hM hN x, ⟪v i x, w⟫ = 0
  indep : ∀ x, LinearIndependent ℝ (fun i => v i x)

/-- The embedding `M × ℝ → ℝᵏ × ℝ`. -/
def embXR (q : M × ℝ) : EuclideanSpace ℝ (Fin k) × ℝ := (q.1.1, q.2)

/-- The tangent space in `ℝᵏ × ℝ` of a submanifold `S ⊆ M × ℝ`. -/
def tangentS {S : Set (M × ℝ)} (hS : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsSliceSubmanifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
        (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin p)) S) (q : S) :
    Submodule ℝ (EuclideanSpace ℝ (Fin k) × ℝ) :=
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := hS.chartedSpace
  LinearMap.range ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
    𝓘(ℝ, EuclideanSpace ℝ (Fin k) × ℝ) (fun r : S => embXR r.1) q :
      EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin k) × ℝ) :
      EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin k) × ℝ)

/-- The inner product on `ℝᵏ × ℝ`. -/
def ipXR (a b : EuclideanSpace ℝ (Fin k) × ℝ) : ℝ := ⟪a.1, b.1⟫ + a.2 * b.2

/-- **A framed cobordism** between two framed submanifolds of `M`: an `(n+1)`-dimensional
submanifold `S ⊆ M × ℝ` which is the product `N₀ × (-∞, ε)` for `t < ε` and `N₁ × (1 - ε, ∞)` for
`t > 1 - ε`, with a framing of `S` in `M × ℝ` restricting to the given framings at the ends.
The cobordism itself is `X = S ∩ (M × [0,1])`, a compact manifold with boundary
`N₀ × 0 ∪ N₁ × 1` (Chapter 2, Lemma 4); Milnor's product structure near the ends is built into
the definition, as in his (p. 41). -/
structure FramedCob (F₀ F₁ : FramedSub hM n p) where
  S : Set (M × ℝ)
  hS : letI := hM.chartedSpace; haveI := hM.isManifold;
    IsSliceSubmanifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin p)) S
  ε : ℝ
  hε : 0 < ε
  hε' : ε < 1 / 2
  end0 : ∀ q : M × ℝ, q.2 < ε → (q ∈ S ↔ q.1 ∈ F₀.N)
  end1 : ∀ q : M × ℝ, 1 - ε < q.2 → (q ∈ S ↔ q.1 ∈ F₁.N)
  compact : IsCompact {q ∈ S | 0 ≤ q.2 ∧ q.2 ≤ 1}
  u : Fin p → S → EuclideanSpace ℝ (Fin k) × ℝ
  smooth : ∀ i, letI := hM.chartedSpace; haveI := hM.isManifold; letI := hS.chartedSpace;
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin k) × ℝ) ∞ (u i)
  tangent : ∀ i q, (u i q).1 ∈ tangentM hM q.1.1
  normal : ∀ i q, ∀ w ∈ tangentS hM hS q, ipXR (u i q) w = 0
  indep : ∀ q, LinearIndependent ℝ (fun i => u i q)
  u_end0 : ∀ i (q : S) (hq : q.1.1 ∈ F₀.N), q.1.2 < ε → u i q = (F₀.v i ⟨q.1.1, hq⟩, 0)
  u_end1 : ∀ i (q : S) (hq : q.1.1 ∈ F₁.N), 1 - ε < q.1.2 → u i q = (F₁.v i ⟨q.1.1, hq⟩, 0)

/-- **Framed cobordism** as a relation. -/
def FramedCobordant (F₀ F₁ : FramedSub hM n p) : Prop := Nonempty (FramedCob hM F₀ F₁)

end Framed

end Milnor
