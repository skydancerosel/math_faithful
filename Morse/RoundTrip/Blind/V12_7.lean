import Morse
/-! Blind formalization of V12_7 (Milnor §21, footnote, p. 114: Cartan's 3-form). Choices:
- Setting (new for §§20–21): a Lie group `G : Type` (Mathlib `Group G`, `LieGroup 𝓘(ℝ, ℝⁿ) ∞ G`, Hausdorff, modelled on
  `ℝⁿ = EuclideanSpace ℝ (Fin n)`, `n = 0` allowed) with a smooth Riemannian metric (Mathlib `RiemannianBundle`,
  `IsContMDiffRiemannianBundle ∞`) that is bi-invariant (`BiInvMetric`: every left and every right translation is an
  isometry, Milnor p. 112); Levi-Civita connection `cov` (`IsLC`, Mathlib `CovariantDerivative`) and the rest of the
  Riemannian prelude copied from the earlier blind files (V11_9, V8_13). Not assumed connected unless said below.
- Milnor's `𝔤` (left-invariant vector fields) is Mathlib's `GroupLieAlgebra 𝓘(ℝ, ℝⁿ) G = T_1G`, `v ↦ X_v = liv v`
  (`mulInvariantVectorField`, `X_v(g) = (L_g)_* v`; every left-invariant field is `liv (X 1)`, and is smooth). The
  bracket of fields is `VectorField.mlieBracket` (`[X,Y] = XY − YX`, Milnor's sign; Mathlib's `⁅v, w⁆ = [X_v, X_w](1)`).
  `⟨u, v⟩` on `T_1G` is `ip` (the metric at `1`); `X ⊢ Y = covF cov X Y = p ↦ cov Y p (X p)`;
  `R(X,Y)Z = curvF cov X Y Z = −X ⊢ (Y ⊢ Z) + Y ⊢ (X ⊢ Z) + [X,Y] ⊢ Z` (Milnor's field formula, the same expression as
  the prelude's `IsCurvVal`, so by tensoriality it is `R` at each point). Identities between fields are equalities of
  fields (i.e. at every point `p : G`).
- Conjunction of (A) and (B).
  (A) For `G` with a bi-invariant metric: (i) `τ(X, Y, Z) = ⟨[X, Y], Z⟩` (at every point, `X, Y, Z ∈ 𝔤`) changes sign
  under each of the three transpositions of its arguments; (ii) "it defines a left-invariant 3-form": there is a family
  `form p` of alternating trilinear forms on `T_pG` (Mathlib `AlternatingMap`, index `Fin 3`), left-invariant
  (`form (g h) ((L_g)_* x) = form h x`), smooth (`form(A, B, C)` is `C^∞` for smooth fields `A, B, C`), with
  `form(X, Y, Z) = ⟨[X, Y], Z⟩` for `X, Y, Z ∈ 𝔤`.
  (B) Cartan's theorem, for every compact connected non-abelian Lie group (non-commutative group; no metric hypothesis,
  since the claim is about all such groups). `H³(G) ≠ 0` is read with real coefficients (de Rham, as for Cartan). Mathlib
  has neither de Rham nor singular cohomology, so it is rendered as `H₃(G; ℝ) ≠ 0` (Mathlib singular homology,
  `Nontrivial`), equivalent by the universal coefficient theorem over the field `ℝ` (`H³ = Hom(H₃, ℝ)`) and de Rham's
  theorem.
-/
namespace RoundTrip.V12_7

open scoped ContDiff Manifold
open Bundle

abbrev Rn (k : ℕ) := EuclideanSpace ℝ (Fin k)

section Prelude
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]

/-- Vector fields on `M`: sections `p ↦ X p ∈ T_pM` of the tangent bundle (no regularity). -/
abbrev VF (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (Rn n) M] := (p : M) → TangentSpace 𝓘(ℝ, Rn n) p

/-- Smooth (`C^∞`) vector field: `p ↦ (p, X p)` is a `C^∞` map `M → TM`. -/
def IsSmoothVF (X : VF n M) : Prop :=
  ContMDiff 𝓘(ℝ, Rn n) (𝓘(ℝ, Rn n)).tangent ∞ (fun p => (⟨p, X p⟩ : TangentBundle 𝓘(ℝ, Rn n) M))

/-- Affine connections: Mathlib's covariant derivative on the tangent bundle; `X ⊢ Y = p ↦ cov Y p (X p)`. -/
abbrev Conn (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M] :=
  CovariantDerivative 𝓘(ℝ, Rn n) (Rn n) (TangentSpace 𝓘(ℝ, Rn n) : M → Type)

/-- A (`C^∞`) connection: the covariant derivative is smooth. -/
def IsGlobalConn (cov : Conn n M) : Prop :=
  ContMDiffCovariantDerivativeOn (Rn n) ∞ cov.toFun Set.univ

/-- Milnor's definition 8.5: `X ⊢ Y - Y ⊢ X = [X, Y]` for smooth fields. -/
def IsSymm (cov : Conn n M) : Prop :=
  ∀ X Y : VF n M, IsSmoothVF X → IsSmoothVF Y → ∀ p : M,
    cov Y p (X p) - cov X p (Y p) = VectorField.mlieBracket 𝓘(ℝ, Rn n) X Y p

/-- A (nondegenerate) interval of `ℝ`. -/
def IsIntv (s : Set ℝ) : Prop := s.OrdConnected ∧ UniqueDiffOn ℝ s

/-- Vector field along `c`. -/
abbrev FA (n : ℕ) {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] (c : ℝ → M) := (t : ℝ) → TangentSpace 𝓘(ℝ, Rn n) (c t)

/-- `V` is smooth along `c` on `s`: `t ↦ (c t, V t) ∈ TM` is `C^∞` on `s`. -/
def IsSmoothAlong (c : ℝ → M) (s : Set ℝ) (V : FA n c) : Prop :=
  ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, Rn n)).tangent ∞ (fun t => (⟨c t, V t⟩ : TangentBundle 𝓘(ℝ, Rn n) M)) s

/-- Velocity `dc/dt` (derivative within `s`). -/
noncomputable def vel (c : ℝ → M) (s : Set ℝ) (t : ℝ) : TangentSpace 𝓘(ℝ, Rn n) (c t) :=
  mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) c s t (1 : ℝ)

/-- Milnor's axioms (a), (b), (c) (p. 46) for `D : V ↦ DV/dt` on fields along `c`, on the interval `s`. -/
def IsCovDerivAlong (cov : Conn n M) (c : ℝ → M) (s : Set ℝ) (D : FA n c → FA n c) : Prop :=
  (∀ V W, IsSmoothAlong c s V → IsSmoothAlong c s W → ∀ t ∈ s, D (fun t => V t + W t) t = D V t + D W t) ∧
  (∀ f : ℝ → ℝ, ContDiffOn ℝ ∞ f s → ∀ V, IsSmoothAlong c s V → ∀ t ∈ s,
      D (fun t => f t • V t) t = derivWithin f s t • V t + f t • D V t) ∧
  (∀ Y : VF n M, IsSmoothVF Y → ∀ t ∈ s, D (fun t => Y (c t)) t = cov Y (c t) (vel c s t))

/-- `W = DV/dt` on `s`: `V` smooth along `c` and `W` is `D V` for a covariant-derivative operation `D`. -/
def HasCovDeriv (cov : Conn n M) (c : ℝ → M) (s : Set ℝ) (V W : FA n c) : Prop :=
  IsSmoothAlong c s V ∧ ∃ D, IsCovDerivAlong cov c s D ∧ ∀ t ∈ s, D V t = W t

/-- Parallel field along `c` on `s`: smooth with `DV/dt = 0`. -/
def IsParallel (cov : Conn n M) (c : ℝ → M) (s : Set ℝ) (V : FA n c) : Prop :=
  HasCovDeriv cov c s V (fun _ => 0)

/-- Smooth curve on the interval `s`. -/
def IsSmoothCurve (c : ℝ → M) (s : Set ℝ) : Prop := ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) ∞ c s

variable [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]

/-- Compatibility with the metric (Milnor p. 47): parallel translation preserves inner products,
i.e. `⟨P, P'⟩` is constant along any smooth curve for parallel fields `P, P'`. -/
def IsCompat (cov : Conn n M) : Prop :=
  ∀ (s : Set ℝ), IsIntv s → ∀ c : ℝ → M, IsSmoothCurve (n := n) c s → ∀ P P' : FA n c,
    IsParallel cov c s P → IsParallel cov c s P' → ∀ t ∈ s, ∀ t' ∈ s, inner ℝ (P t) (P' t) = inner ℝ (P t') (P' t')

/-- The Levi-Civita connection: smooth, symmetric and compatible with the metric. -/
def IsLC (cov : Conn n M) : Prop := IsGlobalConn cov ∧ IsSymm cov ∧ IsCompat cov

/-- Geodesic on an interval `s` (Milnor p. 55): smooth `c` with `D/dt (dc/dt) = 0`. -/
def IsGeodesic (cov : Conn n M) (c : ℝ → M) (s : Set ℝ) : Prop :=
  IsIntv s ∧ IsSmoothCurve (n := n) c s ∧ IsSmoothAlong c s (vel (n := n) c s) ∧ HasCovDeriv cov c s (vel (n := n) c s) (fun _ => 0)

/-- `r = R(x, y) z` for the curvature tensor in Milnor's sign convention
`R(X,Y)Z = ∇_Y∇_X Z - ∇_X∇_Y Z + ∇_{[X,Y]} Z` (so the Jacobi equation reads `D²J/dt² + R(V,J)V = 0`);
tensorial, so computed on any smooth extensions of `x, y, z`. -/
def IsCurvVal (cov : Conn n M) (p : M) (x y z r : TangentSpace 𝓘(ℝ, Rn n) p) : Prop :=
  ∀ X Y Z : VF n M, IsSmoothVF X → IsSmoothVF Y → IsSmoothVF Z → X p = x → Y p = y → Z p = z →
    r = cov (fun q => cov Z q (X q)) p (Y p) - cov (fun q => cov Z q (Y q)) p (X p)
        + cov Z p (VectorField.mlieBracket 𝓘(ℝ, Rn n) X Y p)

open Classical in
/-- The curvature tensor `R(x,y)z` at `p` (Milnor's sign, via `IsCurvVal`); junk value `0` if no value exists. -/
noncomputable def curvR (cov : Conn n M) (p : M) (x y z : TangentSpace 𝓘(ℝ, Rn n) p) : TangentSpace 𝓘(ℝ, Rn n) p :=
  if h : ∃ r, IsCurvVal cov p x y z r then h.choose else 0

open Classical in
/-- The Ricci tensor `K(U₁,U₂) = trace (W ↦ R(U₁,W)U₂)` (Milnor §19; trace of the linear map `W ↦ R(U₁,W)U₂` of `TM_p ≅ ℝⁿ`;
junk value `0` if that map is not linear). -/
noncomputable def ricci (cov : Conn n M) (p : M) (U₁ U₂ : TangentSpace 𝓘(ℝ, Rn n) p) : ℝ :=
  if h : ∃ L : Rn n →ₗ[ℝ] Rn n, ∀ W : Rn n, L W = curvR cov p U₁ W U₂ then LinearMap.trace ℝ (Rn n) h.choose else 0

/-- Milnor's Ricci hypothesis: `K(U,U) ≥ c` for every unit vector `U` at every point. -/
def RicciGE (cov : Conn n M) (c : ℝ) : Prop :=
  ∀ (p : M) (U : TangentSpace 𝓘(ℝ, Rn n) p), ‖U‖ = 1 → c ≤ ricci cov p U U
end Prelude

section FieldCalculus
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]

/-- Milnor's `X ⊢ Y` (covariant derivative of the field `Y` in the direction of the field `X`), as a field. -/
noncomputable def covF (cov : Conn n M) (X Y : VF n M) : VF n M := fun p => cov Y p (X p)

/-- Milnor's curvature of three vector fields (§9, his sign; same expression as `IsCurvVal`):
`R(X,Y)Z = −X ⊢ (Y ⊢ Z) + Y ⊢ (X ⊢ Z) + [X,Y] ⊢ Z`. -/
noncomputable def curvF (cov : Conn n M) (X Y Z : VF n M) : VF n M := fun p =>
  cov (fun q => cov Z q (X q)) p (Y p) - cov (fun q => cov Z q (Y q)) p (X p)
    + cov Z p (VectorField.mlieBracket 𝓘(ℝ, Rn n) X Y p)

/-- The derivative `Y f (p)` of a real function `f` in the direction `v ∈ TM_p`. -/
noncomputable def dirD (f : M → ℝ) (p : M) (v : TangentSpace 𝓘(ℝ, Rn n) p) : ℝ :=
  mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, ℝ) f p v
end FieldCalculus

section LieGroups
/-- `minSmoothness ℝ 3 = 3 ≤ ∞`: lets a `C^∞` Lie group carry Mathlib's Lie algebra structure on `T_1G`. -/
instance leInftyMinSmoothness3 : ENat.LEInfty (minSmoothness ℝ 3) :=
  ⟨by rw [minSmoothness_of_isRCLikeNormedField]; exact ENat.LEInfty.out⟩

variable {n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace (Rn n) G] [LieGroup 𝓘(ℝ, Rn n) ∞ G]

/-- Milnor's `𝔤`: Mathlib's `GroupLieAlgebra 𝓘(ℝ, ℝⁿ) G = T_1G`; `v ∈ T_1G` is identified with the
left-invariant vector field `X_v = liv v`, `X_v(g) = (L_g)_* v` (Mathlib's `mulInvariantVectorField`). Every
left-invariant field `X` is `liv (X 1)`. Mathlib's bracket `⁅v, w⁆ = [X_v, X_w](1)` (bracket of vector fields). -/
noncomputable abbrev liv (v : GroupLieAlgebra 𝓘(ℝ, Rn n) G) : VF n G := mulInvariantVectorField v

variable [Bundle.RiemannianBundle (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)]

variable (n G) in
/-- Left-invariant metric: every left translation `L_g : x ↦ g x` is an isometry. -/
def LeftInvMetric : Prop :=
  ∀ (g h : G) (u v : TangentSpace 𝓘(ℝ, Rn n) h),
    inner ℝ (mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) (fun x => g * x) h u) (mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) (fun x => g * x) h v)
      = inner ℝ u v

variable (n G) in
/-- Right-invariant metric: every right translation `R_g : x ↦ x g` is an isometry. -/
def RightInvMetric : Prop :=
  ∀ (g h : G) (u v : TangentSpace 𝓘(ℝ, Rn n) h),
    inner ℝ (mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) (fun x => x * g) h u) (mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) (fun x => x * g) h v)
      = inner ℝ u v

variable (n G) in
/-- Bi-invariant (left and right invariant) metric (Milnor p. 112). -/
def BiInvMetric : Prop := LeftInvMetric n G ∧ RightInvMetric n G

/-- The inner product `⟨u, v⟩` on `𝔤 = T_1G` (the metric at the identity). -/
noncomputable def ip (u v : GroupLieAlgebra 𝓘(ℝ, Rn n) G) : ℝ :=
  inner ℝ (@id (TangentSpace 𝓘(ℝ, Rn n) (1 : G)) u) (@id (TangentSpace 𝓘(ℝ, Rn n) (1 : G)) v)
end LieGroups

/-- Cartan's 3-form: `⟨[X,Y],Z⟩` is skew-symmetric and defines a left-invariant 3-form; `H³(G) ≠ 0` for compact
connected non-abelian `G`. -/
def B : Prop :=
  (∀ (n : ℕ) (G : Type) [Group G] [TopologicalSpace G] [T2Space G] [ChartedSpace (Rn n) G] [LieGroup 𝓘(ℝ, Rn n) ∞ G] [Bundle.RiemannianBundle (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)] [IsContMDiffRiemannianBundle 𝓘(ℝ, Rn n) ∞ (Rn n) (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)],
    BiInvMetric n G →
      (∀ (u v w : GroupLieAlgebra 𝓘(ℝ, Rn n) G) (p : G),
        inner ℝ (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv u) (liv v) p) (liv w p) = - inner ℝ (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv v) (liv u) p) (liv w p) ∧
        inner ℝ (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv u) (liv v) p) (liv w p) = - inner ℝ (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv u) (liv w) p) (liv v p) ∧
        inner ℝ (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv u) (liv v) p) (liv w p) = - inner ℝ (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv w) (liv v) p) (liv u p)) ∧
      ∃ form : (p : G) → (TangentSpace 𝓘(ℝ, Rn n) p) [⋀^Fin 3]→ₗ[ℝ] ℝ,
        (∀ (g h : G) (x : Fin 3 → TangentSpace 𝓘(ℝ, Rn n) h),
          form (g * h) (fun i => mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) (fun y => g * y) h (x i)) = form h x) ∧
        (∀ A₁ A₂ A₃ : VF n G, IsSmoothVF A₁ → IsSmoothVF A₂ → IsSmoothVF A₃ →
          ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, ℝ) ∞ (fun p => form p ![A₁ p, A₂ p, A₃ p])) ∧
        ∀ (u v w : GroupLieAlgebra 𝓘(ℝ, Rn n) G) (p : G), form p ![liv u p, liv v p, liv w p] = inner ℝ (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv u) (liv v) p) (liv w p)) ∧
  (∀ (n : ℕ) (G : Type) [Group G] [TopologicalSpace G] [T2Space G] [ChartedSpace (Rn n) G] [LieGroup 𝓘(ℝ, Rn n) ∞ G],
    CompactSpace G → ConnectedSpace G → (∃ a b : G, a * b ≠ b * a) →
      Nontrivial (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℝ) 3).obj (ModuleCat.of ℝ ℝ)).obj
        (TopCat.of G)))

end RoundTrip.V12_7
