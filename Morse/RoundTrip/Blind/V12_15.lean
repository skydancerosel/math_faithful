import Morse
/-! Blind formalization of V12_15 (Milnor §21, Lemma 21.2: the geodesics through `e` are the one-parameter subgroups).
Choices:
- Setting exactly as in the blind files V12_1–V12_10 (prelude copied verbatim): a Lie group `G : Type` (Mathlib
  `Group G`, `LieGroup 𝓘(ℝ, ℝⁿ) ∞ G`, Hausdorff, modelled on `ℝⁿ = EuclideanSpace ℝ (Fin n)`, `n = 0` allowed) with a
  smooth Riemannian metric (Mathlib `RiemannianBundle`, `IsContMDiffRiemannianBundle ∞`) that is bi-invariant
  (`BiInvMetric`; Lemma 21.2 is stated in §21 under this standing hypothesis); Levi-Civita connection `cov` (`IsLC`);
  geodesics `IsGeodesic cov γ s` on an interval `s` (prelude). Not assumed connected or compact.
- One-parameter subgroup: a `C^∞` homomorphism `φ : (ℝ, +) → G` (`φ (s + t) = φ s * φ t`; `φ 0 = e` follows).
- "The geodesics `γ` with `γ(0) = e` are precisely the one-parameter subgroups", with geodesics defined on intervals
  (the parenthetical "a symmetric space is complete" is the reason why every geodesic extends to all of `ℝ`):
  (i) every geodesic `γ` on an interval `s ∋ 0` with `γ(0) = e` agrees on `s` with a one-parameter subgroup (in
  particular a geodesic defined on `ℝ` with `γ(0) = e` is one); (ii) every one-parameter subgroup is a geodesic on
  `ℝ`. Constant curves count (the trivial subgroup, the constant geodesic). The completeness remark is not a separate
  claim.
-/
namespace RoundTrip.V12_15

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

section OPS
variable {n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace (Rn n) G] [LieGroup 𝓘(ℝ, Rn n) ∞ G]

/-- One-parameter subgroup of `G`: a `C^∞` homomorphism from the additive group `ℝ` to `G`. -/
def IsOneParamSubgroup (φ : ℝ → G) : Prop :=
  ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) ∞ φ ∧ ∀ s t : ℝ, φ (s + t) = φ s * φ t
end OPS

/-- Lemma 21.2: for a bi-invariant metric, the geodesics `γ` with `γ(0) = e` are exactly the one-parameter subgroups
(every such geodesic on an interval is the restriction of one; every one-parameter subgroup is a geodesic). -/
def B : Prop :=
  ∀ (n : ℕ) (G : Type) [Group G] [TopologicalSpace G] [T2Space G] [ChartedSpace (Rn n) G] [LieGroup 𝓘(ℝ, Rn n) ∞ G] [Bundle.RiemannianBundle (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)] [IsContMDiffRiemannianBundle 𝓘(ℝ, Rn n) ∞ (Rn n) (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)],
    BiInvMetric n G → ∀ cov : Conn n G, IsLC cov →
      (∀ (s : Set ℝ) (γ : ℝ → G), IsGeodesic cov γ s → (0 : ℝ) ∈ s → γ 0 = 1 →
        ∃ φ : ℝ → G, IsOneParamSubgroup (n := n) φ ∧ Set.EqOn γ φ s) ∧
      (∀ φ : ℝ → G, IsOneParamSubgroup (n := n) φ → IsGeodesic cov φ Set.univ)

end RoundTrip.V12_15
