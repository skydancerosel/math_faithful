import Morse
/-! Blind formalization of V12_13 (Milnor §21, proof of Theorem 21.7, p. 117: even index from paired eigenvalues).
Choices:
- Lie-group setting exactly as in the blind files V12_1–V12_10 (prelude copied verbatim): a Lie group `G : Type`
  (Mathlib `Group G`, `LieGroup 𝓘(ℝ, ℝⁿ) ∞ G`, Hausdorff, modelled on `ℝⁿ = EuclideanSpace ℝ (Fin n)`, `n = 0` allowed)
  with a smooth bi-invariant Riemannian metric (`BiInvMetric`) and its Levi-Civita connection `cov` (`IsLC`).
  Theorem 21.7 assumes `G` compact and simply connected and `p, q` not conjugate along any geodesic; the quoted step
  ("conjugate points occur in pairs ⇒ even multiplicities ⇒ even index") uses only the bi-invariant metric, so I state
  it for every Lie group with a bi-invariant metric and every geodesic, without those hypotheses.
- Conjugate-point and index vocabulary copied from the blind files of §§13–19 (V9_24, V11_8, V11_9; section `Ch9`):
  geodesics `γ : [0,1] → G` (`IsGeodesic cov γ (Set.Icc 0 1)`, from `p = γ 0` to `q = γ 1`), Jacobi fields
  `IsJacobi`/`JacOn` (Milnor's curvature sign), multiplicity `conjMult cov γ 0 t` of `γ(t)` as a conjugate point of
  `γ(0)` along `γ` (dimension of the Jacobi fields along `γ|[0,1]` vanishing at `0` and `t`, `ℕ∞`-valued), and the
  index `λ = lam 1 γ` (index of `E_**` on `TΩ_γ`, `ℕ∞`-valued).
- Claims (conjunction), for every geodesic `γ : [0,1] → G`: (i) "every conjugate point has even multiplicity" (= "the
  conjugate points occur in pairs"): for every `t ∈ (0,1]`, `conjMult cov γ 0 t = 2k` for some `k : ℕ` (so it is also
  finite; non-conjugate `t` have multiplicity `0`); (ii) the index of `γ` is even: `lam 1 γ = 2k` for some `k : ℕ`
  (so also finite). The citations of 20.5 and of the Index Theorem are justifications, not separate claims.
-/
namespace RoundTrip.V12_13

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

section Ch9
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]

/-- Piecewise smooth path on `[a, b]`: a subdivision `a = t₀ < ... < t_k = b` with each `pth|[t_{i-1}, t_i]` smooth. -/
def IsPW (pth : ℝ → M) (a b : ℝ) : Prop :=
  ∃ (k : ℕ) (t : ℕ → ℝ), t 0 = a ∧ t k = b ∧ (∀ i < k, t i < t (i + 1)) ∧
    ∀ i < k, ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) ∞ pth (Set.Icc (t i) (t (i + 1)))

/-- Energy `E_a^b(pw) = ∫_a^b ‖dpw/dt‖² dt`. -/
noncomputable def energy (pw : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ‖(mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) pw t (1 : ℝ) : TangentSpace 𝓘(ℝ, Rn n) (pw t))‖ ^ 2

/-- Variation vector field `W_t = ∂α/∂u_i (0, t)`. -/
noncomputable def varField {m : ℕ} (α : Rn m → ℝ → M) (i : Fin m) (t : ℝ) : TangentSpace 𝓘(ℝ, Rn n) (α 0 t) :=
  mfderiv 𝓘(ℝ, Rn m) 𝓘(ℝ, Rn n) (fun u => α u t) 0 (EuclideanSpace.single i (1 : ℝ))

/-- The mixed second derivative `∂²F/∂u₁∂u₂ (0,0)`. -/
noncomputable def mixedD (F : Rn 2 → ℝ) : ℝ :=
  fderiv ℝ (fun u : Rn 2 => fderiv ℝ F u (EuclideanSpace.single 0 (1 : ℝ))) 0 (EuclideanSpace.single 1 (1 : ℝ))

/-- Jacobi field along `γ` on `s` (Milnor §14): smooth `J` with `D²J/dt² + R(V, J)V = 0`, `V = dγ/dt`. -/
def IsJacobi (cov : Conn n M) (γ : ℝ → M) (s : Set ℝ) (J : FA n γ) : Prop :=
  ∃ J' J'' : FA n γ, HasCovDeriv cov γ s J J' ∧ HasCovDeriv cov γ s J' J'' ∧
    ∀ t ∈ s, ∃ r, IsCurvVal cov (γ t) (vel (n := n) γ s t) (J t) (vel (n := n) γ s t) r ∧ J'' t + r = 0

/-- Dimension of the linear span of a set of vectors (`ℕ∞`-valued, so `⊤` for infinite dimension). -/
noncomputable def setDim {V : Type} [AddCommGroup V] [Module ℝ V] (S : Set V) : ℕ∞ :=
  (Module.rank ℝ (Submodule.span ℝ S)).toENat

/-- `H` is negative definite on the subspace `S`. -/
def IsNegDefSub {V : Type} [AddCommGroup V] [Module ℝ V] (H : V → V → ℝ) (S : Submodule ℝ V) : Prop :=
  ∀ v ∈ S, v ≠ 0 → H v v < 0

/-- Index of the form `H` on the (space) `A`: the maximal dimension of a subspace of `A` on which `H` is
negative definite (`⊤` if there are such subspaces of unbounded dimension). -/
noncomputable def bIndex {V : Type} [AddCommGroup V] [Module ℝ V] (A : Set V) (H : V → V → ℝ) : ℕ∞ :=
  ⨆ (S : Submodule ℝ V) (_ : (S : Set V) ⊆ A ∧ FiniteDimensional ℝ S ∧ IsNegDefSub H S), (Module.finrank ℝ S : ℕ∞)

/-- Jacobi fields along `γ` on `s`, normalized to vanish outside `s` (so that fields equal on `s` are equal). -/
def JacOn (cov : Conn n M) (γ : ℝ → M) (s : Set ℝ) : Set (FA n γ) :=
  {J | IsJacobi cov γ s J ∧ ∀ t, t ∉ s → J t = 0}

/-- `γ(a)`, `γ(b)` are conjugate along `γ : [0,1] → M` (`a ≠ b ∈ [0,1]`): a non-zero Jacobi field vanishes at `a` and `b`. -/
def IsConj (cov : Conn n M) (γ : ℝ → M) (a b : ℝ) : Prop :=
  a ≠ b ∧ ∃ J ∈ JacOn cov γ (Set.Icc 0 1), J ≠ 0 ∧ J a = 0 ∧ J b = 0

/-- Multiplicity: dimension of the space of Jacobi fields along `γ|[0,1]` vanishing at `a` and `b`. -/
noncomputable def conjMult (cov : Conn n M) (γ : ℝ → M) (a b : ℝ) : ℕ∞ :=
  setDim {J | J ∈ JacOn cov γ (Set.Icc 0 1) ∧ J a = 0 ∧ J b = 0}

/-- Piecewise smooth fields along `pw` on `[0,τ]` (continuous, smooth on the pieces of some subdivision). -/
def IsPWFieldT (τ : ℝ) (pw : ℝ → M) (W : FA n pw) : Prop :=
  ∃ (k : ℕ) (t : ℕ → ℝ), t 0 = 0 ∧ t k = τ ∧ (∀ i < k, t i < t (i + 1)) ∧
    ContinuousOn (fun s => (⟨pw s, W s⟩ : TangentBundle 𝓘(ℝ, Rn n) M)) (Set.Icc 0 τ) ∧
    ∀ i < k, IsSmoothAlong pw (Set.Icc (t i) (t (i + 1))) W

/-- `TΩ_γ` for paths on `[0,τ]`: piecewise smooth fields with `W 0 = W τ = 0` (extended by `0` outside `[0,τ]`). -/
def InTOmegaT (τ : ℝ) (γ : ℝ → M) (W : FA n γ) : Prop :=
  IsPWFieldT (n := n) τ γ W ∧ W 0 = 0 ∧ W τ = 0 ∧ ∀ t, t ∉ Set.Icc 0 τ → W t = 0

/-- The space `TΩ_γ` (for `[0,τ]`) as a set of fields. -/
def TOm (τ : ℝ) (γ : ℝ → M) : Set (FA n γ) := {W | InTOmegaT (n := n) τ γ W}

/-- Variation of `α 0` of paths on `[0,τ]`, end points fixed, with strip subdivision `t`. -/
def IsVarSubT (τ : ℝ) {m : ℕ} (U : Set (Rn m)) (α : Rn m → ℝ → M) (k : ℕ) (t : ℕ → ℝ) : Prop :=
  IsOpen U ∧ (0 : Rn m) ∈ U ∧ t 0 = 0 ∧ t k = τ ∧ (∀ i < k, t i < t (i + 1)) ∧
  (∀ u ∈ U, IsPW (n := n) (α u) 0 τ ∧ α u 0 = α 0 0 ∧ α u τ = α 0 τ) ∧
  ∀ i < k, ContMDiffOn 𝓘(ℝ, Rn m × ℝ) 𝓘(ℝ, Rn n) ∞ (fun x : Rn m × ℝ => α x.1 x.2) (U ×ˢ Set.Icc (t i) (t (i + 1)))

/-- `E_**(W₁, W₂) = r` for the energy `E_0^τ` at `γ`, via a 2-parameter variation as in Milnor §13. -/
def IsHessT (τ : ℝ) (γ : ℝ → M) (W₁ W₂ : FA n γ) (r : ℝ) : Prop :=
  ∃ (U : Set (Rn 2)) (α : Rn 2 → ℝ → M) (k : ℕ) (t : ℕ → ℝ), IsVarSubT (n := n) τ U α k t ∧ α 0 = γ ∧
    (∀ s, HEq (W₁ s) (varField (n := n) α 0 s)) ∧ (∀ s, HEq (W₂ s) (varField (n := n) α 1 s)) ∧
    DifferentiableAt ℝ (fun u : Rn 2 => fderiv ℝ (fun v : Rn 2 => energy (n := n) (α v) 0 τ) u (EuclideanSpace.single 0 (1 : ℝ))) 0 ∧
    mixedD (fun v : Rn 2 => energy (n := n) (α v) 0 τ) = r

open Classical in
/-- `E_**` as a function (value `0` if no variation realizes the pair; Milnor's Cor. 13.4 says it is well defined). -/
noncomputable def HessT (τ : ℝ) (γ : ℝ → M) (W₁ W₂ : FA n γ) : ℝ :=
  if h : ∃ r, IsHessT (n := n) τ γ W₁ W₂ r then h.choose else 0

/-- `λ(τ)`: the index of `(E_0^τ)_**` on `TΩ_{γ_τ}`, `γ_τ = γ|[0,τ]`. -/
noncomputable def lam (τ : ℝ) (γ : ℝ → M) : ℕ∞ := bIndex (TOm (n := n) τ γ) (HessT (n := n) τ γ)
end Ch9

/-- Proof of 21.7: on a Lie group with a bi-invariant metric every conjugate point along a geodesic has even
multiplicity, and (Index Theorem) every geodesic `γ : [0,1] → G` has even index. -/
def B : Prop :=
  ∀ (n : ℕ) (G : Type) [Group G] [TopologicalSpace G] [T2Space G] [ChartedSpace (Rn n) G] [LieGroup 𝓘(ℝ, Rn n) ∞ G] [Bundle.RiemannianBundle (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)] [IsContMDiffRiemannianBundle 𝓘(ℝ, Rn n) ∞ (Rn n) (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)],
    BiInvMetric n G → ∀ cov : Conn n G, IsLC cov →
      ∀ γ : ℝ → G, IsGeodesic cov γ (Set.Icc 0 1) →
        (∀ t ∈ Set.Ioc (0 : ℝ) 1, ∃ k : ℕ, conjMult cov γ 0 t = 2 * (k : ℕ∞)) ∧
        (∃ k : ℕ, lam (n := n) 1 γ = 2 * (k : ℕ∞))

end RoundTrip.V12_13
