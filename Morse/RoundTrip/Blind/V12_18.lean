import Morse
/-! Blind formalization of V12_18 (Milnor §20, Theorem 20.5 and its proof, pp. 110–111). Choices:
- Setting: an abstract Riemannian manifold as in the earlier blind files of §§13–21 (prelude copied from V12_1 / V11_9):
  `M : Type` Hausdorff, modelled on `ℝⁿ = EuclideanSpace ℝ (Fin n)` (`n = 0` allowed), Mathlib `RiemannianBundle`
  metric with `IsContMDiffRiemannianBundle ∞`, Levi-Civita connection `cov` (`IsLC`), geodesics `IsGeodesic`, parallel
  fields `IsParallel`, curvature `curvR` (pointwise, Milnor's sign `R(X,Y)Z = ∇_Y∇_X Z − ∇_X∇_Y Z + ∇_{[X,Y]}Z`, so the
  Jacobi equation is `D²J/dt² + R(V,J)V = 0`), Jacobi fields `IsJacobi`/`JacOn`, `setDim`. Unlike V9–V11 I do not
  assume `M` connected (Theorem 20.5 is local along `γ`).
- The item's title says "for matrix groups: the Jacobi equation along `exp(tA)`", but the quoted statement is Theorem
  20.5 for an arbitrary locally symmetric manifold; I formalize it in that generality (no matrix groups).
- Locally symmetric (`IsLocSymm`, Milnor p. 109: "the curvature tensor is invariant under parallel translation"): for
  every smooth curve `c` on an interval and parallel fields `X, Y, Z, W` along `c`, `⟨R(X,Y)Z, W⟩` is constant along
  `c` (equivalently, `R(X,Y)Z` is parallel, since parallel translation is an isometry).
- `γ` is a geodesic on an interval `s ∋ 0` (not necessarily all of `ℝ`: `M` need not be complete), `p = γ(0)`,
  `V = γ'(0)` (velocity within `s`), `K_V(W) = R(V,W)V` on `T_pM`. "Let `e_1, …, e_n` be the eigenvalues of `K_V`":
  for every orthonormal basis `U_1, …, U_n` of `T_pM` (`Orthonormal`, `n` vectors) with `K_V(U_i) = e_i U_i` (K_V is
  self-adjoint, so such bases exist and every such list `e` is the eigenvalue list with multiplicity).
- Conjugate points along `γ` at parameter `t ∈ s`, `t ≠ 0` (parameters, not points, since `γ` may self-intersect;
  `t < 0` allowed as `k` ranges over non-zero integers): `IsConjAt cov γ t` = a non-zero Jacobi field along
  `γ|[0,t]` (`Set.uIcc 0 t`) vanishing at `0` and `t`; multiplicity `conjMultAt cov γ t` = dimension of the space of
  such fields (the earlier files' `IsConj`/`conjMult` are the same notions for `γ|[0,1]`).
- Claims (conjunction): (1) for `t ∈ s \ {0}`: `γ(t)` is conjugate to `p` along `γ` iff `t = πk/√e_i` for some
  `i` with `e_i > 0` and some non-zero integer `k`; (2) for `t ∈ s \ {0}`: the multiplicity equals the number of
  indices `i` with `e_i > 0` and `t` an integer multiple of `π/√e_i` (Milnor's "number of `e_i`" counts the list with
  repetitions; `e_i > 0` is implicit in `π/√e_i`); (3) the proof's reduction: for parallel fields `P_1, …, P_n` along
  `γ` with `P_i(0) = U_i`, (a) `K_{γ'(t)}(P_i(t)) = e_i P_i(t)` for all `t ∈ s` (a parallel eigenframe), and (b) for
  smooth `w_i` on `s`, `W = Σ w_i P_i` is a Jacobi field iff `w_i'' + e_i w_i = 0` on `s` for every `i` (derivatives
  within `s`).
-/
namespace RoundTrip.V12_18

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

section Sym
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]

/-- Jacobi field along `γ` on `s` (Milnor §14): smooth `J` with `D²J/dt² + R(V, J)V = 0`, `V = dγ/dt`. -/
def IsJacobi (cov : Conn n M) (γ : ℝ → M) (s : Set ℝ) (J : FA n γ) : Prop :=
  ∃ J' J'' : FA n γ, HasCovDeriv cov γ s J J' ∧ HasCovDeriv cov γ s J' J'' ∧
    ∀ t ∈ s, ∃ r, IsCurvVal cov (γ t) (vel (n := n) γ s t) (J t) (vel (n := n) γ s t) r ∧ J'' t + r = 0

/-- Dimension of the linear span of a set of vectors (`ℕ∞`-valued, so `⊤` for infinite dimension). -/
noncomputable def setDim {V : Type} [AddCommGroup V] [Module ℝ V] (S : Set V) : ℕ∞ :=
  (Module.rank ℝ (Submodule.span ℝ S)).toENat

/-- Jacobi fields along `γ` on `s`, normalized to vanish outside `s` (so that fields equal on `s` are equal). -/
def JacOn (cov : Conn n M) (γ : ℝ → M) (s : Set ℝ) : Set (FA n γ) :=
  {J | IsJacobi cov γ s J ∧ ∀ t, t ∉ s → J t = 0}

/-- `γ(t)` is conjugate to `γ(0)` along `γ|[0,t]` (`t ≠ 0`, either sign): a non-zero Jacobi field along `γ` on the
interval between `0` and `t` vanishes at `0` and at `t`. -/
def IsConjAt (cov : Conn n M) (γ : ℝ → M) (t : ℝ) : Prop :=
  t ≠ 0 ∧ ∃ J ∈ JacOn cov γ (Set.uIcc 0 t), J ≠ 0 ∧ J 0 = 0 ∧ J t = 0

/-- Multiplicity of `γ(t)` as a conjugate point of `γ(0)` along `γ|[0,t]`: dimension of the space of Jacobi fields
along `γ` on the interval between `0` and `t` vanishing at `0` and `t`. -/
noncomputable def conjMultAt (cov : Conn n M) (γ : ℝ → M) (t : ℝ) : ℕ∞ :=
  setDim {J | J ∈ JacOn cov γ (Set.uIcc 0 t) ∧ J 0 = 0 ∧ J t = 0}

/-- Locally symmetric (Milnor p. 109): the curvature tensor is invariant under parallel translation, i.e.
`⟨R(X,Y)Z, W⟩` is constant along every smooth curve for parallel fields `X, Y, Z, W`. -/
def IsLocSymm (cov : Conn n M) : Prop :=
  ∀ (s : Set ℝ), IsIntv s → ∀ c : ℝ → M, IsSmoothCurve (n := n) c s → ∀ X Y Z W : FA n c,
    IsParallel cov c s X → IsParallel cov c s Y → IsParallel cov c s Z → IsParallel cov c s W →
      ∀ t ∈ s, ∀ t' ∈ s, inner ℝ (curvR cov (c t) (X t) (Y t) (Z t)) (W t) = inner ℝ (curvR cov (c t') (X t') (Y t') (Z t')) (W t')

/-- Milnor's `K_V(W) = R(V, W)V` on `T_pM`. -/
noncomputable def KV (cov : Conn n M) (p : M) (V W : TangentSpace 𝓘(ℝ, Rn n) p) : TangentSpace 𝓘(ℝ, Rn n) p :=
  curvR cov p V W V
end Sym

/-- Theorem 20.5: in a locally symmetric manifold, the conjugate points of `p = γ(0)` along the geodesic `γ` are the
`γ(πk/√e_i)` (`k ≠ 0`, `e_i > 0` an eigenvalue of `K_V`), with multiplicity the number of `e_i` such that `t` is a
multiple of `π/√e_i`; in a parallel orthonormal eigenframe the Jacobi equation reads `w_i'' + e_i w_i = 0`. -/
def B : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M] [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)] [IsContMDiffRiemannianBundle 𝓘(ℝ, Rn n) ∞ (Rn n) (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)],
    ∀ cov : Conn n M, IsLC cov → IsLocSymm cov →
    ∀ (s : Set ℝ) (γ : ℝ → M), IsGeodesic cov γ s → (0 : ℝ) ∈ s →
    ∀ (U : Fin n → TangentSpace 𝓘(ℝ, Rn n) (γ 0)) (e : Fin n → ℝ), Orthonormal ℝ U →
      (∀ i, KV cov (γ 0) (vel (n := n) γ s 0) (U i) = e i • U i) →
      (∀ t ∈ s, t ≠ 0 →
        (IsConjAt cov γ t ↔ ∃ i : Fin n, 0 < e i ∧ ∃ k : ℤ, k ≠ 0 ∧ t = Real.pi * k / Real.sqrt (e i))) ∧
      (∀ t ∈ s, t ≠ 0 →
        conjMultAt cov γ t = (({i : Fin n | 0 < e i ∧ ∃ k : ℤ, t = k * (Real.pi / Real.sqrt (e i))}.ncard : ℕ) : ℕ∞)) ∧
      (∀ P : Fin n → FA n γ, (∀ i, IsParallel cov γ s (P i)) → (∀ i, P i 0 = U i) →
        (∀ i, ∀ t ∈ s, KV cov (γ t) (vel (n := n) γ s t) (P i t) = e i • P i t) ∧
        ∀ w : Fin n → ℝ → ℝ, (∀ i, ContDiffOn ℝ ∞ (w i) s) →
          (IsJacobi cov γ s (fun t => ∑ i, w i t • P i t) ↔
            ∀ i, ∀ t ∈ s, derivWithin (derivWithin (w i) s) s t + e i * w i t = 0))

end RoundTrip.V12_18
