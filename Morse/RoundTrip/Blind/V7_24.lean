import Morse
/-! Blind formalization of V7_24. Choices:
- Setting (as in batch 3): `M : Type` an abstract smooth Hausdorff connected manifold modelled on `ℝⁿ = EuclideanSpace ℝ (Fin n)` with Mathlib's `RiemannianBundle` metric; Levi-Civita connection `cov` (`IsLC`, Mathlib `CovariantDerivative`); `D/dt` along curves via Milnor's axioms (`HasCovDeriv`); geodesics `IsGeodesic`, `exp` via `ExpDefined`/`expMap`, `ρ = rho` (inf of arc lengths of piecewise smooth paths); definitions copied from batch 3.
- `IsMinimal cov γ a b` (prelude): `γ` geodesic on `[a,b]` and `arcLen γ a b ≤ arcLen pw a' b'` for every piecewise smooth path `pw` on any `[a',b']` with the same end points (the literal definition). B: for `a < b`, minimal geodesic iff geodesic whose length is `ρ(γ a, γ b)` (the stated property restated through `ρ`).
-/
namespace RoundTrip.V7_24

open scoped ContDiff Manifold unitInterval
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
end Prelude

section Ch7
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]

/-- `γ` starts at `q` with initial velocity `v` (velocity within `s`, at `t = 0`). -/
def InitData (γ : ℝ → M) (s : Set ℝ) (q : M) (v : TangentSpace 𝓘(ℝ, Rn n) q) : Prop :=
  γ 0 = q ∧ HEq (vel (n := n) γ s 0) v

/-- `exp_q(v)` is defined: there is a geodesic `γ : [0,1] → M` with `γ(0) = q`, `γ'(0) = v`. -/
def ExpDefined (cov : Conn n M) (q : M) (v : TangentSpace 𝓘(ℝ, Rn n) q) : Prop :=
  ∃ γ : ℝ → M, IsGeodesic cov γ (Set.Icc 0 1) ∧ InitData γ (Set.Icc 0 1) q v

open Classical in
/-- `exp_q(v) = γ(1)` for such a geodesic (junk value `q` when undefined). -/
noncomputable def expMap (cov : Conn n M) (q : M) (v : TangentSpace 𝓘(ℝ, Rn n) q) : M :=
  if h : ExpDefined cov q v then h.choose 1 else q

/-- Piecewise smooth path on `[a, b]`: a subdivision `a = t₀ < ... < t_k = b` with each `pth|[t_{i-1}, t_i]` smooth. -/
def IsPW (pth : ℝ → M) (a b : ℝ) : Prop :=
  ∃ (k : ℕ) (t : ℕ → ℝ), t 0 = a ∧ t k = b ∧ (∀ i < k, t i < t (i + 1)) ∧
    ∀ i < k, ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) ∞ pth (Set.Icc (t i) (t (i + 1)))

/-- Arc length `∫_a^b ‖dpth/dt‖ dt` (the derivative exists off a finite set). -/
noncomputable def arcLen (pth : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ‖(mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) pth t (1 : ℝ) : TangentSpace 𝓘(ℝ, Rn n) (pth t))‖

/-- Riemannian norm `‖w‖` of `w ∈ ℝⁿ`, read as a vector of `T_qM`. -/
noncomputable def nrm (q : M) (w : Rn n) : ℝ := ‖(w : TangentSpace 𝓘(ℝ, Rn n) q)‖

/-- The open `ε`-ball in `TM_q` (Riemannian norm), as a subset of the model vector space. -/
def tball (q : M) (ε : ℝ) : Set (Rn n) := {w | nrm q w < ε}

/-- `ρ(p, q)`: greatest lower bound of the arc lengths of piecewise smooth paths joining `p` and `q`. -/
noncomputable def rho (p q : M) : ℝ :=
  sInf {L | ∃ (pth : ℝ → M) (a b : ℝ), a ≤ b ∧ IsPW (n := n) pth a b ∧ pth a = p ∧ pth b = q ∧ arcLen (n := n) pth a b = L}

/-- `exp_q` maps the open `ε`-ball of `TM_q` diffeomorphically onto the open set `U`. -/
def IsNormBall (cov : Conn n M) (q : M) (ε : ℝ) (U : Set M) : Prop :=
  IsOpen U ∧ (∀ w ∈ tball q ε, ExpDefined cov q w) ∧
  Set.InjOn (fun w : Rn n => expMap cov q w) (tball q ε) ∧
  (fun w : Rn n => expMap cov q w) '' tball q ε = U ∧
  ContMDiffOn 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) ∞ (fun w : Rn n => expMap cov q w) (tball q ε) ∧
  ∃ g : M → Rn n, ContMDiffOn 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) ∞ g U ∧ ∀ w ∈ tball q ε, g (expMap cov q w) = w

/-- `γ : [0,1] → M` is a geodesic of length `< ε` from `q₁` to `q₂`. -/
def JoinsShort (cov : Conn n M) (ε : ℝ) (γ : ℝ → M) (q₁ q₂ : M) : Prop :=
  IsGeodesic cov γ (Set.Icc 0 1) ∧ γ 0 = q₁ ∧ γ 1 = q₂ ∧ arcLen (n := n) γ 0 1 < ε

/-- Conclusions (1)-(3) of Lemma 10.3 for `W` and `ε`. -/
def IsUniformNormal (cov : Conn n M) (W : Set M) (ε : ℝ) : Prop :=
  (∀ q₁ ∈ W, ∀ q₂ ∈ W, ∃ γ, JoinsShort cov ε γ q₁ q₂ ∧
      ∀ γ', JoinsShort cov ε γ' q₁ q₂ → Set.EqOn γ γ' (Set.Icc 0 1)) ∧
  (∃ G : M × M → TangentBundle 𝓘(ℝ, Rn n) M,
      ContMDiffOn ((𝓘(ℝ, Rn n)).prod (𝓘(ℝ, Rn n))) (𝓘(ℝ, Rn n)).tangent ∞ G (W ×ˢ W) ∧
      ∀ q₁ ∈ W, ∀ q₂ ∈ W, (G (q₁, q₂)).proj = q₁ ∧
        ∃ γ, JoinsShort cov ε γ q₁ q₂ ∧ HEq (vel (n := n) γ (Set.Icc 0 1) 0) (G (q₁, q₂)).snd) ∧
  (∀ q ∈ W, ∃ U, W ⊆ U ∧ IsNormBall cov q ε U)
end Ch7

section Ch7b
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]

/-- Minimal geodesic `γ : [a, b] → M` (Milnor p. 61): a geodesic whose length is `≤` the length of any
other piecewise smooth path (on any parameter interval `[a', b']`) joining its end points. -/
def IsMinimal (cov : Conn n M) (γ : ℝ → M) (a b : ℝ) : Prop :=
  IsGeodesic cov γ (Set.Icc a b) ∧
    ∀ (pw : ℝ → M) (a' b' : ℝ), a' ≤ b' → IsPW (n := n) pw a' b' → pw a' = γ a → pw b' = γ b →
      arcLen (n := n) γ a b ≤ arcLen (n := n) pw a' b'

/-- Geodesic completeness (Milnor p. 58): `exp_q(v)` is defined for all `q` and `v ∈ TM_q`. -/
def GeodComplete (cov : Conn n M) : Prop := ∀ (q : M) (v : TangentSpace 𝓘(ℝ, Rn n) q), ExpDefined cov q v

/-- Completeness of `M` as a metric space `(M, ρ)` (Milnor p. 64): every `ρ`-Cauchy sequence `ρ`-converges. -/
def MetricComplete (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)] : Prop :=
  ∀ x : ℕ → M, (∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ k ≥ N, rho (n := n) (x m) (x k) < ε) →
    ∃ p : M, ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, rho (n := n) (x m) p < ε

/-- A subset is bounded (Milnor p. 64): it has finite diameter for `ρ`. -/
def RBounded (X : Set M) : Prop := ∃ d : ℝ, ∀ x ∈ X, ∀ y ∈ X, rho (n := n) x y ≤ d
end Ch7b

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M] [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)] [IsContMDiffRiemannianBundle 𝓘(ℝ, Rn n) ∞ (Rn n) (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)] [ConnectedSpace M], ∀ cov : Conn n M, IsLC cov → ∀ (γ : ℝ → M) (a b : ℝ), a < b →
    (IsMinimal cov γ a b ↔ IsGeodesic cov γ (Set.Icc a b) ∧ arcLen (n := n) γ a b = rho (n := n) (γ a) (γ b))
end RoundTrip.V7_24
