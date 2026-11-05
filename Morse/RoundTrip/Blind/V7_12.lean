import Morse
/-! Blind formalization of V7_12 (Milnor §10, Lemma 10.5 (Gauss), p. 60). Choices:
- Setting (all items): `M : Type` an abstract smooth (`C^∞`) Hausdorff manifold without boundary modelled on `ℝⁿ = EuclideanSpace ℝ (Fin n)` (`IsManifold 𝓘(ℝ,ℝⁿ) ∞ M`),
  with a smooth Riemannian metric: Mathlib's `Bundle.RiemannianBundle (fun x => TangentSpace 𝓘(ℝ,ℝⁿ) x)` + `IsContMDiffRiemannianBundle`; `⟨·,·⟩ = inner ℝ`, `‖·‖` the fibre norm. Vector fields are sections `p ↦ X p ∈ T_pM`, smooth iff `p ↦ (p, X p) ∈ TM` is `C^∞`.
- Connections: Mathlib's `CovariantDerivative`, `X ⊢ Y = p ↦ cov Y p (X p)`, required `C^∞` (`IsGlobalConn`). `D/dt` along a curve `c` on an interval `s`: Milnor's axioms (a),(b),(c) (p. 46) for an operation `D` on smooth fields along `c`
  (derivatives within `s`); `DV/dt = W` means `∃ D` with these axioms and `D V = W` on `s` (`HasCovDeriv`); parallel = `DV/dt = 0`. Symmetric (`IsSymm`): `X ⊢ Y - Y ⊢ X = [X,Y]` (Mathlib `VectorField.mlieBracket`). Compatible (`IsCompat`): parallel transport preserves inner products (⟨P,P'⟩ constant for parallel P,P'). Levi-Civita: smooth, symmetric, compatible (`IsLC`).
- Intervals: `IsIntv s` = order-connected with `UniqueDiffOn` (nondegenerate interval, any type of endpoints); geodesic `IsGeodesic cov c s`: `c` smooth on `s` and the velocity field `dc/dt` (derivative within `s`) has `D/dt = 0`.
- Connection: the Levi-Civita connection (`IsLC cov`) of the Riemannian manifold; `M` connected (`ConnectedSpace`) and Hausdorff, as in Milnor §10.
- `exp`: `ExpDefined cov q v` iff there is a geodesic `γ : [0,1] → M` with `γ(0)=q`, `γ'(0)=v` (`InitData`); `expMap cov q v = γ(1)` for such a `γ` (chosen; junk value `q` if none). Initial velocities are matched with `HEq` (types `T_{γ 0}M` vs `T_qM`).
- Normal balls: `tball q ε` = open ε-ball of `T_qM` for the Riemannian norm `nrm q` (the fibre norm of `T_qM`, named explicitly as `@Norm.norm (TangentSpace _ q) _`), as a subset of the model space `ℝⁿ` (= `T_qM` as a type); `IsNormBall cov q ε U`: `exp_q` is defined on it, injective, `C^∞`, with image the open set `U` and a `C^∞` inverse `U → ℝⁿ` (diffeomorphism onto `U`). Fix w.r.t. the earlier copies of this prelude: they wrote `nrm q w := ‖(w : TangentSpace _ q)‖`, which Lean elaborates to the Euclidean norm of `ℝⁿ` (the ascription does not change the inferred type of `w`), so their `tball` was a Euclidean ball in the model coordinates of `T_qM`, not a Riemannian one; here every length or norm of a tangent vector (`‖v‖`, `‖dω/dt‖`, radii of balls and shells in `TM_q`, lengths of paths) is the Riemannian one, checked by the `rfl` examples at the end of the prelude (`arcLen` was already Riemannian).
- Paths: piecewise smooth `IsPW` (subdivision with each piece `C^∞`), arc length `arcLen = ∫ ‖dω/dt‖` (derivative `mfderiv`, which exists off finitely many points).
- `U_q`: Milnor's `U_q` is the image of the open ε-ball of `TM_q` under `exp_q` given by Lemma 10.3 (3) (for `q ∈ W`); the statement only involves the fact that `exp_q` maps that ε-ball diffeomorphically onto `U_q`, so B is stated for any `q`, `ε > 0` and `U` with `IsNormBall cov q ε U` (the `U_q` of Lemma 10.3 is the instance; B is therefore formally at least as strong as the literal reading "`q ∈ W`, `W, ε` as in Lemma 10.3").
- "In `U_q` the geodesics through `q` are the orthogonal trajectories of the hypersurfaces `S_r = {exp_q(v) : ‖v‖ = r}`" is formalized
  as in Milnor's proof: for every `C^∞` curve `t ↦ v(t)` of unit vectors of `TM_q` (Riemannian norm `nrm q`) on a nondegenerate interval
  `J`, and `f(r, t) = exp_q(r v(t))`, `⟨∂f/∂r, ∂f/∂t⟩ = 0` for all `0 < r < ε`, `t ∈ J`. `∂f/∂r` (`dfr`) is the velocity of the radial
  geodesic `r ↦ exp_q(r v(t))`, `∂f/∂t` (`dft`) the derivative in `t` (within `J`), both in `T_{f(r,t)}M`; `⟨·,·⟩` is the inner product of
  `T_{f(r,t)}M` given by the metric (`rinner`, named explicitly). Every tangent vector of `S_r` at `exp_q(rv)` is such a `∂f/∂t`, so this
  says that the radial geodesics cross every `S_r` (`0 < r < ε`) orthogonally. The intermediate step ("independent of `r`") is proof,
  not claim, and is not formalized; nor is the converse reading "every orthogonal trajectory is a radial geodesic". -/
namespace RoundTrip.V7_12

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

/-- Riemannian norm `‖w‖` of `w ∈ ℝⁿ`, read as a vector of `T_qM`: the norm of the fibre `T_qM` given by the
metric, named explicitly (a type ascription `‖(w : TangentSpace _ q)‖` would elaborate to the Euclidean norm of `ℝⁿ`). -/
noncomputable def nrm (q : M) (w : Rn n) : ℝ := @Norm.norm (TangentSpace 𝓘(ℝ, Rn n) q) _ w

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

-- Sanity checks (by `rfl`): `nrm q` is the norm of `T_qM` given by the Riemannian metric, and `arcLen`
-- integrates the Riemannian norm of the velocity (not a Euclidean norm of chart coordinates).
example (q : M) (v : TangentSpace 𝓘(ℝ, Rn n) q) : nrm q v = ‖v‖ := rfl
example (pth : ℝ → M) (a b : ℝ) : arcLen (n := n) pth a b =
    ∫ t in a..b, @Norm.norm (TangentSpace 𝓘(ℝ, Rn n) (pth t)) _ (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) pth t (1 : ℝ)) := rfl
end Ch7

section Extra
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]

/-- Riemannian inner product `⟨a, b⟩` of `a, b ∈ ℝⁿ` read as vectors of `T_xM` (the metric's inner product, named explicitly). -/
noncomputable def rinner (x : M) (a b : Rn n) : ℝ := @inner ℝ (TangentSpace 𝓘(ℝ, Rn n) x) _ a b

/-- `∂f/∂r (r, t)` for `f(r, t) = exp_q(r v(t))`: the velocity of `s ↦ exp_q(s v(t))` at `s = r`. -/
noncomputable def dfr (cov : Conn n M) (q : M) (v : ℝ → Rn n) (r t : ℝ) : Rn n :=
  mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) (fun s : ℝ => expMap cov q (s • v t)) r (1 : ℝ)

/-- `∂f/∂t (r, t)` for `f(r, t) = exp_q(r v(t))`, the parameter `t` ranging over the interval `J`. -/
noncomputable def dft (cov : Conn n M) (q : M) (v : ℝ → Rn n) (J : Set ℝ) (r t : ℝ) : Rn n :=
  mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) (fun τ : ℝ => expMap cov q (r • v τ)) J t (1 : ℝ)
end Extra

/-- Gauss lemma: in a normal ball `U_q`, for `f(r, t) = exp_q(r v(t))` with `‖v(t)‖ = 1`, `⟨∂f/∂r, ∂f/∂t⟩ = 0`: radial geodesics are orthogonal to the hypersurfaces `exp_q{‖v‖ = r}`. -/
def B : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, Rn n) ∞ (Rn n) (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)] [ConnectedSpace M], ∀ cov : Conn n M, IsLC cov → ∀ (q : M) (ε : ℝ) (U : Set M), 0 < ε → IsNormBall cov q ε U →
    ∀ (J : Set ℝ) (v : ℝ → Rn n), IsIntv J → ContDiffOn ℝ ∞ v J → (∀ t ∈ J, nrm q (v t) = 1) →
      ∀ r ∈ Set.Ioo 0 ε, ∀ t ∈ J, rinner (expMap cov q (r • v t)) (dfr cov q v r t) (dft cov q v J r t) = 0
end RoundTrip.V7_12
