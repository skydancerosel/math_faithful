import Morse
/-! Blind formalization of V13_15 (Milnor §22, proof of Lemma 22.5, p. 121). Choices:
- Setting as in the earlier blind files; the prelude is copied verbatim from the parallel blind file V13_2 (= the V11_22/V11_9 prelude plus its §22 vocabulary `dPQ`, `OmD`, `inclD`, `IsTopMfd`, `RelPiTrivial`, `Hyp221`): `M : Type` an abstract smooth Hausdorff Riemannian manifold modelled on `ℝⁿ = EuclideanSpace ℝ (Fin n)` (Mathlib `RiemannianBundle`, smooth), Levi-Civita connection `cov` (`IsLC`), geodesics `IsGeodesic` on `[0,1]`, `IsGeodPQ`, minimal geodesics `IsMinimal` (Milnor p. 61), `arcLen`, `ρ = rho`, index `λ(γ) = lam 1 γ` (`ℕ∞`-valued), multiplicity `conjMult`, completeness `MetricComplete`; `Om n p q = Ω(M;p,q)` (piecewise smooth maps `ℝ → M`, only `[0,1]` matters, Milnor's `d`-topology), `OmLe n p q c = Ω^c = E⁻¹[0,c]`, `OmD n p q = Ω^d` with `d = dPQ n p q = ρ(p,q)²`.
- Context = hypotheses of Lemma 22.5 (`Hyp225`, without the index condition, which this step does not use): `f : M → ℝ` smooth with minimum `0` (`f ≥ 0`, `f = 0` somewhere), every `M^c = f⁻¹[0,c]` compact (all `c : ℝ`), `M⁰ = f⁻¹(0)` a topological manifold (`IsTopMfd` of the subspace, as in V13_2: Hausdorff, locally Euclidean, dimension may vary). Lemma 22.5's `M` is only a smooth manifold; "unique minimal geodesic" presupposes a Riemannian metric on `M`, so the claim is stated for every smooth Riemannian metric on `M` (with its Levi-Civita connection). `M` is NOT assumed connected or complete here (Lemma 22.5 does not assume it).
- Claim (conjunction): there are an open `U ⊇ M⁰` and a retraction `r : U → M⁰` (continuous on `U`, values in `M⁰`, `r = id` on `M⁰`) such that each `x ∈ U` is joined to `r(x)` by a unique minimal geodesic `[0,1] → M` (`IsMinimal`, unique on `[0,1]`); and "hence `U` can be deformed into `M⁰` within `M`": a homotopy `H : [0,1] × U → M`, continuous on `[0,1] × U`, `H₀ = id`, `H₁(U) ⊆ M⁰`, which (this is the "hence") moves each `x` along the minimal geodesic from `x` to `r(x)`; in particular `H` fixes `M⁰` pointwise.
- Hanner's theorem itself (`M⁰` is a neighbourhood retract) is the first conjunct; it is not stated separately.
-/
open scoped ContDiff Manifold unitInterval
open Topology Bundle
namespace RoundTrip.V13_15


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

section Ch8
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]

/-- `pw ∈ Ω(M; p, q)`: a piecewise smooth path `[0,1] → M` from `p` to `q` (only values on `[0,1]` matter). -/
def InOmega (p q : M) (pw : ℝ → M) : Prop := IsPW (n := n) pw 0 1 ∧ pw 0 = p ∧ pw 1 = q

/-- A piecewise smooth vector field along `pw`: continuous on `[0,1]` and smooth on each piece of a subdivision. -/
def IsPWField (pw : ℝ → M) (W : FA n pw) : Prop :=
  ∃ (k : ℕ) (t : ℕ → ℝ), t 0 = 0 ∧ t k = 1 ∧ (∀ i < k, t i < t (i + 1)) ∧
    ContinuousOn (fun s => (⟨pw s, W s⟩ : TangentBundle 𝓘(ℝ, Rn n) M)) (Set.Icc 0 1) ∧
    ∀ i < k, IsSmoothAlong pw (Set.Icc (t i) (t (i + 1))) W

/-- Milnor's "tangent space" `TΩ_pw`: piecewise smooth fields `W` along `pw` with `W 0 = 0`, `W 1 = 0`. -/
def InTOmega (pw : ℝ → M) (W : FA n pw) : Prop := IsPWField (n := n) pw W ∧ W 0 = 0 ∧ W 1 = 0

/-- Energy `E_a^b(pw) = ∫_a^b ‖dpw/dt‖² dt`. -/
noncomputable def energy (pw : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ‖(mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) pw t (1 : ℝ) : TangentSpace 𝓘(ℝ, Rn n) (pw t))‖ ^ 2

/-- `E = E_0^1`. -/
noncomputable def Efun (pw : ℝ → M) : ℝ := energy (n := n) pw 0 1

/-- A (`m`-parameter) variation `α : ℝ^m × [0,1] → M` of `α 0`, keeping end points fixed, with strip subdivision `t`:
`U ∋ 0` open, each `α u ∈ Ω(M; p, q)`, and `α` is `C^∞` on each strip `U × [t_{i-1}, t_i]`. -/
def IsVarSub {m : ℕ} (U : Set (Rn m)) (α : Rn m → ℝ → M) (k : ℕ) (t : ℕ → ℝ) : Prop :=
  IsOpen U ∧ (0 : Rn m) ∈ U ∧ t 0 = 0 ∧ t k = 1 ∧ (∀ i < k, t i < t (i + 1)) ∧
  (∀ u ∈ U, IsPW (n := n) (α u) 0 1 ∧ α u 0 = α 0 0 ∧ α u 1 = α 0 1) ∧
  ∀ i < k, ContMDiffOn 𝓘(ℝ, Rn m × ℝ) 𝓘(ℝ, Rn n) ∞ (fun x : Rn m × ℝ => α x.1 x.2) (U ×ˢ Set.Icc (t i) (t (i + 1)))

/-- `α` is a variation (for some strip subdivision). -/
def IsVar {m : ℕ} (U : Set (Rn m)) (α : Rn m → ℝ → M) : Prop := ∃ (k : ℕ) (t : ℕ → ℝ), IsVarSub (n := n) U α k t

/-- Variation vector field `W_t = ∂α/∂u_i (0, t)`. -/
noncomputable def varField {m : ℕ} (α : Rn m → ℝ → M) (i : Fin m) (t : ℝ) : TangentSpace 𝓘(ℝ, Rn n) (α 0 t) :=
  mfderiv 𝓘(ℝ, Rn m) 𝓘(ℝ, Rn n) (fun u => α u t) 0 (EuclideanSpace.single i (1 : ℝ))

/-- `pw` is a critical path of `F` (Milnor p. 69): for every 1-parameter variation `α` of `pw`,
`dF(α u)/du` exists and vanishes at `u = 0`. -/
def IsCriticalPath (F : (ℝ → M) → ℝ) (pw : ℝ → M) : Prop :=
  ∀ (U : Set (Rn 1)) (α : Rn 1 → ℝ → M), IsVar (n := n) U α → α 0 = pw →
    HasFDerivAt (fun u : Rn 1 => F (α u)) (0 : Rn 1 →L[ℝ] ℝ) 0

/-- One-sided velocities `V_{t+}`, `V_{t-}` and the jump `Δ_t V = V_{t+} - V_{t-}` of a piecewise smooth path. -/
noncomputable def Vplus (pw : ℝ → M) (t : ℝ) : TangentSpace 𝓘(ℝ, Rn n) (pw t) :=
  mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) pw (Set.Ici t) t (1 : ℝ)
noncomputable def Vminus (pw : ℝ → M) (t : ℝ) : TangentSpace 𝓘(ℝ, Rn n) (pw t) :=
  mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) pw (Set.Iic t) t (1 : ℝ)
noncomputable def Vjump (pw : ℝ → M) (t : ℝ) : TangentSpace 𝓘(ℝ, Rn n) (pw t) := Vplus (n := n) pw t - Vminus (n := n) pw t

/-- `r = R(x, y) z` for the curvature tensor in Milnor's sign convention
`R(X,Y)Z = ∇_Y∇_X Z - ∇_X∇_Y Z + ∇_{[X,Y]} Z` (so the Jacobi equation reads `D²J/dt² + R(V,J)V = 0`);
tensorial, so computed on any smooth extensions of `x, y, z`. -/
def IsCurvVal (cov : Conn n M) (p : M) (x y z r : TangentSpace 𝓘(ℝ, Rn n) p) : Prop :=
  ∀ X Y Z : VF n M, IsSmoothVF X → IsSmoothVF Y → IsSmoothVF Z → X p = x → Y p = y → Z p = z →
    r = cov (fun q => cov Z q (X q)) p (Y p) - cov (fun q => cov Z q (Y q)) p (X p)
        + cov Z p (VectorField.mlieBracket 𝓘(ℝ, Rn n) X Y p)

/-- The mixed second derivative `∂²F/∂u₁∂u₂ (0,0)`. -/
noncomputable def mixedD (F : Rn 2 → ℝ) : ℝ :=
  fderiv ℝ (fun u : Rn 2 => fderiv ℝ F u (EuclideanSpace.single 0 (1 : ℝ))) 0 (EuclideanSpace.single 1 (1 : ℝ))

/-- `r = E_**(W₁, W₂)` at the geodesic `γ`: `r = ∂²E(α(u₁,u₂))/∂u₁∂u₂ (0,0)` for a 2-parameter variation `α`
of `γ` with variation fields `W₁, W₂`. -/
def IsHess (γ : ℝ → M) (W₁ W₂ : FA n γ) (r : ℝ) : Prop :=
  ∃ (U : Set (Rn 2)) (α : Rn 2 → ℝ → M), IsVar (n := n) U α ∧ α 0 = γ ∧
    (∀ t, HEq (W₁ t) (varField (n := n) α 0 t)) ∧ (∀ t, HEq (W₂ t) (varField (n := n) α 1 t)) ∧
    DifferentiableAt ℝ (fun u : Rn 2 => fderiv ℝ (fun v : Rn 2 => Efun (n := n) (α v)) u (EuclideanSpace.single 0 (1 : ℝ))) 0 ∧
    mixedD (fun v : Rn 2 => Efun (n := n) (α v)) = r
end Ch8

section Ch8b
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]

/-- Fields along a parametrized family `α u t` (dependent on `(u, t)`). -/
abbrev FP {m : ℕ} (α : Rn m → ℝ → M) := (u : Rn m) → (t : ℝ) → TangentSpace 𝓘(ℝ, Rn n) (α u t)

/-- The `u_i`-coordinate curve `s ↦ α(u₀ + s e_i, t)` through `u₀` (used for `D/∂u_i`). -/
noncomputable def uCurve {m : ℕ} (α : Rn m → ℝ → M) (i : Fin m) (u₀ : Rn m) (t : ℝ) (s : ℝ) : M :=
  α (u₀ + s • EuclideanSpace.single i (1 : ℝ)) t

/-- Jacobi field along `γ` on `s` (Milnor §14): smooth `J` with `D²J/dt² + R(V, J)V = 0`, `V = dγ/dt`. -/
def IsJacobi (cov : Conn n M) (γ : ℝ → M) (s : Set ℝ) (J : FA n γ) : Prop :=
  ∃ J' J'' : FA n γ, HasCovDeriv cov γ s J J' ∧ HasCovDeriv cov γ s J' J'' ∧
    ∀ t ∈ s, ∃ r, IsCurvVal cov (γ t) (vel (n := n) γ s t) (J t) (vel (n := n) γ s t) r ∧ J'' t + r = 0
end Ch8b

section Ch9
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]

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

/-- Null space of `H` on `A`: the `v ∈ A` with `H v w = 0` for all `w ∈ A`; the nullity is `setDim` of it. -/
def bNullSet {V : Type} [AddCommGroup V] [Module ℝ V] (A : Set V) (H : V → V → ℝ) : Set V :=
  {v | v ∈ A ∧ ∀ w ∈ A, H v w = 0}

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

/-- Broken Jacobi fields along `γ|[0,τ]` for the subdivision `t₀ = 0 < ... < t_k = τ`:
`W ∈ TΩ` which are Jacobi fields on each `[t_{i-1}, t_i]`. -/
def IsBrokenT (cov : Conn n M) (γ : ℝ → M) (τ : ℝ) (k : ℕ) (t : ℕ → ℝ) (W : FA n γ) : Prop :=
  t 0 = 0 ∧ t k = τ ∧ (∀ i < k, t i < t (i + 1)) ∧ InTOmegaT (n := n) τ γ W ∧
  ∀ i < k, IsJacobi cov γ (Set.Icc (t i) (t (i + 1))) W

/-- `TΩ_γ(t₀,…,t_k)` as a set. -/
def BrokenSet (cov : Conn n M) (γ : ℝ → M) (τ : ℝ) (k : ℕ) (t : ℕ → ℝ) : Set (FA n γ) :=
  {W | IsBrokenT cov γ τ k t W}

/-- `T'`: fields of `TΩ` vanishing at all `t_i`. -/
def TPrime (γ : ℝ → M) (τ : ℝ) (k : ℕ) (t : ℕ → ℝ) : Set (FA n γ) :=
  {W | InTOmegaT (n := n) τ γ W ∧ ∀ i ≤ k, W (t i) = 0}

/-- A neighbourhood `U` in which any two points are joined by a unique minimal geodesic (on `[0,1]`)
depending differentiably on the end points (Milnor §10). -/
def GoodNbhd (cov : Conn n M) (U : Set M) : Prop :=
  IsOpen U ∧
  (∀ q₁ ∈ U, ∀ q₂ ∈ U, ∃ γ : ℝ → M, IsMinimal cov γ 0 1 ∧ γ 0 = q₁ ∧ γ 1 = q₂ ∧
      ∀ γ' : ℝ → M, IsMinimal cov γ' 0 1 → γ' 0 = q₁ → γ' 1 = q₂ → Set.EqOn γ γ' (Set.Icc 0 1)) ∧
  ∃ G : M × M → TangentBundle 𝓘(ℝ, Rn n) M,
      ContMDiffOn ((𝓘(ℝ, Rn n)).prod (𝓘(ℝ, Rn n))) (𝓘(ℝ, Rn n)).tangent ∞ G (U ×ˢ U) ∧
      ∀ q₁ ∈ U, ∀ q₂ ∈ U, (G (q₁, q₂)).proj = q₁ ∧
        ∃ γ, IsMinimal cov γ 0 1 ∧ γ 0 = q₁ ∧ γ 1 = q₂ ∧ HEq (vel (n := n) γ (Set.Icc 0 1) 0) (G (q₁, q₂)).snd

/-- Sufficiently fine subdivision `0 = t₀ < ... < t_k = τ` of `[0,τ]` for `γ`: every `γ|[t_{i-1}, t_i]`
lies in a neighbourhood `U` as in `GoodNbhd` and is minimal. -/
def FineSub (cov : Conn n M) (γ : ℝ → M) (τ : ℝ) (k : ℕ) (t : ℕ → ℝ) : Prop :=
  t 0 = 0 ∧ t k = τ ∧ (∀ i < k, t i < t (i + 1)) ∧
  ∀ i < k, (∃ U, GoodNbhd cov U ∧ ∀ s ∈ Set.Icc (t i) (t (i + 1)), γ s ∈ U) ∧ IsMinimal cov γ (t i) (t (i + 1))

/-- A variation through geodesics, not necessarily fixing end points: `α` is `C^∞` on `(-ε,ε) × [0,1]`
and every `α u`, `|u| < ε`, is a geodesic `[0,1] → M`. -/
def IsGeodVar (cov : Conn n M) (ε : ℝ) (α : Rn 1 → ℝ → M) : Prop :=
  ContMDiffOn 𝓘(ℝ, Rn 1 × ℝ) 𝓘(ℝ, Rn n) ∞ (fun x : Rn 1 × ℝ => α x.1 x.2) (Metric.ball (0 : Rn 1) ε ×ˢ Set.Icc 0 1) ∧
  ∀ u ∈ Metric.ball (0 : Rn 1) ε, IsGeodesic cov (α u) (Set.Icc 0 1)

/-- The space `Σ = TM_{γ(t_1)} ⊕ ... ⊕ TM_{γ(t_i)}`. -/
abbrev Sig (γ : ℝ → M) (t : ℕ → ℝ) (i : ℕ) := (j : Fin i) → TangentSpace 𝓘(ℝ, Rn n) (γ (t ((j : ℕ) + 1)))

/-- Bilinear form `H_τ` on `Σ`, `H_τ(x, y) = E_**(W_x, W_y)` where `W_x` is the broken Jacobi field along
`γ_τ` (subdivision `t₀,…,t_i,τ`) with `W_x(t_j) = x_j`. -/
def HtauRel (cov : Conn n M) (γ : ℝ → M) (t : ℕ → ℝ) (i : ℕ) (τ : ℝ) (x y : Sig (n := n) γ t i) (r : ℝ) : Prop :=
  ∃ W₁ W₂ : FA n γ, IsBrokenT cov γ τ (i + 1) (fun j => if j ≤ i then t j else τ) W₁ ∧
    IsBrokenT cov γ τ (i + 1) (fun j => if j ≤ i then t j else τ) W₂ ∧
    (∀ j : Fin i, W₁ (t ((j : ℕ) + 1)) = x j) ∧ (∀ j : Fin i, W₂ (t ((j : ℕ) + 1)) = y j) ∧
    IsHessT (n := n) τ γ W₁ W₂ r

open Classical in
noncomputable def Htau (cov : Conn n M) (γ : ℝ → M) (t : ℕ → ℝ) (i : ℕ) (τ : ℝ) (x y : Sig (n := n) γ t i) : ℝ :=
  if h : ∃ r, HtauRel cov γ t i τ x y r then h.choose else 0

/-- The path space `Ω^c = {w ∈ Ω(M;p,q) | E(w) ≤ c}`. -/
def OmegaC (p q : M) (c : ℝ) : Set (ℝ → M) := {w | InOmega (n := n) p q w ∧ Efun (n := n) w ≤ c}

/-- `Int Ω^c = E⁻¹([0,c))`. -/
def IntOmegaC (p q : M) (c : ℝ) : Set (ℝ → M) := {w | InOmega (n := n) p q w ∧ Efun (n := n) w < c}

/-- `Ω(t₀,…,t_k)`: paths in `Ω(M;p,q)` whose restriction to each `[t_{i-1}, t_i]` is a geodesic. -/
def OmegaSub (cov : Conn n M) (p q : M) (k : ℕ) (t : ℕ → ℝ) : Set (ℝ → M) :=
  {w | InOmega (n := n) p q w ∧ ∀ i < k, IsGeodesic cov w (Set.Icc (t i) (t (i + 1)))}

/-- Arc length function `s(t)` of `w` from `0` to `t` and its derivative `ds/dt`. -/
noncomputable def dsdt (w : ℝ → M) (t : ℝ) : ℝ := deriv (fun x => arcLen (n := n) w 0 x) t

/-- Milnor's distance `d(w,w') = max_t ρ(w(t),w'(t)) + [∫₀¹ (ds/dt − ds'/dt)² dt]^{1/2}`. -/
noncomputable def dOm (w w' : ℝ → M) : ℝ :=
  (⨆ t : Set.Icc (0 : ℝ) 1, rho (n := n) (w t) (w' t)) +
    Real.sqrt (∫ t in (0 : ℝ)..1, (dsdt (n := n) w t - dsdt (n := n) w' t) ^ 2)

/-- Lemma 10.8-type conclusion on a set `S`: two points of `S` at `ρ`-distance `< ε` are joined by a unique
geodesic of length `< ε`, depending differentiably on the end points. -/
def ShortGood (cov : Conn n M) (S : Set M) (ε : ℝ) : Prop :=
  (∀ q₁ ∈ S, ∀ q₂ ∈ S, rho (n := n) q₁ q₂ < ε → ∃ γ, JoinsShort cov ε γ q₁ q₂ ∧
      ∀ γ', JoinsShort cov ε γ' q₁ q₂ → Set.EqOn γ γ' (Set.Icc 0 1)) ∧
  ∃ G : M × M → TangentBundle 𝓘(ℝ, Rn n) M,
      ContMDiffOn ((𝓘(ℝ, Rn n)).prod (𝓘(ℝ, Rn n))) (𝓘(ℝ, Rn n)).tangent ∞ G {z | z.1 ∈ S ∧ z.2 ∈ S ∧ rho (n := n) z.1 z.2 < ε} ∧
      ∀ q₁ ∈ S, ∀ q₂ ∈ S, rho (n := n) q₁ q₂ < ε → (G (q₁, q₂)).proj = q₁ ∧
        ∃ γ, JoinsShort cov ε γ q₁ q₂ ∧ HEq (vel (n := n) γ (Set.Icc 0 1) 0) (G (q₁, q₂)).snd
end Ch9


section Ch10
variable (n : ℕ) {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]

/-- `Ω = Ω(M; p, q)` as a type: piecewise smooth paths from `p` to `q` (maps `ℝ → M`, only `[0,1]` matters). -/
def Om (p q : M) : Type := {w : ℝ → M // InOmega (n := n) p q w}

/-- Milnor's topology on `Ω`: generated by the open `d`-balls (`d = dOm`); this is the topology of the (pseudo)metric `d`
(two paths agreeing on `[0,1]` are not distinguished by `d`, hence topologically indistinguishable). -/
instance omTopology (p q : M) : TopologicalSpace (Om n p q) :=
  TopologicalSpace.generateFrom {S | ∃ (w : Om n p q) (ε : ℝ), S = {w' | dOm (n := n) w.1 w'.1 < ε}}

/-- `Ω^c = E⁻¹[0,c]`, as a subset of `Ω`. -/
def OmLe (p q : M) (c : ℝ) : Set (Om n p q) := {w | Efun (n := n) w.1 ≤ c}
/-- `Int Ω^c = E⁻¹[0,c)`. -/
def IntOm (p q : M) (c : ℝ) : Set (Om n p q) := {w | Efun (n := n) w.1 < c}

/-- `Ω*`: all continuous paths `[0,1] → M` from `p` to `q`, compact-open topology (subspace of `C(I, M)`). -/
abbrev OmStar (p q : M) : Type := {w : C(unitInterval, M) // w 0 = p ∧ w 1 = q}

/-- Evaluate a path of `Ω*` at a real parameter (clamped to `[0,1]`). -/
noncomputable def evS {p q : M} (w : OmStar p q) (x : ℝ) : M := w.1 (Set.projIcc 0 1 zero_le_one x)

/-- `d*(w,w') = max_t ρ(w t, w' t)`. -/
noncomputable def dstar (w w' : C(unitInterval, M)) : ℝ := ⨆ t : unitInterval, rho (n := n) (w t) (w' t)

/-- `i : Ω → Ω*` is the natural map (the identity on underlying paths). -/
def NatMap {p q : M} (i : Om n p q → OmStar p q) : Prop := ∀ (w : Om n p q) (t : unitInterval), (i w).1 t = w.1 t

/-- Evaluation at the break points: `w ↦ (w(t_1), …, w(t_{k-1}))`. -/
def evalPts (k : ℕ) (t : ℕ → ℝ) (w : ℝ → M) : Fin (k - 1) → M := fun j => w (t ((j : ℕ) + 1))

/-- `B = Int Ω(t₀,…,t_k)^c`: broken geodesics (for the subdivision `t`) with energy `< c`. -/
def Bset (cov : Conn n M) (p q : M) (c : ℝ) (k : ℕ) (t : ℕ → ℝ) : Set (Om n p q) :=
  {w | w.1 ∈ OmegaSub cov p q k t ∧ Efun (n := n) w.1 < c}
/-- `B^a = {w ∈ B | E(w) ≤ a}`. -/
def BsetA (cov : Conn n M) (p q : M) (c : ℝ) (k : ℕ) (t : ℕ → ℝ) (a : ℝ) : Set (Om n p q) :=
  {w | w ∈ Bset n cov p q c k t ∧ Efun (n := n) w.1 ≤ a}

/-- Hypotheses of §16: `c > 0`, `ε > 0` as in Lemma 10.8 for the compact set `S = {r | ρ(p,r) ≤ √c}`,
and a subdivision `0 = t₀ < … < t_k = 1` with `t_i - t_{i-1} < ε²/c`. -/
def Setup16 (cov : Conn n M) (p _q : M) (c ε : ℝ) (k : ℕ) (t : ℕ → ℝ) : Prop :=
  0 < c ∧ 0 < ε ∧ ShortGood cov {r | rho (n := n) p r ≤ Real.sqrt c} ε ∧
  t 0 = 0 ∧ t k = 1 ∧ (∀ i < k, t i < t (i + 1)) ∧ ∀ i < k, t (i + 1) - t i < ε ^ 2 / c

/-- The product manifold model `M × ⋯ × M` (`m` factors). -/
noncomputable abbrev Ipi (m : ℕ) := ModelWithCorners.pi (fun _ : Fin m => 𝓘(ℝ, Rn n))

/-- `F`, `V` represent `E' : B → ℝ` in the coordinates `w ↦ (w(t_1),…,w(t_{k-1}))` of `B ⊆ M^{k-1}`. -/
def IsEprime (cov : Conn n M) (p q : M) (c : ℝ) (k : ℕ) (t : ℕ → ℝ)
    (F : (Fin (k - 1) → M) → ℝ) (V : Set (Fin (k - 1) → M)) : Prop :=
  V = (fun w : Om n p q => evalPts k t w.1) '' Bset n cov p q c k t ∧
  ContMDiffOn (Ipi n (k - 1)) 𝓘(ℝ, ℝ) ∞ F V ∧
  ∀ w ∈ Bset n cov p q c k t, F (evalPts k t w.1) = Efun (n := n) w.1

/-- Deformation retract (the strong kind: the retraction homotopy fixes `A` pointwise) of `A` in `X`, inside an ambient
space `Y`: `H : [0,1] × Y → Y` continuous on `[0,1] × X`, `H 0 = id`, `H 1 (X) ⊆ A`, `H t (X) ⊆ X`, `H t |A = id`. -/
def IsDefRetract {Y : Type} [TopologicalSpace Y] (X A : Set Y) : Prop :=
  A ⊆ X ∧ ∃ H : unitInterval → Y → Y, ContinuousOn (fun z : unitInterval × Y => H z.1 z.2) (Set.univ ×ˢ X) ∧
    (∀ x ∈ X, H 0 x = x) ∧ (∀ x ∈ X, H 1 x ∈ A) ∧ (∀ x ∈ X, ∀ s, H s x ∈ X) ∧ ∀ a ∈ A, ∀ s, H s a = a

/-- Milnor's retraction `r : Int Ω^c → B` and deformation `r_u` (Lemma 16.C), with all properties he states.
`R u` is `r_u`, defined for `u ∈ [0,1]`. -/
def IsRetr16 (cov : Conn n M) (p q : M) (c ε : ℝ) (k : ℕ) (t : ℕ → ℝ)
    (r : Om n p q → Om n p q) (R : unitInterval → Om n p q → Om n p q) : Prop :=
  (∀ w ∈ IntOm n p q c, r w ∈ Bset n cov p q c k t) ∧
  (∀ w ∈ Bset n cov p q c k t, r w = w) ∧
  (∀ w ∈ IntOm n p q c, ∀ i < k, ∃ γ, JoinsShort cov ε γ (w.1 (t i)) (w.1 (t (i + 1))) ∧
      ∀ s ∈ Set.Icc (t i) (t (i + 1)), (r w).1 s = γ ((s - t i) / (t (i + 1) - t i))) ∧
  (∀ w ∈ IntOm n p q c, Efun (n := n) (r w).1 ≤ Efun (n := n) w.1) ∧
  (∀ w ∈ IntOm n p q c, R 0 w = w) ∧ (∀ w ∈ IntOm n p q c, R 1 w = r w) ∧
  ContinuousOn (fun z : unitInterval × Om n p q => R z.1 z.2) (Set.univ ×ˢ IntOm n p q c) ∧
  ∀ w ∈ IntOm n p q c, ∀ i < k, ∀ u : unitInterval, t i ≤ (u : ℝ) → (u : ℝ) ≤ t (i + 1) →
    (∀ s ∈ Set.Icc 0 (t i), (R u w).1 s = (r w).1 s) ∧
    (∃ γ, JoinsShort cov ε γ (w.1 (t i)) (w.1 u) ∧ ∀ s ∈ Set.Icc (t i) (u : ℝ), (R u w).1 s = γ ((s - t i) / (u - t i))) ∧
    (∀ s ∈ Set.Icc (u : ℝ) 1, (R u w).1 s = w.1 s)

/-- Critical point of a function on the product manifold: vanishing differential. -/
def IsCritPi (m : ℕ) (F : (Fin m → M) → ℝ) (x : Fin m → M) : Prop :=
  mfderiv (Ipi n m) 𝓘(ℝ, ℝ) F x = 0

/-- `r = F_**(v, w)` at `x` on the product manifold: `r = ∂²F(α(u₁,u₂))/∂u₁∂u₂(0,0)` for a smooth 2-parameter map `α` into
`M^m` with `α 0 = x`, `∂α/∂u₁(0) = v`, `∂α/∂u₂(0) = w` (Milnor's definition of the Hessian). -/
def IsHessPi (m : ℕ) (F : (Fin m → M) → ℝ) (x : Fin m → M) (v w : Fin m → Rn n) (r : ℝ) : Prop :=
  ∃ (U : Set (Rn 2)) (α : Rn 2 → (Fin m → M)), IsOpen U ∧ (0 : Rn 2) ∈ U ∧ ContMDiffOn 𝓘(ℝ, Rn 2) (Ipi n m) ∞ α U ∧ α 0 = x ∧
    (mfderiv 𝓘(ℝ, Rn 2) (Ipi n m) α 0 (EuclideanSpace.single 0 (1 : ℝ)) : Fin m → Rn n) = v ∧
    (mfderiv 𝓘(ℝ, Rn 2) (Ipi n m) α 0 (EuclideanSpace.single 1 (1 : ℝ)) : Fin m → Rn n) = w ∧
    DifferentiableAt ℝ (fun u : Rn 2 => fderiv ℝ (fun v' : Rn 2 => F (α v')) u (EuclideanSpace.single 0 (1 : ℝ))) 0 ∧
    mixedD (fun u : Rn 2 => F (α u)) = r

open Classical in
/-- `F_**` as a function (value `0` if no realizing variation exists). -/
noncomputable def HessPi (m : ℕ) (F : (Fin m → M) → ℝ) (x : Fin m → M) (v w : Fin m → Rn n) : ℝ :=
  if h : ∃ r, IsHessPi n m F x v w r then h.choose else 0

/-- `γ` is a geodesic from `p` to `q` (on `[0,1]`). -/
def IsGeodPQ (cov : Conn n M) (p q : M) (γ : ℝ → M) : Prop :=
  IsGeodesic cov γ (Set.Icc 0 1) ∧ γ 0 = p ∧ γ 1 = q

/-- `a` is a critical value of `E` on `Ω(M;p,q)`: the energy of some geodesic from `p` to `q`. -/
def IsCritVal (cov : Conn n M) (p q : M) (a : ℝ) : Prop :=
  ∃ γ, IsGeodPQ n cov p q γ ∧ Efun (n := n) γ = a

/-- `p`, `q` are not conjugate along any geodesic from `p` to `q`. -/
def NonConjPQ (cov : Conn n M) (p q : M) : Prop :=
  ∀ γ, IsGeodPQ n cov p q γ → ¬ IsConj cov γ 0 1

/-- A continuous path `γ ∈ Ω*` represents (on `[0,1]`) the geodesic `g`. -/
def IsGeodRep (cov : Conn n M) {p q : M} (γ : OmStar p q) (g : ℝ → M) : Prop :=
  IsGeodesic cov g (Set.Icc 0 1) ∧ ∀ t : unitInterval, γ.1 t = g t

/-- The geodesics from `p` to `q` (as elements of `Ω*`) of index `l` whose energy lies in `J`. -/
def GeodIdx (cov : Conn n M) (p q : M) (l : ℕ) (J : Set ℝ) : Set (OmStar p q) :=
  {γ | ∃ g, IsGeodRep n cov γ g ∧ lam (n := n) 1 g = l ∧ Efun (n := n) g ∈ J}

/-- Sets of measure zero in a manifold (Milnor §6): every chart image has Lebesgue measure `0`. -/
def MfdNull (S : Set M) : Prop :=
  ∀ x : M, MeasureTheory.volume ((extChartAt 𝓘(ℝ, Rn n) x) '' (S ∩ (extChartAt 𝓘(ℝ, Rn n) x).source)) = 0

/-- A smooth map `f` between manifolds is *critical* at `x` if `f_* : TN_x → TM_{f x}` is not one-to-one. -/
def IsCritMap {N : Type} [TopologicalSpace N] [ChartedSpace (Rn n) N] (f : N → M) (x : N) : Prop :=
  ¬ Function.Injective (mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) f x)

/-- Sectional curvature `≤ 0` in Milnor's form: `⟨R(A,B)A,B⟩ ≤ 0` for all `A, B ∈ TM_p`. -/
def NonPosCurv (cov : Conn n M) : Prop :=
  ∀ (p : M) (x y r : TangentSpace 𝓘(ℝ, Rn n) p), IsCurvVal cov p x y x r → inner ℝ r y ≤ 0

/-- Broken-geodesic interpolation of §17: `h(w)` agrees with `w` at `0, A, 2A, …, kA, 1` (`k = ⌊1/A⌋`), each piece of `w`
lies in a neighbourhood `U` as in Milnor §10 (`GoodNbhd`) and `h(w)` is the minimal geodesic on it. -/
def IsBrokenInterp (cov : Conn n M) {p q : M} (A : OmStar p q → ℝ) (h : OmStar p q → Om n p q) : Prop :=
  ∀ w : OmStar p q, 0 < A w ∧ A w ≤ 1 ∧
    ∀ j : ℕ, j ≤ ⌊1 / A w⌋₊ → (h w).1 ((j : ℝ) * A w) = evS w ((j : ℝ) * A w) ∧
      ((j : ℝ) * A w < 1 →
        (∃ U, GoodNbhd cov U ∧ ∀ s : unitInterval, (j : ℝ) * A w ≤ s → (s : ℝ) ≤ min (((j : ℝ) + 1) * A w) 1 → w.1 s ∈ U) ∧
        IsMinimal cov (h w).1 ((j : ℝ) * A w) (min (((j : ℝ) + 1) * A w) 1))

/-- `f : C(X,Y)` maps into `K ⊆ Y` and is a homotopy equivalence `X → K`. -/
def IsHEOnto {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (K : Set Y) : Prop :=
  ∃ hK : ∀ x, f x ∈ K, ∃ g : C(K, X),
    (g.comp (ContinuousMap.mk (Set.codRestrict f K hK) (f.continuous.subtype_mk hK))).Homotopic (ContinuousMap.id X) ∧
    ((ContinuousMap.mk (Set.codRestrict f K hK) (f.continuous.subtype_mk hK)).comp g).Homotopic (ContinuousMap.id K)

/-- Singular homology `H_i(X; ℤ)`. -/
noncomputable def singH (i : ℕ) (X : Type) [TopologicalSpace X] : ModuleCat ℤ :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) i).obj (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)

/-- `M` is (isometric to) the round unit sphere `S^n ⊆ ℝ^{n+1}`: `ψ` is a smooth injective map onto the unit sphere whose
differential is isometric for the Riemannian metric of `M` and the Euclidean inner product. -/
def IsRoundSphere (ψ : M → EuclideanSpace ℝ (Fin (n + 1))) : Prop :=
  ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ ψ ∧ Function.Injective ψ ∧
  Set.range ψ = Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ∧
  ∀ (x : M) (v w : TangentSpace 𝓘(ℝ, Rn n) x),
    inner ℝ v w = inner ℝ (mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ψ x v)
      (mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ψ x w)
end Ch10

section Curv
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]

open Classical in
/-- The curvature tensor `R(x,y)z` at `p` (Milnor's sign, via `IsCurvVal`); junk value `0` if no value exists. -/
noncomputable def curvR (cov : Conn n M) (p : M) (x y z : TangentSpace 𝓘(ℝ, Rn n) p) : TangentSpace 𝓘(ℝ, Rn n) p :=
  if h : ∃ r, IsCurvVal cov p x y z r then h.choose else 0

open Classical in
/-- The Ricci tensor `K(U₁,U₂) = trace (W ↦ R(U₁,W)U₂)` (Milnor §19; trace of the linear map `W ↦ R(U₁,W)U₂` of `TM_p ≅ ℝⁿ`;
junk value `0` if that map is not linear). -/
noncomputable def ricci (cov : Conn n M) (p : M) (U₁ U₂ : TangentSpace 𝓘(ℝ, Rn n) p) : ℝ :=
  if h : ∃ L : Rn n →ₗ[ℝ] Rn n, ∀ W : Rn n, L W = curvR cov p U₁ W U₂ then LinearMap.trace ℝ (Rn n) h.choose else 0

/-- The index `n - 1` (Milnor's "`n`-th" basis vector) of `Fin n`, `n ≥ 1`. -/
def lastIdx (n : ℕ) (hn : 0 < n) : Fin n := ⟨n - 1, by omega⟩

/-- Milnor's Ricci hypothesis: `K(U,U) ≥ c` for every unit vector `U` at every point. -/
def RicciGE (cov : Conn n M) (c : ℝ) : Prop :=
  ∀ (p : M) (U : TangentSpace 𝓘(ℝ, Rn n) p), ‖U‖ = 1 → c ≤ ricci cov p U U
end Curv


section Ch22
variable (n : ℕ) {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]

/-- `d = ρ(p, q)²`. -/
noncomputable def dPQ (p q : M) : ℝ := rho (n := n) p q ^ 2

/-- `Ω^d = E⁻¹[0, d] ⊆ Ω = Ω(M; p, q)` with `d = ρ(p, q)²` (Milnor's notation `Ω^c`, here `c = d`); as a type it carries
the subspace topology of `Ω` (Milnor's `d`-topology). -/
def OmD (p q : M) : Set (Om n p q) := OmLe n p q (dPQ n p q)

/-- The inclusion `Ω^d → Ω`. -/
def inclD (p q : M) : C(↥(OmD n p q), Om n p q) := ⟨Subtype.val, continuous_subtype_val⟩
end Ch22

section Htpy

/-- A topological manifold: a Hausdorff space in which every point has an open neighbourhood homeomorphic to an open
subset of some `ℝ^m` (the dimension `m` may depend on the point; no second countability is required). -/
def IsTopMfd (X : Type) [TopologicalSpace X] : Prop :=
  T2Space X ∧ ∀ x : X, ∃ (m : ℕ) (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin m))), x ∈ e.source

/-- `π_i(X, A) = 0` for every base point in `A` (for `i = 0`: every path component of `X` meets `A`), in the form of the
compression criterion: every map `(I^i, ∂I^i) → (X, A)` is homotopic rel `∂I^i` to a map into `A`. -/
def RelPiTrivial (X : Type) [TopologicalSpace X] (A : Set X) (i : ℕ) : Prop :=
  ∀ f : C(Fin i → unitInterval, X), (∀ y ∈ Cube.boundary (Fin i), f y ∈ A) →
    ∃ g : C(Fin i → unitInterval, X), (∀ y, g y ∈ A) ∧ f.HomotopicRel g (Cube.boundary (Fin i))

/-- `f ∘ γ` for a generalized loop `γ : (I^N, ∂I^N) → (X, x)`. -/
def genLoopMap {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) {x : X}
    (γ : ↥(GenLoop N X x)) : ↥(GenLoop N Y (f x)) :=
  ⟨f.comp γ.1, fun y hy => by simp [GenLoop.boundary γ y hy]⟩

/-- The homomorphism `f_* : π_N(X, x) → π_N(Y, f x)` induced by a map `f` (Mathlib's `HomotopyGroup`). -/
def piMap {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (x : X) :
    HomotopyGroup N X x → HomotopyGroup N Y (f x) :=
  Quotient.map' (genLoopMap f) (fun _ _ h => ContinuousMap.HomotopicRel.comp_continuousMap h f)
end Htpy

section Hyp22
variable (n : ℕ) {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]

/-- Hypotheses of Theorem 22.1 for `p, q` and `λ₀` (written `l0`): the space `Ω^d` of minimal geodesics is a topological
manifold (its separation quotient: `Ω` does not distinguish paths that agree on `[0,1]`), and every non-minimal geodesic
from `p` to `q` has index `λ ≥ λ₀`. -/
def Hyp221 (cov : Conn n M) (p q : M) (l0 : ℕ) : Prop :=
  IsTopMfd (SeparationQuotient ↥(OmD n p q)) ∧
  ∀ γ : ℝ → M, IsGeodPQ n cov p q γ → ¬ IsMinimal cov γ 0 1 → (l0 : ℕ∞) ≤ lam (n := n) 1 γ
end Hyp22

section Hyp225
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M]

/-- Hypotheses of Lemma 22.5 on `f`, except the index condition: `f` smooth with minimum `0`, each
`M^c = f⁻¹[0,c]` compact, and the set `M⁰ = f⁻¹(0)` of minimal points a topological manifold. -/
def Hyp225 (f : M → ℝ) : Prop :=
  ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, ℝ) ∞ f ∧ (∀ x, 0 ≤ f x) ∧ (∃ x, f x = 0) ∧
    (∀ c : ℝ, IsCompact {x | f x ≤ c}) ∧ IsTopMfd ↥{x : M | f x = 0}
end Hyp225

/-- In Lemma 22.5 (for any Riemannian metric on `M`): `M⁰` is a retract of a neighbourhood `U` whose points are joined to
their images by unique minimal geodesics, and `U` deforms into `M⁰` within `M` along these geodesics. -/
def B : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M] [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)] [IsContMDiffRiemannianBundle 𝓘(ℝ, Rn n) ∞ (Rn n) (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)], ∀ (cov : Conn n M), IsLC cov →
    ∀ f : M → ℝ, Hyp225 (n := n) f →
    ∃ (U : Set M) (r : M → M), IsOpen U ∧ {x | f x = 0} ⊆ U ∧ ContinuousOn r U ∧ (∀ x ∈ U, f (r x) = 0) ∧
      (∀ x, f x = 0 → r x = x) ∧
      (∀ x ∈ U, ∃ γ : ℝ → M, IsMinimal cov γ 0 1 ∧ γ 0 = x ∧ γ 1 = r x ∧
        ∀ γ' : ℝ → M, IsMinimal cov γ' 0 1 → γ' 0 = x → γ' 1 = r x → Set.EqOn γ γ' (Set.Icc 0 1)) ∧
      ∃ H : unitInterval → M → M, ContinuousOn (fun z : unitInterval × M => H z.1 z.2) (Set.univ ×ˢ U) ∧
        (∀ x ∈ U, H 0 x = x) ∧ (∀ x ∈ U, f (H 1 x) = 0) ∧
        ∀ x ∈ U, ∃ γ : ℝ → M, IsMinimal cov γ 0 1 ∧ γ 0 = x ∧ γ 1 = r x ∧ ∀ t : unitInterval, H t x = γ t

end RoundTrip.V13_15
