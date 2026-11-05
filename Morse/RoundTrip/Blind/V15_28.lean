import Morse
/-! Blind formalization of V15_28 (Milnor §24, pp. 144, 146: Killing fields are Jacobi fields; a lower bound for the index). Choices:
- Setting as in the blind files V15_1–V15_11 (prelude copied verbatim from them): real matrices `Mat ι = Matrix ι ι ℝ`
  over a finite index type `ι` (Milnor's `ℝⁿ` is `ι = Fin n`;
  `ℝⁿ ⊕ ℝ^{n'}` is `ι = Fin n ⊕ Fin n'`), product topology; `O(n) = Orth (Fin n)` = Mathlib's
  `Matrix.orthogonalGroup (Fin n) ℝ` (`Aᵀ A = 1`) as a subset of `M_n(ℝ)` with the subspace topology (Mathlib matrix
  groups as subsets, as in the §23 blind files V14_*); Milnor's `A*` is `Aᵀ`. `IsSkew A` (`Aᵀ = -A`, `A ∈ 𝔬(n)`);
  `IsCplxStr J` (`J ∈ O(n)` and `J² = -I`, Milnor p. 133; defined for every `n`, non-existent for odd `n`);
  `AntiComm A B` (`AB = -BA`); the fixed structures are a sequence `Js : ℕ → M_n(ℝ)` indexed like Milnor's
  `J_1, J_2, …` (`Js 0` unused), `IsACFam Js m` = `Js 1, …, Js m` are anticommuting complex structures; `OmegaK Js k`
  = Milnor's `Ω_k(n)` (`Ω_0(n) = O(n)`; for `k ≥ 1` the complex structures anticommuting with `Js 1, …, Js (k-1)`);
  `mexp` = Mathlib's matrix exponential `NormedSpace.exp`. Calculus on `M_n(ℝ)` uses the scoped elementwise norm (as
  in V12_14 / V14_*; any norm gives the same notions).
- Metric and geometry: Milnor's `⟨A, B⟩ = tr(ABᵀ)` (`frob`, p. 125) on `M_n(ℝ)`, restricted to `O(n)` (where it is
  bi-invariant) and to `Ω_k(n)`. Mathlib has no manifold structure on `O(n)`, so the Riemannian notions are those of a
  subset `N ⊆ M_n(ℝ)` with the induced metric, defined by hand: `TanSet N p` (velocities at `p` of smooth curves in
  `N`), geodesics `IsGeodOn N γ a b` (smooth on `[a,b]`, values in `N`, acceleration `⊥ TanSet N`, i.e.
  `D/dt dγ/dt = 0` for a submanifold of Euclidean space), piecewise smooth paths `IsPathIn N w` on `[0,1]`, length
  `lenM`, energy `enM`, minimal geodesics `IsMinGeodIn N γ` (a geodesic on `[0,1]` no longer than any piecewise smooth
  path in `N` with the same end points, as `IsMinimal` of V13_1), variations `IsVarIn` (Milnor §12, end points fixed,
  smooth on strips), `T Ω_γ` (`IsVarFieldIn`), and the index `idxIn N γ : ℕ∞` (Milnor §13: the maximal dimension of a
  subspace of `T Ω_γ` on which `E_**(W,W) = d²E(α_u)/du²|₀` (`α` a variation in `N` with field `W`) is negative
  definite). (The §23 blind files V14_20/V14_22, written in parallel, model `SU(n)` instead as an abstract Riemannian
  manifold with an isometric embedding onto the matrix group, `IsSUModel`; the notions agree for the induced metric.)
- Setting (pp. 144–146): `k ≥ 1`, fixed anticommuting `J_1, …, J_{k-1}` (`IsACFam Js (k - 1)`), `J ∈ Ω_k(n)`; Milnor's
  `T` (`Tsp`, the tangent space of `Ω_k(n)` at `J` translated to the Lie algebra, Assertions 1–2 / V15_22) = the skew
  `B` anticommuting with `J` and commuting with `J_1, …, J_{k-1}`; `A ∈ T` with `exp(πA) = −I`, and the geodesic
  `γ(t) = J exp(πtA)` (`geoJA`, defined on all of `ℝ`) from `J` to `−J` in `Ω_k(n)`. All `n`. (`k = 0` is the setting
  of Lemma 24.2, V15_3/V15_30, with `T = 𝔬(n)`; not covered here.)
- `K_A B = −¼[A, [A, B]]` (`KA`, literally Milnor's formula; with velocity `πA` the curvature operator is `π²K_A`, which
  is why the conjugate parameters are `j/e`). The premise "since `Ω_k(n)` is totally geodesic, `K_A` can be computed by
  this formula" is about the curvature tensor of `Ω_k(n)`, which the prelude does not define; it is formalized through
  its consequences: (1) `K_A` maps `T` into `T` (so "the eigenvalues of `K_A` on `T`" make sense); `mult(μ)` =
  `dim {B ∈ T | K_A B = μB}` (`eigMultT`).
- (2) "Each eigenvalue `e²` of `K_A` gives rise to conjugate points for `t = e⁻¹, 2e⁻¹, …` (20.5)": for every `μ = e² > 0`
  and `j ≥ 1`, `γ(j/e)` is conjugate to `γ(0) = J` along `γ` in `Ω_k(n)` with multiplicity `≥ mult(μ)` (vacuous unless
  `μ` is an eigenvalue). Jacobi fields of a subset `N` are defined, as in Milnor §14 for complete manifolds (and in the
  spirit of the title "Killing fields are Jacobi fields"), as the variation fields `W = ∂α/∂u|_{u=0}` of smooth
  variations `α` of `γ|[0,b]` through geodesics of `N` (`IsGeodVarField`; `W = 0` off `[0, b]`); the multiplicity of
  `γ(b)` as a conjugate point (`conjDim N γ b : ℕ∞`) is the maximal dimension of a space of such fields vanishing at
  `0` and `b`.
- (3) "Then apply the index theorem" (the title's lower bound): `idxIn (Ω_k(n)) γ ≥ Σ_{μ > 0} mult(μ) · #{j ≥ 1 | j/√μ < 1}`
  (the conjugate points `γ(j/e)` in the open interval `(0, 1)`, counted with these multiplicities; `#{…} = nBelow μ`;
  a finite sum, `finsum`). Only the lower bound is stated, as in the title (Theorem 20.5 with the index theorem would
  give equality).
-/
namespace RoundTrip.V15_28

open scoped Matrix ContDiff Topology
open scoped Matrix.Norms.Elementwise

section Prelude
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `M(ι) = M_ι(ℝ)`: real square matrices indexed by the finite type `ι`, i.e. endomorphisms of `ℝ^ι` (Milnor's `ℝⁿ`
is `ι = Fin n`; `ℝⁿ ⊕ ℝ^{n'}` is `ι = Fin n ⊕ Fin n'`). Product topology; the elementwise norm (opened above) is
used only to do calculus (`ContDiff`, `deriv`), which does not depend on the choice of norm. -/
abbrev Mat (ι : Type) : Type := Matrix ι ι ℝ

/-- `O(ι)`: Mathlib's orthogonal group (`A ∈ O(ι) ↔ Aᵀ * A = 1`), as a subset of `M(ι)` (subspace topology). -/
abbrev Orth (ι : Type) [Fintype ι] [DecidableEq ι] : Set (Mat ι) := (Matrix.orthogonalGroup ι ℝ : Set (Mat ι))

/-- `A ∈ 𝔬(ι)`: `A` is skew-symmetric, `Aᵀ = -A` (Milnor's `A* = -A`; for real matrices `A* = Aᵀ`). -/
def IsSkew (A : Mat ι) : Prop := Aᵀ = -A

/-- Milnor p. 133: a complex structure on `ℝ^ι` is an orthogonal `J` with `J² = -I` (defined for every `ι`; it
exists only when `card ι` is even). -/
def IsCplxStr (J : Mat ι) : Prop := J ∈ Matrix.orthogonalGroup ι ℝ ∧ J * J = -1

/-- `A` and `B` anticommute: `AB = -BA`. -/
def AntiComm (A B : Mat ι) : Prop := A * B = -(B * A)

/-- `Js 1, …, Js m` are anticommuting complex structures (Milnor p. 136); `Js α` for `α = 0` or `α > m` is ignored. -/
def IsACFam (Js : ℕ → Mat ι) (m : ℕ) : Prop :=
  (∀ α, 1 ≤ α → α ≤ m → IsCplxStr (Js α)) ∧
  ∀ α β, 1 ≤ α → α ≤ m → 1 ≤ β → β ≤ m → α ≠ β → AntiComm (Js α) (Js β)

/-- Milnor's `Ω_k(n)` (p. 136) for the fixed `J_1, …, J_{k-1}` (= `Js 1, …, Js (k-1)`): `Ω_0 = O(n)`, and for `k ≥ 1`
the complex structures anticommuting with `J_1, …, J_{k-1}` (so `Ω_1` = all complex structures). -/
def OmegaK (Js : ℕ → Mat ι) : ℕ → Set (Mat ι)
  | 0 => Orth ι
  | k + 1 => {J | IsCplxStr J ∧ ∀ α, 1 ≤ α → α ≤ k → AntiComm J (Js α)}

/-- Milnor's inner product on matrices, `⟨A, B⟩ = tr(A B*) = tr(A Bᵀ)` (p. 125): the Euclidean (Frobenius) inner
product of `M(ι) ≅ ℝ^{ι × ι}`; it restricts to the bi-invariant metric of `O(ι)`. -/
def frob (A B : Mat ι) : ℝ := Matrix.trace (A * Bᵀ)

/-- The matrix exponential `exp A = Σ Aᵏ/k!` (Mathlib's `NormedSpace.exp`). -/
noncomputable abbrev mexp (A : Mat ι) : Mat ι := NormedSpace.exp A

/-! Riemannian geometry of a subset `N ⊆ M(ι)` with the metric induced by `frob` (`N = O(ι)`, `N = Ω_k(n)`). -/

/-- `T_pN`: the velocities at `0` of smooth curves in `N` through `p` (the tangent space when `N` is a submanifold;
for `N = O(ι)` it is `p·𝔬(ι)`). -/
def TanSet (N : Set (Mat ι)) (p : Mat ι) : Set (Mat ι) :=
  {v | ∃ c : ℝ → Mat ι, ContDiff ℝ ∞ c ∧ (∀ s, c s ∈ N) ∧ c 0 = p ∧ HasDerivAt c v 0}

/-- `γ` is a geodesic of `N` on `[a, b]` (`a < b`) for the induced metric: smooth on `[a, b]`, with values in `N`, and
acceleration normal to `N` (`D/dt (dγ/dt) = 0`, the covariant derivative of a submanifold of Euclidean space being the
tangential part of the ordinary derivative). -/
def IsGeodOn (N : Set (Mat ι)) (γ : ℝ → Mat ι) (a b : ℝ) : Prop :=
  a < b ∧ ContDiffOn ℝ ∞ γ (Set.Icc a b) ∧ (∀ t ∈ Set.Icc a b, γ t ∈ N) ∧
    ∀ t ∈ Set.Icc a b, ∀ v ∈ TanSet N (γ t), frob (iteratedDerivWithin 2 γ (Set.Icc a b) t) v = 0

/-- Piecewise smooth on `[0, 1]`: smooth on each piece of a subdivision `0 = t₀ < ⋯ < t_k = 1`. -/
def IsPWOn (f : ℝ → Mat ι) : Prop :=
  ∃ (k : ℕ) (t : ℕ → ℝ), t 0 = 0 ∧ t k = 1 ∧ (∀ i < k, t i < t (i + 1)) ∧
    ∀ i < k, ContDiffOn ℝ ∞ f (Set.Icc (t i) (t (i + 1)))

/-- A piecewise smooth path `[0, 1] → N` (only the values on `[0, 1]` matter). -/
def IsPathIn (N : Set (Mat ι)) (w : ℝ → Mat ι) : Prop := IsPWOn w ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, w t ∈ N

/-- Length `∫₀¹ ‖dw/dt‖ dt` (the derivative exists off a finite set). -/
noncomputable def lenM (w : ℝ → Mat ι) : ℝ := ∫ t in (0 : ℝ)..1, Real.sqrt (frob (deriv w t) (deriv w t))

/-- Energy `E(w) = ∫₀¹ ‖dw/dt‖² dt`. -/
noncomputable def enM (w : ℝ → Mat ι) : ℝ := ∫ t in (0 : ℝ)..1, frob (deriv w t) (deriv w t)

/-- Minimal geodesic of `N` (Milnor p. 61): a geodesic `[0, 1] → N` whose length is `≤` that of every piecewise smooth
path in `N` with the same end points. -/
def IsMinGeodIn (N : Set (Mat ι)) (γ : ℝ → Mat ι) : Prop :=
  IsGeodOn N γ 0 1 ∧ ∀ w, IsPathIn N w → w 0 = γ 0 → w 1 = γ 1 → lenM γ ≤ lenM w

/-- `α` is a variation of the path `γ` through paths in `N` with fixed end points (Milnor §12), with variation field
`W` (`W t = ∂α/∂u (0, t)`): `α 0 = γ` on `[0, 1]`, and for some `ε > 0` and subdivision `0 = s₀ < ⋯ < s_k = 1`, `α` is
smooth on each strip `(-ε, ε) × [s_i, s_{i+1}]` and each `α u` (`|u| < ε`) is a path in `N` from `γ 0` to `γ 1`. -/
def IsVarIn (N : Set (Mat ι)) (γ : ℝ → Mat ι) (α : ℝ → ℝ → Mat ι) (W : ℝ → Mat ι) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) 1, α 0 t = γ t) ∧
  ∃ ε > (0 : ℝ), ∃ (k : ℕ) (s : ℕ → ℝ), s 0 = 0 ∧ s k = 1 ∧ (∀ i < k, s i < s (i + 1)) ∧
    (∀ i < k, ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => α x.1 x.2) (Set.Ioo (-ε) ε ×ˢ Set.Icc (s i) (s (i + 1)))) ∧
    (∀ u ∈ Set.Ioo (-ε) ε, (∀ t ∈ Set.Icc (0 : ℝ) 1, α u t ∈ N) ∧ α u 0 = γ 0 ∧ α u 1 = γ 1) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun u => α u t) (W t) 0

/-- Milnor's `T Ω_γ` for paths in `N`: piecewise smooth fields `W` along `γ`, tangent to `N`, with `W 0 = W 1 = 0`
(normalized by `W = 0` off `[0, 1]`). -/
def IsVarFieldIn (N : Set (Mat ι)) (γ W : ℝ → Mat ι) : Prop :=
  IsPWOn W ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, W t ∈ TanSet N (γ t)) ∧ W 0 = 0 ∧ W 1 = 0 ∧
    ∀ t ∉ Set.Icc (0 : ℝ) 1, W t = 0

/-- `E_**(W, W) < 0` at the geodesic `γ` of `N` (Milnor §13): some variation of `γ` in `N` with variation field `W`
has `d²E(α u)/du² < 0` at `u = 0` (Milnor: at a geodesic this second derivative is `E_**(W, W)` for every such
variation). -/
def HessNeg (N : Set (Mat ι)) (γ W : ℝ → Mat ι) : Prop :=
  ∃ α : ℝ → ℝ → Mat ι, IsVarIn N γ α W ∧ iteratedDeriv 2 (fun u => enM (α u)) 0 < 0

/-- The index of a geodesic `γ : [0, 1] → N` (Milnor §13): the maximal dimension of a space of fields in `T Ω_γ` on
which `E_**` is negative definite (`ℕ∞`-valued, `⊤` if unbounded). -/
noncomputable def idxIn (N : Set (Mat ι)) (γ : ℝ → Mat ι) : ℕ∞ :=
  ⨆ (V : Submodule ℝ (ℝ → Mat ι)) (_ : FiniteDimensional ℝ V ∧ (∀ W ∈ V, IsVarFieldIn N γ W) ∧
      ∀ W ∈ V, W ≠ 0 → HessNeg N γ W), (Module.finrank ℝ V : ℕ∞)
end Prelude

section KillingJacobi
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Milnor's `T` at `J ∈ Ω_k(n)`: the skew `B` which anticommute with `J` and commute with `J_1, …, J_{k-1}`. -/
def Tsp (Js : ℕ → Mat ι) (k : ℕ) (J : Mat ι) : Set (Mat ι) :=
  {B | IsSkew B ∧ AntiComm B J ∧ ∀ α, 1 ≤ α → α ≤ k - 1 → Commute B (Js α)}

/-- Milnor's `K_A B = −¼[A, [A, B]]`. -/
noncomputable def KA (A B : Mat ι) : Mat ι :=
  (-1 / 4 : ℝ) • (A * (A * B - B * A) - (A * B - B * A) * A)

/-- The multiplicity of `μ` as an eigenvalue of `K_A` on `T`: `dim {B ∈ T | K_A B = μB}`. -/
noncomputable def eigMultT (Js : ℕ → Mat ι) (k : ℕ) (J A : Mat ι) (μ : ℝ) : ℕ :=
  Module.finrank ℝ (Submodule.span ℝ {B : Mat ι | B ∈ Tsp Js k J ∧ KA A B = μ • B})

/-- The geodesic `t ↦ J exp(πtA)`. -/
noncomputable def geoJA (J A : Mat ι) : ℝ → Mat ι := fun t => J * mexp ((Real.pi * t) • A)

/-- `W` is a Jacobi field of `N` along `γ|[0, b]`: the variation field `W(t) = ∂α/∂u (0, t)` (`t ∈ [0, b]`; `W = 0`
elsewhere) of a smooth variation `α` of `γ|[0, b]` through geodesics `α u` of `N` on `[0, b]`. -/
def IsGeodVarField (N : Set (Mat ι)) (γ : ℝ → Mat ι) (b : ℝ) (W : ℝ → Mat ι) : Prop :=
  ∃ (α : ℝ → ℝ → Mat ι) (ε : ℝ), 0 < ε ∧ (∀ u ∈ Set.Ioo (-ε) ε, IsGeodOn N (α u) 0 b) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) b, α 0 t = γ t) ∧
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => α x.1 x.2) (Set.Ioo (-ε) ε ×ˢ Set.Icc (0 : ℝ) b) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) b, HasDerivAt (fun u => α u t) (W t) 0) ∧ ∀ t ∉ Set.Icc (0 : ℝ) b, W t = 0

/-- The multiplicity of `γ(b)` as a conjugate point of `γ(0)` along `γ|[0, b]` in `N`: the maximal dimension of a
space of Jacobi fields along `γ|[0, b]` vanishing at `0` and `b` (`0` if not conjugate). -/
noncomputable def conjDim (N : Set (Mat ι)) (γ : ℝ → Mat ι) (b : ℝ) : ℕ∞ :=
  ⨆ (V : Submodule ℝ (ℝ → Mat ι)) (_ : FiniteDimensional ℝ V ∧
      ∀ W ∈ V, IsGeodVarField N γ b W ∧ W 0 = 0 ∧ W b = 0), (Module.finrank ℝ V : ℕ∞)

/-- `#{j ≥ 1 | j² < μ}`: the number of conjugate parameters `j/√μ` in the open interval `(0, 1)`. -/
noncomputable def nBelow (μ : ℝ) : ℕ := Nat.card {j : ℕ // 1 ≤ j ∧ ((j : ℝ) ^ 2 < μ)}
end KillingJacobi

/-- For the geodesic `t ↦ J exp(πtA)` from `J` to `−J` in `Ω_k(n)` (`A ∈ T`): `K_A B = −¼[A, [A, B]]` preserves `T`;
each eigenvalue `e²` of `K_A` on `T` gives conjugate points at `t = j/e` (multiplicity `≥` that of `e²`); hence the
index is at least the number of these conjugate points in `(0, 1)`, counted with multiplicity. -/
def B : Prop :=
  ∀ (n k : ℕ) (Js : ℕ → Mat (Fin n)), 1 ≤ k → IsACFam Js (k - 1) →
    ∀ J ∈ OmegaK Js k, ∀ A ∈ Tsp Js k J, mexp (Real.pi • A) = -1 →
      (∀ B ∈ Tsp Js k J, KA A B ∈ Tsp Js k J) ∧
      (∀ μ : ℝ, 0 < μ → ∀ j : ℕ, 1 ≤ j →
        (eigMultT Js k J A μ : ℕ∞) ≤ conjDim (OmegaK Js k) (geoJA J A) (j / Real.sqrt μ)) ∧
      (((∑ᶠ (μ : ℝ) (_ : 0 < μ), eigMultT Js k J A μ * nBelow μ : ℕ) : ℕ∞) ≤ idxIn (OmegaK Js k) (geoJA J A))

end RoundTrip.V15_28
