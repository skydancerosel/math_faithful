import Morse
/-! Blind formalization of V15_3 (Milnor §24, Lemma 24.2 and its proof, p. 135). Choices:
- Setting (new for §24; the prelude is shared verbatim by the blind files V15_1–V15_11, for reuse by the other §24
  files): real matrices `Mat ι = Matrix ι ι ℝ` over a finite index type `ι` (Milnor's `ℝⁿ` is `ι = Fin n`;
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
- The index is Milnor's (§13), defined geometrically (`idxIn`), not through the spectrum of `K_A`: Milnor obtains the
  formula for `λ` from the eigenvalues by Theorem 20.5 and the Index Theorem, and that deduction is part of the claim.
- Claim 1 (Lemma 24.2): for every `m ≥ 0` and every geodesic `γ : [0,1] → O(2m)` (`IsGeodOn (Orth _) γ 0 1`) with
  `γ(0) = I`, `γ(1) = -I` which is not minimal (`¬ IsMinGeodIn`), `idxIn (O(2m)) γ ≥ 2m - 2` (truncated subtraction; for
  `m ≤ 1` the bound is `0`). `O(2m)` is `Orth (Fin (2 * m))`.
- Claims 2–3 are about Milnor's `A` with blocks `a_j (0 1; -1 0)`, on `ℝ^{2m} = ℝ^{Fin 2 × Fin m}` (block `j` on
  `e_(0,j), e_(1,j)`, Mathlib's `Matrix.blockDiagonal`, as in V15_2; a relabeling of coordinates is an orthogonal
  change of basis), with Milnor's hypotheses: `a_j ∈ ℤ` odd, `a_j > 0`, `a_1 ≥ ⋯ ≥ a_m` (`Antitone a`); `m ≥ 0`.
- Claim 2 (spectrum): `K_A(W) = R(A,W)A = ¼[[A,W],A]` (Milnor's formula for a bi-invariant metric, §21) acting on
  `𝔬(2m) = T_I O(2m)` (skew matrices). "The non-zero eigenvalues are `(a_i+a_j)²/4` (`i < j`) and `(a_i-a_j)²/4`
  (`i < j`, `a_i ≠ a_j`), each counted twice" is read as: for every `μ ≠ 0`, the `μ`-eigenspace of `K_A` in `𝔬(2m)`
  has dimension `2·#{i<j : (a_i+a_j)²/4 = μ} + 2·#{i<j : a_i ≠ a_j, (a_i-a_j)²/4 = μ}` (`K_A` is self-adjoint for
  `tr(ABᵀ)`, so geometric = algebraic multiplicity; equal values coming from different pairs add up; a `μ ≠ 0` of
  neither form is not an eigenvalue).
- Claim 3 ("so `λ = …`"): `γ(t) = exp(πtA)` is a geodesic of `O(2m)` from `I` to `-I` (Milnor's setting, included as
  conjuncts) and its index is `Σ_{i<j} (a_i + a_j - 2) + Σ_{a_i > a_j} (a_i - a_j - 2)`, the second sum over the
  ordered pairs `(i, j)` with `a_i > a_j` (computed in `ℤ`; it is `≥ 0` under the hypotheses, cast by `Int.toNat`).
-/
namespace RoundTrip.V15_3

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

/-- `σ = (0 1; -1 0)`. -/
def sig2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- The block-diagonal matrix on `ℝ^{2m} = ℝ^{Fin 2 × Fin m}` with `2 × 2` blocks `b j` (block `j` on
`e_(0,j), e_(1,j)`). -/
def blk {m : ℕ} (b : Fin m → Matrix (Fin 2) (Fin 2) ℝ) : Mat (Fin 2 × Fin m) := Matrix.blockDiagonal b

/-- Milnor's `A`, with blocks `a_j σ`. -/
def blkA {m : ℕ} (a : Fin m → ℤ) : Mat (Fin 2 × Fin m) := blk (fun j => (a j : ℝ) • sig2)

/-- The geodesic `t ↦ exp(πtA)`. -/
noncomputable def geoA {m : ℕ} (a : Fin m → ℤ) : ℝ → Mat (Fin 2 × Fin m) :=
  fun t => mexp ((Real.pi * t) • blkA a)

/-- Milnor's `K_A(W) = R(A, W)A = ¼[[A, W], A]` (bi-invariant metric). -/
noncomputable def KA {ι : Type} [Fintype ι] (A W : Mat ι) : Mat ι :=
  (1 / 4 : ℝ) • ((A * W - W * A) * A - A * (A * W - W * A))

/-- The multiplicity of `μ` as an eigenvalue of `K_A` on `𝔬(ι)`: the dimension of `{W ∈ 𝔬(ι) | K_A W = μ W}`. -/
noncomputable def eigMult {ι : Type} [Fintype ι] (A : Mat ι) (μ : ℝ) : ℕ :=
  Module.finrank ℝ (Submodule.span ℝ {W : Mat ι | IsSkew W ∧ KA A W = μ • W})

/-- `#{i < j : (a_i + a_j)²/4 = μ}`. -/
noncomputable def nPlus {m : ℕ} (a : Fin m → ℤ) (μ : ℝ) : ℕ :=
  ((Finset.univ : Finset (Fin m × Fin m)).filter
    (fun p => p.1 < p.2 ∧ ((a p.1 : ℝ) + a p.2) ^ 2 / 4 = μ)).card

/-- `#{i < j : a_i ≠ a_j, (a_i - a_j)²/4 = μ}`. -/
noncomputable def nMinus {m : ℕ} (a : Fin m → ℤ) (μ : ℝ) : ℕ :=
  ((Finset.univ : Finset (Fin m × Fin m)).filter
    (fun p => p.1 < p.2 ∧ a p.1 ≠ a p.2 ∧ ((a p.1 : ℝ) - a p.2) ^ 2 / 4 = μ)).card

/-- Milnor's `λ = Σ_{i<j} (a_i + a_j - 2) + Σ_{a_i > a_j} (a_i - a_j - 2)`. -/
def lamFormula {m : ℕ} (a : Fin m → ℤ) : ℤ :=
  (∑ p ∈ (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 < p.2), (a p.1 + a p.2 - 2)) +
  ∑ p ∈ (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => a p.2 < a p.1), (a p.1 - a p.2 - 2)

/-- Lemma 24.2: a non-minimal geodesic from `I` to `-I` in `O(2m)` has index `≥ 2m - 2`; for `A` with blocks
`a_j σ` (`a_1 ≥ ⋯ ≥ a_m > 0` odd) the non-zero eigenvalues of `K_A` are `(a_i ± a_j)²/4`, each twice, and the index of
`t ↦ exp(πtA)` is `Σ_{i<j} (a_i + a_j - 2) + Σ_{a_i > a_j} (a_i - a_j - 2)`. -/
def B : Prop :=
  (∀ (m : ℕ) (γ : ℝ → Mat (Fin (2 * m))), IsGeodOn (Orth (Fin (2 * m))) γ 0 1 → γ 0 = 1 → γ 1 = -1 →
    ¬ IsMinGeodIn (Orth (Fin (2 * m))) γ → ((2 * m - 2 : ℕ) : ℕ∞) ≤ idxIn (Orth (Fin (2 * m))) γ) ∧
  (∀ (m : ℕ) (a : Fin m → ℤ), (∀ j, Odd (a j) ∧ 0 < a j) → Antitone a →
    (∀ μ : ℝ, μ ≠ 0 → eigMult (blkA a) μ = 2 * nPlus a μ + 2 * nMinus a μ) ∧
    IsGeodOn (Orth (Fin 2 × Fin m)) (geoA a) 0 1 ∧ geoA a 0 = 1 ∧ geoA a 1 = -1 ∧
    idxIn (Orth (Fin 2 × Fin m)) (geoA a) = ((lamFormula a).toNat : ℕ∞))

end RoundTrip.V15_3
