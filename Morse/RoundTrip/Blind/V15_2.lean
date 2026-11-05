import Morse
/-! Blind formalization of V15_2 (Milnor §24, proof of Lemma 24.1, pp. 134–135: `exp(θJ) = cos θ I + sin θ J`).
Choices:
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
- Claim 1 ("in a suitable basis `exp(πA)` is block diagonal with rotation blocks"): for every skew `A` on `ℝ^{2m}`
  (`m ≥ 0`; Milnor works in `O(2m)` here, odd `n` would need an extra zero block and is not stated) there is an
  orthonormal basis, i.e. an orthogonal `P`, in which `A` is block diagonal with blocks `a_j σ`, `σ = (0 1; -1 0)`,
  `a_j ∈ ℝ` (any sign, `0` allowed), and in which `exp(πA)` is block diagonal with the rotation blocks
  `(cos πa_j, sin πa_j; -sin πa_j, cos πa_j)` (`= exp(πa_j σ)`). Here `ℝ^{2m}` is realized as `ℝ^{Fin 2 × Fin m}`
  (Mathlib's `Matrix.blockDiagonal`: block `j` acts on `e_(0,j), e_(1,j)`); any relabeling of coordinates is an
  orthogonal change of basis, so this is the claim for `ℝ^{2m}` with any ordering of the basis.
- Claim 2 (title; "for a complex structure `J`, `exp πJ = -I`"): for every complex structure `J` on `ℝⁿ` (any `n`; for
  odd `n` there are none) and every `θ ∈ ℝ`, `exp(θJ) = cos θ · I + sin θ · J`, and in particular `exp(πJ) = -I`
  (stated as a separate conjunct).
-/
namespace RoundTrip.V15_2

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

/-- The rotation block `(cos θ, sin θ; -sin θ, cos θ) = exp(θσ)`. -/
noncomputable def rot2 (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]

/-- The block-diagonal matrix on `ℝ^{2m} = ℝ^{Fin 2 × Fin m}` with `2 × 2` blocks `b j` (block `j` on
`e_(0,j), e_(1,j)`). -/
def blk {m : ℕ} (b : Fin m → Matrix (Fin 2) (Fin 2) ℝ) : Mat (Fin 2 × Fin m) := Matrix.blockDiagonal b

/-- Normal form: a skew `A` on `ℝ^{2m}` has, in a suitable orthonormal basis, blocks `a_j σ`, and `exp(πA)` the
rotation blocks by `πa_j`; for a complex structure `J`, `exp(θJ) = cos θ I + sin θ J` and `exp(πJ) = -I`. -/
def B : Prop :=
  (∀ (m : ℕ) (A : Mat (Fin 2 × Fin m)), IsSkew A →
    ∃ P ∈ Orth (Fin 2 × Fin m), ∃ a : Fin m → ℝ,
      Pᵀ * A * P = blk (fun j => a j • sig2) ∧
      Pᵀ * mexp (Real.pi • A) * P = blk (fun j => rot2 (Real.pi * a j))) ∧
  (∀ (n : ℕ) (J : Mat (Fin n)), IsCplxStr J →
    (∀ θ : ℝ, mexp (θ • J) = Real.cos θ • (1 : Mat (Fin n)) + Real.sin θ • J) ∧
    mexp (Real.pi • J) = -1)

end RoundTrip.V15_2
