import Morse
/-! Blind formalization of V15_18 (Milnor §24, Remark, pp. 143–144). Choices:
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
- (Prelude and the two bullets above copied verbatim from V15_1–V15_11.) A `(J_1, …, J_k)`-space is `ℝⁿ`
  (`Fin n → ℝ`, any Euclidean space being isometric to one) with anticommuting complex structures `J_1, …, J_k`
  (`IsACFam Js k`: orthogonal, `J_α² = -I`, `J_αJ_β = -J_βJ_α`). `IsMinimalSp` is copied from V15_10 (no subspace
  other than `0` and the whole space is closed under `J_1, …, J_k`); a minimal space (`IsMinACSp`) is moreover
  non-zero (`n ≥ 1`): read literally, "no proper, non-trivial subspace" would make `0` minimal, which `m_0 = 1`
  excludes. `k = 0` is allowed (no structures: a minimal space is a line).
- `m_k` as in V15_13 (`mk k = sInf` of the dimensions of the minimal spaces). The sphere `S^{n-1}` is the set of unit
  vectors of `ℝⁿ` (dot product); "`k` linearly independent vector fields on `S^{n-1}`" (`HasIndepFields n k`):
  `k` continuous maps `v_i : S^{n-1} → ℝⁿ` with `v_i(u) ⊥ u` (tangent) and `v_1(u), …, v_k(u)` linearly independent
  at every `u` (continuous, the usual notion of the vector-field problem; Milnor's fields `u ↦ J_αu` are restrictions
  of linear maps, hence smooth).
- Claims (conjunction): (1) for anticommuting complex structures `J_1, …, J_k` on `ℝⁿ` (any `n`, `k`; Milnor's
  `n = rm_k` is automatic, V15_14) and every unit vector `u`, the vectors `J_1u, …, J_ku` are perpendicular to `u` and
  to each other, and are linearly independent; (2) for every `r ≥ 0` (`r = 0`: the empty sphere, vacuous) and
  `k ≥ 0`, `S^{rm_k - 1}` has `k` linearly independent vector fields (this includes that `ℝ^{rm_k}` carries
  `J_1, …, J_k`); (3) the special cases: `3` on `S^{4r-1}`, `7` on `S^{8r-1}`, `8` on `S^{16r-1}`.
- Not formalized: the attributions (Hurwitz and Radon), and "Adams: best possible", which is a cited theorem of
  Adams (the number of fields cannot be increased), not something Milnor claims to prove; including it would make B
  Adams' vector-field theorem.
-/
namespace RoundTrip.V15_18

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

section MinSp
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Milnor's minimal `(J_1, …, J_m)`-space (p. 143): no subspace of `ℝ^ι` other than `0` and `ℝ^ι` is closed under
`J_1, …, J_m` (as in V15_10). -/
def IsMinimalSp (Js : ℕ → Mat ι) (m : ℕ) : Prop :=
  ∀ W : Submodule ℝ (ι → ℝ), (∀ α, 1 ≤ α → α ≤ m → ∀ v ∈ W, Js α *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤

/-- `ℝ^ι`, with the anticommuting complex structures `J_1, …, J_m` (`IsACFam`), is a minimal `(J_1, …, J_m)`-space:
`ℝ^ι ≠ 0` and no proper non-trivial subspace is closed under `J_1, …, J_m`. -/
def IsMinACSp (Js : ℕ → Mat ι) (m : ℕ) : Prop := Nonempty ι ∧ IsACFam Js m ∧ IsMinimalSp Js m
end MinSp

/-- Milnor's `m_k` (p. 143): the dimension of a minimal `(J_1, …, J_k)`-space (`sInf` of the dimensions of the minimal
spaces `ℝⁿ`; all of them have the same dimension). -/
noncomputable def mk (k : ℕ) : ℕ := sInf {n : ℕ | ∃ Js : ℕ → Mat (Fin n), IsMinACSp Js k}

/-- The unit sphere `S^{n-1} ⊆ ℝⁿ`. -/
def sph (n : ℕ) : Set (Fin n → ℝ) := {u | u ⬝ᵥ u = 1}

/-- `S^{n-1}` carries `k` continuous tangent vector fields which are linearly independent at every point. -/
def HasIndepFields (n k : ℕ) : Prop :=
  ∃ v : Fin k → (Fin n → ℝ) → (Fin n → ℝ), (∀ i, ContinuousOn (v i) (sph n)) ∧
    ∀ u ∈ sph n, (∀ i, v i u ⬝ᵥ u = 0) ∧ LinearIndependent ℝ (fun i => v i u)

/-- For anticommuting `J_1, …, J_k` and a unit vector `u`, `J_1u, …, J_ku` are perpendicular to each other and to `u`;
hence `k` linearly independent vector fields on `S^{rm_k - 1}`: `3` on `S^{4r-1}`, `7` on `S^{8r-1}`, `8` on
`S^{16r-1}`. -/
def B : Prop :=
  (∀ (n k : ℕ) (Js : ℕ → Mat (Fin n)), IsACFam Js k → ∀ u ∈ sph n,
    (∀ α, 1 ≤ α → α ≤ k → (Js α *ᵥ u) ⬝ᵥ u = 0) ∧
    (∀ α β, 1 ≤ α → α ≤ k → 1 ≤ β → β ≤ k → α ≠ β → (Js α *ᵥ u) ⬝ᵥ (Js β *ᵥ u) = 0) ∧
    LinearIndependent ℝ (fun i : Fin k => Js (i.val + 1) *ᵥ u)) ∧
  (∀ r k : ℕ, HasIndepFields (r * mk k) k) ∧
  (∀ r : ℕ, HasIndepFields (4 * r) 3 ∧ HasIndepFields (8 * r) 7 ∧ HasIndepFields (16 * r) 8)

end RoundTrip.V15_18
