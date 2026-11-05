import Morse
/-! Blind formalization of V15_40 (Milnor §24, pp. 146, 148: Theorem 24.5 for `k = 2, 6`: path components and the
direct limit). Choices:
- Setting as in the blind files V15_1–V15_11 (§24 prelude `Prelude` copied verbatim from V15_1; shared by the other §24
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
- Path spaces: section `PathSp` copied verbatim from the blind files V15_31/V15_32 (`OmIn N p q` = Milnor's
  `Ω(N; p, q)`, piecewise smooth paths normalized to be constant outside `[0,1]`, topology of Milnor's metric `d`);
  `ΩΩ_k(n) = OmIn (Ω_k(n)) J_k (-J_k)`. Milnor's inclusion `Ω_{k+1}(n) → ΩΩ_k(n)` is, as in V15_31,
  `J' ↦ (t ↦ J_k exp(πt J_k⁻¹J'))`.
- Section `Stab` (new; shared verbatim by the blind files V15_40 and V15_41): `ℝ^{16r} = ℝ^{Fin 16 × Fin r}` (`r`
  summands `ℝ¹⁶`), Milnor's `J_α = J'_α ⊕ ⋯ ⊕ J'_α` (`bJ`, block diagonal) for given anticommuting complex structures
  `J'_1, …, J'_8` on `ℝ¹⁶` (`IsACFam Js' 8`, arbitrary; Milnor fixes one such family), base points `bpt` (`J_k`, and
  `J_0 = I` for `Ω_0 = O`), the stabilization `stab F X = X ⊕ F` (`ℝ^{16r} ⊕ ℝ¹⁶ = ℝ^{16(r+1)}`, new summand last).
  Direct limits (`DLim`): a sequence of spaces mapped compatibly into a common set (here infinite matrices `InfMat`
  indexed by `Fin 16 × ℕ`, `X ↦ X ⊕ F ⊕ F ⊕ ⋯`, `extM`), as the union of the images with the final topology of the
  stage maps (Milnor's direct limit topology). `Ω_k = LimOm Js' k = lim_r Ω_k(16r)` along `J ↦ J ⊕ J'_k` (Milnor's
  imbedding, `J ↦ J ⊕ I` for `k = 0`).
- Milnor's `ΩΩ_k` in the limit: `J ↦ J ⊕ J'_k` carries `J_k` to `J_k` but `-J_k` to `-J_k ⊕ J'_k ≠ -(J_k ⊕ J'_k)`, so
  `Ω(Ω_k; J_k, -J_k)` has no literal meaning for the direct limit `Ω_k` (the end point `-J_k` is not compatible with the
  stabilizations). I read Milnor's "the inclusions `Ω_{k+1}(n) → ΩΩ_k(n)` give rise, in the limit, to inclusions
  `Ω_{k+1} → ΩΩ_k`" with `ΩΩ_k := lim_r ΩΩ_k(16r)` (`LimPath Js' k`; `ΩΩ_k(16r) = PSt Js' k r`, Milnor's path space
  `OmIn` of V15_31), the bonding maps being `w ↦ w ⊕ ψ` with `ψ(t) = J'_k exp(πt J'_k⁻¹J'_{k+1})` (`psiP`), the minimal
  geodesic from `J'_k` to `-J'_k` through `J'_{k+1}` in `Ω_k(16)`, i.e. the image of `J'_{k+1}` under Milnor's inclusion
  at `n = 16`; these are exactly the maps making the squares with `Ω_{k+1}(16r) → Ω_{k+1}(16(r+1))`
  (`J' ↦ J' ⊕ J'_{k+1}`) commute. Elements of the limit are compared on `[0, 1]` (`extP`), where paths live.
- `k = 2` or `k = 6` (title). "Components" are path components (`ZerothHomotopy`; the spaces involved are locally path
  connected, so these are the components).
- Claim 1 (each `n`): for anticommuting complex structures `J_1, …, J_k` on `ℝⁿ` (`IsACFam Js k`, as in V15_31; base
  point `J_k`) with `n > 0` (for `n = 0` every space is a point), `ΩΩ_k(n) = Ω(Ω_k(n); J_k, -J_k)` has infinitely many
  path components, while `Ω_{k+1}(n)` has finitely many.
- Claim 2 ("passing to the direct limit, one obtains a homotopy equivalence on each component"), for the limits over
  `n = 16r` of the section `Stab`: the limit `Φ : Ω_{k+1} → ΩΩ_k` of Milnor's inclusions (continuous, equal at every
  stage to the inclusion followed by the stage map) restricts, on each path component `C` of `Ω_{k+1}`, to a homotopy
  equivalence of `C` onto the path component of `ΩΩ_k` containing `Φ(C)` (`ContinuousMap.HomotopyEquiv` whose
  underlying map is `Φ`); and the components correspond (every component of `ΩΩ_k` contains some `Φ(y)`, and `Φ`
  separates components), which is implicit in "on each component".
-/
namespace RoundTrip.V15_40

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

section PathSp
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `ρ_N(x, y)`: the distance of the induced Riemannian metric of `N`, the greatest lower bound of the lengths of
piecewise smooth paths in `N` from `x` to `y` (Milnor §16; parametrized by `[0, 1]`, which is no restriction). -/
noncomputable def rhoIn (N : Set (Mat ι)) (x y : Mat ι) : ℝ :=
  sInf {L | ∃ w, IsPathIn N w ∧ w 0 = x ∧ w 1 = y ∧ lenM w = L}

/-- `ds/dt = |dw/dt|`, the speed of `w`. -/
noncomputable def spd (w : ℝ → Mat ι) (t : ℝ) : ℝ := Real.sqrt (frob (deriv w t) (deriv w t))

/-- Milnor's metric on the path space (§16): `d(w, w') = max_t ρ(w t, w' t) + [∫₀¹ (ds/dt − ds'/dt)² dt]^{1/2}`. -/
noncomputable def dOmIn (N : Set (Mat ι)) (w w' : ℝ → Mat ι) : ℝ :=
  (⨆ t : Set.Icc (0 : ℝ) 1, rhoIn N (w t) (w' t)) +
    Real.sqrt (∫ t in (0 : ℝ)..1, (spd w t - spd w' t) ^ 2)

/-- `Ω(N; p, q)`: piecewise smooth paths `[0, 1] → N` from `p` to `q`, normalized to be constant outside `[0, 1]`. -/
def OmIn (N : Set (Mat ι)) (p q : Mat ι) : Type :=
  {w : ℝ → Mat ι // IsPathIn N w ∧ w 0 = p ∧ w 1 = q ∧ ∀ t, w t = w (max 0 (min t 1))}

/-- Milnor's topology on `Ω(N; p, q)`: the topology of the metric `d` (generated by the open `d`-balls). -/
instance omInTopology (N : Set (Mat ι)) (p q : Mat ι) : TopologicalSpace (OmIn N p q) :=
  TopologicalSpace.generateFrom {S | ∃ (w : OmIn N p q) (ε : ℝ), S = {w' | dOmIn N w.1 w'.1 < ε}}

/-- The space of minimal geodesics from `p` to `q` in `N`, a subspace of `Ω(N; p, q)`. -/
def MinGeodSp (N : Set (Mat ι)) (p q : Mat ι) : Set (OmIn N p q) := {w | IsMinGeodIn N w.1}
end PathSp

section Stab

/-- Milnor's structures on `ℝ^{16r} = ℝ¹⁶ ⊕ ⋯ ⊕ ℝ¹⁶` (index type `Fin 16 × Fin r`, the `j`-th summand on the
coordinates `(·, j)`): `J_α = J'_α ⊕ ⋯ ⊕ J'_α` (`r` copies) for given structures `J'_α` on `ℝ¹⁶`. -/
def bJ (Js' : ℕ → Mat (Fin 16)) (r α : ℕ) : Mat (Fin 16 × Fin r) := Matrix.blockDiagonal fun _ => Js' α

/-- The base point `J_k` of `Ω_k(n)`, with `J_0 = I` for `Ω_0(n) = O(n)`. -/
def bpt {ι : Type} [Fintype ι] [DecidableEq ι] (Js : ℕ → Mat ι) (k : ℕ) : Mat ι := if k = 0 then 1 else Js k

/-- `X ⊕ F` on `ℝ^{16r} ⊕ ℝ¹⁶ = ℝ^{16(r+1)}` (the added summand is the last one). -/
def stab {r : ℕ} (F : Mat (Fin 16)) (X : Mat (Fin 16 × Fin r)) : Mat (Fin 16 × Fin (r + 1)) :=
  Matrix.of fun x y =>
    if hx : (x.2 : ℕ) < r then (if hy : (y.2 : ℕ) < r then X (x.1, ⟨x.2, hx⟩) (y.1, ⟨y.2, hy⟩) else 0)
    else (if (y.2 : ℕ) < r then 0 else F x.1 y.1)

/-- Matrices on `ℝ^{16∞} = ℝ¹⁶ ⊕ ℝ¹⁶ ⊕ ⋯` (index type `Fin 16 × ℕ`). -/
abbrev InfMat : Type := Matrix (Fin 16 × ℕ) (Fin 16 × ℕ) ℝ

/-- `X ⊕ F ⊕ F ⊕ ⋯`: the common image of `X ∈ M_{16r}(ℝ)` and of all its stabilizations `X ⊕ F ⊕ ⋯ ⊕ F`. -/
def extM (F : Mat (Fin 16)) (r : ℕ) (X : Mat (Fin 16 × Fin r)) : InfMat :=
  Matrix.of fun x y =>
    if hx : x.2 < r then (if hy : y.2 < r then X (x.1, ⟨x.2, hx⟩) (y.1, ⟨y.2, hy⟩) else 0)
    else (if y.2 = x.2 then F x.1 y.1 else 0)

/-- The direct limit of a sequence of spaces `X r` mapped (compatibly with the bonding maps, injectively) into a set
`A` by `e r`: the union of the images, with the direct-limit (final) topology of the maps `X r → lim`. -/
structure DLim {A : Type} (X : ℕ → Type) (e : ∀ r, X r → A) : Type where
  /-- The point of `A`. -/
  val : A
  /-- It comes from some stage. -/
  mem : ∃ r x, e r x = val

/-- The map from stage `r` to the direct limit. -/
def DLim.incl {A : Type} {X : ℕ → Type} (e : ∀ r, X r → A) (r : ℕ) (x : X r) : DLim X e := ⟨e r x, r, x, rfl⟩

/-- The direct-limit topology: the finest topology making every `X r → lim` continuous. -/
instance {A : Type} {X : ℕ → Type} [∀ r, TopologicalSpace (X r)] (e : ∀ r, X r → A) :
    TopologicalSpace (DLim X e) :=
  ⨆ r, TopologicalSpace.coinduced (DLim.incl e r) inferInstance

/-- Stage `r` of `Ω_k = lim Ω_k(16r)` (along `J ↦ J ⊕ J'_k`, `J'_0 = I`): `X ↦ X ⊕ J'_k ⊕ J'_k ⊕ ⋯`. -/
def eOm (Js' : ℕ → Mat (Fin 16)) (k r : ℕ) (X : ↥(OmegaK (bJ Js' r) k)) : InfMat := extM (bpt Js' k) r X.1

/-- Milnor's `Ω_k = lim_r Ω_k(16r)` (direct limit topology). -/
abbrev LimOm (Js' : ℕ → Mat (Fin 16)) (k : ℕ) : Type := DLim (fun r => ↥(OmegaK (bJ Js' r) k)) (eOm Js' k)

/-- `ΩΩ_k(16r) = Ω(Ω_k(16r); J_k, -J_k)` (Milnor's path space `OmIn`). -/
abbrev PSt (Js' : ℕ → Mat (Fin 16)) (k r : ℕ) : Type :=
  OmIn (OmegaK (bJ Js' r) k) (bpt (bJ Js' r) k) (-bpt (bJ Js' r) k)

/-- `ψ(t) = J'_k exp(πt J'_k⁻¹J'_{k+1})`: the minimal geodesic from `J'_k` to `-J'_k` in `Ω_k(16)` with midpoint
`J'_{k+1}` (`J'_0 = I`), i.e. the image of `J'_{k+1}` under Milnor's inclusion `Ω_{k+1}(16) → ΩΩ_k(16)`. -/
noncomputable def psiP (Js' : ℕ → Mat (Fin 16)) (k : ℕ) (t : ℝ) : Mat (Fin 16) :=
  bpt Js' k * mexp ((Real.pi * t) • ((bpt Js' k)⁻¹ * Js' (k + 1)))

/-- A path in `M_{16r}(ℝ)` stabilized: `t ↦ w(t) ⊕ ψ(t) ⊕ ψ(t) ⊕ ⋯` on `[0, 1]`. The bonding map
`ΩΩ_k(16r) → ΩΩ_k(16(r+1))` is `w ↦ w ⊕ ψ` (which carries the end points `±J_k` to `±J_k`). -/
noncomputable def extP (Js' : ℕ → Mat (Fin 16)) (k r : ℕ) (w : ℝ → Mat (Fin 16 × Fin r)) :
    unitInterval → InfMat :=
  fun t => extM (psiP Js' k t) r (w t)

/-- Stage `r` of the limit of the path spaces `ΩΩ_k(16r)`. -/
noncomputable def eP (Js' : ℕ → Mat (Fin 16)) (k r : ℕ) (w : PSt Js' k r) : unitInterval → InfMat := extP Js' k r w.1

/-- Milnor's `ΩΩ_k` in the limit: `lim_r ΩΩ_k(16r)` along `w ↦ w ⊕ ψ` (direct limit topology). -/
abbrev LimPath (Js' : ℕ → Mat (Fin 16)) (k : ℕ) : Type := DLim (fun r => PSt Js' k r) (eP Js' k)
end Stab

/-- For `k = 2, 6`: `ΩΩ_k(n)` has infinitely many components, `Ω_{k+1}(n)` finitely many; in the direct limit the
inclusion `Ω_{k+1} → ΩΩ_k` is a homotopy equivalence on each component. -/
def B : Prop :=
  (∀ (n k : ℕ) (Js : ℕ → Mat (Fin n)), (k = 2 ∨ k = 6) → IsACFam Js k → 0 < n →
    Infinite (ZerothHomotopy (OmIn (OmegaK Js k) (Js k) (-Js k))) ∧
    Finite (ZerothHomotopy ↥(OmegaK Js (k + 1)))) ∧
  ∀ (k : ℕ) (Js' : ℕ → Mat (Fin 16)), (k = 2 ∨ k = 6) → IsACFam Js' 8 →
    ∃ Φ : C(LimOm Js' (k + 1), LimPath Js' k),
      (∀ (r : ℕ) (x : ↥(OmegaK (bJ Js' r) (k + 1))),
        (Φ (DLim.incl (eOm Js' (k + 1)) r x)).val =
          extP Js' k r (fun t => bpt (bJ Js' r) k * mexp ((Real.pi * t) • ((bpt (bJ Js' r) k)⁻¹ * x.1)))) ∧
      (∀ w : LimPath Js' k, ∃ y : LimOm Js' (k + 1), Joined w (Φ y)) ∧
      (∀ y y' : LimOm Js' (k + 1), Joined (Φ y) (Φ y') → Joined y y') ∧
      ∀ y : LimOm Js' (k + 1),
        ∃ h : ContinuousMap.HomotopyEquiv ↥(pathComponent y) ↥(pathComponent (Φ y)),
          ∀ z : ↥(pathComponent y), (h.toFun z : LimPath Js' k) = Φ z

end RoundTrip.V15_40
