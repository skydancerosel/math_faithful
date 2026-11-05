import Morse
/-! Blind formalization of V15_39 (Milnor §24, p. 148: Theorem 24.5 for each `n`, `k = 2, 6`). Choices:
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
- Path spaces: section `PathSp` copied verbatim from the blind files V15_31/V15_32 (also V15_26): `OmIn N p q` =
  Milnor's `Ω(N; p, q)`, the piecewise smooth paths `[0,1] → N` from `p` to `q` (normalized to be constant outside
  `[0,1]`), with the topology of Milnor's metric `d` (`ρ` = induced distance of `N`); `ΩΩ_k(n) = Ω(Ω_k(n); J, -J)` is
  `OmIn (Ω_k(n)) J (-J)`. Milnor's inclusion `Ω_{k+1}(n) → ΩΩ_k(n)` is, as in V15_31, `J' ↦ (t ↦ J exp(πt J⁻¹J'))` (the
  minimal geodesic from `J` to `-J` with midpoint `J'`). `m_k = mK k` (Milnor's table, copied from V15_31).
- Milnor's `i` and `det_ℂ`: section `CDet` copied verbatim from the blind file V15_34: `iProd Js (k - 1) = J_1⋯J_{k-1}`;
  for real `U` commuting with `i`, `det_ℂ U = cdet i U = det(UQ + I - Q)` and `trace_ℂ U = ctr i U = tr(UQ)`, with
  `Q = ½(I - √-1·i)` the projection onto the `√-1`-eigenspace of `i` (which is `(ℝⁿ, i)` as a complex vector space);
  `f(J') = fJ i J J' = det_ℂ(J⁻¹J')`. Section `Classes` (new; shared by V15_35 and V15_39): `Ω^{(c)} = OmC Js k J c`,
  the paths `w ∈ ΩΩ_k(n)` along which `f ∘ w` (a path in `S¹` from `f(J) = 1`) turns through the angle `π c m_k / 2`
  (`InClass`, via the continuous angle function `θ`, `θ 0 = 0`); this is the normalization for which Milnor's
  `trace A = icm_k/2` holds on the geodesic `J exp(πtA)` (`f(J exp(πtA)) = e^{πt trace_ℂ A}`, V15_34).
- Homotopy groups as in the blind files V13_1–V13_5 / V15_31: Mathlib's `π_ i X x` (`HomotopyGroup (Fin i)`; `π_ 0` =
  the set of path components), `piMap f x` = the induced map `f_*` (section `Htpy` copied verbatim).
- Setting as in V15_31 (Theorem 24.5 for `k ≢ 2 mod 4`): anticommuting complex structures `J_1, …, J_k` on `ℝⁿ`
  (`IsACFam Js k`; `J_1, …, J_{k-1}` define `Ω_k(n)`, `J_k` is the base point, Milnor's `J`), any `n`, any such choice.
- `k = 2` or `k = 6` (title). "The component of `ΩΩ_k(n)`" is a class `Ω^{(c)}` (`OmC Js k J_k c`, V15_35), `c ∈ ℤ`;
  "the corresponding component of `Ω_{k+1}(n)`" is the part of `Ω_{k+1}(n)` which Milnor's inclusion
  `J' ↦ (t ↦ J_k exp(πt J_k⁻¹J'))` carries into `Ω^{(c)}` (`SC Js k c`, subspace topology). "Approximated up to higher and
  higher dimensions, as `n → ∞`": for every `c` and every dimension `d` there is `N` such that for every `n ≥ N` and
  every choice of `J_1, …, J_k` on `ℝⁿ`, the inclusion `SC → Ω^{(c)}` (a continuous map given by its values on `[0,1]`,
  `∃ g`; it is unique) induces bijections `π_i(SC, x) → π_i(Ω^{(c)}, g x)` for all `0 ≤ i ≤ d` and all base points `x`
  (group isomorphisms for `i ≥ 1`, `piMap` being a homomorphism), and every path component of `Ω^{(c)}` meets the image
  (so the components correspond also when `SC` has no base point: then `Ω^{(c)}` is empty). For fixed `c` this says that the dimension up to which the
  inclusion is a homotopy equivalence tends to infinity with `n`; the explicit bound (from V15_38 and Theorem 22.1)
  belongs to the proof.
-/
namespace RoundTrip.V15_39

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

section Htpy
/-- `f ∘ γ` for a generalized loop `γ : (I^N, ∂I^N) → (X, x)`. -/
def genLoopMap {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) {x : X}
    (γ : ↥(GenLoop N X x)) : ↥(GenLoop N Y (f x)) :=
  ⟨f.comp γ.1, fun y hy => by simp [GenLoop.boundary γ y hy]⟩

/-- The homomorphism `f_* : π_N(X, x) → π_N(Y, f x)` induced by a map `f` (Mathlib's `HomotopyGroup`). -/
def piMap {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (x : X) :
    HomotopyGroup N X x → HomotopyGroup N Y (f x) :=
  Quotient.map' (genLoopMap f) (fun _ _ h => ContinuousMap.HomotopicRel.comp_continuousMap h f)
end Htpy

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

/-- Milnor's `m_k` (p. 143): `m_0, …, m_8 = 1, 2, 4, 4, 8, 8, 8, 8, 16` and `m_k = 16 m_{k-8}` for `k > 8`. -/
def mK : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 4
  | 4 => 8
  | 5 => 8
  | 6 => 8
  | 7 => 8
  | k + 8 => 16 * mK k

section CDet
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `J_1J_2⋯J_m` (left-associated; `I` for `m = 0`). -/
def iProd (Js : ℕ → Mat ι) : ℕ → Mat ι
  | 0 => 1
  | m + 1 => iProd Js m * Js (m + 1)

/-- A real matrix as a complex matrix. -/
def cplx (X : Mat ι) : Matrix ι ι ℂ := X.map (fun x : ℝ => (x : ℂ))

/-- `Q = ½(I − √−1·i)`: the projection of `ℂ^ι` onto the `+√−1`-eigenspace of the complex structure `i`. -/
noncomputable def projQ (i : Mat ι) : Matrix ι ι ℂ := (1 / 2 : ℂ) • (1 - Complex.I • cplx i)

/-- The complex determinant of `U` (commuting with `i`) on `(ℝ^ι, i)`: `det(UQ + I − Q)`. -/
noncomputable def cdet (i U : Mat ι) : ℂ := Matrix.det (cplx U * projQ i + (1 - projQ i))

/-- The complex trace of `U` (commuting with `i`) on `(ℝ^ι, i)`: `tr(UQ)`. -/
noncomputable def ctr (i U : Mat ι) : ℂ := Matrix.trace (cplx U * projQ i)

/-- Milnor's `f(J') = det_ℂ(J⁻¹J')` (base point `J`). -/
noncomputable def fJ (i J J' : Mat ι) : ℂ := cdet i (J⁻¹ * J')
end CDet

section Classes
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The path `w : [0, 1] → Ω_k(n)` from `J` lies in Milnor's class `Ω^{(c)}`: the path `f ∘ w` in `S¹` (from
`f(J) = 1`, `f = fJ i J`) turns through the total angle `π c m_k / 2`, i.e. its angle function `θ` (continuous,
`θ 0 = 0`, `f(w t) = e^{iθ(t)}`; unique) ends at `θ 1 = π c m_k / 2` (`m = m_k`). For the geodesic `J exp(πtA)` this
is `trace_ℂ A = i c m_k / 2`, since `f(J exp(πtA)) = e^{πt trace_ℂ A}`. -/
def InClass (i J : Mat ι) (m : ℕ) (c : ℤ) (w : unitInterval → Mat ι) : Prop :=
  ∃ θ : unitInterval → ℝ, Continuous θ ∧ θ 0 = 0 ∧ θ 1 = Real.pi * c * m / 2 ∧
    ∀ t, fJ i J (w t) = Complex.exp ((θ t : ℂ) * Complex.I)

/-- Milnor's class `Ω^{(c)} ⊆ ΩΩ_k(n) = Ω(Ω_k(n); J, -J)` (`i = J_1⋯J_{k-1}`, base point `J ∈ Ω_k(n)`). -/
def OmC (Js : ℕ → Mat ι) (k : ℕ) (J : Mat ι) (c : ℤ) : Set (OmIn (OmegaK Js k) J (-J)) :=
  {w | InClass (iProd Js (k - 1)) J (mK k) c (fun t => w.1 t)}
end Classes

/-- The part of `Ω_{k+1}(n)` corresponding to `Ω^{(c)}`: the `J' ∈ Ω_{k+1}(n)` whose minimal geodesic
`t ↦ J_k exp(πt J_k⁻¹J')` lies in `Ω^{(c)}`. -/
def SC {n : ℕ} (Js : ℕ → Mat (Fin n)) (k : ℕ) (c : ℤ) : Set (Mat (Fin n)) :=
  {X | X ∈ OmegaK Js (k + 1) ∧
    InClass (iProd Js (k - 1)) (Js k) (mK k) c (fun t => Js k * mexp ((Real.pi * (t : ℝ)) • ((Js k)⁻¹ * X)))}

/-- Theorem 24.5 for `k = 2, 6`, for each `n`: the component `Ω^{(c)}` of `ΩΩ_k(n)` is approximated, up to dimensions
tending to infinity with `n`, by the corresponding component of `Ω_{k+1}(n)`. -/
def B : Prop :=
  ∀ k : ℕ, (k = 2 ∨ k = 6) → ∀ (c : ℤ) (d : ℕ), ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ Js : ℕ → Mat (Fin n), IsACFam Js k →
      ∃ g : C(↥(SC Js k c), ↥(OmC Js k (Js k) c)),
        (∀ (x : ↥(SC Js k c)) (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 →
          (g x).1.1 t = Js k * mexp ((Real.pi * t) • ((Js k)⁻¹ * (x : Mat (Fin n))))) ∧
        (∀ i : ℕ, i ≤ d → ∀ x : ↥(SC Js k c), Function.Bijective (piMap (N := Fin i) g x)) ∧
        ∀ w : ↥(OmC Js k (Js k) c), ∃ x : ↥(SC Js k c), Joined w (g x)

end RoundTrip.V15_39
