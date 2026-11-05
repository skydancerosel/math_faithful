import Morse
/-! Blind formalization of V15_31 (Milnor §24, p. 146, and Theorem 24.5, p. 138: Theorem 24.5 for each `n`, `k ≢ 2 (mod 4)`). Choices:
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
- Path spaces (the subset analogue of `Om`, `OmD`, `inclD`, `piMap` of the blind files V13_1–V13_5 / V14_22; the same
  section `PathSp` is used in V15_26, V15_31, V15_32): for `N ⊆ M_n(ℝ)`, `OmIn N p q` = Milnor's `Ω(N; p, q)`,
  the piecewise smooth paths `w : [0,1] → N` from `p` to `q` (`IsPathIn`), with the topology of Milnor's metric
  `d(w, w') = max_t ρ(w(t), w'(t)) + [∫₀¹ (ds/dt − ds'/dt)² dt]^{1/2}` (§16), where `ρ = rhoIn N` is the distance of the
  induced Riemannian metric of `N` (infimum of the lengths `lenM` of piecewise smooth paths in `N`; `w(t)`, `w'(t)` lie
  in one path component of `N`) and `ds/dt = |dw/dt|` (`spd`). Deviation from V13's `Om`: the paths `ℝ → M_n(ℝ)` are
  normalized to be constant outside `[0,1]` (`w t = w (max 0 (min t 1))`), so that `d` is a metric and `Ω` is
  Hausdorff (V13's `Om` keeps paths that differ only outside `[0,1]`, which are topologically indistinguishable; the
  normalization identifies them and changes no homotopy group). "The space of minimal geodesics from `p` to `q`" is
  `MinGeodSp N p q = {w ∈ Ω(N; p, q) | IsMinGeodIn N w}` with the subspace topology of `Ω` (Milnor's `Ω^d`; it is the
  set of minimal geodesics itself rather than V13's `E⁻¹[0, d]`, which coincides with it by V13_1). Homotopy groups are
  Mathlib's `π_ i X x` (`HomotopyGroup (Fin i)`; `π_ 0` = path components, a set; groups for `i ≥ 1`), and
  `piMap f x` = the induced map `f_*` (copied verbatim from V13_1 / V14_22).
- Setting (p. 146): `k ≥ 1` with `k ≢ 2 (mod 4)` (Milnor's case at p. 146; `k = 0`, `Ω_1(n) → ΩO(n)`, is Theorem 24.3,
  V15_32, with the bound `n − 4`), `J_1, …, J_k` anticommuting complex structures on `ℝⁿ` (`IsACFam Js k`; `Ω_k(n)`
  is defined from `J_1, …, J_{k-1}`, its base point is `J_k`, and `Ω_{k+1}(n)` is defined from `J_1, …, J_k`); all
  `n` (no divisibility of `n` assumed). `ΩΩ_k(n) = Ω(Ω_k(n); J_k, −J_k) = OmIn (OmegaK Js k) (Js k) (-Js k)`.
- "The inclusion map `Ω_{k+1}(n) → ΩΩ_k(n)`" is Milnor's identification (Lemma 24.4, p. 138) of `J ∈ Ω_{k+1}(n)`
  with the minimal geodesic `t ↦ J_k exp(πtA)`, `A = J_k⁻¹J`, from `J_k` to `−J_k` (with midpoint `J`), followed by the
  inclusion into `Ω`: B asserts a continuous `j : Ω_{k+1}(n) → Ω(Ω_k(n); J_k, −J_k)` with
  `(j J)(t) = J_k exp(πt J_k⁻¹J)` for `t ∈ [0,1]` (unique, by the normalization of paths).
- "Isomorphisms of homotopy groups in dimensions `≤ n/m_{k+1} − 3`": for `i ≥ 0` with `i ≤ n/m_{k+1} − 3` (rational
  division, written `(i + 3) · m_{k+1} ≤ n`, which is the same as `i + 3 ≤ ⌊n/m_{k+1}⌋`) and every base point
  `J ∈ Ω_{k+1}(n)`, `j_* : π_i(Ω_{k+1}(n), J) → π_i(ΩΩ_k(n), j J)` is bijective, and a group isomorphism for `i ≥ 1`.
- The parenthetical "Theorem 24.5: `π_hO ≅ π_{h−1}Ω_1 ≅ ⋯ ≅ π_1Ω_{h−1}`" concerns the direct limits `O`, `Ω_k`
  (`n → ∞`; see V15_41/V15_43) and is quoted as the purpose of the claim; it is not part of this finite-`n` B.
- Milnor's `m_k` (p. 143, V15_13: the dimension of a minimal `(J_1, …, J_k)`-space) is `mK k`, defined by Milnor's
  table `m_0, …, m_8 = 1, 2, 4, 4, 8, 8, 8, 8, 16` and `m_k = 16 m_{k-8}` (`k > 8`), not as a dimension (that the
  minimal spaces have this dimension is Lemma 24.8 / V15_16, not re-asserted).
-/
namespace RoundTrip.V15_31

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

/-- Theorem 24.5 for each `n`, `k ≢ 2 (mod 4)` (p. 146): the inclusion `Ω_{k+1}(n) → ΩΩ_k(n)`,
`J ↦ (t ↦ J_k exp(πt J_k⁻¹J))`, induces isomorphisms of homotopy groups in dimensions `≤ n/m_{k+1} − 3`. -/
def B : Prop :=
  ∀ (n k : ℕ) (Js : ℕ → Mat (Fin n)), 1 ≤ k → k % 4 ≠ 2 → IsACFam Js k →
    ∃ j : C(↥(OmegaK Js (k + 1)), OmIn (OmegaK Js k) (Js k) (-Js k)),
      (∀ (J : ↥(OmegaK Js (k + 1))) (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 →
        (j J).1 t = Js k * mexp ((Real.pi * t) • ((Js k)⁻¹ * (J : Mat (Fin n))))) ∧
      ∀ J : ↥(OmegaK Js (k + 1)),
        (∀ i : ℕ, (i + 3) * mK (k + 1) ≤ n → Function.Bijective (piMap (N := Fin i) j J)) ∧
        (∀ i : ℕ, (i + 1 + 3) * mK (k + 1) ≤ n →
          ∃ e : π_ (i + 1) ↥(OmegaK Js (k + 1)) J ≃* π_ (i + 1) (OmIn (OmegaK Js k) (Js k) (-Js k)) (j J),
            ⇑e = piMap j J)

end RoundTrip.V15_31
