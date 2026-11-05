import Morse
/-! Blind formalization of V15_16 (Milnor §24, p. 143). Choices:
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
- Claim 1 (title, "minimal spaces have dimension `m_k`"), for `k = 0, …, 8`: every minimal `(J_1, …, J_k)`-space `ℝⁿ`
  has `n = m_k`, with Milnor's values `m_0, …, m_8 = 1, 2, 4, 4, 8, 8, 8, 8, 16` (`mTab`, written out, so that the
  claim does not depend on how `m_k` is defined). Existence of minimal spaces is not asserted here (V15_13).
- The description ("a line over `ℝ, ℂ, ℍ`" for `k = 0, 1, 2`) is the dimension `1, 2, 4` (a `J_1`-space of dimension
  2 is a complex line, a `(J_1, J_2)`-space of dimension 4 a quaternionic line). The further descriptions are read as:
  `k = 3`: `J_3 = J_1J_2` or `J_3 = -J_1J_2` on the whole (minimal) space; `k = 4, 5, 6`: `H ⊕ H'` with `H` the
  quaternionic line on which `J_3 = J_1J_2` and `H'` the one on which `J_3 = -J_1J_2`, i.e.
  `ℝ⁸ = ker(J_3 - J_1J_2) ⊕ ker(J_3 + J_1J_2)`, both 4-dimensional and closed under `J_1, J_2`; `k = 7`:
  `J_7 = ±J_1J_2J_3J_4J_5J_6`; `k = 8`: `L ⊕ L'` with `L, L'` the (8-dimensional) minimal `(J_1, …, J_7)`-spaces on
  which `J_7 = J_1⋯J_6`, resp. `J_7 = -J_1⋯J_6`, i.e. `ℝ¹⁶ = ker(J_7 - J_1⋯J_6) ⊕ ker(J_7 + J_1⋯J_6)`, both
  8-dimensional and closed under `J_1, …, J_7`. (That `H, H'`, `L, L'` are these eigenspaces is my reading of the
  notation, consistent with the `k = 3` and `k = 7` descriptions.) Products are left-associated.
- "The proof follows that of 24.6" is a proof indication, not formalized.
-/
namespace RoundTrip.V15_16

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

/-- Milnor's values `m_0, …, m_8 = 1, 2, 4, 4, 8, 8, 8, 8, 16`. -/
def mTab : Fin 9 → ℕ := ![1, 2, 4, 4, 8, 8, 8, 8, 16]

/-- The subspace `ker A ⊆ ℝⁿ`. -/
def kerM {n : ℕ} (A : Mat (Fin n)) : Submodule ℝ (Fin n → ℝ) := LinearMap.ker (Matrix.mulVecLin A)

/-- `J_1J_2J_3J_4J_5J_6`. -/
def P6 {n : ℕ} (Js : ℕ → Mat (Fin n)) : Mat (Fin n) := Js 1 * Js 2 * Js 3 * Js 4 * Js 5 * Js 6

/-- `S` is closed under `A`. -/
def Stab {n : ℕ} (A : Mat (Fin n)) (S : Submodule ℝ (Fin n → ℝ)) : Prop := ∀ v ∈ S, A *ᵥ v ∈ S

/-- Lemma 24.8 (dimensions): a minimal `(J_1, …, J_k)`-space (`k ≤ 8`) has dimension `m_k`; it is a line over `ℝ, ℂ, ℍ`
(`k ≤ 2`), a quaternionic line with `J_3 = ±J_1J_2` (`k = 3`), `H ⊕ H'` (`k = 4, 5, 6`), has `J_7 = ±J_1⋯J_6`
(`k = 7`), and is `L ⊕ L'` (`k = 8`). -/
def B : Prop :=
  (∀ (k : Fin 9) (n : ℕ) (Js : ℕ → Mat (Fin n)), IsMinACSp Js k → n = mTab k) ∧
  (∀ (n : ℕ) (Js : ℕ → Mat (Fin n)), IsMinACSp Js 3 → Js 3 = Js 1 * Js 2 ∨ Js 3 = -(Js 1 * Js 2)) ∧
  (∀ (k n : ℕ) (Js : ℕ → Mat (Fin n)), 4 ≤ k → k ≤ 6 → IsMinACSp Js k →
    Module.finrank ℝ (kerM (Js 3 - Js 1 * Js 2)) = 4 ∧ Module.finrank ℝ (kerM (Js 3 + Js 1 * Js 2)) = 4 ∧
    kerM (Js 3 - Js 1 * Js 2) ⊔ kerM (Js 3 + Js 1 * Js 2) = ⊤ ∧
    (∀ α, 1 ≤ α → α ≤ 2 → Stab (Js α) (kerM (Js 3 - Js 1 * Js 2)) ∧ Stab (Js α) (kerM (Js 3 + Js 1 * Js 2)))) ∧
  (∀ (n : ℕ) (Js : ℕ → Mat (Fin n)), IsMinACSp Js 7 → Js 7 = P6 Js ∨ Js 7 = -P6 Js) ∧
  (∀ (n : ℕ) (Js : ℕ → Mat (Fin n)), IsMinACSp Js 8 →
    Module.finrank ℝ (kerM (Js 7 - P6 Js)) = 8 ∧ Module.finrank ℝ (kerM (Js 7 + P6 Js)) = 8 ∧
    kerM (Js 7 - P6 Js) ⊔ kerM (Js 7 + P6 Js) = ⊤ ∧
    (∀ α, 1 ≤ α → α ≤ 7 → Stab (Js α) (kerM (Js 7 - P6 Js)) ∧ Stab (Js α) (kerM (Js 7 + P6 Js))))

end RoundTrip.V15_16
