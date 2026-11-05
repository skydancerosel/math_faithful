import Morse
/-! Blind formalization of V15_29 (Milnor §24, pp. 144–145: the splitting into minimal pieces; Lemma 24.8 between two pieces). Choices:
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
- Setting (p. 144): `k ≥ 1`, fixed anticommuting `J_1, …, J_{k-1}` (`IsACFam Js (k - 1)`), `J ∈ Ω_k(n)`, and the
  velocity `A` of a geodesic `t ↦ J exp(πtA)` from `J` to `−J` in `Ω_k(n)`: `A` skew, anticommuting with `J`, commuting
  with `J_1, …, J_{k-1}` (Milnor's `A ∈ T`), `exp(πA) = −I`. All `n`.
- Subspaces of `ℝⁿ` are Mathlib `Submodule`s of `Fin n → ℝ`; `⊥` and isometries use the dot product (as in V15_11).
  "Closed under" a family of matrices: `ClosedF`; "minimal" (Milnor p. 143, V15_13): `M ≠ 0`, closed, and no subspace
  of `M` other than `0` and `M` is closed (`IsMinF`). `F₀ = {J_1, …, J_{k-1}, J, A}` (`famA`).
- Claims (conjunction): (1) there is a decomposition `ℝⁿ = M_1 ⊕ ⋯ ⊕ M_s` into mutually orthogonal subspaces, each
  closed and minimal under `F₀`. (2)–(3) For every subspace `M` closed and minimal under `F₀` — equivalently, every
  piece `M_h` of every such decomposition (the orthogonal complement of a closed subspace is closed, all members of
  `F₀` being orthogonal or skew) — there is an odd `a ∈ ℕ` (so `a > 0`) with `A² = −a²` on `M` (the eigenvalues of `A`
  on `M` are `±ia`, "all equal except for sign"), and `J' = a⁻¹JA` restricted to `M` is a complex structure on `M`
  (preserves `M`, `J'² = −1` and `|J'v| = |v|` on `M`) anticommuting there with `J_1, …, J_{k-1}` and `J`, and `M` is a
  minimal `(J_1, …, J_{k-1}, J, J')`-space; and `dim M = m_{k+1}`. (4) "`s = n/m_{k+1}`": every such decomposition has
  `s · m_{k+1} = n`.
- (5) "For `h ≠ j` an isometry from `M_h` to `M̄_j` exists by 24.8": `M̄_j` is read as `M_j` with the structures
  `J_1, …, J_{k-1}, J, −J'_j` (`J'_j = a_j⁻¹JA|M_j`), so the isometry `D : M_h → M_j` (onto, preserving the dot product)
  commutes with `J_1, …, J_{k-1}`, `J` and satisfies `D J'_h = −J'_j D`. Lemma 24.8 (for `k + 1` structures) needs
  `k + 1 ≢ 3 (mod 4)`, so (5) is stated under Milnor's hypothesis of p. 146, `k ≢ 2 (mod 4)` (not in the quoted text,
  but implied by "by 24.8"); "`h ≠ j`" is read as: any two orthogonal minimal closed subspaces `M`, `M'` (equivalently
  two distinct pieces of some decomposition), `a`, `a'` being their odd numbers from (2).
- Milnor's `m_k` (p. 143, V15_13: the dimension of a minimal `(J_1, …, J_k)`-space) is `mK k`, defined by Milnor's
  table `m_0, …, m_8 = 1, 2, 4, 4, 8, 8, 8, 8, 16` and `m_k = 16 m_{k-8}` (`k > 8`), not as a dimension (that the
  minimal spaces have this dimension is Lemma 24.8 / V15_16, not re-asserted).
-/
namespace RoundTrip.V15_29

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

section Splitting
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `M` is closed under every matrix of the family `F`. -/
def ClosedF (F : Set (Mat ι)) (M : Submodule ℝ (ι → ℝ)) : Prop := ∀ X ∈ F, ∀ v ∈ M, X *ᵥ v ∈ M

/-- `M` is a minimal space for `F` (Milnor p. 143): `M ≠ 0`, `M` is closed under `F`, and no subspace of `M` other
than `0` and `M` is closed under `F`. -/
def IsMinF (F : Set (Mat ι)) (M : Submodule ℝ (ι → ℝ)) : Prop :=
  M ≠ ⊥ ∧ ClosedF F M ∧ ∀ W : Submodule ℝ (ι → ℝ), W ≤ M → ClosedF F W → W = ⊥ ∨ W = M

/-- `S ⊥ T` for the dot product of `ℝ^ι`. -/
def Perp (S T : Submodule ℝ (ι → ℝ)) : Prop := ∀ v ∈ S, ∀ w ∈ T, v ⬝ᵥ w = 0

/-- The family `J_1, …, J_{k-1}, J, X`. -/
def famA (Js : ℕ → Mat ι) (k : ℕ) (J X : Mat ι) : Set (Mat ι) :=
  {Y | (∃ α, 1 ≤ α ∧ α ≤ k - 1 ∧ Y = Js α) ∨ Y = J ∨ Y = X}

/-- `J' = a⁻¹JA`. -/
noncomputable def Jpr (J A : Mat ι) (a : ℕ) : Mat ι := ((a : ℝ)⁻¹) • (J * A)
end Splitting

/-- `ℝⁿ = M_1 ⊕ ⋯ ⊕ M_s`, orthogonal pieces closed and minimal under `J_1, …, J_{k-1}, J, A`; on each piece
`A² = −a_h²` with `a_h` odd, `J' = a_h⁻¹JA` makes it a minimal `(J_1, …, J_{k-1}, J, J')`-space, of dimension
`m_{k+1}`, so `s = n/m_{k+1}`; for `k ≢ 2 (mod 4)`, two pieces `M_h`, `M_j` admit an isometry `M_h → M̄_j`. -/
def B : Prop :=
  ∀ (n k : ℕ) (Js : ℕ → Mat (Fin n)), 1 ≤ k → IsACFam Js (k - 1) →
    ∀ J ∈ OmegaK Js k, ∀ A : Mat (Fin n), IsSkew A → AntiComm A J →
      (∀ α, 1 ≤ α → α ≤ k - 1 → Commute A (Js α)) → mexp (Real.pi • A) = -1 →
      (∃ (s : ℕ) (Ms : Fin s → Submodule ℝ (Fin n → ℝ)), (∀ h, IsMinF (famA Js k J A) (Ms h)) ∧
        (∀ h h', h ≠ h' → Perp (Ms h) (Ms h')) ∧ ⨆ h, Ms h = ⊤) ∧
      (∀ M : Submodule ℝ (Fin n → ℝ), IsMinF (famA Js k J A) M →
        ∃ a : ℕ, Odd a ∧ (∀ v ∈ M, (A * A) *ᵥ v = -((a : ℝ) ^ 2) • v) ∧
          (∀ v ∈ M, Jpr J A a *ᵥ v ∈ M ∧ Jpr J A a *ᵥ (Jpr J A a *ᵥ v) = -v ∧
            (Jpr J A a *ᵥ v) ⬝ᵥ (Jpr J A a *ᵥ v) = v ⬝ᵥ v ∧
            Jpr J A a *ᵥ (J *ᵥ v) = -(J *ᵥ (Jpr J A a *ᵥ v)) ∧
            ∀ α, 1 ≤ α → α ≤ k - 1 → Jpr J A a *ᵥ (Js α *ᵥ v) = -(Js α *ᵥ (Jpr J A a *ᵥ v))) ∧
          IsMinF (famA Js k J (Jpr J A a)) M ∧ Module.finrank ℝ M = mK (k + 1)) ∧
      (∀ (s : ℕ) (Ms : Fin s → Submodule ℝ (Fin n → ℝ)), (∀ h, IsMinF (famA Js k J A) (Ms h)) →
        (∀ h h', h ≠ h' → Perp (Ms h) (Ms h')) → ⨆ h, Ms h = ⊤ → s * mK (k + 1) = n) ∧
      (k % 4 ≠ 2 → ∀ (M M' : Submodule ℝ (Fin n → ℝ)) (a a' : ℕ),
        IsMinF (famA Js k J A) M → IsMinF (famA Js k J A) M' → Perp M M' → Odd a → Odd a' →
        (∀ v ∈ M, (A * A) *ᵥ v = -((a : ℝ) ^ 2) • v) → (∀ v ∈ M', (A * A) *ᵥ v = -((a' : ℝ) ^ 2) • v) →
        ∃ D : Mat (Fin n), (∀ v ∈ M, D *ᵥ v ∈ M') ∧ (∀ w ∈ M', ∃ v ∈ M, D *ᵥ v = w) ∧
          (∀ v ∈ M, ∀ w ∈ M, (D *ᵥ v) ⬝ᵥ (D *ᵥ w) = v ⬝ᵥ w) ∧
          (∀ v ∈ M, D *ᵥ (J *ᵥ v) = J *ᵥ (D *ᵥ v)) ∧
          (∀ α, 1 ≤ α → α ≤ k - 1 → ∀ v ∈ M, D *ᵥ (Js α *ᵥ v) = Js α *ᵥ (D *ᵥ v)) ∧
          ∀ v ∈ M, D *ᵥ (Jpr J A a *ᵥ v) = -(Jpr J A a' *ᵥ (D *ᵥ v)))

end RoundTrip.V15_29
