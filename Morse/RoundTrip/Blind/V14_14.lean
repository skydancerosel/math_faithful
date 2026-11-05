import Morse
/-! Blind formalization of V14_14 (Milnor §23, pp. 126–127, 130: the geodesics from `I` to `−I` in `SU(n)`). Choices:
- §23 matrix-group setting: prelude `Prelude23` copied verbatim from V14_1 (shared by V14_1–V14_20; it continues the
  matrix conventions of V12_14): `Mat n = Matrix (Fin n) (Fin n) ℂ` (`n ≥ 0`, `n = 0` allowed), `U(n) = Un n` and
  `SU(n) = SUn n` are Mathlib's `Matrix.unitaryGroup` / `Matrix.specialUnitaryGroup`, as subsets of `M_n(ℂ)`;
  `𝔲(n) = uAlg n` (skew-Hermitian, `Aᴴ = −A`) and `𝔰𝔲(n) = suAlg n` (skew-Hermitian of trace `0`) are real
  subspaces of `M_n(ℂ)` (Milnor pp. 125–126; taken as the Lie algebras, not re-proved here); `exp = mexp` is Mathlib's
  `NormedSpace.exp` on `M_n(ℂ)`; Milnor's metric `⟨A, B⟩ = Re tr(AB*)` is `ipM` with `|A| = normM A = √(tr AA*)`;
  derivatives / smoothness of curves `ℝ → M_n(ℂ)` use the scoped elementwise norm (`Matrix.Norms.Elementwise`, as in
  V12_14; any norm gives the same notions). Mathlib gives `U(n)` no manifold structure, so lengths are Euclidean
  lengths in `M_n(ℂ)` of curves lying in the group (= Riemannian lengths for the induced bi-invariant metric), and
  the geodesics through `I` are taken, as Milnor does, to be the curves `t ↦ exp tA` (Lemma 21.2 / Theorem 21.3).
- Prelude vocabulary (plain names): `diagI a = diag(ia_1,…,ia_n)`, `milnorA k = diag(iπk_1,…,iπk_n)`,
  `eigenSp A μ = Eigen(μ) ⊆ ℂⁿ`, `expCurve A = (t ↦ exp tA)`, `IsPWIn G c a b` (piecewise smooth path in `G` on
  `[a,b]`), `arcLenM`, `IsMinimalIn G c a b` (length `≤` that of every piecewise smooth path in `G` joining the end
  points, as `IsMinimal` of V13_1), `minVelIn G 𝔤` (the `A ∈ 𝔤` with `exp A = −I` whose geodesic is minimal),
  `Kop A W = ¼[[A,W],A]`, Milnor's `eReal j l = E_jl`, `eImag j l = E'_jl`, `diagSU n`, `Pairs n` (`j < l`),
  `conjParams e` (positive conjugate parameters of an eigenvalue `e`, Theorem 20.5), `specMult`, `specIndex` (index of a
  spectrum via Theorems 20.5 and 15.1), `milnorSpec k`, `bottFormula k = Σ_{k_j > k_l}(k_j − k_l − 2)`.
- `SU(n)` as a Riemannian manifold (needed for geodesics as such, `Ω`, conjugate points and indices): as in the blind
  file V14_22 (and as the round sphere `IsRoundSphere` of V13_6/V13_7), an abstract smooth Hausdorff connected manifold
  `M` modelled on `ℝ^d = EuclideanSpace ℝ (Fin d)` with a smooth Mathlib `RiemannianBundle` metric, and
  `ψ : M → M_n(ℂ)` a smooth topological embedding onto Mathlib's `SU(n)` whose differential is isometric for Milnor's
  `Re tr(AB*)` (`IsSUModel n ψ`, copied verbatim from V14_22 with `dMat`); `B` is claimed for every such model (and every
  Levi-Civita connection `cov`, `IsLC`, where one is needed). `I`, `−I` are the points `p`, `q` with `ψ p = 1`,
  `ψ q = −1`; "the geodesic `t ↦ exp tA`" is a geodesic `γ` of `M` with `ψ (γ t) = exp(tA)`. The group structure (the
  Lie-group prelude of V12_*) is not needed: Milnor's metric is the explicit restriction of `Re tr(AB*)`, which is what
  `IsSUModel` encodes (left and right translations by unitaries are isometries of `M_n(ℂ)` preserving `SU(n)`). Here
  geodesics, lengths and minimality are those of `M` (not Prelude23's matrix-level conventions `expCurve`,
  `IsMinimalIn`, which are used only through the formulas `milnorA`, `Kop`, `conjParams`, `specMult`, `bottFormula`).
- Riemannian vocabulary copied verbatim (only the definitions needed) from V13_1: `Conn`, `IsLC`, `IsGeodesic`,
  `IsGeodPQ`, `IsPW`, `arcLen`, `rho`, `IsMinimal` (Milnor p. 61), `IsJacobi`, `JacOn`, the index `λ(γ) = lam 1 γ`
  (`ℕ∞`-valued: the index of `E_**` on `TΩ_γ`), `Om n p q = Ω(M;p,q)` (Milnor's `d`-topology), `OmD n p q = Ω^d`
  (`d = ρ(p,q)²`), `curvR` (Milnor's sign); from V12_18: `IsConjAt`, `conjMultAt` (conjugate points at any parameter
  `t ≠ 0`, Jacobi fields on `[0,t]`) and `KV` (`K_V(W) = R(V,W)V`); from V14_22: `Grass k m = G_m(ℂ^k)` (Hermitian
  idempotents of rank `m`, subspace topology of `M_k(ℂ)`).
- "A geodesic from `I` to `−I`" = `IsGeodPQ d cov p q γ` (a geodesic `γ : [0,1] → M` with `γ 0 = p`, `γ 1 = q`,
  `ψ p = I`, `ψ q = −I`). The title restricts to `SU(n)` (Milnor's preliminary discussion in `U(n)`, where only the
  condition `Σ k_j = 0` is dropped, is not separately claimed); `n` arbitrary (for odd `n`, `−I ∉ SU(n)` and the claim
  is vacuous).
- Claim: every such `γ` is `t ↦ exp tA` on `[0,1]` (`ψ (γ t) = exp(tA)`) for some `A ∈ 𝔰𝔲(n)` with `exp A = −I`, and
  "after conjugation by a unitary `T`" `A = T·diag(iπk_1,…,iπk_n)·T⁻¹` (`T⁻¹ = Tᴴ`, `T ∈ U(n)`) with odd integers `k_j`
  and `k_1 + … + k_n = 0`. The converse (each such `t ↦ exp tA` is a geodesic from `I` to `−I`) is not claimed: the md
  describes the geodesics; that one-parameter subgroups are geodesics is Lemma 21.2 / Theorem 21.3, presupposed.
-/
namespace RoundTrip.V14_14

open scoped ContDiff Matrix
open scoped Matrix.Norms.Elementwise

section Prelude23

/-- `M_n(ℂ)`, the `n × n` complex matrices. -/
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- `U(n)` as a subset of `M_n(ℂ)` (Mathlib's `Matrix.unitaryGroup`: `Uᴴ U = U Uᴴ = I`). -/
abbrev Un (n : ℕ) : Set (Mat n) := (Matrix.unitaryGroup (Fin n) ℂ : Set (Mat n))

/-- `SU(n)` as a subset of `M_n(ℂ)` (Mathlib's `Matrix.specialUnitaryGroup`: unitary of determinant `1`). -/
abbrev SUn (n : ℕ) : Set (Mat n) := (Matrix.specialUnitaryGroup (Fin n) ℂ : Set (Mat n))

/-- Milnor's inner product `⟨A, B⟩ = Re tr(AB*)` on `M_n(ℂ)` (p. 125); restricted to the tangent spaces of `U(n)` it is
the bi-invariant metric. -/
noncomputable def ipM {n : ℕ} (A B : Mat n) : ℝ := (Matrix.trace (A * Bᴴ)).re

/-- `|A| = √⟨A, A⟩ = √(tr AA*)`. -/
noncomputable def normM {n : ℕ} (A : Mat n) : ℝ := Real.sqrt (ipM A A)

/-- `𝔲(n)`: the skew-Hermitian matrices `Aᴴ = −A` (the Lie algebra of `U(n)`), a real subspace of `M_n(ℂ)`. -/
def uAlg (n : ℕ) : Submodule ℝ (Mat n) where
  carrier := {A | Aᴴ = -A}
  add_mem' := by
    intro A B (hA : Aᴴ = -A) (hB : Bᴴ = -B)
    change (A + B)ᴴ = -(A + B)
    rw [Matrix.conjTranspose_add, hA, hB, neg_add]
  zero_mem' := by
    change (0 : Mat n)ᴴ = -0
    simp
  smul_mem' := by
    intro r A (hA : Aᴴ = -A)
    change (r • A)ᴴ = -(r • A)
    rw [Matrix.conjTranspose_smul, hA, star_trivial, smul_neg]

/-- `𝔰𝔲(n)`: the skew-Hermitian matrices of trace `0` (the Lie algebra of `SU(n)`, Milnor p. 126). -/
def suAlg (n : ℕ) : Submodule ℝ (Mat n) where
  carrier := {A | Aᴴ = -A ∧ Matrix.trace A = 0}
  add_mem' := by
    rintro A B ⟨hA, tA⟩ ⟨hB, tB⟩
    exact ⟨by rw [Matrix.conjTranspose_add, hA, hB, neg_add], by rw [Matrix.trace_add, tA, tB, add_zero]⟩
  zero_mem' := ⟨by simp, by simp⟩
  smul_mem' := by
    rintro r A ⟨hA, tA⟩
    exact ⟨by rw [Matrix.conjTranspose_smul, hA, star_trivial, smul_neg], by rw [Matrix.trace_smul, tA, smul_zero]⟩

/-- The matrix exponential `exp A = Σ Aᵏ/k!` (Mathlib's `NormedSpace.exp`). -/
noncomputable def mexp {n : ℕ} (A : Mat n) : Mat n := NormedSpace.exp A

/-- The one-parameter subgroup `t ↦ exp tA` (the geodesic through `I` with velocity `A`, Milnor §21/§23). -/
noncomputable def expCurve {n : ℕ} (A : Mat n) : ℝ → Mat n := fun t => mexp (t • A)

/-- `diag(ia_1, …, ia_n)` for real `a_j`. -/
noncomputable def diagI {n : ℕ} (a : Fin n → ℝ) : Mat n := Matrix.diagonal fun j => (a j : ℂ) * Complex.I

/-- Milnor's `A = diag(iπk_1, …, iπk_n)` for integers `k_j`. -/
noncomputable def milnorA {n : ℕ} (k : Fin n → ℤ) : Mat n := diagI fun j => Real.pi * (k j : ℝ)

/-- `Eigen(μ) = {v ∈ ℂⁿ | Av = μv}`. -/
noncomputable def eigenSp {n : ℕ} (A : Mat n) (μ : ℂ) : Submodule ℂ (Fin n → ℂ) :=
  Module.End.eigenspace (Matrix.toLin' A) μ

/-- Piecewise smooth path in `G ⊆ M_n(ℂ)` on `[a, b]`: values in `G` on `[a, b]`, and a subdivision
`a = t₀ < … < t_k = b` with `c` smooth (`C^∞`) on each `[t_{i-1}, t_i]` (so `c` is continuous on `[a, b]`). -/
def IsPWIn {n : ℕ} (G : Set (Mat n)) (c : ℝ → Mat n) (a b : ℝ) : Prop :=
  (∀ t ∈ Set.Icc a b, c t ∈ G) ∧
    ∃ (k : ℕ) (t : ℕ → ℝ), t 0 = a ∧ t k = b ∧ (∀ i < k, t i < t (i + 1)) ∧
      ∀ i < k, ContDiffOn ℝ ∞ c (Set.Icc (t i) (t (i + 1)))

/-- Arc length `∫_a^b |dc/dt| dt` for Milnor's metric (the derivative exists off a finite set). -/
noncomputable def arcLenM {n : ℕ} (c : ℝ → Mat n) (a b : ℝ) : ℝ := ∫ t in a..b, normM (deriv c t)

/-- `c|[a,b]` is a minimal path in `G` (Milnor p. 61): a piecewise smooth path in `G` whose length is `≤` the length of
every piecewise smooth path in `G` (on any parameter interval) joining its end points. -/
def IsMinimalIn {n : ℕ} (G : Set (Mat n)) (c : ℝ → Mat n) (a b : ℝ) : Prop :=
  IsPWIn G c a b ∧
    ∀ (pw : ℝ → Mat n) (a' b' : ℝ), a' ≤ b' → IsPWIn G pw a' b' → pw a' = c a → pw b' = c b →
      arcLenM c a b ≤ arcLenM pw a' b'

/-- The velocities `A ∈ 𝔤` of the minimal geodesics `t ↦ exp tA`, `0 ≤ t ≤ 1`, from `I` to `−I` in `G`. -/
def minVelIn {n : ℕ} (G : Set (Mat n)) (𝔤 : Submodule ℝ (Mat n)) : Set (Mat n) :=
  {A | A ∈ 𝔤 ∧ mexp A = -1 ∧ IsMinimalIn G (expCurve A) 0 1}

/-- Milnor's `K_A(W) = R(A, W)A = ¼[[A, W], A]` (p. 130, by Theorem 21.3(b)), `[X, Y] = XY − YX`. -/
noncomputable def Kop {n : ℕ} (A W : Mat n) : Mat n :=
  (1 / 4 : ℝ) • ((A * W - W * A) * A - A * (A * W - W * A))

/-- Milnor's `E_jl` (p. 131): `+1` in place `(j, l)`, `−1` in place `(l, j)`, `0` elsewhere. -/
def eReal {n : ℕ} (j l : Fin n) : Mat n := Matrix.single j l 1 - Matrix.single l j 1

/-- Milnor's `E'_jl` (p. 131): `+i` in places `(j, l)` and `(l, j)`, `0` elsewhere. -/
def eImag {n : ℕ} (j l : Fin n) : Mat n := Matrix.single j l Complex.I + Matrix.single l j Complex.I

/-- The diagonal matrices of `𝔰𝔲(n)`. -/
def diagSU (n : ℕ) : Set (Mat n) := {D | D ∈ suAlg n ∧ ∀ i j, i ≠ j → D i j = 0}

/-- The pairs `(j, l)` with `j < l`. -/
abbrev Pairs (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- Theorem 20.5 as a definition: the (positive) parameters `t = π/√e, 2π/√e, …` at which an eigenvalue `e` of `K_V`
gives a conjugate point (none if `e ≤ 0`). -/
def conjParams (e : ℝ) : Set ℝ := {t | 0 < t ∧ 0 < e ∧ ∃ s : ℤ, t = s * (Real.pi / Real.sqrt e)}

/-- Theorem 20.5: the multiplicity of the conjugate point at parameter `t` for a spectrum `e` of `K_V` (eigenvalues
listed with multiplicity): the number of indices `i` with `t` a conjugate parameter of `e i`. -/
noncomputable def specMult {κ : Type} (e : κ → ℝ) (t : ℝ) : ℕ := {i | t ∈ conjParams (e i)}.ncard

/-- Theorem 15.1 as a definition: the index of a geodesic `γ : [0,1] → M` with spectrum `e`, i.e. the number of
conjugate points `γ(t)`, `0 < t < 1`, counted with multiplicity. -/
noncomputable def specIndex {κ : Type} (e : κ → ℝ) : ℕ := ∑ᶠ t ∈ Set.Ioo (0 : ℝ) 1, specMult e t

/-- Milnor's spectrum of `K_A` on `𝔰𝔲(n)` for `A = diag(iπk_1, …, iπk_n)` (p. 131), read off his basis: for each pair
`j < l` two eigenvalues `π²(k_j − k_l)²/4` (eigenvectors `E_jl`, `E'_jl`), and `n − 1` eigenvalues `0` (the diagonal
matrices of `𝔰𝔲(n)`). -/
noncomputable def milnorSpec {n : ℕ} (k : Fin n → ℤ) : (Pairs n × Fin 2) ⊕ Fin (n - 1) → ℝ
  | .inl (p, _) => Real.pi ^ 2 / 4 * ((k p.1.1 : ℝ) - k p.1.2) ^ 2
  | .inr _ => 0

/-- Milnor's index formula `Σ_{k_j > k_l} (k_j − k_l − 2)`, summed over the ordered pairs `(j, l)` with `k_j > k_l`. -/
def bottFormula {n : ℕ} (k : Fin n → ℤ) : ℤ :=
  ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => k p.2 < k p.1), (k p.1 - k p.2 - 2)

end Prelude23

open scoped Manifold
open Topology Bundle

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

/-- Piecewise smooth path on `[a, b]`: a subdivision `a = t₀ < ... < t_k = b` with each `pth|[t_{i-1}, t_i]` smooth. -/
def IsPW (pth : ℝ → M) (a b : ℝ) : Prop :=
  ∃ (k : ℕ) (t : ℕ → ℝ), t 0 = a ∧ t k = b ∧ (∀ i < k, t i < t (i + 1)) ∧
    ∀ i < k, ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) ∞ pth (Set.Icc (t i) (t (i + 1)))

/-- Arc length `∫_a^b ‖dpth/dt‖ dt` (the derivative exists off a finite set). -/
noncomputable def arcLen (pth : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ‖(mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) pth t (1 : ℝ) : TangentSpace 𝓘(ℝ, Rn n) (pth t))‖

/-- `ρ(p, q)`: greatest lower bound of the arc lengths of piecewise smooth paths joining `p` and `q`. -/
noncomputable def rho (p q : M) : ℝ :=
  sInf {L | ∃ (pth : ℝ → M) (a b : ℝ), a ≤ b ∧ IsPW (n := n) pth a b ∧ pth a = p ∧ pth b = q ∧ arcLen (n := n) pth a b = L}
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
end Ch7b

section Ch8
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]

/-- `pw ∈ Ω(M; p, q)`: a piecewise smooth path `[0,1] → M` from `p` to `q` (only values on `[0,1]` matter). -/
def InOmega (p q : M) (pw : ℝ → M) : Prop := IsPW (n := n) pw 0 1 ∧ pw 0 = p ∧ pw 1 = q

/-- Energy `E_a^b(pw) = ∫_a^b ‖dpw/dt‖² dt`. -/
noncomputable def energy (pw : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ‖(mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) pw t (1 : ℝ) : TangentSpace 𝓘(ℝ, Rn n) (pw t))‖ ^ 2

/-- `E = E_0^1`. -/
noncomputable def Efun (pw : ℝ → M) : ℝ := energy (n := n) pw 0 1

/-- Variation vector field `W_t = ∂α/∂u_i (0, t)`. -/
noncomputable def varField {m : ℕ} (α : Rn m → ℝ → M) (i : Fin m) (t : ℝ) : TangentSpace 𝓘(ℝ, Rn n) (α 0 t) :=
  mfderiv 𝓘(ℝ, Rn m) 𝓘(ℝ, Rn n) (fun u => α u t) 0 (EuclideanSpace.single i (1 : ℝ))

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

end Ch8

section Ch8b
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]

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

/-- Arc length function `s(t)` of `w` from `0` to `t` and its derivative `ds/dt`. -/
noncomputable def dsdt (w : ℝ → M) (t : ℝ) : ℝ := deriv (fun x => arcLen (n := n) w 0 x) t

/-- Milnor's distance `d(w,w') = max_t ρ(w(t),w'(t)) + [∫₀¹ (ds/dt − ds'/dt)² dt]^{1/2}`. -/
noncomputable def dOm (w w' : ℝ → M) : ℝ :=
  (⨆ t : Set.Icc (0 : ℝ) 1, rho (n := n) (w t) (w' t)) +
    Real.sqrt (∫ t in (0 : ℝ)..1, (dsdt (n := n) w t - dsdt (n := n) w' t) ^ 2)

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

/-- `γ` is a geodesic from `p` to `q` (on `[0,1]`). -/
def IsGeodPQ (cov : Conn n M) (p q : M) (γ : ℝ → M) : Prop :=
  IsGeodesic cov γ (Set.Icc 0 1) ∧ γ 0 = p ∧ γ 1 = q
end Ch10

section Curv
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]

open Classical in
/-- The curvature tensor `R(x,y)z` at `p` (Milnor's sign, via `IsCurvVal`); junk value `0` if no value exists. -/
noncomputable def curvR (cov : Conn n M) (p : M) (x y z : TangentSpace 𝓘(ℝ, Rn n) p) : TangentSpace 𝓘(ℝ, Rn n) p :=
  if h : ∃ r, IsCurvVal cov p x y z r then h.choose else 0
end Curv

section Ch22
variable (n : ℕ) {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]

/-- `d = ρ(p, q)²`. -/
noncomputable def dPQ (p q : M) : ℝ := rho (n := n) p q ^ 2

/-- `Ω^d = E⁻¹[0, d] ⊆ Ω = Ω(M; p, q)` with `d = ρ(p, q)²` (Milnor's notation `Ω^c`, here `c = d`); as a type it carries
the subspace topology of `Ω` (Milnor's `d`-topology). -/
def OmD (p q : M) : Set (Om n p q) := OmLe n p q (dPQ n p q)

end Ch22

section Sym
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]

/-- `γ(t)` is conjugate to `γ(0)` along `γ|[0,t]` (`t ≠ 0`, either sign): a non-zero Jacobi field along `γ` on the
interval between `0` and `t` vanishes at `0` and at `t`. -/
def IsConjAt (cov : Conn n M) (γ : ℝ → M) (t : ℝ) : Prop :=
  t ≠ 0 ∧ ∃ J ∈ JacOn cov γ (Set.uIcc 0 t), J ≠ 0 ∧ J 0 = 0 ∧ J t = 0

/-- Multiplicity of `γ(t)` as a conjugate point of `γ(0)` along `γ|[0,t]`: dimension of the space of Jacobi fields
along `γ` on the interval between `0` and `t` vanishing at `0` and `t`. -/
noncomputable def conjMultAt (cov : Conn n M) (γ : ℝ → M) (t : ℝ) : ℕ∞ :=
  setDim {J | J ∈ JacOn cov γ (Set.uIcc 0 t) ∧ J 0 = 0 ∧ J t = 0}

/-- Milnor's `K_V(W) = R(V, W)V` on `T_pM`. -/
noncomputable def KV (cov : Conn n M) (p : M) (V W : TangentSpace 𝓘(ℝ, Rn n) p) : TangentSpace 𝓘(ℝ, Rn n) p :=
  curvR cov p V W V
end Sym

section MatrixGroups

/-- `G_m(ℂ^k)`: the `m`-dimensional subspaces of `ℂ^k`, modelled by their orthogonal projections (Hermitian
idempotent matrices of rank `m`), with the subspace topology of `M_k(ℂ)`. -/
def Grass (k m : ℕ) : Set (Mat k) := {P | P.conjTranspose = P ∧ P * P = P ∧ P.rank = m}
end MatrixGroups

section SUModel
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]

/-- The differential `dψ_x(v)` of `ψ : M → M_k(ℂ)`, read as a matrix (derivative in the normed space
`Fin k → Fin k → ℂ` underlying `M_k(ℂ)`; sup norm, any norm gives the same derivative). -/
noncomputable def dMat (k : ℕ) (ψ : M → (Fin k → Fin k → ℂ)) (x : M) (v : TangentSpace 𝓘(ℝ, Rn n) x) : Mat k :=
  mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, Fin k → Fin k → ℂ) ψ x v

/-- `M` is `SU(k)` with Milnor's bi-invariant metric `⟨A, B⟩ = Re tr(AB*)` (p. 125): `ψ : M → M_k(ℂ)` is a smooth
topological embedding onto `SU(k)` whose differential is isometric for the metric of `M` and `Re tr(AB*)` (the
Euclidean inner product of `M_k(ℂ) = ℝ^{2k²}`). -/
def IsSUModel (k : ℕ) (ψ : M → (Fin k → Fin k → ℂ)) : Prop :=
  ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, Fin k → Fin k → ℂ) ∞ ψ ∧ Topology.IsEmbedding ψ ∧
  Set.range ψ = (Matrix.specialUnitaryGroup (Fin k) ℂ : Set (Mat k)) ∧
  ∀ (x : M) (v w : TangentSpace 𝓘(ℝ, Rn n) x),
    inner ℝ v w = (Matrix.trace (dMat k ψ x v * (dMat k ψ x w)ᴴ)).re
end SUModel

/-- Every geodesic from `I` to `−I` in `SU(n)` is `t ↦ exp tA` with `A ∈ 𝔰𝔲(n)`, `exp A = −I`, and
`A = T·diag(iπk_1,…,iπk_n)·T⁻¹` for a unitary `T` and odd integers `k_j` with `Σ k_j = 0`. -/
def B : Prop :=
  ∀ (n d : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (Rn d) M] [IsManifold 𝓘(ℝ, Rn d) ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn d) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, Rn d) ∞ (Rn d) (fun x : M => TangentSpace 𝓘(ℝ, Rn d) x)]
    [ConnectedSpace M] (ψ : M → Mat n), IsSUModel (n := d) n ψ →
    ∀ cov : Conn d M, IsLC cov → ∀ p q : M, ψ p = 1 → ψ q = -1 → ∀ γ : ℝ → M, IsGeodPQ d cov p q γ →
      ∃ A ∈ suAlg n, mexp A = -1 ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, ψ (γ t) = mexp (t • A)) ∧
        ∃ T ∈ Un n, ∃ k : Fin n → ℤ, (∀ j, Odd (k j)) ∧ ∑ j, k j = 0 ∧ A = T * milnorA k * Tᴴ

end RoundTrip.V14_14
