import Morse
/-! Blind formalization of V14_2 (Milnor §23, pp. 127, 130: length and trace of the velocity). Choices:
- §23 matrix-group setting: prelude `Prelude23` copied verbatim from V14_1 (shared by V14_1–V14_10; it continues the
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
- `A = T·diag(iπk_1,…,iπk_n)·T⁻¹` (`T⁻¹ = Tᴴ`) with `T ∈ U(n)` and odd integers `k_j`: the general velocity of a
  geodesic from `I` to `−I` in `U(n)` (V14_1). "The geodesic `t ↦ exp tA`" is `expCurve A` on `[0,1]` (that it is a
  geodesic is presupposed, Lemma 21.2 / Theorem 21.3, not claimed); its length is `arcLenM (expCurve A) 0 1`
  (`∫₀¹ |d/dt exp tA| dt` for the metric `Re tr(AB*)`).
- Claims (conjunction): (i) the length is `|A| = normM A = √(Re tr AA*)`; (ii) `tr AA* = π²(k_1² + … + k_n²)` (as a
  complex number, so Milnor's `√(tr AA*)` makes sense) and `|A| = π√(k_1² + … + k_n²)`; (iii) `A ∈ 𝔰𝔲(n)` (the Lie
  algebra of `SU(n)`) iff `k_1 + … + k_n = 0`.
- Oddness of the `k_j` is kept as a hypothesis (Milnor's `k_j` are the odd integers of V14_1); the claims do not use it.
-/
namespace RoundTrip.V14_2

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

/-- For `A = T·diag(iπk_j)·T⁻¹` (`T` unitary, `k_j` odd): the geodesic `t ↦ exp tA` (`0 ≤ t ≤ 1`) has length
`|A| = √(tr AA*) = π√(Σ k_j²)`, and `A ∈ 𝔰𝔲(n)` iff `Σ k_j = 0`. -/
def B : Prop :=
  ∀ (n : ℕ), ∀ T ∈ Un n, ∀ k : Fin n → ℤ, (∀ j, Odd (k j)) → ∀ A : Mat n, A = T * milnorA k * Tᴴ →
    arcLenM (expCurve A) 0 1 = normM A ∧
    Matrix.trace (A * Aᴴ) = ((Real.pi ^ 2 * ∑ j, ((k j : ℝ)) ^ 2 : ℝ) : ℂ) ∧
    normM A = Real.pi * Real.sqrt (∑ j, ((k j : ℝ)) ^ 2) ∧
    (A ∈ suAlg n ↔ ∑ j, k j = 0)

end RoundTrip.V14_2
