import Morse.Chapter12.MatrixInner
import Morse.Chapter9.JacobiSystem
import Milnor.Chapter2.LevelSet
import Milnor.Chapter8.FramedOps
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.OfAssociative

/-!
Milnor, *Morse Theory*, §21 (pp. 112–113), §23 (pp. 124–126) and §24 (p. 133): the compact
matrix groups `U(n)`, `SU(n)`, `O(n)`, `SO(n)` as submanifolds of a Euclidean space.

# Matrix groups with the bi-invariant metric induced from `Mₙ(𝕜)`

## Milnor's text, paraphrased

* p. 112: a Lie group `G` with a metric invariant under left and right translations; if `G` is
  compact such a metric exists (Haar measure).
* p. 125: "The group `U(n)` is a smooth submanifold of `Mₙ(ℂ)`" (via the exponential chart, (5)),
  "and its tangent space at `I` is the space of skew-Hermitian matrices" (6); "the Lie algebra of
  `U(n)` can be identified with the space of skew-Hermitian matrices", with bracket
  `[A, B] = AB − BA` ("a short computation shows").  The metric `⟨A, B⟩ = Re tr(AB*)` on the Lie
  algebra is left- and right-invariant (p. 126: `⟨SAS⁻¹, SBS⁻¹⟩ = ⟨A, B⟩`).
* p. 126: `SU(n)`, the matrices of determinant `1`, with Lie algebra the skew-Hermitian matrices of
  trace `0`.  p. 133: the same for `O(n)` and `SO(n)` in the real matrices.

## The setting of this project

The ambient Euclidean space is `V = Mₙ(𝕜)`, `𝕜 = ℂ` or `ℝ`, with the Frobenius inner product
`⟪A, B⟫ = Re tr(Aᴴ B)` (`Morse/Chapter12/MatrixInner.lean`), and the groups are **slice
submanifolds** of `V` in the sense of the companion project, with the induced metric: Parts II–III
of this project then apply to them verbatim.

* `Morse.skewHermitian 𝕜 ι` (`𝔲(n)`, and `𝔬(n)` for `𝕜 = ℝ`) and `Morse.specialSkewHermitian ι`
  (`𝔰𝔲(n)`): real Lie subalgebras of `Mₙ(𝕜)`; `Morse.hermitian 𝕜 ι` the Hermitian matrices.
* `Morse.IsMatrixGroup hG 𝔤`: the hypotheses on a slice submanifold `G ⊆ U(n)` and a Lie algebra
  `𝔤` of skew-Hermitian matrices used in the rest of Chapter 12 (closed under products and `ᴴ`,
  `Ad G`-invariant `𝔤`, `exp 𝔤 ⊆ G`, `dim G = dim 𝔤`).
  **The tangent space**: `Morse.IsMatrixGroup.tangentSubspace_eq`, `T_gG = g·𝔤` (and
  `= 𝔤·g`, `Morse.IsMatrixGroup.mem_tangentSubspace_iff'`).
  **Bi-invariance**: `Morse.IsMatrixGroup.mulLeftIso_image`, `Morse.IsMatrixGroup.mulRightIso_image`
  (left and right translations by elements of `G` are linear isometries of `V` carrying `G` onto
  itself), so the induced metric is left and right invariant.
* **`U(n)` and `O(n)`** (`Matrix.unitaryGroup ι 𝕜`): `Morse.isSliceSubmanifold_unitaryGroup` (a
  regular level set of `A ↦ AᴴA − I`, with values in the Hermitian matrices),
  `Morse.isMatrixGroup_unitaryGroup`, `Morse.isCompact_unitaryGroup`.
* **`SU(n)`** (`Matrix.specialUnitaryGroup ι ℂ`): `Morse.isSliceSubmanifold_specialUnitaryGroup`
  (an open piece of the regular level set of `A ↦ (AᴴA − I, Im det A)`),
  `Morse.isMatrixGroup_specialUnitaryGroup`, `Morse.isCompact_specialUnitaryGroup`.
* **`SO(n)`** (`Matrix.specialOrthogonalGroup ι ℝ`):
  `Morse.isSliceSubmanifold_specialOrthogonalGroup`
  (an open piece of `O(n)`), `Morse.isMatrixGroup_specialOrthogonalGroup`,
  `Morse.isCompact_specialOrthogonalGroup`.

## Gaps in Milnor's text

* p. 125, "`U(n)` is a smooth submanifold": Milnor's chart is `exp` near `0`, which needs that
  `exp A` unitary and `A` small force `A` skew-Hermitian.  Here `U(n)` is a regular level set
  instead; the derivative of `A ↦ AᴴA` at a unitary `A` is onto the Hermitian matrices
  (`H = AS/2 ↦ S`).
* p. 126, `SU(n)`: `{AᴴA = I, det A = 1}` is not a regular level set of `(AᴴA − I, det A − 1)`
  (the values of `det` on `U(n)` have modulus `1`, so the derivative is never onto `ℂ`).  It is an
  open piece of the regular level set `{AᴴA = I, Im det A = 0} = {AᴴA = I, det A = ±1}`
  (`Morse.mem_specialUnitaryGroup_iff_level`); for this, Jacobi's formula
  `d(det)_A(AX) = det A · tr X` is needed (`Morse.fderiv_det_mul`).  The dimension count
  `dim SU(n) = n² − 1` needs `n ≥ 1`.
* p. 125, (6): the identification of the tangent space at `I` with `𝔲(n)`; here
  `T_gG = g·𝔤` at every `g` (`Morse.IsMatrixGroup.tangentSubspace_eq`), by the curves `g exp(tX)`
  and a dimension count.
-/

open Matrix Set Filter Topology Module
open scoped Morse.MatrixInner RealInnerProductSpace Manifold ContDiff

noncomputable section

namespace Morse

/-! ### The Lie algebras -/

section LieAlgebras

variable (𝕜 : Type*) [RCLike 𝕜] (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- **`𝔲(n)`** (for `𝕜 = ℂ`; **`𝔬(n)`** for `𝕜 = ℝ`): the skew-Hermitian matrices `Xᴴ = −X`, a real
Lie subalgebra of `Mₙ(𝕜)` with the commutator bracket (Milnor p. 125). -/
def skewHermitian : LieSubalgebra ℝ (Matrix ι ι 𝕜) where
  carrier := {X | Xᴴ = -X}
  add_mem' {X Y} hX hY := by
    simp only [Set.mem_ofPred_eq] at hX hY ⊢
    rw [conjTranspose_add, hX, hY, neg_add]
  zero_mem' := by simp
  smul_mem' r X hX := by
    simp only [Set.mem_ofPred_eq] at hX ⊢
    rw [conjTranspose_smul, star_trivial, hX, smul_neg]
  lie_mem' {X Y} hX hY := by
    simp only [Set.mem_ofPred_eq] at hX hY ⊢
    rw [Ring.lie_def, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, hX, hY]
    noncomm_ring

/-- The Hermitian matrices `Aᴴ = A`, a real subspace of `Mₙ(𝕜)`. -/
def hermitian : Submodule ℝ (Matrix ι ι 𝕜) where
  carrier := {X | Xᴴ = X}
  add_mem' {X Y} hX hY := by
    simp only [Set.mem_ofPred_eq] at hX hY ⊢
    rw [conjTranspose_add, hX, hY]
  zero_mem' := by simp
  smul_mem' r X hX := by
    simp only [Set.mem_ofPred_eq] at hX ⊢
    rw [conjTranspose_smul, star_trivial, hX]

/-- **`𝔰𝔲(n)`**: the skew-Hermitian matrices of trace `0` (Milnor p. 126, his `𝔤'`). -/
def specialSkewHermitian : LieSubalgebra ℝ (Matrix ι ι ℂ) where
  carrier := {X | Xᴴ = -X ∧ trace X = 0}
  add_mem' {X Y} hX hY := by
    simp only [Set.mem_ofPred_eq] at hX hY ⊢
    rw [conjTranspose_add, hX.1, hY.1, neg_add, trace_add, hX.2, hY.2, add_zero]
    exact ⟨rfl, rfl⟩
  zero_mem' := by simp
  smul_mem' r X hX := by
    simp only [Set.mem_ofPred_eq] at hX ⊢
    rw [conjTranspose_smul, star_trivial, hX.1, smul_neg, trace_smul, hX.2, smul_zero]
    exact ⟨rfl, rfl⟩
  lie_mem' {X Y} hX hY := by
    simp only [Set.mem_ofPred_eq] at hX hY ⊢
    rw [Ring.lie_def, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, hX.1, hY.1,
      trace_sub, trace_mul_comm X Y, sub_self]
    exact ⟨by noncomm_ring, rfl⟩

variable {𝕜 ι}

theorem mem_skewHermitian {X : Matrix ι ι 𝕜} : X ∈ skewHermitian 𝕜 ι ↔ Xᴴ = -X := Iff.rfl

theorem mem_skewHermitian_toSubmodule {X : Matrix ι ι 𝕜} :
    X ∈ (skewHermitian 𝕜 ι).toSubmodule ↔ Xᴴ = -X := Iff.rfl

omit [Fintype ι] [DecidableEq ι] in
theorem mem_hermitian {X : Matrix ι ι 𝕜} : X ∈ hermitian 𝕜 ι ↔ Xᴴ = X := Iff.rfl

theorem mem_specialSkewHermitian {X : Matrix ι ι ℂ} :
    X ∈ specialSkewHermitian ι ↔ Xᴴ = -X ∧ trace X = 0 := Iff.rfl

theorem mem_specialSkewHermitian_toSubmodule {X : Matrix ι ι ℂ} :
    X ∈ (specialSkewHermitian ι).toSubmodule ↔ Xᴴ = -X ∧ trace X = 0 := Iff.rfl

omit [DecidableEq ι] in
/-- The trace of a real skew-symmetric matrix vanishes: `𝔬(n) = 𝔰𝔬(n)`. -/
theorem trace_eq_zero_of_skew_real {X : Matrix ι ι ℝ} (hX : Xᴴ = -X) : trace X = 0 := by
  have h := congrArg trace hX
  rw [trace_conjTranspose, star_trivial, trace_neg] at h
  linarith

/-- The Hermitian part `(A + Aᴴ)/2`, as a real-linear map onto `hermitian 𝕜 ι`. -/
def hermPart : Matrix ι ι 𝕜 →ₗ[ℝ] hermitian 𝕜 ι where
  toFun A := ⟨(1 / 2 : ℝ) • (A + Aᴴ), by
    rw [mem_hermitian, conjTranspose_smul, star_trivial, conjTranspose_add,
      conjTranspose_conjTranspose, add_comm]⟩
  map_add' A B := by
    ext1
    simp only [conjTranspose_add, Submodule.coe_add]
    module
  map_smul' r A := by
    ext1
    simp only [conjTranspose_smul, star_trivial, RingHom.id_apply, Submodule.coe_smul]
    module

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem coe_hermPart (A : Matrix ι ι 𝕜) :
    (hermPart A : Matrix ι ι 𝕜) = (1 / 2 : ℝ) • (A + Aᴴ) := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem hermPart_of_mem {A : Matrix ι ι 𝕜} (hA : Aᴴ = A) : (hermPart A : Matrix ι ι 𝕜) = A := by
  rw [coe_hermPart, hA, ← two_smul ℝ A, smul_smul]
  norm_num

omit [Fintype ι] [DecidableEq ι] in
theorem hermPart_eq_zero_iff {A : Matrix ι ι 𝕜} : hermPart A = 0 ↔ Aᴴ = -A := by
  rw [← Subtype.coe_inj, coe_hermPart, Submodule.coe_zero, smul_eq_zero]
  constructor
  · rintro (h | h)
    · norm_num at h
    · rw [eq_neg_iff_add_eq_zero, add_comm, h]
  · intro h
    right
    rw [h, add_neg_cancel]

/-- The kernel of the Hermitian part is `𝔲(n)`. -/
theorem ker_hermPart :
    LinearMap.ker (hermPart (𝕜 := 𝕜) (ι := ι)) = (skewHermitian 𝕜 ι).toSubmodule := by
  ext A
  rw [LinearMap.mem_ker, hermPart_eq_zero_iff, mem_skewHermitian_toSubmodule]

omit [Fintype ι] [DecidableEq ι] in
theorem range_hermPart : LinearMap.range (hermPart (𝕜 := 𝕜) (ι := ι)) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨S, hS⟩ -
  exact ⟨S, Subtype.ext (hermPart_of_mem hS)⟩

/-- **`dim 𝔲(n) + dim Herm(n) = dim Mₙ(𝕜)`**. -/
theorem finrank_skewHermitian_add_finrank_hermitian :
    finrank ℝ (skewHermitian 𝕜 ι).toSubmodule + finrank ℝ (hermitian 𝕜 ι) =
      finrank ℝ (Matrix ι ι 𝕜) := by
  have h := LinearMap.finrank_range_add_finrank_ker (hermPart (𝕜 := 𝕜) (ι := ι))
  rw [range_hermPart, finrank_top, ker_hermPart] at h
  omega

end LieAlgebras

/-! ### Matrix groups -/

section MatrixGroup

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {G : Set (Matrix ι ι 𝕜)}

/-- **A compact matrix group with Lie algebra `𝔤`**: the hypotheses on a slice submanifold
`G ⊆ U(n)` of `Mₙ(𝕜)` (modelled on `Z`) and a real Lie algebra `𝔤` of skew-Hermitian matrices
used in Chapter 12.  `G` is closed under products and `ᴴ = ⁻¹`, `𝔤` is invariant under `Ad G`,
`exp 𝔤 ⊆ G`, and `dim G = dim 𝔤`.  (Milnor's §21 works with an abstract Lie group; every compact
Lie group is a closed subgroup of some `U(n)`, by the Peter–Weyl theorem, which is not needed
here: the groups of Part IV are given as matrix groups.) -/
structure IsMatrixGroup (_hG : Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix ι ι 𝕜) Z W G)
    (𝔤 : LieSubalgebra ℝ (Matrix ι ι 𝕜)) : Prop where
  unitary : ∀ g ∈ G, gᴴ * g = 1
  mul_mem : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G
  star_mem : ∀ g ∈ G, gᴴ ∈ G
  skew : ∀ X ∈ 𝔤, Xᴴ = -X
  conj_mem : ∀ g ∈ G, ∀ X ∈ 𝔤, g * X * gᴴ ∈ 𝔤
  exp_mem : ∀ X ∈ 𝔤, NormedSpace.exp X ∈ G
  finrank_eq : finrank ℝ Z = finrank ℝ 𝔤.toSubmodule

namespace IsMatrixGroup

variable {hG : Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix ι ι 𝕜) Z W G}
  {𝔤 : LieSubalgebra ℝ (Matrix ι ι 𝕜)} (h : IsMatrixGroup hG 𝔤)
include h

theorem mul_conjTranspose {g : Matrix ι ι 𝕜} (hg : g ∈ G) : g * gᴴ = 1 :=
  mul_conjTranspose_eq_one (h.unitary g hg)

theorem one_mem : (1 : Matrix ι ι 𝕜) ∈ G := by
  simpa using h.exp_mem 0 (zero_mem _)

theorem exp_smul_mem {X : Matrix ι ι 𝕜} (hX : X ∈ 𝔤) (t : ℝ) : NormedSpace.exp (t • X) ∈ G :=
  h.exp_mem _ (𝔤.smul_mem t hX)

/-- The curve `t ↦ g exp(tX)` lies in `G`. -/
theorem mul_exp_smul_mem {g : Matrix ι ι 𝕜} (hg : g ∈ G) {X : Matrix ι ι 𝕜} (hX : X ∈ 𝔤)
    (t : ℝ) : g * NormedSpace.exp (t • X) ∈ G :=
  h.mul_mem g hg _ (h.exp_smul_mem hX t)

/-- `Ad gᴴ` also preserves `𝔤`. -/
theorem conj_mem' {g : Matrix ι ι 𝕜} (hg : g ∈ G) {X : Matrix ι ι 𝕜} (hX : X ∈ 𝔤) :
    gᴴ * X * g ∈ 𝔤 := by
  simpa using h.conj_mem gᴴ (h.star_mem g hg) X hX

/-- `g·𝔤`, the image of `𝔤` under left translation by a unitary `g`. -/
def leftAlg (g : Matrix ι ι 𝕜) (hg : gᴴ * g = 1) : Submodule ℝ (Matrix ι ι 𝕜) :=
  𝔤.toSubmodule.map ((mulLeftIso g hg).toLinearEquiv : Matrix ι ι 𝕜 →ₗ[ℝ] Matrix ι ι 𝕜)

omit h in
theorem mem_leftAlg_iff {g : Matrix ι ι 𝕜} (hg : gᴴ * g = 1) {v : Matrix ι ι 𝕜} :
    v ∈ leftAlg (𝔤 := 𝔤) g hg ↔ gᴴ * v ∈ 𝔤 := by
  rw [leftAlg, Submodule.mem_map]
  constructor
  · rintro ⟨X, hX, rfl⟩
    change gᴴ * (g * X) ∈ 𝔤
    rwa [← Matrix.mul_assoc, hg, Matrix.one_mul]
  · intro hv
    refine ⟨gᴴ * v, hv, ?_⟩
    change g * (gᴴ * v) = v
    rw [← Matrix.mul_assoc, mul_conjTranspose_eq_one hg, Matrix.one_mul]

omit h in
theorem finrank_leftAlg {g : Matrix ι ι 𝕜} (hg : gᴴ * g = 1) :
    finrank ℝ (leftAlg (𝔤 := 𝔤) g hg) = finrank ℝ 𝔤.toSubmodule :=
  LinearEquiv.finrank_map_eq _ _

variable [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W]

/-- **The tangent space of `G` at `g` is `g·𝔤`** (Milnor p. 125, (6), at `g = I`; at other points by
left translation).  The curves `t ↦ g exp(tX)`, `X ∈ 𝔤`, lie in `G` and have velocity `gX` at
`t = 0`, so `g·𝔤 ⊆ T_gG`; both have dimension `dim 𝔤`. -/
theorem tangentSubspace_eq (g : G) :
    tangentSubspace hG g = leftAlg (𝔤 := 𝔤) g.1 (h.unitary g g.2) := by
  symm
  refine Submodule.eq_of_le_of_finrank_eq (K := ℝ) (V := Matrix ι ι 𝕜) ?_ ?_
  · intro v hv
    rw [mem_leftAlg_iff] at hv
    set X := g.1ᴴ * v with hXdef
    have hvX : v = g.1 * X := by
      rw [hXdef, ← Matrix.mul_assoc, h.mul_conjTranspose g.2, Matrix.one_mul]
    have hc : HasDerivAt (fun t : ℝ => g.1 * NormedSpace.exp (t • X)) (g.1 * X) 0 := by
      have := (hasDerivAt_exp_smul_const X (0 : ℝ)).const_mul g.1
      simpa using this
    have hmem : ∀ᶠ s in 𝓝 (0 : ℝ), g.1 * NormedSpace.exp (s • X) ∈ G :=
      Filter.Eventually.of_forall fun s => h.mul_exp_smul_mem g.2 hv s
    have hT := hasDerivAt_mem_tangentSubspace hG hc hmem
    have hg0 : (⟨g.1 * NormedSpace.exp ((0 : ℝ) • X), hmem.self_of_nhds⟩ : G) = g := by
      ext1; simp
    rw [hg0] at hT
    rw [hvX]
    exact hT
  · have h1 := finrank_tanAt hG g.2
    rw [tanAt_of_mem hG g.2] at h1
    rw [finrank_leftAlg, ← h.finrank_eq]
    exact h1.symm

/-- `v ∈ T_gG ↔ gᴴ v ∈ 𝔤`. -/
theorem mem_tangentSubspace_iff (g : G) {v : Matrix ι ι 𝕜} :
    v ∈ tangentSubspace hG g ↔ g.1ᴴ * v ∈ 𝔤 := by
  rw [h.tangentSubspace_eq, mem_leftAlg_iff]

theorem mul_mem_tangentSubspace (g : G) {X : Matrix ι ι 𝕜} (hX : X ∈ 𝔤) :
    g.1 * X ∈ tangentSubspace hG g := by
  rw [h.mem_tangentSubspace_iff, ← Matrix.mul_assoc, h.unitary g g.2, Matrix.one_mul]
  exact hX

/-- **`T_gG = 𝔤·g`** as well: `Ad g` preserves `𝔤`. -/
theorem mem_tangentSubspace_iff' (g : G) {v : Matrix ι ι 𝕜} :
    v ∈ tangentSubspace hG g ↔ v * g.1ᴴ ∈ 𝔤 := by
  rw [h.mem_tangentSubspace_iff]
  constructor
  · intro hv
    have := h.conj_mem g g.2 _ hv
    rwa [← Matrix.mul_assoc, h.mul_conjTranspose g.2, Matrix.one_mul] at this
  · intro hv
    have := h.conj_mem' g.2 hv
    rwa [Matrix.mul_assoc, Matrix.mul_assoc, h.unitary g g.2, Matrix.mul_one] at this

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **Left translations are isometries preserving `G`** (bi-invariance of the induced metric, the
left half). -/
theorem mulLeftIso_image {g : Matrix ι ι 𝕜} (hg : g ∈ G) :
    mulLeftIso g (h.unitary g hg) '' G = G := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact h.mul_mem g hg y hy
  · intro hx
    refine ⟨gᴴ * x, h.mul_mem _ (h.star_mem g hg) x hx, ?_⟩
    change g * (gᴴ * x) = x
    rw [← Matrix.mul_assoc, h.mul_conjTranspose hg, Matrix.one_mul]

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **Right translations are isometries preserving `G`** (bi-invariance, the right half). -/
theorem mulRightIso_image {g : Matrix ι ι 𝕜} (hg : g ∈ G) :
    mulRightIso g (h.unitary g hg) '' G = G := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact h.mul_mem y hy g hg
  · intro hx
    refine ⟨x * gᴴ, h.mul_mem x hx _ (h.star_mem g hg), ?_⟩
    change x * gᴴ * g = x
    rw [Matrix.mul_assoc, h.unitary g hg, Matrix.mul_one]

end IsMatrixGroup

end MatrixGroup

/-! ### `U(n)` and `O(n)` -/

section Unitary

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mem_unitaryGroup_iff_conjTranspose {A : Matrix ι ι 𝕜} :
    A ∈ unitaryGroup ι 𝕜 ↔ Aᴴ * A = 1 := by
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose]

/-- Milnor's defining map of `U(n)` (p. 125), `A ↦ AᴴA − I`, with values in the Hermitian
matrices. -/
def unitaryMap (A : Matrix ι ι 𝕜) : hermitian 𝕜 ι := hermPart (Aᴴ * A - 1)

theorem conjTranspose_mul_self_sub_one (A : Matrix ι ι 𝕜) : (Aᴴ * A - 1)ᴴ = Aᴴ * A - 1 := by
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_one]

theorem unitaryMap_eq_zero_iff {A : Matrix ι ι 𝕜} : unitaryMap A = 0 ↔ Aᴴ * A = 1 := by
  rw [unitaryMap, ← Subtype.coe_inj, hermPart_of_mem (conjTranspose_mul_self_sub_one A),
    Submodule.coe_zero, sub_eq_zero]

theorem preimage_unitaryMap :
    unitaryMap ⁻¹' {0} = (unitaryGroup ι 𝕜 : Set (Matrix ι ι 𝕜)) := by
  ext A
  rw [Set.mem_preimage, Set.mem_singleton_iff, unitaryMap_eq_zero_iff, SetLike.mem_coe,
    mem_unitaryGroup_iff_conjTranspose]

omit [DecidableEq ι] in
/-- `A ↦ Aᴴ`, as a continuous real-linear map. -/
def conjTransposeCLM : Matrix ι ι 𝕜 →L[ℝ] Matrix ι ι 𝕜 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => Aᴴ
      map_add' := fun A B => conjTranspose_add A B
      map_smul' := fun r A => by rw [conjTranspose_smul, star_trivial]; rfl }

omit [DecidableEq ι] in
@[simp] theorem conjTransposeCLM_apply (A : Matrix ι ι 𝕜) : conjTransposeCLM A = Aᴴ := rfl

/-- The Hermitian part, as a continuous linear map. -/
def hermPartCLM : Matrix ι ι 𝕜 →L[ℝ] hermitian 𝕜 ι := LinearMap.toContinuousLinearMap hermPart

omit [DecidableEq ι] in
@[simp] theorem hermPartCLM_apply (A : Matrix ι ι 𝕜) : hermPartCLM A = hermPart A := rfl

/-- `d(AᴴA)_A(H) = HᴴA + AᴴH`, and the derivative of `A ↦ AᴴA − I`. -/
theorem hasFDerivAt_unitaryMap (A : Matrix ι ι 𝕜) :
    ∃ D : Matrix ι ι 𝕜 →L[ℝ] hermitian 𝕜 ι, HasFDerivAt unitaryMap D A ∧
      ∀ H, D H = hermPart (Hᴴ * A + Aᴴ * H) := by
  have h := ((conjTransposeCLM (𝕜 := 𝕜) (ι := ι)).hasFDerivAt.fun_mul'
    (hasFDerivAt_id A)).sub_const 1
  refine ⟨_, (hermPartCLM (𝕜 := 𝕜) (ι := ι)).hasFDerivAt.comp A h, fun H => ?_⟩
  simp only [ContinuousLinearMap.comp_apply, _root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
    conjTransposeCLM_apply, hermPartCLM_apply]
  rw [add_comm]
  rfl

theorem contDiff_unitaryMap : ContDiff ℝ ∞ (unitaryMap : Matrix ι ι 𝕜 → hermitian 𝕜 ι) := by
  have h : ContDiff ℝ ∞ fun B : Matrix ι ι 𝕜 => conjTransposeCLM B * B - 1 :=
    ((conjTransposeCLM (𝕜 := 𝕜) (ι := ι)).contDiff.mul contDiff_id).sub contDiff_const
  exact (hermPartCLM (𝕜 := 𝕜) (ι := ι)).contDiff.comp h

/-- **`0` is a regular value of `A ↦ AᴴA − I`**: at a unitary `A`, `H = AS/2 ↦ S` for every
Hermitian `S`. -/
theorem isRegularValue_unitaryMap :
    Milnor.IsRegularValue 𝓘(ℝ, Matrix ι ι 𝕜) 𝓘(ℝ, hermitian 𝕜 ι)
      (unitaryMap (𝕜 := 𝕜) (ι := ι)) 0 := by
  intro A hA
  rw [unitaryMap_eq_zero_iff] at hA
  unfold Milnor.IsRegularPoint
  obtain ⟨D, hD, hDH⟩ := hasFDerivAt_unitaryMap A
  have hsurj : Function.Surjective D := by
    rintro ⟨S, hS⟩
    refine ⟨(1 / 2 : ℝ) • (A * S), ?_⟩
    rw [hDH]
    ext1
    rw [mem_hermitian] at hS
    rw [conjTranspose_smul, star_trivial, conjTranspose_mul, hS, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_assoc, hA, Matrix.mul_one, ← Matrix.mul_assoc, hA,
      Matrix.one_mul, ← add_smul, hermPart_of_mem]
    · norm_num
    · rw [conjTranspose_smul, star_trivial, hS]
  rw [mfderiv_eq_fderiv, hD.fderiv]
  exact hsurj

/-- **`U(n)` (and `O(n)` for `𝕜 = ℝ`) is a slice submanifold of `Mₙ(𝕜)`**, modelled on `𝔲(n)`:
a regular level set of `A ↦ AᴴA − I` (Milnor p. 125). -/
theorem isSliceSubmanifold_unitaryGroup :
    Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix ι ι 𝕜) (skewHermitian 𝕜 ι).toSubmodule
      (hermitian 𝕜 ι) (unitaryGroup ι 𝕜 : Set (Matrix ι ι 𝕜)) := by
  have h1 : ContMDiff 𝓘(ℝ, Matrix ι ι 𝕜) 𝓘(ℝ, hermitian 𝕜 ι) ∞ (unitaryMap (𝕜 := 𝕜) (ι := ι)) :=
    contDiff_unitaryMap.contMDiff
  have h := Milnor.isSliceSubmanifold_preimage (Z := (skewHermitian 𝕜 ι).toSubmodule)
    finrank_skewHermitian_add_finrank_hermitian h1 isRegularValue_unitaryMap
  rwa [preimage_unitaryMap] at h

/-- **`U(n)` (resp. `O(n)`) with `𝔲(n)` (resp. `𝔬(n)`) is a matrix group.** -/
theorem isMatrixGroup_unitaryGroup :
    IsMatrixGroup (isSliceSubmanifold_unitaryGroup (𝕜 := 𝕜) (ι := ι)) (skewHermitian 𝕜 ι) where
  unitary g hg := mem_unitaryGroup_iff_conjTranspose.1 hg
  mul_mem g hg h hh := Submonoid.mul_mem _ hg hh
  star_mem g hg := by
    rw [← star_eq_conjTranspose]
    exact Unitary.star_mem hg
  skew X hX := hX
  conj_mem g hg X hX := by
    rw [mem_skewHermitian, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      mem_skewHermitian.1 hX]
    noncomm_ring
  exp_mem X hX := mem_unitaryGroup_iff_conjTranspose.2 (exp_conjTranspose_mul_exp_of_skew hX)
  finrank_eq := rfl

/-- `‖A‖² = n` on `U(n)`. -/
theorem norm_sq_of_conjTranspose_mul_self {A : Matrix ι ι 𝕜} (hA : Aᴴ * A = 1) :
    ‖A‖ ^ 2 = Fintype.card ι := by
  rw [← real_inner_self_eq_norm_sq, inner_def, hA, trace_one]
  simp

theorem isClosed_unitaryGroup : IsClosed (unitaryGroup ι 𝕜 : Set (Matrix ι ι 𝕜)) := by
  have h : (unitaryGroup ι 𝕜 : Set (Matrix ι ι 𝕜)) = {A | Aᴴ * A = 1} := by
    ext A; exact mem_unitaryGroup_iff_conjTranspose
  rw [h]
  exact isClosed_eq (conjTransposeCLM.continuous.mul continuous_id) continuous_const

/-- **`U(n)` is compact** (Milnor p. 124): closed and bounded (`‖A‖² = n`). -/
theorem isCompact_unitaryGroup : IsCompact (unitaryGroup ι 𝕜 : Set (Matrix ι ι 𝕜)) := by
  refine Metric.isCompact_of_isClosed_isBounded isClosed_unitaryGroup ?_
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨Real.sqrt (Fintype.card ι), fun A hA => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have h := norm_sq_of_conjTranspose_mul_self (mem_unitaryGroup_iff_conjTranspose.1 hA)
  rw [← h, Real.sqrt_sq (norm_nonneg A)]

theorem isClosed_det_eq_one : IsClosed {A : Matrix ι ι 𝕜 | det A = 1} :=
  isClosed_eq (contDiff_det.continuous) continuous_const

end Unitary

/-! ### `SO(n)` -/

section SpecialOrthogonal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mem_specialOrthogonalGroup_iff_conjTranspose {A : Matrix ι ι ℝ} :
    A ∈ specialOrthogonalGroup ι ℝ ↔ Aᴴ * A = 1 ∧ det A = 1 := by
  rw [← mem_unitaryGroup_iff_conjTranspose]
  exact Iff.rfl

/-- On `O(n)`, `det = ±1`. -/
theorem det_sq_of_orthogonal {A : Matrix ι ι ℝ} (hA : Aᴴ * A = 1) : det A ^ 2 = 1 := by
  have h := congrArg det hA
  rw [det_mul, det_conjTranspose, star_trivial, det_one] at h
  rw [sq]
  exact h

/-- `SO(n) = O(n) ∩ {det > 0}`. -/
theorem specialOrthogonalGroup_inter :
    (specialOrthogonalGroup ι ℝ : Set (Matrix ι ι ℝ)) ∩ {A | 0 < det A} =
      (unitaryGroup ι ℝ : Set (Matrix ι ι ℝ)) ∩ {A | 0 < det A} := by
  ext A
  simp only [Set.mem_inter_iff, SetLike.mem_coe, Set.mem_ofPred_eq,
    mem_specialOrthogonalGroup_iff_conjTranspose, mem_unitaryGroup_iff_conjTranspose]
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, ?_⟩, h2⟩
    have h := det_sq_of_orthogonal h1
    nlinarith [sq_nonneg (det A - 1), sq_nonneg (det A + 1)]

/-- **`SO(n)` is a slice submanifold of `Mₙ(ℝ)`**: an open piece of `O(n)`. -/
theorem isSliceSubmanifold_specialOrthogonalGroup :
    Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix ι ι ℝ) (skewHermitian ℝ ι).toSubmodule
      (hermitian ℝ ι) (specialOrthogonalGroup ι ℝ : Set (Matrix ι ι ℝ)) := by
  refine Milnor.Problems.FramedOps.isSliceSubmanifold_of_locally_eq fun A hA => ⟨_, {A | 0 < det A},
    isSliceSubmanifold_unitaryGroup, isOpen_lt continuous_const contDiff_det.continuous, ?_,
    specialOrthogonalGroup_inter⟩
  rw [Set.mem_ofPred_eq, (mem_specialOrthogonalGroup_iff_conjTranspose.1 hA).2]
  exact one_pos

/-- **`SO(n)` with `𝔬(n)` is a matrix group.** -/
theorem isMatrixGroup_specialOrthogonalGroup :
    IsMatrixGroup (isSliceSubmanifold_specialOrthogonalGroup (ι := ι)) (skewHermitian ℝ ι) where
  unitary g hg := (mem_specialOrthogonalGroup_iff_conjTranspose.1 hg).1
  mul_mem g hg h hh := Submonoid.mul_mem _ hg hh
  star_mem g hg := by
    obtain ⟨h1, h2⟩ := mem_specialOrthogonalGroup_iff_conjTranspose.1 hg
    refine mem_specialOrthogonalGroup_iff_conjTranspose.2 ⟨?_, ?_⟩
    · rw [conjTranspose_conjTranspose]
      exact mul_conjTranspose_eq_one h1
    · rw [det_conjTranspose, h2, star_one]
  skew X hX := hX
  conj_mem g hg X hX := isMatrixGroup_unitaryGroup.conj_mem g
    (mem_unitaryGroup_iff_conjTranspose.2 (mem_specialOrthogonalGroup_iff_conjTranspose.1 hg).1)
    X hX
  exp_mem X hX := by
    refine mem_specialOrthogonalGroup_iff_conjTranspose.2
      ⟨exp_conjTranspose_mul_exp_of_skew hX, ?_⟩
    simpa using det_exp_smul_of_trace_eq_zero (trace_eq_zero_of_skew_real hX) 1
  finrank_eq := rfl

/-- **`SO(n)` is compact.** -/
theorem isCompact_specialOrthogonalGroup :
    IsCompact (specialOrthogonalGroup ι ℝ : Set (Matrix ι ι ℝ)) := by
  refine isCompact_unitaryGroup.of_isClosed_subset ?_ fun A hA => ?_
  · have : (specialOrthogonalGroup ι ℝ : Set (Matrix ι ι ℝ)) =
        (unitaryGroup ι ℝ : Set (Matrix ι ι ℝ)) ∩ {A | det A = 1} := by
      ext A; exact Iff.rfl
    rw [this]
    exact isClosed_unitaryGroup.inter isClosed_det_eq_one
  · exact hA.1

end SpecialOrthogonal

/-! ### `SU(n)` -/

section SpecialUnitary

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mem_specialUnitaryGroup_iff_conjTranspose {A : Matrix ι ι ℂ} :
    A ∈ specialUnitaryGroup ι ℂ ↔ Aᴴ * A = 1 ∧ det A = 1 := by
  rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff_conjTranspose]

/-- The defining map of `SU(n)` used here: `A ↦ (AᴴA − I, Im det A)`. -/
def suMap (A : Matrix ι ι ℂ) : hermitian ℂ ι × ℝ := (unitaryMap A, (det A).im)

/-- On `U(n)`, `|det A| = 1`. -/
theorem normSq_det_of_unitary {A : Matrix ι ι ℂ} (hA : Aᴴ * A = 1) :
    (det A).re ^ 2 + (det A).im ^ 2 = 1 := by
  have h := congrArg det hA
  rw [det_mul, det_conjTranspose, det_one, Complex.star_def, Complex.conj_mul'] at h
  have h2 := congrArg Complex.re h
  rw [Complex.one_re] at h2
  norm_cast at h2
  rw [Complex.sq_norm, Complex.normSq_apply] at h2
  nlinarith [h2]

/-- **The level set** `{AᴴA = I, Im det A = 0}` is `{AᴴA = I, det A = ±1}`, and `SU(n)` is its open
piece `Re det A > 0`. -/
theorem mem_specialUnitaryGroup_iff_level {A : Matrix ι ι ℂ} :
    A ∈ specialUnitaryGroup ι ℂ ↔ suMap A = 0 ∧ 0 < (det A).re := by
  rw [mem_specialUnitaryGroup_iff_conjTranspose, suMap, Prod.mk_eq_zero, unitaryMap_eq_zero_iff]
  constructor
  · rintro ⟨h1, h2⟩
    rw [h2]
    exact ⟨⟨h1, Complex.one_im⟩, by norm_num⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, Complex.ext ?_ (by rw [h2, Complex.one_im])⟩
    have h := normSq_det_of_unitary h1
    rw [h2] at h
    rw [Complex.one_re]
    nlinarith [sq_nonneg ((det A).re - 1), sq_nonneg ((det A).re + 1)]

theorem contDiff_suMap : ContDiff ℝ ∞ (suMap : Matrix ι ι ℂ → hermitian ℂ ι × ℝ) :=
  contDiff_unitaryMap.prodMk (Complex.imCLM.contDiff.comp contDiff_det)

/-- The linear map `A ↦ (hermPart A, Im tr A)`, whose kernel is `𝔰𝔲(n)`. -/
def suPart : Matrix ι ι ℂ →ₗ[ℝ] hermitian ℂ ι × ℝ :=
  LinearMap.prod hermPart (Complex.imLm.comp (traceLinearMap ι ℝ ℂ))

omit [DecidableEq ι] in
theorem suPart_apply (A : Matrix ι ι ℂ) : suPart A = (hermPart A, (trace A).im) := rfl

omit [DecidableEq ι] in
/-- The trace of a Hermitian matrix is real. -/
theorem im_trace_of_hermitian {S : Matrix ι ι ℂ} (hS : Sᴴ = S) : (trace S).im = 0 := by
  have h := congrArg trace hS
  rw [trace_conjTranspose, Complex.star_def] at h
  exact Complex.conj_eq_iff_im.1 h

omit [DecidableEq ι] in
/-- The trace of a skew-Hermitian matrix is imaginary. -/
theorem re_trace_of_skew {X : Matrix ι ι ℂ} (hX : Xᴴ = -X) : (trace X).re = 0 := by
  have h := congrArg (fun A => (trace A).re) hX
  simp only [trace_conjTranspose, Complex.star_def, Complex.conj_re, trace_neg, Complex.neg_re]
    at h
  linarith

theorem ker_suPart : LinearMap.ker (suPart (ι := ι)) = (specialSkewHermitian ι).toSubmodule := by
  ext A
  rw [LinearMap.mem_ker, suPart_apply, Prod.mk_eq_zero, hermPart_eq_zero_iff,
    mem_specialSkewHermitian_toSubmodule]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, Complex.ext (re_trace_of_skew h1) h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h2, Complex.zero_im]⟩

omit [DecidableEq ι] in
theorem range_suPart [Nonempty ι] : LinearMap.range (suPart (ι := ι)) = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro ⟨⟨S, hS⟩, c⟩ -
  have hn : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨S + ((c / Fintype.card ι : ℝ) : ℂ) • (Complex.I • (1 : Matrix ι ι ℂ)), ?_⟩
  rw [suPart_apply, map_add]
  have hskew : (((c / Fintype.card ι : ℝ) : ℂ) • (Complex.I • (1 : Matrix ι ι ℂ)))ᴴ =
      -(((c / Fintype.card ι : ℝ) : ℂ) • (Complex.I • (1 : Matrix ι ι ℂ))) := by
    rw [conjTranspose_smul, conjTranspose_smul, conjTranspose_one]
    simp only [Complex.star_def, Complex.conj_ofReal, Complex.conj_I, neg_smul, smul_neg]
  rw [(hermPart_eq_zero_iff).2 hskew, add_zero, trace_add, Complex.add_im,
    im_trace_of_hermitian hS, zero_add, trace_smul, trace_smul, trace_one]
  refine Prod.ext (Subtype.ext (hermPart_of_mem hS)) ?_
  simp only [smul_eq_mul, Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.natCast_re,
    Complex.I_im, Complex.natCast_im, Complex.ofReal_im]
  field_simp
  ring

/-- **`dim 𝔰𝔲(n) + dim Herm(n) + 1 = dim Mₙ(ℂ)`** (`n ≥ 1`). -/
theorem finrank_specialSkewHermitian_add [Nonempty ι] :
    finrank ℝ (specialSkewHermitian ι).toSubmodule + finrank ℝ (hermitian ℂ ι × ℝ) =
      finrank ℝ (Matrix ι ι ℂ) := by
  have h := LinearMap.finrank_range_add_finrank_ker (suPart (ι := ι))
  rw [range_suPart, finrank_top, ker_suPart] at h
  omega

/-- The derivative of `suMap`. -/
theorem hasFDerivAt_suMap (A : Matrix ι ι ℂ) :
    ∃ D : Matrix ι ι ℂ →L[ℝ] hermitian ℂ ι × ℝ, HasFDerivAt suMap D A ∧
      ∀ H, D H = (hermPart (Hᴴ * A + Aᴴ * H), (fderiv ℝ det A H).im) := by
  obtain ⟨D₁, hD₁, hD₁H⟩ := hasFDerivAt_unitaryMap A
  have hdet : HasFDerivAt det (fderiv ℝ det A) A :=
    (contDiff_det.differentiable (by simp) A).hasFDerivAt
  refine ⟨_, hD₁.prodMk (Complex.imCLM.hasFDerivAt.comp A hdet), fun H => ?_⟩
  simp only [ContinuousLinearMap.prod_apply, hD₁H, ContinuousLinearMap.comp_apply,
    Complex.imCLM_apply]

/-- **`0` is a regular value of `A ↦ (AᴴA − I, Im det A)`**: at a point of the level set
(`A` unitary, `det A = δ = ±1`), `H = A(S/2 + (cδ/n) iI) ↦ (S, c)`, by Jacobi's formula
`d(det)_A(AY) = det A · tr Y`. -/
theorem isRegularValue_suMap [Nonempty ι] :
    Milnor.IsRegularValue 𝓘(ℝ, Matrix ι ι ℂ) 𝓘(ℝ, hermitian ℂ ι × ℝ) (suMap (ι := ι)) 0 := by
  intro A hA
  rw [suMap, Prod.mk_eq_zero, unitaryMap_eq_zero_iff] at hA
  obtain ⟨hU, him⟩ := hA
  have hδ : (det A).re ^ 2 = 1 := by have := normSq_det_of_unitary hU; rw [him] at this; linarith
  have hdetA : det A = ((det A).re : ℂ) := Complex.ext rfl (by rw [him, Complex.ofReal_im])
  unfold Milnor.IsRegularPoint
  obtain ⟨D, hD, hDH⟩ := hasFDerivAt_suMap A
  have hn : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hsurj : Function.Surjective D := by
    rintro ⟨⟨S, hS⟩, c⟩
    rw [mem_hermitian] at hS
    set r : ℝ := c * (det A).re / Fintype.card ι with hr
    set Y : Matrix ι ι ℂ := (1 / 2 : ℝ) • S + (r : ℂ) • (Complex.I • (1 : Matrix ι ι ℂ)) with hY
    have hYH : Yᴴ = (1 / 2 : ℝ) • S - (r : ℂ) • (Complex.I • (1 : Matrix ι ι ℂ)) := by
      rw [hY, conjTranspose_add, conjTranspose_smul, conjTranspose_smul, conjTranspose_smul,
        conjTranspose_one, star_trivial, hS]
      simp only [Complex.star_def, Complex.conj_ofReal, Complex.conj_I, neg_smul, smul_neg,
        sub_eq_add_neg]
    refine ⟨A * Y, ?_⟩
    rw [hDH, fderiv_det_mul]
    refine Prod.ext (Subtype.ext ?_) ?_
    · rw [conjTranspose_mul, Matrix.mul_assoc, hU, Matrix.mul_one, ← Matrix.mul_assoc, hU,
        Matrix.one_mul, hYH, hY]
      have h2 : (1 / 2 : ℝ) • S - (r : ℂ) • (Complex.I • (1 : Matrix ι ι ℂ)) +
          ((1 / 2 : ℝ) • S + (r : ℂ) • (Complex.I • 1)) = (1 / 2 : ℝ) • S + (1 / 2 : ℝ) • S := by
        abel
      rw [h2, ← add_smul, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, one_smul]
      exact hermPart_of_mem hS
    · change (det A * trace Y).im = c
      rw [hY, trace_add, trace_smul, trace_smul, trace_smul, trace_one, hdetA]
      have hS0 := im_trace_of_hermitian hS
      simp only [Complex.real_smul, smul_eq_mul, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.natCast_re, Complex.natCast_im, hS0]
      simp only [mul_zero, zero_mul, add_zero, zero_add, one_mul, sub_zero]
      rw [hr]
      field_simp
      linear_combination c * hδ
  rw [mfderiv_eq_fderiv, hD.fderiv]
  exact hsurj

/-- **`SU(n)` is a slice submanifold of `Mₙ(ℂ)`** (`n ≥ 1`), modelled on `𝔰𝔲(n)`: the open piece
`Re det > 0` of the regular level set `{AᴴA = I, Im det A = 0}`. -/
theorem isSliceSubmanifold_specialUnitaryGroup [Nonempty ι] :
    Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix ι ι ℂ) (specialSkewHermitian ι).toSubmodule
      (hermitian ℂ ι × ℝ) (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) := by
  have h1 : ContMDiff 𝓘(ℝ, Matrix ι ι ℂ) 𝓘(ℝ, hermitian ℂ ι × ℝ) ∞ (suMap (ι := ι)) :=
    contDiff_suMap.contMDiff
  have hT := Milnor.isSliceSubmanifold_preimage (Z := (specialSkewHermitian ι).toSubmodule)
    finrank_specialSkewHermitian_add h1 isRegularValue_suMap
  refine Milnor.Problems.FramedOps.isSliceSubmanifold_of_locally_eq fun A hA =>
    ⟨_, {A | 0 < (det A).re}, hT,
    isOpen_lt continuous_const (Complex.continuous_re.comp contDiff_det.continuous), ?_, ?_⟩
  · exact (mem_specialUnitaryGroup_iff_level.1 hA).2
  · ext B
    simp only [Set.mem_inter_iff, SetLike.mem_coe, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_ofPred_eq, mem_specialUnitaryGroup_iff_level]
    tauto

/-- **`SU(n)` with `𝔰𝔲(n)` is a matrix group** (`n ≥ 1`). -/
theorem isMatrixGroup_specialUnitaryGroup [Nonempty ι] :
    IsMatrixGroup (isSliceSubmanifold_specialUnitaryGroup (ι := ι)) (specialSkewHermitian ι) where
  unitary g hg := (mem_specialUnitaryGroup_iff_conjTranspose.1 hg).1
  mul_mem g hg h hh := Submonoid.mul_mem _ hg hh
  star_mem g hg := by
    obtain ⟨h1, h2⟩ := mem_specialUnitaryGroup_iff_conjTranspose.1 hg
    refine mem_specialUnitaryGroup_iff_conjTranspose.2 ⟨?_, ?_⟩
    · rw [conjTranspose_conjTranspose]
      exact mul_conjTranspose_eq_one h1
    · rw [det_conjTranspose, h2, star_one]
  skew X hX := hX.1
  conj_mem g hg X hX := by
    refine ⟨isMatrixGroup_unitaryGroup.conj_mem g (mem_unitaryGroup_iff_conjTranspose.2
      (mem_specialUnitaryGroup_iff_conjTranspose.1 hg).1) X hX.1, ?_⟩
    rw [trace_mul_comm, ← Matrix.mul_assoc, (mem_specialUnitaryGroup_iff_conjTranspose.1 hg).1,
      Matrix.one_mul]
    exact hX.2
  exp_mem X hX := by
    refine mem_specialUnitaryGroup_iff_conjTranspose.2
      ⟨exp_conjTranspose_mul_exp_of_skew hX.1, ?_⟩
    simpa using det_exp_smul_of_trace_eq_zero hX.2 1
  finrank_eq := rfl

/-- **`SU(n)` is compact.** -/
theorem isCompact_specialUnitaryGroup :
    IsCompact (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) := by
  refine isCompact_unitaryGroup.of_isClosed_subset ?_ fun A hA => hA.1
  have : (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) =
      (unitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) ∩ {A | det A = 1} := by
    ext A; exact Iff.rfl
  rw [this]
  exact isClosed_unitaryGroup.inter isClosed_det_eq_one

end SpecialUnitary

end Morse
