import Mathlib
import Morse.Homotopy.Homogeneous

/-!
# Stiefel manifolds and the bundles `V_{k}(𝕜ⁿ) → V_j(𝕜ⁿ)`

Milnor, *Morse Theory*, §23, pp. 128–129: "for each `m` there exists a fibration
`U(m) → U(m+1) → S^{2m+1}`", and "the complex Stiefel manifold is defined to be the coset space
`U(2m)/U(m)`" (both quoted from Steenrod, *The Topology of Fibre Bundles*, pp. 35, 90 and §7). The
orthogonal analogues are used in §24. This file proves the local triviality of all these bundles
at once, for `𝕜 = ℝ` or `ℂ`.

## The model

`Morse.Homotopy.Stiefel 𝕜 ι κ` is the set of `ι × κ` matrices `F` with `Fᴴ F = 1`, i.e. the
orthonormal `κ`-frames (the columns of `F`) in `𝕜^ι`, with the subspace topology. For `κ = ι` it
is the unitary group `U(ι)` (`O(ι)` for `𝕜 = ℝ`); for `κ` a point it is the unit sphere of `𝕜^ι`;
for `ι = Fin (2m)`, `κ = Fin m` it is Milnor's complex Stiefel manifold `U(2m)/U(m)` (the frame
`F` corresponds to the coset `g U(m)` of any unitary `g` whose last `m` columns are `F`). The group
`U(ι)` acts on the left, `g • F = g F`.

## The bundles

Split the coordinates as `ι = ι₁ ⊕ κ` and let `F₀ = (0; I)` (`Morse.Homotopy.baseFrame`), the
last `|κ|` standard basis vectors. Two maps are considered:

* the restriction of a frame to its last `|κ₂|` vectors,
  `Stiefel (ι₁ ⊕ κ₂) (κ₁ ⊕ κ₂) → Stiefel (ι₁ ⊕ κ₂) κ₂` (`Morse.Homotopy.stiefelRestrict`),
  with fibre `Stiefel ι₁ κ₁` over `F₀`, included by `A ↦ diag(A, I)`
  (`Morse.Homotopy.stiefelRestrict_locallyTrivial`);
* the orbit map `U(ι₁ ⊕ κ) → Stiefel (ι₁ ⊕ κ) κ`, `g ↦ g F₀` (the last `|κ|` columns of `g`),
  with fibre `U(ι₁)` included by `S ↦ diag(S, I)`, Milnor's embedding
  (`Morse.Homotopy.unitaryOrbit_locallyTrivial`).

For `κ` a point these are `V_{k+1}(𝕜^{n+1}) → S` and `U(m+1) → S^{2m+1}` (`O(m+1) → Sᵐ`); for
`ι₁ = κ = Fin m` the second is Milnor's `U(m) → U(2m) → U(2m)/U(m)`.

## The local section

Both are instances of `Morse.Homotopy.exists_triv_of_orbitSection`: `U(ι)` acts transitively
(an orthonormal frame extends to an orthonormal basis,
`Morse.Homotopy.exists_unitary_smul_baseFrame`), and near `F₀` the orbit map has an explicit
continuous section, a matrix version of the rotation taking one unit vector to another. Write a
frame as `F = (W; C)` with `W` its first `|ι₁|` rows and `C` the last `|κ|` rows, so that
`WᴴW + CᴴC = I`. Where `I + C` is invertible (a neighbourhood of `F₀`, where `C = I`),
`s(F) = [[I − W(I + Cᴴ)⁻¹Wᴴ, W], [−(I + C)(I + Cᴴ)⁻¹Wᴴ, C]]`
is unitary (`Morse.Homotopy.secMat_mem_unitaryGroup`) and its last `|κ|` columns are `F`. For one
column (`C = c` a scalar) this is the unitary map of the plane spanned by `e` and `F` sending `e` to
`F`, with determinant `(1 + c)/(1 + c̄)`. Unitarity reduces to the identities
`(I + C)⁻¹(WᴴW + (I + Cᴴ)C) = I` and
`(I + C)⁻¹(WᴴW + (I + Cᴴ)(I + C))(I + Cᴴ)⁻¹ = (I + C)⁻¹ + (I + Cᴴ)⁻¹`,
both consequences of `WᴴW = I − CᴴC`.
-/

open Matrix Set Function Topology

noncomputable section

namespace Morse.Homotopy

section Definition

variable (𝕜 : Type*) [RCLike 𝕜] (ι κ : Type*) [Fintype ι] [DecidableEq κ]

/-- **The Stiefel manifold** of orthonormal `κ`-frames in `𝕜^ι`: the `ι × κ` matrices with
`Fᴴ F = 1` (orthonormal columns), with the subspace topology. -/
def Stiefel : Set (Matrix ι κ 𝕜) := {F | Fᴴ * F = 1}

variable {𝕜 ι κ}

theorem mem_stiefel {F : Matrix ι κ 𝕜} : F ∈ Stiefel 𝕜 ι κ ↔ Fᴴ * F = 1 := Iff.rfl

end Definition

variable {𝕜 : Type*} [RCLike 𝕜]

section Action

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

/-- The unitary group `U(ι)` is the Stiefel manifold of `ι`-frames in `𝕜^ι`. -/
theorem coe_unitaryGroup_eq_stiefel : (unitaryGroup ι 𝕜 : Set (Matrix ι ι 𝕜)) = Stiefel 𝕜 ι ι := by
  ext g
  rw [SetLike.mem_coe, mem_unitaryGroup_iff', star_eq_conjTranspose]
  rfl

theorem mul_mem_stiefel {g : Matrix ι ι 𝕜} (hg : g ∈ unitaryGroup ι 𝕜) {F : Matrix ι κ 𝕜}
    (hF : F ∈ Stiefel 𝕜 ι κ) : g * F ∈ Stiefel 𝕜 ι κ := by
  have hg' : gᴴ * g = 1 := by rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.1 hg
  change (g * F)ᴴ * (g * F) = 1
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', Matrix.one_mul]
  exact hF

/-- `U(ι)` acts on frames by left multiplication. -/
instance : MulAction (unitaryGroup ι 𝕜) (Stiefel 𝕜 ι κ) where
  smul g F := ⟨(g : Matrix ι ι 𝕜) * (F : Matrix ι κ 𝕜), mul_mem_stiefel g.2 F.2⟩
  one_smul _ := Subtype.ext (Matrix.one_mul _)
  mul_smul _ _ _ := Subtype.ext (Matrix.mul_assoc _ _ _)

@[simp]
theorem coe_smul_stiefel (g : unitaryGroup ι 𝕜) (F : Stiefel 𝕜 ι κ) :
    ((g • F : Stiefel 𝕜 ι κ) : Matrix ι κ 𝕜) = (g : Matrix ι ι 𝕜) * (F : Matrix ι κ 𝕜) :=
  rfl

instance : ContinuousSMul (unitaryGroup ι 𝕜) (Stiefel 𝕜 ι κ) where
  continuous_smul := by
    change Continuous fun q : unitaryGroup ι 𝕜 × Stiefel 𝕜 ι κ =>
      (⟨(q.1 : Matrix ι ι 𝕜) * (q.2 : Matrix ι κ 𝕜), mul_mem_stiefel q.1.2 q.2.2⟩ : Stiefel 𝕜 ι κ)
    exact Continuous.subtype_mk ((continuous_subtype_val.comp continuous_fst).matrix_mul
      (continuous_subtype_val.comp continuous_snd)) _

end Action

/-! ### The base frame and the local section -/

section Section

variable {ι₁ κ : Type*} [Fintype ι₁] [Fintype κ] [DecidableEq ι₁] [DecidableEq κ]

/-- The base frame `F₀ = (0; I)`: the last `|κ|` standard basis vectors of `𝕜^{ι₁ ⊕ κ}`. -/
def baseFrame : Matrix (ι₁ ⊕ κ) κ 𝕜 := fromRows 0 1

omit [DecidableEq ι₁] [DecidableEq κ] in
theorem conjTranspose_mul_self_fromRows (W : Matrix ι₁ κ 𝕜) (C : Matrix κ κ 𝕜) :
    (fromRows W C)ᴴ * fromRows W C = Wᴴ * W + Cᴴ * C := by
  rw [conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows]

omit [DecidableEq ι₁] in
theorem baseFrame_mem : (baseFrame : Matrix (ι₁ ⊕ κ) κ 𝕜) ∈ Stiefel 𝕜 (ι₁ ⊕ κ) κ := by
  rw [mem_stiefel, baseFrame, conjTranspose_mul_self_fromRows]
  simp

/-- The base point `F₀` of `Stiefel (ι₁ ⊕ κ) κ`. -/
def stiefelBase : Stiefel 𝕜 (ι₁ ⊕ κ) κ := ⟨baseFrame, baseFrame_mem⟩

omit [DecidableEq ι₁] in
theorem stiefel_blocks {F : Matrix (ι₁ ⊕ κ) κ 𝕜} (hF : F ∈ Stiefel 𝕜 (ι₁ ⊕ κ) κ) :
    F.toRows₁ᴴ * F.toRows₁ + F.toRows₂ᴴ * F.toRows₂ = 1 := by
  rw [← conjTranspose_mul_self_fromRows, fromRows_toRows]
  exact hF

/-- **The local section near `F₀`** (as a matrix):
`s(F) = [[I − W(I + Cᴴ)⁻¹Wᴴ, W], [−(I + C)(I + Cᴴ)⁻¹Wᴴ, C]]` for `F = (W; C)`. -/
def secMat (F : Matrix (ι₁ ⊕ κ) κ 𝕜) : Matrix (ι₁ ⊕ κ) (ι₁ ⊕ κ) 𝕜 :=
  fromBlocks (1 - F.toRows₁ * (1 + F.toRows₂ᴴ)⁻¹ * F.toRows₁ᴴ) F.toRows₁
    (-((1 + F.toRows₂) * (1 + F.toRows₂ᴴ)⁻¹ * F.toRows₁ᴴ)) F.toRows₂

/-- The last `|κ|` columns of `s(F)` are `F`. -/
theorem secMat_mul_baseFrame (F : Matrix (ι₁ ⊕ κ) κ 𝕜) :
    secMat F * (baseFrame : Matrix (ι₁ ⊕ κ) κ 𝕜) = F := by
  rw [secMat, baseFrame, fromBlocks_mul_fromRows]
  simp only [Matrix.mul_zero, Matrix.mul_one, zero_add]
  exact fromRows_toRows F

/-- The block identities behind the unitarity of `s(F)`: `s(F)ᴴ s(F) = I` when `WᴴW + CᴴC = I`
and `I + C` is invertible. -/
theorem secMat_unitary_aux (W : Matrix ι₁ κ 𝕜) (C : Matrix κ κ 𝕜)
    (hWC : Wᴴ * W + Cᴴ * C = 1) (hC : IsUnit (1 + C).det) :
    (fromBlocks (1 - W * (1 + Cᴴ)⁻¹ * Wᴴ) W (-((1 + C) * (1 + Cᴴ)⁻¹ * Wᴴ)) C)ᴴ *
      fromBlocks (1 - W * (1 + Cᴴ)⁻¹ * Wᴴ) W (-((1 + C) * (1 + Cᴴ)⁻¹ * Wᴴ)) C = 1 := by
  set M := (1 + Cᴴ)⁻¹ with hMdef
  set N := (1 + C)⁻¹ with hNdef
  have hCt : IsUnit (1 + Cᴴ).det := by
    rw [show (1 + Cᴴ) = (1 + C)ᴴ by simp, det_conjTranspose]
    exact hC.star
  have hMN : Mᴴ = N := by
    rw [hMdef, conjTranspose_nonsing_inv, conjTranspose_add, conjTranspose_one,
      conjTranspose_conjTranspose]
  have hN : N * (1 + C) = 1 := nonsing_inv_mul _ hC
  have hM : (1 + Cᴴ) * M = 1 := mul_nonsing_inv _ hCt
  have hW : Wᴴ * W = 1 - Cᴴ * C := eq_sub_of_add_eq hWC
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one]
  simp only [conjTranspose_sub, conjTranspose_one, conjTranspose_mul, conjTranspose_neg,
    conjTranspose_conjTranspose, hMN, conjTranspose_add]
  congr 1
  · -- the `(ι₁, ι₁)` block
    have key : N * (Wᴴ * W + (1 + Cᴴ) * (1 + C)) * M = M + N := by
      rw [hW]
      calc N * (1 - Cᴴ * C + (1 + Cᴴ) * (1 + C)) * M
          = N * (1 + C) * M + N * ((1 + Cᴴ) * M) := by noncomm_ring
        _ = M + N := by rw [hN, hM, Matrix.one_mul, Matrix.mul_one]
    trans 1 - W * M * Wᴴ - W * N * Wᴴ + W * (N * (Wᴴ * W + (1 + Cᴴ) * (1 + C)) * M) * Wᴴ
    · simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.add_mul,
        Matrix.neg_mul, Matrix.mul_neg, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
      abel
    · rw [key]
      simp only [Matrix.mul_add, Matrix.add_mul]
      abel
  · -- the `(ι₁, κ)` block
    have key : N * (Wᴴ * W + (1 + Cᴴ) * C) = 1 := by
      rw [hW, show 1 - Cᴴ * C + (1 + Cᴴ) * C = 1 + C by noncomm_ring, hN]
    trans W - W * (N * (Wᴴ * W + (1 + Cᴴ) * C))
    · simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.neg_mul,
        Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
      abel
    · rw [key, Matrix.mul_one, sub_self]
  · -- the `(κ, ι₁)` block
    have key : (Wᴴ * W + Cᴴ * (1 + C)) * M = 1 := by
      rw [hW, show 1 - Cᴴ * C + Cᴴ * (1 + C) = 1 + Cᴴ by noncomm_ring, hM]
    trans Wᴴ - (Wᴴ * W + Cᴴ * (1 + C)) * M * Wᴴ
    · simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_neg, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
      abel
    · rw [key, Matrix.one_mul, sub_self]

/-- **`s(F)` is unitary** for an orthonormal frame `F` with `I + C` invertible. -/
theorem secMat_mem_unitaryGroup {F : Matrix (ι₁ ⊕ κ) κ 𝕜} (hF : F ∈ Stiefel 𝕜 (ι₁ ⊕ κ) κ)
    (hC : IsUnit (1 + F.toRows₂).det) : secMat F ∈ unitaryGroup (ι₁ ⊕ κ) 𝕜 := by
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose]
  exact secMat_unitary_aux _ _ (stiefel_blocks hF) hC

theorem continuous_toRows₁ {m₁ m₂ n : Type*} :
    Continuous (toRows₁ : Matrix (m₁ ⊕ m₂) n 𝕜 → Matrix m₁ n 𝕜) :=
  continuous_matrix fun i j => (continuous_apply j).comp (continuous_apply (Sum.inl i))

theorem continuous_toRows₂ {m₁ m₂ n : Type*} :
    Continuous (toRows₂ : Matrix (m₁ ⊕ m₂) n 𝕜 → Matrix m₂ n 𝕜) :=
  continuous_matrix fun i j => (continuous_apply j).comp (continuous_apply (Sum.inr i))

variable (𝕜 ι₁ κ) in
/-- The domain of the local section: frames whose last block `C` has `I + C` invertible. -/
def secDomain : Set (Stiefel 𝕜 (ι₁ ⊕ κ) κ) := {F | IsUnit (1 + F.1.toRows₂).det}

omit [DecidableEq ι₁] in
theorem isOpen_secDomain : IsOpen (secDomain 𝕜 ι₁ κ) := by
  have hc : Continuous fun F : Stiefel 𝕜 (ι₁ ⊕ κ) κ => (1 + F.1.toRows₂).det := by
    exact Continuous.matrix_det (continuous_const.add
      (continuous_toRows₂.comp continuous_subtype_val))
  have : secDomain 𝕜 ι₁ κ = (fun F : Stiefel 𝕜 (ι₁ ⊕ κ) κ => (1 + F.1.toRows₂).det) ⁻¹' {0}ᶜ := by
    ext F
    simp [secDomain, isUnit_iff_ne_zero]
  rw [this]
  exact isOpen_compl_singleton.preimage hc

omit [DecidableEq ι₁] in
theorem stiefelBase_mem_secDomain : (stiefelBase : Stiefel 𝕜 (ι₁ ⊕ κ) κ) ∈ secDomain 𝕜 ι₁ κ := by
  change IsUnit (1 + (fromRows (0 : Matrix ι₁ κ 𝕜) 1).toRows₂).det
  rw [toRows₂_fromRows, isUnit_iff_ne_zero, ← two_smul 𝕜 (1 : Matrix κ κ 𝕜),
    det_smul, det_one, mul_one]
  exact pow_ne_zero _ two_ne_zero

omit [Fintype ι₁] in
/-- `s` is continuous at every frame with `I + C` invertible. -/
theorem continuousAt_secMat {F : Matrix (ι₁ ⊕ κ) κ 𝕜} (hC : IsUnit (1 + F.toRows₂).det) :
    ContinuousAt secMat F := by
  have hCt : IsUnit (1 + F.toRows₂ᴴ).det := by
    rw [show (1 + F.toRows₂ᴴ) = (1 + F.toRows₂)ᴴ by simp, det_conjTranspose]
    exact hC.star
  have hinv : ContinuousAt (fun F : Matrix (ι₁ ⊕ κ) κ 𝕜 => (1 + F.toRows₂ᴴ)⁻¹) F := by
    have h1 : Continuous fun F : Matrix (ι₁ ⊕ κ) κ 𝕜 => 1 + F.toRows₂ᴴ :=
      continuous_const.add continuous_toRows₂.matrix_conjTranspose
    exact (continuousAt_matrix_inv _ (NormedRing.inverse_continuousAt hCt.unit)).comp
      (f := fun F : Matrix (ι₁ ⊕ κ) κ 𝕜 => 1 + F.toRows₂ᴴ) h1.continuousAt
  let Φ : Matrix (ι₁ ⊕ κ) κ 𝕜 × Matrix κ κ 𝕜 → Matrix (ι₁ ⊕ κ) (ι₁ ⊕ κ) 𝕜 := fun q =>
    fromBlocks (1 - q.1.toRows₁ * q.2 * q.1.toRows₁ᴴ) q.1.toRows₁
      (-((1 + q.1.toRows₂) * q.2 * q.1.toRows₁ᴴ)) q.1.toRows₂
  have hΦ : Continuous Φ := by
    have h1 : Continuous fun q : Matrix (ι₁ ⊕ κ) κ 𝕜 × Matrix κ κ 𝕜 => q.1.toRows₁ :=
      continuous_toRows₁.comp continuous_fst
    have h2 : Continuous fun q : Matrix (ι₁ ⊕ κ) κ 𝕜 × Matrix κ κ 𝕜 => q.1.toRows₂ :=
      continuous_toRows₂.comp continuous_fst
    refine Continuous.matrix_fromBlocks ?_ h1 ?_ h2
    · exact continuous_const.sub ((h1.matrix_mul continuous_snd).matrix_mul
        h1.matrix_conjTranspose)
    · exact (((continuous_const.add h2).matrix_mul continuous_snd).matrix_mul
        h1.matrix_conjTranspose).neg
  change ContinuousAt (fun F => Φ (F, (1 + F.toRows₂ᴴ)⁻¹)) F
  exact ContinuousAt.comp (g := Φ) hΦ.continuousAt (continuousAt_id.prodMk hinv)

/-- **The local section of the orbit map `g ↦ g • F₀`** over `secDomain`, a neighbourhood of
`F₀`. -/
def localSection (F : secDomain 𝕜 ι₁ κ) : unitaryGroup (ι₁ ⊕ κ) 𝕜 :=
  ⟨secMat (F.1 : Matrix (ι₁ ⊕ κ) κ 𝕜), secMat_mem_unitaryGroup F.1.2 F.2⟩

theorem continuous_localSection :
    Continuous (localSection : secDomain 𝕜 ι₁ κ → unitaryGroup (ι₁ ⊕ κ) 𝕜) := by
  refine Continuous.subtype_mk (continuous_iff_continuousAt.2 fun F => ?_) _
  exact (continuousAt_secMat F.2).comp (f := fun F : secDomain 𝕜 ι₁ κ => F.1.1)
    (continuous_subtype_val.comp continuous_subtype_val).continuousAt

theorem localSection_smul (F : secDomain 𝕜 ι₁ κ) :
    localSection F • (stiefelBase : Stiefel 𝕜 (ι₁ ⊕ κ) κ) = F :=
  Subtype.ext (secMat_mul_baseFrame _)

end Section

/-! ### Transitivity -/

section Transitive

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype κ] [DecidableEq ι] in
/-- The columns of a matrix with orthonormal columns are orthonormal in `EuclideanSpace`. -/
theorem orthonormal_cols {F : Matrix ι κ 𝕜} (hF : F ∈ Stiefel 𝕜 ι κ) :
    Orthonormal 𝕜 fun k => WithLp.toLp 2 (fun i => F i k) := by
  rw [orthonormal_iff_ite]
  intro j k
  have := congrFun (congrFun hF j) k
  simp only [mul_apply, conjTranspose_apply, one_apply] at this
  rw [← this, PiLp.inner_apply]
  simp [RCLike.inner_apply, mul_comm]

/-- **`U(ι)` acts transitively on orthonormal frames**: every orthonormal frame `F` is the last
`|κ|` columns of a unitary matrix (an orthonormal family extends to an orthonormal basis). -/
theorem exists_unitary_smul_baseFrame {ι₁ : Type*} [Fintype ι₁] [DecidableEq ι₁]
    (F : Stiefel 𝕜 (ι₁ ⊕ κ) κ) :
    ∃ g : unitaryGroup (ι₁ ⊕ κ) 𝕜, g • (stiefelBase : Stiefel 𝕜 (ι₁ ⊕ κ) κ) = F := by
  classical
  let E := EuclideanSpace 𝕜 (ι₁ ⊕ κ)
  let v : ι₁ ⊕ κ → E := Sum.elim 0 fun k => WithLp.toLp 2 (fun i => (F : Matrix _ _ 𝕜) i k)
  have hv : Orthonormal 𝕜 ((Set.range Sum.inr).domRestrict v) := by
    have h := orthonormal_cols F.2
    rw [orthonormal_iff_ite] at h ⊢
    rintro ⟨_, k, rfl⟩ ⟨_, l, rfl⟩
    simp only [Set.domRestrict_apply, v, Sum.elim_inr, h k l]
    by_cases hkl : k = l
    · subst hkl; simp
    · rw [if_neg hkl, if_neg]
      intro h'
      exact hkl (Sum.inr_injective (congrArg Subtype.val h'))
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp [E, finrank_euclideanSpace])
  refine ⟨⟨_, (EuclideanSpace.basisFun (ι₁ ⊕ κ) 𝕜).toMatrix_orthonormalBasis_mem_unitary b⟩, ?_⟩
  apply Subtype.ext
  ext i k
  simp only [coe_smul_stiefel, stiefelBase, baseFrame, mul_apply]
  rw [Fintype.sum_sum_type]
  simp only [fromRows_apply_inl, fromRows_apply_inr, Matrix.zero_apply, mul_zero,
    Finset.sum_const_zero, zero_add, one_apply, mul_ite, mul_one, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr, hb (Sum.inr k) ⟨k, rfl⟩]
  simp [v]

end Transitive

/-! ### The bundles -/

section Bundles

variable {ι₁ κ₁ κ₂ : Type*} [Fintype ι₁] [Fintype κ₁] [Fintype κ₂] [DecidableEq ι₁]
  [DecidableEq κ₁] [DecidableEq κ₂]

omit [Fintype κ₁] [Fintype κ₂] in
theorem toCols₂_mem_stiefel {ι : Type*} [Fintype ι] {F : Matrix ι (κ₁ ⊕ κ₂) 𝕜}
    (hF : F ∈ Stiefel 𝕜 ι (κ₁ ⊕ κ₂)) : F.toCols₂ ∈ Stiefel 𝕜 ι κ₂ := by
  ext j k
  have := congrFun (congrFun hF (Sum.inr j)) (Sum.inr k)
  simpa [mul_apply, toCols₂, one_apply] using this

variable (𝕜 ι₁ κ₁ κ₂) in
/-- **Restriction of a frame to its last `|κ₂|` vectors**,
`Stiefel (ι₁ ⊕ κ₂) (κ₁ ⊕ κ₂) → Stiefel (ι₁ ⊕ κ₂) κ₂`. -/
def stiefelRestrict (F : Stiefel 𝕜 (ι₁ ⊕ κ₂) (κ₁ ⊕ κ₂)) : Stiefel 𝕜 (ι₁ ⊕ κ₂) κ₂ :=
  ⟨F.1.toCols₂, toCols₂_mem_stiefel F.2⟩

omit [Fintype κ₁] [DecidableEq ι₁] in
theorem continuous_stiefelRestrict : Continuous (stiefelRestrict 𝕜 ι₁ κ₁ κ₂) :=
  Continuous.subtype_mk (continuous_matrix fun i j =>
    continuous_subtype_val.matrix_elem i (Sum.inr j)) _

omit [Fintype κ₁] in
theorem stiefelRestrict_smul (g : unitaryGroup (ι₁ ⊕ κ₂) 𝕜) (F : Stiefel 𝕜 (ι₁ ⊕ κ₂) (κ₁ ⊕ κ₂)) :
    stiefelRestrict 𝕜 ι₁ κ₁ κ₂ (g • F) = g • stiefelRestrict 𝕜 ι₁ κ₁ κ₂ F := by
  apply Subtype.ext
  ext i k
  simp [stiefelRestrict, toCols₂, mul_apply]

omit [Fintype κ₁] [DecidableEq ι₁] in
/-- **A frame whose last vectors are `F₀` is block diagonal**: if `FᴴF = I` and the last `|κ₂|`
columns of `F` are `(0; I)`, then `F = diag(A, I)` with `AᴴA = I`. -/
theorem eq_fromBlocks_of_toCols₂ {F : Matrix (ι₁ ⊕ κ₂) (κ₁ ⊕ κ₂) 𝕜} (hF : Fᴴ * F = 1)
    (h0 : F.toCols₂ = baseFrame) :
    F = fromBlocks F.toBlocks₁₁ 0 0 1 ∧ F.toBlocks₁₁ᴴ * F.toBlocks₁₁ = 1 := by
  have hB : F.toBlocks₁₂ = 0 := by
    ext i j
    have := congrFun (congrFun h0 (Sum.inl i)) j
    simpa [toCols₂, baseFrame, toBlocks₁₂] using this
  have hD : F.toBlocks₂₂ = 1 := by
    ext i j
    have := congrFun (congrFun h0 (Sum.inr i)) j
    simpa [toCols₂, baseFrame, toBlocks₂₂] using this
  have hFb := fromBlocks_toBlocks F
  rw [hB, hD] at hFb
  rw [← hFb, fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one] at hF
  obtain ⟨h11, h12, -, -⟩ := fromBlocks_inj.1 hF
  have hC : F.toBlocks₂₁ = 0 := by
    simpa using h12
  rw [hC] at hFb h11
  refine ⟨hFb.symm, ?_⟩
  simpa using h11

omit [Fintype κ₁] [DecidableEq ι₁] in
theorem fromBlocks_mem_stiefel {A : Matrix ι₁ κ₁ 𝕜} (hA : A ∈ Stiefel 𝕜 ι₁ κ₁) :
    fromBlocks A 0 0 1 ∈ Stiefel 𝕜 (ι₁ ⊕ κ₂) (κ₁ ⊕ κ₂) := by
  rw [mem_stiefel, fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one]
  simp only [conjTranspose_zero, conjTranspose_one, Matrix.zero_mul, Matrix.mul_zero,
    add_zero, zero_add, Matrix.mul_one]
  rw [mem_stiefel.1 hA]

omit [Fintype ι₁] [Fintype κ₁] [Fintype κ₂] [DecidableEq ι₁] [DecidableEq κ₁] in
theorem toCols₂_fromBlocks (A : Matrix ι₁ κ₁ 𝕜) :
    (fromBlocks A 0 0 1 : Matrix (ι₁ ⊕ κ₂) (κ₁ ⊕ κ₂) 𝕜).toCols₂ = baseFrame := by
  ext (i | i) j <;> simp [toCols₂, baseFrame]

variable (𝕜 ι₁ κ₁ κ₂) in
/-- **The fibre of the restriction over `F₀` is `Stiefel ι₁ κ₁`**, `diag(A, I) ↔ A`. -/
def stiefelFibreHomeomorph :
    stiefelRestrict 𝕜 ι₁ κ₁ κ₂ ⁻¹' {stiefelBase} ≃ₜ Stiefel 𝕜 ι₁ κ₁ where
  toFun F := ⟨F.1.1.toBlocks₁₁, (eq_fromBlocks_of_toCols₂ F.1.2
    (congrArg Subtype.val F.2)).2⟩
  invFun A := ⟨⟨fromBlocks A.1 0 0 1, fromBlocks_mem_stiefel A.2⟩,
    Subtype.ext (toCols₂_fromBlocks _)⟩
  left_inv F := Subtype.ext (Subtype.ext
    (eq_fromBlocks_of_toCols₂ F.1.2 (congrArg Subtype.val F.2)).1.symm)
  right_inv _ := Subtype.ext (toBlocks_fromBlocks₁₁ _ _ _ _)
  continuous_toFun := Continuous.subtype_mk (continuous_matrix fun i j =>
    (continuous_subtype_val.comp continuous_subtype_val).matrix_elem (Sum.inl i) (Sum.inl j)) _
  continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk
    (Continuous.matrix_fromBlocks continuous_subtype_val continuous_const continuous_const
      continuous_const) _) _

omit [Fintype κ₁] [DecidableEq ι₁] in
/-- **`V_{k}(𝕜ⁿ) → V_j(𝕜ⁿ)` is locally trivial**: the restriction
`Stiefel (ι₁ ⊕ κ₂) (κ₁ ⊕ κ₂) → Stiefel (ι₁ ⊕ κ₂) κ₂` to the last `|κ₂|` vectors has local
trivializations with fibre `Stiefel ι₁ κ₁` around every point. -/
theorem stiefelRestrict_locallyTrivial (b : Stiefel 𝕜 (ι₁ ⊕ κ₂) κ₂) :
    ∃ U : Set (Stiefel 𝕜 (ι₁ ⊕ κ₂) κ₂), IsOpen U ∧ b ∈ U ∧
      ∃ φ : stiefelRestrict 𝕜 ι₁ κ₁ κ₂ ⁻¹' U ≃ₜ U × Stiefel 𝕜 ι₁ κ₁,
        ∀ x, (φ x).1 = ⟨stiefelRestrict 𝕜 ι₁ κ₁ κ₂ x, x.2⟩ := by
  classical
  exact exists_triv_of_orbitSection' _ continuous_stiefelRestrict stiefelRestrict_smul stiefelBase
    exists_unitary_smul_baseFrame isOpen_secDomain stiefelBase_mem_secDomain localSection
    continuous_localSection localSection_smul (stiefelFibreHomeomorph 𝕜 ι₁ κ₁ κ₂) b

/-! ### The unitary group over the Stiefel manifold -/

variable (𝕜 ι₁ κ₂) in
/-- **The orbit map** `U(ι₁ ⊕ κ₂) → Stiefel (ι₁ ⊕ κ₂) κ₂`, `g ↦ g F₀`, the last `|κ₂|` columns
of `g`. -/
def unitaryOrbit (g : unitaryGroup (ι₁ ⊕ κ₂) 𝕜) : Stiefel 𝕜 (ι₁ ⊕ κ₂) κ₂ := g • stiefelBase

theorem continuous_unitaryOrbit : Continuous (unitaryOrbit 𝕜 ι₁ κ₂) :=
  continuous_id.smul continuous_const

theorem unitaryOrbit_mul (g h : unitaryGroup (ι₁ ⊕ κ₂) 𝕜) :
    unitaryOrbit 𝕜 ι₁ κ₂ (g • h) = g • unitaryOrbit 𝕜 ι₁ κ₂ h :=
  mul_smul g h _

theorem coe_unitaryOrbit (g : unitaryGroup (ι₁ ⊕ κ₂) 𝕜) :
    (unitaryOrbit 𝕜 ι₁ κ₂ g : Matrix (ι₁ ⊕ κ₂) κ₂ 𝕜) =
      (g : Matrix (ι₁ ⊕ κ₂) (ι₁ ⊕ κ₂) 𝕜).toCols₂ := by
  ext i k
  simp [unitaryOrbit, stiefelBase, baseFrame, mul_apply, toCols₂, Fintype.sum_sum_type,
    one_apply]

theorem fromBlocks_mem_unitaryGroup {S : Matrix ι₁ ι₁ 𝕜} (hS : S ∈ unitaryGroup ι₁ 𝕜) :
    fromBlocks S 0 0 1 ∈ unitaryGroup (ι₁ ⊕ κ₂) 𝕜 := by
  rw [← SetLike.mem_coe, coe_unitaryGroup_eq_stiefel]
  rw [← SetLike.mem_coe, coe_unitaryGroup_eq_stiefel] at hS
  exact fromBlocks_mem_stiefel hS

variable (𝕜 ι₁ κ₂) in
/-- **Milnor's embedding** `U(ι₁) → U(ι₁ ⊕ κ₂)`, `S ↦ diag(S, I)` (p. 128). -/
def unitaryIncl : unitaryGroup ι₁ 𝕜 →* unitaryGroup (ι₁ ⊕ κ₂) 𝕜 where
  toFun S := ⟨fromBlocks S 0 0 1, fromBlocks_mem_unitaryGroup S.2⟩
  map_one' := Subtype.ext fromBlocks_one
  map_mul' S T := Subtype.ext (by
    simp only [Submonoid.coe_mul, fromBlocks_multiply, Matrix.mul_zero, add_zero,
      Matrix.zero_mul, zero_add, Matrix.mul_one])

@[simp]
theorem coe_unitaryIncl (S : unitaryGroup ι₁ 𝕜) :
    (unitaryIncl 𝕜 ι₁ κ₂ S : Matrix (ι₁ ⊕ κ₂) (ι₁ ⊕ κ₂) 𝕜) = fromBlocks (S : Matrix _ _ 𝕜) 0 0 1 :=
  rfl

theorem continuous_unitaryIncl : Continuous (unitaryIncl 𝕜 ι₁ κ₂) :=
  Continuous.subtype_mk (Continuous.matrix_fromBlocks continuous_subtype_val continuous_const
    continuous_const continuous_const) _

theorem fromBlocks_toBlocks_of_mem_fiber
    (g : unitaryOrbit 𝕜 ι₁ κ₂ ⁻¹' {stiefelBase}) :
    fromBlocks (g.1 : Matrix (ι₁ ⊕ κ₂) (ι₁ ⊕ κ₂) 𝕜).toBlocks₁₁ 0 0 1 =
        (g.1 : Matrix (ι₁ ⊕ κ₂) (ι₁ ⊕ κ₂) 𝕜) ∧
      (g.1 : Matrix (ι₁ ⊕ κ₂) (ι₁ ⊕ κ₂) 𝕜).toBlocks₁₁ ∈ unitaryGroup ι₁ 𝕜 := by
  have hg : (g.1 : Matrix (ι₁ ⊕ κ₂) (ι₁ ⊕ κ₂) 𝕜)ᴴ * (g.1 : Matrix (ι₁ ⊕ κ₂) (ι₁ ⊕ κ₂) 𝕜) = 1 := by
    rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.1 g.1.2
  have h0 : (g.1 : Matrix (ι₁ ⊕ κ₂) (ι₁ ⊕ κ₂) 𝕜).toCols₂ = baseFrame :=
    (coe_unitaryOrbit g.1).symm.trans (congrArg Subtype.val g.2)
  have h := eq_fromBlocks_of_toCols₂ hg h0
  refine ⟨h.1.symm, ?_⟩
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose]
  exact h.2

variable (𝕜 ι₁ κ₂) in
/-- **The fibre of `U(ι₁ ⊕ κ₂) → Stiefel` over `F₀` is `U(ι₁)`**, embedded by `S ↦ diag(S, I)`. -/
def unitaryFibreHomeomorph :
    unitaryOrbit 𝕜 ι₁ κ₂ ⁻¹' {stiefelBase} ≃ₜ unitaryGroup ι₁ 𝕜 where
  toFun g := ⟨(g.1 : Matrix (ι₁ ⊕ κ₂) (ι₁ ⊕ κ₂) 𝕜).toBlocks₁₁,
    (fromBlocks_toBlocks_of_mem_fiber g).2⟩
  invFun S := ⟨unitaryIncl 𝕜 ι₁ κ₂ S, Subtype.ext ((coe_unitaryOrbit _).trans
    (toCols₂_fromBlocks _))⟩
  left_inv g := Subtype.ext (Subtype.ext (fromBlocks_toBlocks_of_mem_fiber g).1)
  right_inv _ := Subtype.ext (toBlocks_fromBlocks₁₁ _ _ _ _)
  continuous_toFun := Continuous.subtype_mk (continuous_matrix fun i j =>
    (continuous_subtype_val.comp continuous_subtype_val).matrix_elem (Sum.inl i) (Sum.inl j)) _
  continuous_invFun := Continuous.subtype_mk continuous_unitaryIncl _

/-- The inclusion of the fibre is Milnor's embedding. -/
theorem unitaryFibreHomeomorph_symm_apply (S : unitaryGroup ι₁ 𝕜) :
    ((unitaryFibreHomeomorph 𝕜 ι₁ κ₂).symm S : unitaryGroup (ι₁ ⊕ κ₂) 𝕜) =
      unitaryIncl 𝕜 ι₁ κ₂ S :=
  rfl

/-- **`U(ι₁) → U(ι₁ ⊕ κ₂) → Stiefel (ι₁ ⊕ κ₂) κ₂` is a fibre bundle** (Milnor pp. 128–129,
after Steenrod): the orbit map has local trivializations with fibre `U(ι₁)` around every point.
For `κ₂` a point this is `U(m) → U(m+1) → S^{2m+1}`; for `ι₁ = κ₂ = Fin m` it is
`U(m) → U(2m) → U(2m)/U(m)`. -/
theorem unitaryOrbit_locallyTrivial (b : Stiefel 𝕜 (ι₁ ⊕ κ₂) κ₂) :
    ∃ U : Set (Stiefel 𝕜 (ι₁ ⊕ κ₂) κ₂), IsOpen U ∧ b ∈ U ∧
      ∃ φ : unitaryOrbit 𝕜 ι₁ κ₂ ⁻¹' U ≃ₜ U × unitaryGroup ι₁ 𝕜,
        ∀ x, (φ x).1 = ⟨unitaryOrbit 𝕜 ι₁ κ₂ x, x.2⟩ :=
  exists_triv_of_orbitSection' _ continuous_unitaryOrbit unitaryOrbit_mul stiefelBase
    exists_unitary_smul_baseFrame isOpen_secDomain stiefelBase_mem_secDomain localSection
    continuous_localSection localSection_smul (unitaryFibreHomeomorph 𝕜 ι₁ κ₂) b

end Bundles

end Morse.Homotopy
