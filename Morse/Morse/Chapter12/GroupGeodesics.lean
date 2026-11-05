import Morse.Chapter12.MatrixGroups
import Morse.Chapter12.BiInvariant
import Morse.Chapter7.GeodesicFlow

/-!
Milnor, *Morse Theory*, §21 (pp. 112–115): geodesics and curvature of a Lie group with a
bi-invariant metric, for the matrix groups of `Morse/Chapter12/MatrixGroups.lean`.

# Geodesics and curvature of `U(n)`, `SU(n)`, `O(n)`, `SO(n)`

## Milnor's text, paraphrased

* **Lemma 21.1** (p. 112): with a left- and right-invariant metric, `I_τ(σ) = τσ⁻¹τ` is an isometry
  of `G` fixing `τ` and reversing the geodesics through `τ`; so `G` is a symmetric space.
* **Lemma 21.2** (p. 113): the geodesics `γ` with `γ(0) = e` are exactly the one-parameter
  subgroups of `G`.  *Proof*: `I_{γ(t)} I_e` translates `γ` (20.1), so `γ(t)γ(u)γ(t) = γ(u + 2t)`,
  whence `γ(nt) = γ(t)ⁿ`, `γ(t' + t'') = γ(t')γ(t'')` for commensurable `t', t''`, and for all by
  continuity; conversely a one-parameter subgroup is the geodesic with its initial velocity.
* **Theorem 21.3** (pp. 113–114), for left-invariant fields `X, Y, Z, W`: (a) `⟨[X,Y],Z⟩ =
  ⟨X,[Y,Z]⟩`; (b) `R(X,Y)Z = ¼[[X,Y],Z]`; (c) `⟨R(X,Y)Z,W⟩ = ¼⟨[X,Y],[Z,W]⟩`; and, in the proof,
  (d) `X ⊢ Y = ½[X,Y]`.  **Corollary 21.4** (p. 115): the sectional curvature
  `⟨R(X,Y)X,Y⟩ = ¼|[X,Y]|²` is `≥ 0`, `= 0` iff `[X,Y] = 0`.

## What is formalized

For a matrix group `G` with Lie algebra `𝔤` (`Morse.IsMatrixGroup`), as a submanifold of
`Mₙ(𝕜)` with the induced metric, everything is computed *directly in the embedding*, without
left-invariant vector fields:

* **The projection onto `T_gG = g·𝔤`** (`Morse.IsMatrixGroup.tanProj_eq`):
  `P_g(M) = g · P_𝔤(gᴴM)`, where `P_𝔤` is the orthogonal projection of `Mₙ(𝕜)` onto `𝔤`; it
  kills Hermitian matrices (`Morse.algProj_hermitian`).
* **Geodesics** (`Morse.IsMatrixGroup.isGeodesicOn_mul_exp_smul`): `t ↦ g exp(tX)`, `X ∈ 𝔤`, is a
  geodesic on `ℝ`: its acceleration `g exp(tX) X²` is normal to `G`, because `X²` is Hermitian and
  `Re tr(HY) = 0` for `H` Hermitian, `Y` skew-Hermitian.  **Conversely**
  (`Morse.IsMatrixGroup.eqOn_mul_exp_smul`) every geodesic on an interval is of this form, by the
  uniqueness of geodesics.  **Lemma 21.2**: `Morse.IsMatrixGroup.lemma_21_2` (a geodesic through
  `I` is `t ↦ exp(tX)` and is a one-parameter subgroup), `Morse.IsMatrixGroup.exp_eq` (the
  Riemannian exponential at `g` is `gX ↦ g exp X`, Milnor's footnote on p. 57),
  `Morse.IsMatrixGroup.isGeodesicallyComplete`.
* **Lemma 21.1**: `Morse.IsMatrixGroup.symmIso` (`A ↦ τAᴴτ`, a linear isometry of `Mₙ(𝕜)`
  preserving `G` and fixing `τ`) and `Morse.IsMatrixGroup.symmIso_mul_exp_smul` (it reverses the
  geodesics through `τ`).
* **The second fundamental form** (`Morse.IsMatrixGroup.secondFundForm_mul`):
  `II_g(gX, gY) = ½ g(XY + YX)`, from the geodesic equation `γ'' = II(γ', γ')` and polarization.
* **Theorem 21.3**: (d) `Morse.IsMatrixGroup.covAt_mul_right` (`∇_{gX}(qY) = g·½[X,Y]` for the
  left-invariant field `q ↦ qY`); (a) `Morse.isAdInvariant_frobForm`; (b)
  `Morse.IsMatrixGroup.curvOp_mul` (`R(gX, gY)gZ = ¼ g[[X,Y],Z]`, **by the Gauss equation**) and
  `Morse.IsMatrixGroup.curvOp_eq_curv_halfLie`: **the curvature tensor of the submanifold `G` is
  the algebraic `curv (halfLie 𝔤)` of `Morse/Chapter12/BiInvariant.lean`**; (c)
  `Morse.IsMatrixGroup.inner_curvOp_mul`; **Corollary 21.4**: `Morse.IsMatrixGroup.sectional_mul`,
  `Morse.IsMatrixGroup.sectional_mul_nonneg`.

## Gaps in Milnor's text

* p. 113, "the integral curves of `X` are left translates of one-parameter subgroups, and
  therefore are geodesics": this needs Lemma 21.2 *and* that left translations are isometries
  (`Morse.IsMatrixGroup.mulLeftIso_image`); in the embedding both are replaced by the direct
  computation of the acceleration.
* p. 114, (b): Milnor uses that `Y ⊢ Z` is again left-invariant, which needs (d) for all
  left-invariant fields; here (b) is obtained independently from the Gauss equation of
  Chapter 6, `⟨R(x,y)z,w⟩ = ⟨II(x,z),II(y,w)⟩ − ⟨II(x,w),II(y,z)⟩`, and the trace identity
  `tr((XZ+ZX)(YW+WY)) − tr((XW+WX)(YZ+ZY)) = −tr([[X,Y],Z]W)` (`Morse.trace_gauss_identity`), which
  holds for all square matrices.
* p. 113, Lemma 21.2, "by continuity": the passage from commensurable `t', t''` to all needs the
  continuity of `γ` *and* of multiplication; here the one-parameter subgroup property is read off
  from `exp((s + t)X) = exp(sX) exp(tX)`.
-/

open Matrix Set Filter Topology Module
open scoped Morse.MatrixInner RealInnerProductSpace Manifold ContDiff

noncomputable section

namespace Morse

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Two matrix identities -/

omit [DecidableEq ι] in
/-- **The trace identity behind the Gauss equation for `G`**: for all square matrices,
`tr((XZ+ZX)(YW+WY)) − tr((XW+WX)(YZ+ZY)) = −tr([[X,Y],Z]W)`. -/
theorem trace_gauss_identity (X Y Z W : Matrix ι ι 𝕜) :
    trace ((X * Z + Z * X) * (Y * W + W * Y)) - trace ((X * W + W * X) * (Y * Z + Z * Y)) =
      -trace (((X * Y - Y * X) * Z - Z * (X * Y - Y * X)) * W) := by
  have c : ∀ A B C D : Matrix ι ι 𝕜, trace (A * B * C * D) = trace (D * A * B * C) := by
    intro A B C D
    rw [trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, ← Matrix.mul_assoc,
    trace_add, trace_sub]
  rw [c X W Y Z, c X W Z Y, c Y X W Z, c Z X W Y, c Y Z X W, c X Z W Y, c Y X Z W, c X Z Y W,
    c Z X Y W, c X Y Z W, c Z Y X W]
  ring

omit [DecidableEq ι] in
/-- For skew-Hermitian `X, Z`, the anticommutator `XZ + ZX` is Hermitian. -/
theorem conjTranspose_anticomm {X Z : Matrix ι ι 𝕜} (hX : Xᴴ = -X) (hZ : Zᴴ = -Z) :
    (X * Z + Z * X)ᴴ = X * Z + Z * X := by
  rw [conjTranspose_add, conjTranspose_mul, conjTranspose_mul, hX, hZ]
  noncomm_ring

omit [DecidableEq ι] in
/-- For skew-Hermitian `X, Y, Z`, `[[X,Y],Z]` is skew-Hermitian. -/
theorem conjTranspose_lie_lie {X Y Z : Matrix ι ι 𝕜} (hX : Xᴴ = -X) (hY : Yᴴ = -Y)
    (hZ : Zᴴ = -Z) : ((X * Y - Y * X) * Z - Z * (X * Y - Y * X))ᴴ =
      -((X * Y - Y * X) * Z - Z * (X * Y - Y * X)) := by
  simp only [conjTranspose_sub, conjTranspose_mul, hX, hY, hZ]
  noncomm_ring

omit [DecidableEq ι] in
/-- **The Gauss-equation identity**, in inner products: for skew-Hermitian `X, Y, Z, W`,
`⟪XZ+ZX, YW+WY⟫ − ⟪XW+WX, YZ+ZY⟫ = ⟪[[X,Y],Z], W⟫`. -/
theorem inner_gauss_identity {X Y Z W : Matrix ι ι 𝕜} (hX : Xᴴ = -X) (hY : Yᴴ = -Y)
    (hZ : Zᴴ = -Z) (hW : Wᴴ = -W) :
    ⟪X * Z + Z * X, Y * W + W * Y⟫ - ⟪X * W + W * X, Y * Z + Z * Y⟫ =
      ⟪(X * Y - Y * X) * Z - Z * (X * Y - Y * X), W⟫ := by
  rw [inner_def, inner_def, inner_def, conjTranspose_anticomm hX hZ, conjTranspose_anticomm hX hW,
    conjTranspose_lie_lie hX hY hZ, ← map_sub, trace_gauss_identity, Matrix.neg_mul, trace_neg]

omit [DecidableEq ι] in
/-- **21.3(a) for matrices**: `⟪[X,Y], Z⟫ = ⟪X, [Y,Z]⟫` for skew-Hermitian `X, Y`. -/
theorem inner_lie_left {X Y Z : Matrix ι ι 𝕜} (hX : Xᴴ = -X) (hY : Yᴴ = -Y) :
    ⟪X * Y - Y * X, Z⟫ = ⟪X, Y * Z - Z * Y⟫ := by
  rw [inner_def, inner_def, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, hX, hY]
  congr 1
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.sub_mul, Matrix.mul_sub, trace_sub,
    trace_neg, Matrix.mul_assoc]
  rw [trace_mul_comm Y (X * Z), Matrix.mul_assoc]
  ring

/-! ### The projection onto `𝔤` -/

/-- The orthogonal projection of `Mₙ(𝕜)` onto the Lie algebra `𝔤`. -/
def algProj (𝔤 : LieSubalgebra ℝ (Matrix ι ι 𝕜)) : Matrix ι ι 𝕜 →L[ℝ] Matrix ι ι 𝕜 :=
  𝔤.toSubmodule.starProjection

theorem algProj_mem (𝔤 : LieSubalgebra ℝ (Matrix ι ι 𝕜)) (M : Matrix ι ι 𝕜) :
    algProj 𝔤 M ∈ 𝔤 :=
  𝔤.toSubmodule.starProjection_apply_mem M

theorem algProj_of_mem {𝔤 : LieSubalgebra ℝ (Matrix ι ι 𝕜)} {X : Matrix ι ι 𝕜} (hX : X ∈ 𝔤) :
    algProj 𝔤 X = X :=
  Submodule.starProjection_eq_self_iff.2 hX

/-- `P_𝔤` kills the Hermitian matrices (they are orthogonal to the skew-Hermitian ones). -/
theorem algProj_hermitian {𝔤 : LieSubalgebra ℝ (Matrix ι ι 𝕜)} (hskew : ∀ X ∈ 𝔤, Xᴴ = -X)
    {H : Matrix ι ι 𝕜} (hH : Hᴴ = H) : algProj 𝔤 H = 0 := by
  rw [algProj, Submodule.starProjection_apply_eq_zero_iff, Submodule.mem_orthogonal]
  intro u hu
  rw [real_inner_comm]
  exact inner_eq_zero_of_hermitian_of_skew hH (hskew u hu)

/-- `P_𝔤(X + H) = X` for `X ∈ 𝔤` and `H` Hermitian. -/
theorem algProj_add_hermitian {𝔤 : LieSubalgebra ℝ (Matrix ι ι 𝕜)} (hskew : ∀ X ∈ 𝔤, Xᴴ = -X)
    {X H : Matrix ι ι 𝕜} (hX : X ∈ 𝔤) (hH : Hᴴ = H) : algProj 𝔤 (X + H) = X := by
  rw [map_add, algProj_of_mem hX, algProj_hermitian hskew hH, add_zero]

/-- `XY = ½[X,Y] + ½(XY + YX)`: so `P_𝔤(XY) = ½[X,Y]` for `X, Y ∈ 𝔤`. -/
theorem algProj_mul {𝔤 : LieSubalgebra ℝ (Matrix ι ι 𝕜)} (hskew : ∀ X ∈ 𝔤, Xᴴ = -X)
    {X Y : Matrix ι ι 𝕜} (hX : X ∈ 𝔤) (hY : Y ∈ 𝔤) :
    algProj 𝔤 (X * Y) = (1 / 2 : ℝ) • (X * Y - Y * X) := by
  have hlie : X * Y - Y * X ∈ 𝔤 := by
    have := 𝔤.lie_mem hX hY
    rwa [Ring.lie_def] at this
  have h : X * Y = (1 / 2 : ℝ) • (X * Y - Y * X) + (1 / 2 : ℝ) • (X * Y + Y * X) := by module
  conv_lhs => rw [h]
  rw [algProj_add_hermitian hskew (𝔤.smul_mem _ hlie)]
  rw [conjTranspose_smul, star_trivial, conjTranspose_anticomm (hskew X hX) (hskew Y hY)]

/-! ### Milnor's `⟨ , ⟩` on `𝔤` -/

/-- **The Frobenius inner product on `𝔤`**, as a bilinear form on the Lie algebra (Milnor's
`⟨ , ⟩` on `𝔤`, p. 125), in the form used by `Morse/Chapter12/BiInvariant.lean`. -/
def frobForm (𝔤 : LieSubalgebra ℝ (Matrix ι ι 𝕜)) : LinearMap.BilinForm ℝ 𝔤 :=
  LinearMap.mk₂ ℝ (fun X Y => ⟪(X : Matrix ι ι 𝕜), (Y : Matrix ι ι 𝕜)⟫)
    (fun X X' Y => by simp [inner_add_left])
    (fun c X Y => by simp [real_inner_smul_left])
    (fun X Y Y' => by simp [inner_add_right])
    (fun c X Y => by simp [real_inner_smul_right])

theorem frobForm_apply (𝔤 : LieSubalgebra ℝ (Matrix ι ι 𝕜)) (X Y : 𝔤) :
    frobForm 𝔤 X Y = ⟪(X : Matrix ι ι 𝕜), (Y : Matrix ι ι 𝕜)⟫ := rfl

/-- **Theorem 21.3(a)**: on a Lie algebra of skew-Hermitian matrices the Frobenius form is
ad-invariant, `⟨[X,Y],Z⟩ = ⟨X,[Y,Z]⟩` (Milnor p. 126: `⟨SAS⁻¹, SBS⁻¹⟩ = ⟨A, B⟩`, differentiated). -/
theorem isAdInvariant_frobForm {𝔤 : LieSubalgebra ℝ (Matrix ι ι 𝕜)} (hskew : ∀ X ∈ 𝔤, Xᴴ = -X) :
    IsAdInvariant (frobForm 𝔤) := by
  intro X Y Z
  simp only [frobForm_apply, LieSubalgebra.coe_bracket, Ring.lie_def]
  exact inner_lie_left (hskew X X.2) (hskew Y Y.2)

/-- The Frobenius form is positive definite on `𝔤`. -/
theorem frobForm_pos {𝔤 : LieSubalgebra ℝ (Matrix ι ι 𝕜)} (X : 𝔤) (hX : X ≠ 0) :
    0 < frobForm 𝔤 X X := by
  rw [frobForm_apply, real_inner_self_eq_norm_sq]
  have : (X : Matrix ι ι 𝕜) ≠ 0 := fun h0 => hX (Subtype.ext h0)
  positivity

/-! ### Geodesics -/

omit [Fintype ι] [DecidableEq ι] in
theorem hasDerivAt_mul_exp_smul [Fintype ι] [DecidableEq ι] (g X : Matrix ι ι 𝕜) (t : ℝ) :
    HasDerivAt (fun s : ℝ => g * NormedSpace.exp (s • X)) (g * NormedSpace.exp (t • X) * X) t := by
  have := (hasDerivAt_exp_smul_const X t).const_mul g
  simpa only [Matrix.mul_assoc] using this

theorem deriv_mul_exp_smul (g X : Matrix ι ι 𝕜) :
    deriv (fun s : ℝ => g * NormedSpace.exp (s • X)) = fun t => g * NormedSpace.exp (t • X) * X :=
  funext fun t => (hasDerivAt_mul_exp_smul g X t).deriv

theorem deriv_deriv_mul_exp_smul (g X : Matrix ι ι 𝕜) (t : ℝ) :
    deriv (deriv (fun s : ℝ => g * NormedSpace.exp (s • X))) t =
      g * NormedSpace.exp (t • X) * X * X := by
  rw [deriv_mul_exp_smul]
  exact ((hasDerivAt_mul_exp_smul g X t).mul_const X).deriv

section Group

variable {Z W : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {G : Set (Matrix ι ι 𝕜)} {hG : Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix ι ι 𝕜) Z W G}
  {𝔤 : LieSubalgebra ℝ (Matrix ι ι 𝕜)}

namespace IsMatrixGroup

variable (h : IsMatrixGroup hG 𝔤)
include h

/-- **The projection onto `T_gG = g·𝔤`**: `P_g(M) = g · P_𝔤(gᴴ M)`. -/
theorem tanProj_eq (g : G) (M : Matrix ι ι 𝕜) :
    tanProj hG g M = g.1 * algProj 𝔤 (g.1ᴴ * M) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun w hw => ?_
  · rw [h.mem_tangentSubspace_iff, ← Matrix.mul_assoc, h.unitary g g.2, Matrix.one_mul]
    exact algProj_mem 𝔤 _
  · rw [h.mem_tangentSubspace_iff] at hw
    have hw' : w = g.1 * (g.1ᴴ * w) := by
      rw [← Matrix.mul_assoc, h.mul_conjTranspose g.2, Matrix.one_mul]
    have hM : M = g.1 * (g.1ᴴ * M) := by
      rw [← Matrix.mul_assoc, h.mul_conjTranspose g.2, Matrix.one_mul]
    rw [hw', hM, ← Matrix.mul_sub, inner_mul_left_of_unitary (h.unitary g g.2), ← hM]
    exact Submodule.starProjection_inner_eq_zero (K := 𝔤.toSubmodule) _ _ hw

theorem prj_eq {g : Matrix ι ι 𝕜} (hg : g ∈ G) (M : Matrix ι ι 𝕜) :
    prj hG g M = g * algProj 𝔤 (gᴴ * M) := by
  rw [prj_of_mem hG hg, h.tanProj_eq ⟨g, hg⟩]

/-- **The one-parameter subgroups and their translates are geodesics** (Milnor p. 113): for
`g ∈ G` and `X ∈ 𝔤`, `t ↦ g exp(tX)` is a geodesic of `G` on all of `ℝ`.  Its acceleration
`g exp(tX) X²` is normal to `T_{γ(t)}G = γ(t)·𝔤`: `X²` is Hermitian. -/
theorem isGeodesicOn_mul_exp_smul {g : Matrix ι ι 𝕜} (hg : g ∈ G) {X : Matrix ι ι 𝕜}
    (hX : X ∈ 𝔤) : IsGeodesicOn hG (fun t => g * NormedSpace.exp (t • X)) univ where
  isOpen := isOpen_univ
  mem t _ := h.mul_exp_smul_mem hg hX t
  contDiffOn := (contDiff_const.mul (contDiff_exp_smul X)).contDiffOn
  normal t _ := by
    rw [deriv_deriv_mul_exp_smul, Submodule.mem_orthogonal]
    intro u hu
    set q : G := ⟨g * NormedSpace.exp (t • X), h.mul_exp_smul_mem hg hX t⟩
    change u ∈ tangentSubspace hG q at hu
    rw [h.mem_tangentSubspace_iff] at hu
    have hu' : u = q.1 * (q.1ᴴ * u) := by
      rw [← Matrix.mul_assoc, h.mul_conjTranspose q.2, Matrix.one_mul]
    have hXX : g * NormedSpace.exp (t • X) * X * X = q.1 * (X * X) := by
      simp only [q, Matrix.mul_assoc]
    rw [hu', hXX, inner_mul_left_of_unitary (h.unitary q q.2)]
    have hXX' : (X * X)ᴴ = X * X := by
      rw [conjTranspose_mul, h.skew X hX, neg_mul_neg]
    rw [real_inner_comm]
    exact inner_eq_zero_of_hermitian_of_skew hXX' (h.skew _ hu)

/-- `t ↦ exp(tX)`, the one-parameter subgroup, is a geodesic through `I`. -/
theorem isGeodesicOn_exp_smul {X : Matrix ι ι 𝕜} (hX : X ∈ 𝔤) :
    IsGeodesicOn hG (fun t => NormedSpace.exp (t • X)) univ := by
  simpa using h.isGeodesicOn_mul_exp_smul h.one_mem hX

/-- **Every geodesic of `G` is a translate of a one-parameter subgroup** (the converse in
Lemma 21.2, after a left translation): a geodesic on a preconnected open `s ∋ t₀` is
`t ↦ γ(t₀) exp((t − t₀)X)` with `X = γ(t₀)ᴴ γ'(t₀) ∈ 𝔤`, by the uniqueness of geodesics. -/
theorem eqOn_mul_exp_smul {γ : ℝ → Matrix ι ι 𝕜} {s : Set ℝ} (hγ : IsGeodesicOn hG γ s)
    (hs : IsPreconnected s) {t₀ : ℝ} (ht₀ : t₀ ∈ s) :
    (γ t₀)ᴴ * deriv γ t₀ ∈ 𝔤 ∧
      EqOn γ (fun t => γ t₀ * NormedSpace.exp ((t - t₀) • ((γ t₀)ᴴ * deriv γ t₀))) s := by
  set g := γ t₀ with hgdef
  have hg : g ∈ G := hγ.mem t₀ ht₀
  set X := gᴴ * deriv γ t₀ with hXdef
  have hX : X ∈ 𝔤 := by
    have := hγ.deriv_mem ht₀
    rwa [h.mem_tangentSubspace_iff] at this
  refine ⟨hX, ?_⟩
  set g' := g * NormedSpace.exp ((-t₀) • X)
  have hg' : g' ∈ G := h.mul_exp_smul_mem hg hX _
  have hc : (fun t => g' * NormedSpace.exp (t • X)) =
      fun t => g * NormedSpace.exp ((t - t₀) • X) := by
    funext t
    rw [Matrix.mul_assoc, exp_smul_mul_exp_smul, neg_add_eq_sub]
  have hgeo := (h.isGeodesicOn_mul_exp_smul hg' hX).mono hγ.isOpen (subset_univ s)
  rw [hc] at hgeo
  refine hγ.eqOn hgeo hs ht₀ (by simp [hgdef]) ?_
  have hd : HasDerivAt (fun t => g * NormedSpace.exp ((t - t₀) • X)) (g * X) t₀ := by
    have := hasDerivAt_mul_exp_smul g' X t₀
    rw [hc] at this
    convert this using 1
    simp only [g', Matrix.mul_assoc, exp_smul_mul_exp_smul, neg_add_cancel, zero_smul,
      NormedSpace.exp_zero, Matrix.one_mul]
  rw [hd.deriv, hXdef, ← Matrix.mul_assoc, h.mul_conjTranspose hg, Matrix.one_mul]

/-- **Lemma 21.2** (Milnor p. 113): a geodesic `γ : ℝ → G` with `γ(0) = I` is
`t ↦ exp(tX)`, `X = γ'(0) ∈ 𝔤`, a one-parameter subgroup: `γ(s + t) = γ(s)γ(t)`. -/
theorem lemma_21_2 {γ : ℝ → Matrix ι ι 𝕜} (hγ : IsGeodesicOn hG γ univ) (h1 : γ 0 = 1) :
    deriv γ 0 ∈ 𝔤 ∧ (∀ t, γ t = NormedSpace.exp (t • deriv γ 0)) ∧
      ∀ s t, γ (s + t) = γ s * γ t := by
  obtain ⟨hX, heq⟩ := h.eqOn_mul_exp_smul hγ isPreconnected_univ (mem_univ 0)
  rw [h1, conjTranspose_one, Matrix.one_mul] at hX heq
  have hγt : ∀ t, γ t = NormedSpace.exp (t • deriv γ 0) := fun t => by
    rw [heq (mem_univ t)]
    simp
  refine ⟨hX, hγt, fun s t => ?_⟩
  rw [hγt, hγt, hγt, exp_smul_mul_exp_smul]

omit h [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **Lemma 21.2, the other half**: a differentiable one-parameter subgroup `θ` of `Mₙ(𝕜)` is
`t ↦ exp(tθ'(0))`.  (`θ'(t) = θ(t)X = Xθ(t)`, so `exp(−tX)θ(t)` has derivative `0`.) -/
theorem eq_exp_of_oneParam {θ : ℝ → Matrix ι ι 𝕜} (hθ : Differentiable ℝ θ) (h0 : θ 0 = 1)
    (hmul : ∀ s t, θ (s + t) = θ s * θ t) (t : ℝ) :
    θ t = NormedSpace.exp (t • deriv θ 0) := by
  set X := deriv θ 0
  have hX : HasDerivAt θ X 0 := (hθ 0).hasDerivAt
  have hcomm : ∀ t, θ t * X = X * θ t := fun t => by
    have h1 : HasDerivAt (fun s => θ t * θ s) (θ t * X) 0 := hX.const_mul (θ t)
    have h2 : HasDerivAt (fun s => θ s * θ t) (X * θ t) 0 := hX.mul_const (θ t)
    have h3 : (fun s => θ s * θ t) = fun s => θ t * θ s := funext fun s => by
      rw [← hmul, ← hmul, add_comm]
    rw [h3] at h2
    exact h1.unique h2
  have hd : ∀ t, HasDerivAt θ (θ t * X) t := fun t => by
    have h1 : HasDerivAt (fun s => θ t * θ s) (θ t * X) (t - t) := by
      rw [sub_self]; exact hX.const_mul (θ t)
    have h2 := h1.comp_sub_const t t
    have h3 : (fun u => θ t * θ (u - t)) = θ := funext fun u => by
      rw [← hmul, add_sub_cancel]
    rwa [h3] at h2
  set F : ℝ → Matrix ι ι 𝕜 := fun s => NormedSpace.exp ((-s) • X) * θ s
  have hF : ∀ s, HasDerivAt F 0 s := fun s => by
    have he : HasDerivAt (fun u : ℝ => NormedSpace.exp ((-u) • X))
        ((-1 : ℝ) • (NormedSpace.exp ((-s) • X) * X)) s :=
      (hasDerivAt_exp_smul_const X (-s)).scomp s (hasDerivAt_neg s)
    refine (he.fun_mul (hd s)).congr_deriv ?_
    rw [neg_one_smul, Matrix.neg_mul, Matrix.mul_assoc, hcomm s, neg_add_cancel]
  have hconst := is_const_of_deriv_eq_zero (fun s => (hF s).differentiableAt)
    (fun s => (hF s).deriv) t 0
  have hF0 : F 0 = 1 := by simp [F, h0]
  rw [hF0] at hconst
  calc θ t = NormedSpace.exp (t • X) * F t := by
        simp only [F, ← Matrix.mul_assoc, exp_smul_mul_exp_smul, add_neg_cancel, zero_smul,
          NormedSpace.exp_zero, Matrix.one_mul]
    _ = NormedSpace.exp (t • X) := by rw [hconst, Matrix.mul_one]

/-- **Lemma 21.2** (Milnor p. 113), both halves: a differentiable one-parameter subgroup of `G`
is a geodesic (it is `t ↦ exp(tX)` with `X = θ'(0) ∈ T_IG = 𝔤`). -/
theorem isGeodesicOn_of_oneParam {θ : ℝ → Matrix ι ι 𝕜} (hθ : Differentiable ℝ θ)
    (hθG : ∀ t, θ t ∈ G) (h0 : θ 0 = 1) (hmul : ∀ s t, θ (s + t) = θ s * θ t) :
    IsGeodesicOn hG θ univ := by
  have hX : deriv θ 0 ∈ 𝔤 := by
    have hT := hasDerivAt_mem_tangentSubspace hG (hθ 0).hasDerivAt
      (Filter.Eventually.of_forall hθG)
    have h1 : (⟨θ 0, (Filter.Eventually.of_forall (f := 𝓝 (0 : ℝ)) hθG).self_of_nhds⟩ : G) =
        ⟨1, h.one_mem⟩ := Subtype.ext h0
    rw [h1, h.mem_tangentSubspace_iff] at hT
    simpa using hT
  have heq : θ = fun t => NormedSpace.exp (t • deriv θ 0) :=
    funext (eq_exp_of_oneParam hθ h0 hmul)
  rw [heq]
  exact h.isGeodesicOn_exp_smul hX

/-- **The Riemannian exponential map is the matrix exponential** (Milnor's footnote on p. 57, and
Consequence (i) of 21.2 in the exposition): `exp_g(gX) = g exp X` for `X ∈ 𝔤`. -/
theorem exp_eq {g : Matrix ι ι 𝕜} (hg : g ∈ G) {X : Matrix ι ι 𝕜} (hX : X ∈ 𝔤) :
    Morse.exp hG g (g * X) = g * NormedSpace.exp X := by
  have hfrom : IsGeodesicFrom hG (fun t => g * NormedSpace.exp (t • X)) g (g * X) := by
    refine ⟨1, one_pos, (h.isGeodesicOn_mul_exp_smul hg hX).mono isOpen_Ioo (subset_univ _), ?_,
      ?_⟩
    · simp
    · rw [deriv_mul_exp_smul]
      simp
  rw [hfrom.exp_eq, one_smul]

/-- **Matrix groups are geodesically complete** (Milnor's Corollary 20.2 for `G`): every geodesic
`t ↦ g exp(tX)` is defined on all of `ℝ`. -/
theorem isGeodesicallyComplete : IsGeodesicallyComplete hG := by
  intro q v hv
  rw [h.mem_tangentSubspace_iff] at hv
  have hv' : v = q.1 * (q.1ᴴ * v) := by
    rw [← Matrix.mul_assoc, h.mul_conjTranspose q.2, Matrix.one_mul]
  refine ⟨fun t => q.1 * NormedSpace.exp (t • (q.1ᴴ * v)), 1, one_pos,
    (h.isGeodesicOn_mul_exp_smul q.2 hv).mono isOpen_Ioo (subset_univ _), by simp, ?_⟩
  rw [deriv_mul_exp_smul]
  simp only [zero_smul, NormedSpace.exp_zero, Matrix.mul_one]
  exact hv'.symm

/-! ### Lemma 21.1: `G` is a symmetric space -/

omit h [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **Milnor's reflection `I_τ(σ) = τσ⁻¹τ`** (Lemma 21.1), extended to `Mₙ(𝕜)` as
`A ↦ τAᴴτ`: an involutive linear isometry for unitary `τ`. -/
def symmIso (τ : Matrix ι ι 𝕜) (hτ : τᴴ * τ = 1) : Matrix ι ι 𝕜 ≃ₗᵢ[ℝ] Matrix ι ι 𝕜 where
  toFun A := τ * Aᴴ * τ
  invFun A := τ * Aᴴ * τ
  map_add' A B := by rw [conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' r A := by
    rw [conjTranspose_smul, star_trivial, Matrix.mul_smul, Matrix.smul_mul]
    rfl
  left_inv A := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, hτ,
      Matrix.mul_one]
    rw [← Matrix.mul_assoc, mul_conjTranspose_eq_one hτ, Matrix.one_mul]
  right_inv A := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, hτ,
      Matrix.mul_one]
    rw [← Matrix.mul_assoc, mul_conjTranspose_eq_one hτ, Matrix.one_mul]
  norm_map' A := by
    have h1 := inner_mul_left_of_unitary hτ (Aᴴ * τ) (Aᴴ * τ)
    have h2 := inner_mul_right_of_unitary (mul_conjTranspose_eq_one hτ) Aᴴ Aᴴ
    have h3 := inner_conjTranspose A A
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h1 h2 h3
    rw [← Matrix.mul_assoc] at h1
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (h1.trans (h2.trans h3))

omit h [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
@[simp] theorem symmIso_apply (τ : Matrix ι ι 𝕜) (hτ : τᴴ * τ = 1) (A : Matrix ι ι 𝕜) :
    symmIso τ hτ A = τ * Aᴴ * τ := rfl

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **Lemma 21.1** (Milnor p. 112): `I_τ` maps `G` into itself and fixes `τ`. -/
theorem symmIso_mem {τ : Matrix ι ι 𝕜} (hτ : τ ∈ G) {σ : Matrix ι ι 𝕜} (hσ : σ ∈ G) :
    symmIso τ (h.unitary τ hτ) σ ∈ G :=
  h.mul_mem _ (h.mul_mem τ hτ _ (h.star_mem σ hσ)) τ hτ

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem symmIso_self {τ : Matrix ι ι 𝕜} (hτ : τ ∈ G) : symmIso τ (h.unitary τ hτ) τ = τ := by
  rw [symmIso_apply, Matrix.mul_assoc, h.unitary τ hτ, Matrix.mul_one]

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **Lemma 21.1** (Milnor p. 112): `I_τ` **reverses the geodesics through `τ`**:
`I_τ(τ exp(tX)) = τ exp(−tX)`. -/
theorem symmIso_mul_exp_smul {τ : Matrix ι ι 𝕜} (hτ : τ ∈ G) {X : Matrix ι ι 𝕜} (hX : X ∈ 𝔤)
    (t : ℝ) : symmIso τ (h.unitary τ hτ) (τ * NormedSpace.exp (t • X)) =
      τ * NormedSpace.exp ((-t) • X) := by
  rw [symmIso_apply, conjTranspose_mul, ← Matrix.exp_conjTranspose, conjTranspose_smul,
    star_trivial, h.skew X hX, Matrix.mul_assoc, Matrix.mul_assoc, h.unitary τ hτ,
    Matrix.mul_one, smul_neg, neg_smul]

/-! ### The second fundamental form -/

/-- `II_g(gX, gX) = gX²`: the geodesic equation `γ'' = II(γ', γ')` for `γ(t) = g exp(tX)` at
`t = 0`. -/
theorem secondFundForm_mul_self (g : G) {X : Matrix ι ι 𝕜} (hX : X ∈ 𝔤) :
    secondFundForm hG g (g.1 * X) (g.1 * X) = g.1 * (X * X) := by
  have hgeo := h.isGeodesicOn_mul_exp_smul g.2 hX
  have heq := hgeo.deriv_deriv_eq (mem_univ 0)
  have hq : (⟨g.1 * NormedSpace.exp ((0 : ℝ) • X), hgeo.mem 0 (mem_univ 0)⟩ : G) = g :=
    Subtype.ext (by simp)
  rw [hq, deriv_deriv_mul_exp_smul, deriv_mul_exp_smul] at heq
  simp only [zero_smul, NormedSpace.exp_zero, Matrix.mul_one] at heq
  rw [← heq, Matrix.mul_assoc]

/-- **The second fundamental form of `G`**: `II_g(gX, gY) = ½ g(XY + YX)`, by polarization of
`II_g(gX, gX) = gX²` (the second fundamental form is symmetric). -/
theorem secondFundForm_mul (g : G) {X Y : Matrix ι ι 𝕜} (hX : X ∈ 𝔤) (hY : Y ∈ 𝔤) :
    secondFundForm hG g (g.1 * X) (g.1 * Y) = (1 / 2 : ℝ) • (g.1 * (X * Y + Y * X)) := by
  have hXY := h.secondFundForm_mul_self g (𝔤.add_mem hX hY)
  have hcomm := secondFundForm_comm hG (h.mul_mem_tangentSubspace g hX)
    (h.mul_mem_tangentSubspace g hY)
  rw [Matrix.mul_add, secondFundForm_add_left, secondFundForm_add_right,
    secondFundForm_add_right, h.secondFundForm_mul_self g hX, h.secondFundForm_mul_self g hY,
    ← hcomm] at hXY
  have h2 : (2 : ℝ) • secondFundForm hG g (g.1 * X) (g.1 * Y) = g.1 * (X * Y + Y * X) := by
    rw [two_smul]
    have : g.1 * ((X + Y) * (X + Y)) = g.1 * (X * X) + g.1 * (Y * Y) + g.1 * (X * Y + Y * X) := by
      noncomm_ring
    rw [this] at hXY
    set a := secondFundForm hG g (g.1 * X) (g.1 * Y)
    have e1 : a + a = (g.1 * (X * X) + a + (a + g.1 * (Y * Y))) - g.1 * (X * X) -
        g.1 * (Y * Y) := by abel
    rw [e1, hXY]
    abel
  rw [← h2, smul_smul]
  norm_num

/-! ### Theorem 21.3 and Corollary 21.4 -/

/-- **Theorem 21.3(b) via the Gauss equation**: `R(gX, gY)gZ = ¼ g[[X,Y],Z]` for
`X, Y, Z ∈ 𝔤` (Milnor's sign).  Both sides are tangent, and their inner products with every
`gW` agree: `⟨II(gX,gZ), II(gY,gW)⟩ − ⟨II(gX,gW), II(gY,gZ)⟩ = ¼⟨[[X,Y],Z], W⟩`
(`Morse.inner_gauss_identity`). -/
theorem curvOp_mul (g : G) {X Y Z' : Matrix ι ι 𝕜} (hX : X ∈ 𝔤) (hY : Y ∈ 𝔤) (hZ : Z' ∈ 𝔤) :
    curvOp hG g (g.1 * X) (g.1 * Y) (g.1 * Z') =
      (1 / 4 : ℝ) • (g.1 * ((X * Y - Y * X) * Z' - Z' * (X * Y - Y * X))) := by
  have hT : ∀ {M : Matrix ι ι 𝕜}, M ∈ 𝔤 → g.1 * M ∈ tangentSubspace hG g :=
    fun hM => h.mul_mem_tangentSubspace g hM
  have hlie : (X * Y - Y * X) * Z' - Z' * (X * Y - Y * X) ∈ 𝔤 := by
    have h1 := 𝔤.lie_mem (𝔤.lie_mem hX hY) hZ
    simpa only [Ring.lie_def] using h1
  rw [← sub_eq_zero]
  refine eq_zero_of_mem_of_mem_orthogonal hG (q := g) ?_ ?_
  · refine Submodule.sub_mem _ (curvOp_mem hG (hT hX) (hT hY) (hT hZ)) ?_
    rw [← Matrix.mul_smul]
    exact hT (𝔤.smul_mem _ hlie)
  · rw [Submodule.mem_orthogonal']
    intro w hw
    rw [h.mem_tangentSubspace_iff] at hw
    have hw' : w = g.1 * (g.1ᴴ * w) := by
      rw [← Matrix.mul_assoc, h.mul_conjTranspose g.2, Matrix.one_mul]
    set W' := g.1ᴴ * w
    rw [hw', inner_sub_left, inner_curvOp, h.secondFundForm_mul g hX hZ,
      h.secondFundForm_mul g hY hw, h.secondFundForm_mul g hX hw, h.secondFundForm_mul g hY hZ]
    simp only [real_inner_smul_left, real_inner_smul_right,
      inner_mul_left_of_unitary (h.unitary g g.2)]
    have key := inner_gauss_identity (h.skew X hX) (h.skew Y hY) (h.skew Z' hZ) (h.skew W' hw)
    linear_combination (1 / 4 : ℝ) * key

/-- **Corollary 21.4** for `G`: the sectional curvature `⟨R(gX, gY)gX, gY⟩ = ¼‖[X,Y]‖²`. -/
theorem sectional_mul (g : G) {X Y : Matrix ι ι 𝕜} (hX : X ∈ 𝔤) (hY : Y ∈ 𝔤) :
    ⟪curvOp hG g (g.1 * X) (g.1 * Y) (g.1 * X), g.1 * Y⟫ =
      (1 / 4 : ℝ) * ‖X * Y - Y * X‖ ^ 2 := by
  have hlie : X * Y - Y * X ∈ 𝔤 := by
    have := 𝔤.lie_mem hX hY
    rwa [Ring.lie_def] at this
  rw [h.curvOp_mul g hX hY hX, ← Matrix.mul_smul, inner_mul_left_of_unitary (h.unitary g g.2),
    real_inner_smul_left, inner_lie_left (h.skew _ hlie) (h.skew X hX),
    ← real_inner_self_eq_norm_sq]

/-- **Corollary 21.4** for `G`: the sectional curvature is `≥ 0`, and `0` iff `[X,Y] = 0`. -/
theorem sectional_mul_nonneg (g : G) {X Y : Matrix ι ι 𝕜} (hX : X ∈ 𝔤) (hY : Y ∈ 𝔤) :
    0 ≤ ⟪curvOp hG g (g.1 * X) (g.1 * Y) (g.1 * X), g.1 * Y⟫ ∧
      (⟪curvOp hG g (g.1 * X) (g.1 * Y) (g.1 * X), g.1 * Y⟫ = 0 ↔ X * Y = Y * X) := by
  rw [h.sectional_mul g hX hY]
  refine ⟨by positivity, ?_⟩
  rw [mul_eq_zero, pow_eq_zero_iff two_ne_zero, norm_eq_zero, sub_eq_zero]
  norm_num

/-- **Theorem 21.3(d)**, `X ⊢ Y = ½[X,Y]`: the covariant derivative of the left-invariant field
`q ↦ qY` in the direction `gX` is `g · ½[X,Y]`.  (`d(qY)(gX) = gXY`, projected onto `g·𝔤`.) -/
theorem covAt_mul_right (g : G) {X Y : Matrix ι ι 𝕜} (hX : X ∈ 𝔤) (hY : Y ∈ 𝔤) :
    covAt hG g (g.1 * X) (fun q : G => q.1 * Y) = g.1 * ((1 / 2 : ℝ) • (X * Y - Y * X)) := by
  set L : Matrix ι ι 𝕜 →L[ℝ] Matrix ι ι 𝕜 := (ContinuousLinearMap.mul ℝ (Matrix ι ι 𝕜)).flip Y
  have hLf : (fun A : Matrix ι ι 𝕜 => A * Y) = L := funext fun A => rfl
  have hd : DifferentiableAt ℝ (fun A : Matrix ι ι 𝕜 => A * Y) g.1 := by
    rw [hLf]; exact L.differentiableAt
  have hfd : fderiv ℝ (fun A : Matrix ι ι 𝕜 => A * Y) g.1 (g.1 * X) = g.1 * X * Y := by
    rw [hLf, L.fderiv]
    rfl
  rw [covAt, dN_comp_val hG hd (h.mul_mem_tangentSubspace g hX), hfd, h.tanProj_eq,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, h.unitary g g.2, Matrix.one_mul,
    algProj_mul h.skew hX hY]

/-- **Theorem 21.3(b): the curvature tensor of the submanifold `G` is the algebraic one of
`Morse/Chapter12/BiInvariant.lean`**: for `X, Y, Z ∈ 𝔤`,
`R(gX, gY)gZ = g · curv (½[ , ]) X Y Z = g · ¼[[X,Y],Z]`. -/
theorem curvOp_eq_curv_halfLie (g : G) (X Y Z' : 𝔤) :
    curvOp hG g (g.1 * X) (g.1 * Y) (g.1 * Z') =
      g.1 * ((curv (halfLie 𝔤) X Y Z' : 𝔤) : Matrix ι ι 𝕜) := by
  rw [h.curvOp_mul g X.2 Y.2 Z'.2, curv_halfLie]
  change _ = g.1 * ((1 / 4 : ℝ) • ((⁅⁅X, Y⁆, Z'⁆ : 𝔤) : Matrix ι ι 𝕜))
  rw [LieSubalgebra.coe_bracket, LieSubalgebra.coe_bracket, Ring.lie_def, Ring.lie_def,
    Matrix.mul_smul]

/-- The same, for Lemma 9.1's trilinear `curvTensor` on `T_gG`. -/
theorem coe_curvTensor_eq_curv_halfLie (g : G) (X Y Z' : 𝔤) :
    (curvTensor hG g ⟨g.1 * X, h.mul_mem_tangentSubspace g X.2⟩
      ⟨g.1 * Y, h.mul_mem_tangentSubspace g Y.2⟩ ⟨g.1 * Z', h.mul_mem_tangentSubspace g Z'.2⟩ :
        Matrix ι ι 𝕜) = g.1 * ((curv (halfLie 𝔤) X Y Z' : 𝔤) : Matrix ι ι 𝕜) := by
  rw [coe_curvTensor_apply]
  exact h.curvOp_eq_curv_halfLie g X Y Z'

/-- **Theorem 21.3(c)** for `G`: `⟨R(gX, gY)gZ, gW⟩ = ¼⟨[X,Y],[Z,W]⟩`. -/
theorem inner_curvOp_mul (g : G) (X Y Z' W' : 𝔤) :
    ⟪curvOp hG g (g.1 * X) (g.1 * Y) (g.1 * Z'), g.1 * W'⟫ =
      (1 / 4 : ℝ) * frobForm 𝔤 ⁅X, Y⁆ ⁅Z', W'⁆ := by
  rw [h.curvOp_eq_curv_halfLie, inner_mul_left_of_unitary (h.unitary g g.2), ← frobForm_apply,
    curv_inner (isAdInvariant_frobForm h.skew)]

/-- **Milnor's `K_V`** (proof of 21.7, p. 116) for `G`: `R(gA, gW)gA = g · K_A(W)`, with
`K_A = −¼ ad_A²` the operator `jacobiOp` of `Morse/Chapter12/BiInvariant.lean`. -/
theorem curvOp_eq_jacobiOp (g : G) (A W' : 𝔤) :
    curvOp hG g (g.1 * A) (g.1 * W') (g.1 * A) = g.1 * ((jacobiOp 𝔤 A W' : 𝔤) : Matrix ι ι 𝕜) := by
  rw [h.curvOp_eq_curv_halfLie, curv_halfLie_eq_jacobiOp]

end IsMatrixGroup

end Group

end Morse
