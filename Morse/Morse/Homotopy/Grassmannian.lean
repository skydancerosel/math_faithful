import Mathlib
import Morse.Homotopy.Stiefel

/-!
# The Grassmannian `G_m(𝕜ⁿ)` and the bundle `U(m) → V_m(𝕜ⁿ) → G_m(𝕜ⁿ)`

Milnor, *Morse Theory*, §23, p. 129: "The complex Grassmann manifold `G_m(ℂ^{2m})` can be
identified with the coset space `U(2m)/U(m) × U(m)`. (Compare Steenrod §7.) From the exact
sequence of the fibration `U(m) → U(2m)/U(m) → G_m(ℂ^{2m})` we see now that
`πᵢ G_m(ℂ^{2m}) ≅ πᵢ₋₁ U(m)` for `i ≤ 2m`" (paraphrased). This file constructs the fibration;
the homotopy groups are computed in `Morse/Homotopy/BundlesUnitary.lean`.

## The model

`Morse.Homotopy.Grassmannian 𝕜 ι k` is the set of Hermitian projections `P` (`Pᴴ = P`,
`P² = P`) of `𝕜^ι` with `tr P = k`, i.e. the orthogonal projections onto the `k`-dimensional
subspaces. This is the model of Milnor's Lemma 23.1, where a minimal geodesic from `I` to `−I`
in `SU(2m)` is `t ↦ exp(tA)` with `A = iπ(2P − I)` and `tr P = m`
(`Morse.sq_eq_neg_pi_sq_iff`, `Morse.trace_pi_smul_projection`).

The **frame-to-span map** `Stiefel ι (Fin m) → Grassmannian ι m`, `F ↦ F Fᴴ`
(`Morse.Homotopy.frameSpan`), sends an orthonormal frame to the projection onto its span. It is
onto (`Morse.Homotopy.exists_frame_of_mem_grassmannian`: an orthonormal basis of the range of
`P` has `tr P` elements), equivariant for `U(ι)`, acting on frames by `g • F = gF` and on
projections by `g • P = gPgᴴ`, and its fibre over `P₀ = F₀F₀ᴴ` is `{F₀S : S ∈ U(m)} ≅ U(m)`
(`Morse.Homotopy.frameSpanFibreHomeomorph`).

## Local triviality

`Morse.Homotopy.frameSpan_locallyTrivial` (as `Morse.Homotopy.IsLocallyTrivial`:
`Morse.Homotopy.isLocallyTrivial_frameSpan`, `Morse/Homotopy/BundleHomotopy.lean`): by
`Morse.Homotopy.exists_triv_of_orbitSection`,
it suffices to have a continuous unitary `g(P)` with `g(P) P₀ g(P)ᴴ = P` for `P` near `P₀`. Near
`P₀` the columns of `P F₀` are linearly independent (their Gram matrix `F₀ᴴ P F₀` is close to
`I`), and the **Gram–Schmidt process** turns them into an orthonormal frame `σ(P)` spanning the
range of `P`; the Gram–Schmidt process is continuous at linearly independent families
(`Morse.Homotopy.continuousAt_gramSchmidtNormed`), and `σ(P₀) = F₀`. Then `g(P) = s(σ(P))`, with
`s` the explicit section of `Morse/Homotopy/Stiefel.lean`. That `σ(P) σ(P)ᴴ = P` comes from a
trace argument (`Morse.Homotopy.eq_of_mul_eq_of_trace_eq`): if `P` and `Q` are Hermitian
projections with `PQ = Q` and `tr P = tr Q`, then `R = P − Q` is a Hermitian projection with
`tr(RᴴR) = tr R = 0`, so `R = 0`.
-/

open Matrix Set Function Topology Finset InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace Morse.Homotopy

/-! ### Continuity of the Gram–Schmidt process -/

section GramSchmidt

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]

/-- **The Gram–Schmidt process is continuous** at a linearly independent family: each
`gramSchmidt 𝕜 f n = f n − Σ_{i<n} (⟪uᵢ, f n⟫/‖uᵢ‖²) uᵢ` is built from the earlier vectors by
operations that are continuous where `uᵢ ≠ 0`. -/
theorem continuousAt_gramSchmidt {f₀ : ι → E} (h₀ : LinearIndependent 𝕜 f₀) (n : ι) :
    ContinuousAt (fun f : ι → E => gramSchmidt 𝕜 f n) f₀ := by
  induction n using WellFoundedLT.induction with
  | _ n ih =>
  have key : (fun f : ι → E => gramSchmidt 𝕜 f n) = fun f => f n -
      ∑ i ∈ Iio n, (inner 𝕜 (gramSchmidt 𝕜 f i) (f n) / (‖gramSchmidt 𝕜 f i‖ : 𝕜) ^ 2) •
        gramSchmidt 𝕜 f i := by
    funext f
    rw [eq_sub_iff_add_eq]
    exact (gramSchmidt_def'' 𝕜 f n).symm
  rw [key]
  refine (continuous_apply n).continuousAt.sub (tendsto_finsetSum _ fun i hi => ?_)
  have hi' : i < n := Finset.mem_Iio.1 hi
  have hne : (‖gramSchmidt 𝕜 f₀ i‖ : 𝕜) ^ 2 ≠ 0 := by
    have := gramSchmidt_ne_zero i h₀
    exact pow_ne_zero _ (RCLike.ofReal_ne_zero.2 (norm_ne_zero_iff.2 this))
  refine ContinuousAt.smul (ContinuousAt.div ((ih i hi').inner
    (continuous_apply n).continuousAt) ?_ hne) (ih i hi')
  exact ((RCLike.continuous_ofReal.continuousAt).comp (ih i hi').norm).pow 2

/-- The normalized Gram–Schmidt process is continuous at a linearly independent family. -/
theorem continuousAt_gramSchmidtNormed {f₀ : ι → E} (h₀ : LinearIndependent 𝕜 f₀) (n : ι) :
    ContinuousAt (fun f : ι → E => gramSchmidtNormed 𝕜 f n) f₀ := by
  have hne : (‖gramSchmidt 𝕜 f₀ n‖ : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (gramSchmidt_ne_zero n h₀))
  exact ((((RCLike.continuous_ofReal.continuousAt).comp
    (continuousAt_gramSchmidt h₀ n).norm).inv₀ hne)).smul (continuousAt_gramSchmidt h₀ n)

end GramSchmidt

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### Hermitian projections -/

section Projections

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Comparison of projections by their traces**: if `P` and `Q` are Hermitian projections with
`PQ = Q` (the range of `Q` lies in that of `P`) and `tr P = tr Q`, then `P = Q`. -/
theorem eq_of_mul_eq_of_trace_eq {P Q : Matrix ι ι 𝕜} (hP : Pᴴ = P) (hP2 : P * P = P)
    (hQ : Qᴴ = Q) (hQ2 : Q * Q = Q) (hPQ : P * Q = Q) (htr : P.trace = Q.trace) : P = Q := by
  have hQP : Q * P = Q := by
    have := congrArg conjTranspose hPQ
    rwa [conjTranspose_mul, hP, hQ] at this
  have hR : (P - Q)ᴴ * (P - Q) = P - Q := by
    rw [conjTranspose_sub, hP, hQ, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hP2, hQ2,
      hPQ, hQP]
    abel
  have h0 : ((P - Q)ᴴ * (P - Q)).trace = 0 := by
    rw [hR, trace_sub, htr, sub_self]
  exact sub_eq_zero.1 (trace_conjTranspose_mul_self_eq_zero_iff.1 h0)

end Projections

/-! ### The Grassmannian and the frame-to-span map -/

section Grassmannian

variable (𝕜) (ι : Type*) [Fintype ι] [DecidableEq ι] (k : ℕ)

/-- **The Grassmannian** `G_k(𝕜^ι)`, as the set of Hermitian projections `P` (`Pᴴ = P`,
`P² = P`) of trace `k`, with the subspace topology. -/
def Grassmannian : Set (Matrix ι ι 𝕜) := {P | Pᴴ = P ∧ P * P = P ∧ P.trace = k}

variable {𝕜 ι k}

theorem conj_mem_grassmannian {g : Matrix ι ι 𝕜} (hg : g ∈ unitaryGroup ι 𝕜) {P : Matrix ι ι 𝕜}
    (hP : P ∈ Grassmannian 𝕜 ι k) : g * P * gᴴ ∈ Grassmannian 𝕜 ι k := by
  obtain ⟨h1, h2, h3⟩ := hP
  have hg' : gᴴ * g = 1 := by rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.1 hg
  refine ⟨?_, ?_, ?_⟩
  · rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, h1,
      Matrix.mul_assoc]
  · calc g * P * gᴴ * (g * P * gᴴ) = g * P * (gᴴ * g) * P * gᴴ := by
          simp only [Matrix.mul_assoc]
      _ = g * P * gᴴ := by rw [hg', Matrix.mul_one, Matrix.mul_assoc g P P, h2]
  · rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, hg', Matrix.mul_one, h3]

/-- `U(ι)` acts on the Grassmannian by conjugation, `g • P = gPgᴴ`. -/
instance : MulAction (unitaryGroup ι 𝕜) (Grassmannian 𝕜 ι k) where
  smul g P := ⟨(g : Matrix ι ι 𝕜) * P * (g : Matrix ι ι 𝕜)ᴴ, conj_mem_grassmannian g.2 P.2⟩
  one_smul P := Subtype.ext (by
    change ((1 : unitaryGroup ι 𝕜) : Matrix ι ι 𝕜) * P.1 * ((1 : unitaryGroup ι 𝕜) : Matrix ι ι 𝕜)ᴴ
      = P.1
    simp)
  mul_smul g h P := Subtype.ext (by
    change ((g * h : unitaryGroup ι 𝕜) : Matrix ι ι 𝕜) * P.1 *
        ((g * h : unitaryGroup ι 𝕜) : Matrix ι ι 𝕜)ᴴ =
      (g : Matrix ι ι 𝕜) * ((h : Matrix ι ι 𝕜) * P.1 * (h : Matrix ι ι 𝕜)ᴴ) *
        (g : Matrix ι ι 𝕜)ᴴ
    simp [conjTranspose_mul, Matrix.mul_assoc])

@[simp]
theorem coe_smul_grassmannian (g : unitaryGroup ι 𝕜) (P : Grassmannian 𝕜 ι k) :
    ((g • P : Grassmannian 𝕜 ι k) : Matrix ι ι 𝕜) =
      (g : Matrix ι ι 𝕜) * P * (g : Matrix ι ι 𝕜)ᴴ :=
  rfl

instance : ContinuousSMul (unitaryGroup ι 𝕜) (Grassmannian 𝕜 ι k) where
  continuous_smul := by
    change Continuous fun q : unitaryGroup ι 𝕜 × Grassmannian 𝕜 ι k =>
      (⟨(q.1 : Matrix ι ι 𝕜) * q.2 * (q.1 : Matrix ι ι 𝕜)ᴴ,
        conj_mem_grassmannian q.1.2 q.2.2⟩ : Grassmannian 𝕜 ι k)
    have h1 : Continuous fun q : unitaryGroup ι 𝕜 × Grassmannian 𝕜 ι k => (q.1 : Matrix ι ι 𝕜) :=
      continuous_subtype_val.comp continuous_fst
    exact Continuous.subtype_mk ((h1.matrix_mul (continuous_subtype_val.comp
      continuous_snd)).matrix_mul h1.matrix_conjTranspose) _

variable {m : ℕ}

omit [DecidableEq ι] in
theorem mul_conjTranspose_mem_grassmannian {F : Matrix ι (Fin m) 𝕜}
    (hF : F ∈ Stiefel 𝕜 ι (Fin m)) : F * Fᴴ ∈ Grassmannian 𝕜 ι m := by
  refine ⟨by rw [conjTranspose_mul, conjTranspose_conjTranspose], ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Fᴴ, mem_stiefel.1 hF, Matrix.one_mul]
  · rw [trace_mul_comm, mem_stiefel.1 hF, trace_one, Fintype.card_fin]

variable (𝕜 ι m) in
/-- **The frame-to-span map** `V_m(𝕜^ι) → G_m(𝕜^ι)`, `F ↦ F Fᴴ`, the orthogonal projection onto
the span of the frame. -/
def frameSpan (F : Stiefel 𝕜 ι (Fin m)) : Grassmannian 𝕜 ι m :=
  ⟨F.1 * F.1ᴴ, mul_conjTranspose_mem_grassmannian F.2⟩

omit [DecidableEq ι] in
theorem continuous_frameSpan : Continuous (frameSpan 𝕜 ι m) :=
  Continuous.subtype_mk (continuous_subtype_val.matrix_mul
    continuous_subtype_val.matrix_conjTranspose) _

theorem frameSpan_smul (g : unitaryGroup ι 𝕜) (F : Stiefel 𝕜 ι (Fin m)) :
    frameSpan 𝕜 ι m (g • F) = g • frameSpan 𝕜 ι m F := by
  apply Subtype.ext
  simp [frameSpan, conjTranspose_mul, Matrix.mul_assoc]

end Grassmannian

/-! ### Every projection is spanned by a frame -/

section Frames

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The matrix whose columns are the given vectors. -/
def colMatrix {κ : Type*} (v : κ → EuclideanSpace 𝕜 ι) : Matrix ι κ 𝕜 := Matrix.of fun i k => v k i

omit [DecidableEq ι] in
theorem colMatrix_mem_stiefel {κ : Type*} [DecidableEq κ] {v : κ → EuclideanSpace 𝕜 ι}
    (hv : Orthonormal 𝕜 v) : colMatrix v ∈ Stiefel 𝕜 ι κ := by
  rw [orthonormal_iff_ite] at hv
  ext j k
  rw [one_apply, ← hv j k, PiLp.inner_apply]
  simp [colMatrix, mul_apply, RCLike.inner_apply, mul_comm]

omit [Fintype ι] [DecidableEq ι] in
theorem colMatrix_mulVec {κ : Type*} [Fintype κ] (v : κ → EuclideanSpace 𝕜 ι) (c : κ → 𝕜) :
    colMatrix v *ᵥ c = WithLp.ofLp (∑ k, c k • v k) := by
  ext i
  simp [colMatrix, mulVec, dotProduct, mul_comm]

omit [DecidableEq ι] in
theorem conjTranspose_colMatrix_mulVec {κ : Type*} (v : κ → EuclideanSpace 𝕜 ι)
    (x : EuclideanSpace 𝕜 ι) : (colMatrix v)ᴴ *ᵥ WithLp.ofLp x = fun k => inner 𝕜 (v k) x := by
  ext k
  rw [PiLp.inner_apply]
  simp [colMatrix, mulVec, dotProduct, RCLike.inner_apply, mul_comm]

variable (𝕜) in
/-- The vectors fixed by `P` (for a projection, its range), as a subspace of `EuclideanSpace`. -/
def fixSubmodule (P : Matrix ι ι 𝕜) : Submodule 𝕜 (EuclideanSpace 𝕜 ι) where
  carrier := {x | P *ᵥ WithLp.ofLp x = WithLp.ofLp x}
  add_mem' := fun {x y} (hx : P *ᵥ WithLp.ofLp x = _) (hy : P *ᵥ WithLp.ofLp y = _) => by
    change P *ᵥ WithLp.ofLp (x + y) = WithLp.ofLp (x + y)
    rw [WithLp.ofLp_add, mulVec_add, hx, hy]
  zero_mem' := by
    change P *ᵥ WithLp.ofLp 0 = WithLp.ofLp 0
    rw [WithLp.ofLp_zero, mulVec_zero]
  smul_mem' := fun c x (hx : P *ᵥ WithLp.ofLp x = _) => by
    change P *ᵥ WithLp.ofLp (c • x) = WithLp.ofLp (c • x)
    rw [WithLp.ofLp_smul, mulVec_smul, hx]

omit [DecidableEq ι] in
theorem mem_fixSubmodule {P : Matrix ι ι 𝕜} {x : EuclideanSpace 𝕜 ι} :
    x ∈ fixSubmodule 𝕜 P ↔ P *ᵥ WithLp.ofLp x = WithLp.ofLp x :=
  Iff.rfl

omit [DecidableEq ι] in
/-- **Every Hermitian projection of trace `m` is `F Fᴴ` for an orthonormal `m`-frame `F`**: take
an orthonormal basis `b₁, …, b_r` of the range of `P` and `Q = Σ bₖbₖᴴ`. Then `PQ = Q` (the `bₖ`
lie in the range of `P`) and `QP = P` (`Q` fixes the range of `P`), so `P = Q`, and
`m = tr P = tr Q = r`. -/
theorem exists_frame_of_mem_grassmannian {m : ℕ} {P : Matrix ι ι 𝕜}
    (hP : P ∈ Grassmannian 𝕜 ι m) :
    ∃ F : Matrix ι (Fin m) 𝕜, F ∈ Stiefel 𝕜 ι (Fin m) ∧ F * Fᴴ = P := by
  obtain ⟨h1, h2, h3⟩ := hP
  -- the range of `P`, as the space of vectors fixed by `P`
  let V := fixSubmodule 𝕜 P
  let b := stdOrthonormalBasis 𝕜 V
  let v : Fin (Module.finrank 𝕜 V) → EuclideanSpace 𝕜 ι := fun k => (b k : EuclideanSpace 𝕜 ι)
  have hv : Orthonormal 𝕜 v := b.orthonormal.comp_linearIsometry V.subtypeₗᵢ
  let F := colMatrix v
  have hF : F ∈ Stiefel 𝕜 ι _ := colMatrix_mem_stiefel hv
  have hfix : ∀ x ∈ V, P *ᵥ WithLp.ofLp x = WithLp.ofLp x := fun x hx => hx
  -- `Q = F Fᴴ` fixes the range of `P`
  have hQfix : ∀ x ∈ V, (F * Fᴴ) *ᵥ WithLp.ofLp x = WithLp.ofLp x := by
    intro x hx
    rw [← mulVec_mulVec, conjTranspose_colMatrix_mulVec, colMatrix_mulVec]
    congr 1
    have := b.sum_repr' ⟨x, hx⟩
    have := congrArg Subtype.val this
    simpa [v, Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] using this
  have hPQ : P * (F * Fᴴ) = F * Fᴴ := by
    rw [← Matrix.mul_assoc]
    congr 1
    ext i k
    have := congrFun (hfix (v k) (b k).2) i
    simpa [F, colMatrix, mulVec, dotProduct, mul_apply] using this
  have hQP : F * Fᴴ * P = P := by
    ext i j
    have hcol : (WithLp.toLp 2 (fun l => P l j) : EuclideanSpace 𝕜 ι) ∈ V := by
      change P *ᵥ (fun l => P l j) = fun l => P l j
      ext l
      have := congrFun (congrFun h2 l) j
      simpa [mulVec, dotProduct, mul_apply] using this
    have := congrFun (hQfix _ hcol) i
    simpa [mulVec, dotProduct, mul_apply] using this
  have hPQeq : P = F * Fᴴ := by
    have hQh : (F * Fᴴ)ᴴ = F * Fᴴ := by rw [conjTranspose_mul, conjTranspose_conjTranspose]
    have hPQ' : P * (F * Fᴴ) = P := by
      have := congrArg conjTranspose hQP
      rwa [conjTranspose_mul, h1, hQh] at this
    exact hPQ'.symm.trans hPQ
  have hr : Module.finrank 𝕜 V = m := by
    have htr : (P.trace : 𝕜) = Module.finrank 𝕜 V := by
      rw [hPQeq, trace_mul_comm, mem_stiefel.1 hF, trace_one, Fintype.card_fin]
    rw [h3] at htr
    exact_mod_cast htr.symm
  let e : Fin m ≃ Fin (Module.finrank 𝕜 V) := finCongr hr.symm
  refine ⟨F.submatrix id e, ?_, ?_⟩
  · rw [mem_stiefel, conjTranspose_submatrix, ← submatrix_mul Fᴴ F e id e Function.bijective_id,
      mem_stiefel.1 hF, submatrix_one_equiv]
  · rw [conjTranspose_submatrix, submatrix_mul_equiv _ _ _ e, submatrix_id_id, hPQeq]

end Frames

/-! ### The Gram–Schmidt section near `P₀` -/

section Section

variable {ι₁ : Type*} [Fintype ι₁] [DecidableEq ι₁] {m : ℕ}

/-- The base frame `F₀ = (0; I)` of `𝕜^{ι₁ ⊕ Fin m}`. -/
local notation "F₀" => (baseFrame : Matrix (ι₁ ⊕ Fin m) (Fin m) 𝕜)

omit [DecidableEq ι₁] in
theorem baseFrame_conjTranspose_mul {n : Type*} (F : Matrix (ι₁ ⊕ Fin m) n 𝕜) :
    F₀ᴴ * F = F.toRows₂ := by
  conv_lhs => rw [← fromRows_toRows F]
  rw [baseFrame, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows]
  simp

omit [Fintype ι₁] [DecidableEq ι₁] in
theorem baseFrame_mul {n : Type*} (S : Matrix (Fin m) n 𝕜) : F₀ * S = fromRows 0 S := by
  rw [baseFrame, fromRows_mul]
  simp

variable (𝕜 ι₁ m) in
/-- **The base point** `P₀ = F₀F₀ᴴ` of the Grassmannian, the projection onto the last `m`
coordinates. -/
def grassBase : Grassmannian 𝕜 (ι₁ ⊕ Fin m) m := frameSpan 𝕜 _ m stiefelBase

/-- The columns of `P F₀`, the projections of the last `m` standard basis vectors. -/
def gsVecs (P : Matrix (ι₁ ⊕ Fin m) (ι₁ ⊕ Fin m) 𝕜) : Fin m → EuclideanSpace 𝕜 (ι₁ ⊕ Fin m) :=
  fun k => WithLp.toLp 2 fun i => (P * F₀) i k

/-- **The Gram–Schmidt frame** `σ(P)`: the columns of `P F₀`, orthonormalized. -/
def gsFrame (P : Matrix (ι₁ ⊕ Fin m) (ι₁ ⊕ Fin m) 𝕜) : Matrix (ι₁ ⊕ Fin m) (Fin m) 𝕜 :=
  colMatrix (gramSchmidtNormed 𝕜 (gsVecs P))

omit [DecidableEq ι₁] in
theorem colMatrix_gsVecs (P : Matrix (ι₁ ⊕ Fin m) (ι₁ ⊕ Fin m) 𝕜) :
    colMatrix (gsVecs P) = P * F₀ := by
  ext i k
  simp [colMatrix, gsVecs]

omit [DecidableEq ι₁] in
/-- Near `P₀` the columns of `P F₀` are linearly independent: their Gram matrix `F₀ᴴ P F₀` is
invertible. -/
theorem linearIndependent_gsVecs {P : Matrix (ι₁ ⊕ Fin m) (ι₁ ⊕ Fin m) 𝕜}
    (hP : IsUnit (F₀ᴴ * P * F₀).det) : LinearIndependent 𝕜 (gsVecs P) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h1 : (P * F₀) *ᵥ c = 0 := by
    rw [← colMatrix_gsVecs, colMatrix_mulVec, hc]
    rfl
  have h2 : (F₀ᴴ * P * F₀) *ᵥ c = 0 := by
    rw [Matrix.mul_assoc, ← mulVec_mulVec, h1, mulVec_zero]
  exact congrFun (eq_zero_of_mulVec_eq_zero hP.ne_zero h2)

omit [DecidableEq ι₁] in
theorem gsFrame_mem {P : Matrix (ι₁ ⊕ Fin m) (ι₁ ⊕ Fin m) 𝕜}
    (hP : IsUnit (F₀ᴴ * P * F₀).det) : gsFrame P ∈ Stiefel 𝕜 (ι₁ ⊕ Fin m) (Fin m) :=
  colMatrix_mem_stiefel (gramSchmidtNormed_orthonormal (linearIndependent_gsVecs hP))

omit [DecidableEq ι₁] in
/-- The Gram–Schmidt frame lies in the range of `P`. -/
theorem mul_gsFrame {P : Matrix (ι₁ ⊕ Fin m) (ι₁ ⊕ Fin m) 𝕜} (hP2 : P * P = P) :
    P * gsFrame P = gsFrame P := by
  have hsub : Submodule.span 𝕜 (Set.range (gsVecs P)) ≤ fixSubmodule 𝕜 P := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, mem_fixSubmodule]
    ext i
    have h : (P * (P * F₀)) i k = (P * F₀) i k := by rw [← Matrix.mul_assoc, hP2]
    simpa [gsVecs, mulVec, dotProduct, mul_apply] using h
  have hmem : ∀ k, gramSchmidtNormed 𝕜 (gsVecs P) k ∈ fixSubmodule 𝕜 P := by
    intro k
    apply hsub
    rw [← span_gramSchmidt 𝕜 (gsVecs P), ← span_gramSchmidtNormed_range]
    exact Submodule.subset_span ⟨k, rfl⟩
  ext i k
  have := congrFun (hmem k) i
  simpa [gsFrame, colMatrix, mulVec, dotProduct, mul_apply] using this

omit [DecidableEq ι₁] in
/-- **`σ(P)` spans the range of `P`**: `σ(P) σ(P)ᴴ = P`, by the trace comparison. -/
theorem gsFrame_mul_conjTranspose {P : Matrix (ι₁ ⊕ Fin m) (ι₁ ⊕ Fin m) 𝕜}
    (hPG : P ∈ Grassmannian 𝕜 (ι₁ ⊕ Fin m) m) (hP : IsUnit (F₀ᴴ * P * F₀).det) :
    gsFrame P * (gsFrame P)ᴴ = P := by
  obtain ⟨h1, h2, h3⟩ := hPG
  have hσ := mem_stiefel.1 (gsFrame_mem hP)
  refine (eq_of_mul_eq_of_trace_eq h1 h2 ?_ ?_ ?_ ?_).symm
  · rw [conjTranspose_mul, conjTranspose_conjTranspose]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ (gsFrame P), hσ, Matrix.one_mul]
  · rw [← Matrix.mul_assoc, mul_gsFrame h2]
  · rw [h3, trace_mul_comm, hσ, trace_one, Fintype.card_fin]

omit [DecidableEq ι₁] in
/-- At `P₀` the Gram–Schmidt frame is `F₀` itself. -/
theorem gsFrame_base : gsFrame (F₀ * F₀ᴴ) = F₀ := by
  have hF₀ : F₀ᴴ * F₀ = 1 := mem_stiefel.1 baseFrame_mem
  have hv : gsVecs (F₀ * F₀ᴴ) = fun k => WithLp.toLp 2 fun i => F₀ i k := by
    funext k
    simp only [gsVecs, Matrix.mul_assoc, hF₀, Matrix.mul_one]
  have hon := orthonormal_cols (baseFrame_mem (𝕜 := 𝕜) (ι₁ := ι₁) (κ := Fin m))
  rw [gsFrame, hv]
  have hgs : gramSchmidt 𝕜 (fun k => WithLp.toLp 2 fun i => F₀ i k) =
      fun k => WithLp.toLp 2 fun i => F₀ i k :=
    gramSchmidt_of_orthogonal 𝕜 fun j k hjk => hon.2 hjk
  ext i k
  simp only [colMatrix, gramSchmidtNormed, hgs, hon.1 k, RCLike.ofReal_one, inv_one, one_smul,
    of_apply]

omit [DecidableEq ι₁] in
/-- The Gram–Schmidt frame is continuous where the columns of `P F₀` are independent. -/
theorem continuousAt_gsFrame {P : Matrix (ι₁ ⊕ Fin m) (ι₁ ⊕ Fin m) 𝕜}
    (hP : IsUnit (F₀ᴴ * P * F₀).det) : ContinuousAt gsFrame P := by
  have hv : Continuous (gsVecs (𝕜 := 𝕜) (ι₁ := ι₁) (m := m)) :=
    continuous_pi fun k => (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i =>
      (continuous_id.matrix_mul continuous_const).matrix_elem i k)
  refine continuousAt_pi.2 fun i => continuousAt_pi.2 fun k => ?_
  have hli : LinearIndependent 𝕜 (gsVecs P) := linearIndependent_gsVecs hP
  have h0 : ContinuousAt (fun f : Fin m → EuclideanSpace 𝕜 (ι₁ ⊕ Fin m) =>
      gramSchmidtNormed 𝕜 f k) (gsVecs P) := continuousAt_gramSchmidtNormed hli k
  have h := ContinuousAt.comp
    (g := fun f : Fin m → EuclideanSpace 𝕜 (ι₁ ⊕ Fin m) => gramSchmidtNormed 𝕜 f k)
    (f := gsVecs) (x := P) h0 hv.continuousAt
  have hc : Continuous fun x : EuclideanSpace 𝕜 (ι₁ ⊕ Fin m) => WithLp.ofLp x i :=
    (continuous_apply i).comp (PiLp.continuous_ofLp 2 _)
  exact hc.continuousAt.comp h

end Section

/-! ### The bundle `U(m) → V_m → G_m` -/

section Bundle

variable {ι₁ : Type*} [Fintype ι₁] [DecidableEq ι₁] {m : ℕ}

local notation "F₀" => (baseFrame : Matrix (ι₁ ⊕ Fin m) (Fin m) 𝕜)

omit [DecidableEq ι₁] in
theorem coe_grassBase : (grassBase 𝕜 ι₁ m : Matrix (ι₁ ⊕ Fin m) (ι₁ ⊕ Fin m) 𝕜) = F₀ * F₀ᴴ :=
  rfl

variable (𝕜 ι₁ m) in
/-- The domain of the section near `P₀`: the columns of `P F₀` are independent, and the last
block `C` of `σ(P)` has `I + C` invertible. -/
def grassDomain : Set (Grassmannian 𝕜 (ι₁ ⊕ Fin m) m) :=
  {P | IsUnit (F₀ᴴ * P.1 * F₀).det ∧ IsUnit (1 + (gsFrame P.1).toRows₂).det}

omit [DecidableEq ι₁] in
theorem isOpen_grassDomain : IsOpen (grassDomain 𝕜 ι₁ m) := by
  let D := {P : Grassmannian 𝕜 (ι₁ ⊕ Fin m) m | IsUnit (F₀ᴴ * P.1 * F₀).det}
  have hdet : Continuous fun P : Grassmannian 𝕜 (ι₁ ⊕ Fin m) m => (F₀ᴴ * P.1 * F₀).det :=
    ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const).matrix_det
  have hD : IsOpen D := by
    have : D = (fun P : Grassmannian 𝕜 (ι₁ ⊕ Fin m) m => (F₀ᴴ * P.1 * F₀).det) ⁻¹' {0}ᶜ := by
      ext P
      simp [D, isUnit_iff_ne_zero]
    rw [this]
    exact isOpen_compl_singleton.preimage hdet
  have hcont : ContinuousOn
      (fun P : Grassmannian 𝕜 (ι₁ ⊕ Fin m) m => (1 + (gsFrame P.1).toRows₂).det) D := by
    intro P hP
    have h1 : ContinuousAt (fun P : Grassmannian 𝕜 (ι₁ ⊕ Fin m) m => gsFrame P.1) P :=
      (continuousAt_gsFrame hP).comp (f := Subtype.val) continuous_subtype_val.continuousAt
    have h2 : Continuous fun F : Matrix (ι₁ ⊕ Fin m) (Fin m) 𝕜 => (1 + F.toRows₂).det :=
      (continuous_const.add continuous_toRows₂).matrix_det
    exact (h2.continuousAt.comp h1).continuousWithinAt
  have := hcont.isOpen_inter_preimage hD (isOpen_compl_singleton (x := (0 : 𝕜)))
  convert this using 1
  ext P
  simp [grassDomain, D, isUnit_iff_ne_zero]

omit [DecidableEq ι₁] in
theorem grassBase_mem_grassDomain : grassBase 𝕜 ι₁ m ∈ grassDomain 𝕜 ι₁ m := by
  have hF₀ : F₀ᴴ * F₀ = 1 := mem_stiefel.1 baseFrame_mem
  refine ⟨?_, ?_⟩
  · rw [coe_grassBase, ← Matrix.mul_assoc, hF₀, Matrix.one_mul, hF₀, det_one]
    exact isUnit_one
  · rw [coe_grassBase, gsFrame_base]
    exact stiefelBase_mem_secDomain

/-- **The section of the orbit map `U(ι₁ ⊕ Fin m) → G_m`** near `P₀`: `g(P) = s(σ(P))`. -/
def grassSection (P : grassDomain 𝕜 ι₁ m) : unitaryGroup (ι₁ ⊕ Fin m) 𝕜 :=
  ⟨secMat (gsFrame P.1.1), secMat_mem_unitaryGroup (gsFrame_mem P.2.1) P.2.2⟩

theorem continuous_grassSection : Continuous (grassSection (𝕜 := 𝕜) (ι₁ := ι₁) (m := m)) := by
  refine Continuous.subtype_mk (continuous_iff_continuousAt.2 fun P => ?_) _
  have h1 : ContinuousAt (fun P : grassDomain 𝕜 ι₁ m => gsFrame P.1.1) P :=
    (continuousAt_gsFrame P.2.1).comp (f := fun P : grassDomain 𝕜 ι₁ m => P.1.1)
      (continuous_subtype_val.comp continuous_subtype_val).continuousAt
  exact (continuousAt_secMat P.2.2).comp (f := fun P : grassDomain 𝕜 ι₁ m => gsFrame P.1.1) h1

theorem grassSection_smul (P : grassDomain 𝕜 ι₁ m) : grassSection P • grassBase 𝕜 ι₁ m = P := by
  apply Subtype.ext
  change secMat (gsFrame P.1.1) * (F₀ * F₀ᴴ) * (secMat (gsFrame P.1.1))ᴴ = P.1.1
  rw [← Matrix.mul_assoc, secMat_mul_baseFrame, Matrix.mul_assoc, ← conjTranspose_mul,
    secMat_mul_baseFrame, gsFrame_mul_conjTranspose P.1.2 P.2.1]

/-- **`U(ι₁ ⊕ Fin m)` acts transitively on the Grassmannian.** -/
theorem exists_unitary_smul_grassBase (P : Grassmannian 𝕜 (ι₁ ⊕ Fin m) m) :
    ∃ g : unitaryGroup (ι₁ ⊕ Fin m) 𝕜, g • grassBase 𝕜 ι₁ m = P := by
  obtain ⟨F, hF, hFP⟩ := exists_frame_of_mem_grassmannian P.2
  obtain ⟨g, hg⟩ := exists_unitary_smul_baseFrame (⟨F, hF⟩ : Stiefel 𝕜 (ι₁ ⊕ Fin m) (Fin m))
  refine ⟨g, ?_⟩
  rw [grassBase, ← frameSpan_smul, hg]
  exact Subtype.ext hFP

omit [DecidableEq ι₁] in
/-- A frame spanning the range of `P₀` is `F₀ S = (0; S)` with `S` unitary. -/
theorem eq_fromRows_of_mul_conjTranspose {F : Matrix (ι₁ ⊕ Fin m) (Fin m) 𝕜} (hF : Fᴴ * F = 1)
    (h : F * Fᴴ = F₀ * F₀ᴴ) : F = fromRows 0 F.toRows₂ ∧ F.toRows₂ᴴ * F.toRows₂ = 1 := by
  have h1 : F = F₀ * (F₀ᴴ * F) := by
    calc F = F * (Fᴴ * F) := by rw [hF, Matrix.mul_one]
      _ = F * Fᴴ * F := by rw [Matrix.mul_assoc]
      _ = F₀ * (F₀ᴴ * F) := by rw [h, Matrix.mul_assoc]
  refine ⟨by rwa [baseFrame_conjTranspose_mul, baseFrame_mul] at h1, ?_⟩
  rw [← baseFrame_conjTranspose_mul]
  calc (F₀ᴴ * F)ᴴ * (F₀ᴴ * F) = Fᴴ * (F₀ * F₀ᴴ) * F := by
        rw [conjTranspose_mul, conjTranspose_conjTranspose]; simp only [Matrix.mul_assoc]
    _ = (Fᴴ * F) * (Fᴴ * F) := by rw [← h]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hF, Matrix.one_mul]

omit [DecidableEq ι₁] in
theorem fromRows_zero_mem_stiefel {S : Matrix (Fin m) (Fin m) 𝕜} (hS : S ∈ unitaryGroup (Fin m) 𝕜) :
    fromRows (0 : Matrix ι₁ (Fin m) 𝕜) S ∈ Stiefel 𝕜 (ι₁ ⊕ Fin m) (Fin m) := by
  rw [mem_stiefel, conjTranspose_mul_self_fromRows, conjTranspose_zero, Matrix.zero_mul,
    zero_add, ← star_eq_conjTranspose]
  exact mem_unitaryGroup_iff'.1 hS

omit [Fintype ι₁] [DecidableEq ι₁] in
theorem fromRows_zero_mul_conjTranspose {S : Matrix (Fin m) (Fin m) 𝕜}
    (hS : S ∈ unitaryGroup (Fin m) 𝕜) :
    fromRows (0 : Matrix ι₁ (Fin m) 𝕜) S * (fromRows (0 : Matrix ι₁ (Fin m) 𝕜) S)ᴴ = F₀ * F₀ᴴ := by
  have hS' : S * Sᴴ = 1 := by rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff.1 hS
  rw [← baseFrame_mul, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc S, hS',
    Matrix.one_mul]

omit [DecidableEq ι₁] in
theorem toRows₂_mem_unitaryGroup_of_mem_fiber
    (F : frameSpan 𝕜 (ι₁ ⊕ Fin m) m ⁻¹' {grassBase 𝕜 ι₁ m}) :
    F.1.1.toRows₂ ∈ unitaryGroup (Fin m) 𝕜 := by
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose]
  exact (eq_fromRows_of_mul_conjTranspose F.1.2 (congrArg Subtype.val F.2)).2

omit [DecidableEq ι₁] in
theorem fromRows_toRows₂_of_mem_fiber (F : frameSpan 𝕜 (ι₁ ⊕ Fin m) m ⁻¹' {grassBase 𝕜 ι₁ m}) :
    fromRows 0 F.1.1.toRows₂ = F.1.1 :=
  (eq_fromRows_of_mul_conjTranspose F.1.2 (congrArg Subtype.val F.2)).1.symm

omit [Fintype ι₁] [DecidableEq ι₁] in
theorem continuous_fromRows_zero :
    Continuous fun S : Matrix (Fin m) (Fin m) 𝕜 => fromRows (0 : Matrix ι₁ (Fin m) 𝕜) S :=
  continuous_matrix fun i j => by
    rcases i with i | i
    · exact continuous_const
    · exact continuous_id.matrix_elem i j

variable (𝕜 ι₁ m) in
/-- **The fibre of `V_m → G_m` over `P₀` is `U(m)`**, `S ↦ F₀ S = (0; S)`. -/
def frameSpanFibreHomeomorph :
    frameSpan 𝕜 (ι₁ ⊕ Fin m) m ⁻¹' {grassBase 𝕜 ι₁ m} ≃ₜ unitaryGroup (Fin m) 𝕜 where
  toFun F := ⟨F.1.1.toRows₂, toRows₂_mem_unitaryGroup_of_mem_fiber F⟩
  invFun S := ⟨⟨fromRows 0 S.1, fromRows_zero_mem_stiefel S.2⟩,
    Subtype.ext (fromRows_zero_mul_conjTranspose S.2)⟩
  left_inv F := Subtype.ext (Subtype.ext (fromRows_toRows₂_of_mem_fiber F))
  right_inv _ := Subtype.ext (toRows₂_fromRows _ _)
  continuous_toFun := Continuous.subtype_mk
    (continuous_toRows₂.comp (continuous_subtype_val.comp continuous_subtype_val)) _
  continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk
    (continuous_fromRows_zero.comp continuous_subtype_val) _) _

omit [DecidableEq ι₁] in
/-- The inclusion of the fibre is `S ↦ (0; S)`. -/
theorem frameSpanFibreHomeomorph_symm_apply (S : unitaryGroup (Fin m) 𝕜) :
    (((frameSpanFibreHomeomorph 𝕜 ι₁ m).symm S : Stiefel 𝕜 (ι₁ ⊕ Fin m) (Fin m)) :
      Matrix (ι₁ ⊕ Fin m) (Fin m) 𝕜) = fromRows 0 (S : Matrix (Fin m) (Fin m) 𝕜) :=
  rfl

omit [DecidableEq ι₁] in
/-- **The frame-to-span map `V_m(𝕜^{ι₁ ⊕ Fin m}) → G_m(𝕜^{ι₁ ⊕ Fin m})` is a fibre bundle with
fibre `U(m)`** (Milnor p. 129, after Steenrod §7): every point of the Grassmannian has an open
neighbourhood `U` with `frameSpan⁻¹(U) ≅ U × U(m)` over `U`. -/
theorem frameSpan_locallyTrivial (b : Grassmannian 𝕜 (ι₁ ⊕ Fin m) m) :
    ∃ U : Set (Grassmannian 𝕜 (ι₁ ⊕ Fin m) m), IsOpen U ∧ b ∈ U ∧
      ∃ φ : frameSpan 𝕜 (ι₁ ⊕ Fin m) m ⁻¹' U ≃ₜ U × unitaryGroup (Fin m) 𝕜,
        ∀ x, (φ x).1 = ⟨frameSpan 𝕜 (ι₁ ⊕ Fin m) m x, x.2⟩ := by
  classical
  exact exists_triv_of_orbitSection' _ continuous_frameSpan frameSpan_smul (grassBase 𝕜 ι₁ m)
    exists_unitary_smul_grassBase isOpen_grassDomain grassBase_mem_grassDomain grassSection
    continuous_grassSection grassSection_smul (frameSpanFibreHomeomorph 𝕜 ι₁ m) b

end Bundle

end Morse.Homotopy
