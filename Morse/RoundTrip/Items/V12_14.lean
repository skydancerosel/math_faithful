import Morse
import RoundTrip.Check
import RoundTrip.Blind.V12_14
import RoundTrip.Bridge

/-!
# V12_14 (Milnor §21, p. 112; §23, p. 125 (6)): bi-invariant metrics; the tangent space of `U(n)`

`A` (universes `0`): the project's Euclidean model of matrix groups.  `⟪A, B⟫ = Re tr(Aᴴ B)` on `Mₙ(𝕜)`
(`inner_def`; `MatrixInner.innerProductSpace` is vocabulary); left and right multiplication by a unitary matrix
preserve it (`inner_mul_left_of_unitary`, `inner_mul_right_of_unitary`); `exp X` is unitary for skew-Hermitian `X`
(`exp_conjTranspose_mul_exp_of_skew`); for a matrix group `G` (`Morse.IsMatrixGroup hG 𝔤`, vocabulary: a slice
submanifold `G ⊆ U(n)` closed under products and `ᴴ`, `Ad G`-invariant `𝔤` of skew-Hermitian matrices,
`exp 𝔤 ⊆ G`, `dim G = dim 𝔤`) the tangent space at `g` is `g·𝔤` (`tangentSubspace_eq`) and left/right translations
are linear isometries of `Mₙ(𝕜)` preserving `G` (`mulLeftIso_image`, `mulRightIso_image`); the Frobenius form on
`𝔤` (`frobForm`, vocabulary) is ad-invariant (`isAdInvariant_frobForm`) and positive (`frobForm_pos`).

`B` (blind): (1) every compact Lie group (abstract, Mathlib `LieGroup`) carries a smooth bi-invariant Riemannian
metric; (2) for every `k`, the velocities at `0` of `C^∞` curves in `U(k)` through `I` are exactly the
skew-Hermitian matrices.

* `A → B` fails: (1) needs Haar-measure averaging on an arbitrary compact Lie group; `A` only has matrix groups,
  whose metric is induced from `Mₙ(𝕜)`.  But `A → B.2` is proved (`A_to_B2`): `⊆` by the project's
  `hasDerivAt_mem_tangentSubspace` and `A`'s `tangentSubspace_eq` for `U(k)` (`Morse.isMatrixGroup_unitaryGroup`),
  `⊇` by the curves `t ↦ exp(tX)` (`A`'s `exp_conjTranspose_mul_exp_of_skew`); the blind derivative (entrywise
  norm) and the project's (Frobenius norm) are transported (`contDiff_elem_of_frob`; `HasDerivAt` only depends on
  the topology, which is the same).
* `B → A` fails: `B` says nothing about the Frobenius inner product, matrix groups as submanifolds or `frobForm`.

## The embedded special case

`B_emb`: `B`'s (1) for a matrix group `G` (model `ℝᵐ`) as `Bridge.Sub hG` with its group structure (`grp`,
`lieGroup`), together with `B`'s (2) (already concrete).  `B → B_emb` and `A → B_emb` are proved: the induced
metric `Bridge.metric` is smooth and bi-invariant (`biInv`: the differential of `L_g`, read in `Mₙ(𝕜)`, is
`X ↦ gX`, and `A`'s `inner_mul_left_of_unitary` / `inner_mul_right_of_unitary` apply).
-/

open Matrix Set Filter Topology Module
open scoped Morse.MatrixInner RealInnerProductSpace Manifold ContDiff
open Bundle

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace RoundTrip.V12_14

/-- The project's statement (universes `0`). -/
def A : Prop :=
  type_of% @Morse.inner_def.{0,0} ∧
    type_of% @Morse.inner_mul_left_of_unitary.{0,0} ∧
    type_of% @Morse.inner_mul_right_of_unitary.{0,0} ∧
    type_of% @Morse.exp_conjTranspose_mul_exp_of_skew.{0,0} ∧
    type_of% @Morse.IsMatrixGroup.tangentSubspace_eq.{0,0,0,0} ∧
    type_of% @Morse.IsMatrixGroup.mulLeftIso_image.{0,0,0,0} ∧
    type_of% @Morse.IsMatrixGroup.mulRightIso_image.{0,0,0,0} ∧
    type_of% @Morse.isAdInvariant_frobForm.{0,0} ∧
    type_of% @Morse.frobForm_pos.{0,0}

theorem A_holds : A :=
  ⟨@Morse.inner_def, @Morse.inner_mul_left_of_unitary, @Morse.inner_mul_right_of_unitary,
    @Morse.exp_conjTranspose_mul_exp_of_skew, @Morse.IsMatrixGroup.tangentSubspace_eq,
    @Morse.IsMatrixGroup.mulLeftIso_image, @Morse.IsMatrixGroup.mulRightIso_image,
    @Morse.isAdInvariant_frobForm, @Morse.frobForm_pos⟩

/-! ## `B`'s (2) from `A` -/

/-- A `C^∞` curve for the Frobenius norm is `C^∞` for the entrywise norm of the blind file (the identity
`Mₖ(ℂ) → Mₖ(ℂ)` is a continuous linear map between the two normed structures, which have the same
topology). -/
theorem contDiff_elem_of_frob {k : ℕ} {c : ℝ → Matrix (Fin k) (Fin k) ℂ}
    (hc : @ContDiff ℝ _ ℝ _ _ (Matrix (Fin k) (Fin k) ℂ) Morse.MatrixInner.normedAddCommGroup
      Morse.MatrixInner.normedSpace ∞ c) :
    @ContDiff ℝ _ ℝ _ _ (Matrix (Fin k) (Fin k) ℂ) Matrix.normedAddCommGroup Matrix.normedSpace ∞ c :=
  @ContDiff.comp ℝ ℝ (Matrix (Fin k) (Fin k) ℂ) (Matrix (Fin k) (Fin k) ℂ) _ _ _
    Morse.MatrixInner.normedAddCommGroup Morse.MatrixInner.normedSpace
    Matrix.normedAddCommGroup Matrix.normedSpace ∞ _ _
  (@ContinuousLinearMap.contDiff ℝ (Matrix (Fin k) (Fin k) ℂ) (Matrix (Fin k) (Fin k) ℂ) _
    Morse.MatrixInner.normedAddCommGroup
    Morse.MatrixInner.normedSpace Matrix.normedAddCommGroup Matrix.normedSpace ∞
    (ContinuousLinearMap.id ℝ (Matrix (Fin k) (Fin k) ℂ))) hc

/-- `U(k)` with `𝔲(k)` is a matrix group (the project's `isMatrixGroup_unitaryGroup`, re-proved with `A`'s
`exp_conjTranspose_mul_exp_of_skew` as hypothesis). -/
theorem isMatrixGroup_U {k : ℕ}
    (hexp : ∀ {X : Matrix (Fin k) (Fin k) ℂ}, Xᴴ = -X → (NormedSpace.exp X)ᴴ * NormedSpace.exp X = 1) :
    Morse.IsMatrixGroup (Morse.isSliceSubmanifold_unitaryGroup (𝕜 := ℂ) (ι := Fin k))
      (Morse.skewHermitian ℂ (Fin k)) where
  unitary g hg := Morse.mem_unitaryGroup_iff_conjTranspose.1 hg
  mul_mem g hg h hh := Submonoid.mul_mem _ hg hh
  star_mem g hg := by
    rw [← star_eq_conjTranspose]
    exact Unitary.star_mem hg
  skew X hX := hX
  conj_mem g hg X hX := by
    rw [Morse.mem_skewHermitian, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      Morse.mem_skewHermitian.1 hX]
    noncomm_ring
  exp_mem X hX := Morse.mem_unitaryGroup_iff_conjTranspose.2 (hexp hX)
  finrank_eq := rfl

/-- **Bridge**: `A` gives `B`'s (2), the tangent space of `U(k)` at `I`. -/
theorem A_to_B2 (hA : A) :
    ∀ k : ℕ, unitaryTangentAtOne k = {A : Matrix (Fin k) (Fin k) ℂ | A.conjTranspose = -A} := by
  obtain ⟨-, -, -, hexp, htan, -⟩ := hA
  intro k
  ext X
  constructor
  · rintro ⟨c, -, hcU, hc0, hcd⟩
    have hd : HasDerivAt c X 0 := hcd
    have hmem : ∀ᶠ s in 𝓝 (0 : ℝ), c s ∈ (Matrix.unitaryGroup (Fin k) ℂ : Set (Matrix (Fin k) (Fin k) ℂ)) :=
      Eventually.of_forall hcU
    have hT := Morse.hasDerivAt_mem_tangentSubspace
      (Morse.isSliceSubmanifold_unitaryGroup (𝕜 := ℂ) (ι := Fin k)) hd hmem
    rw [htan (isMatrixGroup_U hexp), Morse.IsMatrixGroup.mem_leftAlg_iff] at hT
    change (c 0)ᴴ * X ∈ Morse.skewHermitian ℂ (Fin k) at hT
    rw [hc0, conjTranspose_one, Matrix.one_mul] at hT
    exact hT
  · intro hX
    refine ⟨fun t => NormedSpace.exp (t • X), contDiff_elem_of_frob (Morse.contDiff_exp_smul X),
      fun t => ?_, by simp, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]
      refine hexp ?_
      change (t • X)ᴴ = -(t • X)
      rw [conjTranspose_smul, star_trivial, hX, smul_neg]
    · have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
      simp only [zero_smul, NormedSpace.exp_zero, Matrix.one_mul] at h
      exact h

/-! ## The embedded special case -/

namespace Emb
open RoundTrip.Bridge
open RoundTrip.Bridge

variable {𝕜 : Type} [RCLike 𝕜] {k m : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W]
  {G : Set (Matrix (Fin k) (Fin k) 𝕜)}
  {hG : Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix (Fin k) (Fin k) 𝕜) (Rn m) W G}
  {𝔤 : LieSubalgebra ℝ (Matrix (Fin k) (Fin k) 𝕜)}

/-- The group structure of `G` on `↥G = Bridge.Sub hG`. -/
@[reducible] def grp (h : Morse.IsMatrixGroup hG 𝔤) : Group (Bridge.Sub hG) where
  mul a b := (⟨a.1 * b.1, h.mul_mem _ a.2 _ b.2⟩ : G)
  one := (⟨1, h.one_mem⟩ : G)
  inv a := (⟨a.1ᴴ, h.star_mem _ a.2⟩ : G)
  mul_assoc a b c := Subtype.ext (Matrix.mul_assoc _ _ _)
  one_mul a := Subtype.ext (Matrix.one_mul _)
  mul_one a := Subtype.ext (Matrix.mul_one _)
  inv_mul_cancel a := Subtype.ext (h.unitary _ a.2)

theorem incl_mul (h : Morse.IsMatrixGroup hG 𝔤) (a b : Bridge.Sub hG) :
    incl hG (@HMul.hMul _ _ _ (@instHMul _ (grp h).toMul) a b) = incl hG a * incl hG b := rfl

theorem incl_inv (h : Morse.IsMatrixGroup hG 𝔤) (a : Bridge.Sub hG) :
    incl hG (@Inv.inv _ (grp h).toInv a) = (incl hG a)ᴴ := rfl

theorem incl_one (h : Morse.IsMatrixGroup hG 𝔤) :
    incl hG (@OfNat.ofNat _ 1 (@One.toOfNat1 _ (grp h).toOne)) = 1 := rfl

theorem lieGroup (h : Morse.IsMatrixGroup hG 𝔤) :
    @LieGroup ℝ _ (Rn m) _ (Rn m) _ _ 𝓘(ℝ, Rn m) ∞ (Bridge.Sub hG) (grp h) _ _ := by
  letI := grp h
  refine { contMDiff_mul := ?_, contMDiff_inv := ?_ }
  · have hF : ContMDiff (𝓘(ℝ, Rn m).prod 𝓘(ℝ, Rn m)) 𝓘(ℝ, Matrix (Fin k) (Fin k) 𝕜) ∞
        (fun p : Bridge.Sub hG × Bridge.Sub hG => incl hG p.1 * incl hG p.2) := by
      have h1 : ContMDiff (𝓘(ℝ, Rn m).prod 𝓘(ℝ, Rn m)) 𝓘(ℝ, Matrix (Fin k) (Fin k) 𝕜) ∞
          (fun p : Bridge.Sub hG × Bridge.Sub hG => incl hG p.1) := contMDiff_incl.comp contMDiff_fst
      have h2 : ContMDiff (𝓘(ℝ, Rn m).prod 𝓘(ℝ, Rn m)) 𝓘(ℝ, Matrix (Fin k) (Fin k) 𝕜) ∞
          (fun p : Bridge.Sub hG × Bridge.Sub hG => incl hG p.2) := contMDiff_incl.comp contMDiff_snd
      exact (contDiff_mul (𝕜 := ℝ) (𝔸 := Matrix (Fin k) (Fin k) 𝕜)).contMDiff.comp (h1.prodMk_space h2)
    exact hG.contMDiff_codRestrict hF (fun p => h.mul_mem _ p.1.2 _ p.2.2)
  · have hF : ContMDiff 𝓘(ℝ, Rn m) 𝓘(ℝ, Matrix (Fin k) (Fin k) 𝕜) ∞
        (fun p : Bridge.Sub hG => (incl hG p)ᴴ) :=
      (Morse.conjTransposeCLM (𝕜 := 𝕜) (ι := Fin k)).contDiff.contMDiff.comp contMDiff_incl
    exact hG.contMDiff_codRestrict hF (fun p => h.star_mem _ p.2)

/-- The derivative of a map `f : G → G` induced by an ambient map `F`, read in the ambient space:
`D_{f x} (df_x u) = dF_x (D_x u)`. -/
theorem D_mfderiv_lift {f : Bridge.Sub hG → Bridge.Sub hG}
    {F : Matrix (Fin k) (Fin k) 𝕜 → Matrix (Fin k) (Fin k) 𝕜} (x : Bridge.Sub hG)
    (hF : DifferentiableAt ℝ F (incl hG x)) (hfF : ∀ y, incl hG (f y) = F (incl hG y))
    (hf : MDifferentiableAt 𝓘(ℝ, Rn m) 𝓘(ℝ, Rn m) f x) (u : TangentSpace 𝓘(ℝ, Rn m) x) :
    D hG (f x) (mfderiv 𝓘(ℝ, Rn m) 𝓘(ℝ, Rn m) f x u) = fderiv ℝ F (incl hG x) (D hG x u) := by
  have e : incl hG ∘ f = F ∘ incl hG := funext hfF
  have hi : ∀ y : Bridge.Sub hG, MDifferentiableAt 𝓘(ℝ, Rn m) 𝓘(ℝ, Matrix (Fin k) (Fin k) 𝕜)
      (incl hG) y := fun y => contMDiff_incl.mdifferentiableAt (by simp)
  have h1 := mfderiv_comp x (hi (f x)) hf
  have h2 := mfderiv_comp x hF.mdifferentiableAt (hi x)
  rw [e, h2, mfderiv_eq_fderiv] at h1
  have := congrArg (fun L : Rn m →L[ℝ] Matrix (Fin k) (Fin k) 𝕜 => L u) h1
  exact this.symm

omit [FiniteDimensional ℝ W] in
theorem fderiv_mul_left' (a x w : Matrix (Fin k) (Fin k) 𝕜) :
    fderiv ℝ (fun y => a * y) x w = a * w := by
  have h : HasFDerivAt (fun y => a * y) (ContinuousLinearMap.mul ℝ (Matrix (Fin k) (Fin k) 𝕜) a) x :=
    (ContinuousLinearMap.mul ℝ (Matrix (Fin k) (Fin k) 𝕜) a).hasFDerivAt
  rw [h.fderiv]; rfl

omit [FiniteDimensional ℝ W] in
theorem fderiv_mul_right' (a x w : Matrix (Fin k) (Fin k) 𝕜) :
    fderiv ℝ (fun y => y * a) x w = w * a := by
  have h : HasFDerivAt (fun y => y * a)
      ((ContinuousLinearMap.mul ℝ (Matrix (Fin k) (Fin k) 𝕜)).flip a) x :=
    ((ContinuousLinearMap.mul ℝ (Matrix (Fin k) (Fin k) 𝕜)).flip a).hasFDerivAt
  rw [h.fderiv]; rfl

/-- Left and right translations of `G` are isometries of the induced metric. -/
theorem biInv (h : Morse.IsMatrixGroup hG 𝔤)
    (hL : ∀ U : Matrix (Fin k) (Fin k) 𝕜, Uᴴ * U = 1 → ∀ A B, ⟪U * A, U * B⟫ = ⟪A, B⟫)
    (hR : ∀ U : Matrix (Fin k) (Fin k) 𝕜, U * Uᴴ = 1 → ∀ A B, ⟪A * U, B * U⟫ = ⟪A, B⟫) :
    letI := grp h; haveI := lieGroup h; BiInvMetric m (Bridge.Sub hG) := by
  letI := grp h; haveI := lieGroup h
  constructor
  · intro g x u v
    have hd : ∀ w : TangentSpace 𝓘(ℝ, Rn m) x, D hG (g * x) (mfderiv 𝓘(ℝ, Rn m) 𝓘(ℝ, Rn m)
        (fun y => g * y) x w) = incl hG g * D hG x w := fun w => by
      rw [D_mfderiv_lift (F := fun y => incl hG g * y) x
        ((ContinuousLinearMap.mul ℝ (Matrix (Fin k) (Fin k) 𝕜) (incl hG g)).differentiableAt)
        (fun y => rfl) ((contMDiff_mul_left (I := 𝓘(ℝ, Rn m)) (n := ∞) (a := g)).mdifferentiableAt
          (by simp)), fderiv_mul_left']
    rw [inner_eq, inner_eq, hd, hd]
    exact hL _ (h.unitary _ g.2) _ _
  · intro g x u v
    have hd : ∀ w : TangentSpace 𝓘(ℝ, Rn m) x, D hG (x * g) (mfderiv 𝓘(ℝ, Rn m) 𝓘(ℝ, Rn m)
        (fun y => y * g) x w) = D hG x w * incl hG g := fun w => by
      rw [D_mfderiv_lift (F := fun y => y * incl hG g) x
        (((ContinuousLinearMap.mul ℝ (Matrix (Fin k) (Fin k) 𝕜)).flip (incl hG g)).differentiableAt)
        (fun y => rfl) ((contMDiff_mul_right (I := 𝓘(ℝ, Rn m)) (n := ∞) (a := g)).mdifferentiableAt
          (by simp)), fderiv_mul_right']
    rw [inner_eq, inner_eq, hd, hd]
    exact hR _ (Morse.mul_conjTranspose_eq_one (h.unitary _ g.2)) _ _


end Emb

open Emb

/-- `B` with its claim (1) specialized to a matrix group `G ⊆ Mₖ(𝕜)` modelled on `ℝᵐ`, as `Bridge.Sub hG`
with its group structure; claim (2) unchanged. -/
def B_emb : Prop :=
  (∀ (𝕜 : Type) [RCLike 𝕜] (k m : ℕ) (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] (G : Set (Matrix (Fin k) (Fin k) 𝕜))
    (hG : Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix (Fin k) (Fin k) 𝕜) (Rn m) W G)
    (𝔤 : LieSubalgebra ℝ (Matrix (Fin k) (Fin k) 𝕜)) (h : Morse.IsMatrixGroup hG 𝔤),
    letI := grp h; haveI := lieGroup h
    CompactSpace (Bridge.Sub hG) →
      ∃ (_ : Bundle.RiemannianBundle (fun x : Bridge.Sub hG => TangentSpace 𝓘(ℝ, Rn m) x)),
        IsContMDiffRiemannianBundle 𝓘(ℝ, Rn m) ∞ (Rn m)
          (fun x : Bridge.Sub hG => TangentSpace 𝓘(ℝ, Rn m) x) ∧ BiInvMetric m (Bridge.Sub hG)) ∧
  (∀ k : ℕ, unitaryTangentAtOne k = {A : Matrix (Fin k) (Fin k) ℂ | A.conjTranspose = -A})

theorem B_to_B_emb : B → B_emb := by
  intro hB
  refine ⟨fun 𝕜 _ k m W _ _ _ G hG 𝔤 h => ?_, hB.2⟩
  letI := grp h; haveI := lieGroup h
  exact fun hc => hB.1 m (Bridge.Sub hG) hc

theorem A_to_B_emb : A → B_emb := by
  intro hA
  refine ⟨fun 𝕜 _ k m W _ _ _ G hG 𝔤 h => ?_, A_to_B2 hA⟩
  letI := grp h; haveI := lieGroup h
  exact fun _ => ⟨inferInstance, inferInstance,
    biInv h (fun _ hU => hA.2.1 hU) (fun _ hU => hA.2.2.1 hU)⟩

#rt_check_soft RoundTrip.V12_14.A_to_B2 [Morse.inner_def, Morse.inner_mul_left_of_unitary,
  Morse.inner_mul_right_of_unitary, Morse.exp_conjTranspose_mul_exp_of_skew,
  Morse.IsMatrixGroup.tangentSubspace_eq, Morse.IsMatrixGroup.mulLeftIso_image,
  Morse.IsMatrixGroup.mulRightIso_image, Morse.isAdInvariant_frobForm, Morse.frobForm_pos]
#rt_check_soft RoundTrip.V12_14.A_to_B_emb [Morse.inner_def, Morse.inner_mul_left_of_unitary,
  Morse.inner_mul_right_of_unitary, Morse.exp_conjTranspose_mul_exp_of_skew,
  Morse.IsMatrixGroup.tangentSubspace_eq, Morse.IsMatrixGroup.mulLeftIso_image,
  Morse.IsMatrixGroup.mulRightIso_image, Morse.isAdInvariant_frobForm, Morse.frobForm_pos]
#rt_check RoundTrip.V12_14.B_to_B_emb [Morse.inner_def, Morse.inner_mul_left_of_unitary,
  Morse.inner_mul_right_of_unitary, Morse.exp_conjTranspose_mul_exp_of_skew,
  Morse.IsMatrixGroup.tangentSubspace_eq, Morse.IsMatrixGroup.mulLeftIso_image,
  Morse.IsMatrixGroup.mulRightIso_image, Morse.isAdInvariant_frobForm, Morse.frobForm_pos]
#rt_overlap RoundTrip.V12_14.A_to_B_emb [Morse.inner_def, Morse.inner_mul_left_of_unitary,
  Morse.inner_mul_right_of_unitary, Morse.exp_conjTranspose_mul_exp_of_skew,
  Morse.IsMatrixGroup.tangentSubspace_eq, Morse.IsMatrixGroup.mulLeftIso_image,
  Morse.IsMatrixGroup.mulRightIso_image, Morse.isAdInvariant_frobForm, Morse.frobForm_pos]

end RoundTrip.V12_14
