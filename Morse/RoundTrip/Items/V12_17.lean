import Morse
import RoundTrip.Check
import RoundTrip.Blind.V12_17
import RoundTrip.Bridge

/-!
# V12_17 (Milnor §21, Theorem 21.3 and Corollary 21.4)

`A` (universes `0`): the project's matrix-group version, for `G ⊆ U(n)` a slice submanifold of `Mₙ(𝕜)`
(`Morse.IsMatrixGroup hG 𝔤`) with the induced metric, computed in the embedding: 21.3(a) for skew-Hermitian
matrices (`inner_lie_left`), the Gauss-equation trace identity (`inner_gauss_identity`), `P_g(M) = g P_𝔤(gᴴM)`
(`tanProj_eq`), `II_g(gX, gY) = ½ g(XY + YX)` (`secondFundForm_mul`), (d) `∇_{gX}(q ↦ qY) = g·½[X,Y]`
(`covAt_mul_right`), (b) `R(gX,gY)gZ = ¼ g[[X,Y],Z]` (`curvOp_mul`, `curvOp_eq_curv_halfLie`), (c)
(`inner_curvOp_mul`), 21.4 (`sectional_mul`, `sectional_mul_nonneg`, incl. `= 0 ⇔ [X,Y] = 0`) and
`R(gA,gW)gA = g K_A(W)` (`curvOp_eq_jacobiOp`).

`B` (blind): for every abstract Lie group with a bi-invariant metric and every Levi-Civita connection,
(a)–(d) and 21.4 for left-invariant fields `X_u = mulInvariantVectorField u`, as fields / pointwise.

Neither direction is proved: `B` is about abstract Lie groups with an arbitrary bi-invariant metric, `A` about
matrix groups with the induced metric (where `A` has more: the second fundamental form, the Gauss identity,
the `= 0 ⇔ [X,Y] = 0` half of 21.4, `K_A`).

## The embedded special case

`B_emb`: `B` for a matrix group `G` with model `ℝᵐ`, as `Bridge.Sub hG` with its group structure (`grp`,
`lieGroup`), the induced metric (bi-invariant, `biInv`) and the induced connection `Bridge.conn`.
`B → B_emb` and `A → B_emb` are proved.  Dictionary (`LieDict`): the left-invariant field `X_u` of Mathlib is,
in `Mₙ(𝕜)`, `q ↦ q U₀` with `U₀ = D₁u ∈ 𝔤` (`D_liv`, `U0_mem`); its bracket is `q ↦ q[U₀,V₀]`
(`D_bracket_liv`, from the Bridge's `D_mlieBracket`); and `X_u ⊢ X_v` is the project's `covAt` of `q ↦ qV₀`
in the direction `pU₀` (Bridge's `D_conn_apply`).  Then (d) is `A`'s `covAt_mul_right`, (a) is `A`'s
`inner_lie_left` (after the unitary invariance of the inner product), and (b), (c), 21.4 follow from (d), (a)
and Mathlib's `[X_u, X_v] = X_⁅u,v⁆` by the algebra of `Morse.curv (Morse.halfLie 𝔤)` (`curv_halfLie`, as in
V12_5).  So `A`'s Gauss-equation route to (b) (`curvOp_mul`) is not needed for `B_emb`.
-/

open Matrix Set Filter Topology Module
open scoped Morse.MatrixInner RealInnerProductSpace Manifold ContDiff
open Bundle

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace RoundTrip.V12_17

/-- The project's statement (universes `0`). -/
def A : Prop :=
  type_of% @Morse.inner_lie_left.{0,0} ∧
    type_of% @Morse.inner_gauss_identity.{0,0} ∧
    type_of% @Morse.IsMatrixGroup.tanProj_eq.{0,0,0,0} ∧
    type_of% @Morse.IsMatrixGroup.secondFundForm_mul.{0,0,0,0} ∧
    type_of% @Morse.IsMatrixGroup.covAt_mul_right.{0,0,0,0} ∧
    type_of% @Morse.IsMatrixGroup.curvOp_mul.{0,0,0,0} ∧
    type_of% @Morse.IsMatrixGroup.inner_curvOp_mul.{0,0,0,0} ∧
    type_of% @Morse.IsMatrixGroup.sectional_mul.{0,0,0,0} ∧
    type_of% @Morse.IsMatrixGroup.sectional_mul_nonneg.{0,0,0,0} ∧
    type_of% @Morse.IsMatrixGroup.curvOp_eq_curv_halfLie.{0,0,0,0} ∧
    type_of% @Morse.IsMatrixGroup.curvOp_eq_jacobiOp.{0,0,0,0}

theorem A_holds : A :=
  ⟨@Morse.inner_lie_left, @Morse.inner_gauss_identity, @Morse.IsMatrixGroup.tanProj_eq,
    @Morse.IsMatrixGroup.secondFundForm_mul, @Morse.IsMatrixGroup.covAt_mul_right,
    @Morse.IsMatrixGroup.curvOp_mul, @Morse.IsMatrixGroup.inner_curvOp_mul,
    @Morse.IsMatrixGroup.sectional_mul, @Morse.IsMatrixGroup.sectional_mul_nonneg,
    @Morse.IsMatrixGroup.curvOp_eq_curv_halfLie, @Morse.IsMatrixGroup.curvOp_eq_jacobiOp⟩

/-! ## Left-invariant fields on an abstract Lie group (from V12_1 / V12_5) -/

namespace Dict

variable {n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace (Rn n) G]
  [LieGroup 𝓘(ℝ, Rn n) ∞ G]

theorem liv_bracket (u v : GroupLieAlgebra 𝓘(ℝ, Rn n) G) :
    VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv u) (liv v) = liv ⁅u, v⁆ :=
  (mulInvariantVector_mlieBracket u v).symm

theorem mdiffAt_liv (v : GroupLieAlgebra 𝓘(ℝ, Rn n) G) (p : G) :
    MDifferentiableAt 𝓘(ℝ, Rn n) (𝓘(ℝ, Rn n)).tangent
      (fun q => (⟨q, liv v q⟩ : TangentBundle 𝓘(ℝ, Rn n) G)) p :=
  mdifferentiableAt_mulInvariantVectorField v

theorem liv_add (a b : GroupLieAlgebra 𝓘(ℝ, Rn n) G) : liv (a + b) = liv a + liv b :=
  mulInvariantVectorField_add a b

theorem liv_smul (c : ℝ) (a : GroupLieAlgebra 𝓘(ℝ, Rn n) G) : liv (c • a) = c • liv a :=
  mulInvariantVectorField_smul c a

theorem liv_neg (a : GroupLieAlgebra 𝓘(ℝ, Rn n) G) : liv (-a) = -liv a := by
  rw [← neg_one_smul ℝ a, liv_smul, neg_one_smul]

/-- Under Milnor's (d), `curvF cov X_u X_v X_w` is the left-invariant field of the project's algebraic
`Morse.curv (Morse.halfLie 𝔤) u v w` (V12_5). -/
theorem curvF_liv_of_d (cov : Conn n G)
    (hd : ∀ a b : GroupLieAlgebra 𝓘(ℝ, Rn n) G,
      covF cov (liv a) (liv b) = (1 / 2 : ℝ) • VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv a) (liv b))
    (u v w : GroupLieAlgebra 𝓘(ℝ, Rn n) G) :
    curvF cov (liv u) (liv v) (liv w) =
      liv (Morse.curv (Morse.halfLie (GroupLieAlgebra 𝓘(ℝ, Rn n) G)) u v w) := by
  have hd' : ∀ a b : GroupLieAlgebra 𝓘(ℝ, Rn n) G,
      covF cov (liv a) (liv b) = liv (Morse.halfLie (GroupLieAlgebra 𝓘(ℝ, Rn n) G) a b) := by
    intro a b; rw [hd, liv_bracket, Morse.halfLie_apply, liv_smul]
  have e : curvF cov (liv u) (liv v) (liv w) = covF cov (liv v) (covF cov (liv u) (liv w))
      - covF cov (liv u) (covF cov (liv v) (liv w))
      + covF cov (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv u) (liv v)) (liv w) := rfl
  rw [e, hd' u w, hd' v w, hd' v, hd' u, liv_bracket, hd', Morse.curv, liv_add, liv_add, liv_neg]
  abel

end Dict

open Dict

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


/-! ### Left-invariant fields of `G`, read in `Mₙ(𝕜)` -/

section LieDict

variable [Group (Bridge.Sub hG)] [LieGroup 𝓘(ℝ, Rn m) ∞ (Bridge.Sub hG)]
  (hmul : ∀ a b : Bridge.Sub hG, incl hG (a * b) = incl hG a * incl hG b)
include hmul

/-- `X_u(g) = g U₀`, `U₀ = D₁u`. -/
theorem D_liv (u : GroupLieAlgebra 𝓘(ℝ, Rn m) (Bridge.Sub hG)) (g : Bridge.Sub hG) :
    D hG g (liv u g) = incl hG g * D hG 1 u := by
  have e : D hG g = D hG (g * 1) := by rw [mul_one]
  rw [e]
  exact (D_mfderiv_lift (F := fun y => incl hG g * y) 1
    ((ContinuousLinearMap.mul ℝ (Matrix (Fin k) (Fin k) 𝕜) (incl hG g)).differentiableAt)
    (fun y => hmul g y) ((contMDiff_mul_left (I := 𝓘(ℝ, Rn m)) (n := ∞) (a := g)).mdifferentiableAt
      (by simp)) u).trans (fderiv_mul_left' _ _ _)

theorem amb_liv (u : GroupLieAlgebra 𝓘(ℝ, Rn m) (Bridge.Sub hG)) :
    amb (liv u) = fun q : Bridge.Sub hG => incl hG q * D hG 1 u :=
  funext fun q => D_liv hmul u q

theorem dV_amb_liv (v : GroupLieAlgebra 𝓘(ℝ, Rn m) (Bridge.Sub hG)) (p : Bridge.Sub hG)
    (w : TangentSpace 𝓘(ℝ, Rn m) p) : dV (amb (liv v)) p w = D hG p w * D hG 1 v := by
  have e : amb (liv v) = (fun y => y * D hG 1 v) ∘ incl hG := amb_liv hmul v
  have hd : MDifferentiableAt 𝓘(ℝ, Matrix (Fin k) (Fin k) 𝕜) 𝓘(ℝ, Matrix (Fin k) (Fin k) 𝕜)
      (fun y => y * D hG 1 v) (incl hG p) :=
    (((ContinuousLinearMap.mul ℝ (Matrix (Fin k) (Fin k) 𝕜)).flip (D hG 1 v)).differentiableAt
      (x := incl hG p)).mdifferentiableAt
  rw [dV, e, mfderiv_comp p hd (contMDiff_incl.mdifferentiableAt (by simp)), mfderiv_eq_fderiv]
  exact fderiv_mul_right' _ _ _

/-- `[X_u, X_v](p) = p[U₀, V₀]`. -/
theorem D_bracket_liv (u v : GroupLieAlgebra 𝓘(ℝ, Rn m) (Bridge.Sub hG)) (p : Bridge.Sub hG) :
    D hG p (VectorField.mlieBracket 𝓘(ℝ, Rn m) (liv u) (liv v) p) =
      incl hG p * (D hG 1 u * D hG 1 v - D hG 1 v * D hG 1 u) := by
  rw [D_mlieBracket p _ _ (mdiffAt_liv u p) (mdiffAt_liv v p), dV_amb_liv hmul, dV_amb_liv hmul,
    D_liv hmul, D_liv hmul, Matrix.mul_sub, Matrix.mul_assoc, Matrix.mul_assoc]

theorem U0_mem (hone : incl hG (1 : Bridge.Sub hG) = 1) (h : Morse.IsMatrixGroup hG 𝔤)
    (u : GroupLieAlgebra 𝓘(ℝ, Rn m) (Bridge.Sub hG)) : D hG 1 u ∈ 𝔤 := by
  have := (h.mem_tangentSubspace_iff (1 : Bridge.Sub hG)).1 (D_mem 1 u)
  change (incl hG 1)ᴴ * D hG 1 u ∈ 𝔤 at this
  rwa [hone, conjTranspose_one, Matrix.one_mul] at this

/-- (d) on `G`, from `A`'s `covAt_mul_right`. -/
theorem d_liv (hone : incl hG (1 : Bridge.Sub hG) = 1) (h : Morse.IsMatrixGroup hG 𝔤)
    (hC : ∀ (g : G) {X Y : Matrix (Fin k) (Fin k) 𝕜}, X ∈ 𝔤 → Y ∈ 𝔤 →
      Morse.covAt hG g (g.1 * X) (fun q : G => q.1 * Y) = g.1 * ((1 / 2 : ℝ) • (X * Y - Y * X)))
    (u v : GroupLieAlgebra 𝓘(ℝ, Rn m) (Bridge.Sub hG)) :
    covF (Bridge.conn (hN := hG)) (liv u) (liv v) =
      (1 / 2 : ℝ) • VectorField.mlieBracket 𝓘(ℝ, Rn m) (liv u) (liv v) := by
  funext p
  apply D_injective p
  have h1 : D hG p (covF (Bridge.conn (hN := hG)) (liv u) (liv v) p) =
      Morse.covAt hG p (D hG p (liv u p)) (amb (liv v)) := D_conn_apply (liv v) p (liv u p)
  rw [h1, D_liv hmul, amb_liv hmul]
  refine (hC p (U0_mem hmul hone h u) (U0_mem hmul hone h v)).trans ?_
  have e2 : D hG p (((1 / 2 : ℝ) • VectorField.mlieBracket 𝓘(ℝ, Rn m) (liv u) (liv v)) p) =
      (1 / 2 : ℝ) • D hG p (VectorField.mlieBracket 𝓘(ℝ, Rn m) (liv u) (liv v) p) :=
    (D hG p).map_smul _ _
  rw [e2, D_bracket_liv hmul, Matrix.mul_smul]
  rfl

/-- (a) on `G`, from `A`'s `inner_lie_left`. -/
theorem a_liv (hone : incl hG (1 : Bridge.Sub hG) = 1) (h : Morse.IsMatrixGroup hG 𝔤)
    (hI : ∀ {X Y Z : Matrix (Fin k) (Fin k) 𝕜}, Xᴴ = -X → Yᴴ = -Y →
      ⟪X * Y - Y * X, Z⟫ = ⟪X, Y * Z - Z * Y⟫)
    (u v w : GroupLieAlgebra 𝓘(ℝ, Rn m) (Bridge.Sub hG)) (p : Bridge.Sub hG) :
    @inner ℝ (TangentSpace 𝓘(ℝ, Rn m) p) _ (VectorField.mlieBracket 𝓘(ℝ, Rn m) (liv u) (liv v) p)
        (liv w p) =
      @inner ℝ (TangentSpace 𝓘(ℝ, Rn m) p) _ (liv u p)
        (VectorField.mlieBracket 𝓘(ℝ, Rn m) (liv v) (liv w) p) := by
  rw [inner_eq, inner_eq, D_bracket_liv hmul, D_bracket_liv hmul, D_liv hmul, D_liv hmul,
    Morse.inner_mul_left_of_unitary (U := incl hG p) (h.unitary _ p.2),
    Morse.inner_mul_left_of_unitary (U := incl hG p) (h.unitary _ p.2)]
  exact hI (h.skew _ (U0_mem hmul hone h u)) (h.skew _ (U0_mem hmul hone h v))

end LieDict

/-- `B`'s conclusion on `G`, given (d) and (a) (the algebra of V12_5 / V12_6). -/
theorem B_of_d_a {n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace (Rn n) G]
    [LieGroup 𝓘(ℝ, Rn n) ∞ G] [Bundle.RiemannianBundle (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)]
    (cov : Conn n G)
    (hd : ∀ u v : GroupLieAlgebra 𝓘(ℝ, Rn n) G,
      covF cov (liv u) (liv v) = (1 / 2 : ℝ) • VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv u) (liv v))
    (ha : ∀ (u v w : GroupLieAlgebra 𝓘(ℝ, Rn n) G) (p : G),
        inner ℝ (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv u) (liv v) p) (liv w p)
          = inner ℝ (liv u p) (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv v) (liv w) p)) :
      (∀ (u v w : GroupLieAlgebra 𝓘(ℝ, Rn n) G) (p : G),
        inner ℝ (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv u) (liv v) p) (liv w p)
          = inner ℝ (liv u p) (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv v) (liv w) p)) ∧
      (∀ u v w : GroupLieAlgebra 𝓘(ℝ, Rn n) G,
        curvF cov (liv u) (liv v) (liv w)
          = (1 / 4 : ℝ) • VectorField.mlieBracket 𝓘(ℝ, Rn n)
              (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv u) (liv v)) (liv w)) ∧
      (∀ (u v w z : GroupLieAlgebra 𝓘(ℝ, Rn n) G) (p : G),
        inner ℝ (curvF cov (liv u) (liv v) (liv w) p) (liv z p)
          = (1 / 4 : ℝ) * inner ℝ (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv u) (liv v) p)
              (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv w) (liv z) p)) ∧
      (∀ u v : GroupLieAlgebra 𝓘(ℝ, Rn n) G,
        covF cov (liv u) (liv v) = (1 / 2 : ℝ) • VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv u) (liv v)) ∧
      (∀ (u v : GroupLieAlgebra 𝓘(ℝ, Rn n) G) (p : G),
        inner ℝ (curvF cov (liv u) (liv v) (liv u) p) (liv v p)
            = (1 / 4 : ℝ) * inner ℝ (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv u) (liv v) p)
                (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv u) (liv v) p) ∧
          0 ≤ inner ℝ (curvF cov (liv u) (liv v) (liv u) p) (liv v p)) := by
  have hb : ∀ u v w : GroupLieAlgebra 𝓘(ℝ, Rn n) G,
      curvF cov (liv u) (liv v) (liv w)
        = (1 / 4 : ℝ) • VectorField.mlieBracket 𝓘(ℝ, Rn n)
            (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv u) (liv v)) (liv w) := by
    intro u v w
    rw [curvF_liv_of_d cov hd u v w, Morse.curv_halfLie, liv_smul, liv_bracket, liv_bracket]
  have hc : ∀ (u v w z : GroupLieAlgebra 𝓘(ℝ, Rn n) G) (p : G),
      inner ℝ (curvF cov (liv u) (liv v) (liv w) p) (liv z p)
        = (1 / 4 : ℝ) * inner ℝ (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv u) (liv v) p)
            (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv w) (liv z) p) := by
    intro u v w z p
    rw [hb, Pi.smul_apply, real_inner_smul_left, liv_bracket u v, ha]
  refine ⟨ha, hb, hc, hd, fun u v p => ⟨hc u v u v p, ?_⟩⟩
  rw [hc u v u v p]
  exact mul_nonneg (by norm_num) real_inner_self_nonneg

end Emb

open Emb

/-- `B` for a matrix group `G ⊆ Mₖ(𝕜)` modelled on `ℝᵐ`, as `Bridge.Sub hG` with its group structure, the
induced metric and the induced (Levi-Civita) connection `Bridge.conn`. -/
def B_emb : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (k m : ℕ) (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] (G : Set (Matrix (Fin k) (Fin k) 𝕜))
    (hG : Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix (Fin k) (Fin k) 𝕜) (Rn m) W G)
    (𝔤 : LieSubalgebra ℝ (Matrix (Fin k) (Fin k) 𝕜)) (h : Morse.IsMatrixGroup hG 𝔤),
    letI := grp h; haveI := lieGroup h
    (∀ (u v w : GroupLieAlgebra 𝓘(ℝ, Rn m) (Bridge.Sub hG)) (p : Bridge.Sub hG),
        inner ℝ (VectorField.mlieBracket 𝓘(ℝ, Rn m) (liv u) (liv v) p) (liv w p)
          = inner ℝ (liv u p) (VectorField.mlieBracket 𝓘(ℝ, Rn m) (liv v) (liv w) p)) ∧
      (∀ u v w : GroupLieAlgebra 𝓘(ℝ, Rn m) (Bridge.Sub hG),
        curvF (Bridge.conn (hN := hG)) (liv u) (liv v) (liv w)
          = (1 / 4 : ℝ) • VectorField.mlieBracket 𝓘(ℝ, Rn m)
              (VectorField.mlieBracket 𝓘(ℝ, Rn m) (liv u) (liv v)) (liv w)) ∧
      (∀ (u v w z : GroupLieAlgebra 𝓘(ℝ, Rn m) (Bridge.Sub hG)) (p : Bridge.Sub hG),
        inner ℝ (curvF (Bridge.conn (hN := hG)) (liv u) (liv v) (liv w) p) (liv z p)
          = (1 / 4 : ℝ) * inner ℝ (VectorField.mlieBracket 𝓘(ℝ, Rn m) (liv u) (liv v) p)
              (VectorField.mlieBracket 𝓘(ℝ, Rn m) (liv w) (liv z) p)) ∧
      (∀ u v : GroupLieAlgebra 𝓘(ℝ, Rn m) (Bridge.Sub hG),
        covF (Bridge.conn (hN := hG)) (liv u) (liv v)
          = (1 / 2 : ℝ) • VectorField.mlieBracket 𝓘(ℝ, Rn m) (liv u) (liv v)) ∧
      (∀ (u v : GroupLieAlgebra 𝓘(ℝ, Rn m) (Bridge.Sub hG)) (p : Bridge.Sub hG),
        inner ℝ (curvF (Bridge.conn (hN := hG)) (liv u) (liv v) (liv u) p) (liv v p)
            = (1 / 4 : ℝ) * inner ℝ (VectorField.mlieBracket 𝓘(ℝ, Rn m) (liv u) (liv v) p)
                (VectorField.mlieBracket 𝓘(ℝ, Rn m) (liv u) (liv v) p) ∧
          0 ≤ inner ℝ (curvF (Bridge.conn (hN := hG)) (liv u) (liv v) (liv u) p) (liv v p))

/-- `B_emb` is a special case of `B`: the induced metric is bi-invariant (`biInv`) and the induced connection
is Levi-Civita (`Bridge.conn_isLC`). -/
theorem B_to_B_emb : B → B_emb := by
  intro hB 𝕜 _ k m W _ _ _ G hG 𝔤 h
  letI := grp h; haveI := lieGroup h
  exact hB m (Bridge.Sub hG)
    (biInv h (fun _ hU => Morse.inner_mul_left_of_unitary hU)
      (fun _ hU => Morse.inner_mul_right_of_unitary hU))
    Bridge.conn Bridge.conn_isLC

theorem A_to_B_emb : A → B_emb := by
  intro hA 𝕜 _ k m W _ _ _ G hG 𝔤 h
  letI := grp h; haveI := lieGroup h
  exact B_of_d_a _ (d_liv (incl_mul h) rfl h (hA.2.2.2.2.1 h))
    (a_liv (incl_mul h) rfl h hA.1)


/-- `A`'s (d) (`covAt_mul_right`) for matrix groups with model `ℝᵐ` and `ι = Fin k` (the part of `A` that
`B_emb` covers directly). -/
def A_d : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (k m : ℕ) (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] (G : Set (Matrix (Fin k) (Fin k) 𝕜))
    (hG : Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix (Fin k) (Fin k) 𝕜) (Rn m) W G)
    (𝔤 : LieSubalgebra ℝ (Matrix (Fin k) (Fin k) 𝕜)) (_ : Morse.IsMatrixGroup hG 𝔤) (g : G)
    {X Y : Matrix (Fin k) (Fin k) 𝕜}, X ∈ 𝔤 → Y ∈ 𝔤 →
      Morse.covAt hG g (g.1 * X) (fun q : G => q.1 * Y) = g.1 * ((1 / 2 : ℝ) • (X * Y - Y * X))

open RoundTrip.Bridge in
/-- `B_emb`'s (d) gives back `A`'s (d) for these groups: every `X ∈ 𝔤 = T_IG` is `D₁u` for
`u = L₁X ∈ GroupLieAlgebra`. -/
theorem B_emb_to_A_d : B_emb → A_d := by
  intro hB 𝕜 _ k m W _ _ _ G hG 𝔤 h g X Y hX hY
  letI := grp h; haveI := lieGroup h
  obtain ⟨-, -, -, hd, -⟩ := hB 𝕜 k m W G hG 𝔤 h
  have hT : ∀ {Z : Matrix (Fin k) (Fin k) 𝕜}, Z ∈ 𝔤 → Z ∈ Morse.tangentSubspace hG (1 : Bridge.Sub hG) := by
    intro Z hZ
    refine (h.mem_tangentSubspace_iff (1 : Bridge.Sub hG)).2 ?_
    change (1 : Matrix (Fin k) (Fin k) 𝕜)ᴴ * Z ∈ 𝔤
    rwa [conjTranspose_one, Matrix.one_mul]
  let u : GroupLieAlgebra 𝓘(ℝ, Rn m) (Bridge.Sub hG) := L hG 1 X
  let v : GroupLieAlgebra 𝓘(ℝ, Rn m) (Bridge.Sub hG) := L hG 1 Y
  have hu : D hG 1 u = X := D_L (hT hX)
  have hv : D hG 1 v = Y := D_L (hT hY)
  suffices key : ∀ p : Bridge.Sub hG, Morse.covAt hG p (incl hG p * X) (fun q => incl hG q * Y) =
      incl hG p * ((1 / 2 : ℝ) • (X * Y - Y * X)) from key g
  intro p
  have e := congrArg (D hG p) (congrFun (hd u v) p)
  have h1 : D hG p (covF (Bridge.conn (hN := hG)) (liv u) (liv v) p) =
      Morse.covAt hG p (D hG p (liv u p)) (amb (liv v)) := D_conn_apply (liv v) p (liv u p)
  have e2 : D hG p (((1 / 2 : ℝ) • VectorField.mlieBracket 𝓘(ℝ, Rn m) (liv u) (liv v)) p) =
      (1 / 2 : ℝ) • D hG p (VectorField.mlieBracket 𝓘(ℝ, Rn m) (liv u) (liv v) p) :=
    (D hG p).map_smul _ _
  rw [h1, e2, D_liv (incl_mul h), amb_liv (incl_mul h), D_bracket_liv (incl_mul h), hu, hv] at e
  rw [Matrix.mul_smul]
  exact e

#rt_check RoundTrip.V12_17.A_to_B_emb [Morse.inner_lie_left, Morse.inner_gauss_identity,
  Morse.IsMatrixGroup.tanProj_eq, Morse.IsMatrixGroup.secondFundForm_mul,
  Morse.IsMatrixGroup.covAt_mul_right, Morse.IsMatrixGroup.curvOp_mul,
  Morse.IsMatrixGroup.inner_curvOp_mul, Morse.IsMatrixGroup.sectional_mul,
  Morse.IsMatrixGroup.sectional_mul_nonneg, Morse.IsMatrixGroup.curvOp_eq_curv_halfLie,
  Morse.IsMatrixGroup.curvOp_eq_jacobiOp]
#rt_check RoundTrip.V12_17.B_to_B_emb [Morse.inner_lie_left, Morse.inner_gauss_identity,
  Morse.IsMatrixGroup.tanProj_eq, Morse.IsMatrixGroup.secondFundForm_mul,
  Morse.IsMatrixGroup.covAt_mul_right, Morse.IsMatrixGroup.curvOp_mul,
  Morse.IsMatrixGroup.inner_curvOp_mul, Morse.IsMatrixGroup.sectional_mul,
  Morse.IsMatrixGroup.sectional_mul_nonneg, Morse.IsMatrixGroup.curvOp_eq_curv_halfLie,
  Morse.IsMatrixGroup.curvOp_eq_jacobiOp]
#rt_overlap RoundTrip.V12_17.A_to_B_emb [Morse.inner_lie_left, Morse.inner_gauss_identity,
  Morse.IsMatrixGroup.tanProj_eq, Morse.IsMatrixGroup.secondFundForm_mul,
  Morse.IsMatrixGroup.covAt_mul_right, Morse.IsMatrixGroup.curvOp_mul,
  Morse.IsMatrixGroup.inner_curvOp_mul, Morse.IsMatrixGroup.sectional_mul,
  Morse.IsMatrixGroup.sectional_mul_nonneg, Morse.IsMatrixGroup.curvOp_eq_curv_halfLie,
  Morse.IsMatrixGroup.curvOp_eq_jacobiOp]

#rt_check RoundTrip.V12_17.B_emb_to_A_d [Morse.inner_lie_left, Morse.inner_gauss_identity,
  Morse.IsMatrixGroup.tanProj_eq, Morse.IsMatrixGroup.secondFundForm_mul,
  Morse.IsMatrixGroup.covAt_mul_right, Morse.IsMatrixGroup.curvOp_mul,
  Morse.IsMatrixGroup.inner_curvOp_mul, Morse.IsMatrixGroup.sectional_mul,
  Morse.IsMatrixGroup.sectional_mul_nonneg, Morse.IsMatrixGroup.curvOp_eq_curv_halfLie,
  Morse.IsMatrixGroup.curvOp_eq_jacobiOp]

end RoundTrip.V12_17
