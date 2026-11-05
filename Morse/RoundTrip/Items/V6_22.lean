import Morse
import RoundTrip.Check
import RoundTrip.Blind.V6_22
import RoundTrip.Bridge

open Bundle
open scoped RealInnerProductSpace ContDiff Manifold

namespace RoundTrip.V6_22

/-- The project's statement (universes instantiated at 0; `sectionalCurvature` is a definition:
`⟨R(X,Y)X,Y⟩ / (‖X‖²‖Y‖² − ⟨X,Y⟩²)`), pure algebra on a real inner product space for a trilinear
`R` satisfying (1)–(3) of Lemma 9.3: the sectional curvature is unchanged under
`(X, Y) ↦ (aX + bY, cX + dY)`, `ad − bc ≠ 0`; `−R` also satisfies (1)–(3);
`⟨(−R)(X,Y)Y, X⟩ = ⟨R(X,Y)X, Y⟩` (sign conventions). -/
def A : Prop :=
  type_of% @Morse.IsCurvatureTensor.sectionalCurvature_smul_add.{0} ∧
    type_of% @Morse.IsCurvatureTensor.neg.{0} ∧
    type_of% @Morse.IsCurvatureTensor.inner_neg_apply_swap.{0}

theorem A_holds : A :=
  ⟨@Morse.IsCurvatureTensor.sectionalCurvature_smul_add, @Morse.IsCurvatureTensor.neg,
    @Morse.IsCurvatureTensor.inner_neg_apply_swap⟩

/-- The differential-geometric input A lacks for abstract manifolds: Lemma 9.1 (the curvature of a
Levi-Civita connection at `p` is a trilinear map on `T_pM`) together with Lemma 9.3 (1)–(3) for that
map. (The project has both only for `N ⊆ V`: `curvature_eq_curvTensor`,
`isCurvatureTensor_curvTensor`.) -/
def TensorHyp : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (Rn n) M]
    [IsManifold 𝓘(ℝ, Rn n) ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, Rn n) ∞ (Rn n) (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)],
    ∀ cov : Conn n M, IsLC cov → ∀ p : M,
      ∃ T : TangentSpace 𝓘(ℝ, Rn n) p →ₗ[ℝ] TangentSpace 𝓘(ℝ, Rn n) p →ₗ[ℝ]
          TangentSpace 𝓘(ℝ, Rn n) p →ₗ[ℝ] TangentSpace 𝓘(ℝ, Rn n) p,
        Morse.IsCurvatureTensor T ∧ ∀ X Y Z : VF n M, IsSmoothVF X → IsSmoothVF Y → IsSmoothVF Z →
          curv cov X Y Z p = T (X p) (Y p) (Z p)

/-- Two orthonormal pairs spanning the same plane are related by an invertible `2 × 2` matrix. -/
theorem exists_coeffs {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {A B A' B' : E}
    (hA' : ‖A'‖ = 1) (hB' : ‖B'‖ = 1) (hAB' : ⟪A', B'⟫ = 0)
    (hspan : Submodule.span ℝ {A', B'} = Submodule.span ℝ {A, B}) :
    ∃ a b c d : ℝ, a * d - b * c ≠ 0 ∧ A' = a • A + b • B ∧ B' = c • A + d • B := by
  have h1 : A' ∈ Submodule.span ℝ {A, B} := hspan ▸ Submodule.subset_span (by simp)
  have h2 : B' ∈ Submodule.span ℝ {A, B} := hspan ▸ Submodule.subset_span (by simp)
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1 h1
  obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.1 h2
  refine ⟨a, b, c, d, fun h => ?_, hab.symm, hcd.symm⟩
  have e1 : d • A' - b • B' = 0 := by
    rw [← hab, ← hcd, smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul,
      show d * a = b * c by linarith, mul_comm d b]
    abel
  have e2 : c • A' - a • B' = 0 := by
    rw [← hab, ← hcd, smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul,
      show c * b = a * d by linarith, mul_comm c a]
    abel
  have hAA : ⟪A', A'⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hA']; norm_num
  have hBB : ⟪B', B'⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hB']; norm_num
  have hBA : ⟪B', A'⟫ = 0 := by rw [real_inner_comm]; exact hAB'
  have i1 := congrArg (fun v => ⟪v, A'⟫) e1
  have i2 := congrArg (fun v => ⟪v, B'⟫) e1
  have i3 := congrArg (fun v => ⟪v, A'⟫) e2
  have i4 := congrArg (fun v => ⟪v, B'⟫) e2
  simp only [inner_sub_left, real_inner_smul_left, hAA, hBB, hAB', hBA, inner_zero_left] at i1 i2 i3 i4
  have ha : a = 0 := by linarith
  have hb : b = 0 := by linarith
  rw [← hab, ha, hb, zero_smul, zero_smul, add_zero, norm_zero] at hA'
  exact zero_ne_one hA'

/-- **A + `TensorHyp` ⇒ B**: with the tensor `T` at `p`, `⟨R(X,Y)X,Y⟩_p` for orthonormal
`X_p = A', Y_p = B'` is the sectional curvature `sectionalCurvature T A' B'` (denominator `1`), which
by A's `sectionalCurvature_smul_add` is that of `(A, B)`. -/
theorem A_and_tensor_to_B (hA : A) (hT : TensorHyp) : B := by
  intro n M _ _ _ _ _ _ cov hLC p A B hA1 hB1 hAB
  obtain ⟨T, hTc, hTe⟩ := hT n M cov hLC p
  refine ⟨Morse.sectionalCurvature T A B, fun A' B' hA'1 hB'1 hA'B' hspan X Y hX hY hXp hYp => ?_⟩
  obtain ⟨a, b, c, d, hdet, rfl, rfl⟩ := exists_coeffs hA'1 hB'1 hA'B' hspan
  have hs := hA.1 hTc A B hdet
  rw [Morse.sectionalCurvature, hA'1, hB'1, hA'B'] at hs
  rw [hTe X Y X hX hY hX, hXp, hYp, ← hs]
  norm_num

#rt_check RoundTrip.V6_22.A_and_tensor_to_B [Morse.IsCurvatureTensor.sectionalCurvature_smul_add,
  Morse.IsCurvatureTensor.neg, Morse.IsCurvatureTensor.inner_neg_apply_swap]

/-! ## The embedded special case

Below, B is specialized to `M = ↥N` (`RoundTrip.Bridge.Sub hN`) for a slice submanifold `N ⊆ V`
with model `ℝⁿ`, the induced metric and the induced Levi-Civita connection `Bridge.conn`
(`B_emb`; `B_to_B_emb` shows it is a special case of B). For `↥N` the project has exactly the
missing `TensorHyp`: the curvature of `Bridge.conn` read in `V` is `Morse.curvOp`
(`Bridge.D_curvExpr`), i.e. the trilinear map `Morse.curvTensor hN p`, which satisfies (1)–(3)
(`Morse.isCurvatureTensor_curvTensor`). So A ⇒ B_emb (`A_to_B_emb`, using A's
`sectionalCurvature_smul_add`). B_emb does not imply A: A is algebra about arbitrary tensors. -/

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- Milnor's curvature of the induced connection, read in `V`, is the project's `curvOp`. -/
theorem D_curv {X Y Z : VF n (Bridge.Sub hN)} (hX : IsSmoothVF X) (hY : IsSmoothVF Y)
    (hZ : IsSmoothVF Z) (p : Bridge.Sub hN) :
    D hN p (curv (conn (hN := hN)) X Y Z p) =
      Morse.curvOp hN p (D hN p (X p)) (D hN p (Y p)) (D hN p (Z p)) := by
  have e : curv (conn (hN := hN)) X Y Z p =
      conn (fun q => conn Z q (X q)) p (Y p) - conn (fun q => conn Z q (Y q)) p (X p) +
        conn Z p (VectorField.mlieBracket 𝓘(ℝ, Rn n) X Y p) := by
    simp only [curv]
    abel
  rw [e]
  exact D_curvExpr hX hY hZ p

end Emb

/-- B on embedded manifolds: `M = ↥N` with the induced metric and the induced Levi-Civita
connection (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N),
    ∀ p : Bridge.Sub hN, ∀ A B : TangentSpace 𝓘(ℝ, Rn n) p,
    ‖A‖ = 1 → ‖B‖ = 1 → inner ℝ A B = 0 →
    ∃ K : ℝ, ∀ A' B' : TangentSpace 𝓘(ℝ, Rn n) p, ‖A'‖ = 1 → ‖B'‖ = 1 → inner ℝ A' B' = 0 →
      Submodule.span ℝ {A', B'} = Submodule.span ℝ {A, B} →
      ∀ X Y : VF n (Bridge.Sub hN), IsSmoothVF X → IsSmoothVF Y → X p = A' → Y p = B' →
        inner ℝ (curv (Bridge.conn (hN := hN)) X Y X p) (Y p) = K

/-- `B_emb` is a special case of B (the induced connection is Levi-Civita, `Bridge.conn_isLC`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- **A implies B on embedded manifolds**: `K` is A's `sectionalCurvature` of the curvature tensor
`Morse.curvTensor hN p` at the pair `(D_p A, D_p B)`; an orthonormal pair `(A', B')` spanning the
same plane is an invertible combination of `(A, B)` (`exists_coeffs`), and A's
`sectionalCurvature_smul_add` does the rest. -/
theorem A_to_B_emb (hA : A) : B_emb := by
  intro V _ _ _ W _ _ _ n N hN p A B hA1 hB1 hAB
  set T := Morse.curvTensor hN p
  have hT : Morse.IsCurvatureTensor T := Morse.isCurvatureTensor_curvTensor hN p
  let ι : TangentSpace 𝓘(ℝ, Rn n) p → Morse.tangentSubspace hN p := fun v =>
    ⟨Bridge.D hN p v, Bridge.D_mem p v⟩
  refine ⟨Morse.sectionalCurvature T (ι A) (ι B),
    fun A' B' hA'1 hB'1 hA'B' hspan X Y hX hY hXp hYp => ?_⟩
  obtain ⟨a, b, c, d, hdet, hA', hB'⟩ := exists_coeffs hA'1 hB'1 hA'B' hspan
  have hs := hA.1 hT (ι A) (ι B) hdet
  have e1 : ι A' = a • ι A + b • ι B := Subtype.ext (by
    show Bridge.D hN p A' = a • Bridge.D hN p A + b • Bridge.D hN p B
    rw [hA']
    exact (Bridge.D_tadd p _ _).trans (by rw [Bridge.D_tsmul, Bridge.D_tsmul]))
  have e2 : ι B' = c • ι A + d • ι B := Subtype.ext (by
    show Bridge.D hN p B' = c • Bridge.D hN p A + d • Bridge.D hN p B
    rw [hB']
    exact (Bridge.D_tadd p _ _).trans (by rw [Bridge.D_tsmul, Bridge.D_tsmul]))
  rw [← e1, ← e2] at hs
  have n1 : ‖ι A'‖ = 1 := by
    rw [Submodule.coe_norm]
    exact (Bridge.norm_eq p A').symm.trans hA'1
  have n2 : ‖ι B'‖ = 1 := by
    rw [Submodule.coe_norm]
    exact (Bridge.norm_eq p B').symm.trans hB'1
  have i12 : ⟪ι A', ι B'⟫ = 0 := by
    rw [Submodule.coe_inner]
    exact (Bridge.inner_eq p A' B').symm.trans hA'B'
  rw [Morse.sectionalCurvature, n1, n2, i12] at hs
  rw [← hs, Bridge.inner_eq, Emb.D_curv hX hY hX p, hXp, hYp]
  norm_num
  rfl

#rt_check RoundTrip.V6_22.A_to_B_emb [Morse.IsCurvatureTensor.sectionalCurvature_smul_add,
  Morse.IsCurvatureTensor.neg, Morse.IsCurvatureTensor.inner_neg_apply_swap]

end RoundTrip.V6_22
