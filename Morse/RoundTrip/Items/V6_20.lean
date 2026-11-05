import Morse
import RoundTrip.Check
import RoundTrip.Blind.V6_20
import RoundTrip.Bridge

open Bundle
open scoped ContDiff Manifold RealInnerProductSpace

namespace RoundTrip.V6_20

/-- The project's statement (universes instantiated at 0): Lemma 9.3 (1)–(3): the algebraic equivalence `(∀ Z W, ⟨TZ,W⟩ + ⟨TW,Z⟩ = 0) ↔ ∀ Z, ⟨TZ,Z⟩ = 0` (any inner product space), and, for the induced metric of a slice submanifold `N ⊆ V`, that `curvTensor` satisfies (1)–(3) (`IsCurvatureTensor`, a definition) and (1), (2), (3) for the curvature of smooth tangent fields (`curvature_add_swap` for all fields). -/
def A : Prop :=
  type_of% @Morse.inner_add_inner_eq_zero_iff.{0} ∧
    type_of% @Morse.isCurvatureTensor_curvTensor.{0,0,0} ∧
    type_of% @Morse.curvature_add_swap.{0,0,0} ∧
    type_of% @Morse.curvature_bianchi.{0,0,0} ∧
    type_of% @Morse.inner_curvature_add_inner.{0,0,0}

theorem A_holds : A := ⟨@Morse.inner_add_inner_eq_zero_iff, @Morse.isCurvatureTensor_curvTensor, @Morse.curvature_add_swap, @Morse.curvature_bianchi, @Morse.inner_curvature_add_inner⟩

/-! ## The embedded special case

B is specialized to `M = ↥N` (`RoundTrip.Bridge.Sub hN`) for a slice submanifold `N ⊆ V` with
model `ℝⁿ`, the induced metric and the induced Levi-Civita connection `Bridge.conn` (`B_emb`).
Through the dictionary `Emb.D_curv` (the blind curvature of smooth fields, read in `V`, is the
project's `Morse.curvature` of the ambient fields) and `Emb.liftF` (an ambient tangent field
`Y : N → V` as a vector field on `↥N`), `B_emb` is exactly A's field-level clauses for the model
`ℝⁿ`: (1) for smooth tangent fields, `curvature_bianchi` and `inner_curvature_add_inner`
(`Afields`). These imply A's `isCurvatureTensor_curvTensor` (`Afields_to_Atensor`, using the
project's Lemma 9.1 for `N`, `curvature_eq_curvTensor`, which is not one of this item's
theorems). -/

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

theorem D_tneg (x : Bridge.Sub hN) (v : TangentSpace 𝓘(ℝ, Rn n) x) :
    D hN x (-v) = -D hN x v := map_neg (D hN x) v

/-- **Dictionary: curvature of fields.** The blind curvature of smooth fields for the induced
connection, read in `V`, is the project's `Morse.curvature` of the ambient fields (the first half
of `Bridge.D_curvExpr`; no use of `Morse.curvature_eq`). -/
theorem D_curv (X Y Z : VF n (Bridge.Sub hN)) (hX : IsSmoothVF X) (hY : IsSmoothVF Y)
    (p : Bridge.Sub hN) :
    D hN p (curv (conn (hN := hN)) X Y Z p) = Morse.curvature hN (amb X) (amb Y) (amb Z) p := by
  have hXp := (hX p).mdifferentiableAt (by simp)
  have hYp := (hY p).mdifferentiableAt (by simp)
  have hbr : D hN p (VectorField.mlieBracket 𝓘(ℝ, Rn n) X Y p) =
      Morse.bracket hN (amb X) (amb Y) p := by
    rw [D_mlieBracket p X Y hXp hYp]
    show _ = Morse.dN hN (amb Y) p (amb X p) - Morse.dN hN (amb X) p (amb Y p)
    exact congrArg₂ (· - ·) (dN_D (amb Y) p (X p)).symm (dN_D (amb X) p (Y p)).symm
  have hC : D hN p (conn Z p (VectorField.mlieBracket 𝓘(ℝ, Rn n) X Y p)) =
      Morse.leviCivita hN (Morse.bracket hN (amb X) (amb Y)) (amb Z) p := by
    rw [D_conn_apply, hbr]
    rfl
  have hA : D hN p (conn (fun q => conn Z q (Y q)) p (X p)) =
      Morse.leviCivita hN (amb X) (Morse.leviCivita hN (amb Y) (amb Z)) p := by
    rw [D_conn, amb_conn]
  have hB : D hN p (conn (fun q => conn Z q (X q)) p (Y p)) =
      Morse.leviCivita hN (amb Y) (Morse.leviCivita hN (amb X) (amb Z)) p := by
    rw [D_conn, amb_conn]
  show D hN p (-(conn (fun q => conn Z q (Y q)) p (X p)) + conn (fun q => conn Z q (X q)) p (Y p)
    + conn Z p (VectorField.mlieBracket 𝓘(ℝ, Rn n) X Y p)) = _
  rw [D_tadd, D_tadd, D_tneg, hA, hB, hC]
  rfl

/-- The inner product of a curvature value with a vector, read in `V`. -/
theorem inner_curv (X Y Z : VF n (Bridge.Sub hN)) (hX : IsSmoothVF X) (hY : IsSmoothVF Y)
    (p : Bridge.Sub hN) (w : TangentSpace 𝓘(ℝ, Rn n) p) :
    inner ℝ (curv (conn (hN := hN)) X Y Z p) w =
      ⟪Morse.curvature hN (amb X) (amb Y) (amb Z) p, D hN p w⟫ := by
  rw [← D_curv X Y Z hX hY p]
  rfl

/-- The vector field `q ↦ L_q(Y q)` on `↥N` of an ambient map `Y : N → V`. -/
noncomputable def liftF (Y : N → V) : VF n (Bridge.Sub hN) := fun q => L hN q (Y q)

theorem amb_liftF {Y : N → V} (hYT : Morse.IsTangentField hN Y) : amb (liftF (hN := hN) Y) = Y :=
  funext fun q => D_L (hYT q)

theorem isSmoothVF_liftF {Y : N → V}
    (hY : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, V) ∞ Y)
    (hYT : Morse.IsTangentField hN Y) : IsSmoothVF (liftF (hN := hN) Y) := by
  unfold IsSmoothVF
  rw [contMDiff_section_iff, amb_liftF hYT]
  exact hY

end Emb

/-- B on embedded manifolds: `M = ↥N` with the induced metric and the induced Levi-Civita
connection (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N),
    ∀ X Y Z W' : VF n (Bridge.Sub hN), IsSmoothVF X → IsSmoothVF Y → IsSmoothVF Z →
      IsSmoothVF W' → ∀ p : Bridge.Sub hN,
        curv (Bridge.conn (hN := hN)) X Y Z p + curv (Bridge.conn (hN := hN)) Y X Z p = 0 ∧
        curv (Bridge.conn (hN := hN)) X Y Z p + curv (Bridge.conn (hN := hN)) Y Z X p +
          curv (Bridge.conn (hN := hN)) Z X Y p = 0 ∧
        inner ℝ (curv (Bridge.conn (hN := hN)) X Y Z p) (W' p) +
          inner ℝ (curv (Bridge.conn (hN := hN)) X Y W' p) (Z p) = 0

/-- A's field-level clauses for slice submanifolds modelled on `ℝⁿ`: (1) for smooth tangent fields
(A's `curvature_add_swap` has no hypotheses), (2) `curvature_bianchi`, (3)
`inner_curvature_add_inner`. -/
def Afields : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) (X Y Z' W' : N → V),
    (letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, V) ∞ X) →
    (letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, V) ∞ Y) →
    (letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, V) ∞ Z') →
    (letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, V) ∞ W') →
    Morse.IsTangentField hN X → Morse.IsTangentField hN Y → Morse.IsTangentField hN Z' →
    Morse.IsTangentField hN W' → ∀ q : N,
      Morse.curvature hN X Y Z' q + Morse.curvature hN Y X Z' q = 0 ∧
      Morse.curvature hN X Y Z' q + Morse.curvature hN Y Z' X q + Morse.curvature hN Z' X Y q = 0 ∧
      ⟪Morse.curvature hN X Y Z' q, W' q⟫ + ⟪Morse.curvature hN X Y W' q, Z' q⟫ = 0

/-- A's `isCurvatureTensor_curvTensor` for slice submanifolds modelled on `ℝⁿ`. -/
def Atensor : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) (q : N),
    Morse.IsCurvatureTensor (Morse.curvTensor hN q)

/-- `B_emb` is a special case of B (the induced connection is Levi-Civita, `Bridge.conn_isLC`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

theorem A_to_Afields : A → Afields :=
  fun hA _ _ _ _ _ _ _ _ _ _ hN _ _ _ _ hX hY hZ hW hXT hYT hZT hWT q =>
    ⟨hA.2.2.1 hN _ _ _ q, hA.2.2.2.1 hN hX hY hZ hXT hYT hZT q,
      hA.2.2.2.2 hN hX hY hZ hW hXT hYT hZT hWT q⟩

/-- **B on embedded manifolds is A's field-level clauses (1)–(3) for the model `ℝⁿ`**, through
the dictionary `Emb.D_curv`, `Emb.liftF`. -/
theorem B_emb_iff_Afields : B_emb ↔ Afields := by
  constructor
  · intro h V _ _ _ W _ _ _ n N hN X Y Z W' hX hY hZ hW hXT hYT hZT hWT (q : Bridge.Sub hN)
    have sX := Emb.isSmoothVF_liftF hX hXT
    have sY := Emb.isSmoothVF_liftF hY hYT
    have sZ := Emb.isSmoothVF_liftF hZ hZT
    have sW := Emb.isSmoothVF_liftF hW hWT
    obtain ⟨e1, e2, e3⟩ := h V W n N hN (Emb.liftF X) (Emb.liftF Y) (Emb.liftF Z) (Emb.liftF W')
      sX sY sZ sW q
    have hW' : Bridge.D hN q (Emb.liftF (hN := hN) W' q) = W' q := Bridge.D_L (hWT q)
    have hZ' : Bridge.D hN q (Emb.liftF (hN := hN) Z q) = Z q := Bridge.D_L (hZT q)
    refine ⟨?_, ?_, ?_⟩
    · have := congrArg (Bridge.D hN q) e1
      rw [Bridge.D_tadd, Emb.D_curv _ _ _ sX sY, Emb.D_curv _ _ _ sY sX, Bridge.D_tzero,
        Emb.amb_liftF hXT, Emb.amb_liftF hYT, Emb.amb_liftF hZT] at this
      exact this
    · have := congrArg (Bridge.D hN q) e2
      rw [Bridge.D_tadd, Bridge.D_tadd, Emb.D_curv _ _ _ sX sY, Emb.D_curv _ _ _ sY sZ,
        Emb.D_curv _ _ _ sZ sX, Bridge.D_tzero, Emb.amb_liftF hXT, Emb.amb_liftF hYT,
        Emb.amb_liftF hZT] at this
      exact this
    · rw [Emb.inner_curv _ _ _ sX sY, Emb.inner_curv _ _ _ sX sY, hW', hZ', Emb.amb_liftF hXT,
        Emb.amb_liftF hYT, Emb.amb_liftF hZT, Emb.amb_liftF hWT] at e3
      exact e3
  · intro h V _ _ _ W _ _ _ n N hN X Y Z W' hX hY hZ hW p
    obtain ⟨e1, e2, e3⟩ := h V W n N hN (Bridge.amb X) (Bridge.amb Y) (Bridge.amb Z)
      (Bridge.amb W') (Bridge.contMDiff_amb hX) (Bridge.contMDiff_amb hY)
      (Bridge.contMDiff_amb hZ) (Bridge.contMDiff_amb hW) (Bridge.isTangentField_amb X)
      (Bridge.isTangentField_amb Y) (Bridge.isTangentField_amb Z) (Bridge.isTangentField_amb W') p
    refine ⟨?_, ?_, ?_⟩
    · apply Bridge.D_injective p
      rw [Bridge.D_tadd, Emb.D_curv X Y Z hX hY p, Emb.D_curv Y X Z hY hX p, Bridge.D_tzero]
      exact e1
    · apply Bridge.D_injective p
      rw [Bridge.D_tadd, Bridge.D_tadd, Emb.D_curv X Y Z hX hY p, Emb.D_curv Y Z X hY hZ p,
        Emb.D_curv Z X Y hZ hX p, Bridge.D_tzero]
      exact e2
    · rw [Emb.inner_curv X Y Z hX hY p, Emb.inner_curv X Y W' hX hY p]
      exact e3

/-- A's field-level clauses imply A's `isCurvatureTensor_curvTensor` (model `ℝⁿ`), with the
project's Lemma 9.1 for `N` (`curvature_eq_curvTensor`) and the extensions `projField`. -/
theorem Afields_to_Atensor : Afields → Atensor := by
  intro h V _ _ _ W _ _ _ n N hN q
  have hP : ∀ x : Morse.tangentSubspace hN q,
      (⟨Morse.projField hN x.1 q, Morse.isTangentField_projField hN x.1 q⟩ :
        Morse.tangentSubspace hN q) = x :=
    fun x => Subtype.ext (Morse.projField_apply_of_mem hN x.2)
  have key : ∀ x y z : Morse.tangentSubspace hN q, (Morse.curvTensor hN q x y z : V) =
      Morse.curvature hN (Morse.projField hN x.1) (Morse.projField hN y.1)
        (Morse.projField hN z.1) q := by
    intro x y z
    rw [Morse.curvature_eq_curvTensor hN (Morse.contMDiff_projField hN x.1)
      (Morse.contMDiff_projField hN y.1) (Morse.contMDiff_projField hN z.1)
      (Morse.isTangentField_projField hN x.1) (Morse.isTangentField_projField hN y.1)
      (Morse.isTangentField_projField hN z.1), hP, hP, hP]
  have H := fun x y z w : Morse.tangentSubspace hN q =>
    h V W n N hN (Morse.projField hN x.1) (Morse.projField hN y.1) (Morse.projField hN z.1)
      (Morse.projField hN w.1) (Morse.contMDiff_projField hN x.1)
      (Morse.contMDiff_projField hN y.1) (Morse.contMDiff_projField hN z.1)
      (Morse.contMDiff_projField hN w.1) (Morse.isTangentField_projField hN x.1)
      (Morse.isTangentField_projField hN y.1) (Morse.isTangentField_projField hN z.1)
      (Morse.isTangentField_projField hN w.1) q
  refine ⟨fun x y z => ?_, fun x y z => ?_, fun x y z w => ?_⟩
  · apply Subtype.ext
    rw [Submodule.coe_add, key, key, Submodule.coe_zero]
    exact (H x y z z).1
  · apply Subtype.ext
    rw [Submodule.coe_add, Submodule.coe_add, key, key, key, Submodule.coe_zero]
    exact (H x y z z).2.1
  · rw [Submodule.coe_inner, Submodule.coe_inner, key, key]
    have e := (H x y z w).2.2
    rwa [Morse.projField_apply_of_mem hN w.2, Morse.projField_apply_of_mem hN z.2] at e

/-- **A implies B on embedded manifolds** (uses A's `curvature_add_swap`, `curvature_bianchi`,
`inner_curvature_add_inner`). -/
theorem A_to_B_emb : A → B_emb := fun hA => B_emb_iff_Afields.2 (A_to_Afields hA)

/-- **B implies A's field-level clauses and `isCurvatureTensor_curvTensor`** (model `ℝⁿ`), by
specializing B to `↥N`. -/
theorem B_to_Afields_Atensor : B → Afields ∧ Atensor := fun hB =>
  have h := B_emb_iff_Afields.1 (B_to_B_emb hB)
  ⟨h, Afields_to_Atensor h⟩

#rt_check RoundTrip.V6_20.A_to_B_emb [Morse.inner_add_inner_eq_zero_iff,
  Morse.isCurvatureTensor_curvTensor, Morse.curvature_add_swap, Morse.curvature_bianchi,
  Morse.inner_curvature_add_inner]
#rt_check RoundTrip.V6_20.B_to_Afields_Atensor [Morse.inner_add_inner_eq_zero_iff,
  Morse.isCurvatureTensor_curvTensor, Morse.curvature_add_swap, Morse.curvature_bianchi,
  Morse.inner_curvature_add_inner]
/-- The field-level part alone (no Lemma 9.1 for `N`). -/
theorem B_to_Afields : B → Afields := fun hB => B_emb_iff_Afields.1 (B_to_B_emb hB)

#rt_overlap RoundTrip.V6_20.B_to_Afields [Morse.inner_add_inner_eq_zero_iff,
  Morse.isCurvatureTensor_curvTensor, Morse.curvature_add_swap, Morse.curvature_bianchi,
  Morse.inner_curvature_add_inner]
#rt_overlap RoundTrip.V6_20.B_to_Afields_Atensor [Morse.inner_add_inner_eq_zero_iff,
  Morse.isCurvatureTensor_curvTensor, Morse.curvature_add_swap, Morse.curvature_bianchi,
  Morse.inner_curvature_add_inner]

end RoundTrip.V6_20
