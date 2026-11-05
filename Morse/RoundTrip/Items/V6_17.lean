import Morse
import RoundTrip.Check
import RoundTrip.Blind.V6_17
import RoundTrip.Bridge

open Bundle
open scoped ContDiff Manifold RealInnerProductSpace

namespace RoundTrip.V6_17

/-- The project's statement (universes instantiated at 0): Lemma 9.1 for the induced metric of a slice submanifold `N ⊆ V` (`curvOp`, `curvTensor` are definitions): for smooth tangent fields `R(X,Y)Z = II(Y, II(X,Z)) − II(X, II(Y,Z))` at `q`, i.e. the trilinear map `curvTensor hN q` applied to `X_q, Y_q, Z_q`, so `R(X,Y)Z (q)` depends only on `X_q, Y_q, Z_q`. -/
def A : Prop :=
  type_of% @Morse.curvature_eq.{0,0,0} ∧
    type_of% @Morse.curvature_eq_curvTensor.{0,0,0} ∧
    type_of% @Morse.curvature_congr.{0,0,0}

theorem A_holds : A := ⟨@Morse.curvature_eq, @Morse.curvature_eq_curvTensor, @Morse.curvature_congr⟩

/-! ## The embedded special case

B is specialized to `M = ↥N` (`RoundTrip.Bridge.Sub hN`) for a slice submanifold `N ⊆ V` with
model `ℝⁿ`, the induced metric and the induced connection `Bridge.conn` (`B_emb`). Through the
dictionary `Emb.D_curv` (the blind curvature of smooth fields, read in `V`, is the project's
`Morse.curvature` of the ambient fields), A's `curvature_eq_curvTensor` gives `B_emb` with the
trilinear map `T = L ∘ curvTensor ∘ D` (`A_to_B_emb`); conversely `B_emb`'s tensoriality clause
gives A's `curvature_congr` for the model `ℝⁿ` (`B_emb_to_Acongr`), through `Emb.liftF`. -/

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


/-- `D_p : T_p↥N → T_pN ⊆ V` as a linear map into the subspace. -/
noncomputable def Dt (p : Bridge.Sub hN) : TangentSpace 𝓘(ℝ, Rn n) p →ₗ[ℝ] Morse.tangentSubspace hN p :=
  LinearMap.codRestrict (Morse.tangentSubspace hN p) (D hN p : Rn n →ₗ[ℝ] V) (D_mem p)

/-- `L_p : T_pN → T_p↥N`. -/
noncomputable def Lt (p : Bridge.Sub hN) : Morse.tangentSubspace hN p →ₗ[ℝ] TangentSpace 𝓘(ℝ, Rn n) p :=
  (L hN p : V →ₗ[ℝ] Rn n).comp (Morse.tangentSubspace hN p).subtype

theorem D_Lt (p : Bridge.Sub hN) (v : Morse.tangentSubspace hN p) : D hN p (Lt p v) = v :=
  D_L v.2

/-- The project's curvature tensor `curvTensor hN p`, transported to `T_p↥N`. -/
noncomputable def Tp (p : Bridge.Sub hN) :
    TangentSpace 𝓘(ℝ, Rn n) p →ₗ[ℝ] TangentSpace 𝓘(ℝ, Rn n) p →ₗ[ℝ] TangentSpace 𝓘(ℝ, Rn n) p →ₗ[ℝ]
      TangentSpace 𝓘(ℝ, Rn n) p :=
  LinearMap.mk₂ ℝ (fun x y => (Lt p).comp ((Morse.curvTensor hN p (Dt p x) (Dt p y)).comp (Dt p)))
    (fun x x' y => by ext z; simp)
    (fun a x y => by ext z; simp)
    (fun x y y' => by ext z; simp)
    (fun a x y => by ext z; simp)

theorem D_Tp (p : Bridge.Sub hN) (x y z : TangentSpace 𝓘(ℝ, Rn n) p) :
    D hN p (Tp p x y z) = Morse.curvTensor hN p (Dt p x) (Dt p y) (Dt p z) :=
  D_Lt p _

end Emb

/-- B on embedded manifolds: `M = ↥N` with the induced metric and the induced connection
(a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) (p : Bridge.Sub hN),
    (∀ X X' Y Y' Z Z' : VF n (Bridge.Sub hN), IsSmoothVF X → IsSmoothVF X' → IsSmoothVF Y →
      IsSmoothVF Y' → IsSmoothVF Z → IsSmoothVF Z' → X p = X' p → Y p = Y' p → Z p = Z' p →
        curv (Bridge.conn (hN := hN)) X Y Z p = curv (Bridge.conn (hN := hN)) X' Y' Z' p) ∧
    ∃ T : TangentSpace 𝓘(ℝ, Rn n) p →ₗ[ℝ] TangentSpace 𝓘(ℝ, Rn n) p →ₗ[ℝ]
        TangentSpace 𝓘(ℝ, Rn n) p →ₗ[ℝ] TangentSpace 𝓘(ℝ, Rn n) p,
      ∀ X Y Z : VF n (Bridge.Sub hN), IsSmoothVF X → IsSmoothVF Y → IsSmoothVF Z →
        curv (Bridge.conn (hN := hN)) X Y Z p = T (X p) (Y p) (Z p)

/-- A's `curvature_congr` for slice submanifolds modelled on `ℝⁿ`. -/
def Acongr : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) (X Y Z' X' Y' Z'' : N → V),
    (letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, V) ∞ X) →
    (letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, V) ∞ Y) →
    (letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, V) ∞ Z') →
    (letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, V) ∞ X') →
    (letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, V) ∞ Y') →
    (letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, V) ∞ Z'') →
    Morse.IsTangentField hN X → Morse.IsTangentField hN Y → Morse.IsTangentField hN Z' →
    Morse.IsTangentField hN X' → Morse.IsTangentField hN Y' → Morse.IsTangentField hN Z'' →
    ∀ q : N, X q = X' q → Y q = Y' q → Z' q = Z'' q →
      Morse.curvature hN X Y Z' q = Morse.curvature hN X' Y' Z'' q

/-- `B_emb` is a special case of B (the induced connection is smooth, `Bridge.conn_isGlobalConn`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN p =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isGlobalConn p

/-- **A implies B on embedded manifolds** (uses A's `curvature_eq_curvTensor`): the trilinear map
is the project's `curvTensor`, transported to `T_p↥N`. -/
theorem A_to_B_emb : A → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN p
  have hT : ∀ X Y Z : VF n (Bridge.Sub hN), IsSmoothVF X → IsSmoothVF Y → IsSmoothVF Z →
      curv (Bridge.conn (hN := hN)) X Y Z p = Emb.Tp p (X p) (Y p) (Z p) := by
    intro X Y Z hX hY hZ
    apply Bridge.D_injective p
    rw [Emb.D_curv X Y Z hX hY p, Emb.D_Tp,
      hA.2.1 hN (Bridge.contMDiff_amb hX) (Bridge.contMDiff_amb hY) (Bridge.contMDiff_amb hZ)
        (Bridge.isTangentField_amb X) (Bridge.isTangentField_amb Y) (Bridge.isTangentField_amb Z) p]
    rfl
  refine ⟨fun X X' Y Y' Z Z' hX hX' hY hY' hZ hZ' h1 h2 h3 => ?_, Emb.Tp p, hT⟩
  rw [hT X Y Z hX hY hZ, hT X' Y' Z' hX' hY' hZ', h1, h2, h3]

/-- **B on embedded manifolds implies A's `curvature_congr`** (model `ℝⁿ`). -/
theorem B_emb_to_Acongr : B_emb → Acongr := by
  intro h V _ _ _ W _ _ _ n N hN X Y Z X' Y' Z' hX hY hZ hX' hY' hZ' hXT hYT hZT hXT' hYT' hZT'
    (q : Bridge.Sub hN) h1 h2 h3
  have sX := Emb.isSmoothVF_liftF hX hXT
  have sY := Emb.isSmoothVF_liftF hY hYT
  have sZ := Emb.isSmoothVF_liftF hZ hZT
  have sX' := Emb.isSmoothVF_liftF hX' hXT'
  have sY' := Emb.isSmoothVF_liftF hY' hYT'
  have sZ' := Emb.isSmoothVF_liftF hZ' hZT'
  have e := (h V W n N hN q).1 _ _ _ _ _ _ sX sX' sY sY' sZ sZ'
    (congrArg (Bridge.L hN q) h1) (congrArg (Bridge.L hN q) h2) (congrArg (Bridge.L hN q) h3)
  have := congrArg (Bridge.D hN q) e
  rwa [Emb.D_curv _ _ _ sX sY, Emb.D_curv _ _ _ sX' sY', Emb.amb_liftF hXT, Emb.amb_liftF hYT,
    Emb.amb_liftF hZT, Emb.amb_liftF hXT', Emb.amb_liftF hYT', Emb.amb_liftF hZT'] at this

/-- **B implies A's `curvature_congr`** (model `ℝⁿ`), by specializing B to `↥N`. -/
theorem B_to_Acongr : B → Acongr := fun hB => B_emb_to_Acongr (B_to_B_emb hB)

#rt_check RoundTrip.V6_17.A_to_B_emb [Morse.curvature_eq, Morse.curvature_eq_curvTensor,
  Morse.curvature_congr]
#rt_check RoundTrip.V6_17.B_to_Acongr [Morse.curvature_eq, Morse.curvature_eq_curvTensor,
  Morse.curvature_congr]
#rt_overlap RoundTrip.V6_17.B_to_Acongr [Morse.curvature_eq, Morse.curvature_eq_curvTensor,
  Morse.curvature_congr]

end RoundTrip.V6_17
