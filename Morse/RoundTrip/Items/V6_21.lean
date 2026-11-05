import Morse
import RoundTrip.Check
import RoundTrip.Blind.V6_21
import RoundTrip.Blind.V6_20
import RoundTrip.Bridge

open Bundle
open scoped ContDiff Manifold RealInnerProductSpace

namespace RoundTrip.V6_21

/-- The project's statement (universes instantiated at 0): the octahedron as a statement about an
arbitrary function `T : α⁴ → ℝ` satisfying (1), (2), (3); pair symmetry (4) for trilinear maps
satisfying (1)–(3) (`IsCurvatureTensor`); and (4) for the curvature of the induced metric of a slice
submanifold `N ⊆ V`, for smooth tangent fields. -/
def A : Prop :=
  type_of% @Morse.octahedron.{0} ∧ type_of% @Morse.IsCurvatureTensor.inner_comm_pairs.{0} ∧
    type_of% @Morse.inner_curvature_comm_pairs.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.octahedron, @Morse.IsCurvatureTensor.inner_comm_pairs, @Morse.inner_curvature_comm_pairs⟩

/-- **A + Lemma 9.3 (1)–(3) on abstract manifolds (= the blind B of V6_20) ⇒ B.** A's octahedron
is stated for an arbitrary index type, so it applies verbatim to the values
`T X Y Z W = ⟨R(X, Y)Z, W⟩_p` on smooth vector fields `X, Y, Z, W` (no tensoriality needed). The
only missing input for A ⇒ B is (2) and (3) for an abstract Levi-Civita connection, which A has only
for `N ⊆ V`. -/
theorem A_and_B20_to_B (hA : A) (h20 : RoundTrip.V6_20.B) : B := by
  intro n M _ _ _ _ _ _ cov hLC X Y Z W hX hY hZ hW p
  let α := {X : VF n M // IsSmoothVF X}
  let T : α → α → α → α → ℝ := fun X Y Z W => ⟪curv cov X.1 Y.1 Z.1 p, W.1 p⟫
  have key := fun (X Y Z W : α) =>
    h20 n M cov hLC X.1 Y.1 Z.1 W.1 X.2 Y.2 Z.2 W.2 p
  refine hA.1 T (fun X Y Z W => ?_) (fun X Y Z W => (key X Y Z W).2.2) (fun X Y Z W => ?_)
    ⟨X, hX⟩ ⟨Y, hY⟩ ⟨Z, hZ⟩ ⟨W, hW⟩
  · simp only [T]
    rw [← inner_add_left]
    exact (congrArg (fun v => ⟪v, W.1 p⟫) (key X Y Z W).1).trans (inner_zero_left _)
  · simp only [T]
    rw [← inner_add_left, ← inner_add_left]
    exact (congrArg (fun v => ⟪v, W.1 p⟫) (key X Y Z W).2.1).trans (inner_zero_left _)

#rt_check RoundTrip.V6_21.A_and_B20_to_B [Morse.octahedron, Morse.IsCurvatureTensor.inner_comm_pairs,
  Morse.inner_curvature_comm_pairs]

/-! ## The embedded special case

B is specialized to `M = ↥N` (`RoundTrip.Bridge.Sub hN`) for a slice submanifold `N ⊆ V` with
model `ℝⁿ`, the induced metric and the induced Levi-Civita connection `Bridge.conn` (`B_emb`).
Through the dictionary `Emb.D_curv` (the blind curvature of smooth fields, read in `V`, is the
project's `Morse.curvature` of the ambient fields) and `Emb.liftF` (an ambient tangent field
`Y : N → V` as a vector field on `↥N`), `B_emb` is exactly A's third clause
`inner_curvature_comm_pairs` for the model `ℝⁿ` (`A4n`). -/

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
        inner ℝ (curv (Bridge.conn (hN := hN)) X Y Z p) (W' p) =
          inner ℝ (curv (Bridge.conn (hN := hN)) Z W' X p) (Y p)

/-- A's third clause (`inner_curvature_comm_pairs`) for slice submanifolds modelled on `ℝⁿ`. -/
def A4n : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) (X Y Z' W' : N → V),
    (letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, V) ∞ X) →
    (letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, V) ∞ Y) →
    (letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, V) ∞ Z') →
    (letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, V) ∞ W') →
    Morse.IsTangentField hN X → Morse.IsTangentField hN Y → Morse.IsTangentField hN Z' →
    Morse.IsTangentField hN W' → ∀ q : N,
      ⟪Morse.curvature hN X Y Z' q, W' q⟫ = ⟪Morse.curvature hN Z' W' X q, Y q⟫

/-- `B_emb` is a special case of B (the induced connection is Levi-Civita, `Bridge.conn_isLC`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

theorem A_to_A4n : A → A4n := fun hA _ _ _ _ _ _ _ _ _ _ hN _ _ _ _ hX hY hZ hW hXT hYT hZT hWT q =>
  hA.2.2 hN hX hY hZ hW hXT hYT hZT hWT q

/-- **B on embedded manifolds is A's `inner_curvature_comm_pairs` for the model `ℝⁿ`**, through the
dictionary `Emb.D_curv`, `Emb.liftF`. -/
theorem B_emb_iff_A4n : B_emb ↔ A4n := by
  constructor
  · intro h V _ _ _ W _ _ _ n N hN X Y Z W' hX hY hZ hW hXT hYT hZT hWT q
    have e := h V W n N hN (Emb.liftF X) (Emb.liftF Y) (Emb.liftF Z) (Emb.liftF W')
      (Emb.isSmoothVF_liftF hX hXT) (Emb.isSmoothVF_liftF hY hYT) (Emb.isSmoothVF_liftF hZ hZT)
      (Emb.isSmoothVF_liftF hW hWT) q
    have e := (Emb.inner_curv _ _ (Emb.liftF Z) (Emb.isSmoothVF_liftF hX hXT)
      (Emb.isSmoothVF_liftF hY hYT) q (Emb.liftF W' q)).symm.trans
      (e.trans (Emb.inner_curv _ _ (Emb.liftF X) (Emb.isSmoothVF_liftF hZ hZT)
        (Emb.isSmoothVF_liftF hW hWT) q (Emb.liftF Y q)))
    have hW' : Bridge.D hN q (Emb.liftF (hN := hN) W' q) = W' q := Bridge.D_L (hWT q)
    have hY' : Bridge.D hN q (Emb.liftF (hN := hN) Y q) = Y q := Bridge.D_L (hYT q)
    rw [hW', hY', Emb.amb_liftF hXT, Emb.amb_liftF hYT, Emb.amb_liftF hZT,
      Emb.amb_liftF hWT] at e
    exact e
  · intro h V _ _ _ W _ _ _ n N hN X Y Z W' hX hY hZ hW p
    rw [Emb.inner_curv X Y Z hX hY p, Emb.inner_curv Z W' X hZ hW p]
    exact h V W n N hN (Bridge.amb X) (Bridge.amb Y) (Bridge.amb Z) (Bridge.amb W')
      (Bridge.contMDiff_amb hX) (Bridge.contMDiff_amb hY) (Bridge.contMDiff_amb hZ)
      (Bridge.contMDiff_amb hW) (Bridge.isTangentField_amb X) (Bridge.isTangentField_amb Y)
      (Bridge.isTangentField_amb Z) (Bridge.isTangentField_amb W') p

/-- **A implies B on embedded manifolds** (uses A's `inner_curvature_comm_pairs`). -/
theorem A_to_B_emb : A → B_emb := fun hA => B_emb_iff_A4n.2 (A_to_A4n hA)

/-- **B implies A's `inner_curvature_comm_pairs`** (model `ℝⁿ`), by specializing B to `↥N`. -/
theorem B_to_A4n : B → A4n := fun hB => B_emb_iff_A4n.1 (B_to_B_emb hB)

#rt_check RoundTrip.V6_21.A_to_B_emb [Morse.octahedron, Morse.IsCurvatureTensor.inner_comm_pairs,
  Morse.inner_curvature_comm_pairs]
#rt_check RoundTrip.V6_21.B_to_A4n [Morse.octahedron, Morse.IsCurvatureTensor.inner_comm_pairs,
  Morse.inner_curvature_comm_pairs]
#rt_overlap RoundTrip.V6_21.B_to_A4n [Morse.octahedron, Morse.IsCurvatureTensor.inner_comm_pairs,
  Morse.inner_curvature_comm_pairs]

end RoundTrip.V6_21
