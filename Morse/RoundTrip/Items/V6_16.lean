import Morse
import RoundTrip.Check
import RoundTrip.Blind.V6_16
import RoundTrip.Bridge

open Filter Topology
open scoped ContDiff Manifold

namespace RoundTrip.V6_16

/-- The project's statement (universes instantiated at 0; `milnorCurvature`, `nomizuCurvature`
(abstract, Mathlib `CovariantDerivative`, any model `I`) and `curvature` (embedded `N ⊆ V`, induced
connection) are definitions): Nomizu's curvature is minus Milnor's, and `R(Y, X)Z = −R(X, Y)Z`. -/
def A : Prop :=
  type_of% @Morse.milnorCurvature_eq_neg.{0,0,0} ∧ type_of% @Morse.milnorCurvature_swap.{0,0,0}

theorem A_holds : A := ⟨@Morse.milnorCurvature_eq_neg, @Morse.milnorCurvature_swap⟩

/-- Vocabulary check: B's `curv` / `nomizuCurv` are the project's `milnorCurvature` /
`nomizuCurvature` for the model `𝓘(ℝ, ℝⁿ)` (definitionally). -/
example {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
    (cov : Conn n M) (X Y Z : VF n M) :
    curv cov X Y Z = Morse.milnorCurvature cov X Y Z ∧
      nomizuCurv cov X Y Z = Morse.nomizuCurvature cov X Y Z := ⟨rfl, rfl⟩

/-- **Part (i) of B from A**: Nomizu's `R` is minus Milnor's (A's `milnorCurvature_eq_neg`, used). -/
theorem A_to_B_part_i (hA : A) (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (Rn n) M]
    [IsManifold 𝓘(ℝ, Rn n) ∞ M] (cov : Conn n M) (X Y Z : VF n M) (p : M) :
    nomizuCurv cov X Y Z p = -(curv cov X Y Z p) := by
  have h := hA.1 cov X Y Z p
  change curv cov X Y Z p = -nomizuCurv cov X Y Z p at h
  rw [h, neg_neg]

/-- B ⇒ A holds only because A is provable outright (algebra and Mathlib's `mlieBracket_swap`);
B's sign statement is only for smooth fields of a smooth connection on `ℝⁿ`-manifolds, A for all
fields, all connections, all models. -/
theorem B_to_A : B → A := by
  intro _
  refine ⟨?_, ?_⟩
  · intro E _ _ H _ I M _ _ _ cov X Y Z x
    simp only [Morse.milnorCurvature, Morse.nomizuCurvature]
    abel
  · intro E _ _ H _ I M _ _ _ cov X Y Z x
    simp only [Morse.milnorCurvature]
    rw [VectorField.mlieBracket_swap]
    simp only [Pi.neg_apply, map_neg]
    abel

#rt_check RoundTrip.V6_16.A_to_B_part_i [Morse.milnorCurvature_eq_neg, Morse.milnorCurvature_swap]
#rt_check RoundTrip.V6_16.B_to_A [Morse.milnorCurvature_eq_neg, Morse.milnorCurvature_swap]
#rt_overlap RoundTrip.V6_16.B_to_A [Morse.milnorCurvature_eq_neg, Morse.milnorCurvature_swap]

/-! ## B's part (ii): coordinate fields have vanishing brackets

On the chart source of `extChartAt p`, B's `coordField p i` agrees near every point with Mathlib's
pull-back of the constant field `eᵢ` by the chart (`coordField_eventuallyEq`); by the naturality
of the Lie bracket under pull-back (`VectorField.mpullback_mlieBracket`) the bracket
`[∂ᵢ, ∂ⱼ]` is the pull-back of the bracket of two constant fields on `ℝⁿ`, which is `0`
(`mlieBracket_coordField`). So the term `[∂ᵢ, ∂ⱼ] ⊢ Z` of `R(∂ᵢ, ∂ⱼ)Z` vanishes and B's part (ii)
holds on every `ℝⁿ`-manifold, for every connection and every field `Z` (`B_part_ii`), without any
hypothesis. With A's `milnorCurvature_eq_neg` for part (i), this gives `A_to_B`. -/

section CoordFields

open VectorField

set_option linter.unusedSectionVars false

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]

/-- Near a point of the chart source, `∂ᵢ` is Mathlib's pull-back of the constant field `eᵢ`. -/
theorem coordField_eventuallyEq (p x : M) (hx : x ∈ (extChartAt 𝓘(ℝ, Rn n) p).source)
    (i : Fin n) :
    coordField p i =ᶠ[𝓝 x] mpullback 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) (extChartAt 𝓘(ℝ, Rn n) p)
      (fun _ => EuclideanSpace.single i (1 : ℝ)) := by
  filter_upwards [(isOpen_extChartAt_source p).mem_nhds hx] with y hy
  simp only [coordField, if_pos hy]
  rfl

/-- **`[∂ᵢ, ∂ⱼ] = 0`** on the chart source. -/
theorem mlieBracket_coordField (p x : M) (hx : x ∈ (extChartAt 𝓘(ℝ, Rn n) p).source)
    (i j : Fin n) :
    mlieBracket 𝓘(ℝ, Rn n) (coordField p i) (coordField p j) x = 0 := by
  rw [(coordField_eventuallyEq p x hx i).mlieBracket_vectorField_eq
    (coordField_eventuallyEq p x hx j)]
  have hc : ∀ k : Fin n, MDifferentiableAt 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n).tangent
      (fun y : Rn n => (⟨y, EuclideanSpace.single k (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, Rn n) (Rn n)))
      (extChartAt 𝓘(ℝ, Rn n) p x) := fun k =>
    (contMDiffAt_vectorSpace_iff_contDiffAt.2 (contDiffAt_const (c := EuclideanSpace.single k (1 : ℝ)))).mdifferentiableAt
      (n := ∞) (by simp)
  have hf : ContMDiffAt 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) ∞ (extChartAt 𝓘(ℝ, Rn n) p) x :=
    contMDiffAt_extChartAt' (by rwa [extChartAt_source] at hx)
  have hle : minSmoothness ℝ 2 ≤ ∞ := by
    rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top
  have : IsManifold 𝓘(ℝ, Rn n) (minSmoothness ℝ 2) M := IsManifold.of_le hle
  rw [← mpullback_mlieBracket (hc i) (hc j) hf hle, mpullback_apply]
  have h0 : mlieBracket 𝓘(ℝ, Rn n)
      (fun y : Rn n => (EuclideanSpace.single i (1 : ℝ) : TangentSpace 𝓘(ℝ, Rn n) y))
      (fun y : Rn n => (EuclideanSpace.single j (1 : ℝ) : TangentSpace 𝓘(ℝ, Rn n) y))
      (extChartAt 𝓘(ℝ, Rn n) p x) = 0 := by
    have e := congrFun (mlieBracketWithin_eq_lieBracketWithin (𝕜 := ℝ) (E := Rn n)
      (V := fun y : Rn n => (EuclideanSpace.single i (1 : ℝ) : TangentSpace 𝓘(ℝ, Rn n) y))
      (W := fun y : Rn n => (EuclideanSpace.single j (1 : ℝ) : TangentSpace 𝓘(ℝ, Rn n) y))
      (s := Set.univ)) (extChartAt 𝓘(ℝ, Rn n) p x)
    refine e.trans ?_
    rw [lieBracketWithin_univ]
    simp [lieBracket]
    rfl
  rw [h0, map_zero]

/-- **B's part (ii) holds outright**: `R(∂ᵢ, ∂ⱼ)Z = −∂ᵢ ⊢ (∂ⱼ ⊢ Z) + ∂ⱼ ⊢ (∂ᵢ ⊢ Z)` on the chart
source, for any connection and any field `Z`. -/
theorem B_part_ii (cov : Conn n M) (Z : VF n M) (p x : M)
    (hx : x ∈ (extChartAt 𝓘(ℝ, Rn n) p).source) (i j : Fin n) :
    curv cov (coordField p i) (coordField p j) Z x
      = -(cov (fun y => cov Z y (coordField p j y)) x (coordField p i x))
        + cov (fun y => cov Z y (coordField p i y)) x (coordField p j x) := by
  show _ + _ + cov Z x (mlieBracket 𝓘(ℝ, Rn n) (coordField p i) (coordField p j) x) = _
  rw [mlieBracket_coordField p x hx i j, map_zero, add_zero]

end CoordFields

/-- **A implies B** (revised: part (i) from A's `milnorCurvature_eq_neg`, part (ii) proved
outright, `B_part_ii`). -/
theorem A_to_B : A → B := fun hA n M _ _ _ _ _ _ cov _ =>
  ⟨fun X Y Z _ _ _ p => A_to_B_part_i hA n M cov X Y Z p,
    fun Z _ p x hx i j => B_part_ii cov Z p x hx i j⟩

#rt_check RoundTrip.V6_16.A_to_B [Morse.milnorCurvature_eq_neg, Morse.milnorCurvature_swap]

/-! ## The embedded special case

B is specialized to `M = ↥N` (`RoundTrip.Bridge.Sub hN`) for a slice submanifold `N ⊆ V` with
model `ℝⁿ`, the induced metric and the induced connection `Bridge.conn` (`B_emb`, a special case of
B: `B_to_B_emb`). Since A is about Mathlib's abstract `CovariantDerivative` on any model (not about
embedded manifolds), `A_to_B_emb` is `A_to_B` followed by `B_to_B_emb`, and `B_emb → A` is as
vacuous as `B_to_A`. The embedded content of this item is the vocabulary: the project's embedded
curvature `Morse.curvature hN` (a definition of this item) is A's `milnorCurvature` (= B's `curv`)
of the induced connection, read in `V` (`Emb.D_milnorCurvature`, for smooth `X`, `Y`). -/

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

/-- **Dictionary between the project's two curvature definitions**: A's abstract
`milnorCurvature` of the induced connection on `↥N`, read in `V`, is the project's embedded
`Morse.curvature` of the ambient fields. -/
theorem D_milnorCurvature (X Y Z : VF n (Bridge.Sub hN)) (hX : IsSmoothVF X) (hY : IsSmoothVF Y)
    (p : Bridge.Sub hN) :
    D hN p (Morse.milnorCurvature (conn (hN := hN)) X Y Z p) =
      Morse.curvature hN (amb X) (amb Y) (amb Z) p :=
  D_curv X Y Z hX hY p

end Emb

/-- B on embedded manifolds: `M = ↥N` with the induced metric and the induced connection
(a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N),
    (∀ X Y Z : VF n (Bridge.Sub hN), IsSmoothVF X → IsSmoothVF Y → IsSmoothVF Z →
      ∀ p : Bridge.Sub hN,
        nomizuCurv (Bridge.conn (hN := hN)) X Y Z p = -(curv (Bridge.conn (hN := hN)) X Y Z p)) ∧
    (∀ Z : VF n (Bridge.Sub hN), IsSmoothVF Z → ∀ (p x : Bridge.Sub hN),
      x ∈ (extChartAt 𝓘(ℝ, Rn n) p).source → ∀ i j : Fin n,
        curv (Bridge.conn (hN := hN)) (coordField p i) (coordField p j) Z x
          = -(Bridge.conn (hN := hN) (fun y => Bridge.conn (hN := hN) Z y (coordField p j y)) x
              (coordField p i x))
            + Bridge.conn (hN := hN) (fun y => Bridge.conn (hN := hN) Z y (coordField p i y)) x
              (coordField p j x))

/-- `B_emb` is a special case of B (the induced connection is smooth, `Bridge.conn_isGlobalConn`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ n _ hN =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isGlobalConn

/-- **A implies B on embedded manifolds** (through `A_to_B`). -/
theorem A_to_B_emb : A → B_emb := fun hA => B_to_B_emb (A_to_B hA)

#rt_check RoundTrip.V6_16.A_to_B_emb [Morse.milnorCurvature_eq_neg, Morse.milnorCurvature_swap]

end RoundTrip.V6_16
