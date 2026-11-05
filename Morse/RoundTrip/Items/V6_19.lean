import Morse
import RoundTrip.Check
import RoundTrip.Blind.V6_19
import RoundTrip.Bridge

open Bundle
open scoped ContDiff Manifold RealInnerProductSpace

namespace RoundTrip.V6_19

/-- The project's statement (universes instantiated at 0): Lemma 9.2 for the induced metric of a slice submanifold `N ⊆ V`: for a smooth surface `s : ℝ² → N` and a smooth tangent field `W` along it, `D/∂y D/∂x W − D/∂x D/∂y W = R(∂s/∂x, ∂s/∂y)W` with `R = curvOp` (`D_Y D_X − D_X D_Y`). -/
def A : Prop :=
  type_of% @Morse.covDerivY_covDerivX_sub.{0,0,0}

theorem A_holds : A := @Morse.covDerivY_covDerivX_sub

/-! ## The embedded special case

B is specialized to `M = ↥N` (`RoundTrip.Bridge.Sub hN`) for a slice submanifold `N ⊆ V` with
model `ℝⁿ`, the induced metric and the induced Levi-Civita connection `Bridge.conn` (`B_emb`).
Dictionary for parametrized surfaces (namespace `Emb`): a surface `s : ℝ² → ↥N` is smooth iff it
is smooth in `V` (`contMDiff_surf_iff`); a field `U` along `s` is read in `V` as
`ambS s U = (p ↦ D_{s p}(U p))` (`isSmoothSurfField_iff`); `∂s/∂x`, `∂s/∂y` read in `V` are the
project's `velX`, `velY` (`D_sx`, `D_sy`); and B's `DU/∂x = A` (`IsDx`, existence of an operation
obeying Milnor's axioms along every horizontal line) is `ambS s A = P(∂(ambS s U)/∂x)`, i.e. the
project's `covDerivX` (`isDx_iff`, `isDy_iff`, through `Bridge.hasCovDeriv_iff'`). With
`Emb.D_curv` (the blind curvature read in `V` is `Morse.curvature`) and `Morse.curvature_eq`,
`B_emb` is equivalent to A for the model `ℝⁿ` (`An`). -/

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

/-- A map from a normed space into `N` is smooth iff it is smooth in `V` (from
`Items/V8_12.lean`; generalizes `Bridge.contMDiffWithinAt_curve_iff`). -/
theorem contMDiffWithinAt_map_iff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Bridge.Sub hN} {s : Set E} {x : E} :
    ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, Rn n) ∞ f s x ↔
      ContDiffWithinAt ℝ ∞ (Bridge.incl hN ∘ f) s x := by
  constructor
  · intro h
    exact contMDiffWithinAt_iff_contDiffWithinAt.1
      ((Bridge.contMDiff_incl (f x)).comp_contMDiffWithinAt x h)
  · intro h
    have hcont : ContinuousWithinAt f s x :=
      (Topology.IsInducing.subtypeVal.continuousWithinAt_iff (f := f)).2 h.continuousWithinAt
    rw [contMDiffWithinAt_iff_target]
    refine ⟨hcont, ?_⟩
    set σ := Morse.sliceAt hN (f x)
    have hφ : ContDiffAt ℝ ∞ (fun y => (σ.φ y).1) (Bridge.incl hN (f x)) :=
      contDiff_fst.contDiffAt.comp _ ((Milnor.Problems.sliceChart_contDiffOn σ).contDiffAt
        (σ.φ.open_source.mem_nhds (Morse.mem_sliceAt_source hN (f x))))
    have e : (extChartAt 𝓘(ℝ, Rn n) (f x) ∘ f) =
        (fun y => (σ.φ y).1) ∘ (Bridge.incl hN ∘ f) := rfl
    rw [e]
    exact contMDiffWithinAt_iff_contDiffWithinAt.2 (hφ.comp_contDiffWithinAt x h)

/-- A parametrized surface in `↥N` is smooth iff it is smooth in `V`. -/
theorem contMDiff_surf_iff {s : ℝ × ℝ → Bridge.Sub hN} :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Rn n) ∞ s ↔ ContDiff ℝ ∞ (Bridge.incl hN ∘ s) := by
  rw [← contMDiffOn_univ, ← contDiffOn_univ]
  exact forall₂_congr fun _ _ => contMDiffWithinAt_map_iff

/-- The derivative of a map from a normed space into `N`, read in `V` (from `Items/V8_12.lean`). -/
theorem D_mfderiv_map {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → Bridge.Sub hN}
    {x : E} (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x) (v : E) :
    Bridge.D hN (f x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x v) = fderiv ℝ (Bridge.incl hN ∘ f) x v := by
  have h := HasMFDerivAt.comp x
    ((Bridge.contMDiff_incl (f x)).mdifferentiableAt (by simp)).hasMFDerivAt hf.hasMFDerivAt
  have h' : HasFDerivAt (Bridge.incl hN ∘ f)
      ((Bridge.D hN (f x)).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x : E →L[ℝ] Rn n)) x :=
    hasMFDerivAt_iff_hasFDerivAt.1 h
  have h'' : fderiv ℝ (Bridge.incl hN ∘ f) x =
      (Bridge.D hN (f x)).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x : E →L[ℝ] Rn n) :=
    HasFDerivAt.fderiv h'
  exact (DFunLike.congr_fun h'' v).symm

/-- `∂s/∂x`, read in `V`, is the project's `velX`. -/
theorem D_sx {s : ℝ × ℝ → Bridge.Sub hN} (hs : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Rn n) ∞ s)
    (p : ℝ × ℝ) : D hN (s p) (sx s p) = Morse.velX (N := N) s p :=
  D_mfderiv_map ((hs p).mdifferentiableAt (by simp)) _

/-- `∂s/∂y`, read in `V`, is the project's `velY`. -/
theorem D_sy {s : ℝ × ℝ → Bridge.Sub hN} (hs : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Rn n) ∞ s)
    (p : ℝ × ℝ) : D hN (s p) (sy s p) = Morse.velY (N := N) s p :=
  D_mfderiv_map ((hs p).mdifferentiableAt (by simp)) _

/-- A field along a surface, read in `V`. -/
noncomputable def ambS (s : ℝ × ℝ → Bridge.Sub hN)
    (U : (p : ℝ × ℝ) → TangentSpace 𝓘(ℝ, Rn n) (s p)) (p : ℝ × ℝ) : V :=
  D hN (s p) (U p)

theorem isSmoothSurfField_iff {s : ℝ × ℝ → Bridge.Sub hN}
    {U : (p : ℝ × ℝ) → TangentSpace 𝓘(ℝ, Rn n) (s p)} :
    IsSmoothSurfField s U ↔
      ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Rn n) ∞ s ∧ ContDiff ℝ ∞ (ambS s U) := by
  unfold IsSmoothSurfField
  constructor
  · intro h
    refine ⟨fun p => ?_, contMDiff_iff_contDiff.1 fun p => ?_⟩
    · exact contMDiffWithinAt_univ.1
        ((contMDiffWithinAt_tangent_iff (hN := hN)).1 (h p).contMDiffWithinAt).1
    · exact contMDiffWithinAt_univ.1
        ((contMDiffWithinAt_tangent_iff (hN := hN)).1 (h p).contMDiffWithinAt).2
  · rintro ⟨h1, h2⟩ p
    rw [← contMDiffWithinAt_univ]
    exact (contMDiffWithinAt_tangent_iff (hN := hN)).2
      ⟨(h1 p).contMDiffWithinAt, (contMDiff_iff_contDiff.2 h2 p).contMDiffWithinAt⟩

theorem contMDiff_lineX (y : ℝ) : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun x : ℝ => (x, y)) :=
  contMDiff_iff_contDiff.2 (contDiff_id.prodMk contDiff_const)

theorem contMDiff_lineY (x : ℝ) : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun y : ℝ => (x, y)) :=
  contMDiff_iff_contDiff.2 (contDiff_const.prodMk contDiff_id)

theorem isIntv_univ : RoundTrip.BridgePrelude.IsIntv (Set.univ : Set ℝ) :=
  ⟨Set.ordConnected_univ, uniqueDiffOn_univ⟩

/-- **Dictionary: `DU/∂x` along horizontal lines.** -/
theorem hasCovDeriv_x_iff {s : ℝ × ℝ → Bridge.Sub hN}
    {U A : (p : ℝ × ℝ) → TangentSpace 𝓘(ℝ, Rn n) (s p)} (hU : IsSmoothSurfField s U) (y : ℝ) :
    HasCovDeriv (conn (hN := hN)) (fun x => s (x, y)) Set.univ (fun x => U (x, y))
        (fun x => A (x, y)) ↔
      ∀ x : ℝ, ambS s A (x, y) = P hN (s (x, y)) (Morse.partialX (ambS s U) (x, y)) := by
  obtain ⟨hs, hF⟩ := isSmoothSurfField_iff.1 hU
  have hc : RoundTrip.BridgePrelude.IsSmoothCurve (n := n) (fun x => s (x, y)) Set.univ :=
    (hs.comp (contMDiff_lineX y)).contMDiffOn
  have hsm : RoundTrip.BridgePrelude.IsSmoothAlong (fun x => s (x, y)) Set.univ
      (fun x => U (x, y)) := (hU.comp (contMDiff_lineX y)).contMDiffOn
  have hd : ∀ x : ℝ, HasDerivAt (ambA (fun x => s (x, y)) (fun x => U (x, y)))
      (Morse.partialX (ambS s U) (x, y)) x :=
    fun x => Morse.hasDerivAt_partialX (hF.differentiable (by simp) (x, y))
  refine (hasCovDeriv_iff' isIntv_univ hc).trans ⟨fun h x => ?_, fun h => ⟨hsm, fun x _ => ?_⟩⟩
  · have := h.2 x (Set.mem_univ x)
    rw [derivWithin_univ, (hd x).deriv] at this
    exact this
  · rw [derivWithin_univ, (hd x).deriv]
    exact h x

/-- **Dictionary: `DU/∂y` along vertical lines.** -/
theorem hasCovDeriv_y_iff {s : ℝ × ℝ → Bridge.Sub hN}
    {U A : (p : ℝ × ℝ) → TangentSpace 𝓘(ℝ, Rn n) (s p)} (hU : IsSmoothSurfField s U) (x : ℝ) :
    HasCovDeriv (conn (hN := hN)) (fun y => s (x, y)) Set.univ (fun y => U (x, y))
        (fun y => A (x, y)) ↔
      ∀ y : ℝ, ambS s A (x, y) = P hN (s (x, y)) (Morse.partialY (ambS s U) (x, y)) := by
  obtain ⟨hs, hF⟩ := isSmoothSurfField_iff.1 hU
  have hc : RoundTrip.BridgePrelude.IsSmoothCurve (n := n) (fun y => s (x, y)) Set.univ :=
    (hs.comp (contMDiff_lineY x)).contMDiffOn
  have hsm : RoundTrip.BridgePrelude.IsSmoothAlong (fun y => s (x, y)) Set.univ
      (fun y => U (x, y)) := (hU.comp (contMDiff_lineY x)).contMDiffOn
  have hd : ∀ y : ℝ, HasDerivAt (ambA (fun y => s (x, y)) (fun y => U (x, y)))
      (Morse.partialY (ambS s U) (x, y)) y :=
    fun y => Morse.hasDerivAt_partialY (hF.differentiable (by simp) (x, y))
  refine (hasCovDeriv_iff' isIntv_univ hc).trans ⟨fun h y => ?_, fun h => ⟨hsm, fun y _ => ?_⟩⟩
  · have := h.2 y (Set.mem_univ y)
    rw [derivWithin_univ, (hd y).deriv] at this
    exact this
  · rw [derivWithin_univ, (hd y).deriv]
    exact h y

/-- **Dictionary: B's `DU/∂x = A`** is `A = P(∂U/∂x)` in `V` (the project's `covDerivX`). -/
theorem isDx_iff {s : ℝ × ℝ → Bridge.Sub hN}
    {U A : (p : ℝ × ℝ) → TangentSpace 𝓘(ℝ, Rn n) (s p)} (hU : IsSmoothSurfField s U) :
    IsDx (conn (hN := hN)) s U A ↔
      ∀ p, ambS s A p = P hN (s p) (Morse.partialX (ambS s U) p) := by
  constructor
  · intro h p
    exact (hasCovDeriv_x_iff hU p.2).1 (h 0 p.2) p.1
  · intro h _ y
    exact (hasCovDeriv_x_iff hU y).2 fun x => h (x, y)

/-- **Dictionary: B's `DU/∂y = A`** is `A = P(∂U/∂y)` in `V` (the project's `covDerivY`). -/
theorem isDy_iff {s : ℝ × ℝ → Bridge.Sub hN}
    {U A : (p : ℝ × ℝ) → TangentSpace 𝓘(ℝ, Rn n) (s p)} (hU : IsSmoothSurfField s U) :
    IsDy (conn (hN := hN)) s U A ↔
      ∀ p, ambS s A p = P hN (s p) (Morse.partialY (ambS s U) p) := by
  constructor
  · intro h p
    exact (hasCovDeriv_y_iff hU p.1).1 (h p.1 0) p.2
  · intro h x _
    exact (hasCovDeriv_y_iff hU x).2 fun y => h (x, y)

/-- The project's `covDerivX` of a smooth ambient field. -/
theorem covDerivX_eq' {s : ℝ × ℝ → Bridge.Sub hN} {F : ℝ × ℝ → V} (hF : ContDiff ℝ ∞ F) :
    Morse.covDerivX hN s F = fun q => P hN (s q) (Morse.partialX F q) := by
  funext q
  show Morse.tanProj hN (s q) (deriv (fun x => F (x, q.2)) q.1) = _
  rw [(Morse.hasDerivAt_partialX (hF.differentiable (by simp) q)).deriv]
  rfl

/-- The project's `covDerivY` of a smooth ambient field. -/
theorem covDerivY_eq' {s : ℝ × ℝ → Bridge.Sub hN} {F : ℝ × ℝ → V} (hF : ContDiff ℝ ∞ F) :
    Morse.covDerivY hN s F = fun q => P hN (s q) (Morse.partialY F q) := by
  funext q
  show Morse.tanProj hN (s q) (deriv (fun y => F (q.1, y)) q.2) = _
  rw [(Morse.hasDerivAt_partialY (hF.differentiable (by simp) q)).deriv]
  rfl

theorem contDiff_P_comp {s : ℝ × ℝ → Bridge.Sub hN}
    (hs : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Rn n) ∞ s) : ContDiff ℝ ∞ (fun q => P hN (s q)) :=
  Morse.contDiff_comp_map hN (contMDiff_surf_iff.1 hs) (Morse.contMDiff_tanProj hN)

/-- The blind curvature read in `V` is `curvOp` (with the project's `Morse.curvature_eq`). -/
theorem D_curv_eq_curvOp [FiniteDimensional ℝ W] {X Y Z : VF n (Bridge.Sub hN)} (hX : IsSmoothVF X)
    (hY : IsSmoothVF Y) (hZ : IsSmoothVF Z) (q : Bridge.Sub hN) :
    D hN q (curv (conn (hN := hN)) X Y Z q) = Morse.curvOp hN q (amb X q) (amb Y q) (amb Z q) :=
  (D_curv X Y Z hX hY q).trans (Morse.curvature_eq hN (contMDiff_amb hX) (contMDiff_amb hY)
    (contMDiff_amb hZ) (isTangentField_amb X) (isTangentField_amb Y) (isTangentField_amb Z) q)

theorem amb_eq_of_eq {X : VF n (Bridge.Sub hN)} {q : Bridge.Sub hN}
    {v : TangentSpace 𝓘(ℝ, Rn n) q} (h : X q = v) : amb X q = D hN q v := by
  show D hN q (X q) = _
  rw [h]

end Emb

/-- B on embedded manifolds: `M = ↥N` with the induced metric and the induced Levi-Civita
connection (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    (s : ℝ × ℝ → Bridge.Sub hN), ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Rn n) ∞ s →
    ∀ U : (p : ℝ × ℝ) → TangentSpace 𝓘(ℝ, Rn n) (s p), IsSmoothSurfField s U →
      ∃ A B' C D' : (p : ℝ × ℝ) → TangentSpace 𝓘(ℝ, Rn n) (s p),
        IsDx (Bridge.conn (hN := hN)) s U A ∧ IsDy (Bridge.conn (hN := hN)) s U B' ∧
        IsDy (Bridge.conn (hN := hN)) s A C ∧ IsDx (Bridge.conn (hN := hN)) s B' D' ∧
        ∀ p : ℝ × ℝ, ∀ X Y Z : VF n (Bridge.Sub hN), IsSmoothVF X → IsSmoothVF Y → IsSmoothVF Z →
          X (s p) = sx s p → Y (s p) = sy s p → Z (s p) = U p →
          C p - D' p = curv (Bridge.conn (hN := hN)) X Y Z (s p)

/-- A for slice submanifolds modelled on `ℝⁿ` (with `W` finite-dimensional). -/
def An : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) (s : ℝ × ℝ → N),
    ContDiff ℝ ∞ (fun p => (s p : V)) → ∀ W' : ℝ × ℝ → V, ContDiff ℝ ∞ W' →
    (∀ p, W' p ∈ Morse.tangentSubspace hN (s p)) → ∀ p : ℝ × ℝ,
      Morse.covDerivY hN s (Morse.covDerivX hN s W') p -
          Morse.covDerivX hN s (Morse.covDerivY hN s W') p =
        Morse.curvOp hN (s p) (Morse.velX s p) (Morse.velY s p) (W' p)

/-- `B_emb` is a special case of B (the induced connection is Levi-Civita, `Bridge.conn_isLC`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

theorem A_to_An : A → An := fun hA _ _ _ _ _ _ _ _ _ _ hN _ hs _ hW hWT p => hA hN hs hW hWT p

open Emb in
/-- **A implies B on embedded manifolds** (uses A). The four covariant derivatives are the
projected partial derivatives; their difference is A's commutator. -/
theorem An_to_B_emb : An → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN s hs U hU
  have hF : ContDiff ℝ ∞ (ambS s U) := (isSmoothSurfField_iff.1 hU).2
  have hPs := contDiff_P_comp hs
  let A : (p : ℝ × ℝ) → TangentSpace 𝓘(ℝ, Rn n) (s p) :=
    fun p => Bridge.L hN (s p) (Bridge.P hN (s p) (Morse.partialX (ambS s U) p))
  let B' : (p : ℝ × ℝ) → TangentSpace 𝓘(ℝ, Rn n) (s p) :=
    fun p => Bridge.L hN (s p) (Bridge.P hN (s p) (Morse.partialY (ambS s U) p))
  have hAa : ambS s A = fun p => Bridge.P hN (s p) (Morse.partialX (ambS s U) p) :=
    funext fun p => Bridge.D_L_P _ _
  have hBa : ambS s B' = fun p => Bridge.P hN (s p) (Morse.partialY (ambS s U) p) :=
    funext fun p => Bridge.D_L_P _ _
  have hAs' : ContDiff ℝ ∞ (ambS s A) := by
    rw [hAa]; exact hPs.clm_apply (Morse.contDiff_partialX hF)
  have hBs' : ContDiff ℝ ∞ (ambS s B') := by
    rw [hBa]; exact hPs.clm_apply (Morse.contDiff_partialY hF)
  have hAs : IsSmoothSurfField s A := isSmoothSurfField_iff.2 ⟨hs, hAs'⟩
  have hBs : IsSmoothSurfField s B' := isSmoothSurfField_iff.2 ⟨hs, hBs'⟩
  let C : (p : ℝ × ℝ) → TangentSpace 𝓘(ℝ, Rn n) (s p) :=
    fun p => Bridge.L hN (s p) (Bridge.P hN (s p) (Morse.partialY (ambS s A) p))
  let D' : (p : ℝ × ℝ) → TangentSpace 𝓘(ℝ, Rn n) (s p) :=
    fun p => Bridge.L hN (s p) (Bridge.P hN (s p) (Morse.partialX (ambS s B') p))
  refine ⟨A, B', C, D', (isDx_iff hU).2 fun p => Bridge.D_L_P _ _,
    (isDy_iff hU).2 fun p => Bridge.D_L_P _ _, (isDy_iff hAs).2 fun p => Bridge.D_L_P _ _,
    (isDx_iff hBs).2 fun p => Bridge.D_L_P _ _, ?_⟩
  intro p X Y Z hX hY hZ hXp hYp hZp
  apply Bridge.D_injective (s p)
  have e1 : Morse.covDerivX hN s (ambS s U) = ambS s A := by rw [covDerivX_eq' hF, hAa]
  have e2 : Morse.covDerivY hN s (ambS s U) = ambS s B' := by rw [covDerivY_eq' hF, hBa]
  have hC : Bridge.D hN (s p) (C p) =
      Morse.covDerivY hN s (Morse.covDerivX hN s (ambS s U)) p := by
    rw [e1, covDerivY_eq' hAs']
    exact Bridge.D_L_P _ _
  have hD : Bridge.D hN (s p) (D' p) =
      Morse.covDerivX hN s (Morse.covDerivY hN s (ambS s U)) p := by
    rw [e2, covDerivX_eq' hBs']
    exact Bridge.D_L_P _ _
  have hA := hA V W n N hN s (contMDiff_surf_iff.1 hs) (ambS s U) hF
    (fun q => Bridge.D_mem (s q) (U q)) p
  rw [Bridge.D_tsub_aux, hC, hD, hA, D_curv_eq_curvOp hX hY hZ (s p), amb_eq_of_eq hXp, amb_eq_of_eq hYp, amb_eq_of_eq hZp,
    D_sx hs, D_sy hs]
  rfl

open Emb in
/-- **B on embedded manifolds implies A** (model `ℝⁿ`): B's covariant derivatives along `s` are
forced to be the projected partial derivatives (`isDx_iff`, `isDy_iff`), and B's curvature term,
evaluated on the extensions `Bridge.ext`, is `curvOp` (via `Morse.curvature_eq`). -/
theorem B_emb_to_An : B_emb → An := by
  intro h V _ _ _ W _ _ _ n N hN (s : ℝ × ℝ → Bridge.Sub hN) hS W' hW hWT p
  have hs : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Rn n) ∞ s := contMDiff_surf_iff.2 hS
  let U : (p : ℝ × ℝ) → TangentSpace 𝓘(ℝ, Rn n) (s p) := fun p => Bridge.L hN (s p) (W' p)
  have hUa : ambS s U = W' := funext fun p => Bridge.D_L (hWT p)
  have hU : IsSmoothSurfField s U := isSmoothSurfField_iff.2 ⟨hs, by rw [hUa]; exact hW⟩
  obtain ⟨A, B', C, D', hA, hB, hC, hD, hEq⟩ := h V W n N hN s hs U hU
  have hPs := contDiff_P_comp hs
  have hAa : ambS s A = fun q => Bridge.P hN (s q) (Morse.partialX W' q) := by
    funext q; rw [(isDx_iff hU).1 hA q, hUa]
  have hBa : ambS s B' = fun q => Bridge.P hN (s q) (Morse.partialY W' q) := by
    funext q; rw [(isDy_iff hU).1 hB q, hUa]
  have hAs' : ContDiff ℝ ∞ (ambS s A) := by
    rw [hAa]; exact hPs.clm_apply (Morse.contDiff_partialX hW)
  have hBs' : ContDiff ℝ ∞ (ambS s B') := by
    rw [hBa]; exact hPs.clm_apply (Morse.contDiff_partialY hW)
  have hAs : IsSmoothSurfField s A := isSmoothSurfField_iff.2 ⟨hs, hAs'⟩
  have hBs : IsSmoothSurfField s B' := isSmoothSurfField_iff.2 ⟨hs, hBs'⟩
  have e1 : Morse.covDerivX hN s W' = ambS s A := by rw [covDerivX_eq' hW, hAa]
  have e2 : Morse.covDerivY hN s W' = ambS s B' := by rw [covDerivY_eq' hW, hBa]
  have hCp : Morse.covDerivY hN s (Morse.covDerivX hN s W') p = Bridge.D hN (s p) (C p) := by
    rw [e1, covDerivY_eq' hAs']
    exact ((isDy_iff hAs).1 hC p).symm
  have hDp : Morse.covDerivX hN s (Morse.covDerivY hN s W') p = Bridge.D hN (s p) (D' p) := by
    rw [e2, covDerivX_eq' hBs']
    exact ((isDx_iff hBs).1 hD p).symm
  have hX := Bridge.isSmoothVF_ext (hN := hN) (Bridge.D hN (s p) (sx s p))
  have hY := Bridge.isSmoothVF_ext (hN := hN) (Bridge.D hN (s p) (sy s p))
  have hZ := Bridge.isSmoothVF_ext (hN := hN) (Bridge.D hN (s p) (U p))
  have e := hEq p _ _ _ hX hY hZ (Bridge.ext_apply_D _ _) (Bridge.ext_apply_D _ _)
    (Bridge.ext_apply_D _ _)
  rw [hCp, hDp, ← Bridge.D_tsub_aux, e, D_curv_eq_curvOp hX hY hZ (s p), amb_eq_of_eq (Bridge.ext_apply_D _ _),
    amb_eq_of_eq (Bridge.ext_apply_D _ _), amb_eq_of_eq (Bridge.ext_apply_D _ _), D_sx hs, D_sy hs]
  exact congrArg _ (Bridge.D_L (hWT p))

/-- **A implies B on embedded manifolds** (uses A). -/
theorem A_to_B_emb : A → B_emb := fun hA => An_to_B_emb (A_to_An hA)

/-- **B implies A for the model `ℝⁿ`**, by specializing B to `↥N`. -/
theorem B_to_An : B → An := fun hB => B_emb_to_An (B_to_B_emb hB)

#rt_check RoundTrip.V6_19.A_to_B_emb [Morse.covDerivY_covDerivX_sub]
#rt_check RoundTrip.V6_19.B_to_An [Morse.covDerivY_covDerivX_sub]
#rt_overlap RoundTrip.V6_19.B_to_An [Morse.covDerivY_covDerivX_sub]

end RoundTrip.V6_19
