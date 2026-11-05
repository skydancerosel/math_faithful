import Morse
import RoundTrip.Check
import RoundTrip.Blind.V6_15
import RoundTrip.Bridge

open Set
open scoped ContDiff Manifold

namespace RoundTrip.V6_15

/-- The project's statement (universes instantiated at 0): Lemma 8.7 for the induced connection of a slice submanifold `N ⊆ V` (`velX`, `velY`, `covDerivX`, `covDerivY` are definitions: `∂s/∂x` computed in `V`, `D/∂x = P ∘ ∂/∂x`): `DW/∂x = P(∂W/∂x)` for `W` differentiable, and `D/∂x ∂s/∂y = D/∂y ∂s/∂x` for a smooth surface `s : ℝ² → N`. -/
def A : Prop :=
  type_of% @Morse.covDerivX_eq.{0,0,0} ∧
    type_of% @Morse.covDerivX_velY.{0,0,0}

theorem A_holds : A := ⟨@Morse.covDerivX_eq, @Morse.covDerivX_velY⟩

/-! ## The embedded special case

B is specialized to `M = ↥N` (`RoundTrip.Bridge.Sub hN`) for a slice submanifold `N ⊆ V` with
model `ℝⁿ` and the induced connection `Bridge.conn` (`B_emb`; it is smooth and symmetric,
`Bridge.conn_isGlobalConn`, `Bridge.conn_isSymm`). Dictionary (namespace `Emb`): a surface
`s : ℝ² → ↥N` is smooth iff it is smooth in `V` (`contMDiff_surf_iff`), `∂s/∂x`, `∂s/∂y` read in
`V` are the project's `velX`, `velY` (`D_sx`, `D_sy`), and B's "`D/∂x (∂s/∂y) = u` at `(x₀, y₀)`"
(`CovDerivAt`, existence of an operation obeying Milnor's axioms along the line `y = y₀`) is
`D u = covDerivX hN s (velY s) (x₀, y₀)` (`covDerivAt_x_iff`, through `Bridge.hasCovDeriv_iff`);
likewise for `D/∂y (∂s/∂x)`. Hence `B_emb` is exactly A's `covDerivX_velY` for the model `ℝⁿ`
(`A87n`). -/

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

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

theorem contMDiff_lineX (y : ℝ) : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun x : ℝ => (x, y)) :=
  contMDiff_iff_contDiff.2 (contDiff_id.prodMk contDiff_const)

theorem contMDiff_lineY (x : ℝ) : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun y : ℝ => (x, y)) :=
  contMDiff_iff_contDiff.2 (contDiff_const.prodMk contDiff_id)

theorem isIntv_univ : RoundTrip.BridgePrelude.IsIntv (Set.univ : Set ℝ) :=
  ⟨Set.ordConnected_univ, uniqueDiffOn_univ⟩

theorem contDiff_velX {s : ℝ × ℝ → Bridge.Sub hN} (hs : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Rn n) ∞ s) :
    ContDiff ℝ ∞ (Morse.velX (N := N) s) :=
  Morse.contDiff_partialX (contMDiff_surf_iff.1 hs)

theorem contDiff_velY {s : ℝ × ℝ → Bridge.Sub hN} (hs : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Rn n) ∞ s) :
    ContDiff ℝ ∞ (Morse.velY (N := N) s) :=
  Morse.contDiff_partialY (contMDiff_surf_iff.1 hs)

/-- **Dictionary: `D/∂x (∂s/∂y)` at a point.** -/
theorem covDerivAt_x_iff {s : ℝ × ℝ → Bridge.Sub hN}
    (hs : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Rn n) ∞ s) (x₀ y₀ : ℝ)
    (u : TangentSpace 𝓘(ℝ, Rn n) (s (x₀, y₀))) :
    CovDerivAt (conn (hN := hN)) (fun x => s (x, y₀)) (fun x => sy s (x, y₀)) x₀ u ↔
      D hN (s (x₀, y₀)) u = Morse.covDerivX hN s (Morse.velY (N := N) s) (x₀, y₀) := by
  have hc : RoundTrip.BridgePrelude.IsSmoothCurve (n := n) (fun x => s (x, y₀)) univ :=
    (hs.comp (contMDiff_lineX y₀)).contMDiffOn
  have hamb : ambA (fun x => s (x, y₀)) (fun x => sy s (x, y₀)) =
      fun x => Morse.velY (N := N) s (x, y₀) := funext fun x => D_sy hs (x, y₀)
  have hsm : RoundTrip.BridgePrelude.IsSmoothAlong (n := n) (fun x => s (x, y₀)) univ
      (fun x => sy s (x, y₀)) := by
    refine isSmoothAlong_iff.2 ⟨hc, ?_⟩
    rw [hamb]
    exact ((contDiff_velY hs).comp (contDiff_id.prodMk contDiff_const)).contDiffOn
  have key : Morse.covDerivX hN s (Morse.velY (N := N) s) (x₀, y₀) =
      P hN (s (x₀, y₀)) (derivWithin (ambA (fun x => s (x, y₀)) (fun x => sy s (x, y₀))) univ x₀) := by
    rw [derivWithin_univ, hamb]
    rfl
  constructor
  · rintro ⟨Wf, hW, hWu⟩
    have := ((hasCovDeriv_iff' isIntv_univ hc).1 hW).2 x₀ (mem_univ _)
    rw [key, ← this, ← hWu]
    rfl
  · intro h
    refine ⟨covA (fun x => s (x, y₀)) univ (fun x => sy s (x, y₀)),
      (hasCovDeriv_iff isIntv_univ hc).2 ⟨hsm, fun _ _ => rfl⟩, ?_⟩
    apply D_injective (s (x₀, y₀))
    exact (D_covA (fun x => s (x, y₀)) univ (fun x => sy s (x, y₀)) x₀).trans (h.trans key).symm

/-- **Dictionary: `D/∂y (∂s/∂x)` at a point.** -/
theorem covDerivAt_y_iff {s : ℝ × ℝ → Bridge.Sub hN}
    (hs : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Rn n) ∞ s) (x₀ y₀ : ℝ)
    (u : TangentSpace 𝓘(ℝ, Rn n) (s (x₀, y₀))) :
    CovDerivAt (conn (hN := hN)) (fun y => s (x₀, y)) (fun y => sx s (x₀, y)) y₀ u ↔
      D hN (s (x₀, y₀)) u = Morse.covDerivY hN s (Morse.velX (N := N) s) (x₀, y₀) := by
  have hc : RoundTrip.BridgePrelude.IsSmoothCurve (n := n) (fun y => s (x₀, y)) univ :=
    (hs.comp (contMDiff_lineY x₀)).contMDiffOn
  have hamb : ambA (fun y => s (x₀, y)) (fun y => sx s (x₀, y)) =
      fun y => Morse.velX (N := N) s (x₀, y) := funext fun y => D_sx hs (x₀, y)
  have hsm : RoundTrip.BridgePrelude.IsSmoothAlong (n := n) (fun y => s (x₀, y)) univ
      (fun y => sx s (x₀, y)) := by
    refine isSmoothAlong_iff.2 ⟨hc, ?_⟩
    rw [hamb]
    exact ((contDiff_velX hs).comp (contDiff_const.prodMk contDiff_id)).contDiffOn
  have key : Morse.covDerivY hN s (Morse.velX (N := N) s) (x₀, y₀) =
      P hN (s (x₀, y₀)) (derivWithin (ambA (fun y => s (x₀, y)) (fun y => sx s (x₀, y))) univ y₀) := by
    rw [derivWithin_univ, hamb]
    rfl
  constructor
  · rintro ⟨Wf, hW, hWu⟩
    have := ((hasCovDeriv_iff' isIntv_univ hc).1 hW).2 y₀ (mem_univ _)
    rw [key, ← this, ← hWu]
    rfl
  · intro h
    refine ⟨covA (fun y => s (x₀, y)) univ (fun y => sx s (x₀, y)),
      (hasCovDeriv_iff isIntv_univ hc).2 ⟨hsm, fun _ _ => rfl⟩, ?_⟩
    apply D_injective (s (x₀, y₀))
    exact (D_covA (fun y => s (x₀, y)) univ (fun y => sx s (x₀, y)) y₀).trans (h.trans key).symm

end Emb

/-- B on embedded manifolds: `M = ↥N` with the induced metric and the induced connection
(a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    (s : ℝ × ℝ → Bridge.Sub hN), ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Rn n) ∞ s → ∀ x₀ y₀ : ℝ,
      ∃ u : TangentSpace 𝓘(ℝ, Rn n) (s (x₀, y₀)),
        CovDerivAt (Bridge.conn (hN := hN)) (fun x => s (x, y₀)) (fun x => sy s (x, y₀)) x₀ u ∧
        CovDerivAt (Bridge.conn (hN := hN)) (fun y => s (x₀, y)) (fun y => sx s (x₀, y)) y₀ u

/-- A's `covDerivX_velY` (Lemma 8.7) for slice submanifolds modelled on `ℝⁿ`. -/
def A87n : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) (s : ℝ × ℝ → N),
    ContDiff ℝ ∞ (fun p => (s p : V)) → ∀ p : ℝ × ℝ,
      Morse.covDerivX hN s (Morse.velY s) p = Morse.covDerivY hN s (Morse.velX s) p

/-- `B_emb` is a special case of B (the induced connection is smooth and symmetric). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ n _ hN =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isGlobalConn Bridge.conn_isSymm

theorem A_to_A87n : A → A87n := fun hA _ _ _ _ _ _ _ _ _ hN _ hs p => hA.2 hN hs p

/-- **B on embedded manifolds is A's Lemma 8.7 for the model `ℝⁿ`**, through the dictionary
`Emb.covDerivAt_x_iff`, `Emb.covDerivAt_y_iff`. -/
theorem B_emb_iff_A87n : B_emb ↔ A87n := by
  constructor
  · intro h V _ _ _ W _ _ n N hN (s : ℝ × ℝ → Bridge.Sub hN) hS p
    obtain ⟨x₀, y₀⟩ := p
    have hs := Emb.contMDiff_surf_iff.2 hS
    obtain ⟨u, h1, h2⟩ := h V W n N hN s hs x₀ y₀
    exact ((Emb.covDerivAt_x_iff hs x₀ y₀ u).1 h1).symm.trans ((Emb.covDerivAt_y_iff hs x₀ y₀ u).1 h2)
  · intro h V _ _ _ W _ _ n N hN s hs x₀ y₀
    have hmem : Morse.covDerivX hN s (Morse.velY (N := N) s) (x₀, y₀) ∈
        Morse.tangentSubspace hN (s (x₀, y₀)) := Morse.tanProj_apply_mem hN _ _
    refine ⟨Bridge.L hN (s (x₀, y₀)) (Morse.covDerivX hN s (Morse.velY (N := N) s) (x₀, y₀)),
      (Emb.covDerivAt_x_iff hs x₀ y₀ _).2 (Bridge.D_L hmem),
      (Emb.covDerivAt_y_iff hs x₀ y₀ _).2 ?_⟩
    rw [Bridge.D_L hmem]
    exact h V W n N hN s (Emb.contMDiff_surf_iff.1 hs) (x₀, y₀)

/-- **A implies B on embedded manifolds** (uses A's `covDerivX_velY`). -/
theorem A_to_B_emb : A → B_emb := fun hA => B_emb_iff_A87n.2 (A_to_A87n hA)

/-- **B implies A's Lemma 8.7** (model `ℝⁿ`), by specializing B to `↥N`. -/
theorem B_to_A87n : B → A87n := fun hB => B_emb_iff_A87n.1 (B_to_B_emb hB)

#rt_check RoundTrip.V6_15.A_to_B_emb [Morse.covDerivX_eq, Morse.covDerivX_velY]
#rt_check RoundTrip.V6_15.B_to_A87n [Morse.covDerivX_eq, Morse.covDerivX_velY]
#rt_overlap RoundTrip.V6_15.B_to_A87n [Morse.covDerivX_eq, Morse.covDerivX_velY]

end RoundTrip.V6_15
