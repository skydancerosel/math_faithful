import Morse
import RoundTrip.Check
import RoundTrip.Blind.V8_12
import RoundTrip.Bridge

open Set Filter Topology Function
open scoped ContDiff Manifold

namespace RoundTrip.V8_12

/-- The project's statement (universes instantiated at 0), for a slice submanifold `N ⊆ V` with
the induced metric: `curvR x = curvOp ⟨x, _⟩` on `N` (unfolding of the definition); the curvature
identity (13.3) for a smooth surface `F` in `N` near `p₀`:
`P ∂/∂u (P ∂²F/∂t²) = P ∂/∂t (P ∂²F/∂t∂u) + R(∂F/∂t, ∂F/∂u) ∂F/∂t`; and, for a 1-parameter
variation, `d/du Δ_x(∂α/∂t) = Δ_x(∂/∂t ∂α/∂u)` (ambient vectors, not projected). -/
def A : Prop :=
  type_of% @Morse.curvR_of_mem.{0,0,0} ∧
    type_of% @Morse.curvature_identity.{0,0,0} ∧
    type_of% @Morse.IsVariation.hasDerivAt_jump.{0}

theorem A_holds : A :=
  ⟨@Morse.curvR_of_mem, @Morse.curvature_identity, @Morse.IsVariation.hasDerivAt_jump⟩

/-! ## The embedded special case -/

namespace Emb

set_option linter.unusedSectionVars false

/-- `e₀ ∈ ℝ²`. -/
noncomputable abbrev e0 : Rn 2 := EuclideanSpace.single 0 (1 : ℝ)

theorem norm_smul_e0 (r : ℝ) : ‖r • e0‖ = |r| := by
  rw [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]

/-- A closed interval `[s, u] ⊆ [0, 1]` whose interior avoids the subdivision points lies in one
piece of the subdivision. -/
theorem exists_piece_of_subdiv {t : ℕ → ℝ} {k : ℕ} (h0 : t 0 = 0) (hk : t k = 1)
    (hlt : ∀ i < k, t i < t (i + 1)) {s u : ℝ} (hs : 0 ≤ s) (hsu : s < u) (hub : u ≤ 1)
    (hB : ∀ x ∈ (Finset.range (k + 1)).image t, x ∉ Ioo s u) :
    ∃ i < k, t i ≤ s ∧ u ≤ t (i + 1) := by
  have hP : ∃ j, s < t j ∧ j ≤ k := ⟨k, by rw [hk]; linarith, le_rfl⟩
  classical
  set m := Nat.find hP
  have hm : s < t m ∧ m ≤ k := Nat.find_spec hP
  have hm0 : m ≠ 0 := by
    intro h; have := hm.1; rw [h, h0] at this; linarith
  have hi : t (m - 1) ≤ s := by
    by_contra hcon
    exact Nat.find_min hP (Nat.sub_lt (Nat.pos_of_ne_zero hm0) one_pos)
      ⟨lt_of_not_ge hcon, by omega⟩
  have hu : u ≤ t m := by
    by_contra hcon
    exact hB (t m) (Finset.mem_image.2 ⟨m, Finset.mem_range.2 (by omega), rfl⟩)
      ⟨hm.1, lt_of_not_ge hcon⟩
  have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)
  exact ⟨m - 1, by omega, hi, hm1.symm ▸ hu⟩


variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- A map from a normed space into `N` is smooth (as a map into the manifold `N`) iff it is smooth
in `V` (generalizes `Bridge.contMDiffWithinAt_curve_iff`). -/
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

theorem contMDiffOn_map_iff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Bridge.Sub hN} {s : Set E} :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, Rn n) ∞ f s ↔ ContDiffOn ℝ ∞ (Bridge.incl hN ∘ f) s :=
  forall₂_congr fun _ _ => contMDiffWithinAt_map_iff


theorem P_eq_prj (x : Bridge.Sub hN) : Bridge.P hN x = Morse.prj hN (Bridge.incl hN x) := by
  rw [show Bridge.incl hN x = x.1 from rfl, Morse.prj_of_mem hN x.2]
  rfl

/-- One-sided (or any) velocities of a curve in `N`, read in `V`. -/
theorem D_mfderivWithin_curve {c : ℝ → Bridge.Sub hN} {s : Set ℝ} {t : ℝ}
    (hc : DifferentiableWithinAt ℝ (Bridge.incl hN ∘ c) s t) (hs : UniqueDiffWithinAt ℝ s t) :
    Bridge.D hN (c t) (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) c s t 1) =
      derivWithin (Bridge.incl hN ∘ c) s t :=
  ((Bridge.hasDerivWithinAt_incl_comp (Bridge.mdifferentiableWithinAt_curve_iff.2 hc)).derivWithin
    hs).symm

/-- The derivative of a map from a normed space into `N`, read in `V`. -/
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


/-- The forward half of `Bridge.isCurvVal_iff`, re-proved with `curvR_of_mem` taken as a hypothesis
(the Bridge's proof uses the project lemma `Morse.curvR_of_mem`, one of this item's theorems). -/
theorem D_of_isCurvVal (hcurvR : type_of% @Morse.curvR_of_mem.{0,0,0}) (p : Bridge.Sub hN)
    (x y z r : TangentSpace 𝓘(ℝ, Rn n) p)
    (h : RoundTrip.V8_13.IsCurvVal (Bridge.conn (hN := hN)) p x y z r) :
    Bridge.D hN p r =
      Morse.curvR hN (Bridge.incl hN p) (Bridge.D hN p x) (Bridge.D hN p y) (Bridge.D hN p z) := by
  have hR : ∀ a b c : V, Morse.curvR hN (Bridge.incl hN p) a b c = Morse.curvOp hN p a b c :=
    fun a b c => hcurvR hN p.2 a b c
  have hE : ∀ x : TangentSpace 𝓘(ℝ, Rn n) p,
      Bridge.amb (Bridge.ext (hN := hN) (Bridge.D hN p x)) p = Bridge.D hN p x :=
    fun x => (congrFun (Bridge.amb_ext (Bridge.D hN p x)) p).trans (Bridge.P_D p x)
  have := h _ _ _ (Bridge.isSmoothVF_ext (Bridge.D hN p x)) (Bridge.isSmoothVF_ext (Bridge.D hN p y))
    (Bridge.isSmoothVF_ext (Bridge.D hN p z)) (Bridge.ext_apply_D p x) (Bridge.ext_apply_D p y)
    (Bridge.ext_apply_D p z)
  refine (congrArg (Bridge.D hN p) this).trans ?_
  rw [Bridge.D_curvExpr (Bridge.isSmoothVF_ext _) (Bridge.isSmoothVF_ext _)
    (Bridge.isSmoothVF_ext _) p, hR, hE, hE, hE]

section Var

variable {U : Set (Rn 2)} {α : Rn 2 → ℝ → Bridge.Sub hN} {k : ℕ} {t : ℕ → ℝ}

/-- The variation field `W₁ = ∂α/∂u₁ (0, ·)`, read in `V`, is the derivative along `r ↦ r e₀`. -/
theorem D_varField (hα : IsVarSub (n := n) U α k t) {i : ℕ} (hi : i < k) {τ : ℝ}
    (hτ : τ ∈ Icc (t i) (t (i + 1))) :
    Bridge.D hN (α 0 τ) (varField (n := n) α 0 τ) =
      deriv (fun r : ℝ => Bridge.incl hN (α (r • e0) τ)) 0 := by
  obtain ⟨hU, h0U, -, -, -, -, hsm⟩ := hα
  have hG : ContDiffOn ℝ ∞ (Bridge.incl hN ∘ fun x : Rn 2 × ℝ => α x.1 x.2)
      (U ×ˢ Icc (t i) (t (i + 1))) := contMDiffOn_map_iff.1 (hsm i hi)
  have hcd : ContDiffAt ℝ ∞ (Bridge.incl hN ∘ fun u => α u τ) 0 :=
    (hG.comp (contDiff_id.prodMk contDiff_const).contDiffOn fun u hu => ⟨hu, hτ⟩).contDiffAt
      (hU.mem_nhds h0U)
  have hmd : MDifferentiableAt 𝓘(ℝ, Rn 2) 𝓘(ℝ, Rn n) (fun u => α u τ) 0 := by
    have : ContMDiffAt 𝓘(ℝ, Rn 2) 𝓘(ℝ, Rn n) ∞ (fun u => α u τ) 0 := by
      rw [← contMDiffWithinAt_univ]
      exact contMDiffWithinAt_map_iff.2 (contDiffWithinAt_univ.2 hcd)
    exact this.mdifferentiableAt (by simp)
  have h1 := D_mfderiv_map hmd e0
  have h2 : HasDerivAt (fun r : ℝ => Bridge.incl hN (α (r • e0) τ))
      (fderiv ℝ (Bridge.incl hN ∘ fun u => α u τ) 0 ((1 : ℝ) • e0)) 0 := by
    have hd : HasFDerivAt (Bridge.incl hN ∘ fun u => α u τ)
        (fderiv ℝ (Bridge.incl hN ∘ fun u => α u τ) 0) ((0 : ℝ) • e0) := by
      rw [zero_smul]
      exact (hcd.differentiableAt (by simp)).hasFDerivAt
    exact hd.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).smul_const e0)
  rw [h2.deriv, one_smul, ← h1]
  rfl

end Var

section Curv

variable {U : Set (Rn 2)} {α : Rn 2 → ℝ → Bridge.Sub hN} {k : ℕ} {t : ℕ → ℝ}

/-- **B's first claim on `↥N`, from A's curvature identity** (13.3): the covariant `u₁`-derivative
of the accelerations `A u` at `u = 0` is `D²W₁/dt² + R(V, W₁)V`. -/
theorem curv_part (hcurvR : type_of% @Morse.curvR_of_mem.{0,0,0})
    (hcurv : type_of% @Morse.curvature_identity.{0,0,0})
    (hα : IsVarSub (n := n) U α k t) {i : ℕ} (hi : i < k) (W' W'' Rv : FA n (α 0))
    (hW' : HasCovDeriv (Bridge.conn (hN := hN)) (α 0) (Icc (t i) (t (i + 1)))
      (varField (n := n) α 0) W')
    (hW'' : HasCovDeriv (Bridge.conn (hN := hN)) (α 0) (Icc (t i) (t (i + 1))) W' W'')
    (hRv : ∀ s ∈ Icc (t i) (t (i + 1)), IsCurvVal (Bridge.conn (hN := hN)) (α 0 s)
      (vel (n := n) (α 0) (Icc (t i) (t (i + 1))) s) (varField (n := n) α 0 s)
      (vel (n := n) (α 0) (Icc (t i) (t (i + 1))) s) (Rv s))
    (A : FP (n := n) α)
    (hA : ∀ u ∈ U, HasCovDeriv (Bridge.conn (hN := hN)) (α u) (Ioo (t i) (t (i + 1)))
      (vel (n := n) (α u) (Ioo (t i) (t (i + 1)))) (A u))
    {s : ℝ} (hs : s ∈ Ioo (t i) (t (i + 1))) :
    ∃ δ > 0, Metric.ball (0 : Rn 2) δ ⊆ U ∧ ∃ B : FA n (uCurve α 0 0 s),
      HasCovDeriv (Bridge.conn (hN := hN)) (uCurve α 0 0 s) (Ioo (-δ) δ)
        (fun r => A (0 + r • EuclideanSpace.single 0 (1 : ℝ)) s) B ∧ B 0 = W'' s + Rv s := by
  have hα' := hα
  obtain ⟨hU, h0U, -, -, hlt, -, hsm⟩ := hα
  set I := Icc (t i) (t (i + 1)) with hIdef
  set J := Ioo (t i) (t (i + 1)) with hJdef
  have hti : t i < t (i + 1) := hlt i hi
  have hG : ContDiffOn ℝ ∞ (Bridge.incl hN ∘ fun x : Rn 2 × ℝ => α x.1 x.2) (U ×ˢ I) :=
    contMDiffOn_map_iff.1 (hsm i hi)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU 0 h0U
  have hball₁ : ∀ r ∈ Ioo (-δ) δ, r • e0 ∈ U := fun r hr => hball (by
    rw [Metric.mem_ball, dist_zero_right, norm_smul_e0, abs_lt]; exact hr)
  set U₁ : Set ℝ := {r | r • e0 ∈ U} with hU₁def
  have hU₁ : IsOpen U₁ := hU.preimage (continuous_id.smul continuous_const)
  have h0U₁ : (0 : ℝ) ∈ U₁ := by
    show (0 : ℝ) • e0 ∈ U
    rw [zero_smul]; exact h0U
  set F : ℝ × ℝ → V := fun p => Bridge.incl hN (α (p.1 • e0) p.2) with hFdef
  set O : Set (ℝ × ℝ) := U₁ ×ˢ J with hOdef
  have hO : IsOpen O := hU₁.prod isOpen_Ioo
  have hFO : ContDiffOn ℝ ∞ F O :=
    hG.comp ((contDiff_fst.smul contDiff_const).prodMk contDiff_snd).contDiffOn
      fun p hp => ⟨hp.1, Ioo_subset_Icc_self hp.2⟩
  have hFN : ∀ p ∈ O, F p ∈ N := fun p _ => (α _ _).2
  have hp₀ : ((0 : ℝ), s) ∈ O := ⟨h0U₁, hs⟩
  have key := hcurv hN hO hFO hFN hp₀
  have hdiff : ∀ {H : ℝ × ℝ → V}, ContDiffOn ℝ ∞ H O → ∀ p ∈ O, DifferentiableAt ℝ H p :=
    fun hH p hp => (hH.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp)
  have hFX := Morse.contDiffOn_partialX hO hFO
  have hFY := Morse.contDiffOn_partialY hO hFO
  have hFYY := Morse.contDiffOn_partialY hO hFY
  have hFYX := Morse.contDiffOn_partialY hO hFX
  have hPF : ContDiffOn ℝ ∞ (fun p => Morse.prj hN (F p)) O := Morse.ContDiffOn.prj_comp hN hFO hFN
  set G₁ : ℝ × ℝ → V := fun p => Morse.prj hN (F p) (Morse.partialY (Morse.partialY F) p) with hG₁def
  set G₂ : ℝ × ℝ → V := fun p => Morse.prj hN (F p) (Morse.partialY (Morse.partialX F) p) with hG₂def
  have hG₁ : ContDiffOn ℝ ∞ G₁ O := hPF.clm_apply hFYY
  have hG₂ : ContDiffOn ℝ ∞ G₂ O := hPF.clm_apply hFYX
  have hF0 : ∀ τ, F (0, τ) = Bridge.incl hN (α 0 τ) := fun τ => by simp [F]
  -- the curve `r ↦ α(r e₀, s)`
  have hc₀ : ∀ r, (uCurve α 0 0 s) r = α (r • e0) s := fun r => by simp [uCurve]
  have hc₀F : ∀ r, Bridge.incl hN ((uCurve α 0 0 s) r) = F (r, s) := fun r => by rw [hc₀]
  have hIδ : IsIntv (Ioo (-δ) δ) := ⟨ordConnected_Ioo, isOpen_Ioo.uniqueDiffOn⟩
  have h0δ : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hc₀s : IsSmoothCurve (n := n) (uCurve α 0 0 s) (Ioo (-δ) δ) := by
    refine Bridge.isSmoothCurve_iff.2 ?_
    refine (hFO.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      fun r hr => ⟨hball₁ r hr, hs⟩).congr fun r _ => ?_
    exact hc₀F r
  -- the accelerations `A u`, read in `V`
  have hAamb : ∀ r ∈ Ioo (-δ) δ, Bridge.ambA (uCurve α 0 0 s) (fun r => A (0 + r • EuclideanSpace.single 0 (1 : ℝ)) s) r = G₁ (r, s) := by
    intro r hr
    have hu : (0 : Rn 2) + r • e0 ∈ U := by rw [zero_add]; exact hball₁ r hr
    set c := α (0 + r • e0) with hcdef
    have hcJ : ContDiffOn ℝ ∞ (Bridge.incl hN ∘ c) J :=
      hG.comp (contDiff_const.prodMk contDiff_id).contDiffOn
        fun τ hτ => ⟨hu, Ioo_subset_Icc_self hτ⟩
    have hcs : IsSmoothCurve (n := n) c J := Bridge.isSmoothCurve_iff.2 hcJ
    have hJ : IsIntv J := ⟨ordConnected_Ioo, isOpen_Ioo.uniqueDiffOn⟩
    have h1 := ((Bridge.hasCovDeriv_iff' hJ hcs).1 (hA _ hu)).2 s hs
    have e : Bridge.incl hN ∘ c = fun y => F (r, y) := by
      funext y; simp [c, F]
    have h2 : Bridge.ambA c (vel (n := n) c J) =ᶠ[𝓝 s] deriv (Bridge.incl hN ∘ c) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with τ hτ
      exact (Bridge.ambA_vel_eqOn hJ.2 hcs hτ).trans (derivWithin_of_isOpen isOpen_Ioo hτ)
    have h3 : deriv (Bridge.incl hN ∘ c) =ᶠ[𝓝 s] fun τ => Morse.partialY F (r, τ) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with τ hτ
      rw [e]
      exact (Morse.hasDerivAt_partialY (hdiff hFO (r, τ) ⟨hball₁ r hr, hτ⟩)).deriv
    have h4 : derivWithin (Bridge.ambA c (vel (n := n) c J)) J s = Morse.partialY (Morse.partialY F) (r, s) := by
      rw [derivWithin_of_isOpen isOpen_Ioo hs, h2.deriv_eq, h3.deriv_eq]
      exact (Morse.hasDerivAt_partialY (hdiff hFY (r, s) ⟨hball₁ r hr, hs⟩)).deriv
    show Bridge.ambA c (A (0 + r • e0)) s = G₁ (r, s)
    rw [h1, h4, P_eq_prj]
    show Morse.prj hN ((Bridge.incl hN ∘ c) s) _ = _
    rw [e]
  have hsmooth : IsSmoothAlong (uCurve α 0 0 s) (Ioo (-δ) δ) (fun r => A (0 + r • EuclideanSpace.single 0 (1 : ℝ)) s) := by
    refine Bridge.isSmoothAlong_iff.2 ⟨hc₀s, ?_⟩
    refine (hG₁.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      fun r hr => ⟨hball₁ r hr, hs⟩).congr fun r hr => ?_
    exact hAamb r hr
  refine ⟨δ, hδ, hball, Bridge.covA (uCurve α 0 0 s) (Ioo (-δ) δ) (fun r => A (0 + r • EuclideanSpace.single 0 (1 : ℝ)) s),
    (Bridge.hasCovDeriv_iff hIδ hc₀s).2 ⟨hsmooth, fun r _ => rfl⟩, ?_⟩
  -- the value at `r = 0`
  have hc00 : (uCurve α 0 0 s) 0 = α 0 s := by rw [hc₀, zero_smul]
  have hDeq : Bridge.D hN ((uCurve α 0 0 s) 0) = Bridge.D hN (α 0 s) := congrArg (Bridge.D hN) hc00
  have hL : Bridge.D hN ((uCurve α 0 0 s) 0) (Bridge.covA (uCurve α 0 0 s) (Ioo (-δ) δ) (fun r => A (0 + r • EuclideanSpace.single 0 (1 : ℝ)) s) 0) =
      Morse.prj hN (F (0, s)) (Morse.partialX G₁ (0, s)) := by
    refine (Bridge.D_covA (uCurve α 0 0 s) (Ioo (-δ) δ)
      (fun r => A (0 + r • EuclideanSpace.single 0 (1 : ℝ)) s) 0).trans ?_
    rw [P_eq_prj, hc₀F]
    congr 1
    have hev : Bridge.ambA (uCurve α 0 0 s) (fun r => A (0 + r • EuclideanSpace.single 0 (1 : ℝ)) s) =ᶠ[𝓝 0] fun r => G₁ (r, s) := by
      filter_upwards [isOpen_Ioo.mem_nhds h0δ] with r hr
      exact hAamb r hr
    rw [derivWithin_of_isOpen isOpen_Ioo h0δ, hev.deriv_eq]
    exact (Morse.hasDerivAt_partialX (hdiff hG₁ _ hp₀)).deriv
  have hI : IsIntv I := ⟨ordConnected_Icc, uniqueDiffOn_Icc hti⟩
  have hα0I : IsSmoothCurve (n := n) (α 0) I :=
    Bridge.isSmoothCurve_iff.2 (hG.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      fun τ hτ => ⟨h0U, hτ⟩)
  have hW1amb : ∀ τ ∈ J, Bridge.ambA (α 0) (varField (n := n) α 0) τ = Morse.partialX F (0, τ) := by
    intro τ hτ
    show Bridge.D hN (α 0 τ) (varField (n := n) α 0 τ) = _
    rw [D_varField hα' hi (Ioo_subset_Icc_self hτ)]
    exact (Morse.hasDerivAt_partialX (hdiff hFO (0, τ) ⟨h0U₁, hτ⟩)).deriv
  have hW'amb : ∀ τ ∈ J, Bridge.ambA (α 0) W' τ = G₂ (0, τ) := by
    intro τ hτ
    have h1 := ((Bridge.hasCovDeriv_iff' hI hα0I).1 hW').2 τ (Ioo_subset_Icc_self hτ)
    rw [h1, P_eq_prj, ← hF0 τ]
    congr 1
    have hev : Bridge.ambA (α 0) (varField (n := n) α 0) =ᶠ[𝓝 τ] fun y => Morse.partialX F (0, y) := by
      filter_upwards [isOpen_Ioo.mem_nhds hτ] with y hy
      exact hW1amb y hy
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hτ.1 hτ.2), hev.deriv_eq]
    exact (Morse.hasDerivAt_partialY (hdiff hFX (0, τ) ⟨h0U₁, hτ⟩)).deriv
  have hW''amb : Bridge.D hN (α 0 s) (W'' s) = Morse.prj hN (F (0, s)) (Morse.partialY G₂ (0, s)) := by
    have h1 := ((Bridge.hasCovDeriv_iff' hI hα0I).1 hW'').2 s (Ioo_subset_Icc_self hs)
    show Bridge.ambA (α 0) W'' s = _
    rw [h1, P_eq_prj, ← hF0 s]
    congr 1
    have hev : Bridge.ambA (α 0) W' =ᶠ[𝓝 s] fun y => G₂ (0, y) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with y hy
      exact hW'amb y hy
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2), hev.deriv_eq]
    exact (Morse.hasDerivAt_partialY (hdiff hG₂ _ hp₀)).deriv
  have hvel : Bridge.D hN (α 0 s) (vel (n := n) (α 0) I s) = Morse.partialY F (0, s) := by
    refine (Bridge.D_vel hα0I hI.2 (Ioo_subset_Icc_self hs)).trans ?_
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2)]
    have e : Bridge.incl hN ∘ α 0 = fun y => F (0, y) := by funext y; exact (hF0 y).symm
    rw [e]
    exact (Morse.hasDerivAt_partialY (hdiff hFO _ hp₀)).deriv
  have hRvamb : Bridge.D hN (α 0 s) (Rv s) =
      Morse.curvR hN (F (0, s)) (Morse.partialY F (0, s)) (Morse.partialX F (0, s)) (Morse.partialY F (0, s)) := by
    have h1 := D_of_isCurvVal hcurvR (α 0 s) _ _ _ (Rv s) (hRv s (Ioo_subset_Icc_self hs))
    have hW1 : Bridge.D hN (α 0 s) (varField (n := n) α 0 s) = Morse.partialX F (0, s) :=
      hW1amb s hs
    rw [h1, ← hF0 s, hvel, hW1]
  apply Bridge.D_injective (α 0 s)
  rw [hDeq] at hL
  rw [hL, Bridge.D_tadd, hW''amb, hRvamb]
  exact key

end Curv

section Jump

variable {U : Set (Rn 2)} {α : Rn 2 → ℝ → Bridge.Sub hN} {k : ℕ} {t : ℕ → ℝ}

/-- A blind 2-parameter variation, restricted to the line `r ↦ r e₀`, is a project variation. -/
theorem isVariation_line (hα : IsVarSub (n := n) U α k t) :
    Morse.IsVariation N {r : ℝ | r • e0 ∈ U} (fun r τ => Bridge.incl hN (α (r • e0) τ))
      ((Finset.range (k + 1)).image t) := by
  obtain ⟨hU, h0U, ht0, htk, hlt, hpath, hsm⟩ := hα
  have hcont : Continuous (fun s : ℝ => s • e0) := continuous_id.smul continuous_const
  refine ⟨hU.preimage hcont, by simpa using h0U, fun u _ τ _ => (α _ τ).2, ?_, ?_, ?_⟩
  · intro u hu
    simp only [Set.mem_ofPred_eq] at hu
    simp only [zero_smul]
    rw [(hpath _ hu).2.1]
  · intro u hu
    simp only [Set.mem_ofPred_eq] at hu
    simp only [zero_smul]
    rw [(hpath _ hu).2.2]
  · intro s u hs hsu hu hB
    obtain ⟨i, hi, hti, hut⟩ := exists_piece_of_subdiv ht0 htk hlt hs hsu hu hB
    have h2 : ContDiffOn ℝ ∞ (Bridge.incl hN ∘ (fun x : Rn 2 × ℝ => α x.1 x.2))
        (U ×ˢ Icc (t i) (t (i + 1))) := contMDiffOn_map_iff.1 (hsm i hi)
    have hmap : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p.1 • e0, p.2)) :=
      (contDiff_fst.smul contDiff_const).prodMk contDiff_snd
    exact h2.comp hmap.contDiffOn fun p hp => ⟨hp.1, hti.trans hp.2.1, hp.2.2.trans hut⟩

/-- **B's second claim on `↥N`, from A's `hasDerivAt_jump`**: the covariant `u₁`-derivative of
the velocity jump `Δ_x V(u)` at `u = 0` is the jump `Δ_x (DW₁/dt)`. -/
theorem jump_part (hjump : type_of% @Morse.IsVariation.hasDerivAt_jump.{0})
    (hα : IsVarSub (n := n) U α k t) {j : ℕ} (hj : j + 1 < k) (P Q : FA n (α 0))
    (hP : HasCovDeriv (Bridge.conn (hN := hN)) (α 0) (Icc (t j) (t (j + 1)))
      (varField (n := n) α 0) P)
    (hQ : HasCovDeriv (Bridge.conn (hN := hN)) (α 0) (Icc (t (j + 1)) (t (j + 2)))
      (varField (n := n) α 0) Q) :
    ∃ δ > 0, Metric.ball (0 : Rn 2) δ ⊆ U ∧ ∃ B : FA n (uCurve α 0 0 (t (j + 1))),
      HasCovDeriv (Bridge.conn (hN := hN)) (uCurve α 0 0 (t (j + 1))) (Ioo (-δ) δ)
        (fun r => Vjump (n := n) (α (0 + r • EuclideanSpace.single 0 (1 : ℝ))) (t (j + 1))) B ∧
      B 0 = Q (t (j + 1)) - P (t (j + 1)) := by
  have hα' := hα
  obtain ⟨hU, h0U, ht0, htk, hlt, -, hsm⟩ := hα
  set x := t (j + 1) with hxdef
  set a := t j with hadef
  set b := t (j + 2) with hbdef
  have hax : a < x := hlt j (by omega)
  have hxb : x < b := hlt (j + 1) hj
  have hx01 : x ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · have := Bridge.le_of_strictSeq hlt (Nat.zero_le j) (by omega)
      rw [ht0] at this
      linarith
    · have := Bridge.le_of_strictSeq hlt (show j + 2 ≤ k by omega) le_rfl
      rw [htk] at this
      linarith
  have hG₁ : ContDiffOn ℝ ∞ (Bridge.incl hN ∘ fun x : Rn 2 × ℝ => α x.1 x.2) (U ×ˢ Icc a x) :=
    contMDiffOn_map_iff.1 (hsm j (by omega))
  have hG₂ : ContDiffOn ℝ ∞ (Bridge.incl hN ∘ fun x : Rn 2 × ℝ => α x.1 x.2) (U ×ˢ Icc x b) :=
    contMDiffOn_map_iff.1 (hsm (j + 1) hj)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU 0 h0U
  have hball₁ : ∀ r ∈ Ioo (-δ) δ, r • e0 ∈ U := fun r hr => hball (by
    rw [Metric.mem_ball, dist_zero_right, norm_smul_e0, abs_lt]; exact hr)
  set U₁ : Set ℝ := {r | r • e0 ∈ U} with hU₁def
  have hU₁ : IsOpen U₁ := hU.preimage (continuous_id.smul continuous_const)
  have h0U₁ : (0 : ℝ) ∈ U₁ := by
    show (0 : ℝ) • e0 ∈ U
    rw [zero_smul]; exact h0U
  set σ : ℝ → ℝ → V := fun r τ => Bridge.incl hN (α (r • e0) τ) with hσdef
  have hmap : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p.1 • e0, p.2)) :=
    (contDiff_fst.smul contDiff_const).prodMk contDiff_snd
  have hσ₁ : ContDiffOn ℝ ∞ (Morse.unc σ) (U₁ ×ˢ Icc a x) :=
    hG₁.comp hmap.contDiffOn fun p hp => ⟨hp.1, hp.2⟩
  have hσ₂ : ContDiffOn ℝ ∞ (Morse.unc σ) (U₁ ×ˢ Icc x b) :=
    hG₂.comp hmap.contDiffOn fun p hp => ⟨hp.1, hp.2⟩
  have hJ := hjump (isVariation_line hα') h0U₁ hx01
  -- the jumps, read in `V`
  have hjumpamb : ∀ r ∈ U₁, Bridge.D hN (α (r • e0) x) (Vjump (n := n) (α (r • e0)) x) =
      Morse.jump (σ r) x := by
    intro r hr
    have hR : ContDiffOn ℝ ∞ (σ r) (Icc x b) :=
      hσ₂.comp (contDiff_const.prodMk contDiff_id).contDiffOn fun τ hτ => ⟨hr, hτ⟩
    have hL : ContDiffOn ℝ ∞ (σ r) (Icc a x) :=
      hσ₁.comp (contDiff_const.prodMk contDiff_id).contDiffOn fun τ hτ => ⟨hr, hτ⟩
    have hdR : DifferentiableWithinAt ℝ (Bridge.incl hN ∘ α (r • e0)) (Ici x) x :=
      ((hR.differentiableOn (by simp)) x (left_mem_Icc.2 hxb.le)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE hxb)
    have hdL : DifferentiableWithinAt ℝ (Bridge.incl hN ∘ α (r • e0)) (Iic x) x :=
      ((hL.differentiableOn (by simp)) x (right_mem_Icc.2 hax.le)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE hax)
    show Bridge.D hN (α (r • e0) x) (Vplus (n := n) (α (r • e0)) x - Vminus (n := n) (α (r • e0)) x) = _
    have e1 : Bridge.D hN (α (r • e0) x) (Vplus (n := n) (α (r • e0)) x) =
        derivWithin (σ r) (Ici x) x := D_mfderivWithin_curve hdR (uniqueDiffWithinAt_Ici x)
    have e2 : Bridge.D hN (α (r • e0) x) (Vminus (n := n) (α (r • e0)) x) =
        derivWithin (σ r) (Iic x) x := D_mfderivWithin_curve hdL (uniqueDiffWithinAt_Iic x)
    rw [Bridge.D_tsub_aux, Morse.jump, e1, e2]
  have hjumpamb' : ∀ r ∈ Ioo (-δ) δ, Bridge.ambA (uCurve α 0 0 x)
      (fun r => Vjump (n := n) (α (0 + r • EuclideanSpace.single 0 (1 : ℝ))) x) r =
        Morse.jump (σ r) x := by
    intro r hr
    show Bridge.D hN (α (0 + r • e0) x) (Vjump (n := n) (α (0 + r • e0)) x) = _
    rw [zero_add]
    exact hjumpamb r (hball₁ r hr)
  -- smoothness in `r`
  have hjsmooth : ContDiffOn ℝ ∞ (fun r => Morse.jump (σ r) x) (Ioo (-δ) δ) := by
    have h1 : ContDiffOn ℝ ∞ (fun r => Morse.pdT (U₁ ×ˢ Icc x b) (Morse.unc σ) (r, x) -
        Morse.pdT (U₁ ×ˢ Icc a x) (Morse.unc σ) (r, x)) (Ioo (-δ) δ) :=
      ((Morse.contDiffOn_pdT hU₁ hxb hσ₂).comp (contDiff_id.prodMk contDiff_const).contDiffOn
        fun r hr => ⟨hball₁ r hr, left_mem_Icc.2 hxb.le⟩).sub
      ((Morse.contDiffOn_pdT hU₁ hax hσ₁).comp (contDiff_id.prodMk contDiff_const).contDiffOn
        fun r hr => ⟨hball₁ r hr, right_mem_Icc.2 hax.le⟩)
    refine h1.congr fun r hr => ?_
    rw [Morse.jump, Morse.piece_derivWithin_Ici hxb hσ₂ (hball₁ r hr),
      Morse.piece_derivWithin_Iic hax hσ₁ (hball₁ r hr)]
  have hc₀ : ∀ r, uCurve α 0 0 x r = α (r • e0) x := fun r => by simp [uCurve]
  have hIδ : IsIntv (Ioo (-δ) δ) := ⟨ordConnected_Ioo, isOpen_Ioo.uniqueDiffOn⟩
  have h0δ : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hc₀s : IsSmoothCurve (n := n) (uCurve α 0 0 x) (Ioo (-δ) δ) := by
    refine Bridge.isSmoothCurve_iff.2 ?_
    refine (hσ₂.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      fun r hr => ⟨hball₁ r hr, left_mem_Icc.2 hxb.le⟩).congr fun r _ => ?_
    show Bridge.incl hN (uCurve α 0 0 x r) = _
    rw [hc₀]
    rfl
  have hsmooth : IsSmoothAlong (uCurve α 0 0 x) (Ioo (-δ) δ)
      (fun r => Vjump (n := n) (α (0 + r • EuclideanSpace.single 0 (1 : ℝ))) x) :=
    Bridge.isSmoothAlong_iff.2 ⟨hc₀s, hjsmooth.congr fun r hr => hjumpamb' r hr⟩
  refine ⟨δ, hδ, hball, Bridge.covA (uCurve α 0 0 x) (Ioo (-δ) δ)
      (fun r => Vjump (n := n) (α (0 + r • EuclideanSpace.single 0 (1 : ℝ))) x),
    (Bridge.hasCovDeriv_iff hIδ hc₀s).2 ⟨hsmooth, fun r _ => rfl⟩, ?_⟩
  -- the value at `r = 0`
  set W₁ : ℝ → V := fun τ => deriv (fun v => σ v τ) 0 with hW₁def
  have hc00 : uCurve α 0 0 x 0 = α 0 x := by rw [hc₀, zero_smul]
  have hσ0 : σ 0 x = Bridge.incl hN (α 0 x) := by simp [σ]
  have hDeq : Bridge.D hN (uCurve α 0 0 x 0) = Bridge.D hN (α 0 x) := congrArg (Bridge.D hN) hc00
  have hLHS : Bridge.D hN (uCurve α 0 0 x 0) (Bridge.covA (uCurve α 0 0 x) (Ioo (-δ) δ)
      (fun r => Vjump (n := n) (α (0 + r • EuclideanSpace.single 0 (1 : ℝ))) x) 0) =
        Morse.prj hN (Bridge.incl hN (α 0 x)) (Morse.jump W₁ x) := by
    refine (Bridge.D_covA (uCurve α 0 0 x) (Ioo (-δ) δ)
      (fun r => Vjump (n := n) (α (0 + r • EuclideanSpace.single 0 (1 : ℝ))) x) 0).trans ?_
    rw [P_eq_prj, hc00]
    congr 1
    have hev : Bridge.ambA (uCurve α 0 0 x)
        (fun r => Vjump (n := n) (α (0 + r • EuclideanSpace.single 0 (1 : ℝ))) x) =ᶠ[𝓝 0]
          fun r => Morse.jump (σ r) x := by
      filter_upwards [isOpen_Ioo.mem_nhds h0δ] with r hr
      exact hjumpamb' r hr
    rw [derivWithin_of_isOpen isOpen_Ioo h0δ, hev.deriv_eq]
    exact hJ.deriv
  -- the covariant derivatives `P`, `Q` of `W₁` on the two pieces, read in `V`
  have hW₁eq : ∀ i < k, ∀ τ ∈ Icc (t i) (t (i + 1)),
      Bridge.ambA (α 0) (varField (n := n) α 0) τ = W₁ τ :=
    fun i hi τ hτ => D_varField hα' hi hτ
  have hside : ∀ {c d : ℝ} (i : ℕ) (hi : i < k) (hcd : t i = c ∧ t (i + 1) = d) (Z : FA n (α 0)),
      HasCovDeriv (Bridge.conn (hN := hN)) (α 0) (Icc c d) (varField (n := n) α 0) Z →
      ∀ τ ∈ Icc c d, ∀ S : Set ℝ, Icc c d ∈ 𝓝[S] τ → UniqueDiffWithinAt ℝ S τ →
        Bridge.D hN (α 0 τ) (Z τ) = Morse.prj hN (Bridge.incl hN (α 0 τ)) (derivWithin W₁ S τ) := by
    intro c d i hi hcd Z hZ τ hτ S hS hSu
    obtain ⟨hc, hd⟩ := hcd
    have hcd' : c < d := hc ▸ hd ▸ hlt i hi
    have hI : IsIntv (Icc c d) := ⟨ordConnected_Icc, uniqueDiffOn_Icc hcd'⟩
    have hGi : ContDiffOn ℝ ∞ (Bridge.incl hN ∘ fun x : Rn 2 × ℝ => α x.1 x.2) (U ×ˢ Icc c d) := by
      have := contMDiffOn_map_iff.1 (hsm i hi); rwa [hc, hd] at this
    have hα0 : IsSmoothCurve (n := n) (α 0) (Icc c d) :=
      Bridge.isSmoothCurve_iff.2 (hGi.comp (contDiff_const.prodMk contDiff_id).contDiffOn
        fun τ hτ => ⟨h0U, hτ⟩)
    have h1 := ((Bridge.hasCovDeriv_iff' hI hα0).1 hZ)
    have heq : EqOn (Bridge.ambA (α 0) (varField (n := n) α 0)) W₁ (Icc c d) := fun τ hτ =>
      hW₁eq i hi τ (by rw [hc, hd]; exact hτ)
    have hdiff : DifferentiableWithinAt ℝ W₁ (Icc c d) τ :=
      (((Bridge.isSmoothAlong_iff.1 h1.1).2.congr fun y hy => (heq hy).symm).differentiableOn
        (by simp)) τ hτ
    show Bridge.ambA (α 0) Z τ = _
    rw [h1.2 τ hτ, P_eq_prj, derivWithin_congr heq (heq hτ)]
    congr 1
    exact ((hdiff.hasDerivWithinAt.mono_of_mem_nhdsWithin hS).derivWithin hSu).symm
  have hQx := hside (j + 1) hj ⟨rfl, rfl⟩ Q hQ x (left_mem_Icc.2 hxb.le) (Ici x)
    (Icc_mem_nhdsGE hxb) (uniqueDiffWithinAt_Ici x)
  have hPx := hside j (by omega) ⟨rfl, rfl⟩ P hP x (right_mem_Icc.2 hax.le) (Iic x)
    (Icc_mem_nhdsLE hax) (uniqueDiffWithinAt_Iic x)
  apply Bridge.D_injective (α 0 x)
  rw [hDeq] at hLHS
  rw [hLHS, Bridge.D_tsub_aux, hQx, hPx, ← map_sub, Morse.jump]

end Jump

end Emb

/-! ## B on embedded manifolds -/

/-- B on embedded manifolds: `M = ↥N` with the induced metric and the induced Levi-Civita
connection (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
    ∀ (U : Set (Rn 2)) (α : Rn 2 → ℝ → Bridge.Sub hN) (k : ℕ) (t : ℕ → ℝ),
      IsVarSub (n := n) U α k t →
    (∀ i < k, ∀ (W' W'' Rv : FA n (α 0)),
      HasCovDeriv (Bridge.conn (hN := hN)) (α 0) (Set.Icc (t i) (t (i + 1))) (varField (n := n) α 0) W' →
      HasCovDeriv (Bridge.conn (hN := hN)) (α 0) (Set.Icc (t i) (t (i + 1))) W' W'' →
      (∀ s ∈ Set.Icc (t i) (t (i + 1)), IsCurvVal (Bridge.conn (hN := hN)) (α 0 s)
        (vel (n := n) (α 0) (Set.Icc (t i) (t (i + 1))) s)
        (varField (n := n) α 0 s) (vel (n := n) (α 0) (Set.Icc (t i) (t (i + 1))) s) (Rv s)) →
      ∀ Acc : FP (n := n) α, (∀ u ∈ U, HasCovDeriv (Bridge.conn (hN := hN)) (α u)
          (Set.Ioo (t i) (t (i + 1))) (vel (n := n) (α u) (Set.Ioo (t i) (t (i + 1)))) (Acc u)) →
      ∀ s ∈ Set.Ioo (t i) (t (i + 1)), ∃ δ > 0, Metric.ball (0 : Rn 2) δ ⊆ U ∧
        ∃ B : FA n (uCurve α 0 0 s),
          HasCovDeriv (Bridge.conn (hN := hN)) (uCurve α 0 0 s) (Set.Ioo (-δ) δ)
            (fun r => Acc (0 + r • EuclideanSpace.single 0 (1 : ℝ)) s) B ∧
          B 0 = W'' s + Rv s) ∧
    (∀ j : ℕ, j + 1 < k → ∀ P Q : FA n (α 0),
      HasCovDeriv (Bridge.conn (hN := hN)) (α 0) (Set.Icc (t j) (t (j + 1))) (varField (n := n) α 0) P →
      HasCovDeriv (Bridge.conn (hN := hN)) (α 0) (Set.Icc (t (j + 1)) (t (j + 2)))
        (varField (n := n) α 0) Q →
      ∃ δ > 0, Metric.ball (0 : Rn 2) δ ⊆ U ∧
        ∃ B : FA n (uCurve α 0 0 (t (j + 1))),
          HasCovDeriv (Bridge.conn (hN := hN)) (uCurve α 0 0 (t (j + 1))) (Set.Ioo (-δ) δ)
            (fun r => Vjump (n := n) (α (0 + r • EuclideanSpace.single 0 (1 : ℝ))) (t (j + 1))) B ∧
          B 0 = Q (t (j + 1)) - P (t (j + 1)))

/-- `B_emb` is a special case of B (the induced connection is Levi-Civita, `Bridge.conn_isLC`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- **A implies B on embedded manifolds**: the first claim from A's `curvature_identity`
(`Emb.curv_part`), the second from A's `IsVariation.hasDerivAt_jump` (`Emb.jump_part`), through
the Bridge dictionary (`hasCovDeriv_iff`, `isCurvVal_iff`) and the new lemmas of `Emb`. -/
theorem A_to_B_emb : A → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN _ U α k t hα
  exact ⟨fun i hi W' W'' Rv hW' hW'' hRv Acc hAcc s hs =>
      Emb.curv_part hA.1 hA.2.1 hα hi W' W'' Rv hW' hW'' hRv Acc hAcc hs,
    fun j hj P Q hP hQ => Emb.jump_part hA.2.2 hα hj P Q hP hQ⟩

/-! Neither `A → B` nor `B → A` is proved; see `V8_12.json`. -/

#rt_check RoundTrip.V8_12.A_to_B_emb [Morse.curvR_of_mem, Morse.curvature_identity,
  Morse.IsVariation.hasDerivAt_jump]
#rt_overlap RoundTrip.V8_12.A_to_B_emb [Morse.curvR_of_mem, Morse.curvature_identity,
  Morse.IsVariation.hasDerivAt_jump]

end RoundTrip.V8_12
