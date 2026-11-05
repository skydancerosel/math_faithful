import Morse
import RoundTrip.Check
import RoundTrip.Blind.V7_12
import RoundTrip.Bridge

open Set Filter Topology Function
open scoped ContDiff Manifold RealInnerProductSpace

namespace RoundTrip.V7_12

/-- The project's statement (universes instantiated at 0): for a normal radius `ε` at `q`
(`NormalCoord`, smooth extension `F` of `exp_q`), the radial geodesics have constant speed
(`‖dF_{ru}(u)‖ = ‖u‖`), `dF_w` is injective on `T_qN`, the Gauss lemma
`⟨d(exp_q)_w(w), d(exp_q)_w(x)⟩ = ⟨w, x⟩` (`w ∈ B_ε(q)`, `x ∈ T_qN`), and its orthogonal form. -/
def A : Prop :=
  type_of% @Morse.NormalCoord.norm_fderiv_F_apply.{0,0,0} ∧
    type_of% @Morse.NormalCoord.injective_fderiv_F.{0,0,0} ∧
    type_of% @Morse.gauss_lemma.{0,0,0} ∧
    type_of% @Morse.gauss_lemma_orthogonal.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.NormalCoord.norm_fderiv_F_apply, @Morse.NormalCoord.injective_fderiv_F,
    @Morse.gauss_lemma, @Morse.gauss_lemma_orthogonal⟩

/-- B on embedded manifolds: `M = ↥N` with the induced metric and the induced Levi-Civita
connection (a special case of B, `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)], ∀ (q : Bridge.Sub hN) (ε : ℝ) (U : Set (Bridge.Sub hN)),
    0 < ε → IsNormBall (Bridge.conn (hN := hN)) q ε U →
    ∀ (J : Set ℝ) (v : ℝ → Rn n), IsIntv J → ContDiffOn ℝ ∞ v J → (∀ t ∈ J, nrm q (v t) = 1) →
      ∀ r ∈ Set.Ioo 0 ε, ∀ t ∈ J, rinner (expMap (Bridge.conn (hN := hN)) q (r • v t))
        (dfr (Bridge.conn (hN := hN)) q v r t) (dft (Bridge.conn (hN := hN)) q v J r t) = 0

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-! ## The embedded special case: dictionary (partly copied from `Items/V7_10.lean`) -/

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-! Restatements of Bridge lemmas in this blind file's vocabulary (definitionally equal). -/

theorem D_vel' {c : ℝ → Bridge.Sub hN} {s : Set ℝ} {t : ℝ} (hc : IsSmoothCurve (n := n) c s)
    (hs : UniqueDiffOn ℝ s) (ht : t ∈ s) :
    D hN (c t) (vel (n := n) c s t) = derivWithin (incl hN ∘ c) s t := D_vel hc hs ht

theorem isGeodesic_iff' {c : ℝ → Bridge.Sub hN} {s : Set ℝ} :
    IsGeodesic (conn (hN := hN)) c s ↔ IsIntv s ∧ ContDiffOn ℝ ∞ (incl hN ∘ c) s ∧
      ∀ t ∈ s, P hN (c t) (derivWithin (derivWithin (incl hN ∘ c) s) s t) = 0 := isGeodesic_iff

theorem arcLen_eq' (c : ℝ → Bridge.Sub hN) (a b : ℝ) :
    arcLen (n := n) c a b = Morse.pathLength (incl hN ∘ c) a b := arcLen_eq c a b

theorem expDefined_of_mem_expDom' {q : Bridge.Sub hN} {w : Rn n}
    (h : (incl hN q, D hN q w) ∈ Morse.expDom hN) : ExpDefined (conn (hN := hN)) q w :=
  expDefined_of_mem_expDom h

theorem expMap_eq' {q : Bridge.Sub hN} {w : Rn n} (h : (incl hN q, D hN q w) ∈ Morse.expDom hN) :
    incl hN (expMap (conn (hN := hN)) q w) = Morse.exp hN (incl hN q) (D hN q w) := expMap_eq h

theorem eqOn_Icc_of_isGeodesic' {c₁ c₂ : ℝ → Bridge.Sub hN}
    (h₁ : IsGeodesic (conn (hN := hN)) c₁ (Icc 0 1)) (h₂ : IsGeodesic (conn (hN := hN)) c₂ (Icc 0 1))
    (h0 : c₁ 0 = c₂ 0)
    (h0' : derivWithin (incl hN ∘ c₁) (Icc 0 1) 0 = derivWithin (incl hN ∘ c₂) (Icc 0 1) 0) :
    EqOn c₁ c₂ (Icc 0 1) := eqOn_Icc_of_isGeodesic zero_lt_one h₁ h₂ h0 h0'

theorem initData_iff' {γ : ℝ → Bridge.Sub hN} {s : Set ℝ} {q : Bridge.Sub hN} {w : Rn n}
    (h0 : γ 0 = q) : InitData (n := n) γ s q w ↔ D hN (γ 0) (vel (n := n) γ s 0) = D hN q w :=
  initData_iff h0

/-- The Riemannian norm of `T_qN` (blind `nrm`) is the ambient norm. -/
theorem incl_val (x : Bridge.Sub hN) : incl hN x = Subtype.val x := rfl

theorem nrm_eq (q : Bridge.Sub hN) (w : Rn n) : nrm (n := n) q w = ‖D hN q w‖ :=
  RoundTrip.Bridge.norm_eq q w

theorem mem_tball_iff {q : Bridge.Sub hN} {ε : ℝ} {w : Rn n} :
    w ∈ tball (n := n) q ε ↔ ‖D hN q w‖ < ε := by
  show nrm (n := n) q w < ε ↔ _
  rw [nrm_eq]

theorem isOpen_tball (q : Bridge.Sub hN) (ε : ℝ) : IsOpen (tball (n := n) q ε) := by
  have : tball (n := n) q ε = (fun w => ‖D hN q w‖) ⁻¹' Iio ε := by
    ext w; exact mem_tball_iff
  rw [this]
  exact isOpen_Iio.preimage (continuous_norm.comp (D hN q).continuous)

theorem mem_tangentSubspace_of_eq {x y : Bridge.Sub hN} (h : x = y) {v : V}
    (hv : v ∈ Morse.tangentSubspace hN x) : v ∈ Morse.tangentSubspace hN y := by
  subst h; exact hv

/-- A blind geodesic on `[0, 1]` extends to a project geodesic on an open interval
(`Morse.exists_initial_ray`), with the same initial data. -/
theorem isGeodesicFrom_of_isGeodesic {γ : ℝ → Bridge.Sub hN}
    (hγ : IsGeodesic (conn (hN := hN)) γ (Icc 0 1)) :
    ∃ g : ℝ → V, Morse.IsGeodesicFrom hN g (incl hN (γ 0))
        (D hN (γ 0) (vel (n := n) γ (Icc 0 1) 0)) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, g t = incl hN (γ t) := by
  obtain ⟨-, hcd, -⟩ := isGeodesic_iff'.1 hγ
  have hγ' : RoundTrip.BridgePrelude.IsGeodesic (conn (hN := hN)) γ (Icc 0 1) := hγ
  have hc : Morse.IsSmoothCurveIn hN (incl hN ∘ γ) := ⟨hcd, fun t _ => (γ t).2⟩
  obtain ⟨η, hη, hray, heq⟩ := Morse.exists_initial_ray (hN := hN) hc (isGeodesicOn_Ioo hγ')
  set g : ℝ → V := fun t => Morse.exp hN ((incl hN ∘ γ) 0)
    (t • Morse.velAlong (incl hN ∘ γ) 0) with hg
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h0J : (0 : ℝ) ∈ Ioo (-η) (1 + η) := ⟨by linarith, by linarith⟩
  refine ⟨g, ⟨η, hη, hray, heq 0 h0I, ?_⟩, heq⟩
  have h1 : HasDerivWithinAt (incl hN ∘ γ) (deriv g 0) (Icc 0 1) 0 :=
    (hray.hasDerivAt h0J).hasDerivWithinAt.congr (fun t ht => (heq t ht).symm) (heq 0 h0I).symm
  rw [D_vel' (isSmoothCurve_iff.2 hcd) (uniqueDiffOn_Icc zero_lt_one) h0I]
  exact (uniqueDiffOn_Icc zero_lt_one 0 h0I).eq_deriv _ h1
    (h1.differentiableWithinAt.hasDerivWithinAt)

/-- The blind `exp_q w` is defined iff the project's is. -/
theorem mem_expDom_of_expDefined {q : Bridge.Sub hN} {w : Rn n}
    (h : ExpDefined (conn (hN := hN)) q w) : (incl hN q, D hN q w) ∈ Morse.expDom hN := by
  obtain ⟨γ, hγ, h0, hv⟩ := h
  obtain ⟨g, hg, -⟩ := isGeodesicFrom_of_isGeodesic hγ
  have hD := (initData_iff' (s := Icc 0 1) (w := w) h0).1 ⟨h0, hv⟩
  rw [hD, h0] at hg
  exact ⟨g, hg⟩

/-- The length of a blind geodesic on `[0, 1]` is the norm of its initial velocity. -/
theorem arcLen_isGeodesic {γ : ℝ → Bridge.Sub hN} (hγ : IsGeodesic (conn (hN := hN)) γ (Icc 0 1)) :
    arcLen (n := n) γ 0 1 = ‖D hN (γ 0) (vel (n := n) γ (Icc 0 1) 0)‖ := by
  obtain ⟨g, ⟨δ, hδ, hgeo, -, hd⟩, heq⟩ := isGeodesicFrom_of_isGeodesic hγ
  rw [arcLen_eq', pathLength_congr (c := incl hN ∘ γ) (c' := g) zero_le_one (fun t ht => (heq t ht).symm),
    hgeo.pathLength_eq isPreconnected_Ioo zero_le_one
      (Icc_subset_Ioo (by linarith) (by linarith)) (t₀ := 0) ⟨by linarith, by linarith⟩, hd]
  ring

/-- A project geodesic `t ↦ exp_q(tv)` gives a blind geodesic of length `‖v‖` on `[0, 1]` with
initial velocity `v`. -/
theorem exists_joinsShort {q₁ q₂ : Bridge.Sub hN} {v : V} {ε : ℝ}
    (hv : v ∈ Morse.tangentSubspace hN q₁) (hdom : (incl hN q₁, v) ∈ Morse.expDom hN)
    (hvε : ‖v‖ < ε) (hexp : Morse.exp hN (incl hN q₁) v = incl hN q₂) :
    ∃ γ, JoinsShort (conn (hN := hN)) ε γ q₁ q₂ ∧
      HEq (vel (n := n) γ (Icc 0 1) 0) (L hN q₁ v) := by
  obtain ⟨g, hg⟩ := hdom
  have hg' : Morse.IsGeodesicFrom hN g (incl hN q₁) (D hN q₁ (L hN q₁ v)) := by
    rw [D_L hv]; exact hg
  obtain ⟨h1, h2, h3⟩ := isGeodesic_lift_of_isGeodesicFrom (w := L hN q₁ v) hg'
  have h1' : IsGeodesic (conn (hN := hN)) (lift g q₁) (Icc 0 1) := h1
  have h2' : InitData (n := n) (lift g q₁) (Icc 0 1) q₁ (L hN q₁ v) := h2
  refine ⟨lift g q₁, ⟨h1', h2'.1, ?_, ?_⟩, h2'.2⟩
  · apply Subtype.ext
    change incl hN (lift g q₁ 1) = incl hN q₂
    rw [h3 1 ⟨zero_le_one, le_rfl⟩, ← hexp, hg.exp_eq]
  · rw [arcLen_isGeodesic h1', (initData_iff' h2'.1).1 h2', D_L hv]
    exact hvε

/-- Every `w` in the blind ball has `exp_q` defined in the project's sense. -/
theorem NormalCoord.mem_expDom {q : Bridge.Sub hN} {ε : ℝ} (nc : Morse.NormalCoord hN q ε)
    {w : Rn n} (hw : w ∈ tball (n := n) q ε) : (incl hN q, D hN q w) ∈ Morse.expDom hN :=
  nc.mem_expDom _ (D_mem q w) (mem_tball_iff.1 hw)

/-- **Dictionary: a project normal radius gives a blind normal ball** (Riemannian norm), with
`U_q = N ∩ nc.U`. -/
theorem isNormBall_of_normalCoord {q : Bridge.Sub hN} {ε : ℝ} (nc : Morse.NormalCoord hN q ε) :
    IsNormBall (conn (hN := hN)) q ε {y | incl hN y ∈ nc.U} := by
  have hval : ∀ w ∈ tball (n := n) q ε,
      incl hN (expMap (conn (hN := hN)) q w) = Morse.exp hN (Subtype.val q) (D hN q w) :=
    fun w hw => expMap_eq' (NormalCoord.mem_expDom nc hw)
  have hT : ∀ w : Rn n, D hN q w ∈ Morse.tangentSubspace hN q := D_mem q
  refine ⟨nc.isOpen_U.preimage continuous_subtype_val,
    fun w hw => expDefined_of_mem_expDom' (NormalCoord.mem_expDom nc hw), ?_, ?_, ?_, ?_⟩
  · intro w₁ h₁ w₂ h₂ h12
    apply D_injective q
    have e : incl hN (expMap (conn (hN := hN)) q w₁) = incl hN (expMap (conn (hN := hN)) q w₂) :=
      congrArg (incl hN) h12
    rw [hval w₁ h₁, hval w₂ h₂] at e
    rw [← nc.G_exp _ (hT w₁) (mem_tball_iff.1 h₁), ← nc.G_exp _ (hT w₂) (mem_tball_iff.1 h₂)]
    exact congrArg nc.G e
  · ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      show incl hN _ ∈ nc.U
      rw [hval w hw]
      exact nc.exp_mem_U _ (hT w) (mem_tball_iff.1 hw)
    · intro hy
      have hyU : (incl hN y) ∈ nc.U := hy
      have hGT := nc.G_mem _ hyU y.2
      have hw : L hN q (nc.G (incl hN y)) ∈ tball q ε := by
        rw [mem_tball_iff, D_L hGT]; exact nc.norm_G_lt _ hyU y.2
      refine ⟨_, hw, ?_⟩
      apply Subtype.ext
      change incl hN _ = incl hN y
      rw [hval _ hw, D_L hGT]
      exact nc.exp_G _ hyU y.2
  · intro w hw
    have h : ContMDiffAt 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) ∞ (fun w' : Rn n => expMap (conn (hN := hN)) q w') w :=
      Morse.contMDiffAt_of_val_eventuallyEq hN (F := fun w' : Rn n => nc.F (D hN q w')) ?_ ?_
    · exact h.contMDiffWithinAt
    · exact (nc.contDiffOn_F.contDiffAt (nc.isOpen_O.mem_nhds
        (nc.mem_O _ (hT w) (mem_tball_iff.1 hw)))).comp w (D hN q).contDiff.contDiffAt
    · filter_upwards [(isOpen_tball q ε).mem_nhds hw] with w' hw'
      rw [nc.F_eq _ (hT w') (mem_tball_iff.1 hw')]
      exact hval w' hw'
  · refine ⟨fun y => L hN q (nc.G (incl hN y)), ?_, fun w hw => ?_⟩
    · intro y hy
      have hy' : incl hN y ∈ nc.U := hy
      have hG : ContMDiffAt 𝓘(ℝ, Rn n) 𝓘(ℝ, V) ∞ (fun y : Bridge.Sub hN => nc.G (incl hN y)) y :=
        (nc.contDiffOn_G.contDiffAt (nc.isOpen_U.mem_nhds hy')).contMDiffAt.comp y
          (contMDiff_incl y)
      exact ((L hN q).contDiff.contMDiff.contMDiffAt.comp y hG).contMDiffWithinAt
    · show L hN q (nc.G (incl hN (expMap _ q w))) = w
      rw [hval w hw, nc.G_exp _ (hT w) (mem_tball_iff.1 hw), L_D]

/-- **Dictionary: a blind normal ball gives the project's `PartialDiffeomorph` form of
`exp_q`** (the form of `Morse.exists_expDiffeo` / `Morse.NormalCoord.expDiffeo`): `exp_q` on the
open `ε`-ball of the inner product space `T_qN ⊆ V` is a `PartialDiffeomorph` onto `U`. -/
theorem exists_partialDiffeomorph_of_isNormBall {q : Bridge.Sub hN} {ε : ℝ}
    {U : Set (Bridge.Sub hN)} (h : IsNormBall (conn (hN := hN)) q ε U) :
    letI := hN.chartedSpace
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Morse.tangentSubspace hN q) 𝓘(ℝ, Rn n)
      (Morse.tangentSubspace hN q) N ∞, Φ.source = Metric.ball 0 ε ∧ Φ.target = U ∧
        ∀ v ∈ Φ.source, ((Φ v : N) : V) = Morse.exp hN (incl hN q) v := by
  let _ : ChartedSpace (Rn n) N := hN.chartedSpace
  obtain ⟨hUo, hdef, -, himg, hsm, g, hg, hgl⟩ := h
  set T := Morse.tangentSubspace hN q with hT
  let Lq : T →L[ℝ] Rn n := (L hN q).comp T.subtypeL
  let Dq : Rn n →L[ℝ] T := (D hN q).codRestrict T (D_mem q)
  have hLq : ∀ v : T, D hN q (Lq v) = v := fun v => D_L v.2
  have hball : ∀ v : T, v ∈ Metric.ball (0 : T) ε ↔ Lq v ∈ tball (n := n) q ε := by
    intro v
    rw [Metric.mem_ball, dist_zero_right, mem_tball_iff, hLq]
    rfl
  have hexpv : ∀ w ∈ tball (n := n) q ε,
      incl hN (expMap (conn (hN := hN)) q w) = Morse.exp hN (incl hN q) (D hN q w) :=
    fun w hw => expMap_eq' (mem_expDom_of_expDefined (hdef w hw))
  have hgD : ∀ y ∈ U, g y ∈ tball (n := n) q ε ∧ expMap (conn (hN := hN)) q (g y) = y := by
    intro y hy
    rw [← himg] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    rw [hgl w hw]
    exact ⟨hw, rfl⟩
  refine ⟨{ toFun := fun v => (expMap (conn (hN := hN)) q (Lq v) : Bridge.Sub hN)
            invFun := fun y => Dq (g y)
            source := Metric.ball 0 ε
            target := U
            map_source' := fun v hv => by
              rw [← himg]
              exact ⟨Lq v, (hball v).1 hv, rfl⟩
            map_target' := fun y hy => by
              rw [hball]
              show L hN q (D hN q (g y)) ∈ tball (n := n) q ε
              rw [L_D]
              exact (hgD y hy).1
            left_inv' := fun v hv => by
              apply Subtype.ext
              show D hN q (g (expMap (conn (hN := hN)) q (Lq v))) = v
              rw [hgl _ ((hball v).1 hv), hLq]
            right_inv' := fun y hy => by
              show expMap (conn (hN := hN)) q (L hN q (D hN q (g y))) = y
              rw [L_D]
              exact (hgD y hy).2
            open_source := Metric.isOpen_ball
            open_target := hUo
            contMDiffOn_toFun := hsm.comp Lq.contMDiff.contMDiffOn (fun v hv => (hball v).1 hv)
            contMDiffOn_invFun := Dq.contMDiff.comp_contMDiffOn hg }, rfl, rfl, fun v hv => ?_⟩
  show incl hN (expMap (conn (hN := hN)) q (Lq v)) = _
  rw [hexpv _ ((hball v).1 hv), hLq]


/-- **Dictionary, converse: the project's `PartialDiffeomorph` form of `exp_q` gives a blind normal
ball.** (Every `v` in the ball lies in the domain of `exp`: otherwise `exp_q v = q = exp_q 0`
(junk value) would contradict injectivity.) -/
theorem isNormBall_of_partialDiffeomorph {q : Bridge.Sub hN} {ε : ℝ}
    (Φ : letI := hN.chartedSpace
      PartialDiffeomorph 𝓘(ℝ, Morse.tangentSubspace hN q) 𝓘(ℝ, Rn n)
        (Morse.tangentSubspace hN q) N ∞)
    (hs : Φ.source = Metric.ball 0 ε)
    (hΦ : ∀ v ∈ Φ.source, ((Φ v : N) : V) = Morse.exp hN (incl hN q) v) :
    IsNormBall (conn (hN := hN)) q ε Φ.target := by
  let _ : ChartedSpace (Rn n) N := hN.chartedSpace
  let Dq : Rn n →L[ℝ] Morse.tangentSubspace hN q :=
    (D hN q).codRestrict (Morse.tangentSubspace hN q) (D_mem q)
  have hball : ∀ w : Rn n, w ∈ tball (n := n) q ε ↔ Dq w ∈ Φ.source := by
    intro w
    rw [hs, Metric.mem_ball, dist_zero_right, mem_tball_iff]
    rfl
  -- every `v` in the ball is in the domain of `exp`
  have hdom : ∀ v ∈ Φ.source, (incl hN q, (v : V)) ∈ Morse.expDom hN := by
    intro v hv
    by_contra hnot
    have hε : 0 < ε := by
      have := hv; rw [hs, Metric.mem_ball, dist_zero_right] at this
      exact (norm_nonneg _).trans_lt this
    have h0 : (0 : Morse.tangentSubspace hN q) ∈ Φ.source := by rw [hs]; exact Metric.mem_ball_self hε
    have hv0 : v = 0 := by
      apply Φ.toPartialEquiv.injOn hv h0
      apply Subtype.ext
      rw [hΦ v hv, hΦ 0 h0]
      have e1 : Morse.exp hN (incl hN q) (v : V) = incl hN q := by
        unfold Morse.exp; exact dif_neg hnot
      rw [e1, Submodule.coe_zero]
      exact (Morse.exp_zero (hN := hN) q.2).symm
    apply hnot
    rw [hv0, Submodule.coe_zero]
    exact Morse.zero_mem_expDom q.2
  have hval : ∀ w ∈ tball (n := n) q ε,
      expMap (conn (hN := hN)) q w = (Φ (Dq w) : Bridge.Sub hN) := by
    intro w hw
    apply Subtype.ext
    change incl hN (expMap (conn (hN := hN)) q w) = ((Φ (Dq w) : N) : V)
    rw [expMap_eq' (hdom _ ((hball w).1 hw)), hΦ _ ((hball w).1 hw)]
    rfl
  refine ⟨Φ.open_target, fun w hw => expDefined_of_mem_expDom' (hdom _ ((hball w).1 hw)),
    ?_, ?_, ?_, ?_⟩
  · intro w₁ h₁ w₂ h₂ h12
    apply D_injective q
    have e : Dq w₁ = Dq w₂ := by
      apply Φ.toPartialEquiv.injOn ((hball w₁).1 h₁) ((hball w₂).1 h₂)
      have := h12
      simp only at this
      rw [hval w₁ h₁, hval w₂ h₂] at this
      exact this
    exact congrArg Subtype.val e
  · ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      simp only
      rw [hval w hw]
      exact Φ.toPartialEquiv.map_source ((hball w).1 hw)
    · intro hy
      have hsrc := Φ.toPartialEquiv.map_target hy
      refine ⟨L hN q (Φ.toPartialEquiv.symm y : V), ?_, ?_⟩
      · rw [hball]
        convert hsrc using 1
        exact Subtype.ext (D_L (Φ.toPartialEquiv.symm y).2)
      · have hw : L hN q (Φ.toPartialEquiv.symm y : V) ∈ tball (n := n) q ε := by
          rw [hball]
          convert hsrc using 1
          exact Subtype.ext (D_L (Φ.toPartialEquiv.symm y).2)
        simp only
        rw [hval _ hw]
        have e : Dq (L hN q (Φ.toPartialEquiv.symm y : V)) = Φ.toPartialEquiv.symm y :=
          Subtype.ext (D_L (Φ.toPartialEquiv.symm y).2)
        rw [e]
        exact Φ.toPartialEquiv.right_inv hy
  · have h1 : ContMDiffOn 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) ∞
        (fun w => (Φ (Dq w) : Bridge.Sub hN)) (tball (n := n) q ε) :=
      Φ.contMDiffOn_toFun.comp Dq.contMDiff.contMDiffOn (fun w hw => (hball w).1 hw)
    exact h1.congr fun w hw => hval w hw
  · refine ⟨fun y => L hN q (Φ.toPartialEquiv.symm y : V), ?_, fun w hw => ?_⟩
    · have h1 := Φ.contMDiffOn_invFun
      exact (((L hN q).comp (Morse.tangentSubspace hN q).subtypeL).contMDiff.comp_contMDiffOn h1)
    · show L hN q (Φ.toPartialEquiv.symm (expMap (conn (hN := hN)) q w : Bridge.Sub hN) : V) = w
      rw [hval w hw, Φ.toPartialEquiv.left_inv ((hball w).1 hw)]
      exact L_D q w

/-- **Smooth extension from an open subset of `N`**: a function smooth on an open `U ⊆ N` is the
restriction of a function smooth on an open `U' ⊆ V` with `N ∩ U' = U` (local retractions
`Morse.exists_retraction`, glued by a smooth partition of unity,
`exists_contMDiffMap_forall_mem_convex_of_local`). -/
theorem exists_ambient_ext {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {U : Set (Bridge.Sub hN)} (hU : IsOpen U) {g : Bridge.Sub hN → E}
    (hg : ContMDiffOn 𝓘(ℝ, Rn n) 𝓘(ℝ, E) ∞ g U) :
    ∃ U' : Set V, IsOpen U' ∧ (∀ y : Bridge.Sub hN, incl hN y ∈ U' ↔ y ∈ U) ∧
      ∃ G : V → E, ContDiffOn ℝ ∞ G U' ∧ ∀ y ∈ U, G (incl hN y) = g y := by
  classical
  obtain ⟨O', hO', hO'U⟩ := isOpen_induced_iff.1 hU
  have hmemU : ∀ y : Bridge.Sub hN, y ∈ U ↔ incl hN y ∈ O' := fun y => by
    rw [← hO'U]; rfl
  have hr : ∀ y : Bridge.Sub hN, ∃ Ur : Set V, IsOpen Ur ∧ incl hN y ∈ Ur ∧ ∃ r : V → V,
      ContDiffOn ℝ ∞ r Ur ∧ (∀ x ∈ Ur, r x ∈ N) ∧ ∀ x ∈ Ur, x ∈ N → r x = x :=
    fun y => Morse.exists_retraction hN y
  choose Ur hUr hyUr r hrs hrN hrid using hr
  set O : Bridge.Sub hN → Set V := fun z => Ur z ∩ O' ∩ (Ur z ∩ r z ⁻¹' O') with hOdef
  have hO : ∀ z, IsOpen (O z) := fun z =>
    ((hUr z).inter hO').inter ((hrs z).continuousOn.isOpen_inter_preimage (hUr z) hO')
  set U' : Set V := ⋃ z ∈ U, O z with hU'def
  have hU' : IsOpen U' := isOpen_biUnion fun z _ => hO z
  have hN' : ∀ y : Bridge.Sub hN, incl hN y ∈ U' ↔ y ∈ U := by
    intro y
    constructor
    · intro hy
      obtain ⟨z, -, hz⟩ := mem_iUnion₂.1 hy
      exact (hmemU y).2 hz.1.2
    · intro hy
      refine mem_iUnion₂.2 ⟨y, hy, ⟨hyUr y, (hmemU y).1 hy⟩, hyUr y, ?_⟩
      show r y (incl hN y) ∈ O'
      rw [hrid y _ (hyUr y) y.2]
      exact (hmemU y).1 hy
  -- local representatives
  let lift : Bridge.Sub hN → V → Bridge.Sub hN := fun z x =>
    ⟨if r z x ∈ N then r z x else incl hN z, by
      split_ifs with h
      · exact h
      · exact z.2⟩
  have hlift : ∀ z, ∀ x ∈ Ur z, incl hN (lift z x) = r z x := fun z x hx => by
    show (if r z x ∈ N then r z x else incl hN z) = r z x
    rw [if_pos (hrN z x hx)]
  set Gz : Bridge.Sub hN → V → E := fun z x => g (lift z x) with hGz
  have hGzs : ∀ z, ContDiffOn ℝ ∞ (Gz z) (O z) := by
    intro z x hx
    have hxU : x ∈ Ur z := hx.1.1
    have hl : ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ, Rn n) ∞ (lift z) x :=
      Morse.contMDiffAt_of_val_eventuallyEq hN (F := r z)
        ((hrs z).contDiffAt ((hUr z).mem_nhds hxU))
        (by
          filter_upwards [(hUr z).mem_nhds hxU] with x' hx'
          exact hlift z x' hx')
    have hlU : lift z x ∈ U := by
      rw [hmemU, hlift z x hxU]; exact hx.2.2
    have hgx : ContMDiffAt 𝓘(ℝ, Rn n) 𝓘(ℝ, E) ∞ g (lift z x) :=
      hg.contMDiffAt (hU.mem_nhds hlU)
    exact (contMDiffAt_iff_contDiffAt.1 (hgx.comp x hl)).contDiffWithinAt
  have hGzeq : ∀ z, ∀ x ∈ O z, ∀ hx : x ∈ N, Gz z x = g ⟨x, hx⟩ := by
    intro z x hxO hx
    show g (lift z x) = g ⟨x, hx⟩
    congr 1
    apply Subtype.ext
    exact (hlift z x hxO.1.1).trans (hrid z x hxO.1.1 hx)
  -- the open manifold `U'`
  let Uo : TopologicalSpace.Opens V := ⟨U', hU'⟩
  have : LocallyCompactSpace Uo := hU'.locallyCompactSpace
  let t : Uo → Set E := fun x => {e | ∀ hx : (x : V) ∈ N, e = g ⟨x, hx⟩}
  have ht : ∀ x, Convex ℝ (t x) := by
    intro x
    by_cases hx : (x : V) ∈ N
    · have : t x = {g ⟨x, hx⟩} := by
        ext e
        simp only [t, mem_ofPred_eq, mem_singleton_iff]
        exact ⟨fun h => h hx, fun h _ => h⟩
      rw [this]; exact convex_singleton _
    · have : t x = univ := by
        ext e
        simp only [t, mem_ofPred_eq, mem_univ, iff_true]
        exact fun h => absurd h hx
      rw [this]; exact convex_univ
  have Hloc : ∀ x : Uo, ∃ S ∈ 𝓝 x, ∃ f : Uo → E,
      ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ((⊤ : ℕ∞) : WithTop ℕ∞) f S ∧ ∀ y ∈ S, f y ∈ t y := by
    intro x
    obtain ⟨z, hzU, hxz⟩ := mem_iUnion₂.1 x.2
    by_cases hxN : (x : V) ∈ N
    · refine ⟨Subtype.val ⁻¹' O z, (hO z).preimage continuous_subtype_val |>.mem_nhds hxz,
        fun y => Gz z y, fun y hy => ?_, fun y hy hyN => hGzeq z y hy hyN⟩
      have h1 : ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ (Gz z) y :=
        ((hGzs z).contDiffAt ((hO z).mem_nhds hy)).contMDiffAt
      exact (contMDiffAt_subtype_iff.2 h1).contMDiffWithinAt
    · set S0 : Set V := O z ∩ (Ur z ∩ (fun x' => r z x' - x') ⁻¹' {0}ᶜ) with hS0
      have hS0o : IsOpen S0 :=
        (hO z).inter (((hrs z).continuousOn.sub continuousOn_id).isOpen_inter_preimage (hUr z)
          isOpen_compl_singleton)
      have hxS0 : (x : V) ∈ S0 := by
        refine ⟨hxz, hxz.1.1, ?_⟩
        simp only [mem_preimage, mem_compl_iff, mem_singleton_iff, sub_eq_zero]
        intro h
        exact hxN (h ▸ hrN z x hxz.1.1)
      refine ⟨Subtype.val ⁻¹' S0, hS0o.preimage continuous_subtype_val |>.mem_nhds hxS0,
        fun _ => 0, contMDiffOn_const, fun y hy hyN => ?_⟩
      exfalso
      have := hy.2.2
      simp only [mem_preimage, mem_compl_iff, mem_singleton_iff, sub_eq_zero] at this
      exact this (hrid z y hy.2.1 hyN)
  obtain ⟨G₀, hG₀⟩ := exists_contMDiffMap_forall_mem_convex_of_local 𝓘(ℝ, V) ht Hloc
  refine ⟨U', hU', hN', fun x => if h : x ∈ U' then G₀ ⟨x, h⟩ else 0, ?_, ?_⟩
  · intro x hx
    have h1 : ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ, E) ∞
        (fun x' : Uo => (fun x => if h : x ∈ U' then G₀ ⟨x, h⟩ else 0) (x' : V)) ⟨x, hx⟩ := by
      have e : (fun x' : Uo => (fun x => if h : x ∈ U' then G₀ ⟨x, h⟩ else 0) (x' : V)) = G₀ := by
        funext x'
        beta_reduce
        rw [dif_pos (show (x' : V) ∈ U' from x'.2)]
      rw [e]
      exact G₀.contMDiff _
    exact (contMDiffAt_iff_contDiffAt.1 ((contMDiffAt_subtype_iff (U := Uo)
      (f := fun x => if h : x ∈ U' then G₀ ⟨x, h⟩ else 0) (x := ⟨x, hx⟩)).1 h1)).contDiffWithinAt
  · intro y hy
    have hyU' : incl hN y ∈ U' := (hN' y).2 hy
    simp only [dif_pos hyU']
    exact hG₀ ⟨incl hN y, hyU'⟩ y.2


/-- **Dictionary, converse: a blind normal ball gives a project normal radius** (`NormalCoord`):
`F = incl ∘ exp_q ∘ L_q ∘ P_q` extends `exp_q`, and the blind smooth inverse extends to an
ambient open set by `exists_ambient_ext`. -/
theorem isNormalRadius_of_isNormBall {q : Bridge.Sub hN} {ε : ℝ} {U : Set (Bridge.Sub hN)}
    (hε : 0 < ε) (h : IsNormBall (conn (hN := hN)) q ε U) : Morse.IsNormalRadius hN q ε := by
  obtain ⟨hUo, hdef, -, himg, hsm, g, hg, hgl⟩ := h
  obtain ⟨U', hU'o, hU'N, G₀, hG₀s, hG₀⟩ := exists_ambient_ext hUo hg
  have hdom : ∀ w ∈ tball (n := n) q ε, (incl hN q, D hN q w) ∈ Morse.expDom hN :=
    fun w hw => mem_expDom_of_expDefined (hdef w hw)
  have hval : ∀ w ∈ tball (n := n) q ε,
      incl hN (expMap (conn (hN := hN)) q w) = Morse.exp hN (incl hN q) (D hN q w) :=
    fun w hw => expMap_eq' (hdom w hw)
  have hLt : ∀ v ∈ Morse.tangentSubspace hN q, ‖v‖ < ε → L hN q v ∈ tball (n := n) q ε :=
    fun v hv hvε => by rw [mem_tball_iff, D_L hv]; exact hvε
  have hexpv : ∀ v ∈ Morse.tangentSubspace hN q, ‖v‖ < ε →
      Morse.exp hN (incl hN q) v = incl hN (expMap (conn (hN := hN)) q (L hN q v)) :=
    fun v hv hvε => by rw [hval _ (hLt v hv hvε), D_L hv]
  have hinU : ∀ w ∈ tball (n := n) q ε, expMap (conn (hN := hN)) q w ∈ U := fun w hw => by
    rw [← himg]; exact ⟨w, hw, rfl⟩
  have hfromU : ∀ y : Bridge.Sub hN, y ∈ U →
      ∃ w ∈ tball (n := n) q ε, expMap (conn (hN := hN)) q w = y ∧ g y = w := by
    intro y hy
    rw [← himg] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    exact ⟨w, hw, rfl, hgl w hw⟩
  have hPmem : ∀ v : V, ‖P hN q v‖ < ε → L hN q (P hN q v) ∈ tball (n := n) q ε :=
    fun v hv => by rw [mem_tball_iff, D_L_P]; exact hv
  refine ⟨{ O := {v | ‖P hN q v‖ < ε}
            U := U'
            F := fun v => incl hN (expMap (conn (hN := hN)) q (L hN q (P hN q v)))
            G := fun y => D hN q (G₀ y)
            pos := hε
            isOpen_O := isOpen_lt (continuous_norm.comp (P hN q).continuous) continuous_const
            isOpen_U := hU'o
            contDiffOn_F := ?_
            contDiffOn_G := (D hN q).contDiff.comp_contDiffOn hG₀s
            mem_expDom := fun v hv hvε => by
              have := hdom _ (hLt v hv hvε)
              rwa [D_L hv] at this
            mem_O := fun v hv hvε => by
              show ‖P hN q v‖ < ε
              rw [show P hN q v = v from Morse.tanProj_eq_self hN hv]
              exact hvε
            F_eq := fun v hv hvε => by
              show incl hN (expMap (conn (hN := hN)) q (L hN q (P hN q v))) = _
              rw [show P hN q v = v from Morse.tanProj_eq_self hN hv]
              exact (hexpv v hv hvε).symm
            exp_mem_U := fun v hv hvε => by
              rw [← incl_val q, hexpv v hv hvε]
              exact (hU'N _).2 (hinU _ (hLt v hv hvε))
            G_exp := fun v hv hvε => by
              show D hN q (G₀ (Morse.exp hN (Subtype.val q) v)) = v
              rw [← incl_val q, hexpv v hv hvε, hG₀ _ (hinU _ (hLt v hv hvε)),
                hgl _ (hLt v hv hvε), D_L hv]
            G_mem := fun y _ _ => D_mem q _
            norm_G_lt := fun y hyU hyN => by
              obtain ⟨w, hw, hwy, hgw⟩ := hfromU ⟨y, hyN⟩ ((hU'N ⟨y, hyN⟩).1 hyU)
              show ‖D hN q (G₀ (incl hN ⟨y, hyN⟩))‖ < ε
              rw [hG₀ _ ((hU'N ⟨y, hyN⟩).1 hyU), hgw]
              exact mem_tball_iff.1 hw
            exp_G := fun y hyU hyN => by
              obtain ⟨w, hw, hwy, hgw⟩ := hfromU ⟨y, hyN⟩ ((hU'N ⟨y, hyN⟩).1 hyU)
              show Morse.exp hN (Subtype.val q) (D hN q (G₀ (incl hN ⟨y, hyN⟩))) = y
              rw [hG₀ _ ((hU'N ⟨y, hyN⟩).1 hyU), hgw, ← incl_val q, ← hval w hw, hwy]
              rfl }⟩
  intro v hv
  have hmem := hPmem v hv
  have h1 : ContMDiffAt 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) ∞ (fun w : Rn n => expMap (conn (hN := hN)) q w)
      (L hN q (P hN q v)) := hsm.contMDiffAt ((isOpen_tball q ε).mem_nhds hmem)
  have h12 : ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ, Rn n) ∞
      (fun v => expMap (conn (hN := hN)) q (L hN q (P hN q v))) v :=
    h1.comp v ((L hN q).comp (P hN q)).contDiff.contMDiff.contMDiffAt
  have h2 : ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ, V) ∞
      (fun v => incl hN (expMap (conn (hN := hN)) q (L hN q (P hN q v)))) v :=
    (contMDiff_incl _).comp v h12
  exact (contMDiffAt_iff_contDiffAt.1 h2).contDiffWithinAt

/-- The derivative of `exp_q` (on the vector space `T_qN`) at a point of the `ε`-ball. -/
theorem hasFDerivAt_expT {q : N} {ε : ℝ} (nc : Morse.NormalCoord hN q ε)
    (w : Morse.tangentSubspace hN q) (hw : ‖(w : V)‖ < ε) :
    HasFDerivAt (fun v : Morse.tangentSubspace hN q => Morse.exp hN q v)
      (fderiv ℝ (fun v : Morse.tangentSubspace hN q => Morse.exp hN q v) w) w := by
  have hev : (fun v : Morse.tangentSubspace hN q => Morse.exp hN q v) =ᶠ[𝓝 w]
      fun v : Morse.tangentSubspace hN q => nc.F v := by
    have hball : ∀ᶠ v : Morse.tangentSubspace hN q in 𝓝 w, ‖(v : V)‖ < ε :=
      (continuous_norm.comp continuous_subtype_val).continuousAt.eventually (gt_mem_nhds hw)
    filter_upwards [hball] with v hv
    exact (nc.F_eq v v.2 hv).symm
  have hFd : HasFDerivAt nc.F (fderiv ℝ nc.F w)
      (((Morse.tangentSubspace hN q).subtypeL : Morse.tangentSubspace hN q →L[ℝ] V) w) :=
    nc.hasFDerivAt_F w.2 hw
  have hT : HasFDerivAt (fun v : Morse.tangentSubspace hN q => nc.F v)
      ((fderiv ℝ nc.F w).comp (Morse.tangentSubspace hN q).subtypeL) w :=
    hFd.comp w (Morse.tangentSubspace hN q).subtypeL.hasFDerivAt
  have h := hT.congr_of_eventuallyEq hev
  rwa [← h.fderiv] at h

/-- Constant speed of the radial geodesic, from the project's geodesic theory (not from A):
`‖d(exp_q)_w(w)‖ = ‖w‖`. -/
theorem norm_fderiv_expT_self {q : N} {ε : ℝ} (nc : Morse.NormalCoord hN q ε)
    (w : Morse.tangentSubspace hN q) (hw : ‖(w : V)‖ < ε) :
    ‖fderiv ℝ (fun v : Morse.tangentSubspace hN q => Morse.exp hN q v) w w‖ = ‖(w : V)‖ := by
  set E := fun v : Morse.tangentSubspace hN q => Morse.exp hN q v with hEdef
  have hE := hasFDerivAt_expT nc w hw
  obtain ⟨γ, hγ⟩ := nc.mem_expDom w w.2 hw
  obtain ⟨δ, hδ, hgeo, -⟩ := hγ.isGeodesicOn_exp_smul
  have hline : HasDerivAt (fun t : ℝ => t • w) w 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const w
  have h1 : HasDerivAt (fun t : ℝ => E (t • w)) (fderiv ℝ E w w) 1 :=
    hE.comp_hasDerivAt_of_eq (1 : ℝ) hline (one_smul ℝ w).symm
  have h1' : HasDerivAt (fun t : ℝ => Morse.exp hN q (t • (w : V))) (fderiv ℝ E w w) 1 := h1
  have h0 := Morse.hasDerivAt_exp_smul_zero (hN := hN) q w.2
  have := hgeo.norm_deriv_eq isPreconnected_Ioo (t := 1) (t' := 0)
    ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
  rw [h1'.deriv, h0.deriv] at this
  exact this

/-- **Orthogonality from B**: `⟨d(exp_q)_w(w), d(exp_q)_w(x)⟩ = 0` for `x ⊥ w`, obtained from B
applied to the curve of unit vectors `t ↦ cos t · w/‖w‖ + sin t · x/‖x‖` at `t = 0`,
`r = ‖w‖`. -/
theorem inner_fderiv_expT_eq_zero (hB : B_emb) [ConnectedSpace (Bridge.Sub hN)] {q : N} {ε : ℝ}
    (nc : Morse.NormalCoord hN q ε) (w x : Morse.tangentSubspace hN q) (hw : ‖(w : V)‖ < ε)
    (hw0 : w ≠ 0) (hwx : ⟪(w : V), (x : V)⟫ = 0) :
    ⟪fderiv ℝ (fun v : Morse.tangentSubspace hN q => Morse.exp hN q v) w w,
      fderiv ℝ (fun v : Morse.tangentSubspace hN q => Morse.exp hN q v) w x⟫ = 0 := by
  set E := fun v : Morse.tangentSubspace hN q => Morse.exp hN q v with hEdef
  set Dw := fderiv ℝ E w with hDw
  have hE : HasFDerivAt E Dw w := hasFDerivAt_expT nc w hw
  by_cases hx0 : x = 0
  · rw [hx0, map_zero, inner_zero_right]
  let q' : Bridge.Sub hN := q
  set r : ℝ := ‖(w : V)‖ with hr
  have hrpos : 0 < r := norm_pos_iff.2 (fun h => hw0 (Subtype.ext h))
  set s : ℝ := ‖(x : V)‖ with hs
  have hspos : 0 < s := norm_pos_iff.2 (fun h => hx0 (Subtype.ext h))
  set u : Morse.tangentSubspace hN q := r⁻¹ • w with hu
  set e : Morse.tangentSubspace hN q := s⁻¹ • x with he
  have hwu : r • u = w := by rw [hu, smul_smul, mul_inv_cancel₀ hrpos.ne', one_smul]
  have hxe : s • e = x := by rw [he, smul_smul, mul_inv_cancel₀ hspos.ne', one_smul]
  have hnu : ‖(u : V)‖ = 1 := by
    rw [hu, Submodule.coe_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hrpos,
      inv_mul_cancel₀ hrpos.ne']
  have hne : ‖(e : V)‖ = 1 := by
    rw [he, Submodule.coe_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hspos,
      inv_mul_cancel₀ hspos.ne']
  have hue : ⟪(u : V), (e : V)⟫ = 0 := by
    rw [hu, he, Submodule.coe_smul, Submodule.coe_smul, inner_smul_left, inner_smul_right, hwx]
    simp
  clear_value u e
  -- the curve of unit vectors
  set vT : ℝ → Morse.tangentSubspace hN q := fun t => Real.cos t • u + Real.sin t • e with hvT
  have hvT0 : vT 0 = u := by simp [hvT]
  have hnorm_vT : ∀ t, ‖(vT t : V)‖ = 1 := by
    intro t
    have h2 : ‖(vT t : V)‖ ^ 2 = 1 := by
      have : (vT t : V) = Real.cos t • (u : V) + Real.sin t • (e : V) := rfl
      rw [this, norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right, hue,
        hnu, hne, Real.norm_eq_abs, Real.norm_eq_abs]
      simp only [mul_zero, mul_one, conj_trivial, add_zero]
      rw [sq_abs, sq_abs, Real.cos_sq_add_sin_sq]
    have h0 := norm_nonneg (vT t : V)
    nlinarith [h2, h0]
  set vR : ℝ → Rn n := fun t => L hN q' (vT t : V) with hvR
  have hDvR : ∀ t, D hN q' (vR t) = (vT t : V) := fun t => D_L (vT t).2
  have hvR_smooth : ContDiffOn ℝ ∞ vR univ := by
    have hc : ContDiff ℝ ∞ vT :=
      (Real.contDiff_cos.smul contDiff_const).add (Real.contDiff_sin.smul contDiff_const)
    exact (((L hN q').comp (Morse.tangentSubspace hN q).subtypeL).contDiff.comp hc).contDiffOn
  have hunit : ∀ t ∈ (univ : Set ℝ), nrm (n := n) q' (vR t) = 1 := by
    intro t _
    rw [nrm_eq, hDvR, hnorm_vT]
  -- B at `r = ‖w‖`, `t = 0`
  have key := hB V W n N hN q' ε {y | incl hN y ∈ nc.U} nc.pos (isNormBall_of_normalCoord nc) univ
    vR ⟨ordConnected_univ, uniqueDiffOn_univ⟩ hvR_smooth hunit r ⟨hrpos, hw⟩ 0 (mem_univ _)
  -- read B in `V`
  set c₁ : ℝ → Bridge.Sub hN := fun s' => expMap (conn (hN := hN)) q' (s' • vR 0) with hc₁
  set c₂ : ℝ → Bridge.Sub hN := fun τ => expMap (conn (hN := hN)) q' (r • vR τ) with hc₂
  have key' : ⟪D hN (c₁ r) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) c₁ r 1),
      D hN (c₂ 0) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) c₂ 0 1)⟫ = 0 := by
    have e2 : mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) c₂ univ 0 = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) c₂ 0 := by
      rw [mfderivWithin_univ]
    have := key
    simp only [rinner, dfr, dft] at this
    rw [e2] at this
    exact this
  rw [D_mfderiv_curve, D_mfderiv_curve] at key'
  -- the two derivatives
  have hexpv : ∀ z : Rn n, ‖D hN q' z‖ < ε →
      incl hN (expMap (conn (hN := hN)) q' z) = Morse.exp hN q (D hN q' z) := fun z hz =>
    expMap_eq' (nc.mem_expDom _ (D_mem q' z) hz)
  have hd1 : deriv (incl hN ∘ c₁) r = Dw u := by
    have hev : (incl hN ∘ c₁) =ᶠ[𝓝 r] fun s' => E (s' • u) := by
      filter_upwards [Ioo_mem_nhds (show -ε < r by linarith) hw] with s' hs'
      have hlt : ‖D hN q' (s' • vR 0)‖ < ε := by
        rw [map_smul, hDvR, hvT0, norm_smul, hnu, mul_one, Real.norm_eq_abs, abs_lt]
        exact hs'
      simp only [Function.comp_apply, hc₁]
      rw [hexpv _ hlt, map_smul, hDvR, hvT0]
      rfl
    have hline : HasDerivAt (fun s' : ℝ => s' • u) u r := by
      simpa using (hasDerivAt_id r).smul_const u
    exact hev.deriv_eq.trans (hE.comp_hasDerivAt_of_eq r hline hwu.symm).deriv
  have hd2 : deriv (incl hN ∘ c₂) 0 = Dw (r • e) := by
    have hev : (incl hN ∘ c₂) = fun τ => E (r • vT τ) := by
      funext τ
      have hlt : ‖D hN q' (r • vR τ)‖ < ε := by
        rw [map_smul, hDvR, norm_smul, hnorm_vT, mul_one, Real.norm_eq_abs, abs_of_pos hrpos]
        exact hw
      simp only [Function.comp_apply, hc₂]
      rw [hexpv _ hlt, map_smul, hDvR]
      rfl
    have hcurve : HasDerivAt (fun τ : ℝ => r • vT τ) (r • e) 0 := by
      have h1 : HasDerivAt vT e 0 := by
        have hc := (Real.hasDerivAt_cos 0).smul_const u
        have hs' := (Real.hasDerivAt_sin 0).smul_const e
        have := hc.add hs'
        rwa [show -Real.sin 0 • u + Real.cos 0 • e = e by simp] at this
      exact h1.const_smul r
    have hpt : r • vT 0 = w := by rw [hvT0, hwu]
    rw [hev]
    exact (hE.comp_hasDerivAt_of_eq 0 hcurve hpt.symm).deriv
  rw [hd1, hd2, map_smul, inner_smul_right] at key'
  have hue' : ⟪Dw u, Dw e⟫ = 0 := by
    rcases mul_eq_zero.1 key' with h | h
    · exact absurd h hrpos.ne'
    · exact h
  rw [← hwu, ← hxe, map_smul, map_smul, inner_smul_left, inner_smul_right, hue']
  simp

/-- **B on embedded manifolds gives the Gauss lemma** of A: orthogonality from B, constant speed
from the project's geodesic theory. -/
theorem gauss_of_B_emb (hB : B_emb) [ConnectedSpace (Bridge.Sub hN)] {q : N} {ε : ℝ}
    (h : Morse.IsNormalRadius hN q ε) (w x : Morse.tangentSubspace hN q) (hw : ‖(w : V)‖ < ε) :
    ⟪fderiv ℝ (fun v : Morse.tangentSubspace hN q => Morse.exp hN q v) w w,
      fderiv ℝ (fun v : Morse.tangentSubspace hN q => Morse.exp hN q v) w x⟫ = ⟪(w : V), x⟫ := by
  obtain ⟨nc⟩ := h
  set Dw := fderiv ℝ (fun v : Morse.tangentSubspace hN q => Morse.exp hN q v) w with hDw
  by_cases hw0 : w = 0
  · rw [hw0, map_zero, inner_zero_left, Submodule.coe_zero, inner_zero_left]
  have hwpos : 0 < ‖(w : V)‖ := norm_pos_iff.2 (fun h => hw0 (Subtype.ext h))
  set a : ℝ := ⟪(w : V), (x : V)⟫ / ‖(w : V)‖ ^ 2 with ha
  set x' : Morse.tangentSubspace hN q := x - a • w with hx'
  have hwx' : ⟪(w : V), (x' : V)⟫ = 0 := by
    rw [hx', Submodule.coe_sub, Submodule.coe_smul, inner_sub_right, inner_smul_right,
      real_inner_self_eq_norm_sq, ha]
    field_simp
    ring
  have h0 := inner_fderiv_expT_eq_zero hB nc w x' hw hw0 hwx'
  have hsp := norm_fderiv_expT_self nc w hw
  have hx : x = a • w + x' := by rw [hx']; abel
  rw [hx, map_add, map_smul, inner_add_right, inner_smul_right, h0, add_zero,
    real_inner_self_eq_norm_sq, hsp, Submodule.coe_add, Submodule.coe_smul, inner_add_right,
    inner_smul_right, real_inner_self_eq_norm_sq, hwx', add_zero]


/-- **A's Gauss lemma gives B on embedded manifolds**: for a blind normal ball (a project normal
radius by `isNormalRadius_of_isNormBall`) and a curve `v` of unit vectors, `∂f/∂r = d(exp_q)_w(v)`
and `∂f/∂t = d(exp_q)_w(r v')` at `w = r v(t)`, and `⟨w, v'⟩ = 0`. -/
theorem B_emb_of_gauss_orth
    (hG : ∀ {q : N} {ε : ℝ}, Morse.IsNormalRadius hN q ε → ∀ (w x : Morse.tangentSubspace hN q),
      ‖(w : V)‖ < ε → ⟪(w : V), x⟫ = 0 →
        ⟪fderiv ℝ (fun v : Morse.tangentSubspace hN q => Morse.exp hN q v) w w,
          fderiv ℝ (fun v : Morse.tangentSubspace hN q => Morse.exp hN q v) w x⟫ = 0)
    (q : Bridge.Sub hN) (ε : ℝ) (U : Set (Bridge.Sub hN)) (hε : 0 < ε)
    (hU : IsNormBall (conn (hN := hN)) q ε U) (J : Set ℝ) (v : ℝ → Rn n) (hJ : IsIntv J)
    (hv : ContDiffOn ℝ ∞ v J) (hunit : ∀ t ∈ J, nrm (n := n) q (v t) = 1) (r : ℝ)
    (hr : r ∈ Ioo 0 ε) (t : ℝ) (ht : t ∈ J) :
    rinner (expMap (conn (hN := hN)) q (r • v t)) (dfr (conn (hN := hN)) q v r t)
      (dft (conn (hN := hN)) q v J r t) = 0 := by
  have hNR := isNormalRadius_of_isNormBall hε hU
  obtain ⟨nc⟩ := hNR
  have hrpos : 0 < r := hr.1
  have hrε : r < ε := hr.2
  let Dq : Rn n →L[ℝ] Morse.tangentSubspace hN q :=
    (D hN q).codRestrict (Morse.tangentSubspace hN q) (D_mem q)
  set vT : ℝ → Morse.tangentSubspace hN q := fun τ => Dq (v τ) with hvT
  have hvTcoe : ∀ τ, ((vT τ : Morse.tangentSubspace hN q) : V) = D hN q (v τ) := fun τ => rfl
  have hvTn : ∀ τ ∈ J, ‖(vT τ : V)‖ = 1 := fun τ hτ => by
    rw [hvTcoe, ← nrm_eq]; exact hunit τ hτ
  set w : Morse.tangentSubspace hN q := r • vT t with hw
  have hwn : ‖(w : V)‖ = r := by
    rw [hw, Submodule.coe_smul, norm_smul, hvTn t ht, Real.norm_eq_abs, abs_of_pos hrpos,
      mul_one]
  have hwε : ‖(w : V)‖ < ε := by rw [hwn]; exact hrε
  set E := fun x : Morse.tangentSubspace hN q => Morse.exp hN (Subtype.val q) x with hEdef
  set Dw := fderiv ℝ E w with hDw
  have hE : HasFDerivAt E Dw w := hasFDerivAt_expT nc w hwε
  -- the derivative of `v` within `J`
  have hvd : HasDerivWithinAt v (derivWithin v J t) J t :=
    ((hv.differentiableOn (by simp)) t ht).hasDerivWithinAt
  set vT' : Morse.tangentSubspace hN q := Dq (derivWithin v J t) with hvT'
  have hvTd : HasDerivWithinAt vT vT' J t := Dq.hasFDerivAt.comp_hasDerivWithinAt t hvd
  -- `⟨v, v'⟩ = 0`
  have horth : ⟪(vT t : V), (vT' : V)⟫ = 0 := by
    have h1 := hvTd.inner (𝕜 := ℝ) hvTd
    have h2 : HasDerivWithinAt (fun τ => ⟪vT τ, vT τ⟫) 0 J t := by
      refine (hasDerivWithinAt_const t J (1 : ℝ)).congr (fun τ hτ => ?_) ?_
      · rw [real_inner_self_eq_norm_sq, Submodule.coe_norm, hvTn τ hτ, one_pow]
      · rw [real_inner_self_eq_norm_sq, Submodule.coe_norm, hvTn t ht, one_pow]
    have h3 := (hJ.2 t ht).eq_deriv _ h1 h2
    rw [real_inner_comm (vT t) vT'] at h3
    have h4 : ⟪vT t, vT'⟫ = 0 := by linarith
    exact h4
  have hwv' : ⟪(w : V), (vT' : V)⟫ = 0 := by
    rw [hw, Submodule.coe_smul, inner_smul_left, horth]; simp
  have hG0 : ⟪Dw w, Dw vT'⟫ = 0 := hG ⟨nc⟩ w vT' hwε hwv'
  -- read `∂f/∂r` and `∂f/∂t` in `V`
  have hexpv : ∀ z : Rn n, ‖D hN q z‖ < ε →
      incl hN (expMap (conn (hN := hN)) q z) = Morse.exp hN (Subtype.val q) (D hN q z) :=
    fun z hz => expMap_eq' (nc.mem_expDom _ (D_mem q z) hz)
  set c₁ : ℝ → Bridge.Sub hN := fun s => expMap (conn (hN := hN)) q (s • v t) with hc₁
  set c₂ : ℝ → Bridge.Sub hN := fun τ => expMap (conn (hN := hN)) q (r • v τ) with hc₂
  have hd1 : D hN (c₁ r) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) c₁ r 1) = Dw (vT t) := by
    rw [D_mfderiv_curve]
    have hev : (incl hN ∘ c₁) =ᶠ[𝓝 r] fun s => E (s • vT t) := by
      filter_upwards [Ioo_mem_nhds (show -ε < r by linarith) hrε] with s hs
      have hlt : ‖D hN q (s • v t)‖ < ε := by
        rw [map_smul, norm_smul, ← hvTcoe, hvTn t ht, mul_one, Real.norm_eq_abs, abs_lt]
        exact hs
      simp only [Function.comp_apply, hc₁]
      rw [hexpv _ hlt, map_smul]
      rfl
    have hline : HasDerivAt (fun s : ℝ => s • vT t) (vT t) r := by
      simpa using (hasDerivAt_id r).smul_const (vT t)
    exact hev.deriv_eq.trans (hE.comp_hasDerivAt_of_eq r hline rfl).deriv
  have hd2 : D hN (c₂ t) (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) c₂ J t 1) = Dw (r • vT') := by
    have heq : EqOn (incl hN ∘ c₂) (fun τ => E (r • vT τ)) J := by
      intro τ hτ
      have hlt : ‖D hN q (r • v τ)‖ < ε := by
        rw [map_smul, norm_smul, ← hvTcoe, hvTn τ hτ, mul_one, Real.norm_eq_abs,
          abs_of_pos hrpos]
        exact hrε
      simp only [Function.comp_apply, hc₂]
      rw [hexpv _ hlt, map_smul]
      rfl
    have hcurve : HasDerivWithinAt (fun τ => r • vT τ) (r • vT') J t := hvTd.const_smul r
    have hEc : HasDerivWithinAt (fun τ => E (r • vT τ)) (Dw (r • vT')) J t :=
      hE.comp_hasDerivWithinAt_of_eq t hcurve rfl
    have hinc : HasDerivWithinAt (incl hN ∘ c₂) (Dw (r • vT')) J t :=
      hEc.congr (fun τ hτ => heq hτ) (heq ht)
    have hmd : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) c₂ J t :=
      mdifferentiableWithinAt_curve_iff.2 hinc.differentiableWithinAt
    exact (hJ.2 t ht).eq_deriv _ (hasDerivWithinAt_incl_comp hmd) hinc
  change ⟪D hN (c₁ r) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) c₁ r 1),
    D hN (c₂ t) (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) c₂ J t 1)⟫ = 0
  rw [hd1, hd2, map_smul, inner_smul_right]
  have hDwvt : Dw (vT t) = r⁻¹ • Dw w := by
    rw [hw, map_smul, smul_smul, inv_mul_cancel₀ hrpos.ne', one_smul]
  rw [hDwvt, inner_smul_left, hG0]
  simp

end Emb

/-- The Gauss-lemma conjuncts of A (`gauss_lemma`, `gauss_lemma_orthogonal`), for slice
submanifolds modelled on `ℝⁿ` that are connected (B assumes `M` connected). -/
def A_gauss : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)] {q : N} {ε : ℝ}, Morse.IsNormalRadius hN q ε →
    ∀ (w x : Morse.tangentSubspace hN q), ‖(w : V)‖ < ε →
      ⟪fderiv ℝ (fun v : Morse.tangentSubspace hN q => Morse.exp hN q v) w w,
        fderiv ℝ (fun v : Morse.tangentSubspace hN q => Morse.exp hN q v) w x⟫ = ⟪(w : V), x⟫ ∧
      (⟪(w : V), x⟫ = 0 →
        ⟪fderiv ℝ (fun v : Morse.tangentSubspace hN q => Morse.exp hN q v) w w,
          fderiv ℝ (fun v : Morse.tangentSubspace hN q => Morse.exp hN q v) w x⟫ = 0)

theorem A_to_A_gauss : A → A_gauss := fun hA _ _ _ _ _ _ _ _ _ _ _ _ _ _ h w x hw =>
  ⟨hA.2.2.1 h w x hw, hA.2.2.2 h w x hw⟩

/-- **B on embedded manifolds implies the Gauss-lemma part of A.** -/
theorem B_emb_to_A_gauss : B_emb → A_gauss := by
  intro hB V _ _ _ W _ _ _ n N hN _ q ε h w x hw
  have e := Emb.gauss_of_B_emb hB h w x hw
  exact ⟨e, fun h0 => e.trans h0⟩

theorem B_to_A_gauss : B → A_gauss := fun hB => B_emb_to_A_gauss (B_to_B_emb hB)

/-- **A implies B on embedded manifolds** (uses A's `gauss_lemma_orthogonal`; a blind normal ball
is a project normal radius by `Emb.isNormalRadius_of_isNormBall`). -/
theorem A_to_B_emb : A → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN _ q ε U hε hU J v hJ hv hunit r hr t ht
  exact Emb.B_emb_of_gauss_orth (hN := hN) (fun h w x hw hwx => hA.2.2.2 h w x hw hwx)
    q ε U hε hU J v hJ hv hunit r hr t ht

/-- So on embedded manifolds (model `ℝⁿ`, connected) B is equivalent to the Gauss-lemma part of
A. -/
theorem B_emb_iff_A_gauss : B_emb ↔ A_gauss := by
  constructor
  · exact B_emb_to_A_gauss
  · intro hA V _ _ _ W _ _ _ n N hN _ q ε U hε hU J v hJ hv hunit r hr t ht
    exact Emb.B_emb_of_gauss_orth (hN := hN)
      (fun h w x hw hwx => (hA V W n N hN h w x hw).2 hwx) q ε U hε hU J v hJ hv hunit r hr t ht

#rt_check RoundTrip.V7_12.A_to_B_emb [Morse.NormalCoord.norm_fderiv_F_apply,
  Morse.NormalCoord.injective_fderiv_F, Morse.gauss_lemma, Morse.gauss_lemma_orthogonal]
#rt_check RoundTrip.V7_12.B_to_A_gauss [Morse.NormalCoord.norm_fderiv_F_apply,
  Morse.NormalCoord.injective_fderiv_F, Morse.gauss_lemma, Morse.gauss_lemma_orthogonal]
#rt_overlap RoundTrip.V7_12.B_to_A_gauss [Morse.NormalCoord.norm_fderiv_F_apply,
  Morse.NormalCoord.injective_fderiv_F, Morse.gauss_lemma, Morse.gauss_lemma_orthogonal]

end RoundTrip.V7_12
