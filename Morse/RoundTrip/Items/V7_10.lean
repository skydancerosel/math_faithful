import Morse
import RoundTrip.Check
import RoundTrip.Blind.V7_10
import RoundTrip.Bridge

open Set Filter Topology Function
open scoped ContDiff Manifold

namespace RoundTrip.V7_10

/-- The project's statement (universes instantiated at 0): the chart Jacobian of
`F(q, v) = (q, exp_q v)` at `(u₀, 0)`; Lemma 10.3 for slice submanifolds `N ⊆ V` with `W = N ∩ O`;
its clause (1) for geodesics; every point has a normal radius; `exp_q` is a `PartialDiffeomorph`
of an `ε`-ball of `T_qN` onto an open subset of `N` containing `q`. -/
def A : Prop :=
  type_of% @Morse.LocalSpray.hasFDerivAt_chartF.{0,0,0} ∧
    type_of% @Morse.lemma_10_3.{0,0,0} ∧
    type_of% @Morse.lemma_10_3_geodesic.{0,0,0} ∧
    type_of% @Morse.exists_isNormalRadius.{0,0,0} ∧
    type_of% @Morse.exists_expDiffeo.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.LocalSpray.hasFDerivAt_chartF, @Morse.lemma_10_3, @Morse.lemma_10_3_geodesic,
    @Morse.exists_isNormalRadius, @Morse.exists_expDiffeo⟩

/-! ## The embedded special case: dictionary -/

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

/-- **Dictionary: the conclusion of the project's Lemma 10.3 gives the blind one** for
`W = N ∩ O`. -/
theorem isUniformNormal_of {O : Set V} {ε : ℝ}
    (h1 : ∀ q₁ q₂ : N, (q₁ : V) ∈ O → (q₂ : V) ∈ O →
        ∃! v, v ∈ Morse.tangentSubspace hN q₁ ∧ ‖v‖ < ε ∧ Morse.exp hN q₁ v = q₂)
    (h2 : ∃ O₂ : Set (V × V), IsOpen O₂ ∧ ∃ G : V × V → V, ContDiffOn ℝ ∞ G O₂ ∧
        ∀ q₁ q₂ : N, (q₁ : V) ∈ O → (q₂ : V) ∈ O → ((q₁ : V), (q₂ : V)) ∈ O₂ ∧
          G (q₁, q₂) ∈ Morse.tangentSubspace hN q₁ ∧ ‖G (q₁, q₂)‖ < ε ∧
          Morse.exp hN q₁ (G (q₁, q₂)) = q₂)
    (h3 : ∀ q : N, (q : V) ∈ O → Morse.IsNormalRadius hN q ε) :
    IsUniformNormal (conn (hN := hN)) {y : Bridge.Sub hN | incl hN y ∈ O} ε := by
  -- uniqueness of short geodesics
  have huniq : ∀ q₁ q₂ : Bridge.Sub hN, incl hN q₁ ∈ O → incl hN q₂ ∈ O → ∀ γ γ',
      JoinsShort (conn (hN := hN)) ε γ q₁ q₂ → JoinsShort (conn (hN := hN)) ε γ' q₁ q₂ →
      EqOn γ γ' (Icc 0 1) := by
    intro q₁ q₂ hq₁ hq₂ γ γ' hγ hγ'
    obtain ⟨v, -, hvu⟩ := h1 q₁ q₂ hq₁ hq₂
    have key : ∀ c, JoinsShort (conn (hN := hN)) ε c q₁ q₂ →
        derivWithin (incl hN ∘ c) (Icc 0 1) 0 = v := by
      rintro c ⟨hc, hc0, hc1, hcl⟩
      obtain ⟨g, hg, heq⟩ := isGeodesicFrom_of_isGeodesic hc
      have hcd := (isGeodesic_iff'.1 hc).2.1
      have hD := D_vel' (isSmoothCurve_iff.2 hcd) (uniqueDiffOn_Icc zero_lt_one)
        (⟨le_rfl, zero_le_one⟩ : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
      rw [← hD]
      apply hvu
      refine ⟨mem_tangentSubspace_of_eq hc0 (D_mem _ _), ?_, ?_⟩
      · rw [← arcLen_isGeodesic hc]; exact hcl
      · have e1 : Morse.exp hN (incl hN q₁) (D hN (c 0) (vel (n := n) c (Icc 0 1) 0)) = g 1 := by
          have := hg.exp_eq
          rwa [show incl hN (c 0) = incl hN q₁ from congrArg _ hc0] at this
        exact e1.trans ((heq 1 ⟨zero_le_one, le_rfl⟩).trans (congrArg _ hc1))
    exact eqOn_Icc_of_isGeodesic' hγ.1 hγ'.1 (hγ.2.1.trans hγ'.2.1.symm)
      ((key γ hγ).trans (key γ' hγ').symm)
  -- existence, from a short vector
  have hex : ∀ q₁ q₂ : Bridge.Sub hN, incl hN q₁ ∈ O → ∀ v, v ∈ Morse.tangentSubspace hN q₁ →
      ‖v‖ < ε → Morse.exp hN (incl hN q₁) v = incl hN q₂ → ∃ γ, JoinsShort (conn (hN := hN)) ε γ q₁ q₂ ∧
        HEq (vel (n := n) γ (Icc 0 1) 0) (L hN q₁ v) := by
    intro q₁ q₂ hq₁ v hv hvε hexp
    obtain ⟨nc⟩ := h3 q₁ hq₁
    exact exists_joinsShort hv (nc.mem_expDom v hv hvε) hvε hexp
  refine ⟨fun q₁ hq₁ q₂ hq₂ => ?_, ?_, fun q hq => ?_⟩
  · obtain ⟨v, ⟨hv, hvε, hexp⟩, -⟩ := h1 q₁ q₂ hq₁ hq₂
    obtain ⟨γ, hγ, -⟩ := hex q₁ q₂ hq₁ v hv hvε hexp
    exact ⟨γ, hγ, fun γ' hγ' => huniq q₁ q₂ hq₁ hq₂ γ γ' hγ hγ'⟩
  · obtain ⟨O₂, hO₂, G, hG, hGp⟩ := h2
    refine ⟨fun x => ⟨x.1, L hN x.1 (G (incl hN x.1, incl hN x.2))⟩, ?_, fun q₁ hq₁ q₂ hq₂ => ?_⟩
    · intro x hx
      rw [contMDiffWithinAt_tangent_iff]
      refine ⟨(contMDiff_fst).contMDiffAt.contMDiffWithinAt, ?_⟩
      have hp := hGp x.1 x.2 hx.1 hx.2
      have hi : ContMDiff ((𝓘(ℝ, Rn n)).prod (𝓘(ℝ, Rn n))) 𝓘(ℝ, V × V) ∞
          (fun x : Bridge.Sub hN × Bridge.Sub hN => (incl hN x.1, incl hN x.2)) :=
        (contMDiff_incl.comp contMDiff_fst).prodMk_space (contMDiff_incl.comp contMDiff_snd)
      have h1' : ContMDiffAt ((𝓘(ℝ, Rn n)).prod (𝓘(ℝ, Rn n))) 𝓘(ℝ, V) ∞
          (fun x : Bridge.Sub hN × Bridge.Sub hN => G (incl hN x.1, incl hN x.2)) x :=
        (hG.contDiffAt (hO₂.mem_nhds hp.1)).contMDiffAt.comp x (hi x)
      refine h1'.contMDiffWithinAt.congr (fun y hy => ?_) ?_
      · exact D_L (hGp y.1 y.2 hy.1 hy.2).2.1
      · exact D_L hp.2.1
    · obtain ⟨-, hT, hε, hexp⟩ := hGp q₁ q₂ hq₁ hq₂
      obtain ⟨γ, hγ, hv⟩ := hex q₁ q₂ hq₁ _ hT hε hexp
      exact ⟨rfl, γ, hγ, hv⟩
  · obtain ⟨nc⟩ := h3 q hq
    refine ⟨_, fun y hy => ?_, isNormBall_of_normalCoord nc⟩
    obtain ⟨v, ⟨hv, hvε, hexp⟩, -⟩ := h1 q y hq hy
    show incl hN y ∈ nc.U
    have := nc.exp_mem_U v hv hvε
    rwa [hexp] at this

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


/-- The data of a blind short geodesic, read in `V`: its initial velocity `v ∈ T_{q₁}N` has
`‖v‖ < ε` and `exp_{q₁}(v) = q₂`. -/
theorem joinsShort_data {ε : ℝ} {γ : ℝ → Bridge.Sub hN} {q₁ q₂ : Bridge.Sub hN}
    (hγ : JoinsShort (conn (hN := hN)) ε γ q₁ q₂) :
    D hN (γ 0) (vel (n := n) γ (Icc 0 1) 0) ∈ Morse.tangentSubspace hN q₁ ∧
      ‖D hN (γ 0) (vel (n := n) γ (Icc 0 1) 0)‖ < ε ∧
      Morse.exp hN (incl hN q₁) (D hN (γ 0) (vel (n := n) γ (Icc 0 1) 0)) = incl hN q₂ := by
  obtain ⟨hg, h0, h1, hl⟩ := hγ
  obtain ⟨g, hgf, heq⟩ := isGeodesicFrom_of_isGeodesic hg
  refine ⟨mem_tangentSubspace_of_eq h0 (D_mem _ _), ?_, ?_⟩
  · rw [← arcLen_isGeodesic hg]; exact hl
  · have e1 := hgf.exp_eq
    rw [show incl hN (γ 0) = incl hN q₁ from congrArg _ h0] at e1
    exact e1.trans ((heq 1 ⟨zero_le_one, le_rfl⟩).trans (congrArg _ h1))

/-- **Dictionary, converse: B's conclusion gives the project's Lemma 10.3** (for model `ℝⁿ`): the
same `ε`, and `O = O_W ∩ U_r` with `U_r` the domain of a smooth local retraction onto `N` at `p`
(`Morse.exists_retraction`), used to extend B's smooth map `G : W × W → TN` to an open set of
`V × V`; clause (3) by `isNormalRadius_of_isNormBall`. -/
theorem lemma_10_3_of_isUniformNormal {p : Bridge.Sub hN} {W' : Set (Bridge.Sub hN)}
    (hWo : IsOpen W') (hpW : p ∈ W') {ε : ℝ} (hε : 0 < ε)
    (hUN : IsUniformNormal (conn (hN := hN)) W' ε) :
    ∃ O : Set V, IsOpen O ∧ incl hN p ∈ O ∧ ∃ ε > 0,
      (∀ q₁ q₂ : N, (q₁ : V) ∈ O → (q₂ : V) ∈ O →
        ∃! v, v ∈ Morse.tangentSubspace hN q₁ ∧ ‖v‖ < ε ∧ Morse.exp hN q₁ v = q₂) ∧
      (∃ O₂ : Set (V × V), IsOpen O₂ ∧ ∃ G : V × V → V, ContDiffOn ℝ ∞ G O₂ ∧
        ∀ q₁ q₂ : N, (q₁ : V) ∈ O → (q₂ : V) ∈ O → ((q₁ : V), (q₂ : V)) ∈ O₂ ∧
          G (q₁, q₂) ∈ Morse.tangentSubspace hN q₁ ∧ ‖G (q₁, q₂)‖ < ε ∧
          Morse.exp hN q₁ (G (q₁, q₂)) = q₂) ∧
      (∀ q : N, (q : V) ∈ O → Morse.IsNormalRadius hN q ε) := by
  classical
  obtain ⟨h1, ⟨G', hG's, hG'p⟩, h3⟩ := hUN
  obtain ⟨OW, hOW, hOWW⟩ := isOpen_induced_iff.1 hWo
  have hmemW : ∀ y : Bridge.Sub hN, y ∈ W' ↔ incl hN y ∈ OW := fun y => by
    rw [← hOWW]; rfl
  obtain ⟨Ur, hUr, hpUr, r, hrs, hrN, hrid⟩ := Morse.exists_retraction hN p
  have hNR : ∀ q : Bridge.Sub hN, q ∈ W' → Morse.IsNormalRadius hN q ε := fun q hq => by
    obtain ⟨U, -, hU⟩ := h3 q hq
    exact isNormalRadius_of_isNormBall hε hU
  refine ⟨OW ∩ Ur, hOW.inter hUr, ⟨(hmemW p).1 hpW, hpUr⟩, ε, hε, ?_, ?_,
    fun q hq => hNR q ((hmemW q).2 hq.1)⟩
  · -- (1)
    intro q₁ q₂ hq₁ hq₂
    let q₁' : Bridge.Sub hN := q₁
    let q₂' : Bridge.Sub hN := q₂
    have hW₁ : q₁' ∈ W' := (hmemW q₁').2 hq₁.1
    have hW₂ : q₂' ∈ W' := (hmemW q₂').2 hq₂.1
    obtain ⟨γ, hγ, huγ⟩ := h1 q₁' hW₁ q₂' hW₂
    obtain ⟨hvT, hvε, hvexp⟩ := joinsShort_data hγ
    refine ⟨_, ⟨hvT, hvε, hvexp⟩, fun v' ⟨hv'T, hv'ε, hv'exp⟩ => ?_⟩
    obtain ⟨nc⟩ := hNR q₁' hW₁
    obtain ⟨γ', hγ', hv'⟩ := exists_joinsShort (q₁ := q₁') (q₂ := q₂') hv'T
      (nc.mem_expDom v' hv'T hv'ε) hv'ε hv'exp
    have heqγ := huγ γ' hγ'
    have hI : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
    have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    have hc := (isGeodesic_iff'.1 hγ.1).2.1
    have hc' := (isGeodesic_iff'.1 hγ'.1).2.1
    have e1 := D_vel' (isSmoothCurve_iff.2 hc) hI h0I
    have e2 := D_vel' (isSmoothCurve_iff.2 hc') hI h0I
    have e3 : derivWithin (incl hN ∘ γ) (Icc 0 1) 0 = derivWithin (incl hN ∘ γ') (Icc 0 1) 0 :=
      derivWithin_congr (fun t ht => congrArg (incl hN) (heqγ ht)) (congrArg (incl hN) (heqγ h0I))
    have e4 := (initData_iff' (s := Icc 0 1) (w := L hN q₁' v') hγ'.2.1).1 ⟨hγ'.2.1, hv'⟩
    rw [D_L hv'T] at e4
    rw [← e4, e2, ← e3, ← e1]
  · -- (2)
    let lift : V → Bridge.Sub hN := fun x =>
      ⟨if r x ∈ N then r x else incl hN p, by
        split_ifs with h
        · exact h
        · exact p.2⟩
    have hlift : ∀ x ∈ Ur, incl hN (lift x) = r x := fun x hx => by
      show (if r x ∈ N then r x else incl hN p) = r x
      rw [if_pos (hrN x hx)]
    have hliftq : ∀ q : Bridge.Sub hN, incl hN q ∈ Ur → lift (incl hN q) = q := fun q hq =>
      Subtype.ext ((hlift _ hq).trans (hrid _ hq q.2))
    set Or : Set V := Ur ∩ r ⁻¹' OW with hOr
    have hOro : IsOpen Or := (hrs.continuousOn).isOpen_inter_preimage hUr hOW
    have hliftW : ∀ x ∈ Or, lift x ∈ W' := fun x hx => by
      rw [hmemW, hlift x hx.1]; exact hx.2
    set G : V × V → V := fun y => D hN (G' (lift y.1, lift y.2)).proj (G' (lift y.1, lift y.2)).2
      with hGdef
    refine ⟨Or ×ˢ Or, hOro.prod hOro, G, ?_, fun q₁ q₂ hq₁ hq₂ => ?_⟩
    · intro y hy
      have hl : ∀ (f : V × V → V), ContDiff ℝ ∞ f → f y ∈ Or →
          ContMDiffAt 𝓘(ℝ, V × V) 𝓘(ℝ, Rn n) ∞ (fun y => lift (f y)) y := by
        intro f hf hfy
        refine Morse.contMDiffAt_of_val_eventuallyEq hN (F := fun y => r (f y))
          ((hrs.contDiffAt (hUr.mem_nhds hfy.1)).comp y hf.contDiffAt) ?_
        filter_upwards [hf.continuous.continuousAt.preimage_mem_nhds (hUr.mem_nhds hfy.1)]
          with y' hy'
        exact hlift _ hy'
      have hΦ : ContMDiffAt 𝓘(ℝ, V × V) ((𝓘(ℝ, Rn n)).prod (𝓘(ℝ, Rn n))) ∞
          (fun y : V × V => (lift y.1, lift y.2)) y :=
        (hl Prod.fst contDiff_fst hy.1).prodMk (hl Prod.snd contDiff_snd hy.2)
      have hWW : (lift y.1, lift y.2) ∈ W' ×ˢ W' := ⟨hliftW _ hy.1, hliftW _ hy.2⟩
      have hG'a : ContMDiffAt ((𝓘(ℝ, Rn n)).prod (𝓘(ℝ, Rn n))) (𝓘(ℝ, Rn n)).tangent ∞ G'
          (lift y.1, lift y.2) := hG's.contMDiffAt ((hWo.prod hWo).mem_nhds hWW)
      have hcomp := (hG'a.comp y hΦ).contMDiffWithinAt (s := univ)
      rw [contMDiffWithinAt_tangent_iff] at hcomp
      exact (contMDiffAt_iff_contDiffAt.1 (contMDiffWithinAt_univ.1 hcomp.2)).contDiffWithinAt
    · let q₁' : Bridge.Sub hN := q₁
      let q₂' : Bridge.Sub hN := q₂
      have hq₁r : incl hN q₁' ∈ Or := ⟨hq₁.2, by
        show r (q₁ : V) ∈ OW; rw [hrid _ hq₁.2 q₁.2]; exact hq₁.1⟩
      have hq₂r : incl hN q₂' ∈ Or := ⟨hq₂.2, by
        show r (q₂ : V) ∈ OW; rw [hrid _ hq₂.2 q₂.2]; exact hq₂.1⟩
      have hW₁ : q₁' ∈ W' := (hmemW q₁').2 hq₁.1
      have hW₂ : q₂' ∈ W' := (hmemW q₂').2 hq₂.1
      obtain ⟨hproj, γ, hγ, hv⟩ := hG'p q₁' hW₁ q₂' hW₂
      have hGq : G ((q₁ : V), (q₂ : V)) = D hN (G' (q₁', q₂')).proj (G' (q₁', q₂')).2 := by
        show D hN (G' (lift (incl hN q₁'), lift (incl hN q₂'))).proj
          (G' (lift (incl hN q₁'), lift (incl hN q₂'))).2 = _
        rw [hliftq q₁' hq₁.2, hliftq q₂' hq₂.2]
      have hD : D hN (γ 0) (vel (n := n) γ (Icc 0 1) 0) =
          D hN (G' (q₁', q₂')).proj (G' (q₁', q₂')).2 :=
        (initData_iff' (s := Icc 0 1) (hγ.2.1.trans hproj.symm)).1
          ⟨hγ.2.1.trans hproj.symm, hv⟩
      obtain ⟨hvT, hvε, hvexp⟩ := joinsShort_data hγ
      rw [hGq, ← hD]
      exact ⟨⟨hq₁r, hq₂r⟩, hvT, hvε, hvexp⟩

end Emb

/-- B on embedded manifolds: `M = ↥N` with the induced metric and the induced Levi-Civita
connection (a special case of B, `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)], ∀ p : Bridge.Sub hN,
    ∃ W' : Set (Bridge.Sub hN), IsOpen W' ∧ p ∈ W' ∧ ∃ ε > 0,
      IsUniformNormal (Bridge.conn (hN := hN)) W' ε

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- **A implies B on embedded manifolds** (uses A's `lemma_10_3`). -/
theorem A_to_B_emb : A → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN _ p
  obtain ⟨O, hO, hpO, ε, hε, h1, h2, h3⟩ := hA.2.1 hN p
  exact ⟨_, hO.preimage continuous_subtype_val, hpO, ε, hε, Emb.isUniformNormal_of h1 h2 h3⟩

/-- The `exists_expDiffeo` conjunct of A, for slice submanifolds modelled on `ℝⁿ` that are
connected (B assumes `M` connected). -/
def A_expDiffeo : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)] (q : N),
    letI := hN.chartedSpace
    ∃ ε > 0, ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Morse.tangentSubspace hN q) 𝓘(ℝ, Rn n)
      (Morse.tangentSubspace hN q) N ∞, Φ.source = Metric.ball 0 ε ∧ q ∈ Φ.target ∧
        ∀ v ∈ Φ.source, ((Φ v : N) : V) = Morse.exp hN q v

theorem A_to_A_expDiffeo : A → A_expDiffeo := fun hA _ _ _ _ _ _ _ _ _ _ hN _ q =>
  hA.2.2.2.2 hN q

/-- **B on embedded manifolds gives A's `exists_expDiffeo`** (for model `ℝⁿ`, connected `N`),
through the dictionary `Emb.exists_partialDiffeomorph_of_isNormBall`. -/
theorem B_emb_to_A_expDiffeo : B_emb → A_expDiffeo := by
  intro hB V _ _ _ W _ _ _ n N hN _ q
  let q' : Bridge.Sub hN := q
  obtain ⟨W', -, hqW, ε, hε, -, -, h3⟩ := hB V W n N hN q'
  obtain ⟨U, hWU, hU⟩ := h3 q' hqW
  obtain ⟨Φ, hs, ht, hΦ⟩ := Emb.exists_partialDiffeomorph_of_isNormBall hU
  refine ⟨ε, hε, Φ, hs, ?_, hΦ⟩
  rw [ht]
  exact hWU hqW

theorem B_to_A_expDiffeo : B → A_expDiffeo := fun hB => B_emb_to_A_expDiffeo (B_to_B_emb hB)

/-- The part of A that B covers on embedded manifolds (model `ℝⁿ`, connected `N`, B assumes `M`
connected): Lemma 10.3, its clause (1) for geodesics, normal radii, and the `PartialDiffeomorph`
form. (The chart-Jacobian lemma `Morse.LocalSpray.hasFDerivAt_chartF` is a step of the proof, not
covered by B.) -/
def A_emb : Prop :=
  (∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)] (p : N),
    ∃ O : Set V, IsOpen O ∧ (p : V) ∈ O ∧ ∃ ε > 0,
      (∀ q₁ q₂ : N, (q₁ : V) ∈ O → (q₂ : V) ∈ O →
        ∃! v, v ∈ Morse.tangentSubspace hN q₁ ∧ ‖v‖ < ε ∧ Morse.exp hN q₁ v = q₂) ∧
      (∃ O₂ : Set (V × V), IsOpen O₂ ∧ ∃ G : V × V → V, ContDiffOn ℝ ∞ G O₂ ∧
        ∀ q₁ q₂ : N, (q₁ : V) ∈ O → (q₂ : V) ∈ O → ((q₁ : V), (q₂ : V)) ∈ O₂ ∧
          G (q₁, q₂) ∈ Morse.tangentSubspace hN q₁ ∧ ‖G (q₁, q₂)‖ < ε ∧
          Morse.exp hN q₁ (G (q₁, q₂)) = q₂) ∧
      (∀ q : N, (q : V) ∈ O → Morse.IsNormalRadius hN q ε)) ∧
  (∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)] (p : N), ∃ ε > 0, Morse.IsNormalRadius hN p ε) ∧
  A_expDiffeo

theorem A_to_A_emb : A → A_emb :=
  fun hA => ⟨fun _ _ _ _ _ _ _ _ _ _ hN _ p => hA.2.1 hN p,
    fun _ _ _ _ _ _ _ _ _ _ hN _ p => hA.2.2.2.1 hN p, A_to_A_expDiffeo hA⟩

/-- **B on embedded manifolds gives A** (all of A except the chart-Jacobian step and the trivial
`lemma_10_3_geodesic`), through `Emb.lemma_10_3_of_isUniformNormal`,
`Emb.isNormalRadius_of_isNormBall` and `Emb.exists_partialDiffeomorph_of_isNormBall`. -/
theorem B_emb_to_A_emb : B_emb → A_emb := by
  intro hB
  refine ⟨fun V _ _ _ W _ _ _ n N hN _ p => ?_, fun V _ _ _ W _ _ _ n N hN _ p => ?_,
    B_emb_to_A_expDiffeo hB⟩
  · let p' : Bridge.Sub hN := p
    obtain ⟨W', hWo, hpW, ε, hε, hUN⟩ := hB V W n N hN p'
    exact Emb.lemma_10_3_of_isUniformNormal hWo hpW hε hUN
  · let p' : Bridge.Sub hN := p
    obtain ⟨W', -, hpW, ε, hε, -, -, h3⟩ := hB V W n N hN p'
    obtain ⟨U, -, hU⟩ := h3 p' hpW
    exact ⟨ε, hε, Emb.isNormalRadius_of_isNormBall hε hU⟩

theorem B_to_A_emb : B → A_emb := fun hB => B_emb_to_A_emb (B_to_B_emb hB)

/-- **On embedded manifolds (model `ℝⁿ`, connected), B is equivalent to A minus the chart-Jacobian
step.** -/
theorem B_emb_iff_A_emb : B_emb ↔ A_emb := by
  refine ⟨B_emb_to_A_emb, fun hA V _ _ _ W _ _ _ n N hN _ p => ?_⟩
  obtain ⟨O, hO, hpO, ε, hε, h1, h2, h3⟩ := hA.1 V W n N hN p
  exact ⟨_, hO.preimage continuous_subtype_val, hpO, ε, hε, Emb.isUniformNormal_of h1 h2 h3⟩

/-- `lemma_10_3_geodesic` holds outright (it does not involve B or any geometry). -/
theorem lemma_10_3_geodesic_holds : type_of% @Morse.lemma_10_3_geodesic.{0,0,0} := by
  intro V _ _ _ Z _ _ _ W _ _ _ N hN q₁ q₂ ε huniq γ v hγ hvε h1
  obtain ⟨δ, hδ, hγo, h0, h0'⟩ := hγ
  have hv : v ∈ Morse.tangentSubspace hN q₁ := by
    have := hγo.deriv_mem (t := 0) ⟨by linarith, by linarith⟩
    rw [h0'] at this
    convert this using 2
    exact Subtype.ext h0.symm
  have hexp : Morse.exp hN q₁ v = q₂ := by
    rw [(show Morse.IsGeodesicFrom hN γ q₁ v from ⟨δ, hδ, hγo, h0, h0'⟩).exp_eq, h1]
  exact huniq.unique ⟨hv, hvε, hexp⟩ huniq.exists.choose_spec

#rt_check RoundTrip.V7_10.A_to_B_emb [Morse.LocalSpray.hasFDerivAt_chartF, Morse.lemma_10_3,
  Morse.lemma_10_3_geodesic, Morse.exists_isNormalRadius, Morse.exists_expDiffeo]
#rt_check RoundTrip.V7_10.B_to_A_expDiffeo [Morse.LocalSpray.hasFDerivAt_chartF, Morse.lemma_10_3,
  Morse.lemma_10_3_geodesic, Morse.exists_isNormalRadius, Morse.exists_expDiffeo]
#rt_check RoundTrip.V7_10.B_to_A_emb [Morse.LocalSpray.hasFDerivAt_chartF, Morse.lemma_10_3,
  Morse.lemma_10_3_geodesic, Morse.exists_isNormalRadius, Morse.exists_expDiffeo]
#rt_check RoundTrip.V7_10.lemma_10_3_geodesic_holds [Morse.LocalSpray.hasFDerivAt_chartF,
  Morse.lemma_10_3, Morse.lemma_10_3_geodesic, Morse.exists_isNormalRadius, Morse.exists_expDiffeo]
#rt_overlap RoundTrip.V7_10.B_to_A_emb [Morse.LocalSpray.hasFDerivAt_chartF, Morse.lemma_10_3,
  Morse.lemma_10_3_geodesic, Morse.exists_isNormalRadius, Morse.exists_expDiffeo]
#rt_overlap RoundTrip.V7_10.B_to_A_expDiffeo [Morse.LocalSpray.hasFDerivAt_chartF, Morse.lemma_10_3,
  Morse.lemma_10_3_geodesic, Morse.exists_isNormalRadius, Morse.exists_expDiffeo]

end RoundTrip.V7_10
