import Morse
import RoundTrip.Check
import RoundTrip.Blind.«V7_10′»
import RoundTrip.Bridge

open Set Filter Topology Function
open scoped ContDiff Manifold

namespace RoundTrip.«V7_10′»

/-- The project's statement (universes instantiated at 0): every point `x ∈ N` of a slice
submanifold is the centre of *good balls* — the ambient balls `B(x, r)`, `r ≤ r₀`, are good
(`Morse.IsGoodBall`: open; for one `δ > 0` any two points of `N ∩ O` are at distance `< δ` and
joined as in Corollary 10.8 at scale `δ` (unique geodesic of length `< δ`, minimal, smoothly
dependent); the minimal geodesic between them stays in `N ∩ O`); and Lebesgue numbers for good
balls on compact subsets of `N`. -/
def A : Prop :=
  type_of% @Morse.exists_isGoodBall_ball.{0,0,0} ∧
    type_of% @Morse.exists_lebesgue_goodBall.{0,0,0}

theorem A_holds : A := ⟨@Morse.exists_isGoodBall_ball, @Morse.exists_lebesgue_goodBall⟩

/-! ## The embedded special case: dictionary (copied from `Items/V7_10.lean`) -/

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


/-- A project geodesic `g` from `q₁` with initial velocity `v`, `‖v‖ < ε`, ending at `q₂`, gives a
blind short geodesic which is `g` on `[0, 1]`. -/
theorem exists_joinsShort_of_isGeodesicFrom {q₁ q₂ : Bridge.Sub hN} {v : V} {ε : ℝ} {g : ℝ → V}
    (hv : v ∈ Morse.tangentSubspace hN q₁) (hg : Morse.IsGeodesicFrom hN g (incl hN q₁) v)
    (hvε : ‖v‖ < ε) (h1 : g 1 = incl hN q₂) :
    ∃ γ, JoinsShort (conn (hN := hN)) ε γ q₁ q₂ ∧ ∀ t ∈ Icc (0 : ℝ) 1, incl hN (γ t) = g t := by
  have hg' : Morse.IsGeodesicFrom hN g (incl hN q₁) (D hN q₁ (L hN q₁ v)) := by
    rw [D_L hv]; exact hg
  obtain ⟨h1', h2, h3⟩ := isGeodesic_lift_of_isGeodesicFrom (w := L hN q₁ v) hg'
  have h1'' : IsGeodesic (conn (hN := hN)) (lift g q₁) (Icc 0 1) := h1'
  have h2' : InitData (n := n) (lift g q₁) (Icc 0 1) q₁ (L hN q₁ v) := h2
  refine ⟨lift g q₁, ⟨h1'', h2'.1, ?_, ?_⟩, h3⟩
  · apply Subtype.ext
    change incl hN (lift g q₁ 1) = incl hN q₂
    rw [h3 1 ⟨zero_le_one, le_rfl⟩, h1]
  · rw [arcLen_isGeodesic h1'', (initData_iff' h2'.1).1 h2', D_L hv]
    exact hvε

/-- The length of a blind smooth curve bounds the project's distance between its end points. -/
theorem riemDist_le_arcLen {γ : ℝ → Bridge.Sub hN} (hγ : IsGeodesic (conn (hN := hN)) γ (Icc 0 1)) :
    Morse.riemDist (N := N) (incl hN (γ 0)) (incl hN (γ 1)) ≤
      ENNReal.ofReal (arcLen (n := n) γ 0 1) := by
  rw [arcLen_eq']
  exact Morse.riemDist_le_pathLength
    (Morse.IsPiecewiseSmooth.of_contDiffOn (isGeodesic_iff'.1 hγ).2.1 zero_le_one subset_rfl)
    (fun t _ => (γ t).2)

end Emb

/-- B on embedded manifolds: `M = ↥N` with the induced metric and the induced Levi-Civita
connection (a special case of B, `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)], ∀ p : Bridge.Sub hN,
    ∃ W' : Set (Bridge.Sub hN), IsOpen W' ∧ p ∈ W' ∧ ∃ ε > 0,
      IsUniformNormal (Bridge.conn (hN := hN)) W' ε ∧
      ∀ q₁ ∈ W', ∀ q₂ ∈ W', ∀ γ : ℝ → Bridge.Sub hN, JoinsShort (Bridge.conn (hN := hN)) ε γ q₁ q₂ →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ W'

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- **A implies B on embedded manifolds**: a small good ball `B(p, r)` (from A's
`exists_isGoodBall_ball`) inside the `O` of Lemma 10.3 (`Morse.lemma_10_3`, another item's
theorem) gives `W = N ∩ B(p, r)`; the short geodesic of Lemma 10.3 (1) between two of its points
is the minimal geodesic of the good ball (uniqueness, its length bounds `ρ`), which stays in `W`. -/
theorem A_to_B_emb : A → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN _ p
  obtain ⟨O₀, hO₀, hpO₀, ε, hε, h1, h2, h3⟩ := Morse.lemma_10_3 hN p
  obtain ⟨r₀, hr₀, hgood⟩ := hA.1 hN p.2
  obtain ⟨r₂, hr₂, hr₂O⟩ := Metric.isOpen_iff.1 hO₀ _ hpO₀
  set r := min r₀ r₂ with hr
  have hrpos : 0 < r := lt_min hr₀ hr₂
  have hG := hgood r (min_le_left _ _)
  have hsub : Metric.ball (Bridge.incl hN p) r ⊆ O₀ :=
    (Metric.ball_subset_ball (min_le_right _ _)).trans hr₂O
  -- Lemma 10.3 restricted to the ball
  have h1' : ∀ q₁ q₂ : N, (q₁ : V) ∈ Metric.ball (Bridge.incl hN p) r → (q₂ : V) ∈ Metric.ball (Bridge.incl hN p) r →
      ∃! v, v ∈ Morse.tangentSubspace hN q₁ ∧ ‖v‖ < ε ∧ Morse.exp hN q₁ v = q₂ :=
    fun q₁ q₂ hq₁ hq₂ => h1 q₁ q₂ (hsub hq₁) (hsub hq₂)
  have h2' : ∃ O₂ : Set (V × V), IsOpen O₂ ∧ ∃ G : V × V → V, ContDiffOn ℝ ∞ G O₂ ∧
      ∀ q₁ q₂ : N, (q₁ : V) ∈ Metric.ball (Bridge.incl hN p) r → (q₂ : V) ∈ Metric.ball (Bridge.incl hN p) r →
        ((q₁ : V), (q₂ : V)) ∈ O₂ ∧ G (q₁, q₂) ∈ Morse.tangentSubspace hN q₁ ∧
          ‖G (q₁, q₂)‖ < ε ∧ Morse.exp hN q₁ (G (q₁, q₂)) = q₂ := by
    obtain ⟨O₂, hO₂, G, hGs, hGp⟩ := h2
    exact ⟨O₂, hO₂, G, hGs, fun q₁ q₂ hq₁ hq₂ => hGp q₁ q₂ (hsub hq₁) (hsub hq₂)⟩
  have h3' : ∀ q : N, (q : V) ∈ Metric.ball (Bridge.incl hN p) r → Morse.IsNormalRadius hN q ε :=
    fun q hq => h3 q (hsub hq)
  have hU := Emb.isUniformNormal_of (hN := hN) h1' h2' h3'
  refine ⟨_, Metric.isOpen_ball.preimage continuous_subtype_val, Metric.mem_ball_self hrpos, ε,
    hε, hU, fun q₁ hq₁ q₂ hq₂ γ hγ t ht => ?_⟩
  -- the minimal geodesic of the good ball
  have hy : Bridge.incl hN q₁ ∈ N ∩ Metric.ball (Bridge.incl hN p) r := ⟨q₁.2, hq₁⟩
  have hz : Bridge.incl hN q₂ ∈ N ∩ Metric.ball (Bridge.incl hN p) r := ⟨q₂.2, hq₂⟩
  obtain ⟨η, hη, hgeo, -⟩ := hG.isGeodesicOn_minGeo hy hz
  have hfrom : Morse.IsGeodesicFrom hN (Morse.minGeo hN (Bridge.incl hN q₁) (Bridge.incl hN q₂)) (Bridge.incl hN q₁)
      (Morse.minJoin hN (Bridge.incl hN q₁) (Bridge.incl hN q₂)) :=
    ⟨η, hη, hgeo, Morse.minGeo_zero hN q₁.2 _, (Morse.hasDerivAt_minGeo_zero hN q₁.2 _).deriv⟩
  have hlen : ‖Morse.minJoin hN (Bridge.incl hN q₁) (Bridge.incl hN q₂)‖ < ε := by
    have hρ := Emb.riemDist_le_arcLen hγ.1
    rw [hγ.2.1, hγ.2.2.1] at hρ
    have hρ' : Morse.riemDist (N := N) (Bridge.incl hN q₁) (Bridge.incl hN q₂) = ENNReal.ofReal ‖Morse.minJoin hN (Bridge.incl hN q₁) (Bridge.incl hN q₂)‖ :=
      (hG.join hy hz).2.2.1
    have hρ'' : ENNReal.ofReal ‖Morse.minJoin hN (Bridge.incl hN q₁) (Bridge.incl hN q₂)‖ ≤ ENNReal.ofReal (arcLen (n := n) γ 0 1) := by
      rw [← hρ']; exact hρ
    have hl : 0 ≤ arcLen (n := n) γ 0 1 := Bridge.arcLen_nonneg zero_le_one
    exact ((ENNReal.ofReal_le_ofReal_iff hl).1 hρ'').trans_lt hγ.2.2.2
  obtain ⟨γ₀, hγ₀, heq⟩ := Emb.exists_joinsShort_of_isGeodesicFrom
    (Morse.minJoin_mem_tangentSubspace q₁.2 _) hfrom hlen (hG.minGeo_one hy hz)
  have huniq := hU.1 q₁ hq₁ q₂ hq₂
  obtain ⟨γ₁, hγ₁, hγ₁u⟩ := huniq
  have e : γ t = γ₀ t := ((hγ₁u γ hγ).symm.trans (hγ₁u γ₀ hγ₀)) ht
  show Bridge.incl hN (γ t) ∈ Metric.ball (Bridge.incl hN p) r
  rw [e, heq t ht]
  exact (hG.convex _ hy _ hz t ht).2

#rt_check RoundTrip.«V7_10′».A_to_B_emb [Morse.exists_isGoodBall_ball, Morse.exists_lebesgue_goodBall]

end RoundTrip.«V7_10′»
