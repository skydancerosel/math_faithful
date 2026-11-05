import Morse
import RoundTrip.Check
import RoundTrip.Blind.V7_14
import RoundTrip.Bridge

open Set Filter Topology
open scoped ContDiff Manifold RealInnerProductSpace

namespace RoundTrip.V7_14

/-- The project's statement (universes instantiated at 0; `ballSet nc s = U ∩ G⁻¹(ball 0 s)` and
`closedBallSet nc s = F(closedBall 0 s ∩ T_qN)` are definitions), for a slice submanifold `N ⊆ V`
with the induced metric and a normal radius `ε` at `q` (`Morse.NormalCoord`): closed normal balls
of radius `s < ε` are compact; and (paths leaving the normal ball) an admissible path `c` in `N`
on `[a, b]` from `q` to a point outside the normal ball of radius `s`, `0 < s < ε`, has times
`a ≤ t₁ < t₂ ≤ b` with `c(t₁) = q`, `c` in `U − {q}` on `(t₁, t₂]`, `‖G(c(t₂))‖ = s`,
`‖G(c(t))‖ < s` on `[t₁, t₂)`, and `L(c|[t₁, t₂]) ≥ s`. -/
def A : Prop :=
  type_of% @Morse.NormalCoord.isCompact_closedBallSet.{0,0,0} ∧
    type_of% @Morse.NormalCoord.exists_crossing.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.NormalCoord.isCompact_closedBallSet, @Morse.NormalCoord.exists_crossing⟩

/-! Neither `A → B` nor `B → A` is proved; see `V7_14.json`. B quantifies over abstract connected
Hausdorff `ℝⁿ`-manifolds with an arbitrary smooth Mathlib `RiemannianBundle` metric and an
arbitrary Levi-Civita `CovariantDerivative`, while A only concerns slice submanifolds `N ⊆ V` with
the induced metric; conversely A's compactness of closed normal balls and its specific crossing
segment (last visit of `q` to first exit) are not consequences of B.

## The embedded special case

B is specialized to `M = ↥N` (`RoundTrip.Bridge.Sub hN`) with the induced metric and the induced
Levi-Civita connection `Bridge.conn` (`B_emb`). The `Emb` section repeats the normal-ball
dictionary of `Items/V7_13.lean` (Items files do not import each other) and adds the affine
reparametrization of paths to `[0, 1]`. On embedded manifolds B is exactly A's crossing lemma for
piecewise smooth paths on connected `N` (`B_emb_iff_A_pw`). -/

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

/-- **Smooth extension from a compact set**, vector-valued (the proof of the project's real-valued
`Morse.exists_contDiff_eq_of_locally`, with values in `F`). -/
theorem exists_contDiff_eq_of_locally' {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {K S : Set E}
    (hK : IsCompact K) (hKS : K ⊆ S) {f : E → F}
    (hloc : ∀ x ∈ K, ∃ O : Set E, IsOpen O ∧ x ∈ O ∧ ∃ G : E → F,
      ContDiffOn ℝ ∞ G O ∧ ∀ y ∈ S ∩ O, f y = G y) :
    ∃ F' : E → F, ContDiff ℝ ∞ F' ∧ ∀ y ∈ K, F' y = f y := by
  classical
  choose! O hO hxO G hG hfG using hloc
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => O x) (fun x => hO x x.2)
    fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxO x hx⟩
  obtain ⟨φ, hφ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E) hK.isClosed
    (fun i : t => O (i : K)) (fun i => hO _ (i : K).2) fun x hx => by
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (ht hx)
      exact mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩
  have hφs : ∀ i : t, ContDiff ℝ ∞ (φ i) := fun i =>
    contMDiff_iff_contDiff.1 (φ i).contMDiff
  refine ⟨fun x => ∑ i : t, φ i x • G (i : K) x, ?_, fun y hy => ?_⟩
  · exact ContDiff.sum fun i _ => Morse.contDiff_smul_of_tsupport (hO _ (i : K).2) (hφs i)
      (hG _ (i : K).2) (hφ i)
  · have hsum := φ.sum_eq_one hy
    rw [finsum_eq_sum_of_fintype] at hsum
    have hterm : ∀ i : t, φ i y • G (i : K) y = φ i y • f y := by
      intro i
      by_cases h0 : φ i y = 0
      · simp [h0]
      · have hyO : y ∈ O (i : K) := hφ i (subset_tsupport _ h0)
        rw [hfG _ (i : K).2 y ⟨hKS hy, hyO⟩]
    simp only [hterm, ← Finset.sum_smul, hsum, one_smul]

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- B's Riemannian norm of `T_qN` is the ambient norm of `D_q w`. -/
theorem nrm_eq (q : Sub hN) (w : Rn n) : nrm (n := n) q w = ‖D hN q w‖ := norm_eq q w

theorem mem_tball_iff {q : Sub hN} {ε : ℝ} {w : Rn n} :
    w ∈ tball (n := n) q ε ↔ ‖D hN q w‖ < ε := by
  show nrm (n := n) q w < ε ↔ _
  rw [nrm_eq]

theorem tball_eq (q : Sub hN) (ε : ℝ) : tball (n := n) q ε = {w | ‖D hN q w‖ < ε} := by
  ext w; exact mem_tball_iff

theorem isOpen_tball (q : Sub hN) (ε : ℝ) : IsOpen (tball (n := n) q ε) := by
  rw [tball_eq]; exact isOpen_lt (D hN q).continuous.norm continuous_const

theorem norm_D_L {q : Sub hN} {v : V} (hv : v ∈ Morse.tangentSubspace hN q) :
    ‖D hN q (L hN q v)‖ = ‖v‖ := by rw [D_L hv]

/-- A blind `exp_q(w)` (a geodesic of the induced connection on the closed `[0, 1]`) is in the
project's `expDom` (a geodesic on an open interval containing `[0, 1]`), via
`Morse.exists_initial_ray`. -/
theorem mem_expDom_of_expDefined {q : Sub hN} {w : Rn n}
    (h : ExpDefined (conn (hN := hN)) q w) : (incl hN q, D hN q w) ∈ Morse.expDom hN := by
  obtain ⟨γ, hγ, hinit⟩ := h
  have hγ' : RoundTrip.BridgePrelude.IsGeodesic (conn (hN := hN)) γ (Icc 0 1) := hγ
  obtain ⟨-, hcd, -⟩ := isGeodesic_iff.1 hγ'
  have hc : Morse.IsSmoothCurveIn hN (incl hN ∘ γ) := ⟨hcd, fun t _ => (γ t).2⟩
  obtain ⟨η, hη, hray, heq⟩ := Morse.exists_initial_ray (hN := hN) hc (isGeodesicOn_Ioo hγ')
  set g : ℝ → V := fun t => Morse.exp hN ((incl hN ∘ γ) 0)
    (t • Morse.velAlong (incl hN ∘ γ) 0) with hg
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h0J : (0 : ℝ) ∈ Ioo (-η) (1 + η) := ⟨by linarith, by linarith⟩
  have hγ0 : γ 0 = q := hinit.1
  have hinit' : RoundTrip.BridgePrelude.InitData (n := n) γ (Icc 0 1) q w := hinit
  have hD := (initData_iff hγ0).1 hinit'
  have hderiv : deriv g 0 = D hN q w := by
    have h1 : HasDerivWithinAt (incl hN ∘ γ) (deriv g 0) (Icc 0 1) 0 :=
      (hray.hasDerivAt h0J).hasDerivWithinAt.congr (fun t ht => (heq t ht).symm)
        (heq 0 h0I).symm
    rw [← hD, D_vel (isSmoothCurve_iff.2 hcd) (uniqueDiffOn_Icc zero_lt_one) h0I]
    exact (uniqueDiffOn_Icc zero_lt_one 0 h0I).eq_deriv _ h1
      (h1.differentiableWithinAt.hasDerivWithinAt)
  refine ⟨g, η, hη, hray, ?_, hderiv⟩
  show g 0 = incl hN q
  refine (heq 0 h0I).trans ?_
  show incl hN (γ 0) = incl hN q
  rw [hγ0]

/-- Blind `exp` agrees with the project's `exp` wherever the blind one is defined. -/
theorem incl_expMap {q : Sub hN} {w : Rn n} (h : ExpDefined (conn (hN := hN)) q w) :
    incl hN (expMap (conn (hN := hN)) q w) = Morse.exp hN (Subtype.val (q : ↥N)) (D hN q w) := by
  have := expMap_eq (mem_expDom_of_expDefined h)
  exact this

/-- **Dictionary: normal balls (project ⇒ blind).** A project normal radius `ε` at `q`
(`NormalCoord`) makes `N ∩ U` a blind normal ball of radius `ε` of the induced connection. -/
theorem isNormBall_of_normalCoord {q : Sub hN} {ε : ℝ} (nc : Morse.NormalCoord hN q ε) :
    IsNormBall (conn (hN := hN)) q ε {x : Sub hN | incl hN x ∈ nc.U} := by
  have hexp : ∀ w ∈ tball (n := n) q ε, ExpDefined (conn (hN := hN)) q w := fun w hw =>
    expDefined_of_mem_expDom (nc.mem_expDom _ (D_mem q w) (mem_tball_iff.1 hw))
  have hval : ∀ w ∈ tball (n := n) q ε,
      incl hN (expMap (conn (hN := hN)) q w) = nc.F (D hN q w) := fun w hw => by
    rw [incl_expMap (hexp w hw), nc.F_eq _ (D_mem q w) (mem_tball_iff.1 hw)]
  refine ⟨nc.isOpen_U.preimage continuous_subtype_val, hexp, ?_, ?_, ?_, ?_⟩
  · intro w hw w' hw' h
    have h1 := congrArg (incl hN) h
    simp only at h1
    rw [incl_expMap (hexp w hw), incl_expMap (hexp w' hw')] at h1
    have h2 := congrArg nc.G h1
    rw [nc.G_exp _ (D_mem q w) (mem_tball_iff.1 hw),
      nc.G_exp _ (D_mem q w') (mem_tball_iff.1 hw')] at h2
    exact D_injective q h2
  · ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      show incl hN (expMap _ q w) ∈ nc.U
      rw [incl_expMap (hexp w hw)]
      exact nc.exp_mem_U _ (D_mem q w) (mem_tball_iff.1 hw)
    · intro hx
      have hxU : incl hN x ∈ nc.U := hx
      have hxN : incl hN x ∈ N := x.2
      have hw : L hN q (nc.G (incl hN x)) ∈ tball (n := n) q ε := by
        rw [mem_tball_iff, D_L (nc.G_mem _ hxU hxN)]; exact nc.norm_G_lt _ hxU hxN
      refine ⟨_, hw, ?_⟩
      apply Subtype.ext
      show incl hN (expMap _ q _) = incl hN x
      rw [incl_expMap (hexp _ hw), D_L (nc.G_mem _ hxU hxN)]
      exact nc.exp_G _ hxU hxN
  · intro w hw
    have hO : D hN q w ∈ nc.O := nc.mem_O _ (D_mem q w) (mem_tball_iff.1 hw)
    have hF : ContDiffAt ℝ ∞ (fun w => nc.F (D hN q w)) w :=
      (nc.contDiffOn_F.contDiffAt (nc.isOpen_O.mem_nhds hO)).comp w
        (D hN q).contDiff.contDiffAt
    set g' : Rn n → Sub hN := fun w => expMap (conn (hN := hN)) q w with hg'
    have hc : ContMDiffAt 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) ∞ g' w :=
      Morse.contMDiffAt_of_val_eventuallyEq hN (g := g') hF (by
        filter_upwards [(isOpen_tball q ε).mem_nhds hw] with w' hw'
        exact hval w' hw')
    exact hc.contMDiffWithinAt
  · refine ⟨fun x => L hN q (nc.G (incl hN x)), ?_, ?_⟩
    · intro x hx
      have h1 : ContMDiffAt 𝓘(ℝ, Rn n) 𝓘(ℝ, V) ∞ (fun x : Sub hN => nc.G (incl hN x)) x :=
        (nc.contDiffOn_G.contDiffAt (nc.isOpen_U.mem_nhds hx)).contMDiffAt.comp x
          (contMDiff_incl x)
      exact ((L hN q).contDiff.contMDiff.contMDiffAt.comp x h1).contMDiffWithinAt
    · intro w hw
      show L hN q (nc.G (incl hN (expMap _ q w))) = w
      rw [incl_expMap (hexp w hw), nc.G_exp _ (D_mem q w) (mem_tball_iff.1 hw), L_D]

/-! ### Blind normal balls give project normal radii -/

theorem incl_eq (x : Sub hN) : incl hN x = Subtype.val (x : ↥N) := rfl

open Classical in
/-- A point of `V`, read in `N` (junk value `q₀` off `N`). -/
noncomputable def liftV (q₀ : Sub hN) (y : V) : Sub hN := if h : y ∈ N then (⟨y, h⟩ : N) else q₀

theorem liftV_of_mem (q₀ : Sub hN) {y : V} (h : y ∈ N) : liftV q₀ y = (⟨y, h⟩ : N) := by
  unfold liftV; exact dif_pos h

theorem incl_liftV (q₀ : Sub hN) {y : V} (h : y ∈ N) : incl hN (liftV q₀ y) = y := by
  rw [liftV_of_mem q₀ h]; rfl

theorem liftV_incl (q₀ x : Sub hN) : liftV q₀ (incl hN x) = x := liftV_of_mem q₀ x.2

theorem isInducing_incl : Topology.IsInducing (incl hN) := Topology.IsInducing.subtypeVal

/-- **Local smooth extension** (slice charts): a function on `N`, smooth on an open `U ⊆ N`, is near
each point of `U` the restriction of a function smooth on an open set of `V`. -/
theorem exists_local_extension {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set (Sub hN)} (hU : IsOpen U) {h : Sub hN → E}
    (hh : ContMDiffOn 𝓘(ℝ, Rn n) 𝓘(ℝ, E) ∞ h U) {x : Sub hN} (hx : x ∈ U) :
    ∃ O : Set V, IsOpen O ∧ incl hN x ∈ O ∧ ∃ G : V → E, ContDiffOn ℝ ∞ G O ∧
      ∀ y (hy : y ∈ N), y ∈ O → G y = h ⟨y, hy⟩ := by
  set σ := Morse.sliceAt hN x
  obtain ⟨Ut, hUt, hUeq⟩ := isInducing_incl.isOpen_iff.1 hU
  have hmem : (x : N).1 ∈ σ.φ.source := Morse.mem_sliceAt_source hN x
  set T := σ.toChart.target
  set φ1 : V → Rn n := fun y => (σ.φ y).1 with hφ1
  set Fr : V → V := fun y => Morse.sliceParam σ (φ1 y) with hFr
  have hφs := Milnor.Problems.sliceChart_contDiffOn σ
  have hφ1s : ContDiffOn ℝ ∞ φ1 σ.φ.source := contDiff_fst.comp_contDiffOn hφs
  set O₁ := σ.φ.source ∩ φ1 ⁻¹' T with hO₁
  have hO₁ : IsOpen O₁ :=
    hφ1s.continuousOn.isOpen_inter_preimage σ.φ.open_source (Morse.isOpen_toChart_target σ)
  have hFrs : ContDiffOn ℝ ∞ Fr O₁ :=
    (Morse.contDiffOn_sliceParam σ).comp (hφ1s.mono inter_subset_left) fun y hy => hy.2
  have hFrN : ∀ y ∈ O₁, Fr y ∈ N := fun y hy => Morse.sliceParam_mem σ hy.2
  set O := O₁ ∩ Fr ⁻¹' Ut with hO
  have hOo : IsOpen O := hFrs.continuousOn.isOpen_inter_preimage hO₁ hUt
  have hFr_self : ∀ y (hy : y ∈ N), y ∈ σ.φ.source → Fr y = y := fun y hy hs =>
    Morse.sliceParam_toChart σ (q := ⟨y, hy⟩) hs
  have hxO₁ : incl hN x ∈ O₁ := ⟨hmem, Morse.toChart_apply_mem_target σ hmem⟩
  refine ⟨O, hOo, ⟨hxO₁, ?_⟩, fun y => h (liftV x (Fr y)), ?_, ?_⟩
  · show Fr (incl hN x) ∈ Ut
    rw [show Fr (incl hN x) = incl hN x from hFr_self _ x.2 hmem]
    have : x ∈ incl hN ⁻¹' Ut := hUeq.symm ▸ hx
    exact this
  · intro y hy
    have hFa : ContDiffAt ℝ ∞ Fr y := hFrs.contDiffAt (hO₁.mem_nhds hy.1)
    set r : V → Sub hN := fun y => liftV x (Fr y) with hr
    have hrc : ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ, Rn n) ∞ r y :=
      Morse.contMDiffAt_of_val_eventuallyEq hN (g := r) hFa (by
        filter_upwards [hO₁.mem_nhds hy.1] with y' hy'
        exact incl_liftV x (hFrN y' hy'))
    have hry : r y ∈ U := by
      rw [← hUeq]
      show incl hN (liftV x (Fr y)) ∈ Ut
      rw [incl_liftV x (hFrN y hy.1)]
      exact hy.2
    have hhc : ContMDiffAt 𝓘(ℝ, Rn n) 𝓘(ℝ, E) ∞ h (r y) := hh.contMDiffAt (hU.mem_nhds hry)
    exact (contMDiffAt_iff_contDiffAt.1 (hhc.comp y hrc)).contDiffWithinAt
  · intro y hy hyO
    show h (liftV x (Fr y)) = h ⟨y, hy⟩
    rw [hFr_self y hy hyO.1.1, liftV_of_mem x hy]

/-- **Dictionary: normal balls (blind ⇒ project).** If `exp_q` maps the Riemannian `ε`-ball of
`T_qN` diffeomorphically onto an open `U ⊆ N` (blind `IsNormBall` of the induced connection), then
every `ε' ∈ (0, ε)` is a project normal radius at `q`. -/
theorem normalCoord_of_isNormBall {q : Sub hN} {ε : ℝ} {U : Set (Sub hN)}
    (hB : IsNormBall (conn (hN := hN)) q ε U) {ε' : ℝ} (hε' : 0 < ε') (hεε' : ε' < ε) :
    Nonempty (Morse.NormalCoord hN q ε') := by
  obtain ⟨hUo, hexp, -, himg, hsmooth, g, hg, hgexp⟩ := hB
  set E : Rn n → Sub hN := fun w => expMap (conn (hN := hN)) q w with hE
  set ε'' := (ε' + ε) / 2 with hε''
  have hε''lt : ε'' < ε := by rw [hε'']; linarith
  have hε'ε'' : ε' < ε'' := by rw [hε'']; linarith
  set T := Morse.tangentSubspace hN q
  -- basic facts
  have hEU : ∀ w ∈ tball (n := n) q ε, E w ∈ U := fun w hw => himg ▸ mem_image_of_mem _ hw
  have hEincl : ∀ w ∈ tball (n := n) q ε, incl hN (E w) = Morse.exp hN (Subtype.val (q : ↥N)) (D hN q w) :=
    fun w hw => incl_expMap (hexp w hw)
  have hUE : ∀ z ∈ U, E (g z) = z ∧ g z ∈ tball (n := n) q ε := by
    intro z hz
    rw [← himg] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact ⟨by rw [hgexp w hw], by rw [hgexp w hw]; exact hw⟩
  have hLt : ∀ v ∈ T, ‖v‖ < ε → L hN q v ∈ tball (n := n) q ε := fun v hv hvε => by
    rw [mem_tball_iff, D_L hv]; exact hvε
  -- the compact set `K = exp_q(closedBall ε'')`
  set Kw : Set (Rn n) := L hN q '' (Metric.closedBall (0 : V) ε'' ∩ (T : Set V)) with hKw
  have hKwc : IsCompact Kw :=
    ((isCompact_closedBall (0 : V) ε'').inter_right (Submodule.closed_of_finiteDimensional _)).image
      (L hN q).continuous
  have hKw_sub : Kw ⊆ tball (n := n) q ε := by
    rintro _ ⟨v, ⟨hv, hvT⟩, rfl⟩
    refine hLt v hvT (lt_of_le_of_lt ?_ hε''lt)
    simpa using hv
  set K : Set V := incl hN '' (E '' Kw) with hK
  have hKc : IsCompact K :=
    (hKwc.image_of_continuousOn (hsmooth.continuousOn.mono hKw_sub)).image contMDiff_incl.continuous
  -- the function to extend
  set f : V → V := fun y => D hN q (g (liftV q y)) with hf
  have hKS : K ⊆ incl hN '' U := by
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact mem_image_of_mem _ (hEU w (hKw_sub hw))
  have hhs : ContMDiffOn 𝓘(ℝ, Rn n) 𝓘(ℝ, V) ∞ (fun z => D hN q (g z)) U :=
    (D hN q).contDiff.contMDiff.comp_contMDiffOn hg
  have hloc : ∀ x ∈ K, ∃ O : Set V, IsOpen O ∧ x ∈ O ∧ ∃ G : V → V,
      ContDiffOn ℝ ∞ G O ∧ ∀ y ∈ incl hN '' U ∩ O, f y = G y := by
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    obtain ⟨O, hO, hxO, G, hG, hGeq⟩ := exists_local_extension hUo hhs (hEU w (hKw_sub hw))
    refine ⟨O, hO, hxO, G, hG, ?_⟩
    rintro y ⟨⟨z, -, rfl⟩, hyO⟩
    rw [incl_eq] at hyO ⊢
    rw [hGeq _ z.2 hyO]
    show D hN q (g (liftV q (incl hN z))) = _
    rw [liftV_incl]
    rfl
  obtain ⟨Gx, hGx, hGxK⟩ := exists_contDiff_eq_of_locally' hKc hKS hloc
  -- the open set `U'` of `V`
  set U'N : Set (Sub hN) := U ∩ {z | ‖D hN q (g z)‖ < ε'} with hU'N
  have hU'No : IsOpen U'N :=
    ((D hN q).continuous.norm.comp_continuousOn hg.continuousOn).isOpen_inter_preimage hUo
      isOpen_Iio
  obtain ⟨U', hU'o, hU'eq⟩ := isInducing_incl.isOpen_iff.1 hU'No
  -- points of `U' ∩ N`
  have hpt : ∀ y ∈ U', ∀ hy : y ∈ N, ∃ w ∈ tball (n := n) q ε,
      E w = (⟨y, hy⟩ : N) ∧ ‖D hN q w‖ < ε' ∧ Gx y = D hN q w := by
    intro y hyU hy
    have hz : ((⟨y, hy⟩ : N) : Sub hN) ∈ U'N := by rw [← hU'eq]; exact hyU
    obtain ⟨hzE, hzt⟩ := hUE _ hz.1
    refine ⟨g ⟨y, hy⟩, hzt, hzE, hz.2, ?_⟩
    have hyK : y ∈ K := by
      refine ⟨E (g ⟨y, hy⟩), ⟨g ⟨y, hy⟩, ⟨D hN q (g ⟨y, hy⟩), ⟨?_, D_mem _ _⟩, L_D _ _⟩, rfl⟩, ?_⟩
      · simpa using hz.2.le.trans hε'ε''.le
      · rw [hzE]; rfl
    rw [hGxK y hyK]
    show D hN q (g (liftV q y)) = _
    rw [liftV_of_mem q hy]
  refine ⟨{
    O := {v : V | ‖D hN q (L hN q v)‖ < ε}
    U := U'
    F := fun v => incl hN (E (L hN q v))
    G := Gx
    pos := hε'
    isOpen_O := isOpen_lt ((D hN q).continuous.comp (L hN q).continuous).norm continuous_const
    isOpen_U := hU'o
    contDiffOn_F := ?_
    contDiffOn_G := hGx.contDiffOn
    mem_expDom := ?_
    mem_O := ?_
    F_eq := ?_
    exp_mem_U := ?_
    G_exp := ?_
    G_mem := ?_
    norm_G_lt := ?_
    exp_G := ?_ }⟩
  · rw [← contMDiffOn_iff_contDiffOn]
    refine contMDiff_incl.comp_contMDiffOn (hsmooth.comp (L hN q).contDiff.contMDiff.contMDiffOn ?_)
    intro v hv
    exact mem_tball_iff.2 hv
  · intro v hv hvε
    have := mem_expDom_of_expDefined (hexp _ (hLt v hv (hvε.trans hεε')))
    rwa [D_L hv] at this
  · intro v hv hvε
    show ‖D hN q (L hN q v)‖ < ε
    rw [D_L hv]; exact hvε.trans hεε'
  · intro v hv hvε
    show incl hN (E (L hN q v)) = _
    rw [hEincl _ (hLt v hv (hvε.trans hεε')), D_L hv]
  · intro v hv hvε
    have hw := hLt v hv (hvε.trans hεε')
    rw [← D_L hv, ← hEincl _ hw]
    have : E (L hN q v) ∈ U'N := by
      refine ⟨hEU _ hw, ?_⟩
      show ‖D hN q (g (E (L hN q v)))‖ < ε'
      rw [hgexp _ hw, D_L hv]; exact hvε
    rw [← hU'eq] at this
    exact this
  · intro v hv hvε
    have hw := hLt v hv (hvε.trans hεε')
    have hvK : Morse.exp hN (Subtype.val (q : ↥N)) v ∈ K := by
      refine ⟨E (L hN q v), ⟨L hN q v, ⟨v, ⟨?_, hv⟩, rfl⟩, rfl⟩, ?_⟩
      · simpa using hvε.le.trans hε'ε''.le
      · rw [hEincl _ hw, D_L hv]
    rw [hGxK _ hvK]
    show D hN q (g (liftV q (Morse.exp hN (Subtype.val (q : ↥N)) v))) = v
    rw [← D_L hv, ← hEincl _ hw, liftV_incl, hgexp _ hw]
  · intro y hyU hy
    obtain ⟨w, -, -, -, hGy⟩ := hpt y hyU hy
    rw [hGy]; exact D_mem _ _
  · intro y hyU hy
    obtain ⟨w, -, -, hw', hGy⟩ := hpt y hyU hy
    rw [hGy]; exact hw'
  · intro y hyU hy
    obtain ⟨w, hw, hEw, -, hGy⟩ := hpt y hyU hy
    rw [hGy, ← hEincl w hw, hEw]
    rfl

/-- A blind geodesic `γ` of the induced connection on `[0, 1]` is the radial geodesic
`t ↦ exp_{γ(0)}(t v)` on `[0, 1]`, `v = D(γ'(0)) ∈ T_{γ(0)}N`, and its length is `‖v‖`
(`Morse.exists_initial_ray`, `Morse.IsGeodesicOn.pathLength_eq`). -/
theorem geodesic_data {γ : ℝ → Sub hN} (hγ : IsGeodesic (conn (hN := hN)) γ (Icc 0 1)) :
    ∃ v ∈ Morse.tangentSubspace hN (γ 0),
      (∀ t ∈ Icc (0 : ℝ) 1, incl hN (γ t) = Morse.exp hN (incl hN (γ 0)) (t • v)) ∧
      arcLen (n := n) γ 0 1 = ‖v‖ ∧ D hN (γ 0) (vel (n := n) γ (Icc 0 1) 0) = v := by
  have hγ' : RoundTrip.BridgePrelude.IsGeodesic (conn (hN := hN)) γ (Icc 0 1) := hγ
  obtain ⟨-, hcd, -⟩ := isGeodesic_iff.1 hγ'
  have hc : Morse.IsSmoothCurveIn hN (incl hN ∘ γ) := ⟨hcd, fun t _ => (γ t).2⟩
  obtain ⟨η, hη, hray, heq⟩ := Morse.exists_initial_ray (hN := hN) hc (isGeodesicOn_Ioo hγ')
  set v := Morse.velAlong (incl hN ∘ γ) 0 with hv
  set g : ℝ → V := fun t => Morse.exp hN ((incl hN ∘ γ) 0) (t • v) with hg
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h0J : (0 : ℝ) ∈ Ioo (-η) (1 + η) := ⟨by linarith, by linarith⟩
  have hvD : D hN (γ 0) (vel (n := n) γ (Icc 0 1) 0) = v :=
    D_vel (isSmoothCurve_iff.2 hcd) (uniqueDiffOn_Icc zero_lt_one) h0I
  have hderiv : deriv g 0 = v := by
    have h1 : HasDerivWithinAt (incl hN ∘ γ) (deriv g 0) (Icc 0 1) 0 :=
      (hray.hasDerivAt h0J).hasDerivWithinAt.congr (fun t ht => (heq t ht).symm)
        (heq 0 h0I).symm
    exact (uniqueDiffOn_Icc zero_lt_one 0 h0I).eq_deriv _ h1
      (h1.differentiableWithinAt.hasDerivWithinAt)
  refine ⟨v, hvD ▸ D_mem _ _, fun t ht => (heq t ht).symm, ?_, hvD⟩
  have hEq : EqOn (incl hN ∘ γ) g (Icc 0 1) := fun t ht => (heq t ht).symm
  rw [show arcLen (n := n) γ 0 1 = RoundTrip.BridgePrelude.arcLen (n := n) γ 0 1 from rfl,
    arcLen_eq, pathLength_congr zero_le_one hEq,
    hray.pathLength_eq isPreconnected_Ioo zero_le_one
      (Icc_subset_Ioo (by linarith) (by linarith)) h0J, hderiv]
  ring

/-- A blind piecewise smooth path, read in `V`. -/
theorem path_data {pth : ℝ → Sub hN} {a b : ℝ} (hpw : IsPW (n := n) pth a b) :
    Morse.IsPiecewiseSmooth (incl hN ∘ pth) a b ∧ (∀ t ∈ Icc a b, (incl hN ∘ pth) t ∈ N) ∧
      arcLen (n := n) pth a b = Morse.pathLength (incl hN ∘ pth) a b :=
  ⟨isPiecewiseSmooth_of_isPW hpw, fun t _ => (pth t).2, arcLen_eq pth a b⟩

/-- Images of paths in `N` are determined by their images in `V`. -/
theorem image_eq_of_incl {f g : ℝ → Sub hN} {s s' : Set ℝ}
    (h : (incl hN ∘ f) '' s = (incl hN ∘ g) '' s') : f '' s = g '' s' := by
  have hinj : Function.Injective (incl hN) := fun x y hxy => Subtype.ext hxy
  apply Set.image_injective.2 hinj
  rw [Set.image_image, Set.image_image]
  exact h

/-- A point of `N ∩ U` in a project normal ball is the blind `exp_q` of `L_q(G(y))`, whose
Riemannian norm is `‖G(y)‖`. -/
theorem eq_expMap_G {q : Sub hN} {ε ε' : ℝ} {U : Set (Sub hN)}
    (hB : IsNormBall (conn (hN := hN)) q ε U) (hεε' : ε' ≤ ε) (nc : Morse.NormalCoord hN q ε')
    {x : Sub hN} (hx : incl hN x ∈ nc.U) :
    x = expMap (conn (hN := hN)) q (L hN q (nc.G (incl hN x))) ∧
      nrm (n := n) q (L hN q (nc.G (incl hN x))) = ‖nc.G (incl hN x)‖ := by
  have hT := nc.G_mem _ hx x.2
  have hlt := nc.norm_G_lt _ hx x.2
  have hnrm : nrm (n := n) q (L hN q (nc.G (incl hN x))) = ‖nc.G (incl hN x)‖ := by
    rw [nrm_eq, D_L hT]
  refine ⟨?_, hnrm⟩
  have hball : L hN q (nc.G (incl hN x)) ∈ tball (n := n) q ε := by
    show nrm (n := n) q _ < ε
    rw [hnrm]; exact hlt.trans_le hεε'
  apply Subtype.ext
  show incl hN x = incl hN (expMap _ q _)
  rw [incl_expMap (hB.2.1 _ hball), D_L hT]
  exact (nc.exp_G _ hx x.2).symm

/-! ### Affine reparametrization of paths to `[0, 1]` -/

/-- A piecewise smooth path on `[a, b]`, `a < b`, read on `[0, 1]`. -/
theorem isPiecewiseSmooth_reparam {c : ℝ → V} {a b : ℝ} (hab : a < b)
    (hc : Morse.IsPiecewiseSmooth c a b) :
    Morse.IsPiecewiseSmooth (fun t => c ((b - a) * t + a)) 0 1 := by
  obtain ⟨-, hcont, B, hB⟩ := hc
  have hk : 0 < b - a := sub_pos.2 hab
  have hmaps : ∀ x ∈ Icc (0 : ℝ) 1, (b - a) * x + a ∈ Icc a b := fun x hx =>
    ⟨by nlinarith [hx.1], by nlinarith [hx.2]⟩
  refine ⟨zero_le_one, hcont.comp ((continuous_const.mul continuous_id).add
    continuous_const).continuousOn hmaps, B.image (fun x => (x - a) / (b - a)),
    fun s t hs hst ht hB' => ?_⟩
  have hc := hB ((b - a) * s + a) ((b - a) * t + a) (by nlinarith) (by nlinarith) (by nlinarith)
    fun x hx hx' => hB' ((x - a) / (b - a)) (Finset.mem_image.2 ⟨x, hx, rfl⟩)
      ⟨by rw [lt_div_iff₀ hk]; linarith [hx'.1], by rw [div_lt_iff₀ hk]; linarith [hx'.2]⟩
  exact hc.comp ((contDiff_const.mul contDiff_id).add contDiff_const).contDiffOn
    fun x hx => ⟨by nlinarith [hx.1], by nlinarith [hx.2]⟩

theorem pathLength_reparam (c : ℝ → V) {a b : ℝ} (hab : a < b) :
    Morse.pathLength (fun t => c ((b - a) * t + a)) 0 1 = Morse.pathLength c a b := by
  have hk : 0 < b - a := sub_pos.2 hab
  have hd : ∀ t, deriv (fun t => c ((b - a) * t + a)) t = (b - a) • deriv c ((b - a) * t + a) :=
    fun t => by
      have h1 := deriv_comp_mul_left (b - a) (fun s => c (s + a)) t
      have h2 := deriv_comp_add_const (f := c) (a := a) (x := (b - a) * t)
      exact h1.trans (by rw [h2])
  simp only [Morse.pathLength, hd, norm_smul, Real.norm_eq_abs, abs_of_pos hk]
  rw [intervalIntegral.integral_const_mul]
  have := intervalIntegral.smul_integral_comp_mul_add (a := 0) (b := 1)
    (fun x => ‖deriv c x‖) (b - a) a
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one, sub_add_cancel] at this
  exact this

theorem image_reparam (c : ℝ → V) {a b : ℝ} (hab : a < b) :
    (fun t => c ((b - a) * t + a)) '' Icc 0 1 = c '' Icc a b := by
  have hk : 0 < b - a := sub_pos.2 hab
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨(b - a) * t + a, ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(x - a) / (b - a), ⟨div_nonneg (by linarith [hx.1]) hk.le,
      (div_le_one hk).2 (by linarith [hx.2])⟩, ?_⟩
    simp only
    rw [mul_div_cancel₀ _ hk.ne', sub_add_cancel]

end Emb

open Emb in
/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`) with the induced metric and the induced
Levi-Civita connection (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
    ∀ (q : Bridge.Sub hN) (ε : ℝ) (U : Set (Bridge.Sub hN)), 0 < ε →
      IsNormBall (Bridge.conn (hN := hN)) q ε U →
    ∀ r : ℝ, 0 < r → r < ε → ∀ pth : ℝ → Bridge.Sub hN, IsPW (n := n) pth 0 1 → pth 0 = q →
      pth 1 ∈ shell (Bridge.conn (hN := hN)) q r →
      (∀ δ : ℝ, 0 < δ → δ < r → ∃ a' b' : ℝ, 0 ≤ a' ∧ a' ≤ b' ∧ b' ≤ 1 ∧
          pth a' ∈ shell (Bridge.conn (hN := hN)) q δ ∧ pth b' ∈ shell (Bridge.conn (hN := hN)) q r ∧
          (∀ t ∈ Set.Icc a' b', pth t ∈ between (Bridge.conn (hN := hN)) q δ r) ∧
          r - δ ≤ arcLen (n := n) pth a' b') ∧
      r ≤ arcLen (n := n) pth 0 1

/-- `B_emb` is a special case of B (the induced connection is Levi-Civita, `Bridge.conn_isLC`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- The part of A that B covers: the project's crossing lemma `exists_crossing` for piecewise
smooth (not merely admissible) paths, for connected slice submanifolds modelled on `ℝⁿ` (B assumes
`M` connected). -/
def A_pw : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N), IsConnected N →
    ∀ (q : N) (ε : ℝ) (nc : Morse.NormalCoord hN q ε) (c : ℝ → V) (a b : ℝ),
      Morse.IsPiecewiseSmooth c a b → (∀ t ∈ Icc a b, c t ∈ N) → c a = q →
      ∀ s : ℝ, 0 < s → s < ε → c b ∉ nc.ballSet s →
      ∃ t₁ t₂, a ≤ t₁ ∧ t₁ < t₂ ∧ t₂ ≤ b ∧ c t₁ = q ∧
        (∀ t ∈ Ioc t₁ t₂, c t ∈ nc.U ∧ c t ≠ q) ∧ ‖nc.G (c t₂)‖ = s ∧
        (∀ t ∈ Ico t₁ t₂, ‖nc.G (c t)‖ < s) ∧ s ≤ Morse.pathLength c t₁ t₂

theorem A_to_A_pw : A → A_pw := fun hA _ _ _ _ _ _ _ _ _ _ _ _ _ _ nc _ _ _ hc hcN ha _ hs hsε hb =>
  hA.2 nc hc.isAdmissible hcN ha hs hsε hb


open Emb Bridge in
/-- **The piecewise smooth part of A implies B on embedded manifolds**: A's crossing segment
`[t₁, t₂]` (in a project normal ball of radius `ε' ∈ (r, ε)`, `Emb.normalCoord_of_isNormBall`) gives
(ii); for (i) the segment `[a', t₂]` starts at the last time `a'` of `[t₁, t₂]` with radius `≤ δ`,
and its length is `≥ r − δ` by the project's Lemma 10.6 (`radius_sub_le_pathLength`, not part of
this item). -/
theorem A_pw_to_B_emb : A_pw → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN hcs q ε U hε hB r hr hrε pth hpw hp0 hp1
  have hconn : IsConnected N := isConnected_iff_connectedSpace.2 hcs
  obtain ⟨w₁, hw₁, hpw₁⟩ := hp1
  set ε' := (r + ε) / 2 with hε'
  have hε'pos : 0 < ε' := by rw [hε']; linarith
  have hε'lt : ε' < ε := by rw [hε']; linarith
  have hrε' : r < ε' := by rw [hε']; linarith
  obtain ⟨nc⟩ := normalCoord_of_isNormBall hB hε'pos hε'lt
  obtain ⟨hcpw, hcN, hL⟩ := path_data hpw
  set c := incl hN ∘ pth with hc_def
  have hca : c 0 = Subtype.val (q : ↥N) := by
    show incl hN (pth 0) = incl hN q
    rw [hp0]
  have hDw₁ : ‖D hN q w₁‖ = r := by rw [← nrm_eq]; exact hw₁
  have hw₁b : w₁ ∈ tball (n := n) q ε := by rw [mem_tball_iff, hDw₁]; exact hrε
  have hc1 : c 1 = Morse.exp hN (Subtype.val (q : ↥N)) (D hN q w₁) := by
    show incl hN (pth 1) = _
    rw [← hpw₁]
    exact incl_expMap (hB.2.1 _ hw₁b)
  have hbs : c 1 ∉ nc.ballSet r := by
    rw [nc.mem_ballSet, hc1, nc.G_exp _ (D_mem q w₁) (by rw [hDw₁]; exact hrε'), hDw₁]
    exact fun h => lt_irrefl _ h.2
  obtain ⟨t₁, t₂, ht₁, ht₁₂, ht₂, hct₁, hafter, ht₂s, hbefore, hL₁₂⟩ :=
    hA V W n N hN hconn q ε' nc c 0 1 hcpw hcN hca r hr hrε' hbs
  have hca' := hcpw.isAdmissible
  refine ⟨fun δ hδ hδr => ?_, ?_⟩
  swap
  · rw [hL]
    exact hL₁₂.trans (hca'.pathLength_le ht₁ ht₁₂.le ht₂)
  -- the radius along `[t₁, t₂]`
  set ρ : ℝ → ℝ := fun t => ‖nc.G (c t)‖ with hρ
  have hU : ∀ t ∈ Icc t₁ t₂, c t ∈ nc.U := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, hct₁]; exact nc.mem_U_self
    · exact (hafter t ⟨h, ht.2⟩).1
  have hρc : ContinuousOn ρ (Icc t₁ t₂) :=
    (nc.contDiffOn_G.continuousOn.comp (hcpw.2.1.mono (Icc_subset_Icc ht₁ ht₂)) hU).norm
  have hρ₁ : ρ t₁ = 0 := by
    show ‖nc.G (c t₁)‖ = 0
    rw [hct₁, nc.G_self, norm_zero]
  -- the last time `a'` with radius `≤ δ`
  set S := Icc t₁ t₂ ∩ ρ ⁻¹' Iic δ with hS
  have hSc : IsClosed S := hρc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have ht₁S : t₁ ∈ S := ⟨⟨le_rfl, ht₁₂.le⟩, by show ρ t₁ ≤ δ; rw [hρ₁]; exact hδ.le⟩
  have hSb : BddAbove S := ⟨t₂, fun t ht => ht.1.2⟩
  set a' := sSup S with ha'
  have ha'S : a' ∈ S := hSc.csSup_mem ⟨t₁, ht₁S⟩ hSb
  have hρa' : ρ a' = δ := by
    refine le_antisymm ha'S.2 ?_
    obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc ha'S.1.2
      (hρc.mono (Icc_subset_Icc ha'S.1.1 le_rfl))
      (⟨ha'S.2, by show δ ≤ ‖nc.G (c t₂)‖; rw [ht₂s]; exact hδr.le⟩ : δ ∈ Icc (ρ a') (ρ t₂))
    have htS : t ∈ S := ⟨⟨ha'S.1.1.trans ht.1, ht.2⟩, by show ρ t ≤ δ; rw [hteq]⟩
    have := le_csSup hSb htS
    rw [le_antisymm this ht.1] at hteq
    rw [hteq]
  have ht₁a' : t₁ < a' := by
    refine lt_of_le_of_ne ha'S.1.1 fun h => ?_
    rw [← h, hρ₁] at hρa'
    exact hδ.ne hρa'
  have hafter' : ∀ t ∈ Icc a' t₂, δ ≤ ρ t ∧ ρ t ≤ r := by
    intro t ht
    refine ⟨?_, ?_⟩
    · rcases eq_or_lt_of_le ht.1 with h | h
      · rw [← h, hρa']
      · by_contra hlt
        have htS : t ∈ S := ⟨⟨ha'S.1.1.trans ht.1, ht.2⟩, (not_le.1 hlt).le⟩
        exact absurd (le_csSup hSb htS) (not_le.2 h)
    · rcases eq_or_lt_of_le ht.2 with h | h
      · show ‖nc.G (c t)‖ ≤ r
        rw [h, ht₂s]
      · exact (hbefore t ⟨ha'S.1.1.trans ht.1, h⟩).le
  -- reading points of the segment in the blind normal ball
  have hpt : ∀ t ∈ Icc t₁ t₂, pth t = expMap (conn (hN := hN)) q (L hN q (nc.G (c t))) ∧
      nrm (n := n) q (L hN q (nc.G (c t))) = ρ t := fun t ht =>
    eq_expMap_G hB hε'lt.le nc (hU t ht)
  have hsub : ∀ t ∈ Icc a' t₂, t ∈ Icc t₁ t₂ := fun t ht => ⟨ht₁a'.le.trans ht.1, ht.2⟩
  refine ⟨a', t₂, ht₁.trans ht₁a'.le, ha'S.1.2, ht₂, ?_, ?_, ?_, ?_⟩
  · have h := hpt a' ha'S.1
    exact ⟨_, by show nrm (n := n) q _ = δ; rw [h.2, hρa'], h.1.symm⟩
  · have h := hpt t₂ ⟨ht₁₂.le, le_rfl⟩
    exact ⟨_, by show nrm (n := n) q _ = r; rw [h.2]; exact ht₂s, h.1.symm⟩
  · intro t ht
    have h := hpt t (hsub t ht)
    exact ⟨_, by show δ ≤ nrm (n := n) q _ ∧ nrm (n := n) q _ ≤ r; rw [h.2]; exact hafter' t ht,
      h.1.symm⟩
  · rw [show arcLen (n := n) pth a' t₂ = Morse.pathLength c a' t₂ from arcLen_eq pth a' t₂]
    have hmem : ∀ t ∈ Icc a' t₂, c t ∈ N ∧ c t ∈ nc.U ∧ c t ≠ Subtype.val (q : ↥N) :=
      fun t ht => ⟨(pth t).2, hafter t ⟨ht₁a'.trans_le ht.1, ht.2⟩⟩
    have := nc.radius_sub_le_pathLength (hca'.mono (ht₁.trans ht₁a'.le) ha'S.1.2 ht₂) hmem
    rw [ht₂s] at this
    have e : ‖nc.G (c a')‖ = δ := hρa'
    rw [e] at this
    exact this

/-- **A implies B on embedded manifolds** (through `A_pw`). -/
theorem A_to_B_emb : A → B_emb := fun hA => A_pw_to_B_emb (A_to_A_pw hA)

#rt_check RoundTrip.V7_14.A_to_B_emb [Morse.NormalCoord.isCompact_closedBallSet,
  Morse.NormalCoord.exists_crossing]

open Emb Bridge in
/-- **B on embedded manifolds implies the project's crossing lemma for piecewise smooth paths**
(connected `N`). The segment `[t₁, t₂]` (last visit of `q` before the first exit) is chosen by
the project's topological argument (re-done here, with the compactness of the closed normal ball
proved inline); its length bound `s ≤ L(c|[t₁, t₂])` is B's conclusion (ii), applied to the
segment reparametrized to `[0, 1]`. -/
theorem B_emb_to_A_pw : B_emb → A_pw := by
  intro hB V _ _ _ W _ _ _ n N hN hconn q₀ ε nc c a b hc hcN ha s hs hsε hb
  obtain ⟨q, rfl⟩ : ∃ q : Sub hN, q = q₀ := ⟨q₀, rfl⟩
  have : ConnectedSpace (Sub hN) := isConnected_iff_connectedSpace.1 hconn
  have hca := hc.isAdmissible
  have hqball : Subtype.val (q : ↥N) ∈ nc.ballSet s := (nc.mem_ballSet).2 ⟨nc.mem_U_self, by
    rw [nc.G_self, norm_zero]; exact hs⟩
  -- the first exit time `t₂` (the project's argument)
  set S₂ := Icc a b ∩ c ⁻¹' (nc.ballSet s)ᶜ with hS₂_def
  have hS₂c : IsClosed S₂ :=
    hca.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc (nc.isOpen_ballSet s).isClosed_compl
  have hbS₂ : b ∈ S₂ := ⟨⟨hca.le, le_rfl⟩, hb⟩
  have hS₂bdd : BddBelow S₂ := ⟨a, fun t ht => ht.1.1⟩
  set t₂ := sInf S₂ with ht₂_def
  have ht₂S : t₂ ∈ S₂ := hS₂c.csInf_mem ⟨b, hbS₂⟩ hS₂bdd
  have haS₂ : a ∉ S₂ := fun h => h.2 (by rw [ha]; exact hqball)
  have hat₂ : a < t₂ := lt_of_le_of_ne ht₂S.1.1 fun h => haS₂ (h ▸ ht₂S)
  have hbefore : ∀ t ∈ Ico a t₂, c t ∈ nc.ballSet s := by
    intro t ht
    by_contra hcon
    have : t ∈ S₂ := ⟨⟨ht.1, ht.2.le.trans ht₂S.1.2⟩, hcon⟩
    exact absurd (csInf_le hS₂bdd this) (not_le.2 ht.2)
  have ht₂cl : c t₂ ∈ nc.closedBallSet s := by
    have hK : IsCompact (Metric.closedBall (0 : V) s ∩ (Morse.tangentSubspace hN q : Set V)) :=
      (isCompact_closedBall 0 s).inter_right (Submodule.closed_of_finiteDimensional _)
    have hcl : IsClosed (nc.closedBallSet s) :=
      (hK.image_of_continuousOn (nc.contDiffOn_F.continuousOn.mono fun v hv =>
        nc.mem_O v hv.2 (lt_of_le_of_lt (by simpa using hv.1) hsε))).isClosed
    have hcont : ContinuousWithinAt c (Ico a t₂) t₂ :=
      (hca.continuousOn t₂ ht₂S.1).mono (Ico_subset_Icc_self.trans
        (Icc_subset_Icc le_rfl ht₂S.1.2))
    have : (𝓝[Ico a t₂] t₂).NeBot := right_nhdsWithin_Ico_neBot hat₂
    refine hcl.mem_of_tendsto hcont (eventually_nhdsWithin_of_forall fun t ht => ?_)
    have h1 := hbefore t ht
    rw [nc.mem_ballSet] at h1
    exact (nc.mem_closedBallSet hsε).2 ⟨hcN t ⟨ht.1, ht.2.le.trans ht₂S.1.2⟩, h1.1, h1.2.le⟩
  obtain ⟨-, ht₂U, ht₂le⟩ := (nc.mem_closedBallSet hsε).1 ht₂cl
  have ht₂s : ‖nc.G (c t₂)‖ = s := by
    refine le_antisymm ht₂le (not_lt.1 fun hlt => ht₂S.2 ?_)
    exact (nc.mem_ballSet).2 ⟨ht₂U, hlt⟩
  have ht₂q : c t₂ ≠ Subtype.val (q : ↥N) := by
    intro h
    rw [h, nc.G_self, norm_zero] at ht₂s
    exact hs.ne' ht₂s.symm
  -- the last visit `t₁` of `q` before `t₂`
  set S₁ := Icc a t₂ ∩ c ⁻¹' {Subtype.val (q : ↥N)} with hS₁_def
  have hS₁c : IsClosed S₁ :=
    (hca.continuousOn.mono (Icc_subset_Icc le_rfl ht₂S.1.2)).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_singleton
  have haS₁ : a ∈ S₁ := ⟨⟨le_rfl, hat₂.le⟩, ha⟩
  have hS₁bdd : BddAbove S₁ := ⟨t₂, fun t ht => ht.1.2⟩
  set t₁ := sSup S₁ with ht₁_def
  have ht₁S : t₁ ∈ S₁ := hS₁c.csSup_mem ⟨a, haS₁⟩ hS₁bdd
  have ht₁t₂ : t₁ < t₂ := lt_of_le_of_ne ht₁S.1.2 fun h => ht₂q (h ▸ ht₁S.2)
  have hafter : ∀ t ∈ Ioc t₁ t₂, c t ∈ nc.U ∧ c t ≠ Subtype.val (q : ↥N) := by
    intro t ht
    refine ⟨?_, fun h => ?_⟩
    · rcases eq_or_lt_of_le ht.2 with h | h
      · rw [h]; exact ht₂U
      · exact ((nc.mem_ballSet).1 (hbefore t ⟨ht₁S.1.1.trans ht.1.le, h⟩)).1
    · have : t ∈ S₁ := ⟨⟨ht₁S.1.1.trans ht.1.le, ht.2⟩, h⟩
      exact absurd (le_csSup hS₁bdd this) (not_le.2 ht.1)
  refine ⟨t₁, t₂, ht₁S.1.1, ht₁t₂, ht₂S.1.2, ht₁S.2, hafter, ht₂s, fun t ht => ?_, ?_⟩
  · exact ((nc.mem_ballSet).1 (hbefore t ⟨ht₁S.1.1.trans ht.1, ht.2⟩)).2
  -- the length of `[t₁, t₂]`: B's conclusion (ii) for the reparametrized segment
  have hNB := isNormBall_of_normalCoord (q := q) nc
  have hseg : Morse.IsPiecewiseSmooth c t₁ t₂ := hc.mono ht₁S.1.1 ht₁t₂.le ht₂S.1.2
  set c' : ℝ → V := fun t => c ((t₂ - t₁) * t + t₁) with hc'
  have hc'pw := isPiecewiseSmooth_reparam ht₁t₂ hseg
  have hc'N : ∀ t ∈ Icc (0 : ℝ) 1, c' t ∈ N := fun t ht =>
    hcN _ ⟨ht₁S.1.1.trans (by nlinarith [ht.1, ht₁t₂]), (by nlinarith [ht.2, ht₁t₂] :
      (t₂ - t₁) * t + t₁ ≤ t₂).trans ht₂S.1.2⟩
  have hpw := isPW_lift (n := n) hc'pw hc'N q
  have heqc : ∀ t ∈ Icc (0 : ℝ) 1, incl hN (lift c' q t) = c' t := fun t ht => incl_lift q (hc'N t ht)
  have hc'0 : c' 0 = c t₁ := by simp only [hc', mul_zero, zero_add]
  have hc'1 : c' 1 = c t₂ := by simp only [hc', mul_one, sub_add_cancel]
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1I : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hp0 : lift c' q 0 = q := Subtype.ext ((heqc 0 h0I).trans (hc'0.trans ht₁S.2))
  have hp1 : lift c' q 1 ∈ shell (conn (hN := hN)) q s := by
    have hx : incl hN (lift c' q 1) ∈ nc.U := by rw [heqc 1 h1I, hc'1]; exact ht₂U
    obtain ⟨he, hn⟩ := eq_expMap_G hNB le_rfl nc hx
    refine ⟨_, ?_, he.symm⟩
    show nrm (n := n) q _ = s
    rw [hn, heqc 1 h1I, hc'1, ht₂s]
  have := (hB V W n N hN q ε _ nc.pos hNB s hs hsε (lift c' q) hpw hp0 hp1).2
  rw [show arcLen (n := n) (lift c' q) 0 1 = Morse.pathLength (incl hN ∘ lift c' q) 0 1 from
    arcLen_eq _ 0 1, pathLength_congr (c := incl hN ∘ lift c' q) zero_le_one heqc,
    pathLength_reparam c ht₁t₂] at this
  exact this

/-- **On embedded manifolds, B is exactly the piecewise smooth crossing lemma of A** (for connected
`N`). -/
theorem B_emb_iff_A_pw : B_emb ↔ A_pw := ⟨B_emb_to_A_pw, A_pw_to_B_emb⟩

#rt_check RoundTrip.V7_14.B_emb_to_A_pw [Morse.NormalCoord.isCompact_closedBallSet,
  Morse.NormalCoord.exists_crossing]
#rt_overlap RoundTrip.V7_14.B_emb_to_A_pw [Morse.NormalCoord.isCompact_closedBallSet,
  Morse.NormalCoord.exists_crossing]

end RoundTrip.V7_14
