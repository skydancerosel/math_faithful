import Morse
import RoundTrip.Check
import RoundTrip.Blind.V7_16
import RoundTrip.Bridge

open Set Filter Topology
open scoped ContDiff Manifold RealInnerProductSpace

namespace RoundTrip.V7_16

/-- The project's statement (universes instantiated at 0), for a slice submanifold `N ⊆ V` with the
induced metric, a normal radius `ε` at `q` (`Morse.NormalCoord`) and an admissible path `c` in `N`
from `q` to `exp_q(v)`, `0 < ‖v‖ < ε`, of length exactly `‖v‖`: (sharp equality case of Theorem
10.4) `c(t) = exp_q((L(c|[a, t])/‖v‖) v)` on `[a, b]`, a monotone reparametrization of the geodesic
`t ↦ exp_q(tv)`; the arc length `t ↦ L(c|[a, t])` of an admissible path is monotone; and (Milnor's
equality clause) `c([a, b]) = {exp_q(tv) : 0 ≤ t ≤ 1}`. -/
def A : Prop :=
  type_of% @Morse.NormalCoord.eq_exp_of_pathLength_eq.{0,0,0} ∧
    type_of% @Morse.IsAdmissible.monotoneOn_pathLength.{0} ∧
    type_of% @Morse.NormalCoord.image_eq_of_pathLength_eq.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.NormalCoord.eq_exp_of_pathLength_eq, @Morse.IsAdmissible.monotoneOn_pathLength,
    @Morse.NormalCoord.image_eq_of_pathLength_eq⟩

/-! Neither `A → B` nor `B → A` is proved; see `V7_16.json`. B quantifies over abstract connected
Hausdorff `ℝⁿ`-manifolds with an arbitrary smooth Mathlib `RiemannianBundle` metric and an
arbitrary Levi-Civita `CovariantDerivative`, while A only concerns slice submanifolds `N ⊆ V` with
the induced metric; conversely A's sharp form (monotone reparametrization) and the monotonicity of
arc length are not consequences of B's strict inequality.

## The embedded special case

B is specialized to `M = ↥N` (`RoundTrip.Bridge.Sub hN`) with the induced metric and the induced
Levi-Civita connection `Bridge.conn` (`B_emb`). The `Emb` section repeats the normal-ball
dictionary of `Items/V7_13.lean` (Items files do not import each other) and adds the reading of a
short blind geodesic as `t ↦ exp_q(tv)` with length `‖v‖` (`Emb.geodesic_data`). -/

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

end Emb

open Emb in
/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`) with the induced metric and the induced
Levi-Civita connection (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (Wc : Type) [NormedAddCommGroup Wc] [NormedSpace ℝ Wc] [FiniteDimensional ℝ Wc] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) Wc N)
    [ConnectedSpace (Bridge.Sub hN)],
    ∀ (W : Set (Bridge.Sub hN)) (ε : ℝ), IsOpen W → 0 < ε →
      IsUniformNormal (Bridge.conn (hN := hN)) W ε →
    ∀ q₁ ∈ W, ∀ q₂ ∈ W, ∀ γ : ℝ → Bridge.Sub hN, JoinsShort (Bridge.conn (hN := hN)) ε γ q₁ q₂ →
      ∀ pth : ℝ → Bridge.Sub hN, IsPW (n := n) pth 0 1 → pth 0 = q₁ → pth 1 = q₂ →
        pth '' Set.Icc 0 1 ≠ γ '' Set.Icc 0 1 → arcLen (n := n) γ 0 1 < arcLen (n := n) pth 0 1

/-- `B_emb` is a special case of B (the induced connection is Levi-Civita, `Bridge.conn_isLC`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

open Emb Bridge in
/-- **A implies B on embedded manifolds**: the inequality `L(γ) ≤ L(ω)` from the project's
`Morse.NormalCoord.norm_le_pathLength` (not part of this item), the equality case from A's
`image_eq_of_pathLength_eq`, in a project normal ball of radius `ε' ∈ (L(γ), ε)` obtained from
B's uniformly normal `W` (`Emb.normalCoord_of_isNormBall`). -/
theorem A_to_B_emb : A → B_emb := by
  intro hA V _ _ _ Wc _ _ _ n N hN _ W ε hWo hε hUN q₁ hq₁ q₂ hq₂ γ hJ pth hpw hp0 hp1 hne
  obtain ⟨hγ, hγ0, hγ1, hγlen⟩ := hJ
  obtain ⟨v, hvT, hγv, hlen, -⟩ := geodesic_data hγ
  rw [hγ0] at hvT hγv
  obtain ⟨U, -, hB⟩ := hUN.2.2 q₁ hq₁
  have hvε : ‖v‖ < ε := hlen ▸ hγlen
  set ε' := (‖v‖ + ε) / 2 with hε'
  have hε'pos : 0 < ε' := by rw [hε']; linarith [norm_nonneg v]
  have hε'lt : ε' < ε := by rw [hε']; linarith
  have hvε' : ‖v‖ < ε' := by rw [hε']; linarith
  obtain ⟨nc⟩ := normalCoord_of_isNormBall hB hε'pos hε'lt
  obtain ⟨hcpw, hcN, hL⟩ := path_data hpw
  have h1I : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hca : (incl hN ∘ pth) 0 = Subtype.val (q₁ : ↥N) := by
    show incl hN (pth 0) = incl hN q₁
    rw [hp0]
  have hcb : (incl hN ∘ pth) 1 = Morse.exp hN (Subtype.val (q₁ : ↥N)) v := by
    show incl hN (pth 1) = _
    rw [hp1, ← hγ1, hγv 1 h1I, one_smul]
    rfl
  have hle := nc.norm_le_pathLength hcpw.isAdmissible hcN hca hvT hvε' hcb
  rw [hlen, hL]
  refine lt_of_le_of_ne hle fun heq => hne (image_eq_of_incl ?_)
  have hray : (incl hN ∘ γ) '' Icc 0 1 =
      (fun t : ℝ => Morse.exp hN (Subtype.val (q₁ : ↥N)) (t • v)) '' Icc 0 1 :=
    image_congr fun t ht => hγv t ht
  rw [hray]
  rcases eq_or_ne v 0 with rfl | hv0
  · -- `q₁ = q₂`: both images are the point `q₁`
    rw [norm_zero] at heq
    have hconst := hcpw.isAdmissible.eq_of_pathLength_eq_zero heq.symm
    ext y
    simp only [mem_image, smul_zero]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, by rw [hconst t ht, hca, Morse.exp_zero q₁.2]⟩
    · rintro ⟨τ, -, rfl⟩
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, by rw [hca, Morse.exp_zero q₁.2]⟩
  · exact hA.2.2 nc hcpw.isAdmissible hcN hca hvT hvε' hcb hv0 heq.symm

#rt_check RoundTrip.V7_16.A_to_B_emb [Morse.NormalCoord.eq_exp_of_pathLength_eq,
  Morse.IsAdmissible.monotoneOn_pathLength, Morse.NormalCoord.image_eq_of_pathLength_eq]
#rt_overlap RoundTrip.V7_16.A_to_B_emb [Morse.NormalCoord.eq_exp_of_pathLength_eq,
  Morse.IsAdmissible.monotoneOn_pathLength, Morse.NormalCoord.image_eq_of_pathLength_eq]

end RoundTrip.V7_16
