import Morse
import RoundTrip.Check
import RoundTrip.Blind.V7_15
import RoundTrip.Bridge

open Set Filter Topology
open scoped ContDiff Manifold RealInnerProductSpace

namespace RoundTrip.V7_15

/-- The project's statement (universes instantiated at 0), for a slice submanifold `N ⊆ V` with the
induced metric: for a normal radius `ε` at `q` (`Morse.NormalCoord`) and `v ∈ T_qN`, `‖v‖ < ε`,
`t ↦ exp_q(tv)` is a geodesic near `[0, 1]` with velocity `v` at `0` (`radial`) and length `‖v‖` on
`[0, 1]` (`pathLength_exp_smul`); every admissible path in `N` from `q` to `exp_q(v)` has length
`≥ ‖v‖` (`norm_le_pathLength`, Theorem 10.4's inequality); and Milnor's Theorem 10.4
(`theorem_10_4`): every `p ∈ N` has an open `O ∋ p` and `ε > 0` (from Lemma 10.3) such that any
`q₁, q₂ ∈ N ∩ O` are joined by `t ↦ exp_{q₁}(tv)`, `‖v‖ < ε`, of length `‖v‖`, and every piecewise
smooth path in `N` on any `[a, b]` from `q₁` to `q₂` has length `≥ ‖v‖`, with equality only if
its image is that of the geodesic. -/
def A : Prop :=
  type_of% @Morse.NormalCoord.radial.{0,0,0} ∧
    type_of% @Morse.NormalCoord.pathLength_exp_smul.{0,0,0} ∧
    type_of% @Morse.NormalCoord.norm_le_pathLength.{0,0,0} ∧
    type_of% @Morse.theorem_10_4.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.NormalCoord.radial, @Morse.NormalCoord.pathLength_exp_smul,
    @Morse.NormalCoord.norm_le_pathLength, @Morse.theorem_10_4⟩

/-! Neither `A → B` nor `B → A` is proved; see `V7_15.json`. B quantifies over abstract connected
Hausdorff `ℝⁿ`-manifolds with an arbitrary smooth Mathlib `RiemannianBundle` metric and an
arbitrary Levi-Civita `CovariantDerivative`, while A only concerns slice submanifolds `N ⊆ V` with
the induced metric; conversely A's statements about an arbitrary normal radius (`radial`,
`pathLength_exp_smul`, `norm_le_pathLength`) are not consequences of B, whose hypothesis is a
uniformly normal `W` (Lemma 10.3).

## The embedded special case

B is specialized to `M = ↥N` (`RoundTrip.Bridge.Sub hN`) with the induced metric and the induced
Levi-Civita connection `Bridge.conn` (`B_emb`). The `Emb` section repeats the normal-ball
dictionary of `Items/V7_13.lean` (Items files do not import each other), reads a short blind
geodesic as `t ↦ exp_q(tv)` with length `‖v‖` (`Emb.geodesic_data`), and re-derives Milnor's
equality clause in an arbitrary normal ball from A's `norm_le_pathLength` (`Emb.image_eq_of_eq`:
the project's own proof of `Morse.NormalCoord.image_eq_of_pathLength_eq`, which cannot be cited
because it uses `norm_le_pathLength`, a theorem of this item). Conversely the neighbourhoods of the
project's Lemma 10.3 are uniformly normal in B's sense (`Emb.isUniformNormal_of`), so B on embedded
manifolds implies the project's `theorem_10_4` for connected `N` (`B_emb_to_A_10_4`). -/

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

/-- The sharp equality case of Theorem 10.4, with A's `norm_le_pathLength` supplied by the
hypothesis (the proof of `Morse.NormalCoord.eq_exp_of_pathLength_eq`, verbatim otherwise). -/
theorem eq_exp_of_eq (hA : RoundTrip.V7_15.A) {q : N} {ε : ℝ} (nc : Morse.NormalCoord hN q ε)
    {c : ℝ → V} {a b : ℝ} (hc : Morse.IsAdmissible c a b)
    (hcN : ∀ t ∈ Icc a b, c t ∈ N) (ha : c a = q) {v : V} (hv : v ∈ Morse.tangentSubspace hN q)
    (hvε : ‖v‖ < ε) (hb : c b = Morse.exp hN q v) (hv0 : v ≠ 0)
    (heq : Morse.pathLength c a b = ‖v‖) :
    ∀ t ∈ Icc a b, c t = Morse.exp hN q ((Morse.pathLength c a t / ‖v‖) • v) := by
  set s := ‖v‖ with hs_def
  have hs : 0 < s := norm_pos_iff.2 hv0
  have hbs : c b ∉ nc.ballSet s := by
    rw [nc.mem_ballSet, hb, nc.G_exp v hv hvε]
    exact fun h => lt_irrefl _ h.2
  obtain ⟨t₁, t₂, ht₁, ht₁₂, ht₂, hct₁, hafter, ht₂s, hbefore, hL⟩ :=
    nc.exists_crossing hc hcN ha hs hvε hbs
  have hsplit₁ := hc.pathLength_add (m := t₁) ⟨ht₁, ht₁₂.le.trans ht₂⟩
  have hsplit₂ := (hc.mono ht₁ (ht₁₂.le.trans ht₂) le_rfl).pathLength_add (m := t₂) ⟨ht₁₂.le, ht₂⟩
  have hn₁ := (hc.mono le_rfl ht₁ (ht₁₂.le.trans ht₂)).pathLength_nonneg
  have hn₃ := (hc.mono (ht₁.trans ht₁₂.le) ht₂ le_rfl).pathLength_nonneg
  have hL₁ : Morse.pathLength c a t₁ = 0 := by linarith
  have hL₃ : Morse.pathLength c t₂ b = 0 := by linarith
  have hL₂ : Morse.pathLength c t₁ t₂ = s := by linarith
  have hconst₁ := (hc.mono le_rfl ht₁ (ht₁₂.le.trans ht₂)).eq_of_pathLength_eq_zero hL₁
  have hconst₃ := (hc.mono (ht₁.trans ht₁₂.le) ht₂ le_rfl).eq_of_pathLength_eq_zero hL₃
  have hct₂ : c t₂ = Morse.exp hN q v := by rw [← hb, hconst₃ b ⟨ht₂, le_rfl⟩]
  have hGt₂ : nc.G (c t₂) = v := by rw [hct₂, nc.G_exp v hv hvε]
  have hmid : ∀ t ∈ Ioc t₁ t₂, Morse.pathLength c t₁ t = ‖nc.G (c t)‖ ∧
      c t = Morse.exp hN q ((‖nc.G (c t)‖ / s) • v) := by
    intro t ht
    have htN : c t ∈ N := hcN t ⟨ht₁.trans ht.1.le, ht.2.trans ht₂⟩
    obtain ⟨htU, htq⟩ := hafter t ht
    have hGT := nc.G_mem _ htU htN
    have hGε := nc.norm_G_lt _ htU htN
    have hlow₁ : ‖nc.G (c t)‖ ≤ Morse.pathLength c t₁ t :=
      hA.2.2.1 nc (hc.mono ht₁ ht.1.le (ht.2.trans ht₂))
        (fun x hx => hcN x ⟨ht₁.trans hx.1, hx.2.trans (ht.2.trans ht₂)⟩) hct₁ hGT hGε
        (nc.exp_G _ htU htN).symm
    have hct' : Morse.IsAdmissible c t t₂ := hc.mono (ht₁.trans ht.1.le) ht.2 ht₂
    have hmem' : ∀ x ∈ Icc t t₂, c x ∈ N ∧ c x ∈ nc.U ∧ c x ≠ q := fun x hx =>
      ⟨hcN x ⟨ht₁.trans (ht.1.le.trans hx.1), hx.2.trans ht₂⟩,
        hafter x ⟨ht.1.trans_le hx.1, hx.2⟩⟩
    have hlow₂ := nc.radius_sub_le_pathLength hct' hmem'
    rw [ht₂s] at hlow₂
    have hsplit := (hc.mono ht₁ ht₁₂.le ht₂).pathLength_add (m := t) ⟨ht.1.le, ht.2⟩
    have heq₁ : Morse.pathLength c t₁ t = ‖nc.G (c t)‖ := by linarith
    have heq₂ : Morse.pathLength c t t₂ = ‖nc.G (c t₂)‖ - ‖nc.G (c t)‖ := by rw [ht₂s]; linarith
    refine ⟨heq₁, ?_⟩
    have hdir := nc.direction_eq_of_pathLength_eq hct' hmem' heq₂ t ⟨le_rfl, ht.2⟩
    rw [hGt₂, ← hs_def] at hdir
    have hGt0 : ‖nc.G (c t)‖ ≠ 0 := norm_ne_zero_iff.2 (nc.G_ne_zero htU htN htq)
    have hG : nc.G (c t) = (‖nc.G (c t)‖ / s) • v :=
      calc nc.G (c t) = ‖nc.G (c t)‖ • (‖nc.G (c t)‖⁻¹ • nc.G (c t)) := by
            rw [smul_smul, mul_inv_cancel₀ hGt0, one_smul]
        _ = ‖nc.G (c t)‖ • (s⁻¹ • v) := by rw [hdir]
        _ = (‖nc.G (c t)‖ / s) • v := by rw [smul_smul, div_eq_mul_inv]
    rw [← hG, nc.exp_G _ htU htN]
  intro t ht
  rcases le_or_gt t t₁ with htt₁ | htt₁
  · have hLt : Morse.pathLength c a t = 0 := le_antisymm
      (hL₁ ▸ (hc.mono le_rfl ht₁ (ht₁₂.le.trans ht₂)).pathLength_le le_rfl ht.1 htt₁)
      (hc.mono le_rfl ht.1 ht.2).pathLength_nonneg
    rw [hconst₁ t ⟨ht.1, htt₁⟩, hLt, zero_div, zero_smul, Morse.exp_zero q.2, ha]
  rcases le_or_gt t t₂ with htt₂ | htt₂
  · obtain ⟨h1, h2⟩ := hmid t ⟨htt₁, htt₂⟩
    have hsplit := (hc.mono le_rfl ht.1 ht.2).pathLength_add (m := t₁) ⟨ht₁, htt₁.le⟩
    rw [h2]
    congr 2
    rw [← hsplit, hL₁, zero_add, h1]
  · have hsplit := (hc.mono le_rfl ht.1 ht.2).pathLength_add (m := t₂) ⟨ht₁.trans ht₁₂.le, htt₂.le⟩
    have hLt₂t : Morse.pathLength c t₂ t = 0 := le_antisymm
      (hL₃ ▸ (hc.mono (ht₁.trans ht₁₂.le) ht₂ le_rfl).pathLength_le le_rfl htt₂.le ht.2)
      (hc.mono (ht₁.trans ht₁₂.le) htt₂.le ht.2).pathLength_nonneg
    have hLat₂ : Morse.pathLength c a t₂ = s := by
      have := (hc.mono le_rfl (ht₁.trans ht₁₂.le) ht₂).pathLength_add (m := t₁) ⟨ht₁, ht₁₂.le⟩
      rw [← this, hL₁, zero_add, hL₂]
    rw [← hsplit, hLat₂, hLt₂t, add_zero, div_self hs.ne', one_smul,
      hconst₃ t ⟨htt₂.le, ht.2⟩, hct₂]

/-- Milnor's equality clause in an arbitrary normal ball, with A's `norm_le_pathLength` supplied
by the hypothesis (the proof of `Morse.NormalCoord.image_eq_of_pathLength_eq`). -/
theorem image_eq_of_eq (hA : RoundTrip.V7_15.A) {q : N} {ε : ℝ} (nc : Morse.NormalCoord hN q ε)
    {c : ℝ → V} {a b : ℝ} (hc : Morse.IsAdmissible c a b)
    (hcN : ∀ t ∈ Icc a b, c t ∈ N) (ha : c a = q) {v : V} (hv : v ∈ Morse.tangentSubspace hN q)
    (hvε : ‖v‖ < ε) (hb : c b = Morse.exp hN q v) (hv0 : v ≠ 0)
    (heq : Morse.pathLength c a b = ‖v‖) :
    c '' Icc a b = (fun t : ℝ => Morse.exp hN q (t • v)) '' Icc 0 1 := by
  have hs : 0 < ‖v‖ := norm_pos_iff.2 hv0
  have hrep := eq_exp_of_eq hA nc hc hcN ha hv hvε hb hv0 heq
  set ρ : ℝ → ℝ := fun t => Morse.pathLength c a t / ‖v‖ with hρ_def
  have hρc : ContinuousOn ρ (Icc a b) := hc.continuousOn_pathLength.div_const _
  have hρa : ρ a = 0 := by simp [hρ_def, Morse.pathLength]
  have hρb : ρ b = 1 := by simp [hρ_def, heq, div_self hs.ne']
  have hρmaps : ρ '' Icc a b = Icc 0 1 := by
    apply Subset.antisymm
    · rintro _ ⟨t, ht, rfl⟩
      have h1 := hc.monotoneOn_pathLength ⟨le_rfl, hc.le⟩ ht ht.1
      have h2 := hc.monotoneOn_pathLength ht ⟨hc.le, le_rfl⟩ ht.2
      simp only [Morse.pathLength, intervalIntegral.integral_same] at h1
      constructor
      · exact div_nonneg h1 hs.le
      · rw [div_le_one hs, ← heq]; exact h2
    · have := intermediate_value_Icc hc.le hρc
      rwa [hρa, hρb] at this
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨ρ t, hρmaps ▸ mem_image_of_mem ρ ht, (hrep t ht).symm⟩
  · rintro ⟨τ, hτ, rfl⟩
    rw [← hρmaps] at hτ
    obtain ⟨t, ht, rfl⟩ := hτ
    exact ⟨t, ht, hrep t ht⟩

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

/-! ### Lemma 10.3's neighbourhoods are blind uniformly normal sets -/

/-- A project geodesic `t ↦ exp_q(tv)` (`(q, v) ∈ expDom`, `v ∈ T_qN`) gives a blind geodesic on
`[0, 1]` from `q` with initial velocity `L_q v`, length `‖v‖`, ending at `exp_q(v)`. -/
theorem short_of_mem_expDom {q : Sub hN} {v : V} (hv : v ∈ Morse.tangentSubspace hN q)
    (h : (incl hN q, v) ∈ Morse.expDom hN) :
    ∃ γ : ℝ → Sub hN, IsGeodesic (conn (hN := hN)) γ (Icc 0 1) ∧ γ 0 = q ∧
      InitData (n := n) γ (Icc 0 1) q (L hN q v) ∧
      incl hN (γ 1) = Morse.exp hN (incl hN q) v ∧ arcLen (n := n) γ 0 1 = ‖v‖ := by
  obtain ⟨g, hg⟩ := h
  have hg' : Morse.IsGeodesicFrom hN g (incl hN q) (D hN q (L hN q v)) := by rwa [D_L hv]
  obtain ⟨h1, h2, -⟩ := isGeodesic_lift_of_isGeodesicFrom hg'
  have hγ : IsGeodesic (conn (hN := hN)) (lift g q) (Icc 0 1) := h1
  have hinit : InitData (n := n) (lift g q) (Icc 0 1) q (L hN q v) := h2
  have h0 : lift g q 0 = q := hinit.1
  obtain ⟨v', -, hγv, hlen, hvD⟩ := geodesic_data hγ
  have hv' : v' = v := by
    have := (initData_iff (n := n) h0).1 h2
    rw [D_L hv] at this
    rw [← hvD]
    exact this
  rw [h0, hv'] at hγv
  rw [hv'] at hlen
  refine ⟨lift g q, hγ, h0, hinit, ?_, hlen⟩
  rw [hγv 1 ⟨zero_le_one, le_rfl⟩, one_smul]

/-- **Lemma 10.3 gives B's hypothesis**: for `O, ε` with the three conclusions of the project's
`Morse.lemma_10_3`, `W = N ∩ O` is a blind uniformly normal set (`IsUniformNormal`) for the induced
connection. -/
theorem isUniformNormal_of {O : Set V} {ε : ℝ}
    (h1 : ∀ q₁ q₂ : N, (q₁ : V) ∈ O → (q₂ : V) ∈ O →
      ∃! v, v ∈ Morse.tangentSubspace hN q₁ ∧ ‖v‖ < ε ∧ Morse.exp hN q₁ v = q₂)
    (h2 : ∃ O₂ : Set (V × V), IsOpen O₂ ∧ ∃ G : V × V → V, ContDiffOn ℝ ∞ G O₂ ∧
      ∀ q₁ q₂ : N, (q₁ : V) ∈ O → (q₂ : V) ∈ O → ((q₁ : V), (q₂ : V)) ∈ O₂ ∧
        G (q₁, q₂) ∈ Morse.tangentSubspace hN q₁ ∧ ‖G (q₁, q₂)‖ < ε ∧
        Morse.exp hN q₁ (G (q₁, q₂)) = q₂)
    (h3 : ∀ q : N, (q : V) ∈ O → Morse.IsNormalRadius hN q ε) :
    IsUniformNormal (conn (hN := hN)) {x : Sub hN | incl hN x ∈ O} ε := by
  -- short geodesics from the project's `exp`
  have hshort : ∀ q₁ q₂ : Sub hN, incl hN q₁ ∈ O → ∀ v ∈ Morse.tangentSubspace hN q₁, ‖v‖ < ε →
      Morse.exp hN (incl hN q₁) v = incl hN q₂ →
      ∃ γ, JoinsShort (conn (hN := hN)) ε γ q₁ q₂ ∧ InitData (n := n) γ (Icc 0 1) q₁ (L hN q₁ v) ∧
        arcLen (n := n) γ 0 1 = ‖v‖ := by
    intro q₁ q₂ hq₁ v hv hvε hexp
    obtain ⟨nc⟩ := h3 q₁ hq₁
    obtain ⟨γ, hγ, h0, hinit, h1γ, hlen⟩ := short_of_mem_expDom hv (nc.mem_expDom v hv hvε)
    refine ⟨γ, ⟨hγ, h0, ?_, hlen ▸ hvε⟩, hinit, hlen⟩
    apply Subtype.ext
    exact h1γ.trans hexp
  refine ⟨fun q₁ hq₁ q₂ hq₂ => ?_, ?_, fun q hq => ?_⟩
  · obtain ⟨v, ⟨hv, hvε, hexp⟩, huniq⟩ := h1 q₁ q₂ hq₁ hq₂
    obtain ⟨γ, hJ, -, -⟩ := hshort q₁ q₂ hq₁ v hv hvε hexp
    refine ⟨γ, hJ, fun γ' hJ' => fun t ht => ?_⟩
    obtain ⟨hγ'g, hγ'0, hγ'1, hγ'len⟩ := hJ'
    obtain ⟨hγg, hγ0, hγ1, hγlen⟩ := hJ
    obtain ⟨v', hv'T, hγ'v, hlen', -⟩ := geodesic_data hγ'g
    obtain ⟨v₀, hv₀T, hγv₀, hlen₀, -⟩ := geodesic_data hγg
    rw [hγ'0] at hv'T hγ'v
    rw [hγ0] at hv₀T hγv₀
    have h1I : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
    have e' : v' = v := huniq v' ⟨hv'T, hlen' ▸ hγ'len, by
      rw [← one_smul ℝ v']; exact (hγ'v 1 h1I).symm.trans (congrArg (incl hN) hγ'1)⟩
    have e₀ : v₀ = v := huniq v₀ ⟨hv₀T, hlen₀ ▸ hγlen, by
      rw [← one_smul ℝ v₀]; exact (hγv₀ 1 h1I).symm.trans (congrArg (incl hN) hγ1)⟩
    apply Subtype.ext
    show incl hN (γ t) = incl hN (γ' t)
    rw [hγv₀ t ht, hγ'v t ht, e', e₀]
  · obtain ⟨O₂, hO₂, G₀, hG₀, hG₀p⟩ := h2
    refine ⟨fun p => (⟨p.1, L hN p.1 (G₀ (incl hN p.1, incl hN p.2))⟩ :
      TangentBundle 𝓘(ℝ, Rn n) (Sub hN)), ?_, fun q₁ hq₁ q₂ hq₂ => ?_⟩
    · intro b hb
      rw [contMDiffWithinAt_tangent_iff]
      refine ⟨contMDiff_fst.contMDiffAt.contMDiffWithinAt, ?_⟩
      have hbO := (hG₀p b.1 b.2 hb.1 hb.2).1
      have hinc : ContMDiffAt ((𝓘(ℝ, Rn n)).prod (𝓘(ℝ, Rn n))) 𝓘(ℝ, V × V) ∞
          (fun p : Sub hN × Sub hN => (incl hN p.1, incl hN p.2)) b :=
        ((contMDiff_incl.comp contMDiff_fst).contMDiffAt).prodMk_space
          ((contMDiff_incl.comp contMDiff_snd).contMDiffAt)
      have hG : ContMDiffAt ((𝓘(ℝ, Rn n)).prod (𝓘(ℝ, Rn n))) 𝓘(ℝ, V) ∞
          (fun p : Sub hN × Sub hN => G₀ (incl hN p.1, incl hN p.2)) b :=
        ContDiffAt.comp_contMDiffAt (f := fun p : Sub hN × Sub hN => (incl hN p.1, incl hN p.2))
          (x := b) (hG₀.contDiffAt (hO₂.mem_nhds hbO)) hinc
      refine hG.contMDiffWithinAt.congr (fun p hp => ?_) ?_
      · exact D_L (hG₀p p.1 p.2 hp.1 hp.2).2.1
      · exact D_L (hG₀p b.1 b.2 hb.1 hb.2).2.1
    · obtain ⟨-, hT, hε', hexp⟩ := hG₀p q₁ q₂ hq₁ hq₂
      obtain ⟨γ, hJ, hinit, -⟩ := hshort q₁ q₂ hq₁ _ hT hε' hexp
      exact ⟨rfl, γ, hJ, hinit.2⟩
  · obtain ⟨nc⟩ := h3 q hq
    refine ⟨_, fun x hx => ?_, isNormBall_of_normalCoord (q := q) nc⟩
    obtain ⟨v, ⟨hv, hvε, hexp⟩, -⟩ := h1 q x hq hx
    show incl hN x ∈ nc.U
    rw [← show Morse.exp hN (incl hN q) v = incl hN x from hexp]
    exact nc.exp_mem_U v hv hvε

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
      (∀ pth : ℝ → Bridge.Sub hN, IsPW (n := n) pth 0 1 → pth 0 = q₁ → pth 1 = q₂ →
        arcLen (n := n) γ 0 1 ≤ arcLen (n := n) pth 0 1 ∧
        (arcLen (n := n) γ 0 1 = arcLen (n := n) pth 0 1 →
          pth '' Set.Icc 0 1 = γ '' Set.Icc 0 1)) ∧
      ∀ (pth : ℝ → Bridge.Sub hN) (a b : ℝ), a ≤ b → IsPW (n := n) pth a b → pth a = q₁ →
        pth b = q₂ → arcLen (n := n) γ 0 1 ≤ arcLen (n := n) pth a b

/-- `B_emb` is a special case of B (the induced connection is Levi-Civita, `Bridge.conn_isLC`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

open Emb Bridge in
/-- **A implies B on embedded manifolds**: in a project normal ball of radius `ε' ∈ (L(γ), ε)`
obtained from B's uniformly normal `W` (`Emb.normalCoord_of_isNormBall`), the inequality is A's
`norm_le_pathLength` and the equality clause is `Emb.image_eq_of_eq` (A's `norm_le_pathLength`
plus the project's Lemma 10.6 and crossing lemma). -/
theorem A_to_B_emb : A → B_emb := by
  intro hA V _ _ _ Wc _ _ _ n N hN _ W ε hWo hε hUN q₁ hq₁ q₂ hq₂ γ hJ
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
  have h1I : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  -- any piecewise smooth path from `q₁` to `q₂`
  have key : ∀ (pth : ℝ → Sub hN) (a b : ℝ), IsPW (n := n) pth a b → pth a = q₁ → pth b = q₂ →
      Morse.IsPiecewiseSmooth (incl hN ∘ pth) a b ∧ (∀ t ∈ Icc a b, (incl hN ∘ pth) t ∈ N) ∧
      arcLen (n := n) pth a b = Morse.pathLength (incl hN ∘ pth) a b ∧
      (incl hN ∘ pth) a = Subtype.val (q₁ : ↥N) ∧
      (incl hN ∘ pth) b = Morse.exp hN (Subtype.val (q₁ : ↥N)) v := by
    intro pth a b hpw ha hb
    obtain ⟨hcpw, hcN, hL⟩ := path_data hpw
    refine ⟨hcpw, hcN, hL, ?_, ?_⟩
    · show incl hN (pth a) = incl hN q₁
      rw [ha]
    · show incl hN (pth b) = _
      rw [hb, ← hγ1, hγv 1 h1I, one_smul]
      rfl
  refine ⟨fun pth hpw hp0 hp1 => ?_, fun pth a b hab hpw ha hb => ?_⟩
  · obtain ⟨hcpw, hcN, hL, hca, hcb⟩ := key pth 0 1 hpw hp0 hp1
    have hle := hA.2.2.1 nc hcpw.isAdmissible hcN hca hvT hvε' hcb
    rw [hlen, hL]
    refine ⟨hle, fun heq => image_eq_of_incl ?_⟩
    have hray : (incl hN ∘ γ) '' Icc 0 1 =
        (fun t : ℝ => Morse.exp hN (Subtype.val (q₁ : ↥N)) (t • v)) '' Icc 0 1 :=
      image_congr fun t ht => hγv t ht
    rw [hray]
    rcases eq_or_ne v 0 with rfl | hv0
    · rw [norm_zero] at heq
      have hconst := hcpw.isAdmissible.eq_of_pathLength_eq_zero heq.symm
      ext y
      simp only [mem_image, smul_zero]
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨0, ⟨le_rfl, zero_le_one⟩, by rw [hconst t ht, hca, Morse.exp_zero q₁.2]⟩
      · rintro ⟨τ, -, rfl⟩
        exact ⟨0, ⟨le_rfl, zero_le_one⟩, by rw [hca, Morse.exp_zero q₁.2]⟩
    · exact image_eq_of_eq hA nc hcpw.isAdmissible hcN hca hvT hvε' hcb hv0 heq.symm
  · obtain ⟨hcpw, hcN, hL, hca, hcb⟩ := key pth a b hpw ha hb
    rw [hlen, hL]
    exact hA.2.2.1 nc hcpw.isAdmissible hcN hca hvT hvε' hcb

#rt_check RoundTrip.V7_15.A_to_B_emb [Morse.NormalCoord.radial,
  Morse.NormalCoord.pathLength_exp_smul, Morse.NormalCoord.norm_le_pathLength, Morse.theorem_10_4]

/-- The part of A that B covers: the project's `theorem_10_4` for connected slice submanifolds
modelled on `ℝⁿ` (B assumes `M` connected). -/
def A_10_4 : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (Wc : Type) [NormedAddCommGroup Wc] [NormedSpace ℝ Wc] [FiniteDimensional ℝ Wc] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) Wc N), IsConnected N → ∀ p : N,
    ∃ O : Set V, IsOpen O ∧ (p : V) ∈ O ∧ ∃ ε > 0, ∀ q₁ q₂ : N, (q₁ : V) ∈ O → (q₂ : V) ∈ O →
      ∃ v ∈ Morse.tangentSubspace hN q₁, ‖v‖ < ε ∧ Morse.exp hN q₁ v = q₂ ∧
        Morse.pathLength (fun t : ℝ => Morse.exp hN q₁ (t • v)) 0 1 = ‖v‖ ∧
        ∀ (c : ℝ → V) (a b : ℝ), Morse.IsPiecewiseSmooth c a b → (∀ t ∈ Icc a b, c t ∈ N) →
          c a = q₁ → c b = q₂ → ‖v‖ ≤ Morse.pathLength c a b ∧
            (Morse.pathLength c a b = ‖v‖ →
              c '' Icc a b = (fun t : ℝ => Morse.exp hN q₁ (t • v)) '' Icc 0 1)

theorem A_to_A_10_4 : A → A_10_4 := fun hA _ _ _ _ _ _ _ _ _ _ _ _ p => hA.2.2.2 p

open Emb Bridge in
/-- **B on embedded manifolds implies the project's Theorem 10.4** (connected `N`): the
neighbourhood `N ∩ O` of the project's Lemma 10.3 is uniformly normal in B's sense
(`Emb.isUniformNormal_of`), and paths on `[a, b]` are reparametrized to `[0, 1]` for the equality
clause. -/
theorem B_emb_to_A_10_4 : B_emb → A_10_4 := by
  intro hB V _ _ _ Wc _ _ _ n N hN hconn p
  have : ConnectedSpace (Sub hN) := isConnected_iff_connectedSpace.1 hconn
  obtain ⟨O, hO, hpO, ε, hε, h1, h2, h3⟩ := Morse.lemma_10_3 hN p
  have hUN := isUniformNormal_of h1 h2 h3
  have hWo : IsOpen {x : Sub hN | incl hN x ∈ O} := hO.preimage continuous_subtype_val
  refine ⟨O, hO, hpO, ε, hε, fun q₁' q₂' hq₁' hq₂' => ?_⟩
  obtain ⟨q₁, rfl⟩ : ∃ q : Sub hN, q = q₁' := ⟨q₁', rfl⟩
  obtain ⟨q₂, rfl⟩ : ∃ q : Sub hN, q = q₂' := ⟨q₂', rfl⟩
  have hq₁ : q₁ ∈ {x : Sub hN | incl hN x ∈ O} := hq₁'
  have hq₂ : q₂ ∈ {x : Sub hN | incl hN x ∈ O} := hq₂'
  obtain ⟨v, ⟨hv, hvε, hexp⟩, -⟩ := h1 q₁ q₂ hq₁' hq₂'
  obtain ⟨nc⟩ := h3 q₁ hq₁'
  obtain ⟨γ, hγ, h0, -, h1γ, hlen⟩ := short_of_mem_expDom hv (nc.mem_expDom v hv hvε)
  have hJ : JoinsShort (conn (hN := hN)) ε γ q₁ q₂ :=
    ⟨hγ, h0, Subtype.ext (h1γ.trans hexp), hlen ▸ hvε⟩
  obtain ⟨v', hv'T, hγv', hlen', hvD'⟩ := geodesic_data hγ
  rw [h0] at hγv' hv'T
  have hv' : v' = v := by
    have := hγv' 1 ⟨zero_le_one, le_rfl⟩
    rw [one_smul] at this
    rw [h1 q₁ q₂ hq₁' hq₂' |>.unique ⟨hv'T, hlen' ▸ hlen ▸ hvε, this.symm.trans h1γ |>.trans hexp⟩
      ⟨hv, hvε, hexp⟩]
  rw [hv'] at hγv'
  obtain ⟨hP1, hP2⟩ := hB V Wc n N hN _ ε hWo hε hUN q₁ hq₁ q₂ hq₂ γ hJ
  have hray : EqOn (incl hN ∘ γ) (fun t : ℝ => Morse.exp hN (Subtype.val (q₁ : ↥N)) (t • v))
      (Icc 0 1) := fun t ht => hγv' t ht
  refine ⟨v, hv, hvε, hexp, ?_, fun c a b hc hcN ha hb => ?_⟩
  · rw [← pathLength_congr zero_le_one hray, ← hlen]
    exact (arcLen_eq γ 0 1).symm
  -- the path in `N`
  have hab : a ≤ b := hc.1
  have hle : ‖v‖ ≤ Morse.pathLength c a b := by
    have hpw := isPW_lift (n := n) hc hcN q₁
    have heqc : EqOn (incl hN ∘ lift c q₁) c (Icc a b) := fun t ht => incl_lift q₁ (hcN t ht)
    have := hP2 (lift c q₁) a b hab hpw (Subtype.ext ((heqc ⟨le_rfl, hab⟩).trans ha))
      (Subtype.ext ((heqc ⟨hab, le_rfl⟩).trans hb))
    rw [hlen, show arcLen (n := n) (lift c q₁) a b = Morse.pathLength (incl hN ∘ lift c q₁) a b from
      arcLen_eq _ a b, pathLength_congr hab heqc] at this
    exact this
  refine ⟨hle, fun heq => ?_⟩
  rcases eq_or_lt_of_le hab with rfl | hlt
  · -- a constant path: `q₁ = q₂`, `v = 0`
    have hv0 : v = 0 := by
      simp only [Morse.pathLength, intervalIntegral.integral_same] at heq
      exact norm_eq_zero.1 heq.symm
    subst hv0
    ext y
    simp only [mem_image, smul_zero, Icc_self, mem_singleton_iff, exists_eq_left]
    constructor
    · rintro rfl
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, by rw [ha, Morse.exp_zero q₁.2]⟩
    · rintro ⟨τ, -, rfl⟩
      rw [ha, Morse.exp_zero q₁.2]
  · -- reparametrize to `[0, 1]`
    set c' : ℝ → V := fun t => c ((b - a) * t + a) with hc'
    have hc'pw := isPiecewiseSmooth_reparam hlt hc
    have hc'N : ∀ t ∈ Icc (0 : ℝ) 1, c' t ∈ N := fun t ht =>
      hcN _ ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
    have hpw := isPW_lift (n := n) hc'pw hc'N q₁
    have heqc : EqOn (incl hN ∘ lift c' q₁) c' (Icc 0 1) := fun t ht => incl_lift q₁ (hc'N t ht)
    have hc'0 : c' 0 = incl hN q₁ := by simp only [hc', mul_zero, zero_add]; exact ha
    have hc'1 : c' 1 = incl hN q₂ := by simp only [hc', mul_one, sub_add_cancel]; exact hb
    obtain ⟨-, himg⟩ := hP1 (lift c' q₁) hpw
      (Subtype.ext ((heqc ⟨le_rfl, zero_le_one⟩).trans hc'0))
      (Subtype.ext ((heqc ⟨zero_le_one, le_rfl⟩).trans hc'1))
    have hlen' : arcLen (n := n) γ 0 1 = arcLen (n := n) (lift c' q₁) 0 1 := by
      rw [hlen, show arcLen (n := n) (lift c' q₁) 0 1 = Morse.pathLength (incl hN ∘ lift c' q₁) 0 1
        from arcLen_eq _ 0 1, pathLength_congr zero_le_one heqc, pathLength_reparam c hlt, heq]
    have himg' := congrArg (fun s => incl hN '' s) (himg hlen')
    simp only [Set.image_image] at himg'
    rw [← image_reparam c hlt, ← image_congr heqc, ← image_congr hray]
    exact himg'

#rt_check RoundTrip.V7_15.B_emb_to_A_10_4 [Morse.NormalCoord.radial,
  Morse.NormalCoord.pathLength_exp_smul, Morse.NormalCoord.norm_le_pathLength, Morse.theorem_10_4]
#rt_overlap RoundTrip.V7_15.B_emb_to_A_10_4 [Morse.NormalCoord.radial,
  Morse.NormalCoord.pathLength_exp_smul, Morse.NormalCoord.norm_le_pathLength, Morse.theorem_10_4]

end RoundTrip.V7_15
