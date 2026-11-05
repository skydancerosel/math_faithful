import Morse
import RoundTrip.Check
import RoundTrip.Blind.V7_13
import RoundTrip.Bridge

open Set Filter Topology
open scoped ContDiff Manifold RealInnerProductSpace

namespace RoundTrip.V7_13

/-- The project's statement (universes instantiated at 0), for a slice submanifold `N ⊆ V` with
the induced metric and a normal radius `ε` at `q` (`Morse.NormalCoord`: `exp_q` maps
`B_ε(0) ∩ T_qN` diffeomorphically onto `N ∩ U`, with smooth extensions `F` of `exp_q` and `G` of
its inverse): (pointwise Lemma 10.6) for a curve `c` in `N ∩ U − {q}` differentiable at `t`, the
radius `ρ = ‖G ∘ c‖` has `|ρ'(t)| ≤ ‖c'(t)‖`, and if `ρ'(t) = ‖c'(t)‖` the direction `G(c)/ρ` has
derivative `0` at `t`; (Lemma 10.6) for an admissible path `c` in `N ∩ U − {q}` on `[a, b]`,
`ρ(b) − ρ(a) ≤ L(c)`; and with equality the direction `G(c)/ρ` is constant on `[a, b]`. -/
def A : Prop :=
  type_of% @Morse.NormalCoord.hasDerivAt_radius.{0,0,0} ∧
    type_of% @Morse.NormalCoord.radius_sub_le_pathLength.{0,0,0} ∧
    type_of% @Morse.NormalCoord.direction_eq_of_pathLength_eq.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.NormalCoord.hasDerivAt_radius, @Morse.NormalCoord.radius_sub_le_pathLength,
    @Morse.NormalCoord.direction_eq_of_pathLength_eq⟩

/-! Neither `A → B` nor `B → A` is proved; see `V7_13.json`. B quantifies over abstract connected
Hausdorff `ℝⁿ`-manifolds with an arbitrary smooth Mathlib `RiemannianBundle` metric and an
arbitrary Levi-Civita `CovariantDerivative` (Milnor's axioms), while A only concerns slice
submanifolds `N ⊆ V` with the induced metric; conversely A has the pointwise form
(`hasDerivAt_radius`) and covers admissible (not only piecewise smooth) paths.

## The embedded special case

Below, B is specialized to `M = ↥N` (`RoundTrip.Bridge.Sub hN`) with the induced metric and the
induced Levi-Civita connection `Bridge.conn` (`B_emb`). The `Emb` section proves the missing
dictionary entries between B's normal balls (`IsNormBall`: `exp_q` a diffeomorphism of the
Riemannian `ε`-ball of `T_qN` onto an open `U ⊆ N`) and the project's `NormalCoord`:
* `Emb.isNormBall_of_normalCoord`: a `NormalCoord hN q ε` gives `IsNormBall conn q ε (N ∩ U)`;
* `Emb.normalCoord_of_isNormBall`: `IsNormBall conn q ε U` gives `NormalCoord hN q ε'` for every
  `0 < ε' < ε` (the smooth extension `G` of the inverse to an open set of `V` is glued with a
  partition of unity from slice-chart extensions near the compact set `exp_q(closedBall ε'')`,
  `ε' < ε'' < ε`; the radius is shrunk because the gluing lemma wants a compact set).
These lemmas are repeated in `V7_14`, `V7_15`, `V7_16` (Items files do not import each other).
On embedded manifolds B is exactly the piecewise smooth part of A (`B_emb_iff_A_pw`). -/

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

/-- Increase of the radius along an admissible path in a punctured normal ball: if the length on
every subinterval bounds the increase of the radius (Lemma 10.6) and the total length equals
`ρ(b) − ρ(a)`, the radius `ρ = ‖G ∘ c‖` is nondecreasing. -/
theorem monotoneOn_of_eq {q : N} {ε : ℝ} (nc : Morse.NormalCoord hN q ε)
    {c : ℝ → V} {a b : ℝ} (hc : Morse.IsAdmissible c a b)
    (hsub : ∀ x y, a ≤ x → x ≤ y → y ≤ b →
      ‖nc.G (c y)‖ - ‖nc.G (c x)‖ ≤ Morse.pathLength c x y)
    (heq : Morse.pathLength c a b = ‖nc.G (c b)‖ - ‖nc.G (c a)‖) :
    MonotoneOn (fun t => ‖nc.G (c t)‖) (Icc a b) := by
  intro s hs t ht hst
  have h1 := hsub a s le_rfl hs.1 hs.2
  have h2 := hsub s b hs.1 hs.2 le_rfl
  have h3 := hsub a t le_rfl ht.1 ht.2
  have h4 := hsub t b ht.1 ht.2 le_rfl
  have e1 := hc.pathLength_add hs
  have e2 := hc.pathLength_add ht
  have hle := (hc.mono le_rfl ht.1 ht.2).pathLength_le le_rfl hs.1 hst
  simp only
  linarith

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
    ∀ (pth : ℝ → Bridge.Sub hN) (a b : ℝ), a ≤ b → IsPW (n := n) pth a b →
      (∀ t ∈ Set.Icc a b, pth t ∈ U \ {q}) →
    ∀ (r : ℝ → ℝ) (v : ℝ → Rn n),
      (∀ t ∈ Set.Icc a b, 0 < r t ∧ r t < ε ∧ nrm q (v t) = 1 ∧
        pth t = expMap (Bridge.conn (hN := hN)) q (r t • v t)) →
      |r b - r a| ≤ arcLen (n := n) pth a b ∧
      (arcLen (n := n) pth a b = |r b - r a| →
        (MonotoneOn r (Set.Icc a b) ∨ AntitoneOn r (Set.Icc a b)) ∧ ∀ t ∈ Set.Icc a b, v t = v a)

/-- `B_emb` is a special case of B (the induced connection is Levi-Civita, `Bridge.conn_isLC`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- The part of A that B covers: A's integrated Lemma 10.6 (`radius_sub_le_pathLength` and
`direction_eq_of_pathLength_eq`) for piecewise smooth (not merely admissible) paths, for connected
slice submanifolds modelled on `ℝⁿ` (B assumes `M` connected). -/
def A_pw : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N), IsConnected N →
    ∀ (q : N) (ε : ℝ) (nc : Morse.NormalCoord hN q ε) (c : ℝ → V) (a b : ℝ),
      Morse.IsPiecewiseSmooth c a b → (∀ t ∈ Icc a b, c t ∈ N ∧ c t ∈ nc.U ∧ c t ≠ q) →
      ‖nc.G (c b)‖ - ‖nc.G (c a)‖ ≤ Morse.pathLength c a b ∧
      (Morse.pathLength c a b = ‖nc.G (c b)‖ - ‖nc.G (c a)‖ →
        ∀ t ∈ Icc a b, ‖nc.G (c t)‖⁻¹ • nc.G (c t) = ‖nc.G (c b)‖⁻¹ • nc.G (c b))

theorem A_to_A_pw : A → A_pw := fun hA _ _ _ _ _ _ _ _ _ _ _ _ _ _ nc _ _ _ hc hmem =>
  ⟨hA.2.1 nc hc.isAdmissible hmem, hA.2.2 nc hc.isAdmissible hmem⟩

open Emb Bridge in
/-- **The piecewise smooth part of A implies B on embedded manifolds** (A's Lemma 10.6 and its
equality clause, through `Emb.normalCoord_of_isNormBall` with a radius `ε' < ε` covering the compact
path). -/
theorem A_pw_to_B_emb : A_pw → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN hcs q ε U hε hB pth a b hab hpw hU r v hrv
  have hconn : IsConnected N := isConnected_iff_connectedSpace.2 hcs
  obtain ⟨hUo, hexp, hinj, himg, hsmooth, g, hg, hgexp⟩ := hB
  set c : ℝ → V := incl hN ∘ pth with hc_def
  have hcpw : Morse.IsPiecewiseSmooth c a b := isPiecewiseSmooth_of_isPW hpw
  have hca : Morse.IsAdmissible c a b := hcpw.isAdmissible
  have hL : ∀ x y, arcLen (n := n) pth x y = Morse.pathLength c x y := fun x y => arcLen_eq pth x y
  -- `r t • v t` is in the ball, and `g (pth t) = r t • v t`
  have hnv : ∀ t ∈ Icc a b, ‖D hN q (v t)‖ = 1 := fun t ht => by
    rw [← nrm_eq]; exact (hrv t ht).2.2.1
  have hDrv : ∀ t ∈ Icc a b, ‖D hN q (r t • v t)‖ = r t := fun t ht => by
    rw [map_smul, norm_smul, hnv t ht, mul_one, Real.norm_eq_abs, abs_of_pos (hrv t ht).1]
  have hball : ∀ t ∈ Icc a b, r t • v t ∈ tball (n := n) q ε := fun t ht => by
    rw [mem_tball_iff, hDrv t ht]; exact (hrv t ht).2.1
  have hgp : ∀ t ∈ Icc a b, g (pth t) = r t • v t := fun t ht => by
    rw [(hrv t ht).2.2.2]; exact hgexp _ (hball t ht)
  -- the radii are bounded by some `ε₁ < ε` (compactness)
  have hpc : ContinuousOn pth (Icc a b) := isInducing_incl.continuousOn_iff.2 hcpw.2.1
  have hrc : ContinuousOn (fun t => ‖D hN q (g (pth t))‖) (Icc a b) :=
    ((D hN q).continuous.norm.comp_continuousOn
      (hg.continuousOn.comp hpc fun t ht => (hU t ht).1))
  obtain ⟨t₀, ht₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hab) hrc
  have hreq : ∀ t ∈ Icc a b, ‖D hN q (g (pth t))‖ = r t := fun t ht => by
    rw [hgp t ht, hDrv t ht]
  have hr₀ : ∀ t ∈ Icc a b, r t ≤ r t₀ := fun t ht => by
    rw [← hreq t ht, ← hreq t₀ ht₀]; exact hmax ht
  set ε' := (r t₀ + ε) / 2 with hε'
  have hε'pos : 0 < ε' := by have := (hrv t₀ ht₀).1; rw [hε']; linarith
  have hε'lt : ε' < ε := by have := (hrv t₀ ht₀).2.1; rw [hε']; linarith
  have hrε' : ∀ t ∈ Icc a b, r t < ε' := fun t ht => by
    have := hr₀ t ht; have := (hrv t₀ ht₀).2.1; rw [hε']; linarith
  obtain ⟨nc⟩ := normalCoord_of_isNormBall ⟨hUo, hexp, hinj, himg, hsmooth, g, hg, hgexp⟩ hε'pos hε'lt
  -- the path in the project's normal coordinates
  have hcG : ∀ t ∈ Icc a b, c t ∈ nc.U ∧ nc.G (c t) = D hN q (r t • v t) := fun t ht => by
    have hT := D_mem q (r t • v t)
    have hn : ‖D hN q (r t • v t)‖ < ε' := by rw [hDrv t ht]; exact hrε' t ht
    have hct : c t = Morse.exp hN (Subtype.val (q : ↥N)) (D hN q (r t • v t)) := by
      show incl hN (pth t) = _
      rw [(hrv t ht).2.2.2]; exact incl_expMap (hexp _ (hball t ht))
    rw [hct]
    exact ⟨nc.exp_mem_U _ hT hn, nc.G_exp _ hT hn⟩
  have hρ : ∀ t ∈ Icc a b, ‖nc.G (c t)‖ = r t := fun t ht => by
    rw [(hcG t ht).2, hDrv t ht]
  have hdir : ∀ t ∈ Icc a b, ‖nc.G (c t)‖⁻¹ • nc.G (c t) = D hN q (v t) := fun t ht => by
    rw [hρ t ht, (hcG t ht).2, map_smul, smul_smul, inv_mul_cancel₀ (hrv t ht).1.ne', one_smul]
  have hmem : ∀ t ∈ Icc a b, c t ∈ N ∧ c t ∈ nc.U ∧ c t ≠ Subtype.val (q : ↥N) := fun t ht =>
    ⟨(pth t).2, (hcG t ht).1, fun h => (hU t ht).2 (Subtype.ext h)⟩
  have hAp := hA V W n N hN hconn q ε' nc
  have hsub : ∀ x y, a ≤ x → x ≤ y → y ≤ b →
      ‖nc.G (c y)‖ - ‖nc.G (c x)‖ ≤ Morse.pathLength c x y := fun x y hx hxy hy =>
    (hAp c x y (hcpw.mono hx hxy hy) fun u hu => hmem u ⟨hx.trans hu.1, hu.2.trans hy⟩).1
  -- the reversed path
  set c' : ℝ → V := fun t => c (a + b - t) with hc'
  have hrev : ∀ t ∈ Icc a b, a + b - t ∈ Icc a b := fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hc'pw : Morse.IsPiecewiseSmooth c' a b := hcpw.reverse
  have hc'a : Morse.IsAdmissible c' a b := hc'pw.isAdmissible
  have hmem' : ∀ t ∈ Icc a b, c' t ∈ N ∧ c' t ∈ nc.U ∧ c' t ≠ Subtype.val (q : ↥N) :=
    fun t ht => hmem _ (hrev t ht)
  have hsub' : ∀ x y, a ≤ x → x ≤ y → y ≤ b →
      ‖nc.G (c' y)‖ - ‖nc.G (c' x)‖ ≤ Morse.pathLength c' x y := fun x y hx hxy hy =>
    (hAp c' x y (hc'pw.mono hx hxy hy) fun u hu => hmem' u ⟨hx.trans hu.1, hu.2.trans hy⟩).1
  have hL' : Morse.pathLength c' a b = Morse.pathLength c a b := Morse.pathLength_reverse c a b
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hbI : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have h1 := (hAp c a b hcpw hmem).1
  have h2 := (hAp c' a b hc'pw hmem').1
  simp only [hc', show a + b - b = a by ring, show a + b - a = b by ring] at h2
  rw [hρ b hbI, hρ a haI] at h1 h2
  rw [hL', ← hL] at h2
  rw [← hL] at h1
  refine ⟨abs_sub_le_iff.2 ⟨h1, h2⟩, fun heq => ?_⟩
  rcases le_total (r a) (r b) with hle | hle
  · -- the radius increases
    rw [abs_of_nonneg (sub_nonneg.2 hle), hL] at heq
    have heq' : Morse.pathLength c a b = ‖nc.G (c b)‖ - ‖nc.G (c a)‖ := by
      rw [hρ b hbI, hρ a haI]; exact heq
    refine ⟨Or.inl ?_, fun t ht => ?_⟩
    · have := monotoneOn_of_eq nc hca hsub heq'
      exact this.congr fun t ht => hρ t ht
    · have h3 := (hAp c a b hcpw hmem).2 heq' t ht
      have h4 := (hAp c a b hcpw hmem).2 heq' a haI
      rw [hdir t ht, hdir b hbI] at h3
      rw [hdir a haI, hdir b hbI] at h4
      exact D_injective q (h3.trans h4.symm)
  · -- the radius decreases: the reversed path
    rw [abs_of_nonpos (sub_nonpos.2 hle), hL, ← hL'] at heq
    have heq' : Morse.pathLength c' a b = ‖nc.G (c' b)‖ - ‖nc.G (c' a)‖ := by
      simp only [hc', show a + b - b = a by ring, show a + b - a = b by ring]
      rw [hρ b hbI, hρ a haI]; rw [heq]; ring
    refine ⟨Or.inr ?_, fun t ht => ?_⟩
    · have hm := monotoneOn_of_eq nc hc'a hsub' heq'
      intro s hs t ht hst
      have := hm (hrev t ht) (hrev s hs) (by linarith)
      simp only [hc', show a + b - (a + b - t) = t by ring,
        show a + b - (a + b - s) = s by ring] at this
      rw [hρ t ht, hρ s hs] at this
      exact this
    · have h3 := (hAp c' a b hc'pw hmem').2 heq' (a + b - t) (hrev t ht)
      simp only [hc', show a + b - (a + b - t) = t by ring, show a + b - b = a by ring] at h3
      rw [hdir t ht, hdir a haI] at h3
      exact D_injective q h3

/-- **A implies B on embedded manifolds** (through `A_pw`). -/
theorem A_to_B_emb : A → B_emb := fun hA => A_pw_to_B_emb (A_to_A_pw hA)

open Emb Bridge in
/-- **B on embedded manifolds implies A's integrated Lemma 10.6 for piecewise smooth paths**
(connected `N`), through `Emb.isNormBall_of_normalCoord`, with `r = ‖G ∘ c‖`, `v = G(c)/r`. -/
theorem B_emb_to_A_pw : B_emb → A_pw := by
  intro hB V _ _ _ W _ _ _ n N hN hconn q₀ ε nc c a b hc hmem
  obtain ⟨q, rfl⟩ : ∃ q : Sub hN, q = q₀ := ⟨q₀, rfl⟩
  have : ConnectedSpace (Sub hN) := isConnected_iff_connectedSpace.1 hconn
  have hab : a ≤ b := hc.1
  have hNB := isNormBall_of_normalCoord (q := q) nc
  set pth : ℝ → Sub hN := lift c q with hpth
  have hpw : IsPW (n := n) pth a b := isPW_lift hc (fun t ht => (hmem t ht).1) q
  have heqc : ∀ t ∈ Icc a b, incl hN (pth t) = c t := fun t ht => incl_lift (q : Sub hN) (hmem t ht).1
  have hlen : arcLen (n := n) pth a b = Morse.pathLength c a b := by
    rw [show arcLen (n := n) pth a b = RoundTrip.BridgePrelude.arcLen (n := n) pth a b from rfl,
      arcLen_eq, pathLength_congr (c := incl hN ∘ pth) hab fun t ht => heqc t ht]
  have hpU : ∀ t ∈ Icc a b, pth t ∈ {x : Sub hN | incl hN x ∈ nc.U} \ {(q : Sub hN)} := fun t ht => by
    refine ⟨?_, fun h => (hmem t ht).2.2 ?_⟩
    · show incl hN (pth t) ∈ nc.U
      rw [heqc t ht]; exact (hmem t ht).2.1
    · rw [← heqc t ht, h]; rfl
  set r : ℝ → ℝ := fun t => ‖nc.G (c t)‖ with hr
  set v : ℝ → Rn n := fun t => L hN q (‖nc.G (c t)‖⁻¹ • nc.G (c t)) with hv
  have hGT : ∀ t ∈ Icc a b, nc.G (c t) ∈ Morse.tangentSubspace hN q :=
    fun t ht => nc.G_mem _ (hmem t ht).2.1 (hmem t ht).1
  have hG0 : ∀ t ∈ Icc a b, nc.G (c t) ≠ 0 :=
    fun t ht => nc.G_ne_zero (hmem t ht).2.1 (hmem t ht).1 (hmem t ht).2.2
  have hDv : ∀ t ∈ Icc a b, D hN q (v t) = ‖nc.G (c t)‖⁻¹ • nc.G (c t) := fun t ht =>
    D_L (Submodule.smul_mem _ _ (hGT t ht))
  have hrv : ∀ t ∈ Icc a b, 0 < r t ∧ r t < ε ∧ nrm (M := Sub hN) q (v t) = 1 ∧
      pth t = expMap (conn (hN := hN)) q (r t • v t) := by
    intro t ht
    have hpos : 0 < ‖nc.G (c t)‖ := norm_pos_iff.2 (hG0 t ht)
    refine ⟨hpos, nc.norm_G_lt _ (hmem t ht).2.1 (hmem t ht).1, ?_, ?_⟩
    · refine (nrm_eq (hN := hN) q (v t)).trans ?_
      rw [hDv t ht, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']
    · have hrv' : D hN q (r t • v t) = nc.G (c t) := by
        rw [map_smul, hDv t ht, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
      have hball : r t • v t ∈ tball (n := n) (M := Sub hN) q ε := by
        rw [mem_tball_iff, hrv']; exact nc.norm_G_lt _ (hmem t ht).2.1 (hmem t ht).1
      apply Subtype.ext
      show incl hN (pth t) = incl hN (expMap _ q _)
      rw [incl_expMap (hNB.2.1 _ hball), hrv', heqc t ht]
      exact (nc.exp_G _ (hmem t ht).2.1 (hmem t ht).1).symm
  obtain ⟨h1, h2⟩ := hB V W n N hN q ε _ nc.pos hNB pth a b hab hpw hpU r v hrv
  rw [hlen] at h1 h2
  refine ⟨(le_abs_self _).trans h1, fun heq => ?_⟩
  have habs : Morse.pathLength c a b = |r b - r a| := by
    have := (le_abs_self (r b - r a)).trans h1
    rw [heq] at h1 ⊢
    exact (le_antisymm h1 (le_abs_self _)).symm
  have hconst := (h2 habs).2
  intro t ht
  have e1 := congrArg (D hN q) (hconst t ht)
  have e2 := congrArg (D hN q) (hconst b ⟨hab, le_rfl⟩)
  rw [hDv t ht, hDv a ⟨le_rfl, hab⟩] at e1
  rw [hDv b ⟨hab, le_rfl⟩, hDv a ⟨le_rfl, hab⟩] at e2
  exact e1.trans e2.symm

/-- **On embedded manifolds, B is exactly the piecewise smooth part of A.** -/
theorem B_emb_iff_A_pw : B_emb ↔ A_pw := ⟨B_emb_to_A_pw, A_pw_to_B_emb⟩

#rt_check RoundTrip.V7_13.A_to_B_emb [Morse.NormalCoord.hasDerivAt_radius,
  Morse.NormalCoord.radius_sub_le_pathLength, Morse.NormalCoord.direction_eq_of_pathLength_eq]
#rt_check RoundTrip.V7_13.B_emb_to_A_pw [Morse.NormalCoord.hasDerivAt_radius,
  Morse.NormalCoord.radius_sub_le_pathLength, Morse.NormalCoord.direction_eq_of_pathLength_eq]
#rt_overlap RoundTrip.V7_13.B_emb_to_A_pw [Morse.NormalCoord.hasDerivAt_radius,
  Morse.NormalCoord.radius_sub_le_pathLength, Morse.NormalCoord.direction_eq_of_pathLength_eq]

end RoundTrip.V7_13
