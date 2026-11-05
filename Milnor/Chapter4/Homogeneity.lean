import Milnor.Chapter4.BumpDiffeo

/-!
# The Homogeneity Lemma (Milnor, chapter 4)

Let `N` be a connected smooth manifold without boundary.  For any two points `y, z` there is a
diffeomorphism `h : N → N`, smoothly isotopic to the identity, with `h y = z`.

We define `Isotopic J y z` to mean that such an `h` exists together with a smooth map
`H : N × ℝ → N` with `H(·,0) = id` and `H(·,1) = h`.  This relation is reflexive, transitive and
symmetric; each point is isotopic to every point of a chart neighbourhood (moving it by a
bump-function diffeomorphism of the model space, transported through the chart); so the
isotopy classes are open, and connectedness finishes the argument.
-/

open Set Metric Function Filter Topology
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

open Milnor.Bump

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N]

open Classical in
/-- Transport of a self-map `g` of the model space through the extended chart at `y`:
`p ↦ e⁻¹(g(e p))` on the chart domain, identity elsewhere. -/
def transport (J : ModelWithCorners ℝ F H) (y : N) (g : F → F) (p : N) : N :=
  if p ∈ (extChartAt J y).source then (extChartAt J y).symm (g (extChartAt J y p)) else p

theorem transport_of_mem {y : N} {g : F → F} {p : N} (hp : p ∈ (extChartAt J y).source) :
    transport J y g p = (extChartAt J y).symm (g (extChartAt J y p)) := if_pos hp

theorem transport_of_notMem {y : N} {g : F → F} {p : N} (hp : p ∉ (extChartAt J y).source) :
    transport J y g p = p := if_neg hp

theorem transport_id (y : N) (p : N) : transport J y id p = p := by
  unfold transport; split_ifs with hp
  · exact (extChartAt J y).left_inv hp
  · rfl

theorem transport_eq_self_of_notMem_image {y : N} {g : F → F} {K : Set F}
    (hgK : ∀ u, u ∉ K → g u = u) {p : N} (hp : p ∉ (extChartAt J y).symm '' K) :
    transport J y g p = p := by
  unfold transport; split_ifs with hs
  · have : extChartAt J y p ∉ K := fun h => hp ⟨_, h, (extChartAt J y).left_inv hs⟩
    rw [hgK _ this, (extChartAt J y).left_inv hs]
  · rfl

theorem transport_transport {y : N} {g g' : F → F}
    (hg : ∀ u ∈ (extChartAt J y).target, g u ∈ (extChartAt J y).target)
    (hgg' : ∀ u, g' (g u) = u) (p : N) : transport J y g' (transport J y g p) = p := by
  by_cases hp : p ∈ (extChartAt J y).source
  · rw [transport_of_mem hp]
    have h1 : g (extChartAt J y p) ∈ (extChartAt J y).target :=
      hg _ ((extChartAt J y).map_source hp)
    rw [transport_of_mem ((extChartAt J y).map_target h1), (extChartAt J y).right_inv h1, hgg',
      (extChartAt J y).left_inv hp]
  · rw [transport_of_notMem hp, transport_of_notMem hp]

theorem isClosed_image_symm_of_isCompact {y : N} [T2Space N] {K : Set F} (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt J y).target) : IsClosed ((extChartAt J y).symm '' K) :=
  (hK.image_of_continuousOn ((continuousOn_extChartAt_symm y).mono hKt)).isClosed

theorem notMem_image_symm_of_notMem_source {y : N} {K : Set F}
    (hKt : K ⊆ (extChartAt J y).target) {p : N} (hp : p ∉ (extChartAt J y).source) :
    p ∉ (extChartAt J y).symm '' K :=
  fun ⟨u, hu, hup⟩ => hp (hup ▸ (extChartAt J y).map_target (hKt hu))

/-- Smoothness of the transport of a smooth map which is the identity outside a compact subset
of the chart target. -/
theorem contMDiff_transport [T2Space N] {y : N} {g : F → F} (hg : ContDiff ℝ ∞ g) {K : Set F}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt J y).target) (hgK : ∀ u, u ∉ K → g u = u)
    (hgt : ∀ u ∈ (extChartAt J y).target, g u ∈ (extChartAt J y).target) :
    ContMDiff J J ∞ (transport J y g) := by
  intro p
  by_cases hp : p ∈ (extChartAt J y).source
  · have hp' : (chartAt H y).source ∈ 𝓝 p :=
      (chartAt H y).open_source.mem_nhds (by rwa [extChartAt_source] at hp)
    have h1 : ContMDiffAt J 𝓘(ℝ, F) ∞ (extChartAt J y) p :=
      (contMDiffOn_extChartAt (x := y)).contMDiffAt hp'
    have h2 : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ g (extChartAt J y p) := hg.contMDiff.contMDiffAt
    have h3 : ContMDiffAt 𝓘(ℝ, F) J ∞ (extChartAt J y).symm (g (extChartAt J y p)) :=
      (contMDiffOn_extChartAt_symm y).contMDiffAt
        (extChartAt_target_mem_nhds' (hgt _ ((extChartAt J y).map_source hp)))
    refine (h3.comp p (h2.comp p h1)).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_extChartAt_source y).mem_nhds hp] with q hq
    exact transport_of_mem hq
  · have hC := isClosed_image_symm_of_isCompact (J := J) hK hKt
    have hpC := notMem_image_symm_of_notMem_source hKt hp
    refine contMDiffAt_id.congr_of_eventuallyEq ?_
    filter_upwards [hC.isOpen_compl.mem_nhds hpC] with q hq
    exact transport_eq_self_of_notMem_image hgK hq

/-- Joint smoothness in `(p, t)` of the transported family `u ↦ u + φ(u) • (σ(t) • c)`,
`σ` the smooth transition function. -/
theorem contMDiff_transport_shift [T2Space N] {y : N} {φ : F → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (c : F) {K : Set F} (hK : IsCompact K) (hKt : K ⊆ (extChartAt J y).target)
    (hφK : ∀ u, u ∉ K → φ u = 0)
    (hgt : ∀ s : ℝ, ∀ u ∈ (extChartAt J y).target,
      shift φ (Real.smoothTransition s • c) u ∈ (extChartAt J y).target) :
    ContMDiff (J.prod 𝓘(ℝ, ℝ)) J ∞
      (fun q : N × ℝ => transport J y (shift φ (Real.smoothTransition q.2 • c)) q.1) := by
  rintro ⟨p, t⟩
  by_cases hp : p ∈ (extChartAt J y).source
  · have hp' : (chartAt H y).source ∈ 𝓝 p :=
      (chartAt H y).open_source.mem_nhds (by rwa [extChartAt_source] at hp)
    have h1 : ContMDiffAt (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞
        (fun q : N × ℝ => extChartAt J y q.1) (p, t) :=
      ((contMDiffOn_extChartAt (x := y)).contMDiffAt hp').comp (p, t) contMDiffAt_fst
    have hφ' : ContMDiffAt (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun q : N × ℝ => φ (extChartAt J y q.1)) (p, t) :=
      hφ.contMDiff.contMDiffAt.comp (p, t) h1
    have hs : ContMDiffAt (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun q : N × ℝ => Real.smoothTransition q.2) (p, t) :=
      (Real.smoothTransition.contDiff (n := ⊤)).contMDiff.contMDiffAt.comp (p, t) contMDiffAt_snd
    have h2 : ContMDiffAt (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞
        (fun q : N × ℝ => shift φ (Real.smoothTransition q.2 • c) (extChartAt J y q.1))
        (p, t) :=
      h1.add (hφ'.smul (hs.smul contMDiffAt_const))
    have h3 : ContMDiffAt 𝓘(ℝ, F) J ∞ (extChartAt J y).symm
        (shift φ (Real.smoothTransition t • c) (extChartAt J y p)) :=
      (contMDiffOn_extChartAt_symm y).contMDiffAt
        (extChartAt_target_mem_nhds' (hgt _ _ ((extChartAt J y).map_source hp)))
    refine (h3.comp (p, t) h2).congr_of_eventuallyEq ?_
    filter_upwards [((isOpen_extChartAt_source y).prod isOpen_univ).mem_nhds
      ⟨hp, mem_univ _⟩] with q hq
    exact transport_of_mem hq.1
  · have hC := isClosed_image_symm_of_isCompact (J := J) hK hKt
    have hpC := notMem_image_symm_of_notMem_source hKt hp
    refine contMDiffAt_fst.congr_of_eventuallyEq ?_
    filter_upwards [(hC.isOpen_compl.prod isOpen_univ).mem_nhds ⟨hpC, mem_univ _⟩] with q hq
    exact transport_eq_self_of_notMem_image (fun u hu => shift_of_eq_zero (hφK u hu)) hq.1

/-- `y` and `z` are *isotopic*: there is a diffeomorphism `h` of `N` with `h y = z` and a smooth
map `H : N × ℝ → N` with `H(·, 0) = id`, `H(·, 1) = h`, and every `H(·, t)` a diffeomorphism
(a smooth isotopy from the identity to `h`, as in Milnor). -/
def Isotopic (J : ModelWithCorners ℝ F H) (y z : N) : Prop :=
  ∃ (h : N ≃ₘ⟮J, J⟯ N) (Hm : N × ℝ → N), ContMDiff (J.prod 𝓘(ℝ, ℝ)) J ∞ Hm ∧
    (∀ x, Hm (x, 0) = x) ∧ (∀ x, Hm (x, 1) = h x) ∧ h y = z ∧
    ∀ t, ∃ ht : N ≃ₘ⟮J, J⟯ N, ∀ x, Hm (x, t) = ht x

theorem Isotopic.refl (y : N) : Isotopic J y y :=
  ⟨Diffeomorph.refl J N ∞, Prod.fst, contMDiff_fst, fun _ => rfl, fun _ => rfl, rfl,
    fun _ => ⟨Diffeomorph.refl J N ∞, fun _ => rfl⟩⟩

theorem Isotopic.trans {y z w : N} (h₁ : Isotopic J y z) (h₂ : Isotopic J z w) :
    Isotopic J y w := by
  obtain ⟨h₁, H₁, hH₁, h₁0, h₁1, hy, s₁⟩ := h₁
  obtain ⟨h₂, H₂, hH₂, h₂0, h₂1, hz, s₂⟩ := h₂
  refine ⟨h₁.trans h₂, fun q => H₂ (H₁ q, q.2), hH₂.comp (hH₁.prodMk contMDiff_snd),
    fun x => ?_, fun x => ?_, ?_, fun t => ?_⟩
  · simp only [h₁0, h₂0]
  · simp only [h₁1, h₂1, Diffeomorph.coe_trans, Function.comp]
  · simp only [Diffeomorph.coe_trans, Function.comp, hy, hz]
  · obtain ⟨a₁, ha₁⟩ := s₁ t
    obtain ⟨a₂, ha₂⟩ := s₂ t
    exact ⟨a₁.trans a₂, fun x => by simp only [ha₁, ha₂, Diffeomorph.coe_trans, Function.comp]⟩

theorem Isotopic.symm {y z : N} (hyz : Isotopic J y z) : Isotopic J z y := by
  obtain ⟨h, Hm, hH, h0, h1, hy, s⟩ := hyz
  refine ⟨h.symm, fun q => h.symm (Hm (q.1, 1 - q.2)),
    h.symm.contMDiff.comp (hH.comp (contMDiff_fst.prodMk (contMDiff_const.sub contMDiff_snd))),
    fun x => ?_, fun x => ?_, ?_, fun t => ?_⟩
  · simp only [sub_zero, h1, Diffeomorph.symm_apply_apply]
  · simp only [sub_self, h0]
  · rw [← hy, Diffeomorph.symm_apply_apply]
  · obtain ⟨a, ha⟩ := s (1 - t)
    exact ⟨a.trans h.symm, fun x => by simp only [ha, Diffeomorph.coe_trans, Function.comp]⟩

/-- **Local homogeneity**: every point of a chart neighbourhood of `y` is isotopic to `y`. -/
theorem eventually_isotopic [T2Space N] (y : N) : ∀ᶠ z in 𝓝 y, Isotopic J y z := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (extChartAt_target_mem_nhds (I := J) y)
  let φ : ContDiffBump (extChartAt J y y) := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hφ : ContDiff ℝ ∞ φ := φ.contDiff (n := ⊤)
  have hK : IsCompact (closedBall (extChartAt J y y) (ε / 2)) := isCompact_closedBall _ _
  have hKt : closedBall (extChartAt J y y) (ε / 2) ⊆ (extChartAt J y).target := fun u hu =>
    hball (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hu) (by linarith)))
  have hφK : ∀ u, u ∉ closedBall (extChartAt J y y) (ε / 2) → φ u = 0 := fun u hu =>
    φ.zero_of_le_dist (le_of_lt (not_le.1 fun h => hu (mem_closedBall.2 h)))
  have hφa : φ (extChartAt J y y) = 1 :=
    φ.one_of_mem_closedBall (mem_closedBall_self (by positivity))
  obtain ⟨L, hL, hL'⟩ := exists_lipschitz_of_hasCompactSupport hφ φ.hasCompactSupport
  have hδ : 0 < 1 / ((L : ℝ) + 1) := by positivity
  have hmem : {z | z ∈ (extChartAt J y).source ∧
      extChartAt J y z ∈ ball (extChartAt J y y) (1 / ((L : ℝ) + 1))} ∈ 𝓝 y :=
    inter_mem (extChartAt_source_mem_nhds y)
      ((continuousAt_extChartAt y).preimage_mem_nhds (ball_mem_nhds _ hδ))
  filter_upwards [hmem] with z hz
  obtain ⟨hz1, hz2⟩ := hz
  -- the displacement vector
  set c : F := extChartAt J y z - extChartAt J y y with hc_def
  have hcn : ‖c‖ < 1 / ((L : ℝ) + 1) := by rw [hc_def, ← dist_eq_norm]; exact hz2
  have hc : (L : ℝ) * ‖c‖ < 1 := by
    have h1 : ‖c‖ * ((L : ℝ) + 1) < 1 := (lt_div_iff₀ (by positivity)).1 hcn
    nlinarith [norm_nonneg c, L.coe_nonneg]
  have hcs : ∀ s : ℝ, (L : ℝ) * ‖Real.smoothTransition s • c‖ < 1 := fun s => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg s)]
    have h1 := Real.smoothTransition.le_one s
    have h0 : 0 ≤ (L : ℝ) * ‖c‖ := by positivity
    calc (L : ℝ) * (Real.smoothTransition s * ‖c‖)
        = ((L : ℝ) * ‖c‖) * Real.smoothTransition s := by ring
      _ ≤ ((L : ℝ) * ‖c‖) * 1 := by gcongr
      _ < 1 := by linarith
  have hgK : ∀ (d : F) u, u ∉ closedBall (extChartAt J y y) (ε / 2) → shift φ d u = u :=
    fun d u hu => shift_of_eq_zero (hφK u hu)
  have hgt : ∀ s : ℝ, ∀ u ∈ (extChartAt J y).target,
      shift φ (Real.smoothTransition s • c) u ∈ (extChartAt J y).target := fun s =>
    mapsTo_of_eq_id_outside hKt (shift_injective hL (hcs s)) (hgK _)
  -- for every admissible displacement `d`, `transport (shift φ d)` is a diffeomorphism
  have hdiffeo : ∀ d : F, (L : ℝ) * ‖d‖ < 1 →
      ∃ hd : N ≃ₘ⟮J, J⟯ N, ∀ x, hd x = transport J y (shift φ d) x := by
    intro d hd
    have hbij : Bijective (shift φ d) := ⟨shift_injective hL hd, shift_surjective hL hd⟩
    set g' : F → F := ⇑(Equiv.ofBijective (shift φ d) hbij).symm with hg'_def
    have hg'g : ∀ u, g' (shift φ d u) = u := (Equiv.ofBijective (shift φ d) hbij).symm_apply_apply
    have hgg' : ∀ u, shift φ d (g' u) = u := (Equiv.ofBijective (shift φ d) hbij).apply_symm_apply
    have hg'K : ∀ u, u ∉ closedBall (extChartAt J y y) (ε / 2) → g' u = u := fun u hu => by
      have := hg'g u; rwa [hgK d u hu] at this
    have hg't : ∀ u ∈ (extChartAt J y).target, g' u ∈ (extChartAt J y).target :=
      mapsTo_of_eq_id_outside hKt (Equiv.injective _) hg'K
    have hg' : ContDiff ℝ ∞ g' := shift_symm_contDiff hφ hL' hd hbij
    have hgt1 : ∀ u ∈ (extChartAt J y).target, shift φ d u ∈ (extChartAt J y).target :=
      mapsTo_of_eq_id_outside hKt hbij.1 (hgK d)
    let hd : N ≃ₘ⟮J, J⟯ N :=
      { toFun := transport J y (shift φ d)
        invFun := transport J y g'
        left_inv := fun p => transport_transport hgt1 hg'g p
        right_inv := fun p => transport_transport hg't hgg' p
        contMDiff_toFun := contMDiff_transport (shift_contDiff hφ d) hK hKt (hgK d) hgt1
        contMDiff_invFun := contMDiff_transport hg' hK hKt hg'K hg't }
    exact ⟨hd, fun x => rfl⟩
  obtain ⟨h, hh⟩ := hdiffeo c hc
  refine ⟨h, fun q => transport J y (shift φ (Real.smoothTransition q.2 • c)) q.1,
    contMDiff_transport_shift hφ c hK hKt hφK hgt, fun x => ?_, fun x => ?_, ?_, fun t => ?_⟩
  · show transport J y (shift φ (Real.smoothTransition 0 • c)) x = x
    have : shift φ (Real.smoothTransition 0 • c) = id := by
      funext u; rw [Real.smoothTransition.zero, zero_smul, shift_zero]; rfl
    rw [this, transport_id]
  · show transport J y (shift φ (Real.smoothTransition 1 • c)) x = h x
    rw [Real.smoothTransition.one, one_smul]; exact (hh x).symm
  · show h y = z
    rw [hh y]
    show transport J y (shift φ c) y = z
    rw [transport_of_mem (mem_extChartAt_source y)]
    have h1 : shift φ c (extChartAt J y y) = extChartAt J y z := by
      show extChartAt J y y + φ (extChartAt J y y) • c = extChartAt J y z
      rw [hφa, one_smul, hc_def, add_sub_cancel]
    rw [h1]
    exact (extChartAt J y).left_inv hz1
  · obtain ⟨ht, hht⟩ := hdiffeo (Real.smoothTransition t • c) (hcs t)
    exact ⟨ht, fun x => (hht x).symm⟩

/-- **Homogeneity Lemma** (Milnor, chapter 4).  On a connected manifold without boundary, any two
points are isotopic: there is a diffeomorphism `h` with `h y = z`, joined to the identity by a
smooth map `H : N × ℝ → N` with `H(·,0) = id`, `H(·,1) = h`. -/
theorem isotopic_of_preconnected [T2Space N] [PreconnectedSpace N] (y z : N) :
    Isotopic J y z := by
  have hopen : IsOpen {z | Isotopic J y z} := by
    rw [isOpen_iff_mem_nhds]; intro z hz
    exact (eventually_isotopic z).mono fun w hw => Isotopic.trans hz hw
  have hclosed : IsClosed {z | Isotopic J y z} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]; intro z hz
    exact (eventually_isotopic z).mono fun w hw hyw => hz (Isotopic.trans hyw (Isotopic.symm hw))
  have huniv := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨y, Isotopic.refl y⟩
  exact (Set.eq_univ_iff_forall.1 huniv) z

end Milnor
