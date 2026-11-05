import Morse
import RoundTrip.Check
import RoundTrip.Blind.V8_11
import RoundTrip.Bridge

open Set Filter Topology Function
open scoped ContDiff Manifold

namespace RoundTrip.V8_11

/-- The project's statement (universes instantiated at 0), for a slice submanifold `N ⊆ V` with
the induced metric: the three steps of the converse of Corollary 12.3 — (1) at a critical path
(first variation zero on `TΩ`) the acceleration vanishes off the break points, (2) the velocity
jumps vanish, (3) gluing two geodesic pieces with a common velocity gives a geodesic — together
with the existence of a geodesic through any point with any tangent velocity (from Lemma 10.2), and
**Corollary 12.3**: `c ∈ Ω(N; p, q)` is a critical path of `E` iff it is an unbroken geodesic. -/
def A : Prop :=
  type_of% @Morse.accel_eq_zero_of_critical.{0,0,0} ∧
    type_of% @Morse.jump_eq_zero_of_critical.{0,0,0} ∧
    type_of% @Morse.exists_isGeodesicOn_through.{0,0,0} ∧
    type_of% @Morse.isGeodesicOn_of_glue.{0,0,0} ∧
    type_of% @Morse.corollary_12_3.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.accel_eq_zero_of_critical, @Morse.jump_eq_zero_of_critical,
    @Morse.exists_isGeodesicOn_through, @Morse.isGeodesicOn_of_glue, @Morse.corollary_12_3⟩

/-! ## The embedded special case: dictionary for paths, geodesics and 1-parameter variations
(identical to the one in `Items/V8_10.lean`, restated in this file's blind vocabulary) -/

namespace Emb

set_option linter.unusedSectionVars false

/-- `e₀ ∈ ℝ¹`. -/
noncomputable abbrev e0 : Rn 1 := EuclideanSpace.single 0 (1 : ℝ)

theorem smul_e0 (u : Rn 1) : (u 0) • e0 = u := by
  ext i
  fin_cases i
  simp

/-- A subdivision `0 = t₀ < ⋯ < t_k = 1` whose open pieces avoid a finite set `B`. -/
theorem exists_subdiv (B : Finset ℝ) : ∃ (k : ℕ) (t : ℕ → ℝ), t 0 = 0 ∧ t k = 1 ∧
    (∀ i < k, t i < t (i + 1)) ∧
    ∀ i < k, 0 ≤ t i ∧ t (i + 1) ≤ 1 ∧ ∀ x ∈ B, x ∉ Ioo (t i) (t (i + 1)) := by
  classical
  have hlt : (0 : ℝ) < 1 := zero_lt_one
  set a : ℝ := 0
  set b : ℝ := 1
  set S : Finset ℝ := insert a (insert b (B.filter (· ∈ Ioo a b)))
  have hS : ∀ x ∈ S, a ≤ x ∧ x ≤ b := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_filter] at hx
    rcases hx with rfl | rfl | ⟨-, hx⟩
    · exact ⟨le_rfl, hlt.le⟩
    · exact ⟨hlt.le, le_rfl⟩
    · exact ⟨hx.1.le, hx.2.le⟩
  have haS : a ∈ S := Finset.mem_insert_self _ _
  have hbS : b ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  set m := S.card
  have hm : 1 < m := Finset.one_lt_card.2 ⟨a, haS, b, hbS, hlt.ne⟩
  set e := S.orderEmbOfFin rfl
  set t : ℕ → ℝ := fun j => if h : j < m then e ⟨j, h⟩ else b
  have ht : ∀ j (h : j < m), t j = e ⟨j, h⟩ := fun j h => dif_pos h
  refine ⟨m - 1, t, ?_, ?_, ?_, ?_⟩
  · rw [ht 0 (by omega), Finset.orderEmbOfFin_zero rfl (by omega)]
    exact le_antisymm (Finset.min'_le _ _ haS) ((hS _ (Finset.min'_mem _ _)).1)
  · rw [ht (m - 1) (by omega), Finset.orderEmbOfFin_last rfl (by omega)]
    exact le_antisymm ((hS _ (Finset.max'_mem _ _)).2) (Finset.le_max' _ _ hbS)
  · intro i hi
    rw [ht i (by omega), ht (i + 1) (by omega)]
    exact e.strictMono (Fin.mk_lt_mk.2 (Nat.lt_succ_self i))
  · intro i hi
    rw [ht i (by omega), ht (i + 1) (by omega)]
    refine ⟨(hS _ (Finset.orderEmbOfFin_mem _ _ _)).1, (hS _ (Finset.orderEmbOfFin_mem _ _ _)).2,
      fun x hx hxi => ?_⟩
    have hxS : x ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_filter.2 ⟨hx, (hS _ (Finset.orderEmbOfFin_mem _ _ _)).1.trans_lt hxi.1,
        hxi.2.trans_le (hS _ (Finset.orderEmbOfFin_mem _ _ _)).2⟩))
    obtain ⟨j, rfl⟩ : x ∈ Set.range e := by
      rw [Finset.range_orderEmbOfFin]; exact hxS
    have h1 := e.lt_iff_lt.1 hxi.1
    have h2 := e.lt_iff_lt.1 hxi.2
    rw [Fin.lt_def] at h1 h2
    simp only at h1 h2
    omega

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

theorem mem_pathSpace_of_isPW {pw : ℝ → Bridge.Sub hN} (h : IsPW (n := n) pw 0 1) :
    Bridge.incl hN ∘ pw ∈ Morse.pathSpace N (Bridge.incl hN (pw 0)) (Bridge.incl hN (pw 1)) :=
  ⟨Bridge.isPiecewiseSmooth_of_isPW h, fun t _ => (pw t).2, rfl, rfl⟩

/-! ### Geodesics on `[0, 1]` -/

/-- A blind geodesic on `[0, 1]` (induced connection) is a project unbroken geodesic. -/
theorem isUnbrokenGeodesic_of_isGeodesic {pw : ℝ → Bridge.Sub hN}
    (h : IsGeodesic (Bridge.conn (hN := hN)) pw (Icc 0 1)) :
    Morse.IsUnbrokenGeodesic hN (Bridge.incl hN ∘ pw) := by
  have h' : RoundTrip.BridgePrelude.IsGeodesic (Bridge.conn (hN := hN)) pw (Icc 0 1) := h
  exact ⟨(Bridge.isGeodesic_iff.1 h').2.1, Bridge.isGeodesicOn_Ioo h'⟩

/-- A project unbroken geodesic is a blind geodesic on the closed interval `[0, 1]` (at the end
points the normal acceleration vanishes by continuity). -/
theorem isGeodesic_of_isUnbrokenGeodesic {pw : ℝ → Bridge.Sub hN}
    (h : Morse.IsUnbrokenGeodesic hN (Bridge.incl hN ∘ pw)) :
    IsGeodesic (Bridge.conn (hN := hN)) pw (Icc 0 1) := by
  show RoundTrip.BridgePrelude.IsGeodesic _ _ _
  refine Bridge.isGeodesic_iff.2 ⟨⟨ordConnected_Icc, uniqueDiffOn_Icc zero_lt_one⟩, h.1, ?_⟩
  set f := Bridge.incl hN ∘ pw
  set I := Icc (0 : ℝ) 1
  have uI : UniqueDiffOn ℝ I := uniqueDiffOn_Icc zero_lt_one
  have hg : ContinuousOn (derivWithin (derivWithin f I) I) I :=
    ((h.1.derivWithin uI (m := ∞) (by simp)).derivWithin uI (m := 0) (by simp)).continuousOn
  have hpw : ContinuousOn pw I := fun t ht =>
    (Topology.IsInducing.subtypeVal.continuousWithinAt_iff (f := pw)).2 (h.1.continuousOn t ht)
  have hP : ContinuousOn (fun t => Bridge.P hN (pw t)) I :=
    Bridge.contMDiff_P.continuous.comp_continuousOn hpw
  have hcont : ContinuousOn
      (fun t => Bridge.P hN (pw t) (derivWithin (derivWithin f I) I t)) I := hP.clm_apply hg
  have hzero : EqOn (fun t => Bridge.P hN (pw t) (derivWithin (derivWithin f I) I t)) 0
      (Ioo 0 1) := by
    intro t ht
    have h1 : deriv f =ᶠ[𝓝 t] derivWithin f I := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
      exact (derivWithin_of_mem_nhds (Icc_mem_nhds hτ.1 hτ.2)).symm
    have e : derivWithin (derivWithin f I) I t = deriv (deriv f) t := by
      rw [h1.deriv_eq, derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
    show Bridge.P hN (pw t) _ = 0
    rw [e]
    exact (Morse.tanProj_eq_zero_iff hN).2 (h.2.normal t ht)
  intro t ht
  exact hzero.of_subset_closure hcont continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo zero_ne_one]) ht

theorem isGeodesic_iff_isUnbrokenGeodesic {pw : ℝ → Bridge.Sub hN} :
    IsGeodesic (Bridge.conn (hN := hN)) pw (Icc 0 1) ↔
      Morse.IsUnbrokenGeodesic hN (Bridge.incl hN ∘ pw) :=
  ⟨isUnbrokenGeodesic_of_isGeodesic, isGeodesic_of_isUnbrokenGeodesic⟩

/-! ### 1-parameter variations -/

/-- A blind 1-parameter variation (`U ⊆ ℝ¹`) in `N` is a project variation along the line
`s ↦ s e₀`. -/
theorem isVariation_of_isVar {U : Set (Rn 1)} {α : Rn 1 → ℝ → Bridge.Sub hN}
    (h : IsVar (n := n) U α) : ∃ B : Finset ℝ,
      Morse.IsVariation N {s : ℝ | s • e0 ∈ U} (fun s τ => Bridge.incl hN (α (s • e0) τ)) B := by
  obtain ⟨k, t, hU, h0U, ht0, htk, hlt, hpath, hsm⟩ := h
  refine ⟨(Finset.range (k + 1)).image t, ?_⟩
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
    have h2 : ContDiffOn ℝ ∞ (Bridge.incl hN ∘ (fun x : Rn 1 × ℝ => α x.1 x.2))
        (U ×ˢ Icc (t i) (t (i + 1))) := contMDiffOn_map_iff.1 (hsm i hi)
    have hmap : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p.1 • e0, p.2)) :=
      (contDiff_fst.smul contDiff_const).prodMk contDiff_snd
    exact h2.comp hmap.contDiffOn fun p hp => ⟨hp.1, hti.trans hp.2.1, hp.2.2.trans hut⟩

/-- **Critical paths, project ⇒ blind.** -/
theorem isCriticalPath_of_project {pw : ℝ → Bridge.Sub hN}
    (h : Morse.IsCriticalPath N (Bridge.incl hN ∘ pw)) :
    IsCriticalPath (n := n) (Efun (n := n)) pw := by
  intro U α hα hα0
  obtain ⟨B, hB⟩ := isVariation_of_isVar hα
  have hd := h _ _ B hB (fun t _ => by simp [hα0])
  have key : (fun u : Rn 1 => Efun (n := n) (α u)) =
      (fun s => Morse.energy (fun τ => Bridge.incl hN (α (s • e0) τ)) 0 1) ∘
        (fun u : Rn 1 => u 0) := by
    funext u
    simp only [comp_apply, smul_e0]
    exact Bridge.energy_eq (α u) 0 1
  have hlin : HasFDerivAt (fun u : Rn 1 => u 0) (EuclideanSpace.proj (0 : Fin 1) : Rn 1 →L[ℝ] ℝ)
      (0 : Rn 1) := (EuclideanSpace.proj (0 : Fin 1) : Rn 1 →L[ℝ] ℝ).hasFDerivAt
  have hd' : HasDerivAt (fun s => Morse.energy (fun τ => Bridge.incl hN (α (s • e0) τ)) 0 1) 0
      ((fun u : Rn 1 => u 0) 0) := by simpa using hd
  have := hd'.comp_hasFDerivAt (0 : Rn 1) hlin
  rw [key]
  simpa using this

open Classical in
/-- The blind variation attached to a project variation `α` on `U ⊆ ℝ` (values `pw` off
`U × [0, 1]`). -/
noncomputable def toBlind (U : Set ℝ) (α : ℝ → ℝ → V)
    (hmem : ∀ u ∈ U, ∀ τ ∈ Icc (0 : ℝ) 1, α u τ ∈ N) (pw : ℝ → Bridge.Sub hN) (u : Rn 1)
    (τ : ℝ) : Bridge.Sub hN :=
  if hh : u 0 ∈ U ∧ τ ∈ Icc (0 : ℝ) 1 then
    (show Bridge.Sub hN from (⟨α (u 0) τ, hmem _ hh.1 τ hh.2⟩ : N)) else pw τ

theorem incl_toBlind {U : Set ℝ} {α : ℝ → ℝ → V} {hmem : ∀ u ∈ U, ∀ τ ∈ Icc (0 : ℝ) 1, α u τ ∈ N}
    {pw : ℝ → Bridge.Sub hN} {u : Rn 1} {τ : ℝ} (hu : u 0 ∈ U) (hτ : τ ∈ Icc (0 : ℝ) 1) :
    Bridge.incl hN (toBlind U α hmem pw u τ) = α (u 0) τ := by
  unfold toBlind
  split_ifs with hh
  · rfl
  · exact absurd ⟨hu, hτ⟩ hh

theorem toBlind_of_not {U : Set ℝ} {α : ℝ → ℝ → V}
    {hmem : ∀ u ∈ U, ∀ τ ∈ Icc (0 : ℝ) 1, α u τ ∈ N}
    {pw : ℝ → Bridge.Sub hN} {u : Rn 1} {τ : ℝ} (hh : ¬ (u 0 ∈ U ∧ τ ∈ Icc (0 : ℝ) 1)) :
    toBlind U α hmem pw u τ = pw τ := by
  unfold toBlind
  rw [dif_neg hh]

/-- **Critical paths, blind ⇒ project.** A project variation `α` (any open `U ⊆ ℝ`, any break
set) is turned into a blind one on `{u ∈ ℝ¹ | u 0 ∈ U}` (values `pw` off `U × [0, 1]`). -/
theorem isCriticalPath_project_of_blind {pw : ℝ → Bridge.Sub hN}
    (h : IsCriticalPath (n := n) (Efun (n := n)) pw) :
    Morse.IsCriticalPath N (Bridge.incl hN ∘ pw) := by
  intro U α B hα hα0
  classical
  obtain ⟨k, t, ht0, htk, hlt, hgood⟩ := exists_subdiv B
  set U' : Set (Rn 1) := {u | u 0 ∈ U} with hU'
  set α' : Rn 1 → ℝ → Bridge.Sub hN := toBlind U α hα.mem pw with hα'def
  have hinc : ∀ u ∈ U', ∀ τ ∈ Icc (0 : ℝ) 1, Bridge.incl hN (α' u τ) = α (u 0) τ :=
    fun u hu τ hτ => incl_toBlind hu hτ
  have hα'0 : α' 0 = pw := by
    funext τ
    by_cases hh : (0 : Rn 1) 0 ∈ U ∧ τ ∈ Icc (0 : ℝ) 1
    · apply Subtype.ext
      show Bridge.incl hN (α' 0 τ) = Bridge.incl hN (pw τ)
      rw [hinc 0 hh.1 τ hh.2]
      have := hα0 τ hh.2
      simpa using this
    · exact toBlind_of_not hh
  have hmap : ContDiff ℝ ∞ (fun x : Rn 1 × ℝ => (x.1 0, x.2)) :=
    ((EuclideanSpace.proj (0 : Fin 1) : Rn 1 →L[ℝ] ℝ).contDiff.comp contDiff_fst).prodMk
      contDiff_snd
  have hsm : ∀ i < k, ContDiffOn ℝ ∞ (Bridge.incl hN ∘ fun x : Rn 1 × ℝ => α' x.1 x.2)
      (U' ×ˢ Icc (t i) (t (i + 1))) := by
    intro i hi
    obtain ⟨h1, h2, h3⟩ := hgood i hi
    have hF := hα.smooth _ _ h1 (hlt i hi) h2 h3
    refine (hF.comp hmap.contDiffOn fun x hx => ⟨hx.1, hx.2⟩).congr fun x hx => ?_
    exact hinc x.1 hx.1 x.2 ⟨h1.trans hx.2.1, hx.2.2.trans h2⟩
  have hU'o : IsOpen U' :=
    hα.isOpen.preimage (EuclideanSpace.proj (0 : Fin 1) : Rn 1 →L[ℝ] ℝ).continuous
  have h0U' : (0 : Rn 1) ∈ U' := by
    show (0 : Rn 1) 0 ∈ U
    simpa using hα.zero_mem
  have hvar : IsVar (n := n) U' α' := by
    refine ⟨k, t, hU'o, h0U', ht0, htk, hlt, fun u hu => ⟨⟨k, t, ht0, htk, hlt, fun i hi => ?_⟩,
      ?_, ?_⟩, fun i hi => contMDiffOn_map_iff.2 (hsm i hi)⟩
    · refine Bridge.contMDiffOn_curve_iff.2 ?_
      exact (hsm i hi).comp (contDiff_const.prodMk contDiff_id).contDiffOn
        fun τ hτ => ⟨hu, hτ⟩
    · apply Subtype.ext
      show Bridge.incl hN (α' u 0) = Bridge.incl hN (α' 0 0)
      rw [hinc u hu 0 ⟨le_rfl, zero_le_one⟩, hinc 0 h0U' 0 ⟨le_rfl, zero_le_one⟩,
        hα.start _ hu]
      simp
    · apply Subtype.ext
      show Bridge.incl hN (α' u 1) = Bridge.incl hN (α' 0 1)
      rw [hinc u hu 1 ⟨zero_le_one, le_rfl⟩, hinc 0 h0U' 1 ⟨zero_le_one, le_rfl⟩,
        hα.finish _ hu]
      simp
  have hd := h U' α' hvar hα'0
  have hd' : HasFDerivAt (fun u : Rn 1 => Efun (n := n) (α' u)) (0 : Rn 1 →L[ℝ] ℝ)
      ((fun s : ℝ => s • e0) 0) := by simpa using hd
  have hcomp := hd'.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).smul_const e0)
  simp only [zero_apply] at hcomp
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hα.isOpen.mem_nhds hα.zero_mem] with s hs
  simp only [comp_apply, id]
  have hsU : (s • e0) ∈ U' := by
    show (s • e0) 0 ∈ U
    simpa using hs
  have e1 : Efun (n := n) (α' (s • e0)) = Morse.energy (Bridge.incl hN ∘ α' (s • e0)) 0 1 :=
    Bridge.energy_eq (α' (s • e0)) 0 1
  rw [e1]
  refine Morse.energy_congr fun τ hτ => ?_
  rw [comp_apply, hinc _ hsU τ hτ]
  simp

theorem isCriticalPath_iff {pw : ℝ → Bridge.Sub hN} :
    IsCriticalPath (n := n) (Efun (n := n)) pw ↔ Morse.IsCriticalPath N (Bridge.incl hN ∘ pw) :=
  ⟨isCriticalPath_project_of_blind, isCriticalPath_of_project⟩


/-! ### Connected components (copied from `Items/V7_28.lean`) -/

/-- An open part has the same tangent spaces. -/
theorem tangentSubspace_inter {O : Set V} (hO : IsOpen O) (x : V) (hx : x ∈ N ∩ O) :
    Morse.tangentSubspace (Morse.IsSliceSubmanifold.inter_isOpen hN hO) ⟨x, hx⟩ =
      Morse.tangentSubspace hN ⟨x, hx.1⟩ := by
  obtain ⟨σ, hσ⟩ := hN x hx.1
  rw [Morse.tangentSubspace_eq_range_fderiv_sliceParam _ (Morse.SliceChart.inter σ hO hx hσ)
    ⟨hσ, hx.2⟩, Morse.tangentSubspace_eq_range_fderiv_sliceParam hN σ hσ]
  rfl

omit [FiniteDimensional ℝ W] in
/-- The connected component of `q` in a slice submanifold is an open part `N ∩ O`, connected, and
piecewise smooth paths in `N` starting in it stay in it. -/
theorem exists_component (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn n) W N) (q : N) :
    ∃ O : Set V, IsOpen O ∧ (q : V) ∈ O ∧ IsConnected (N ∩ O) ∧
      ∀ (c : ℝ → V) (a b : ℝ), Morse.IsPiecewiseSmooth c a b → (∀ t ∈ Icc a b, c t ∈ N) →
        c a ∈ N ∩ O → ∀ t ∈ Icc a b, c t ∈ N ∩ O := by
  let _ := hN.chartedSpace
  have := ChartedSpace.locallyConnectedSpace (Bridge.Rn n) N
  have hK : IsOpen (connectedComponent q) := isOpen_connectedComponent
  obtain ⟨O, hO, hOK⟩ := isOpen_induced_iff.1 hK
  have hNO : N ∩ O = connectedComponentIn N (q : V) := by
    rw [connectedComponentIn_eq_image q.2]
    ext x
    constructor
    · rintro ⟨hxN, hxO⟩
      refine ⟨⟨x, hxN⟩, ?_, rfl⟩
      rw [← hOK]
      exact hxO
    · rintro ⟨y, hyK, rfl⟩
      refine ⟨y.2, ?_⟩
      rw [← hOK] at hyK
      exact hyK
  refine ⟨O, hO, ?_, ?_, ?_⟩
  · have : q ∈ connectedComponent q := mem_connectedComponent
    rw [← hOK] at this
    exact this
  · rw [hNO]
    exact isConnected_connectedComponentIn_iff.2 q.2
  · intro c a b hc hcN ha t ht
    rw [hNO] at ha ⊢
    rw [connectedComponentIn_eq ha]
    have hpre : IsPreconnected (c '' Icc a b) := isPreconnected_Icc.image c hc.2.1
    exact hpre.subset_connectedComponentIn ⟨a, ⟨le_rfl, hc.1⟩, rfl⟩
      (by rintro _ ⟨s, hs, rfl⟩; exact hcN s hs) ⟨t, ht, rfl⟩

/-- A geodesic of `N` lying in the open part `N ∩ O` is a geodesic of `N ∩ O`. -/
theorem isGeodesicOn_inter {O : Set V} (hO : IsOpen O) {γ : ℝ → V} {s : Set ℝ}
    (h : Morse.IsGeodesicOn hN γ s) (hs : ∀ t ∈ s, γ t ∈ N ∩ O) :
    Morse.IsGeodesicOn (Morse.IsSliceSubmanifold.inter_isOpen hN hO) γ s :=
  ⟨h.isOpen, hs, h.contDiffOn, fun t ht => by
    rw [tangentSubspace_inter hO (γ t) (hs t ht)]
    exact h.normal t ht⟩

/-- The project's critical paths are a local notion: a critical path of `N ∩ O`, for the component
`N ∩ O` of its initial point, is a critical path of `N`. -/
theorem isCriticalPath_of_component {O : Set V} (hO : IsOpen O)
    (hpath : ∀ (c : ℝ → V) (a b : ℝ), Morse.IsPiecewiseSmooth c a b → (∀ t ∈ Icc a b, c t ∈ N) →
        c a ∈ N ∩ O → ∀ t ∈ Icc a b, c t ∈ N ∩ O)
    {c : ℝ → V} (hc0 : c 0 ∈ N ∩ O) (h : Morse.IsCriticalPath (N ∩ O) c) :
    Morse.IsCriticalPath N c := by
  intro U α B hα hα0
  have hα' : Morse.IsVariation (N ∩ O) U α B :=
    { isOpen := hα.isOpen
      zero_mem := hα.zero_mem
      mem := fun u hu t ht => hpath (α u) 0 1 (hα.isPiecewiseSmooth hu) (hα.mem u hu)
        (by rw [hα.start u hu, hα0 0 ⟨le_rfl, zero_le_one⟩]; exact hc0) t ht
      start := hα.start
      finish := hα.finish
      smooth := hα.smooth }
  exact h U α B hα' hα0


/-! ### Congruence on `[0, 1]` and components -/

theorem isCriticalPath_congr {N : Set V} {c c' : ℝ → V} (h : EqOn c c' (Icc 0 1)) :
    Morse.IsCriticalPath N c ↔ Morse.IsCriticalPath N c' := by
  constructor
  · intro hc U α B hα hα0
    exact hc U α B hα fun t ht => (hα0 t ht).trans (h ht).symm
  · intro hc U α B hα hα0
    exact hc U α B hα fun t ht => (hα0 t ht).trans (h ht)

theorem isUnbrokenGeodesic_congr {c c' : ℝ → V} (h : EqOn c c' (Icc 0 1))
    (hc : Morse.IsUnbrokenGeodesic hN c) : Morse.IsUnbrokenGeodesic hN c' :=
  ⟨hc.1.congr fun t ht => (h ht).symm, hc.2.congr fun t ht => h (Ioo_subset_Icc_self ht)⟩

/-- A geodesic of the open part `N ∩ O` is a geodesic of `N`. -/
theorem isGeodesicOn_of_inter {O : Set V} (hO : IsOpen O) {γ : ℝ → V} {s : Set ℝ}
    (h : Morse.IsGeodesicOn (Morse.IsSliceSubmanifold.inter_isOpen hN hO) γ s) :
    Morse.IsGeodesicOn hN γ s :=
  ⟨h.isOpen, fun t ht => (h.mem t ht).1, h.contDiffOn, fun t ht => by
    have := h.normal t ht
    rwa [tangentSubspace_inter hO (γ t) (h.mem t ht)] at this⟩

theorem isCriticalPath_inter_of {O : Set V} {c : ℝ → V} (h : Morse.IsCriticalPath N c) :
    Morse.IsCriticalPath (N ∩ O) c := fun U α B hα hα0 =>
  h U α B
    { isOpen := hα.isOpen
      zero_mem := hα.zero_mem
      mem := fun u hu t ht => (hα.mem u hu t ht).1
      start := hα.start
      finish := hα.finish
      smooth := hα.smooth } hα0

end Emb

/-! ## B on embedded manifolds -/

/-- B on embedded manifolds: `M = ↥N` with the induced metric and the induced Levi-Civita
connection (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)], ∀ pw : ℝ → Bridge.Sub hN, IsPW (n := n) pw 0 1 →
    (IsCriticalPath (n := n) (Efun (n := n)) pw ↔ IsGeodesic (Bridge.conn (hN := hN)) pw (Icc 0 1))

/-- `B_emb` is a special case of B (the induced connection is Levi-Civita, `Bridge.conn_isLC`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- Corollary 12.3 of A, for slice submanifolds modelled on `ℝⁿ`. -/
def A_cor : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) (c : ℝ → V) (p q : V),
    c ∈ Morse.pathSpace N p q → (Morse.IsCriticalPath N c ↔ Morse.IsUnbrokenGeodesic hN c)

theorem A_to_A_cor : A → A_cor := fun hA _ _ _ _ _ _ _ _ _ _ hN _ _ _ hc =>
  hA.2.2.2.2 hN hc

/-- **A implies B on embedded manifolds** (through `Emb.isCriticalPath_iff`,
`Emb.isGeodesic_iff_isUnbrokenGeodesic`, and A's Corollary 12.3). -/
theorem A_cor_to_B_emb : A_cor → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN _ pw hpw
  rw [Emb.isCriticalPath_iff, Emb.isGeodesic_iff_isUnbrokenGeodesic]
  exact hA V W n N hN _ _ _ (Emb.mem_pathSpace_of_isPW hpw)

theorem A_to_B_emb : A → B_emb := fun hA => A_cor_to_B_emb (A_to_A_cor hA)

/-- **B on embedded manifolds implies A's Corollary 12.3** (for every slice submanifold modelled
on `ℝⁿ`, connected or not: B is applied to the component of `c 0`). -/
theorem B_emb_to_A_cor : B_emb → A_cor := by
  intro hB V _ _ _ W _ _ _ n N hN c p q hc
  have hc0 : c 0 ∈ N := hc.2.1 0 ⟨le_rfl, zero_le_one⟩
  obtain ⟨O, hO, hqO, hconn, hpath⟩ := Emb.exists_component hN ⟨c 0, hc0⟩
  have hN' : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W (N ∩ O) :=
    Morse.IsSliceSubmanifold.inter_isOpen hN hO
  have : ConnectedSpace (Bridge.Sub hN') := isConnected_iff_connectedSpace.1 hconn
  have hcN' : ∀ t ∈ Icc (0 : ℝ) 1, c t ∈ N ∩ O :=
    hpath c 0 1 hc.1 hc.2.1 ⟨hc0, hqO⟩
  set pw : ℝ → Bridge.Sub hN' :=
    Bridge.lift c (⟨c 0, hcN' 0 ⟨le_rfl, zero_le_one⟩⟩ : ↥(N ∩ O)) with hpwdef
  have hpw : IsPW (n := n) pw 0 1 := Bridge.isPW_lift hc.1 hcN' _
  have heq : EqOn (Bridge.incl hN' ∘ pw) c (Icc 0 1) := fun t ht =>
    Bridge.incl_lift _ (hcN' t ht)
  have key := hB V W n (N ∩ O) hN' pw hpw
  rw [Emb.isCriticalPath_iff, Emb.isGeodesic_iff_isUnbrokenGeodesic,
    Emb.isCriticalPath_congr heq] at key
  constructor
  · intro hcrit
    have hg := key.1 (Emb.isCriticalPath_inter_of hcrit)
    have hg' := Emb.isUnbrokenGeodesic_congr heq hg
    exact ⟨hg'.1, Emb.isGeodesicOn_of_inter hO hg'.2⟩
  · intro hgeo
    refine Emb.isCriticalPath_of_component hO hpath ⟨hc0, hqO⟩ (key.2 ?_)
    refine Emb.isUnbrokenGeodesic_congr (fun t ht => (heq ht).symm) ⟨hgeo.1, ?_⟩
    exact Emb.isGeodesicOn_inter hO hgeo.2 fun t ht => hcN' t (Ioo_subset_Icc_self ht)

/-- **B implies A's Corollary 12.3** (by specializing B to `↥N`). -/
theorem B_to_A_cor : B → A_cor := fun hB => B_emb_to_A_cor (B_to_B_emb hB)

theorem B_emb_iff_A_cor : B_emb ↔ A_cor := ⟨B_emb_to_A_cor, A_cor_to_B_emb⟩

/-! Neither `A → B` nor `B → A` is proved; see `V8_11.json`. -/

#rt_check RoundTrip.V8_11.A_to_B_emb [Morse.accel_eq_zero_of_critical,
  Morse.jump_eq_zero_of_critical, Morse.exists_isGeodesicOn_through, Morse.isGeodesicOn_of_glue,
  Morse.corollary_12_3]
#rt_check RoundTrip.V8_11.B_to_A_cor [Morse.accel_eq_zero_of_critical,
  Morse.jump_eq_zero_of_critical, Morse.exists_isGeodesicOn_through, Morse.isGeodesicOn_of_glue,
  Morse.corollary_12_3]
#rt_overlap RoundTrip.V8_11.B_to_A_cor [Morse.accel_eq_zero_of_critical,
  Morse.jump_eq_zero_of_critical, Morse.exists_isGeodesicOn_through, Morse.isGeodesicOn_of_glue,
  Morse.corollary_12_3]

end RoundTrip.V8_11
