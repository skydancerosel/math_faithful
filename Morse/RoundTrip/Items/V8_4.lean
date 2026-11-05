import Morse
import RoundTrip.Check
import RoundTrip.Blind.V8_4
import RoundTrip.Bridge

open Set Filter Topology
open scoped ContDiff Manifold

namespace RoundTrip.V8_4

/-- The only declaration of this item, `Morse.IsCriticalPath`, is a definition: there is no listed
theorem, so the project's formal statement is the empty conjunction. -/
def A : Prop := True

theorem A_holds : A := trivial

/-- `ℝ ≃L ℝ¹`, `x ↦ x e₀`. -/
noncomputable def e1 : ℝ ≃L[ℝ] Rn 1 :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => EuclideanSpace.single 0 x
      invFun := fun v => v 0
      map_add' := fun x y => by
        ext i; fin_cases i; simp
      map_smul' := fun a x => by
        ext i; fin_cases i; simp
      left_inv := fun x => by simp
      right_inv := fun v => by
        ext i
        fin_cases i
        simp }

theorem e1_apply (x : ℝ) : e1 x = EuclideanSpace.single 0 x := rfl

/-- A function on `ℝ¹` has derivative `0` at `0` iff it does along `x ↦ x e₀`. -/
theorem hasFDerivAt_zero_iff (f : Rn 1 → ℝ) :
    HasFDerivAt f (0 : Rn 1 →L[ℝ] ℝ) 0 ↔
      HasDerivAt (fun x : ℝ => f (EuclideanSpace.single 0 x)) 0 0 := by
  rw [hasDerivAt_iff_hasFDerivAt]
  have h := e1.comp_right_hasFDerivAt_iff (f := f) (x := 0) (f' := 0)
  have e0 : e1 0 = 0 := map_zero e1
  rw [e0] at h
  have hz : (ContinuousLinearMap.toSpanSingleton ℝ (0 : ℝ)) =
      (0 : Rn 1 →L[ℝ] ℝ).comp (e1 : ℝ →L[ℝ] Rn 1) := by
    ext; simp
  rw [hz]
  exact h.symm

/-- `B` holds outright: Milnor's wording is the blind definition, read along `x ↦ x e₀`. -/
theorem B_holds : B := by
  intro n M _ _ _ _ _ _ _ F pw
  exact forall₂_congr fun U α => imp_congr_right fun _ => imp_congr_right fun _ =>
    hasFDerivAt_zero_iff _

theorem A_to_B : A → B := fun _ => B_holds

theorem B_to_A : B → A := fun _ => trivial

/-! ### Vocabulary check (not part of `A`): on embedded manifolds the blind critical paths of the
energy are the project's critical paths

For a slice submanifold `N ⊆ V` modelled on `ℝⁿ` (`M = ↥N`, induced metric) and any `pw : ℝ → ↥N`,
`IsCriticalPath Efun pw` (blind: all `ℝ¹`-parameter variations with a subdivision, `α 0 = pw`
everywhere, Fréchet derivative `0`) iff `Morse.IsCriticalPath N (incl ∘ pw)` (project: all
`ℝ`-parameter variations with a finite break set, `α 0 = c` on `[0, 1]`, derivative `0`). The
dictionary for variations below is copied from `Items/V8_9.lean`. -/

namespace Vocab

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

theorem exists_piece_of_mem {k : ℕ} {t : ℕ → ℝ} (h0 : t 0 = 0) (hk : t k = 1)
    (hlt : ∀ i < k, t i < t (i + 1)) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ i < k, s ∈ Icc (t i) (t (i + 1)) := by
  classical
  have hk0 : k ≠ 0 := by rintro rfl; rw [h0] at hk; exact zero_ne_one hk
  have hP : ∃ j, s ≤ t j ∧ j ≤ k := ⟨k, hk ▸ hs.2, le_rfl⟩
  have hm := Nat.find_spec hP
  by_cases hm0 : Nat.find hP = 0
  · refine ⟨0, Nat.pos_of_ne_zero hk0, ?_, ?_⟩
    · rw [h0]; exact hs.1
    · have : s ≤ t 0 := by rw [← hm0]; exact hm.1
      exact this.trans (hlt 0 (Nat.pos_of_ne_zero hk0)).le
  · refine ⟨Nat.find hP - 1, by omega, ?_, ?_⟩
    · by_contra hcon
      exact Nat.find_min hP (Nat.sub_lt (Nat.pos_of_ne_zero hm0) one_pos)
        ⟨(lt_of_not_ge hcon).le, by omega⟩
    · rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)]; exact hm.1

theorem exists_piece_of_free {k : ℕ} {t : ℕ → ℝ} (h0 : t 0 = 0) (hk : t k = 1)
    {s u : ℝ} (hs : 0 ≤ s) (hsu : s < u) (hu : u ≤ 1)
    (hB : ∀ x ∈ (Finset.range (k + 1)).image t, x ∉ Ioo s u) :
    ∃ i < k, t i ≤ s ∧ u ≤ t (i + 1) := by
  classical
  have hP : ∃ j, s < t j ∧ j ≤ k := ⟨k, by rw [hk]; linarith, le_rfl⟩
  have hm : s < t (Nat.find hP) ∧ Nat.find hP ≤ k := Nat.find_spec hP
  have hm0 : Nat.find hP ≠ 0 := by
    intro h
    have h1 := hm.1
    rw [h, h0] at h1
    linarith
  have hi : t (Nat.find hP - 1) ≤ s := by
    by_contra hcon
    exact Nat.find_min hP (Nat.sub_lt (Nat.pos_of_ne_zero hm0) one_pos)
      ⟨lt_of_not_ge hcon, by omega⟩
  have hu' : u ≤ t (Nat.find hP) := by
    by_contra hcon
    exact hB (t (Nat.find hP)) (Finset.mem_image.2 ⟨Nat.find hP, Finset.mem_range.2 (by omega),
      rfl⟩) ⟨hm.1, lt_of_not_ge hcon⟩
  refine ⟨Nat.find hP - 1, by omega, hi, ?_⟩
  rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)]
  exact hu'

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-! ### Variations: blind `IsVarSub` on `↥N` gives a project `IsVariation` in `V` -/

/-- The project-side 1-parameter family: `α'(x, s) = α(x e₀, s) ∈ N ⊆ V`. -/
noncomputable def amb2 (α : Rn 1 → ℝ → Bridge.Sub hN) : ℝ → ℝ → V := fun x s => incl hN (α (e1 x) s)

theorem amb2_zero (α : Rn 1 → ℝ → Bridge.Sub hN) : amb2 α 0 = incl hN ∘ α 0 := funext fun s => by
  show incl hN (α (e1 0) s) = incl hN (α 0 s)
  rw [map_zero]

theorem isVariation_of_isVarSub {U : Set (Rn 1)} {α : Rn 1 → ℝ → Bridge.Sub hN} {k : ℕ}
    {t : ℕ → ℝ} (h : IsVarSub (n := n) U α k t) :
    Morse.IsVariation N (e1 ⁻¹' U) (amb2 α) ((Finset.range (k + 1)).image t) := by
  obtain ⟨hU, h0U, ht0, htk, hlt, hend, hsm⟩ := h
  refine ⟨hU.preimage e1.continuous, ?_, fun _ _ _ _ => (α _ _).2, fun x hx => ?_,
    fun x hx => ?_, fun s u hs hsu hu hB => ?_⟩
  · show e1 0 ∈ U
    rw [map_zero]; exact h0U
  · show incl hN (α (e1 x) 0) = incl hN (α (e1 0) 0)
    rw [map_zero, (hend _ hx).2.1]
  · show incl hN (α (e1 x) 1) = incl hN (α (e1 0) 1)
    rw [map_zero, (hend _ hx).2.2]
  · obtain ⟨i, hi, hti, hui⟩ := exists_piece_of_free ht0 htk hs hsu hu hB
    have h1 : ContMDiffOn 𝓘(ℝ, Rn 1 × ℝ) 𝓘(ℝ, V) ∞ (fun x : Rn 1 × ℝ => incl hN (α x.1 x.2))
        (U ×ˢ Icc (t i) (t (i + 1))) := contMDiff_incl.comp_contMDiffOn (hsm i hi)
    have h2 := contMDiffOn_iff_contDiffOn.1 h1
    have hL : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (e1 p.1, p.2)) :=
      (e1.contDiff.comp contDiff_fst).prodMk contDiff_snd
    exact h2.comp hL.contDiffOn fun p hp => ⟨hp.1, hti.trans hp.2.1, hp.2.2.trans hui⟩

/-- The blind energy of `α u` is the project energy of the project-side family. -/
theorem efun_comp (α : Rn 1 → ℝ → Bridge.Sub hN) :
    (fun u : Rn 1 => Efun (n := n) (α u)) = (fun x => Morse.energy (amb2 α x) 0 1) ∘ e1.symm :=
  funext fun u => by
    show Efun (n := n) (α u) = Morse.energy (amb2 α (e1.symm u)) 0 1
    have e : amb2 α (e1.symm u) = incl hN ∘ α u := funext fun s => by
      show incl hN (α (e1 (e1.symm u)) s) = incl hN (α u s)
      rw [ContinuousLinearEquiv.apply_symm_apply]
    rw [e]
    exact Bridge.energy_eq (α u) 0 1



/-- A subdivision of `[0, 1]` avoiding a finite set (as in the Bridge's `isPW_lift`). -/
theorem exists_subdivision (B : Finset ℝ) :
    ∃ (k : ℕ) (t : ℕ → ℝ), t 0 = 0 ∧ t k = 1 ∧ (∀ i < k, t i < t (i + 1)) ∧
      ∀ i < k, 0 ≤ t i ∧ t (i + 1) ≤ 1 ∧ ∀ x ∈ B, x ∉ Ioo (t i) (t (i + 1)) := by
  classical
  have hlt : (0 : ℝ) < 1 := zero_lt_one
  set S : Finset ℝ := insert 0 (insert 1 (B.filter (· ∈ Ioo (0 : ℝ) 1)))
  have hS : ∀ x ∈ S, 0 ≤ x ∧ x ≤ 1 := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_filter] at hx
    rcases hx with rfl | rfl | ⟨-, hx⟩
    · exact ⟨le_rfl, hlt.le⟩
    · exact ⟨hlt.le, le_rfl⟩
    · exact ⟨hx.1.le, hx.2.le⟩
  have haS : (0 : ℝ) ∈ S := Finset.mem_insert_self _ _
  have hbS : (1 : ℝ) ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  set m := S.card
  have hm : 1 < m := Finset.one_lt_card.2 ⟨0, haS, 1, hbS, hlt.ne⟩
  set e := S.orderEmbOfFin rfl
  set t : ℕ → ℝ := fun j => if h : j < m then e ⟨j, h⟩ else 1
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

/-- Smoothness of maps from a normed space into `↥N`, read in `V` (the Bridge's
`contMDiffWithinAt_curve_iff` with a general source). -/
theorem contMDiffWithinAt_iff' {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Bridge.Sub hN} {s : Set E} {x : E} :
    ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, Rn n) ∞ f s x ↔ ContDiffWithinAt ℝ ∞ (incl hN ∘ f) s x := by
  constructor
  · intro h
    exact contMDiffWithinAt_iff_contDiffWithinAt.1
      ((contMDiff_incl (f x)).comp_contMDiffWithinAt x h)
  · intro h
    have hcont : ContinuousWithinAt f s x :=
      (Topology.IsInducing.subtypeVal.continuousWithinAt_iff (f := f)).2 h.continuousWithinAt
    rw [contMDiffWithinAt_iff_target]
    refine ⟨hcont, ?_⟩
    set σ := Morse.sliceAt hN (f x)
    have hφ : ContDiffAt ℝ ∞ (fun y => (σ.φ y).1) (incl hN (f x)) :=
      contDiff_fst.contDiffAt.comp _ ((Milnor.Problems.sliceChart_contDiffOn σ).contDiffAt
        (σ.φ.open_source.mem_nhds (Morse.mem_sliceAt_source hN (f x))))
    have e : (extChartAt 𝓘(ℝ, Rn n) (f x) ∘ f) = (fun y => (σ.φ y).1) ∘ (incl hN ∘ f) := rfl
    rw [e]
    exact contMDiffWithinAt_iff_contDiffWithinAt.2 (hφ.comp_contDiffWithinAt x h)

/-- The blind family lifted from a project family. -/
noncomputable def liftVar (α' : ℝ → ℝ → V) (p₀ : Bridge.Sub hN) : Rn 1 → ℝ → Bridge.Sub hN :=
  fun u => lift (α' (e1.symm u)) p₀

theorem incl_liftVar {U : Set ℝ} {α' : ℝ → ℝ → V} {B : Finset ℝ}
    (hα : Morse.IsVariation N U α' B) (p₀ : Bridge.Sub hN) {u : Rn 1} (hu : e1.symm u ∈ U)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : incl hN (liftVar α' p₀ u s) = α' (e1.symm u) s :=
  incl_lift p₀ (hα.mem _ hu s hs)

/-- **A project variation lifts to a blind variation**, for a subdivision avoiding its break
points. -/
theorem isVarSub_liftVar {U : Set ℝ} {α' : ℝ → ℝ → V} {B : Finset ℝ}
    (hα : Morse.IsVariation N U α' B) (p₀ : Bridge.Sub hN) {k : ℕ} {t : ℕ → ℝ} (ht0 : t 0 = 0)
    (htk : t k = 1) (hlt : ∀ i < k, t i < t (i + 1))
    (hgood : ∀ i < k, 0 ≤ t i ∧ t (i + 1) ≤ 1 ∧ ∀ x ∈ B, x ∉ Ioo (t i) (t (i + 1))) :
    IsVarSub (n := n) (e1.symm ⁻¹' U) (liftVar α' p₀) k t := by
  have h0 : e1.symm 0 ∈ U := by rw [map_zero]; exact hα.zero_mem
  refine ⟨hα.isOpen.preimage e1.symm.continuous, h0, ht0, htk, hlt, fun u hu => ⟨?_, ?_, ?_⟩,
    fun i hi => ?_⟩
  · exact isPW_lift (hα.isPiecewiseSmooth hu) (hα.mem _ hu) p₀
  · apply Subtype.ext
    show incl hN (liftVar α' p₀ u 0) = incl hN (liftVar α' p₀ 0 0)
    rw [incl_liftVar hα p₀ hu ⟨le_rfl, zero_le_one⟩, incl_liftVar hα p₀ h0 ⟨le_rfl, zero_le_one⟩,
      map_zero, hα.start _ hu]
  · apply Subtype.ext
    show incl hN (liftVar α' p₀ u 1) = incl hN (liftVar α' p₀ 0 1)
    rw [incl_liftVar hα p₀ hu ⟨zero_le_one, le_rfl⟩, incl_liftVar hα p₀ h0 ⟨zero_le_one, le_rfl⟩,
      map_zero, hα.finish _ hu]
  · obtain ⟨h0i, hi1, hBi⟩ := hgood i hi
    have hL : ContDiff ℝ ∞ (fun p : Rn 1 × ℝ => (e1.symm p.1, p.2)) :=
      (e1.symm.contDiff.comp contDiff_fst).prodMk contDiff_snd
    have hg : ContDiffOn ℝ ∞ (fun x : Rn 1 × ℝ => α' (e1.symm x.1) x.2)
        ((e1.symm ⁻¹' U) ×ˢ Icc (t i) (t (i + 1))) :=
      (hα.smooth (t i) (t (i + 1)) h0i (hlt i hi) hi1 hBi).comp
        (f := fun p : Rn 1 × ℝ => (e1.symm p.1, p.2)) hL.contDiffOn fun x hx => ⟨hx.1, hx.2⟩
    intro x hx
    rw [contMDiffWithinAt_iff']
    refine (hg x hx).congr (fun y hy => ?_) ?_
    · exact incl_liftVar hα p₀ hy.1 ⟨h0i.trans hy.2.1, hy.2.2.trans hi1⟩
    · exact incl_liftVar hα p₀ hx.1 ⟨h0i.trans hx.2.1, hx.2.2.trans hi1⟩


theorem efun_eq (pw : ℝ → Bridge.Sub hN) :
    Efun (n := n) pw = Morse.energy (incl hN ∘ pw) 0 1 := Bridge.energy_eq pw 0 1

/-- **The blind critical paths of `E` on `↥N` are the project's critical paths.** -/
theorem isCriticalPath_iff (pw : ℝ → Bridge.Sub hN) :
    IsCriticalPath (n := n) (Efun (n := n)) pw ↔ Morse.IsCriticalPath N (incl hN ∘ pw) := by
  constructor
  · -- blind ⇒ project: lift a project variation (and keep `pw` off `[0, 1]`)
    intro h U α' B hα hαc
    classical
    obtain ⟨k, t, ht0, htk, hlt, hgood⟩ := exists_subdivision B
    set p₀ : Bridge.Sub hN := ⟨α' 0 0, hα.mem 0 hα.zero_mem 0 ⟨le_rfl, zero_le_one⟩⟩
    have hvs := isVarSub_liftVar (n := n) hα p₀ ht0 htk hlt hgood
    have h0 : e1.symm 0 ∈ U := by rw [map_zero]; exact hα.zero_mem
    set α : Rn 1 → ℝ → Bridge.Sub hN := fun u s =>
      if s ∈ Icc (0 : ℝ) 1 then liftVar α' p₀ u s else pw s with hαdef
    have heqOn : ∀ u, EqOn (α u) (liftVar α' p₀ u) (Icc 0 1) := fun u s hs => by
      simp only [hαdef, if_pos hs]
    have hvs' : IsVarSub (n := n) (e1.symm ⁻¹' U) α k t := by
      obtain ⟨hU, h0U, ht0', htk', hlt', hend, hsm⟩ := hvs
      have hsub : ∀ i < k, Icc (t i) (t (i + 1)) ⊆ Icc 0 1 := fun i hi =>
        Icc_subset_Icc (hgood i hi).1 (hgood i hi).2.1
      refine ⟨hU, h0U, ht0', htk', hlt', fun u hu => ⟨?_, ?_, ?_⟩, fun i hi => ?_⟩
      · obtain ⟨k', t', h0', h1', hl', hs'⟩ := (hend u hu).1
        refine ⟨k', t', h0', h1', hl', fun j hj => (hs' j hj).congr fun s hs => heqOn u ?_⟩
        exact ⟨h0' ▸ Bridge.le_of_strictSeq hl' (Nat.zero_le j) hj.le |>.trans hs.1,
          hs.2.trans (h1' ▸ Bridge.le_of_strictSeq hl' (Nat.succ_le_of_lt hj) le_rfl)⟩
      · rw [heqOn u ⟨le_rfl, zero_le_one⟩, heqOn 0 ⟨le_rfl, zero_le_one⟩]; exact (hend u hu).2.1
      · rw [heqOn u ⟨zero_le_one, le_rfl⟩, heqOn 0 ⟨zero_le_one, le_rfl⟩]; exact (hend u hu).2.2
      · exact (hsm i hi).congr fun x hx => heqOn x.1 (hsub i hi hx.2)
    have hα0 : α 0 = pw := funext fun s => by
      by_cases hs : s ∈ Icc (0 : ℝ) 1
      · rw [heqOn 0 hs]
        apply Subtype.ext
        show incl hN (liftVar α' p₀ 0 s) = incl hN (pw s)
        rw [incl_liftVar hα p₀ h0 hs, map_zero]
        exact hαc s hs
      · simp only [hαdef, if_neg hs]
    have hF := h (e1.symm ⁻¹' U) α ⟨k, t, hvs'⟩ hα0
    have hev : (fun u : Rn 1 => Efun (n := n) (α u)) =ᶠ[𝓝 0]
        (fun x => Morse.energy (α' x) 0 1) ∘ e1.symm := by
      filter_upwards [(hα.isOpen.preimage e1.symm.continuous).mem_nhds h0] with u hu
      show Efun (n := n) (α u) = Morse.energy (α' (e1.symm u)) 0 1
      rw [efun_eq]
      exact Morse.energy_congr fun s hs => by
        show incl hN (α u s) = _
        rw [heqOn u hs]; exact incl_liftVar hα p₀ hu hs
    have hF2 := hF.congr_of_eventuallyEq hev.symm
    have hF2' : HasFDerivAt ((fun x => Morse.energy (α' x) 0 1) ∘ e1.symm)
        (0 : Rn 1 →L[ℝ] ℝ) (e1 0) := by
      rw [map_zero]; exact hF2
    have hF3 := (hF2'.comp (0 : ℝ) e1.hasFDerivAt).hasDerivAt
    have hfun : ((fun x => Morse.energy (α' x) 0 1) ∘ e1.symm) ∘ e1 =
        fun x => Morse.energy (α' x) 0 1 := funext fun x => by simp
    rw [hfun] at hF3
    simpa using hF3
  · -- project ⇒ blind: a blind variation is a project variation
    rintro h U α ⟨k, t, hvs⟩ hα0
    have hv := isVariation_of_isVarSub hvs
    have hd := h _ _ _ hv fun s _ => by rw [amb2_zero, hα0]
    have hd' : HasFDerivAt (fun x => Morse.energy (amb2 α x) 0 1) (0 : ℝ →L[ℝ] ℝ) (e1.symm 0) := by
      rw [map_zero]
      have := hd.hasFDerivAt
      simpa using this
    rw [efun_comp]
    have := hd'.comp (0 : Rn 1) e1.symm.hasFDerivAt
    simpa using this

end Vocab

#rt_check RoundTrip.V8_4.A_to_B [Morse.IsCriticalPath]
#rt_check RoundTrip.V8_4.B_to_A [Morse.IsCriticalPath]
#rt_overlap RoundTrip.V8_4.B_to_A [Morse.IsCriticalPath]

end RoundTrip.V8_4
