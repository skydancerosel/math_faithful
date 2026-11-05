import Morse
import RoundTrip.Check
import RoundTrip.Blind.V8_9
import RoundTrip.Bridge

open Set Filter Topology MeasureTheory
open scoped ContDiff Manifold RealInnerProductSpace Interval

namespace RoundTrip.V8_9

/-- The project's statement (universes instantiated at 0): for a slice submanifold `N ⊆ V` with the
induced metric and a 1-parameter variation `α` (`Morse.IsVariation N U α B`: `U ⊆ ℝ` open, `0 ∈ U`,
fixed end points, smooth on the closed strips `U × [s, t]` free of the finite break set `B`):
(12.2′) at every `u₀ ∈ U`, `u ↦ E(α_u)` has derivative `2·firstVariation(α_{u₀}, ∂α/∂u(u₀, ·))`;
(Theorem 12.2) at `u = 0`, for any `ω` equal to `α 0` on `[0, 1]`, the derivative is
`2·(-Σᶠ_{t∈(0,1)} ⟨W_t, Δ_t ω'⟩ - ∫₀¹ ⟨W_t, P(ω'')⟩ dt)`, `W = varField α`. -/
def A : Prop :=
  type_of% @Morse.IsVariation.hasDerivAt_energy.{0,0,0} ∧ type_of% @Morse.first_variation.{0,0,0}

theorem A_holds : A := ⟨@Morse.IsVariation.hasDerivAt_energy, @Morse.first_variation⟩

/-! Neither `A → B` nor `B → A` is proved; see `V8_9.json`. Below: the embedded special case. -/

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

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

theorem e1_symm_apply (v : Rn 1) : e1.symm v = v 0 := rfl

/-! ### Subdivisions -/

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

/-- **Dictionary: variation fields.** -/
theorem D_varField {U : Set (Rn 1)} {α : Rn 1 → ℝ → Bridge.Sub hN} {k : ℕ} {t : ℕ → ℝ}
    (h : IsVarSub (n := n) U α k t) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    D hN (α 0 s) (varField (n := n) α 0 s) = Morse.varField (amb2 α) s := by
  obtain ⟨hU, h0U, ht0, htk, hlt, -, hsm⟩ := h
  obtain ⟨i, hi, hsi⟩ := exists_piece_of_mem ht0 htk hlt hs
  have hι : ContMDiff 𝓘(ℝ, Rn 1) 𝓘(ℝ, Rn 1 × ℝ) ∞ (fun u : Rn 1 => (u, s)) :=
    contMDiff_iff_contDiff.2 (contDiff_id.prodMk contDiff_const)
  have hf : ContMDiffOn 𝓘(ℝ, Rn 1) 𝓘(ℝ, Rn n) ∞ (fun u => α u s) U :=
    (hsm i hi).comp hι.contMDiffOn fun u hu => ⟨hu, hsi⟩
  have hfd : MDifferentiableAt 𝓘(ℝ, Rn 1) 𝓘(ℝ, Rn n) (fun u => α u s) 0 :=
    ((hf 0 h0U).contMDiffAt (hU.mem_nhds h0U)).mdifferentiableAt (by simp)
  have h1 : HasMFDerivAt 𝓘(ℝ, Rn 1) 𝓘(ℝ, V) (incl hN ∘ fun u => α u s) 0
      ((D hN (α 0 s)).comp (mfderiv 𝓘(ℝ, Rn 1) 𝓘(ℝ, Rn n) (fun u => α u s) 0)) :=
    HasMFDerivAt.comp (0 : Rn 1)
      (((contMDiff_incl (α 0 s)).mdifferentiableAt (by simp)).hasMFDerivAt) hfd.hasMFDerivAt
  have h2 := hasMFDerivAt_iff_hasFDerivAt.1 h1
  have h2' : HasFDerivAt (incl hN ∘ fun u => α u s)
      ((D hN (α 0 s)).comp (mfderiv 𝓘(ℝ, Rn 1) 𝓘(ℝ, Rn n) (fun u => α u s) 0)) (e1 0) := by
    rw [map_zero]; exact h2
  have h3 := (h2'.comp (0 : ℝ) e1.hasFDerivAt).hasDerivAt
  exact h3.deriv.symm

/-- **Dictionary: one-sided velocities** (as in `Items/V8_7.lean`). -/
theorem D_mfderivWithin_curve (c : ℝ → Bridge.Sub hN) {s : Set ℝ} {t : ℝ}
    (hs : UniqueDiffWithinAt ℝ s t) :
    D hN (c t) (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) c s t 1) = derivWithin (incl hN ∘ c) s t := by
  by_cases h : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) c s t
  · exact ((hasDerivWithinAt_incl_comp h).derivWithin hs).symm
  · rw [mfderivWithin_zero_of_not_mdifferentiableWithinAt h,
      derivWithin_zero_of_not_differentiableWithinAt
        (mt mdifferentiableWithinAt_curve_iff.2 h)]
    exact map_zero _

/-- **Dictionary: the velocity jump** (as in `Items/V8_7.lean`). -/
theorem D_Vjump (c : ℝ → Bridge.Sub hN) (t : ℝ) :
    D hN (c t) (Vjump (n := n) c t) = Morse.jump (incl hN ∘ c) t := by
  have h1 := D_mfderivWithin_curve c (uniqueDiffWithinAt_Ici t)
  have h2 := D_mfderivWithin_curve c (uniqueDiffWithinAt_Iic t)
  exact (D_tsub_aux _ _ _).trans (congrArg₂ (· - ·) h1 h2)

/-- At an interior point of a closed piece, the second derivative within the piece is `c''`. -/
theorem derivWithin_derivWithin_eq {c : ℝ → V} {a b x : ℝ} (hx : x ∈ Ioo a b) :
    derivWithin (derivWithin c (Icc a b)) (Icc a b) x = deriv (deriv c) x := by
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with u hu
  exact derivWithin_of_mem_nhds (Icc_mem_nhds hu.1 hu.2)

/-- **Dictionary: accelerations.** A blind acceleration of `c` on a closed piece, read in `V`, is
the project's `accel` at the interior points of the piece. -/
theorem D_accel {c : ℝ → Bridge.Sub hN} {a b : ℝ} (hab : a < b)
    (hc : IsSmoothCurve (n := n) c (Icc a b)) {Acc : FA n c}
    (hA : HasCovDeriv (Bridge.conn (hN := hN)) c (Icc a b) (vel (n := n) c (Icc a b)) Acc)
    {x : ℝ} (hx : x ∈ Ioo a b) :
    D hN (c x) (Acc x) = Morse.accel hN (incl hN ∘ c) x := by
  have hs : RoundTrip.BridgePrelude.IsIntv (Icc a b) := ⟨ordConnected_Icc, uniqueDiffOn_Icc hab⟩
  have hA' : RoundTrip.BridgePrelude.HasCovDeriv (Bridge.conn (hN := hN)) c (Icc a b)
      (RoundTrip.BridgePrelude.vel (n := n) c (Icc a b)) Acc := hA
  have h := ((hasCovDeriv_iff' hs hc).1 hA').2 x (Ioo_subset_Icc_self hx)
  rw [derivWithin_congr (ambA_vel_eqOn hs.2 hc) (ambA_vel_eqOn hs.2 hc (Ioo_subset_Icc_self hx)),
    derivWithin_derivWithin_eq hx] at h
  show ambA c Acc x = _
  have e : Morse.prj hN ((incl hN ∘ c) x) = P hN (c x) := Morse.prj_of_mem hN (c x).2
  rw [h, Morse.accel, Morse.covD, e]

/-! ### The project side: smoothness of the slice, integrability, splitting -/

theorem contDiffOn_slice {U' : Set ℝ} {α' : ℝ → ℝ → V} {B : Finset ℝ}
    (hα : Morse.IsVariation N U' α' B) {s u : ℝ} (hs : 0 ≤ s) (hsu : s < u) (hu : u ≤ 1)
    (hB : ∀ x ∈ B, x ∉ Ioo s u) : ContDiffOn ℝ ∞ (α' 0) (Icc s u) :=
  (hα.smooth s u hs hsu hu hB).comp (contDiffOn_const.prodMk contDiffOn_id) fun _ hx =>
    ⟨hα.zero_mem, hx⟩

theorem differentiableAt_slice {U' : Set ℝ} {α' : ℝ → ℝ → V} {B : Finset ℝ}
    (hα : Morse.IsVariation N U' α' B) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hxB : x ∉ B) :
    DifferentiableAt ℝ (α' 0) x := by
  obtain ⟨s, s', h0s, hsx, hxs', hs'1, hBs⟩ := Morse.exists_piece_around B hx.1 hx.2 hxB
  exact ((contDiffOn_slice hα h0s (hsx.trans hxs') hs'1 hBs).contDiffAt
    (Icc_mem_nhds hsx hxs')).differentiableAt (by simp)

theorem intervalIntegrable_fv {U' : Set ℝ} {α' : ℝ → ℝ → V} {B : Finset ℝ}
    (hα : Morse.IsVariation N U' α' B) :
    IntervalIntegrable (fun x => ⟪Morse.varField α' x, Morse.accel hN (α' 0) x⟫) volume 0 1 := by
  have hX : ContinuousOn (Morse.varField α') (Icc 0 1) :=
    ((Morse.mem_pathTangent hN).1 (hα.varField_mem hN)).1.2.1
  refine Morse.intervalIntegrable_of_piecewise (B := B) (lo := 0) (hi := 1)
    (fun s u hs hsu hu hB => ?_) le_rfl zero_le_one le_rfl
  have hc := contDiffOn_slice hα hs hsu hu hB
  have hU : UniqueDiffOn ℝ (Icc s u) := uniqueDiffOn_Icc hsu
  have hd1 : ContDiffOn ℝ ∞ (derivWithin (α' 0) (Icc s u)) (Icc s u) :=
    hc.derivWithin hU (by simp)
  have hdd : ContinuousOn (derivWithin (derivWithin (α' 0) (Icc s u)) (Icc s u)) (Icc s u) :=
    (hd1.derivWithin hU (m := 0) (by simp)).continuousOn
  have hP : ContinuousOn (fun x => Morse.prj hN (α' 0 x)) (Icc s u) :=
    (Morse.ContDiffOn.prj_comp hN hc fun x hx =>
      hα.mem 0 hα.zero_mem x ⟨hs.trans hx.1, hx.2.trans hu⟩).continuousOn
  refine ⟨fun x => ⟪Morse.varField α' x,
    Morse.prj hN (α' 0 x) (derivWithin (derivWithin (α' 0) (Icc s u)) (Icc s u) x)⟫,
    (hX.mono (Icc_subset_Icc hs hu)).inner (hP.clm_apply hdd), fun x hx => ?_⟩
  simp only [Morse.accel, Morse.covD, derivWithin_derivWithin_eq hx]

theorem integral_split {f : ℝ → ℝ} {k : ℕ} {t : ℕ → ℝ} (h0 : t 0 = 0) (hk : t k = 1)
    (hlt : ∀ i < k, t i < t (i + 1)) (hf : IntervalIntegrable f volume 0 1) :
    ∫ x in (0 : ℝ)..1, f x = ∑ i ∈ Finset.range k, ∫ x in t i..t (i + 1), f x := by
  have hint : ∀ j < k, IntervalIntegrable f volume (t j) (t (j + 1)) := by
    intro j hj
    refine hf.mono_set ?_
    rw [uIcc_of_le (hlt j hj).le, uIcc_of_le zero_le_one]
    refine Icc_subset_Icc ?_ ?_
    · rw [← h0]; exact Bridge.le_of_strictSeq hlt (Nat.zero_le j) hj.le
    · rw [← hk]; exact Bridge.le_of_strictSeq hlt (Nat.succ_le_of_lt hj) le_rfl
  rw [intervalIntegral.sum_integral_adjacent_intervals hint, h0, hk]

theorem sum_filter_image {k : ℕ} {t : ℕ → ℝ} (h0 : t 0 = 0) (hk : t k = 1)
    (hlt : ∀ i < k, t i < t (i + 1)) (g : ℝ → ℝ) :
    ∑ x ∈ (Finset.range (k + 1)).image t with x ∈ Ioo (0 : ℝ) 1, g x =
      ∑ i ∈ Finset.Ico 1 k, g (t i) := by
  classical
  have hfilt : Finset.filter (fun x => x ∈ Ioo (0 : ℝ) 1) ((Finset.range (k + 1)).image t) =
      (Finset.Ico 1 k).image t := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨j, hj, rfl⟩, hx⟩
      refine ⟨j, ⟨?_, ?_⟩, rfl⟩
      · by_contra h
        have : j = 0 := by omega
        subst this
        rw [h0] at hx
        exact lt_irrefl 0 hx.1
      · by_contra h
        have : j = k := by omega
        subst this
        rw [hk] at hx
        exact lt_irrefl 1 hx.2
    · rintro ⟨j, ⟨hj1, hjk⟩, rfl⟩
      refine ⟨⟨j, by omega, rfl⟩, ?_, ?_⟩
      · rw [← h0]; exact Bridge.lt_of_strictSeq hlt (by omega) hjk.le
      · rw [← hk]; exact Bridge.lt_of_strictSeq hlt hjk le_rfl
  rw [hfilt, Finset.sum_image]
  intro i hi j hj hij
  simp only [Finset.coe_Ico, mem_Ico] at hi hj
  rcases lt_trichotomy i j with h | h | h
  · exact absurd hij (Bridge.lt_of_strictSeq hlt h hj.2.le).ne
  · exact h
  · exact absurd hij.symm (Bridge.lt_of_strictSeq hlt h hi.2.le).ne

open Bundle in
/-- **The blind right-hand side is the project's first variation** of the project-side family. -/
theorem fv_eq_rhs {U : Set (Rn 1)} {α : Rn 1 → ℝ → Bridge.Sub hN} {k : ℕ} {t : ℕ → ℝ}
    (hα : IsVarSub (n := n) U α k t) (Acc : ℕ → FA n (α 0))
    (hAcc : ∀ i < k, HasCovDeriv (Bridge.conn (hN := hN)) (α 0)
        (Set.Icc (t i) (t (i + 1))) (vel (n := n) (α 0) (Set.Icc (t i) (t (i + 1)))) (Acc i)) :
    Morse.firstVariation hN (amb2 α 0) (Morse.varField (amb2 α)) =
      - (∑ i ∈ Finset.Ico 1 k, inner ℝ (varField (n := n) α 0 (t i)) (Vjump (n := n) (α 0) (t i)))
      - ∑ i ∈ Finset.range k, ∫ s in (t i)..(t (i + 1)), inner ℝ (varField (n := n) α 0 s) (Acc i s) := by
  have hv := isVariation_of_isVarSub hα
  obtain ⟨hU, h0U, ht0, htk, hlt, hend, hsm⟩ := id hα
  rw [Morse.firstVariation, Morse.finsum_jump_eq_sum (B := (Finset.range (k + 1)).image t)
      (fun x hx hxB => differentiableAt_slice hv hx hxB),
    sum_filter_image ht0 htk hlt, integral_split ht0 htk hlt (intervalIntegrable_fv hv)]
  have hS : ∀ i ∈ Finset.Ico 1 k,
      ⟪Morse.varField (amb2 α) (t i), Morse.jump (amb2 α 0) (t i)⟫ =
        inner ℝ (varField (n := n) α 0 (t i)) (Vjump (n := n) (α 0) (t i)) := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hti : t i ∈ Icc (0 : ℝ) 1 := by
      constructor
      · rw [← ht0]; exact Bridge.le_of_strictSeq hlt (Nat.zero_le i) hi.2.le
      · rw [← htk]; exact Bridge.le_of_strictSeq hlt hi.2.le le_rfl
    show _ = ⟪D hN (α 0 (t i)) (varField (n := n) α 0 (t i)),
      D hN (α 0 (t i)) (Vjump (n := n) (α 0) (t i))⟫
    rw [D_varField hα hti, D_Vjump, ← amb2_zero]
  have hι : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn 1 × ℝ) ∞ (fun x : ℝ => ((0 : Rn 1), x)) :=
    contMDiff_iff_contDiff.2 (contDiff_const.prodMk contDiff_id)
  have hI : ∀ i ∈ Finset.range k,
      ∫ x in t i..t (i + 1), ⟪Morse.varField (amb2 α) x, Morse.accel hN (amb2 α 0) x⟫ =
        ∫ x in t i..t (i + 1), inner ℝ (varField (n := n) α 0 x) (Acc i x) := by
    intro i hi
    rw [Finset.mem_range] at hi
    refine intervalIntegral.integral_congr_Ioo_of_le (hlt i hi).le fun x hx => ?_
    have hxI : x ∈ Icc (0 : ℝ) 1 := by
      constructor
      · rw [← ht0]; exact (Bridge.le_of_strictSeq hlt (Nat.zero_le i) hi.le).trans hx.1.le
      · rw [← htk]; exact hx.2.le.trans (Bridge.le_of_strictSeq hlt (Nat.succ_le_of_lt hi) le_rfl)
    have hcurve : IsSmoothCurve (n := n) (α 0) (Icc (t i) (t (i + 1))) :=
      (hsm i hi).comp hι.contMDiffOn fun x hx => ⟨h0U, hx⟩
    show _ = ⟪D hN (α 0 x) (varField (n := n) α 0 x), D hN (α 0 x) (Acc i x)⟫
    rw [D_varField hα hxI, D_accel (hlt i hi) hcurve (hAcc i hi) hx, ← amb2_zero]
  rw [Finset.sum_congr rfl hS, Finset.sum_congr rfl hI]

/-! ### Reverse dictionary: project variations give blind variations -/

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

/-- Accelerations exist on the pieces (the Bridge's `covA`). -/
theorem exists_acc {c : ℝ → Bridge.Sub hN} {k : ℕ} {t : ℕ → ℝ} (hlt : ∀ i < k, t i < t (i + 1))
    (hc : ∀ i < k, IsSmoothCurve (n := n) c (Icc (t i) (t (i + 1)))) :
    ∃ Acc : ℕ → FA n c, ∀ i < k, HasCovDeriv (Bridge.conn (hN := hN)) c
        (Set.Icc (t i) (t (i + 1))) (vel (n := n) c (Set.Icc (t i) (t (i + 1)))) (Acc i) := by
  refine ⟨fun i => covA c (Icc (t i) (t (i + 1))) (vel (n := n) c (Icc (t i) (t (i + 1)))),
    fun i hi => ?_⟩
  set s := Icc (t i) (t (i + 1))
  have hs : RoundTrip.BridgePrelude.IsIntv s := ⟨ordConnected_Icc, uniqueDiffOn_Icc (hlt i hi)⟩
  have hci := hc i hi
  have hc' : ContDiffOn ℝ ∞ (incl hN ∘ c) s := isSmoothCurve_iff.1 hci
  have hv : RoundTrip.BridgePrelude.IsSmoothAlong c s (RoundTrip.BridgePrelude.vel (n := n) c s) :=
    isSmoothAlong_iff.2 ⟨hci, (hc'.derivWithin hs.2 (by simp)).congr (ambA_vel_eqOn hs.2 hci)⟩
  exact (hasCovDeriv_iff hs hci).2 ⟨hv, fun _ _ => rfl⟩

/-- `firstVariation` only depends on the path on `[0, 1]` (as in the project's proof of
`first_variation`). -/
theorem fv_congr_path {c c' X : ℝ → V} (h : ∀ t ∈ Icc (0 : ℝ) 1, c t = c' t) :
    Morse.firstVariation hN c X = Morse.firstVariation hN c' X := by
  have hev : ∀ t ∈ Ioo (0 : ℝ) 1, c =ᶠ[𝓝 t] c' := fun t ht => by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
    exact h x (Ioo_subset_Icc_self hx)
  have hjump : ∀ t ∈ Ioo (0 : ℝ) 1, Morse.jump c t = Morse.jump c' t := fun t ht =>
    Morse.jump_congr (hev t ht)
  have hacc : ∀ t ∈ Ioo (0 : ℝ) 1, Morse.accel hN c t = Morse.accel hN c' t := fun t ht => by
    rw [Morse.accel, Morse.accel, Morse.covD, Morse.covD, (hev t ht).deriv.deriv_eq,
      (hev t ht).self_of_nhds]
  have h1 : ∫ t in (0 : ℝ)..1, ⟪X t, Morse.accel hN c t⟫ =
      ∫ t in (0 : ℝ)..1, ⟪X t, Morse.accel hN c' t⟫ :=
    intervalIntegral.integral_congr_Ioo_of_le zero_le_one fun t ht => by
      simp only [hacc t ht]
  have h2 : ∑ᶠ t ∈ Ioo (0 : ℝ) 1, ⟪X t, Morse.jump c t⟫ =
      ∑ᶠ t ∈ Ioo (0 : ℝ) 1, ⟪X t, Morse.jump c' t⟫ :=
    finsum_mem_congr rfl fun t ht => by rw [hjump t ht]
  rw [Morse.firstVariation, Morse.firstVariation, h1, h2]

end Emb

open Bundle in
/-- B on embedded manifolds: `M = ↥N` with the induced metric and the induced Levi-Civita
connection (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
    ∀ (U : Set (Rn 1)) (α : Rn 1 → ℝ → Bridge.Sub hN) (k : ℕ) (t : ℕ → ℝ),
      IsVarSub (n := n) U α k t →
    ∀ A : ℕ → FA n (α 0), (∀ i < k, HasCovDeriv (Bridge.conn (hN := hN)) (α 0)
        (Set.Icc (t i) (t (i + 1))) (vel (n := n) (α 0) (Set.Icc (t i) (t (i + 1)))) (A i)) →
      DifferentiableAt ℝ (fun u : Rn 1 => Efun (n := n) (α u)) 0 ∧
      (1 / 2 : ℝ) * fderiv ℝ (fun u : Rn 1 => Efun (n := n) (α u)) 0 (EuclideanSpace.single 0 (1 : ℝ)) =
        - (∑ i ∈ Finset.Ico 1 k, inner ℝ (varField (n := n) α 0 (t i)) (Vjump (n := n) (α 0) (t i)))
        - ∑ i ∈ Finset.range k, ∫ s in (t i)..(t (i + 1)), inner ℝ (varField (n := n) α 0 s) (A i s)

/-- `B_emb` is a special case of B (the induced connection is Levi-Civita, `Bridge.conn_isLC`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

open Emb Bridge Bundle in
/-- **A implies B on embedded manifolds**, from A's `first_variation` through the dictionary
(variations `Emb.isVariation_of_isVarSub`, energies `Emb.efun_comp`, variation fields
`Emb.D_varField`, jumps `Emb.D_Vjump`, accelerations `Emb.D_accel`), with the jump sum reindexed
by `Morse.finsum_jump_eq_sum` (item V8_7) and the integral split along the subdivision. -/
theorem A_to_B_emb : A → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN _ U α k t hα Acc hAcc
  have hv := isVariation_of_isVarSub hα
  obtain ⟨hU, h0U, ht0, htk, hlt, hend, hsm⟩ := id hα
  have hfv := hA.2 hN hv (c := amb2 α 0) (fun _ _ => rfl)
  set d := 2 * Morse.firstVariation hN (amb2 α 0) (Morse.varField (amb2 α)) with hd
  have h1 : HasFDerivAt (fun x => Morse.energy (amb2 α x) 0 1)
      (ContinuousLinearMap.toSpanSingleton ℝ d) (e1.symm 0) := by
    rw [map_zero]; exact hfv.hasFDerivAt
  have hF : HasFDerivAt (fun u : Rn 1 => Efun (n := n) (α u))
      ((ContinuousLinearMap.toSpanSingleton ℝ d).comp (e1.symm : Rn 1 →L[ℝ] ℝ)) 0 := by
    rw [efun_comp]
    exact h1.comp (0 : Rn 1) e1.symm.hasFDerivAt
  refine ⟨hF.differentiableAt, ?_⟩
  rw [hF.fderiv]
  have e1s : e1.symm (EuclideanSpace.single 0 (1 : ℝ)) = 1 := by
    rw [e1_symm_apply]; simp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    ContinuousLinearEquiv.coe_coe, e1s, one_smul, hd]
  rw [fv_eq_rhs hα Acc hAcc]
  ring

/-- A's two claims for slice submanifolds modelled on `ℝⁿ` (connected, as in B). -/
def A_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
    (∀ {U : Set ℝ} {α' : ℝ → ℝ → V} {B : Finset ℝ}, Morse.IsVariation N U α' B →
      ∀ {u₀ : ℝ}, u₀ ∈ U → HasDerivAt (fun u => Morse.energy (α' u) 0 1)
        (2 * Morse.firstVariation hN (α' u₀) fun t => deriv (fun v => α' v t) u₀) u₀) ∧
    (∀ {U : Set ℝ} {α' : ℝ → ℝ → V} {B : Finset ℝ}, Morse.IsVariation N U α' B →
      ∀ {c : ℝ → V}, (∀ t ∈ Icc (0 : ℝ) 1, α' 0 t = c t) →
        HasDerivAt (fun u => Morse.energy (α' u) 0 1)
          (2 * Morse.firstVariation hN c (Morse.varField α')) 0)

open Emb Bridge in
/-- B on embedded manifolds gives the first variation formula at `u = 0` for every project
variation (lifted to a blind variation along a subdivision avoiding its break points). -/
theorem fv_of_B_emb (h : B_emb) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] {n : ℕ} {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}
    [ConnectedSpace (Bridge.Sub hN)] {U : Set ℝ} {α' : ℝ → ℝ → V} {B : Finset ℝ}
    (hα : Morse.IsVariation N U α' B) :
    HasDerivAt (fun u => Morse.energy (α' u) 0 1)
      (2 * Morse.firstVariation hN (α' 0) (Morse.varField α')) 0 := by
  obtain ⟨k, t, ht0, htk, hlt, hgood⟩ := exists_subdivision B
  set p₀ : Bridge.Sub hN := ⟨α' 0 0, hα.mem 0 hα.zero_mem 0 ⟨le_rfl, zero_le_one⟩⟩
  have hvs := isVarSub_liftVar (n := n) hα p₀ ht0 htk hlt hgood
  have h0 : e1.symm 0 ∈ U := by rw [map_zero]; exact hα.zero_mem
  have hι : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn 1 × ℝ) ∞ (fun x : ℝ => ((0 : Rn 1), x)) :=
    contMDiff_iff_contDiff.2 (contDiff_const.prodMk contDiff_id)
  have hcurve : ∀ i < k, IsSmoothCurve (n := n) (liftVar α' p₀ 0) (Icc (t i) (t (i + 1))) :=
    fun i hi => (hvs.2.2.2.2.2.2 i hi).comp hι.contMDiffOn fun x hx => ⟨hvs.2.1, hx⟩
  obtain ⟨Acc, hAcc⟩ := exists_acc hlt hcurve
  obtain ⟨hdiff, hval⟩ := h V W n N hN (e1.symm ⁻¹' U) (liftVar α' p₀) k t hvs Acc hAcc
  rw [← fv_eq_rhs hvs Acc hAcc] at hval
  have hfvq : Morse.firstVariation hN (amb2 (liftVar α' p₀) 0) (Morse.varField (amb2 (liftVar α' p₀)))
      = Morse.firstVariation hN (α' 0) (Morse.varField α') := by
    rw [fv_congr_path (c' := α' 0), Morse.firstVariation_congr_field hN]
    · intro s hs
      unfold Morse.varField
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [hα.isOpen.mem_nhds hα.zero_mem] with x hx
      show incl hN (liftVar α' p₀ (e1 x) s) = α' x s
      rw [incl_liftVar hα p₀ (by rwa [ContinuousLinearEquiv.symm_apply_apply]) hs,
        ContinuousLinearEquiv.symm_apply_apply]
    · intro s hs
      rw [amb2_zero]
      show incl hN (liftVar α' p₀ 0 s) = α' 0 s
      rw [incl_liftVar hα p₀ h0 hs, map_zero]
  rw [hfvq] at hval
  have hev : (fun u : Rn 1 => Efun (n := n) (liftVar α' p₀ u)) =ᶠ[𝓝 0]
      (fun x => Morse.energy (α' x) 0 1) ∘ e1.symm := by
    filter_upwards [(hα.isOpen.preimage e1.symm.continuous).mem_nhds h0] with u hu
    show Efun (n := n) (liftVar α' p₀ u) = Morse.energy (α' (e1.symm u)) 0 1
    rw [show Efun (n := n) (liftVar α' p₀ u) = Morse.energy (incl hN ∘ liftVar α' p₀ u) 0 1 from
      Bridge.energy_eq _ 0 1]
    exact Morse.energy_congr fun s hs => incl_liftVar hα p₀ hu hs
  have hF2 := hdiff.hasFDerivAt.congr_of_eventuallyEq hev.symm
  have hF2' : HasFDerivAt ((fun x => Morse.energy (α' x) 0 1) ∘ e1.symm)
      (fderiv ℝ (fun u : Rn 1 => Efun (n := n) (liftVar α' p₀ u)) 0) (e1 0) := by
    rw [map_zero]; exact hF2
  have hF3 := (hF2'.comp (0 : ℝ) e1.hasFDerivAt).hasDerivAt
  have hfun : ((fun x => Morse.energy (α' x) 0 1) ∘ e1.symm) ∘ e1 =
      fun x => Morse.energy (α' x) 0 1 := funext fun x => by simp
  rw [hfun] at hF3
  have hval' : ((fderiv ℝ (fun u : Rn 1 => Efun (n := n) (liftVar α' p₀ u)) 0).comp
      (e1 : ℝ →L[ℝ] Rn 1)) 1 = 2 * Morse.firstVariation hN (α' 0) (Morse.varField α') := by
    show fderiv ℝ (fun u : Rn 1 => Efun (n := n) (liftVar α' p₀ u)) 0 (e1 1) = _
    rw [e1_apply]
    linarith
  rw [hval'] at hF3
  exact hF3

open Emb in
/-- **B on embedded manifolds implies A** (for slice submanifolds modelled on `ℝⁿ`). -/
theorem B_emb_to_A_emb : B_emb → A_emb := by
  intro h V _ _ _ W _ _ _ n N hN _
  have hfv0 : ∀ {U : Set ℝ} {α' : ℝ → ℝ → V} {B : Finset ℝ}, Morse.IsVariation N U α' B →
      ∀ {c : ℝ → V}, (∀ t ∈ Icc (0 : ℝ) 1, α' 0 t = c t) →
        HasDerivAt (fun u => Morse.energy (α' u) 0 1)
          (2 * Morse.firstVariation hN c (Morse.varField α')) 0 := by
    intro U α' B hα c hc
    rw [← fv_congr_path hc]
    exact fv_of_B_emb h hα
  refine ⟨fun {U α' B} hα u₀ hu₀ => ?_, hfv0⟩
  -- shift the parameter
  have hsh : Morse.IsVariation N ((fun u => u₀ + u) ⁻¹' U) (fun u => α' (u₀ + u)) B := by
    have h0' : u₀ + 0 ∈ U := by rwa [add_zero]
    refine ⟨hα.isOpen.preimage (continuous_const.add continuous_id), h0',
      fun u hu t ht => hα.mem _ hu t ht, fun u hu => (hα.start _ hu).trans (hα.start _ h0').symm,
      fun u hu => (hα.finish _ hu).trans (hα.finish _ h0').symm, fun s t hs hst ht hB => ?_⟩
    have hL : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (u₀ + p.1, p.2)) :=
      (contDiff_const.add contDiff_fst).prodMk contDiff_snd
    exact (hα.smooth s t hs hst ht hB).comp (f := fun p : ℝ × ℝ => (u₀ + p.1, p.2))
      hL.contDiffOn fun p hp => ⟨hp.1, hp.2⟩
  have h1 := hfv0 hsh (c := α' u₀) fun t _ => by simp only [add_zero]
  have hvf : Morse.varField (fun u => α' (u₀ + u)) = fun t => deriv (fun v => α' v t) u₀ :=
    funext fun t => by
      unfold Morse.varField
      rw [deriv_comp_const_add (fun v => α' v t) u₀ 0, add_zero]
  rw [hvf] at h1
  have h1' : HasDerivAt (fun u => Morse.energy (α' (u₀ + u)) 0 1)
      (2 * Morse.firstVariation hN (α' u₀) fun t => deriv (fun v => α' v t) u₀) (-u₀ + u₀) := by
    rwa [neg_add_cancel]
  have h2 := HasDerivAt.comp_const_add (-u₀) u₀ h1'
  simpa only [add_neg_cancel_left] using h2

theorem B_to_A_emb : B → A_emb := fun hB => B_emb_to_A_emb (B_to_B_emb hB)

#rt_check RoundTrip.V8_9.A_to_B_emb [Morse.IsVariation.hasDerivAt_energy, Morse.first_variation]
#rt_check RoundTrip.V8_9.B_to_A_emb [Morse.IsVariation.hasDerivAt_energy, Morse.first_variation]
#rt_overlap RoundTrip.V8_9.B_to_A_emb [Morse.IsVariation.hasDerivAt_energy, Morse.first_variation]

end RoundTrip.V8_9
