import Morse
import RoundTrip.L2.Blind.Morse_PathSp
namespace RoundTrip.L2.Morse_PathSp

open Set Filter Topology MeasureTheory
open scoped ContDiff unitInterval ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ### Piecewise smooth paths and the distance `ρ` -/

/-- The blind piecewise smoothness on `[0, 1]` is the project's (continuity on `[0, 1]` follows
from smoothness on the pieces). -/
theorem isPWS_iff (c : ℝ → V) : IsPWS c ↔ Morse.IsPiecewiseSmooth c 0 1 := by
  constructor
  · rintro ⟨S, hS⟩
    exact ⟨zero_le_one, Morse.continuousOn_of_piecewise fun s t hs hst ht hB =>
      (hS s t hs hst ht hB).continuousOn, S, hS⟩
  · rintro ⟨-, -, S, hS⟩
    exact ⟨S, hS⟩

/-- Affine reparametrisation of a piecewise smooth path on `[a, b]` to `[0, 1]`. -/
theorem isPiecewiseSmooth_affine {c : ℝ → V} {a b : ℝ} (hc : Morse.IsPiecewiseSmooth c a b)
    (hab : a < b) : Morse.IsPiecewiseSmooth (fun s => c ((b - a) * s + a)) 0 1 := by
  obtain ⟨-, hcont, B, hB⟩ := hc
  have hh : 0 < b - a := sub_pos.2 hab
  have hmaps : ∀ {s s' : ℝ}, 0 ≤ s → s' ≤ 1 → MapsTo (fun s => (b - a) * s + a) (Icc s s')
      (Icc ((b - a) * s + a) ((b - a) * s' + a)) := fun _ _ t ht =>
    ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  refine ⟨zero_le_one, hcont.comp (by fun_prop) fun t ht => ⟨by nlinarith [ht.1],
    by nlinarith [ht.2]⟩, B.image fun t => (t - a) / (b - a), fun s s' hs hss' hs' hB' => ?_⟩
  have hc' : ContDiffOn ℝ ∞ c (Icc ((b - a) * s + a) ((b - a) * s' + a)) := by
    refine hB _ _ (by nlinarith) (by nlinarith) (by nlinarith) fun x hx hxI => ?_
    refine hB' ((x - a) / (b - a)) (Finset.mem_image_of_mem _ hx) ⟨?_, ?_⟩
    · rw [lt_div_iff₀ hh]; linarith [hxI.1]
    · rw [div_lt_iff₀ hh]; linarith [hxI.2]
  exact hc'.comp (by fun_prop) (hmaps hs hs')

/-- The length is invariant under the affine reparametrisation. -/
theorem pathLength_affine (c : ℝ → V) {a b : ℝ} (hab : a < b) :
    Morse.pathLength (fun s => c ((b - a) * s + a)) 0 1 = Morse.pathLength c a b := by
  have hh : 0 < b - a := sub_pos.2 hab
  rw [Morse.pathLength, Morse.pathLength]
  simp_rw [Morse.deriv_comp_affine c (b - a) a, norm_smul, Real.norm_of_nonneg hh.le]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_add (fun x => ‖deriv c x‖) hh.ne' a, smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]
  simp

/-- The blind set of lengths of paths on `[0, 1]`. -/
def lens (N : Set V) (x y : V) : Set ℝ :=
  {L | ∃ c : ℝ → V, IsPWS c ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, c t ∈ N) ∧ c 0 = x ∧ c 1 = y ∧ len c = L}

theorem pathLengths_eq (N : Set V) (x y : V) :
    Morse.pathLengths (N := N) x y = ENNReal.ofReal '' lens N x y := by
  ext L
  constructor
  · rintro ⟨c, a, b, hc, hcN, ha, hb, rfl⟩
    rcases eq_or_lt_of_le hc.1 with rfl | hab
    · refine ⟨0, ⟨fun _ => x, (isPWS_iff _).2 (Morse.IsPiecewiseSmooth.of_contDiff contDiff_const
        zero_le_one), fun _ _ => ha ▸ hcN a ⟨le_rfl, le_rfl⟩, rfl, ?_, by simp [len]⟩, ?_⟩
      · rw [← hb, ha]
      · simp [Morse.pathLength]
    · refine ⟨Morse.pathLength c a b, ⟨fun s => c ((b - a) * s + a),
        (isPWS_iff _).2 (isPiecewiseSmooth_affine hc hab), fun t ht => hcN _
        ⟨by nlinarith [ht.1, sub_pos.2 hab], by nlinarith [ht.2, sub_pos.2 hab]⟩,
        by simpa using ha, by simpa using hb, ?_⟩, rfl⟩
      rw [← pathLength_affine c hab]
      rfl
  · rintro ⟨L, ⟨c, hc, hcN, h0, h1, rfl⟩, rfl⟩
    exact ⟨c, 0, 1, (isPWS_iff c).1 hc, hcN, h0, h1, rfl⟩

theorem toReal_sInf_ofReal_image {S : Set ℝ} (hS : ∀ L ∈ S, 0 ≤ L) :
    (sInf (ENNReal.ofReal '' S)).toReal = sInf S := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  · rw [← Monotone.map_csInf_of_continuousAt ENNReal.continuous_ofReal.continuousAt
      (fun _ _ h => ENNReal.ofReal_le_ofReal h) hne ⟨0, hS⟩, ENNReal.toReal_ofReal (Real.sInf_nonneg hS)]

/-- **The blind distance `ρ` is the project's `riemDist`** (read in `ℝ`; `0` = `toReal ⊤` when
there is no path). -/
theorem rho_eq (N : Set V) (x y : V) : rho N x y = (Morse.riemDist (N := N) x y).toReal := by
  rw [Morse.riemDist, pathLengths_eq, toReal_sInf_ofReal_image]
  · rfl
  · rintro L ⟨c, -, -, -, -, rfl⟩
    exact intervalIntegral.integral_nonneg zero_le_one fun _ _ => norm_nonneg _

/-! ### The comparison map `Ω (project) → Ω (blind)`: restriction to `[0, 1]` -/

section Map

variable {N : Set V} {p q : V}

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] in
theorem ext_eq (w : I → V) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ext w t = w ⟨t, ht⟩ := by
  simp [ext, projIcc_of_mem _ ht]

/-- Restriction to `[0, 1]` of a project path. -/
noncomputable def toT (γ : Morse.PathSp N p q) : T N p q :=
  ⟨fun t => γ.1 t, by
    obtain ⟨-, -, B, hB⟩ := γ.2.1
    exact ⟨B, fun a b ha hab hb hBab => (hB a b ha hab hb hBab).congr fun t ht => by
      rw [ext_eq _ ⟨ha.trans ht.1, ht.2.trans hb⟩]⟩, fun t => γ.2.2.1 t t.2,
    by simpa using γ.2.2.2.1, by simpa using γ.2.2.2.2⟩

/-- The extension (constant off `[0, 1]`) of a blind path, as a project path. -/
noncomputable def ofT (w : T N p q) : Morse.PathSp N p q :=
  ⟨ext w.1, (isPWS_iff _).1 w.2.1, fun t ht => by rw [ext_eq _ ht]; exact w.2.2.1 _,
    by rw [ext_eq _ ⟨le_rfl, zero_le_one⟩]; exact w.2.2.2.1,
    by rw [ext_eq _ ⟨zero_le_one, le_rfl⟩]; exact w.2.2.2.2⟩

theorem toT_ofT (w : T N p q) : toT (ofT w) = w := by
  refine Subtype.ext (funext fun t => ?_)
  change ext w.1 t = w.1 t
  rw [ext_eq _ t.2]

/-- **The comparison map is surjective.** -/
theorem toT_surjective : Function.Surjective (toT : Morse.PathSp N p q → T N p q) :=
  fun w => ⟨ofT w, toT_ofT w⟩

/-- Two project paths have the same image iff they agree on `[0, 1]`. -/
theorem toT_eq_iff (γ γ' : Morse.PathSp N p q) :
    toT γ = toT γ' ↔ EqOn γ.1 γ'.1 (Icc 0 1) := by
  constructor
  · intro h t ht
    exact congrFun (congrArg Subtype.val h) ⟨t, ht⟩
  · intro h
    exact Subtype.ext (funext fun t => h t.2)

/-- Two paths of `Ω(N; p, q)` are at finite uniform distance (copied from the layer-1 item
`V10_1`). -/
theorem supDist_ne_top {c c' : ℝ → V} (hc : c ∈ Morse.pathSpace N p q)
    (hc' : c' ∈ Morse.pathSpace N p q) : Morse.PathSp.supDist N c c' ≠ ⊤ := by
  have key : ∀ {c : ℝ → V}, c ∈ Morse.pathSpace N p q → ∀ t ∈ Icc (0 : ℝ) 1,
      Morse.riemDist (N := N) p (c t) ≤ ENNReal.ofReal (Morse.pathLength c 0 1) := by
    intro c hc t ht
    have h1 := Morse.riemDist_le_pathLength (N := N) (hc.1.mono le_rfl ht.1 ht.2)
      (fun s hs => hc.2.1 s ⟨hs.1, hs.2.trans ht.2⟩)
    rw [hc.2.2.1] at h1
    exact h1.trans (ENNReal.ofReal_le_ofReal (hc.1.isAdmissible.pathLength_le le_rfl ht.1 ht.2))
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal (Morse.pathLength c 0 1) +
    ENNReal.ofReal (Morse.pathLength c' 0 1)) (by simp) ?_
  refine iSup₂_le fun t ht => ?_
  calc Morse.riemDist (N := N) (c t) (c' t)
      ≤ Morse.riemDist (N := N) (c t) p + Morse.riemDist (N := N) p (c' t) :=
        Morse.riemDist_triangle _ _ _
    _ ≤ _ := add_le_add ((Morse.riemDist_comm _ _).trans_le (key hc t ht)) (key hc' t ht)

theorem edist_ne_top (γ γ' : Morse.PathSp N p q) : edist γ γ' ≠ ⊤ := by
  rw [Morse.PathSp.edist_def]
  exact ENNReal.add_ne_top.2 ⟨supDist_ne_top γ.2 γ'.2, ENNReal.ofReal_ne_top⟩

/-- **Milnor's metric agrees**: the blind `d` of the restrictions is the project's `edist`
(which is finite on `Ω`). -/
theorem dist_toT (γ γ' : Morse.PathSp N p q) : dist (toT γ) (toT γ') = (edist γ γ').toReal := by
  have hsup : (⨆ t : I, rho N ((toT γ).1 t) ((toT γ').1 t)) =
      (Morse.PathSp.supDist N γ γ').toReal := by
    rw [Morse.PathSp.supDist, iSup_subtype', ENNReal.toReal_iSup fun t => ne_top_of_le_ne_top
      (supDist_ne_top γ.2 γ'.2) (Morse.PathSp.riemDist_le_supDist t.2)]
    exact iSup_congr fun t => rho_eq _ _ _
  have hl2 : Real.sqrt (∫ t in (0 : ℝ)..1,
      (‖deriv (ext (toT γ).1) t‖ - ‖deriv (ext (toT γ').1) t‖) ^ 2) =
      Morse.PathSp.l2Dist γ γ' := by
    rw [Morse.PathSp.l2Dist]
    congr 1
    refine intervalIntegral.integral_congr_ae ?_
    have hne : ∀ᵐ τ ∂(volume : Measure ℝ), τ ≠ 1 := (countable_singleton 1).ae_notMem _
    filter_upwards [hne] with τ h1 hτ
    have hτ' : τ ∈ Ioo (0 : ℝ) 1 := by
      rw [uIoc_of_le zero_le_one] at hτ
      exact ⟨hτ.1, lt_of_le_of_ne hτ.2 h1⟩
    have hev : ∀ γ : Morse.PathSp N p q, ext (toT γ).1 =ᶠ[𝓝 τ] γ.1 := fun γ => by
      filter_upwards [Ioo_mem_nhds hτ'.1 hτ'.2] with x hx
      exact ext_eq _ (Ioo_subset_Icc_self hx)
    simp only [Morse.PathSp.speed, (hev γ).deriv_eq, (hev γ').deriv_eq]
  change d (toT γ) (toT γ') = _
  rw [Morse.PathSp.edist_def, ENNReal.toReal_add (supDist_ne_top γ.2 γ'.2) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (Morse.PathSp.l2Dist_nonneg _ _), d, hsup, hl2]

theorem d_toT_nonneg (γ γ' : Morse.PathSp N p q) : 0 ≤ d (toT γ) (toT γ') := by
  change 0 ≤ dist (toT γ) (toT γ')
  rw [dist_toT]
  exact ENNReal.toReal_nonneg

theorem d_toT_lt_iff (γ γ' : Morse.PathSp N p q) (r : ℝ) :
    d (toT γ) (toT γ') < r ↔ γ' ∈ Metric.eball γ (ENNReal.ofReal r) := by
  change dist (toT γ) (toT γ') < r ↔ _
  rw [dist_toT, Metric.mem_eball', ENNReal.lt_ofReal_iff_toReal_lt (edist_ne_top _ _)]

/-- **Milnor's topology agrees**: the project's (pseudo-emetric) topology on `Ω` is induced, via
restriction to `[0, 1]`, by the blind topology generated by the open `d`-balls. -/
theorem isInducing_toT : Topology.IsInducing (toT : Morse.PathSp N p q → T N p q) := by
  refine ⟨?_⟩
  change _ = TopologicalSpace.induced toT (TopologicalSpace.generateFrom _)
  rw [induced_generateFrom_eq]
  apply le_antisymm
  · refine le_generateFrom fun s hs => ?_
    obtain ⟨U, ⟨w, r, rfl⟩, rfl⟩ := hs
    obtain ⟨γ₀, rfl⟩ := toT_surjective w
    convert Metric.isOpen_eball (x := γ₀) (ε := ENNReal.ofReal r) using 1
    ext γ'
    exact d_toT_lt_iff γ₀ γ' r
  · rw [le_iff_nhds]
    intro x
    rw [Metric.nhds_basis_eball.ge_iff]
    intro ε hε
    obtain ⟨r, -, hr, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
    have hopen : IsOpen[TopologicalSpace.generateFrom
        (preimage toT '' {U | ∃ (w : T N p q) (r : ℝ), U = {w' | d w w' < r}})]
        (toT ⁻¹' {w' | d (toT x) w' < r}) :=
      TopologicalSpace.isOpen_generateFrom_of_mem ⟨_, ⟨toT x, r, rfl⟩, rfl⟩
    have hx : x ∈ toT ⁻¹' {w' | d (toT x) w' < r} := by
      change d (toT x) (toT x) < r
      rw [d_toT_lt_iff x x r, Metric.mem_eball, edist_self]
      exact hr
    refine Filter.mem_of_superset (@IsOpen.mem_nhds _ (TopologicalSpace.generateFrom _) _ _ hopen hx)
      fun γ' hγ' => ?_
    have := (d_toT_lt_iff x γ' r).1 hγ'
    exact Metric.eball_subset_eball hrε.le this

end Map

/-- **Agreement up to the values off `[0, 1]`**: restriction to `[0, 1]` is a surjection from the
project's `Ω(N; p, q)` (functions `ℝ → V`, values off `[0, 1]` free) onto the blind one (functions
on `[0, 1]`), identifying exactly the paths that agree on `[0, 1]`; it carries the project's
`edist` (finite on `Ω`) to Milnor's `d`, and the project's topology is the one induced from the
blind `d`-ball topology. So the blind space is the project's pseudo-emetric space with paths at
distance `0` identified. -/
theorem agree (N : Set V) (p q : V) :
    Function.Surjective (toT : Morse.PathSp N p q → T N p q) ∧
      (∀ γ γ' : Morse.PathSp N p q, toT γ = toT γ' ↔ EqOn γ.1 γ'.1 (Icc 0 1)) ∧
      (∀ γ γ' : Morse.PathSp N p q, edist γ γ' ≠ ⊤ ∧
        dist (toT γ) (toT γ') = (edist γ γ').toReal) ∧
      Topology.IsInducing (toT : Morse.PathSp N p q → T N p q) :=
  ⟨toT_surjective, toT_eq_iff, fun γ γ' => ⟨edist_ne_top γ γ', dist_toT γ γ'⟩, isInducing_toT⟩

end RoundTrip.L2.Morse_PathSp
