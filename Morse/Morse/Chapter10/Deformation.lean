import Morse.Chapter10.RetractionConv

/-!
Milnor, *Morse Theory*, §16, p. 91 (Theorem 16.2, second assertion): `B^a` is a deformation
retract of `Ω^a`, for a submanifold `N ⊆ ℝᴷ` with the induced metric.

# `Ω^a` deformation retracts onto `B^a`

## Milnor's text, paraphrased

(p. 91) The deformation `r_u` of `Int Ω^c` (`0 ≤ u ≤ 1`, `Morse/Chapter10/Retraction.lean`) has
`r_0 = ` identity and `r_1 = r`, a retraction onto `B = Int Ω(t₀, …, t_k)^c`; "it is easily
verified" that `r_u(ω)` is continuous in both variables.  Hence `B` is a deformation retract of
`Int Ω^c`, and since `E(r_u(ω)) ≤ E(ω)`, `B^a` is a deformation retract of `Ω^a` for `a < c`.

## In the embedded setting

For `B : Morse.BrokenSetup hN p q c m`:

* `Morse.PathSp.pathSpace_congr`, `Morse.PathSp.supDist_congr`, `Morse.PathSp.l2Dist_congr`:
  membership in `Ω` and Milnor's metric only see the values of paths on `[0, 1]`.
* `Morse.BrokenSetup.deform u γ`: **Milnor's `r_u(γ)` as a point of `Ω`** — `r_u(γ)` on
  `[0, 1]` and `γ` off `[0, 1]`, for `u ∈ [0, 1]` and `E(γ) < c` (and `γ` otherwise).
* `Morse.BrokenSetup.deform_zero` (`r_0 = id`), `Morse.BrokenSetup.deform_one_mem_brokenPaths`
  (`r_1` lands in `B`), `Morse.BrokenSetup.deform_of_mem_brokenPaths` (`r_u` fixes `B`),
  `Morse.BrokenSetup.energy_deform_le` (`E(r_u(γ)) ≤ E(γ)`).
* `Morse.BrokenSetup.continuousOn_deform`: **`(u, γ) ↦ r_u(γ)` is continuous on
  `[0, 1] × Int Ω^c`** for Milnor's metric, by gluing the segment-wise statements
  `Morse.BrokenSetup.tendsto_retrSeg` (the formulas of neighbouring segments agree,
  `Morse.BrokenSetup.retrSeg_eq_retr`).
* `Morse.BrokenSetup.theorem_16_2_deformationRetract`: **`B^a` is a strong deformation retract of
  `Ω^a`** (`a < c`).
* `Morse.BrokenSetup.homotopyEquivBroken`: hence the homotopy equivalence `Ω^a ≃ₕ B^a`, `B^a`
  as a subspace of `Ω`.

## What Milnor leaves implicit

* **Continuity in both variables** is the content of `Morse/Chapter10/RetractionConv.lean`; at the
  division points `u = tᵢ` the two formulas for `r_u` agree, so the segment-wise continuity glues.
* **Paths are functions on `[0, 1]`**: here a path is a function on `ℝ`, and `r_u(γ)` is
  completed by `γ` off `[0, 1]` so that `r_0(γ) = γ` and `r_u(β) = β` hold exactly.
-/

open Set Filter Topology Function Module Metric MeasureTheory
open scoped ContDiff Manifold RealInnerProductSpace ENNReal Interval NNReal

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

namespace PathSp

variable {p q : V}

omit [FiniteDimensional ℝ V] in
/-- A function agreeing on `[0, 1]` with a path of `Ω` is in `Ω`. -/
theorem pathSpace_congr {γ γ' : ℝ → V} (hγ : γ ∈ pathSpace N p q) (h : EqOn γ' γ (Icc 0 1)) :
    γ' ∈ pathSpace N p q := by
  obtain ⟨⟨h01, hcont, Bk, hBk⟩, hN', h0, h1⟩ := hγ
  refine ⟨⟨h01, hcont.congr h, Bk, fun s t hs hst ht hB => (hBk s t hs hst ht hB).congr
    fun τ hτ => h ⟨hs.trans hτ.1, hτ.2.trans ht⟩⟩, fun τ hτ => by rw [h hτ]; exact hN' τ hτ,
    ?_, ?_⟩
  · rw [h ⟨le_rfl, zero_le_one⟩, h0]
  · rw [h ⟨zero_le_one, le_rfl⟩, h1]

omit [FiniteDimensional ℝ V] in
/-- The uniform part of Milnor's metric only sees the values on `[0, 1]`. -/
theorem supDist_congr {α α' β β' : ℝ → V} (hα : EqOn α α' (Icc 0 1)) (hβ : EqOn β β' (Icc 0 1)) :
    supDist N α β = supDist N α' β' := by
  simp only [supDist]
  exact iSup_congr fun t => iSup_congr fun ht => by rw [hα ht, hβ ht]

omit [FiniteDimensional ℝ V] in
/-- The `L²` part of Milnor's metric only sees the values on `[0, 1]`. -/
theorem l2Dist_congr {α α' β β' : ℝ → V} (hα : EqOn α α' (Icc 0 1)) (hβ : EqOn β β' (Icc 0 1)) :
    l2Dist α β = l2Dist α' β' := by
  simp only [l2Dist]
  congr 1
  exact intervalIntegral.integral_congr_Ioo_of_le zero_le_one fun t ht => by
    simp only [speed_congr hα ht, speed_congr hβ ht]

omit [FiniteDimensional ℝ V] in
/-- A map into `Ω` at distance `0` from a continuous one is continuous. -/
theorem continuous_of_edist_eq_zero {X : Type*} [TopologicalSpace X]
    {Y : Type*} [PseudoEMetricSpace Y] {F G : X → Y} (hG : Continuous G)
    (h : ∀ x, edist (F x) (G x) = 0) : Continuous F := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  rw [ContinuousAt, tendsto_iff_edist_tendsto_0]
  have hG' := tendsto_iff_edist_tendsto_0.1 (hG.tendsto x)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hG' (fun _ => bot_le)
    fun y => ?_
  calc edist (F y) (F x) ≤ edist (F y) (G y) + edist (G y) (F x) := edist_triangle _ _ _
    _ ≤ edist (F y) (G y) + (edist (G y) (G x) + edist (G x) (F x)) :=
        add_le_add le_rfl (edist_triangle _ _ _)
    _ = edist (G y) (G x) := by rw [h y, edist_comm (G x), h x, zero_add, add_zero]

end PathSp

namespace BrokenSetup

variable {p q : V} {c : ℝ} {m : ℕ} (B : BrokenSetup hN p q c m)

open Classical in
/-- The function underlying `Morse.BrokenSetup.deform`. -/
def deformFun (u : ℝ) (γ : PathSp N p q) : ℝ → V :=
  if u ∈ Icc (0 : ℝ) 1 ∧ energy γ 0 1 < c then
    fun τ => if τ ∈ Icc (0 : ℝ) 1 then B.retr u γ τ else γ τ
  else γ

theorem deformFun_mem (u : ℝ) (γ : PathSp N p q) : B.deformFun u γ ∈ pathSpace N p q := by
  unfold deformFun
  split_ifs with h
  · exact PathSp.pathSpace_congr (B.retr_mem_pathSpace γ.mem h.2 h.1) fun _ hτ => if_pos hτ
  · exact γ.mem

/-- **Milnor's deformation `r_u` as a self-map of `Ω`** (p. 91): `r_u(γ)` on `[0, 1]` and `γ` off
`[0, 1]`, for `u ∈ [0, 1]` and `γ ∈ Int Ω^c`; `γ` itself otherwise. -/
def deform (u : ℝ) (γ : PathSp N p q) : PathSp N p q := ⟨B.deformFun u γ, B.deformFun_mem u γ⟩

/-- Unfolding `deform`. -/
theorem coe_deform {u : ℝ} {γ : PathSp N p q} (h : u ∈ Icc (0 : ℝ) 1 ∧ energy γ 0 1 < c) :
    (B.deform u γ : ℝ → V) = fun τ => if τ ∈ Icc (0 : ℝ) 1 then B.retr u γ τ else γ τ :=
  if_pos h

theorem deform_of_not {u : ℝ} {γ : PathSp N p q} (h : ¬(u ∈ Icc (0 : ℝ) 1 ∧ energy γ 0 1 < c)) :
    B.deform u γ = γ :=
  Subtype.ext (if_neg h)

section Deform

variable {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) {γ : PathSp N p q} (hE : energy γ 0 1 < c)
include hu hE

/-- On `[0, 1]`, `deform u γ` is `r_u(γ)`. -/
theorem eqOn_deform : EqOn (B.deform u γ) (B.retr u γ) (Icc 0 1) := fun τ hτ => by
  rw [B.coe_deform ⟨hu, hE⟩]
  exact if_pos hτ

/-- **Milnor's metric between two values of the deformation**. -/
theorem edist_deform {u' : ℝ} (hu' : u' ∈ Icc (0 : ℝ) 1) {γ' : PathSp N p q}
    (hE' : energy γ' 0 1 < c) :
    edist (B.deform u γ) (B.deform u' γ') = PathSp.supDist N (B.retr u γ) (B.retr u' γ') +
      ENNReal.ofReal (PathSp.l2Dist (B.retr u γ) (B.retr u' γ')) := by
  rw [PathSp.edist_def, PathSp.supDist_congr (B.eqOn_deform hu hE) (B.eqOn_deform hu' hE'),
    PathSp.l2Dist_congr (B.eqOn_deform hu hE) (B.eqOn_deform hu' hE')]

end Deform

/-- **`r_0` is the identity.** -/
theorem deform_zero (γ : PathSp N p q) : B.deform 0 γ = γ := by
  by_cases hE : energy γ 0 1 < c
  · refine Subtype.ext (funext fun τ => ?_)
    by_cases hτ : τ ∈ Icc (0 : ℝ) 1
    · exact (B.eqOn_deform ⟨le_rfl, zero_le_one⟩ hE hτ).trans (B.retr_zero γ.mem hE hτ)
    · rw [B.coe_deform ⟨⟨le_rfl, zero_le_one⟩, hE⟩]
      exact if_neg hτ
  · exact B.deform_of_not fun h => hE h.2

/-- **`r_u` fixes the broken geodesics** (`B = Int Ω(t₀, …, t_k)^c`). -/
theorem deform_of_mem_brokenPaths {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) {γ : PathSp N p q}
    (hγ : (γ : ℝ → V) ∈ B.brokenPaths) : B.deform u γ = γ := by
  refine Subtype.ext (funext fun τ => ?_)
  by_cases hτ : τ ∈ Icc (0 : ℝ) 1
  · exact (B.eqOn_deform hu hγ.2.2 hτ).trans (B.retr_of_mem_brokenPaths hγ hu hτ)
  · rw [B.coe_deform ⟨hu, hγ.2.2⟩]
    exact if_neg hτ

/-- **`E(r_u(γ)) ≤ E(γ)`.** -/
theorem energy_deform_le (u : ℝ) (γ : PathSp N p q) :
    energy (B.deform u γ) 0 1 ≤ energy γ 0 1 := by
  by_cases h : u ∈ Icc (0 : ℝ) 1 ∧ energy γ 0 1 < c
  · rw [energy_congr (B.eqOn_deform h.1 h.2)]
    exact B.energy_retr_le γ.mem h.2 h.1
  · rw [B.deform_of_not h]

/-- **`r_1` retracts `Int Ω^c` onto `B`**: `r_1(γ)` is a broken geodesic (on `[0, 1]`, the
broken geodesic of the break points of `γ`). -/
theorem deform_one_mem_brokenPaths {γ : PathSp N p q} (hE : energy γ 0 1 < c) :
    (B.deform 1 γ : ℝ → V) ∈ B.brokenPaths := by
  have hy := B.nodeVal_mem γ.mem hE
  have heq : EqOn (B.deform 1 γ) (B.path (B.nodeVal γ)) (Icc 0 1) := fun τ hτ =>
    (B.eqOn_deform ⟨zero_le_one, le_rfl⟩ hE hτ).trans (B.retr_one γ.mem hE hτ)
  obtain ⟨-, hbr, hEp⟩ := ((B.lemma_16_1).1 _ hy).1
  refine ⟨(B.deform 1 γ).mem, fun k => (hbr k).congr fun τ hτ =>
    (heq ⟨(B.t_nonneg _).trans hτ.1.le, hτ.2.le.trans (B.t_le_one _)⟩).symm, ?_⟩
  rw [energy_congr heq]
  exact hEp

/-- **Continuity of Milnor's deformation in both variables** (p. 91, "easily verified"):
`(u, γ) ↦ r_u(γ)` is continuous on `[0, 1] × Int Ω^c` for Milnor's metric `d`. -/
theorem continuousOn_deform :
    ContinuousOn (fun z : ℝ × PathSp N p q => B.deform z.1 z.2)
      (Icc (0 : ℝ) 1 ×ˢ {γ : PathSp N p q | energy γ 0 1 < c}) := by
  rintro ⟨u₀, γ₀⟩ ⟨hu₀, hE₀⟩
  set D := Icc (0 : ℝ) 1 ×ˢ {γ : PathSp N p q | energy γ 0 1 < c} with hD_def
  rw [ContinuousWithinAt, tendsto_iff_edist_tendsto_0, ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hD : ∀ᶠ z in 𝓝[D] (u₀, γ₀), z ∈ D := self_mem_nhdsWithin
  have hfst : Tendsto (fun z : ℝ × PathSp N p q => z.1) (𝓝[D] (u₀, γ₀)) (𝓝 u₀) :=
    (continuous_fst.tendsto _).mono_left nhdsWithin_le_nhds
  have hsnd : Tendsto (fun z : ℝ × PathSp N p q => z.2) (𝓝[D] (u₀, γ₀)) (𝓝 γ₀) :=
    (continuous_snd.tendsto _).mono_left nhdsWithin_le_nhds
  -- segment by segment
  have hseg : ∀ k : Fin (m + 1), ∀ᶠ z in 𝓝[D] (u₀, γ₀),
      z.1 ∈ Icc (B.t k.castSucc) (B.t k.succ) →
        edist (B.deform z.1 z.2) (B.deform u₀ γ₀) ≤ ε := by
    intro k
    by_cases hk : u₀ ∈ Icc (B.t k.castSucc) (B.t k.succ)
    · set l' := 𝓝[D] (u₀, γ₀) ⊓ 𝓟 {z : ℝ × PathSp N p q | z.1 ∈ Icc (B.t k.castSucc) (B.t k.succ)}
      have hl'D : ∀ᶠ z in l', z ∈ D := hD.filter_mono inf_le_left
      have hl'k : ∀ᶠ z in l', z.1 ∈ Icc (B.t k.castSucc) (B.t k.succ) :=
        mem_inf_of_right (mem_principal_self _)
      have h := B.tendsto_retrSeg (l := l') (i := k) (us := fun z => z.1) (γs := fun z => z.2)
        (hfst.mono_left inf_le_left) (hsnd.mono_left inf_le_left) hl'k hk
        (hl'D.mono fun z hz => hz.2) hE₀
      have h' : ∀ᶠ z in l', edist (B.deform z.1 z.2) (B.deform u₀ γ₀) ≤ ε := by
        filter_upwards [(ENNReal.tendsto_nhds_zero.1 h) ε hε, hl'D, hl'k] with z hz hzD hzk
        rw [B.edist_deform hzD.1 hzD.2 hu₀ hE₀, ← B.retrSeg_eq_retr z.2.mem hzD.2 hzk,
          ← B.retrSeg_eq_retr γ₀.mem hE₀ hk]
        exact hz
      filter_upwards [eventually_inf_principal.1 h'] with z hz hzk using hz hzk
    · have : ∀ᶠ z in 𝓝[D] (u₀, γ₀), z.1 ∉ Icc (B.t k.castSucc) (B.t k.succ) :=
        hfst.eventually (isClosed_Icc.isOpen_compl.mem_nhds hk)
      filter_upwards [this] with z hz hz' using absurd hz' hz
  filter_upwards [Filter.eventually_all.2 hseg, hD] with z hz hzD
  exact hz _ (B.mem_Icc_segOf hzD.1)

/-- **Theorem 16.2, second assertion** (Milnor p. 91): **for `a < c`, `B^a` is a (strong)
deformation retract of `Ω^a`**.  Milnor's deformation `(u, γ) ↦ r_u(γ)` is continuous on
`[0, 1] × Ω^a` for Milnor's metric, does not increase the energy (so it maps `Ω^a` to itself),
starts at the identity, ends in `B^a = Ω^a ∩ Int Ω(t₀, …, t_k)^c`, and fixes `B^a` throughout. -/
theorem theorem_16_2_deformationRetract {a : ℝ} (ha : a < c) :
    ContinuousOn (fun z : ℝ × PathSp N p q => B.deform z.1 z.2)
        (Icc (0 : ℝ) 1 ×ˢ {γ : PathSp N p q | energy γ 0 1 ≤ a}) ∧
      (∀ u γ, energy (B.deform u γ) 0 1 ≤ energy γ 0 1) ∧
      (∀ γ, B.deform 0 γ = γ) ∧
      (∀ γ : PathSp N p q, energy γ 0 1 ≤ a → (B.deform 1 γ : ℝ → V) ∈ B.brokenPaths) ∧
      (∀ u ∈ Icc (0 : ℝ) 1, ∀ γ : PathSp N p q, (γ : ℝ → V) ∈ B.brokenPaths →
        B.deform u γ = γ) :=
  ⟨B.continuousOn_deform.mono (prod_mono subset_rfl fun _ hγ => lt_of_le_of_lt hγ ha),
    B.energy_deform_le, B.deform_zero, fun _ hγ => B.deform_one_mem_brokenPaths (hγ.trans_lt ha),
    fun _ hu _ hγ => B.deform_of_mem_brokenPaths hu hγ⟩

/-- `(t, γ) ↦ r_{1−t}(γ)` on `[0, 1] × Ω^a`, `a < c`, as a map to `Ω^a`. -/
theorem continuous_deform_sublevel {a : ℝ} (ha : a < c) :
    Continuous fun x : unitInterval × {γ : PathSp N p q // energy γ 0 1 ≤ a} =>
      (⟨B.deform (1 - (x.1 : ℝ)) x.2.1, (B.energy_deform_le _ _).trans x.2.2⟩ :
        {γ : PathSp N p q // energy γ 0 1 ≤ a}) := by
  refine Continuous.subtype_mk ?_ _
  have hc := B.continuousOn_deform.comp_continuous
    (f := fun x : unitInterval × {γ : PathSp N p q // energy γ 0 1 ≤ a} =>
      ((1 - (x.1 : ℝ)), x.2.1)) (by fun_prop) fun x =>
      ⟨⟨by linarith [x.1.2.2], by linarith [x.1.2.1]⟩, lt_of_le_of_lt x.2.2 ha⟩
  exact hc

/-- **Milnor's retraction `r = r_1 : Ω^a → B^a`** (`a < c`). -/
def retrMap {a : ℝ} (ha : a < c) :
    C({γ : PathSp N p q // energy γ 0 1 ≤ a},
      {γ : PathSp N p q // energy γ 0 1 ≤ a ∧ (γ : ℝ → V) ∈ B.brokenPaths}) where
  toFun γ := ⟨B.deform 1 γ.1, (B.energy_deform_le _ _).trans γ.2,
    B.deform_one_mem_brokenPaths (lt_of_le_of_lt γ.2 ha)⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact B.continuousOn_deform.comp_continuous
      (f := fun γ : {γ : PathSp N p q // energy γ 0 1 ≤ a} => ((1 : ℝ), γ.1)) (by fun_prop)
      fun γ => ⟨⟨zero_le_one, le_rfl⟩, lt_of_le_of_lt γ.2 ha⟩

/-- The inclusion `B^a → Ω^a`. -/
def inclMap (a : ℝ) :
    C({γ : PathSp N p q // energy γ 0 1 ≤ a ∧ (γ : ℝ → V) ∈ B.brokenPaths},
      {γ : PathSp N p q // energy γ 0 1 ≤ a}) where
  toFun γ := ⟨γ.1, γ.2.1⟩

/-- **`Ω^a` has the homotopy type of `B^a`** (`a < c`, Milnor p. 91): Milnor's retraction `r_1`
and the inclusion are inverse homotopy equivalences, `B^a = Ω^a ∩ Int Ω(t₀, …, t_k)^c` as a
subspace of `Ω`; the homotopy from the identity of `Ω^a` is `(t, γ) ↦ r_{1−t}(γ)`. -/
def homotopyEquivBroken {a : ℝ} (ha : a < c) :
    ContinuousMap.HomotopyEquiv {γ : PathSp N p q // energy γ 0 1 ≤ a}
      {γ : PathSp N p q // energy γ 0 1 ≤ a ∧ (γ : ℝ → V) ∈ B.brokenPaths} where
  toFun := B.retrMap ha
  invFun := B.inclMap a
  left_inv := ⟨{
    toFun := fun x => ⟨B.deform (1 - (x.1 : ℝ)) x.2.1, (B.energy_deform_le _ _).trans x.2.2⟩
    continuous_toFun := B.continuous_deform_sublevel ha
    map_zero_left := fun γ => by simp [retrMap, inclMap]
    map_one_left := fun γ => by
      apply Subtype.ext
      simp [B.deform_zero] }⟩
  right_inv := by
    have : (B.retrMap ha).comp (B.inclMap a) = ContinuousMap.id _ := by
      ext γ
      exact B.deform_of_mem_brokenPaths ⟨zero_le_one, le_rfl⟩ γ.2.2
    rw [this]

end BrokenSetup

end Morse
