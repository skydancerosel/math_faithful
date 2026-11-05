import Morse.Chapter10.PathMetric

/-!
Milnor, *Morse Theory*, §16, p. 91: the retraction of `Int Ω^c` onto the broken geodesics, for a
submanifold `N ⊆ ℝᴷ` with the induced metric.

# Milnor's deformation `r_u`

## Milnor's text, paraphrased

(p. 91) A retraction `r : Int Ω^c → B` is defined by letting `r(ω)` be the broken geodesic in `B`
which on each `[t_{i−1}, t_i]` is the geodesic of length `< ε` from `ω(t_{i−1})` to `ω(t_i)`
(it exists since `ρ(ω(t_{i−1}), ω(t_i))² ≤ (t_i − t_{i−1}) E < ε²`); clearly `E(r(ω)) ≤ E(ω) < c`.
It fits into a family `r_u : Int Ω^c → Int Ω^c`: for `t_{i−1} ≤ u ≤ t_i`, `r_u(ω)` is `r(ω)` on
`[0, t_{i−1}]`, the minimal geodesic from `ω(t_{i−1})` to `ω(u)` on `[t_{i−1}, u]`, and `ω` on
`[u, 1]`.  Then `r_0` is the identity and `r_1 = r`.  "It is easily verified" that `r_u(ω)` is
continuous in both variables, so `B` is a deformation retract of `Int Ω^c`; since
`E(r_u(ω)) ≤ E(ω)`, each `B^a` is a deformation retract of `Ω^a`.

## In the embedded setting

For `B : Morse.BrokenSetup hN p q c m` (segments `[tᵢ, t_{i+1}]`, `i : Fin (m + 1)`):

* `Morse.BrokenSetup.sgeoOver x y a b`: the short geodesic from `x` to `y` run over `[a, b]`
  (`Morse.BrokenSetup.sgeoOver_isGeodesicOn`, energy `ρ(x, y)²/(b − a)`:
  `Morse.BrokenSetup.energy_sgeoOver`).
* `Morse.BrokenSetup.retrSeg i u γ` (for `u ∈ [tᵢ, t_{i+1}]`) and
  `Morse.BrokenSetup.retr u γ = retrSeg (segOf u) u γ`: **Milnor's `r_u(γ)`**; its three pieces
  are described by `Morse.BrokenSetup.retrSeg_eqOn_left`, `Morse.BrokenSetup.retrSeg_eqOn_mid`,
  `Morse.BrokenSetup.retrSeg_eqOn_right`.
* For `γ ∈ Ω` with `E(γ) < c`: `Morse.BrokenSetup.retr_mem_pathSpace` (`r_u(γ) ∈ Ω`),
  `Morse.BrokenSetup.energy_retr_le` (**`E(r_u(γ)) ≤ E(γ)`**, and on `[tᵢ, u]`:
  `Morse.BrokenSetup.energy_retrSeg_mid_le`), `Morse.BrokenSetup.retr_zero` (`r_0(γ) = γ`),
  `Morse.BrokenSetup.retr_one` (`r_1(γ)` is the broken geodesic of the break points of `γ`),
  `Morse.BrokenSetup.retr_of_mem_brokenPaths` (**`r_u` fixes the broken geodesics**), all as
  paths on `[0, 1]`.
* `Morse.BrokenSetup.retrSeg_eq_retr`: on the closed segment `u ∈ [tᵢ, t_{i+1}]` the formula with
  index `i` gives `r_u`, also at `u = t_{i+1}` where `segOf u` jumps (the two formulas agree,
  `Morse.BrokenSetup.path_nodeVal_eq_sgeoOver`).

The continuity of `(u, γ) ↦ r_u(γ)` is proved in `Morse/Chapter10/RetractionConv.lean` and
`Morse/Chapter10/Deformation.lean`.

## What Milnor leaves implicit

* **`r_u` fixes `B`**: on `[t_{i−1}, u]` a broken geodesic is a sub-arc of the short geodesic of
  its segment, which is the short geodesic between its own ends (uniqueness in Corollary 10.8).
* **`E(r_u(ω)) ≤ E(ω)`** segment by segment: each replaced piece is a short geodesic with the same
  ends over the same time interval, whose energy `ρ²/(length)` is at most the energy of `ω` there
  (Schwarz's inequality).
* **The formulas for neighbouring intervals agree at `u = tᵢ`** (needed for `r_u` to be
  well defined and continuous in `u`).
-/

open Set Filter Topology Function Module Metric MeasureTheory
open scoped ContDiff Manifold RealInnerProductSpace ENNReal Interval

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

/-! ### Two lemmas on the energy -/

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The energy on `[a, b]` only depends on the path on `[a, b]`. -/
theorem energy_congr_Icc [InnerProductSpace ℝ V] {c c' : ℝ → V} {a b : ℝ} (hab : a ≤ b)
    (h : EqOn c c' (Icc a b)) : energy c a b = energy c' a b := by
  refine intervalIntegral.integral_congr_Ioo_of_le hab fun t ht => ?_
  have hev : c =ᶠ[𝓝 t] c' := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
    exact h (Ioo_subset_Icc_self hx)
  simp only [hev.deriv_eq]

omit [FiniteDimensional ℝ V] in
/-- **Schwarz's inequality with the distance**: `ρ(c(a), c(b))² ≤ (b − a) E_a^b(c)`. -/
theorem riemDist_sq_le_energy {c : ℝ → V} {a b : ℝ} (hc : IsPiecewiseSmooth c a b)
    (hcN : ∀ t ∈ Icc a b, c t ∈ N) :
    (riemDist (N := N) (c a) (c b)).toReal ^ 2 ≤ (b - a) * energy c a b := by
  have hρ := riemDist_le_pathLength (N := N) hc hcN
  have hL0 := hc.isAdmissible.pathLength_nonneg
  have hρL := ENNReal.toReal_le_of_le_ofReal hL0 hρ
  calc (riemDist (N := N) (c a) (c b)).toReal ^ 2 ≤ pathLength c a b ^ 2 := by gcongr
    _ ≤ (b - a) * energy c a b := pathLength_sq_le_energy hc

namespace BrokenSetup

variable {p q : V} {c : ℝ} {m : ℕ} (B : BrokenSetup hN p q c m)

/-! ### The short geodesic between two points, over a given time interval -/

/-- **The short geodesic from `x` to `y`, run over `[a, b]`** at constant speed. -/
def sgeoOver (x y : V) (a b τ : ℝ) : V := exp hN x (((τ - a) / (b - a)) • B.joinVec x y)

theorem sgeoOver_left {x y : V} (hx : x ∈ N) (a b : ℝ) : B.sgeoOver x y a b a = x := by
  rw [sgeoOver, sub_self, zero_div, zero_smul, exp_zero hx]

section Sgeo

variable {x y : V} (hx : x ∈ closedRiemBall N p √c) (hy : y ∈ closedRiemBall N p √c)
  (hxy : riemDist (N := N) x y < ENNReal.ofReal B.δ)
include hx hy hxy

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem sgeoOver_right {a b : ℝ} (hab : a < b) : B.sgeoOver x y a b b = y := by
  rw [sgeoOver, div_self (sub_pos.2 hab).ne', one_smul]
  exact (B.joinVec_spec hx hy hxy).2.2.1

/-- **The short geodesic over `[a, b]` is a geodesic** on an open interval containing `[a, b]`,
of speed `ρ(x, y)/(b − a)`. -/
theorem sgeoOver_isGeodesicOn {a b : ℝ} (hab : a < b) :
    ∃ η > 0, IsGeodesicOn hN (B.sgeoOver x y a b) (Ioo (a - η) (b + η)) ∧
      ∀ τ ∈ Ioo (a - η) (b + η), ‖deriv (B.sgeoOver x y a b) τ‖ = ‖B.joinVec x y‖ / (b - a) := by
  set v := B.joinVec x y
  have hxN : x ∈ N := hx.1
  have hvT : prj hN x v = v := (B.joinVec_spec hx hy hxy).1
  obtain ⟨γ, hγ⟩ := B.mem_expDom_joinVec hx hy hxy
  obtain ⟨δ', hδ', hgeo, -⟩ := hγ.isGeodesicOn_exp_smul
  have hl : 0 < b - a := sub_pos.2 hab
  set k := 1 / (b - a)
  set l := -(a / (b - a))
  have haff : ∀ τ, k * τ + l = (τ - a) / (b - a) := fun τ => by
    simp only [k, l]; field_simp; ring
  have h := hgeo.comp_mul_add k l
  have hEq : EqOn (fun τ => exp hN x ((k * τ + l) • v)) (B.sgeoOver x y a b) univ := fun τ _ => by
    simp only [sgeoOver, haff]; rfl
  have hgeo' : IsGeodesicOn hN (B.sgeoOver x y a b) (Ioo (a - δ' * (b - a)) (b + δ' * (b - a))) :=
    (h.mono isOpen_Ioo fun τ hτ => by
      simp only [mem_preimage, mem_Ioo, haff]
      constructor
      · rw [lt_div_iff₀ hl]; nlinarith [hτ.1]
      · rw [div_lt_iff₀ hl]; nlinarith [hτ.2]).congr (hEq.mono (subset_univ _))
  refine ⟨δ' * (b - a), by positivity, hgeo', fun τ hτ => ?_⟩
  have ha : a ∈ Ioo (a - δ' * (b - a)) (b + δ' * (b - a)) :=
    ⟨by nlinarith, by nlinarith⟩
  have hd0 : HasDerivAt (fun s => exp hN x (s • v)) v (k * a + l) := by
    rw [haff, sub_self, zero_div]
    exact hasDerivAt_exp_smul_zero ⟨x, hxN⟩ ((prj_eq_self_iff hN hxN).1 hvT)
  have haffd : HasDerivAt (fun τ : ℝ => k * τ + l) k a := by
    simpa using ((hasDerivAt_id a).const_mul k).add_const l
  have hcomp := hd0.scomp a haffd
  have hda : HasDerivAt (B.sgeoOver x y a b) (k • v) a :=
    hcomp.congr_of_eventuallyEq (Eventually.of_forall fun τ => (hEq (mem_univ τ)).symm)
  rw [hgeo'.norm_deriv_eq isPreconnected_Ioo hτ ha, hda.deriv, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  simp only [k]
  ring

/-- **The energy of the short geodesic over `[a, b]`** is `ρ(x, y)²/(b − a)`. -/
theorem energy_sgeoOver {a b : ℝ} (hab : a < b) :
    energy (B.sgeoOver x y a b) a b = (riemDist (N := N) x y).toReal ^ 2 / (b - a) := by
  obtain ⟨η, hη, hgeo, hspeed⟩ := B.sgeoOver_isGeodesicOn hx hy hxy hab
  have hadm : IsAdmissible (B.sgeoOver x y a b) a b :=
    (IsPiecewiseSmooth.of_contDiffOn hgeo.contDiffOn hab.le fun τ hτ =>
      ⟨by linarith [hτ.1], by linarith [hτ.2]⟩).isAdmissible
  rw [energy_eq_of_norm_deriv hadm (k := ‖B.joinVec x y‖ / (b - a)) fun τ hτ _ =>
    hspeed τ ⟨by linarith [hτ.1], by linarith [hτ.2]⟩, (B.joinVec_spec hx hy hxy).2.2.2.1,
    ENNReal.toReal_ofReal (norm_nonneg _)]
  have hl : (b - a) ≠ 0 := (sub_pos.2 hab).ne'
  field_simp

end Sgeo

/-! ### The deformation `r_u` -/

/-- **Milnor's `r_u(γ)` for `u` in the `i`-th segment** `[tᵢ, t_{i+1}]` (p. 91): the broken
geodesic of the break points of `γ` on `[0, tᵢ]`, the short geodesic from `γ(tᵢ)` to `γ(u)` on
`[tᵢ, u]`, and `γ` on `[u, 1]`. -/
def retrSeg (i : Fin (m + 1)) (u : ℝ) (γ : ℝ → V) (τ : ℝ) : V :=
  if τ ≤ B.t i.castSucc then B.path (B.nodeVal γ) τ
  else if τ ≤ u then B.sgeoOver (γ (B.t i.castSucc)) (γ u) (B.t i.castSucc) u τ else γ τ

/-- **Milnor's deformation** `r_u(γ)` (p. 91). -/
def retr (u : ℝ) (γ : ℝ → V) : ℝ → V := B.retrSeg (B.segOf u) u γ

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **`r_u(γ)` on `[0, tᵢ]`** is the broken geodesic of the break points of `γ`. -/
theorem retrSeg_eqOn_left (i : Fin (m + 1)) (u : ℝ) (γ : ℝ → V) :
    EqOn (B.retrSeg i u γ) (B.path (B.nodeVal γ)) (Iic (B.t i.castSucc)) := fun τ hτ => by
  rw [retrSeg, if_pos (mem_Iic.1 hτ)]

/-! ### Facts about broken geodesics used below -/

/-- The broken geodesic passes through its vertices. -/
theorem path_t {y : Fin m → V} (hy : y ∈ B.nodes) (k : Fin (m + 2)) :
    B.path y (B.t k) = vert p q y k := by
  have h := B.vert_nodeVal (B.path_mem_pathSpace hy) k
  rw [B.nodeVal_path hy] at h
  exact h.symm

/-- The energy of the `k`-th segment of the broken geodesic is `ρ(x_k, x_{k+1})²/(t_{k+1} − t_k)`
(the summand of formula (∗)). -/
theorem energy_path_seg {y : Fin m → V} (hy : y ∈ B.nodes) (k : Fin (m + 1)) :
    energy (B.path y) (B.t k.castSucc) (B.t k.succ) =
      (riemDist (N := N) (vert p q y k.castSucc) (vert p q y k.succ)).toReal ^ 2 / B.len k := by
  have hps := (B.path_mem_pathSpace hy).1
  have hadm : IsAdmissible (B.path y) (B.t k.castSucc) (B.t k.succ) :=
    (hps.mono (B.t_nonneg _) (B.t_le_iff.2 Fin.castSucc_lt_succ.le) (B.t_le_one _)).isAdmissible
  have h := energy_eq_of_norm_deriv hadm (k := ‖B.joinVec (vert p q y k.castSucc)
    (vert p q y k.succ)‖ / B.len k) fun τ hτ _ => B.norm_deriv_path hy k hτ
  rw [h, (B.joinVec_vert hy k).2.2.2, ENNReal.toReal_ofReal (norm_nonneg _)]
  have hl := (B.len_pos k).ne'
  change _ * B.len k = _
  field_simp

/-! ### Properties of `r_u` -/

section Retr

variable {γ : ℝ → V} (hγ : γ ∈ pathSpace N p q) (hE : energy γ 0 1 < c)
include hγ hE

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- Points of `γ` within one segment are at distance `< δ`. -/
theorem riemDist_lt_of_seg (i : Fin (m + 1)) {a b : ℝ} (ha : B.t i.castSucc ≤ a) (hab : a ≤ b)
    (hb : b ≤ B.t i.succ) : riemDist (N := N) (γ a) (γ b) < ENNReal.ofReal B.δ := by
  have h0 : 0 ≤ a := (B.t_nonneg _).trans ha
  have h1 : b ≤ 1 := hb.trans (B.t_le_one _)
  have hps := hγ.1.mono h0 hab h1
  have hN' : ∀ τ ∈ Icc a b, γ τ ∈ N := fun τ hτ => hγ.2.1 τ ⟨h0.trans hτ.1, hτ.2.trans h1⟩
  have hρ := riemDist_le_pathLength (N := N) hps hN'
  have hfin : riemDist (N := N) (γ a) (γ b) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hρ
  have hsq := riemDist_sq_le_energy hps hN'
  have hEab : energy γ a b ≤ energy γ 0 1 :=
    intervalIntegral.integral_mono_interval h0 hab h1 (Eventually.of_forall fun _ => sq_nonneg _)
      hγ.1.intervalIntegrable_norm_deriv_sq
  have hE0 : 0 ≤ energy γ a b := PathSp.energy_nonneg_of_le hab
  have hlen : b - a ≤ B.len i := by simp only [Subdivision.len]; linarith
  have hfine := B.fine i
  have hc := B.c_pos
  have h2 : (riemDist (N := N) (γ a) (γ b)).toReal ^ 2 < B.δ ^ 2 := by
    calc _ ≤ (b - a) * energy γ a b := hsq
      _ ≤ B.len i * c := by
          apply mul_le_mul hlen (hEab.trans hE.le) hE0 (B.len_pos i).le
      _ < B.δ ^ 2 := by linarith
  rw [← ENNReal.ofReal_toReal hfin]
  exact (ENNReal.ofReal_lt_ofReal_iff B.δ_pos).2 (lt_of_pow_lt_pow_left₀ 2 B.δ_pos.le h2)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem nodeVal_mem : B.nodeVal γ ∈ B.nodes := (B.nodeVal_mem_nodes_of_energy_lt hγ hE).1

/-- The broken geodesic of the break points of `γ` passes through the points `γ(t_k)`. -/
theorem path_nodeVal_t (k : Fin (m + 2)) : B.path (B.nodeVal γ) (B.t k) = γ (B.t k) := by
  rw [B.path_t (B.nodeVal_mem hγ hE), B.vert_nodeVal hγ]

variable {i : Fin (m + 1)} {u : ℝ} (hu : u ∈ Icc (B.t i.castSucc) (B.t i.succ))
include hu

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] hγ hE in
theorem u_mem : u ∈ Icc (0 : ℝ) 1 := ⟨(B.t_nonneg _).trans hu.1, hu.2.trans (B.t_le_one _)⟩

/-- **`r_u(γ)` is a path from `p` to `q`.** -/
theorem retrSeg_mem_pathSpace : B.retrSeg i u γ ∈ pathSpace N p q := by
  have hy := B.nodeVal_mem hγ hE
  have hu01 := B.u_mem hu
  set a := B.t i.castSucc
  have ha0 : 0 ≤ a := B.t_nonneg _
  have ha1 : a < 1 := by
    rw [← B.t_last]; exact B.t_lt_iff.2 (Fin.castSucc_lt_last _)
  have hxa := mem_closedRiemBall_of_energy_le hγ hE.le ⟨ha0, ha1.le⟩
  have hxu := mem_closedRiemBall_of_energy_le hγ hE.le hu01
  have hρ := B.riemDist_lt_of_seg hγ hE i le_rfl hu.1 hu.2
  -- the middle piece
  have hS : IsPiecewiseSmooth (B.sgeoOver (γ a) (γ u) a u) a u ∧
      (∀ τ ∈ Icc a u, B.sgeoOver (γ a) (γ u) a u τ ∈ N) ∧
      B.sgeoOver (γ a) (γ u) a u a = γ a ∧ B.sgeoOver (γ a) (γ u) a u u = γ u := by
    rcases eq_or_lt_of_le hu.1 with h | h
    · have hl := B.sgeoOver_left (y := γ a) hxa.1 a a
      rw [← h]
      refine ⟨⟨le_rfl, by rw [Icc_self]; exact continuousOn_singleton _ _, ∅,
        fun s t hs hst ht _ => absurd (hs.trans_lt hst) (not_lt.2 ht)⟩, fun τ hτ => ?_, hl, hl⟩
      rw [le_antisymm hτ.2 hτ.1, hl]
      exact hxa.1
    · obtain ⟨η, hη, hgeo, -⟩ := B.sgeoOver_isGeodesicOn hxa hxu hρ h
      have hsub : Icc a u ⊆ Ioo (a - η) (u + η) := fun τ hτ =>
        ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      exact ⟨IsPiecewiseSmooth.of_contDiffOn hgeo.contDiffOn h.le hsub,
        fun τ hτ => hgeo.mem τ (hsub hτ), B.sgeoOver_left hxa.1 a u,
        B.sgeoOver_right hxa hxu hρ h⟩
  obtain ⟨hSps, hSN, hSa, hSu⟩ := hS
  have hP := (B.path_mem_pathSpace hy).1.mono le_rfl ha0 ha1.le
  have hγu := hγ.1.mono hu01.1 hu01.2 le_rfl
  have hPa : B.path (B.nodeVal γ) a = γ a := B.path_nodeVal_t hγ hE _
  have h2 : IsPiecewiseSmooth (fun τ => if τ ≤ u then B.sgeoOver (γ a) (γ u) a u τ else γ τ)
      a 1 := hSps.concat hγu hSu
  have h3 : B.path (B.nodeVal γ) a =
      (fun τ => if τ ≤ u then B.sgeoOver (γ a) (γ u) a u τ else γ τ) a := by
    simp only [if_pos hu.1, hSa, hPa]
  refine ⟨hP.concat h2 h3, fun τ hτ => ?_, ?_, ?_⟩
  · simp only [retrSeg]
    split_ifs with h1 h2'
    · exact B.path_mem hy τ hτ
    · exact hSN τ ⟨(not_le.1 h1).le, h2'⟩
    · exact hγ.2.1 τ hτ
  · show B.retrSeg i u γ 0 = p
    rw [retrSeg, if_pos (B.t_nonneg _), ← B.t_zero, B.path_nodeVal_t hγ hE, B.t_zero, hγ.2.2.1]
  · show B.retrSeg i u γ 1 = q
    have h1 : ¬(1 : ℝ) ≤ B.t i.castSucc := not_le.2 ha1
    rw [retrSeg, if_neg h1]
    split_ifs with h2'
    · obtain rfl : u = 1 := le_antisymm hu01.2 h2'
      exact hSu.trans hγ.2.2.2
    · exact hγ.2.2.2

omit hu in
/-- **`r_u(γ)` on `[tᵢ, u]`** is the short geodesic from `γ(tᵢ)` to `γ(u)`. -/
theorem retrSeg_eqOn_mid :
    EqOn (B.retrSeg i u γ) (B.sgeoOver (γ (B.t i.castSucc)) (γ u) (B.t i.castSucc) u)
      (Icc (B.t i.castSucc) u) := by
  intro τ hτ
  simp only [retrSeg]
  rcases eq_or_lt_of_le hτ.1 with h | h
  · rw [if_pos h.symm.le, ← h, B.path_nodeVal_t hγ hE,
      B.sgeoOver_left (hγ.2.1 _ ⟨B.t_nonneg _, B.t_le_one _⟩)]
  · rw [if_neg (not_le.2 h), if_pos hτ.2]

/-- **`r_u(γ)` on `[u, ∞)`** is `γ`. -/
theorem retrSeg_eqOn_right : EqOn (B.retrSeg i u γ) γ (Ici u) := by
  intro τ hτ
  have hτ' : u ≤ τ := hτ
  simp only [retrSeg]
  rcases eq_or_lt_of_le hu.1 with h | h
  · rcases eq_or_lt_of_le hτ' with h' | h'
    · rw [if_pos (h.trans h').ge, ← h', ← h, B.path_nodeVal_t hγ hE]
    · rw [if_neg (not_le.2 (h ▸ h')), if_neg (not_le.2 h')]
  · rw [if_neg (not_le.2 (h.trans_le hτ'))]
    rcases eq_or_lt_of_le hτ' with h' | h'
    · rw [if_pos h'.ge, ← h', B.sgeoOver_right (mem_closedRiemBall_of_energy_le hγ hE.le
        ⟨B.t_nonneg _, B.t_le_one _⟩) (mem_closedRiemBall_of_energy_le hγ hE.le (B.u_mem hu))
        (B.riemDist_lt_of_seg hγ hE i le_rfl hu.1 hu.2) h]
    · rw [if_neg (not_le.2 h')]

/-- **The energy of `r_u(γ)` on `[tᵢ, u]`** is at most that of `γ` (Schwarz's inequality). -/
theorem energy_retrSeg_mid_le :
    energy (B.retrSeg i u γ) (B.t i.castSucc) u ≤ energy γ (B.t i.castSucc) u := by
  have hu01 := B.u_mem hu
  have ha01 : B.t i.castSucc ∈ Icc (0 : ℝ) 1 := ⟨B.t_nonneg _, B.t_le_one _⟩
  rw [energy_congr_Icc hu.1 (B.retrSeg_eqOn_mid hγ hE)]
  rcases eq_or_lt_of_le hu.1 with h | h
  · rw [← h]; simp [energy]
  · rw [B.energy_sgeoOver (mem_closedRiemBall_of_energy_le hγ hE.le ha01)
      (mem_closedRiemBall_of_energy_le hγ hE.le hu01)
      (B.riemDist_lt_of_seg hγ hE i le_rfl hu.1 hu.2) h, div_le_iff₀ (sub_pos.2 h), mul_comm]
    exact riemDist_sq_le_energy (hγ.1.mono ha01.1 hu.1 hu01.2) fun τ hτ =>
      hγ.2.1 τ ⟨ha01.1.trans hτ.1, hτ.2.trans hu01.2⟩

/-- **`E(r_u(γ)) ≤ E(γ)`** (Milnor p. 91): segment by segment, a replaced piece is a short geodesic
with the same ends over the same time interval. -/
theorem energy_retrSeg_le : energy (B.retrSeg i u γ) 0 1 ≤ energy γ 0 1 := by
  have hy := B.nodeVal_mem hγ hE
  have hu01 := B.u_mem hu
  have hr := B.retrSeg_mem_pathSpace hγ hE hu
  have hmem : ∀ k, B.t k ∈ uIcc (0 : ℝ) 1 := fun k => by
    rw [uIcc_of_le zero_le_one]; exact ⟨B.t_nonneg k, B.t_le_one k⟩
  have hsum : ∀ {g : ℝ → V}, g ∈ pathSpace N p q →
      energy g 0 1 = ∑ k : Fin (m + 1), energy g (B.t k.castSucc) (B.t k.succ) := by
    intro g hg
    have := sum_integral_fin B.t fun k l => hg.1.intervalIntegrable_norm_deriv_sq.mono_set
      (uIcc_subset_uIcc (hmem k) (hmem l))
    rw [B.t_zero, B.t_last] at this
    rw [energy, ← this]
    rfl
  rw [hsum hr, hsum hγ]
  refine Finset.sum_le_sum fun k _ => ?_
  have hk0 := B.t_nonneg k.castSucc
  have hkl := B.t_le_iff.2 (Fin.castSucc_lt_succ (i := k)).le
  have hk1 := B.t_le_one k.succ
  rcases lt_trichotomy k i with hki | rfl | hki
  · -- before `tᵢ`: the broken geodesic of the break points
    have hki' : B.t k.succ ≤ B.t i.castSucc := B.t_le_iff.2 (by
      rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; exact hki)
    rw [energy_congr_Icc hkl ((B.retrSeg_eqOn_left i u γ).mono fun τ hτ =>
        (show τ ≤ B.t i.castSucc from hτ.2.trans hki')), B.energy_path_seg hy k,
      B.vert_nodeVal hγ, B.vert_nodeVal hγ, div_le_iff₀ (B.len_pos k), mul_comm]
    exact riemDist_sq_le_energy (hγ.1.mono hk0 hkl hk1) fun τ hτ =>
      hγ.2.1 τ ⟨hk0.trans hτ.1, hτ.2.trans hk1⟩
  · -- the segment containing `u`: the short geodesic, then `γ` itself
    have hint : ∀ {g : ℝ → V}, g ∈ pathSpace N p q → ∀ x y, x ∈ Icc (0 : ℝ) 1 →
        y ∈ Icc (0 : ℝ) 1 → IntervalIntegrable (fun τ => ‖deriv g τ‖ ^ 2) volume x y :=
      fun hg x y hx hy' => hg.1.intervalIntegrable_norm_deriv_sq.mono_set
        (uIcc_subset_uIcc (by rwa [uIcc_of_le zero_le_one]) (by rwa [uIcc_of_le zero_le_one]))
    have ha01 : B.t k.castSucc ∈ Icc (0 : ℝ) 1 := ⟨hk0, hkl.trans hk1⟩
    have hb01 : B.t k.succ ∈ Icc (0 : ℝ) 1 := ⟨hk0.trans hkl, hk1⟩
    rw [energy, ← intervalIntegral.integral_add_adjacent_intervals (b := u) (hint hr _ _ ha01 hu01)
      (hint hr _ _ hu01 hb01), energy, ← intervalIntegral.integral_add_adjacent_intervals (b := u)
      (hint hγ _ _ ha01 hu01) (hint hγ _ _ hu01 hb01)]
    exact add_le_add (B.energy_retrSeg_mid_le hγ hE hu) (le_of_eq (energy_congr_Icc hu.2
      ((B.retrSeg_eqOn_right hγ hE hu).mono Icc_subset_Ici_self)))
  · -- after `t_{i+1}`: `γ` itself
    have hik : B.t i.succ ≤ B.t k.castSucc := B.t_le_iff.2 (by
      rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; exact hki)
    exact le_of_eq (energy_congr_Icc hkl ((B.retrSeg_eqOn_right hγ hE hu).mono fun τ hτ =>
      (show u ≤ τ from hu.2.trans (hik.trans hτ.1))))

omit hu in
/-- On `[tᵢ, t_{i+1}]`, the broken geodesic of the break points of `γ` is the short geodesic from
`γ(tᵢ)` to `γ(t_{i+1})` over that interval. -/
theorem path_nodeVal_eq_sgeoOver (k : Fin (m + 1)) {τ : ℝ}
    (hτ : τ ∈ Icc (B.t k.castSucc) (B.t k.succ)) :
    B.path (B.nodeVal γ) τ =
      B.sgeoOver (γ (B.t k.castSucc)) (γ (B.t k.succ)) (B.t k.castSucc) (B.t k.succ) τ := by
  rw [B.path_eq_segPath (B.nodeVal_mem hγ hE) k hτ, segPath, sgeoOver, B.vert_nodeVal hγ,
    B.vert_nodeVal hγ]
  rfl

/-- **The formulas for neighbouring segments agree**: on `u ∈ [tᵢ, t_{i+1}]`, the formula with
index `i` is `r_u` (also at `u = t_{i+1}`, where `segOf u` is the next index). -/
theorem retrSeg_eq_retr : B.retrSeg i u γ = B.retr u γ := by
  rcases eq_or_lt_of_le hu.2 with h | h
  · by_cases hi : i = Fin.last m
    · subst hi
      rw [retr, B.segOf_of_one_le (by rw [h, Fin.succ_last, B.t_last])]
    · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 hi
      have hseg : B.segOf u = j.succ := by
        rw [h]
        exact B.segOf_eq le_rfl (B.t_lt_iff.2 (Fin.castSucc_lt_succ (i := j.succ)))
      rw [retr, hseg]
      subst h
      funext τ
      have hlt : B.t j.castSucc.castSucc < B.t j.castSucc.succ :=
        B.t_lt_iff.2 Fin.castSucc_lt_succ
      have e : B.t j.succ.castSucc = B.t j.castSucc.succ := rfl
      simp only [retrSeg, e]
      split_ifs <;> first
        | rfl
        | (exfalso; linarith)
        | exact (B.path_nodeVal_eq_sgeoOver hγ hE j.castSucc ⟨by linarith, by linarith⟩).symm
  · rw [retr, B.segOf_eq hu.1 h]

end Retr

section RetrU

variable {γ : ℝ → V} (hγ : γ ∈ pathSpace N p q) (hE : energy γ 0 1 < c) {u : ℝ}
  (hu : u ∈ Icc (0 : ℝ) 1)
include hγ hE hu

/-- **`r_u(γ) ∈ Ω`** for `0 ≤ u ≤ 1`. -/
theorem retr_mem_pathSpace : B.retr u γ ∈ pathSpace N p q :=
  B.retrSeg_mem_pathSpace hγ hE (B.mem_Icc_segOf hu)

/-- **`E(r_u(γ)) ≤ E(γ)`** (Milnor p. 91). -/
theorem energy_retr_le : energy (B.retr u γ) 0 1 ≤ energy γ 0 1 :=
  B.energy_retrSeg_le hγ hE (B.mem_Icc_segOf hu)

end RetrU

section RetrEnds

variable {γ : ℝ → V} (hγ : γ ∈ pathSpace N p q) (hE : energy γ 0 1 < c)
include hγ hE

/-- **`r_0` is the identity** (on `[0, 1]`). -/
theorem retr_zero : EqOn (B.retr 0 γ) γ (Icc 0 1) := by
  intro τ hτ
  have h01 : B.t (0 : Fin (m + 1)).castSucc < B.t (0 : Fin (m + 1)).succ :=
    B.t_lt_iff.2 Fin.castSucc_lt_succ
  have ht0 : B.t (0 : Fin (m + 1)).castSucc = 0 := by rw [Fin.castSucc_zero, B.t_zero]
  have hseg : B.segOf 0 = 0 := B.segOf_eq ht0.le (by rw [← ht0]; exact h01)
  simp only [retr, hseg, retrSeg, ht0]
  split_ifs with h1
  · rw [le_antisymm h1 hτ.1, ← ht0, B.path_nodeVal_t hγ hE]
  · rfl

/-- **`r_1` is Milnor's retraction `r`**: `r_1(γ)` is the broken geodesic of the break points of
`γ` (on `[0, 1]`). -/
theorem retr_one : EqOn (B.retr 1 γ) (B.path (B.nodeVal γ)) (Icc 0 1) := by
  intro τ hτ
  have h1 : B.t (Fin.last m).succ = 1 := by rw [Fin.succ_last, B.t_last]
  simp only [retr, B.segOf_of_one_le le_rfl, retrSeg]
  split_ifs with h2 h3
  · rfl
  · have := B.path_nodeVal_eq_sgeoOver hγ hE (Fin.last m) (τ := τ) ⟨(not_le.1 h2).le, by
      rw [h1]; exact hτ.2⟩
    rw [h1] at this
    exact this.symm
  · exact absurd hτ.2 h3

end RetrEnds

/-- **`r_u` fixes the broken geodesics** (on `[0, 1]`): on `[tᵢ, u]`, a broken geodesic is a
sub-arc of the short geodesic of its segment, which is the short geodesic between its own ends
(uniqueness in Corollary 10.8). -/
theorem retr_of_mem_brokenPaths {γ : ℝ → V} (hγ : γ ∈ B.brokenPaths) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) : EqOn (B.retr u γ) γ (Icc 0 1) := by
  intro τ hτ
  set i := B.segOf u
  have hui := B.mem_Icc_segOf hu
  simp only [retr, retrSeg]
  split_ifs with h1 h2
  · exact B.path_nodeVal hγ hτ
  · -- the short geodesic from `γ(tᵢ)` to `γ(u)` is `γ`
    have hiu : B.t i.castSucc < u := lt_of_lt_of_le (not_le.1 h1) h2
    obtain ⟨w, hwT, hwδ, hwexp, -, -⟩ := B.exists_segVec hγ i
    set a := B.t i.castSucc
    set s := (u - a) / B.len i
    have hl := B.len_pos i
    have hs0 : 0 < s := div_pos (sub_pos.2 hiu) hl
    have hs1 : s ≤ 1 := by
      rw [div_le_one hl]
      simp only [Subdivision.len, a]
      linarith [hui.2]
    have hball : ∀ σ ∈ Icc (0 : ℝ) 1, γ σ ∈ closedRiemBall N p √c := fun σ hσ =>
      mem_closedRiemBall_of_energy_le hγ.1 hγ.2.2.le hσ
    have ha01 : a ∈ Icc (0 : ℝ) 1 := ⟨B.t_nonneg _, B.t_le_one _⟩
    have hρ := B.riemDist_lt_of_seg hγ.1 hγ.2.2 i le_rfl hui.1 hui.2
    have hw' : prj hN (γ a) (s • w) = s • w := by rw [map_smul, hwT]
    have hwδ' : ‖s • w‖ < B.δ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
      calc s * ‖w‖ ≤ 1 * ‖w‖ := by gcongr
        _ < B.δ := by rw [one_mul]; exact hwδ
    have hexp : exp hN (γ a) (s • w) = γ u := hwexp u hui
    have hj := (B.joinVec_spec (hball _ ha01) (hball _ hu) hρ).2.2.2.2 _ hw' hwδ' hexp
    rw [sgeoOver, ← hj, smul_smul]
    have : (τ - a) / (u - a) * s = (τ - a) / B.len i := by
      simp only [s]
      field_simp [(sub_pos.2 hiu).ne']
    rw [this]
    exact hwexp τ ⟨(not_le.1 h1).le, h2.trans hui.2⟩
  · rfl

end BrokenSetup

end Morse
