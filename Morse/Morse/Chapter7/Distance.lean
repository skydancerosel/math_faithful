import Morse.Chapter7.Minimal

/-!
Milnor, *Morse Theory*, §10, p. 62, for a submanifold `N ⊆ ℝᴷ` with the induced metric.

# The Riemannian distance

## Milnor's text, paraphrased

(p. 62) Define the *distance* `ρ(p, q)` between two points `p, q ∈ M` to be the greatest lower
bound of the arc-lengths of piecewise smooth paths joining these points.  Milnor asserts that this
"clearly" makes `M` a metric space, and that its compatibility with the topology of `M` follows
easily from Theorem 10.4.

## In the embedded setting

* `Morse.riemDist hN p q ∈ [0, ∞]`: the infimum of the lengths of piecewise smooth paths in `N`
  from `p` to `q`; `∞` if there is none (for `q ∉ N`, or `q` in another component of `N`).
* **The metric axioms**: `Morse.riemDist_self`, `Morse.riemDist_comm` (reversal of paths),
  `Morse.riemDist_triangle` (concatenation), `Morse.eq_of_riemDist_eq_zero` (positivity, from the
  exposition's Lemma C, `Morse.NormalCoord.exists_crossing`).  So `riemDist` is an extended metric
  on `N`.
* **Small metric balls are normal balls** (`Morse.NormalCoord.riemDist_lt_iff`): if `ε` is a
  normal radius at `p` and `0 < r ≤ ε`, then `{y : ρ(p, y) < r} = exp_p(B_r(0))`; and points of
  the sphere `exp_p(v)`, `‖v‖ < ε`, are at distance exactly `‖v‖`
  (`Morse.NormalCoord.riemDist_exp`).
* **Compatibility with the topology** (`Morse.hasBasis_nhdsWithin_riemDist`): the metric balls
  `{y : ρ(p, y) < r}`, `r > 0`, form a basis of neighbourhoods of `p` in `N`.
* **Corollary 10.8** (`Morse.corollary_10_8`): for a compact `K ⊆ N` there is `δ > 0` such that
  any two points of `K` at distance `< δ` are joined by a unique geodesic of length `< δ`, which is
  minimal and depends smoothly on its endpoints (`Morse.IsShortJoin`).

Milnor's Corollary 10.8 (p. 62): given a compact set `K ⊂ M` there is `δ > 0` such that any two
points of `K` with distance less than `δ` are joined by a unique geodesic of length less than `δ`;
this geodesic is minimal and depends differentiably on its endpoints.  Proof: cover `K` by open
sets `W` as in 10.3 and let `δ` be small enough so that any two points of `K` at distance `< δ` lie
in a common `W`.

## What Milnor leaves implicit

* **Positivity** (`ρ(p, q) > 0` for `p ≠ q`) is not "clear": a path from `p` to `q` may leave every
  normal neighbourhood of `p`, and the lower bound needs the shell-crossing argument
  (`Morse.NormalCoord.exists_crossing`, used through `Morse.NormalCoord.ofReal_le_riemDist`).
* **Finiteness** needs `M` connected (Milnor's standing assumption); here `ρ` takes values in
  `[0, ∞]`, so no connectedness is assumed.
* **Compatibility with the topology** "follows easily from 10.4": precisely, a metric ball of radius
  `r ≤ ε` is the normal ball `exp_p(B_r(0))`, which is open in `N`, and normal balls of small
  radius lie in any given neighbourhood of `p` (continuity of `exp_p` at `0`).
* **Corollary 10.8.**  Choosing `δ` so that any two points of `K` at distance `< δ` lie in a
  common `W` is a Lebesgue number argument; here it is done with a finite subcover by
  metric balls `B(x_i, s_i)`, `2s_i` smaller than the `ε` and the size of `W` at `x_i`, and the
  triangle inequality, with `δ = min s_i`.  Uniqueness "of length `< δ`" needs `δ ≤ ε_i` (else
  Lemma 10.3 (1) does not apply); minimality is Theorem 10.4 (`ρ(y, z) = ‖v‖`); "depends
  differentiably" means: the initial vector is, near each pair, the restriction of a smooth map on
  an open set of pairs (`V × V`), on the pairs at distance `< δ`.
-/

open Set Filter Topology Function Module Metric MeasureTheory
open scoped ContDiff Manifold RealInnerProductSpace ENNReal

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

/-- The lengths of the piecewise smooth paths in `N` from `p` to `q`, as extended reals. -/
def pathLengths (p q : V) : Set ℝ≥0∞ :=
  {L | ∃ (c : ℝ → V) (a b : ℝ), IsPiecewiseSmooth c a b ∧ (∀ t ∈ Icc a b, c t ∈ N) ∧
    c a = p ∧ c b = q ∧ L = ENNReal.ofReal (pathLength c a b)}

/-- **The distance** `ρ(p, q)` (Milnor, p. 62): the greatest lower bound of the lengths of
piecewise smooth paths in `N` joining `p` to `q` (`∞` if there is none). -/
def riemDist (p q : V) : ℝ≥0∞ := sInf (pathLengths (N := N) p q)

omit [FiniteDimensional ℝ V] in
theorem riemDist_le_pathLength {c : ℝ → V} {a b : ℝ} (hc : IsPiecewiseSmooth c a b)
    (hcN : ∀ t ∈ Icc a b, c t ∈ N) :
    riemDist (N := N) (c a) (c b) ≤ ENNReal.ofReal (pathLength c a b) :=
  sInf_le ⟨c, a, b, hc, hcN, rfl, rfl, rfl⟩

omit [FiniteDimensional ℝ V] in
theorem riemDist_self {p : V} (hp : p ∈ N) : riemDist (N := N) p p = 0 := by
  refine le_antisymm ?_ bot_le
  have h := riemDist_le_pathLength (N := N) (c := fun _ => p) (a := 0) (b := 0)
    (IsPiecewiseSmooth.of_contDiffOn (s := univ) contDiffOn_const le_rfl (subset_univ _))
    (fun _ _ => hp)
  simpa [pathLength] using h

omit [FiniteDimensional ℝ V] in
theorem riemDist_eq_top_of_notMem {p q : V} (hq : q ∉ N) : riemDist (N := N) p q = ⊤ := by
  rw [riemDist, sInf_eq_top]
  rintro L ⟨c, a, b, hc, hcN, -, hb, -⟩
  exact absurd (hb ▸ hcN b ⟨hc.1, le_rfl⟩) hq

omit [FiniteDimensional ℝ V] in
theorem pathLengths_comm (p q : V) : pathLengths (N := N) p q ⊆ pathLengths (N := N) q p := by
  rintro L ⟨c, a, b, hc, hcN, ha, hb, rfl⟩
  refine ⟨fun t => c (a + b - t), a, b, hc.reverse, fun t ht => hcN _
    ⟨by linarith [ht.2], by linarith [ht.1]⟩, by simp [hb], by simp [ha],
    by rw [pathLength_reverse]⟩

omit [FiniteDimensional ℝ V] in
/-- **Symmetry** of the distance (reversal of paths). -/
theorem riemDist_comm (p q : V) : riemDist (N := N) p q = riemDist (N := N) q p := by
  rw [riemDist, riemDist, Subset.antisymm (pathLengths_comm p q) (pathLengths_comm q p)]

omit [FiniteDimensional ℝ V] in
/-- **The triangle inequality** (concatenation of paths). -/
theorem riemDist_triangle (p q r : V) :
    riemDist (N := N) p r ≤ riemDist (N := N) p q + riemDist (N := N) q r := by
  rw [riemDist, riemDist, riemDist, sInf_eq_iInf' (s := pathLengths (N := N) p q),
    sInf_eq_iInf' (s := pathLengths (N := N) q r)]
  refine ENNReal.le_iInf_add_iInf fun L₁ L₂ => ?_
  obtain ⟨L₁, c₁, a₁, b₁, hc₁, hc₁N, ha₁, hb₁, rfl⟩ := L₁
  obtain ⟨L₂, c₂, a₂, b₂, hc₂, hc₂N, ha₂, hb₂, rfl⟩ := L₂
  set d := a₂ - b₁ with hd
  have hc₂' := hc₂.translate d
  have ha₂' : a₂ - d = b₁ := by rw [hd]; ring
  rw [ha₂'] at hc₂'
  have hjoin : c₁ b₁ = (fun t => c₂ (t + d)) b₁ := by simp [hd, hb₁, ha₂]
  have hcat := hc₁.concat hc₂' hjoin
  have hlen := pathLength_concat hc₁.isAdmissible hc₂'.isAdmissible
  have htr := pathLength_translate c₂ a₂ b₂ d
  rw [ha₂'] at htr
  rw [htr] at hlen
  have hle := riemDist_le_pathLength (N := N) hcat (by
    intro t ht
    by_cases h : t ≤ b₁
    · simp only [if_pos h]; exact hc₁N t ⟨ht.1, h⟩
    · simp only [if_neg h]
      exact hc₂N _ ⟨by linarith [not_le.1 h], by linarith [ht.2]⟩)
  have hstart : (if a₁ ≤ b₁ then c₁ a₁ else c₂ (a₁ + d)) = p := by
    simp [if_pos hc₁.1, ha₁]
  have hend : (if b₂ - d ≤ b₁ then c₁ (b₂ - d) else c₂ (b₂ - d + d)) = r := by
    rcases eq_or_lt_of_le hc₂.1 with h | h
    · simp only [hd, show b₂ - (a₂ - b₁) = b₁ by rw [← h]; ring, le_refl, if_pos]
      rw [hb₁, ← ha₂, ← hb₂, h]
    · have : ¬ (b₂ - d ≤ b₁) := by rw [hd]; linarith
      simp only [if_neg this, show b₂ - d + d = b₂ by ring, hb₂]
  rw [hstart, hend, hlen,
    ENNReal.ofReal_add hc₁.isAdmissible.pathLength_nonneg hc₂.isAdmissible.pathLength_nonneg]
    at hle
  exact hle

/-! ### Normal balls and metric balls -/

namespace NormalCoord

variable {hN} {p : N} {ε : ℝ} (nc : NormalCoord hN p ε)

/-- **A lower bound for the distance** (Theorem 10.4 for paths leaving the normal ball): every
point of `N` outside the normal ball `B_s(p)`, `0 < s < ε`, is at distance `≥ s`. -/
theorem ofReal_le_riemDist {s : ℝ} (hs : 0 < s) (hsε : s < ε) {y : V}
    (hy : y ∉ nc.ballSet s) : ENNReal.ofReal s ≤ riemDist (N := N) p y := by
  refine le_sInf ?_
  rintro L ⟨c, a, b, hc, hcN, ha, hb, rfl⟩
  obtain ⟨t₁, t₂, ht₁, ht₁₂, ht₂, -, -, -, -, hL⟩ :=
    nc.exists_crossing hc.isAdmissible hcN ha hs hsε (by rw [hb]; exact hy)
  exact ENNReal.ofReal_le_ofReal (hL.trans (hc.isAdmissible.pathLength_le ht₁ ht₁₂.le ht₂))

include nc in
/-- The radial geodesic gives the upper bound `ρ(p, exp_p v) ≤ ‖v‖`. -/
theorem riemDist_exp_le {v : V} (hv : v ∈ tangentSubspace hN p) (hvε : ‖v‖ < ε) :
    riemDist (N := N) p (exp hN p v) ≤ ENNReal.ofReal ‖v‖ := by
  obtain ⟨δ, hδ, hgeo, -⟩ := nc.radial hv hvε
  have hps : IsPiecewiseSmooth (fun t : ℝ => exp hN p (t • v)) 0 1 :=
    IsPiecewiseSmooth.of_contDiffOn hgeo.contDiffOn zero_le_one
      (Icc_subset_Ioo (by linarith) (by linarith))
  have hN' : ∀ t ∈ Icc (0 : ℝ) 1, exp hN p (t • v) ∈ N := by
    intro t ht
    refine nc.exp_mem (Submodule.smul_mem _ _ hv) ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    calc t * ‖v‖ ≤ 1 * ‖v‖ := by gcongr; exact ht.2
      _ < ε := by linarith
  have h := riemDist_le_pathLength (N := N) hps hN'
  simp only [zero_smul, one_smul, exp_zero p.2] at h
  rwa [nc.pathLength_exp_smul hv hvε] at h

include nc in
/-- **Points of the spheres are at the expected distance** (Milnor, p. 62, via Theorem 10.4):
`ρ(p, exp_p v) = ‖v‖` for `v ∈ T_pN`, `‖v‖ < ε`. -/
theorem riemDist_exp {v : V} (hv : v ∈ tangentSubspace hN p) (hvε : ‖v‖ < ε) :
    riemDist (N := N) p (exp hN p v) = ENNReal.ofReal ‖v‖ := by
  refine le_antisymm (nc.riemDist_exp_le hv hvε) ?_
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  refine nc.ofReal_le_riemDist (norm_pos_iff.2 hv0) hvε ?_
  rw [nc.mem_ballSet, nc.G_exp v hv hvε]
  exact fun h => lt_irrefl _ h.2

/-- **Small metric balls are normal balls** (Milnor, p. 62): for `0 < r ≤ ε`,
`ρ(p, y) < r` iff `y ∈ N` lies in the normal ball `exp_p(B_r(0))`. -/
theorem riemDist_lt_iff {r : ℝ} (hr : 0 < r) (hrε : r ≤ ε) {y : V} :
    riemDist (N := N) p y < ENNReal.ofReal r ↔ y ∈ N ∧ y ∈ nc.ballSet r := by
  constructor
  · intro h
    have hyN : y ∈ N := by
      by_contra hy
      rw [riemDist_eq_top_of_notMem hy] at h
      exact not_top_lt h
    refine ⟨hyN, ?_⟩
    by_contra hy
    obtain ⟨s, hs0, hs1, hs2⟩ := ENNReal.lt_iff_exists_real_btwn.1 h
    have hsr : s < r := (ENNReal.ofReal_lt_ofReal_iff hr).1 hs2
    have hspos : 0 < s := by
      by_contra hneg
      rw [ENNReal.ofReal_of_nonpos (not_lt.1 hneg)] at hs1
      exact not_lt_zero hs1
    have hy' : y ∉ nc.ballSet s := fun h' => hy ((nc.mem_ballSet).2
      ⟨((nc.mem_ballSet).1 h').1, ((nc.mem_ballSet).1 h').2.trans hsr⟩)
    exact absurd (nc.ofReal_le_riemDist hspos (hsr.trans_le hrε) hy') (not_le.2 hs1)
  · rintro ⟨hyN, hy⟩
    obtain ⟨hyU, hyr⟩ := (nc.mem_ballSet).1 hy
    have hv := nc.G_mem y hyU hyN
    have hvε : ‖nc.G y‖ < ε := nc.norm_G_lt y hyU hyN
    have h := nc.riemDist_exp_le hv hvε
    rw [nc.exp_G y hyU hyN] at h
    exact h.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).2 hyr)

end NormalCoord

include hN in
/-- **Positivity**: distinct points of `N` are at positive distance (so `ρ` is an extended metric
on `N`). -/
theorem eq_of_riemDist_eq_zero {p q : N} (h : riemDist (N := N) p q = 0) : p = q := by
  by_contra hne
  have hne' : (q : V) ≠ p := fun h' => hne (Subtype.ext h'.symm)
  obtain ⟨ε, hε, ⟨nc⟩⟩ := exists_isNormalRadius hN p
  have key : ∃ s, 0 < s ∧ s < ε ∧ (q : V) ∉ nc.ballSet s := by
    by_cases hqU : (q : V) ∈ nc.U
    · have hG := norm_pos_iff.2 (nc.G_ne_zero hqU q.2 hne')
      refine ⟨min ‖nc.G q‖ (ε / 2), lt_min hG (by linarith), (min_le_right _ _).trans_lt
        (by linarith), fun h' => ?_⟩
      have := ((nc.mem_ballSet).1 h').2
      exact absurd (this.trans_le (min_le_left _ _)) (lt_irrefl _)
    · exact ⟨ε / 2, by linarith, by linarith, fun h' => hqU ((nc.mem_ballSet).1 h').1⟩
  obtain ⟨s, hs, hsε, hq⟩ := key
  have := nc.ofReal_le_riemDist hs hsε hq
  rw [h, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at this
  linarith

include hN in
/-- **The metric topology is the topology of `N`** (Milnor, p. 62: the metric is compatible with
the topology of `M`): the metric balls `{y : ρ(p, y) < r}`, `r > 0`, form a basis of
neighbourhoods of `p` in `N`. -/
theorem hasBasis_nhdsWithin_riemDist (p : N) :
    (𝓝[N] (p : V)).HasBasis (fun r : ℝ => 0 < r)
      (fun r => {y | riemDist (N := N) p y < ENNReal.ofReal r}) := by
  obtain ⟨ε, hε, ⟨nc⟩⟩ := exists_isNormalRadius hN p
  have hball : ∀ r, 0 < r → r ≤ ε →
      {y | riemDist (N := N) p y < ENNReal.ofReal r} = N ∩ nc.ballSet r := by
    intro r hr hrε
    ext y
    exact nc.riemDist_lt_iff hr hrε
  have hpball : ∀ r, 0 < r → (p : V) ∈ nc.ballSet r := fun r hr =>
    (nc.mem_ballSet).2 ⟨nc.mem_U_self, by rw [nc.G_self, norm_zero]; exact hr⟩
  refine ⟨fun t => ⟨fun ht => ?_, ?_⟩⟩
  · -- a neighbourhood of `p` in `N` contains a small metric ball
    obtain ⟨O, hO, hpO, hOt⟩ := mem_nhdsWithin.1 ht
    have hF0 : nc.F 0 = p := by
      rw [nc.F_eq 0 (Submodule.zero_mem _) (by simpa using nc.pos), exp_zero p.2]
    have hFc : ContinuousAt nc.F 0 :=
      nc.contDiffOn_F.continuousOn.continuousAt (nc.isOpen_O.mem_nhds
        (nc.mem_O 0 (Submodule.zero_mem _) (by simpa using nc.pos)))
    obtain ⟨r₀, hr₀, hr₀O⟩ := Metric.mem_nhds_iff.1
      (hFc.preimage_mem_nhds (hO.mem_nhds (by rw [hF0]; exact hpO)))
    set r := min r₀ ε with hr_def
    have hr : 0 < r := lt_min hr₀ hε
    refine ⟨r, hr, fun y hy => hOt ⟨?_, ?_⟩⟩
    · rw [hball r hr (min_le_right _ _)] at hy
      obtain ⟨hyN, hy⟩ := hy
      obtain ⟨hyU, hyr⟩ := (nc.mem_ballSet).1 hy
      have hv := nc.G_mem y hyU hyN
      have hvε := nc.norm_G_lt y hyU hyN
      have hFy : nc.F (nc.G y) = y := by rw [nc.F_eq _ hv hvε, nc.exp_G y hyU hyN]
      rw [← hFy]
      exact hr₀O (by rw [mem_ball, dist_zero_right]; exact hyr.trans_le (min_le_left _ _))
    · rw [hball r hr (min_le_right _ _)] at hy
      exact hy.1
  · -- a metric ball is a neighbourhood of `p` in `N`
    rintro ⟨r, hr, hrt⟩
    set r' := min r ε with hr'_def
    have hr' : 0 < r' := lt_min hr hε
    have hsub : N ∩ nc.ballSet r' ⊆ t := by
      intro y hy
      rw [← hball r' hr' (min_le_right _ _)] at hy
      exact hrt (lt_of_lt_of_le hy (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
    refine mem_of_superset ?_ hsub
    exact inter_mem_nhdsWithin N ((nc.isOpen_ballSet r').mem_nhds (hpball r' hr'))

/-! ### Corollary 10.8 -/

/-- The conclusion of Corollary 10.8 for two points `y, z` and a bound `δ`: `y` and `z` are joined
by a geodesic `t ↦ exp_y(tv)`, `0 ≤ t ≤ 1`, of length `‖v‖ < δ`; it is minimal
(`ρ(y, z) = ‖v‖`); it is the only geodesic from `y` to `z` of length `< δ`; and `v` depends
smoothly on the endpoints (it is the restriction of a smooth map `G` near `(y, z)`, on pairs at
distance `< δ`). -/
def IsShortJoin (δ : ℝ) (y z : N) : Prop :=
  ∃ v ∈ tangentSubspace hN y, ‖v‖ < δ ∧ exp hN y v = z ∧
    riemDist (N := N) y z = ENNReal.ofReal ‖v‖ ∧
    (∀ w ∈ tangentSubspace hN y, ‖w‖ < δ → exp hN y w = z → w = v) ∧
    ∃ O₂ : Set (V × V), IsOpen O₂ ∧ ((y : V), (z : V)) ∈ O₂ ∧ ∃ G : V × V → V,
      ContDiffOn ℝ ∞ G O₂ ∧ G (y, z) = v ∧
      ∀ y' z' : N, ((y' : V), (z' : V)) ∈ O₂ → riemDist (N := N) y' z' < ENNReal.ofReal δ →
        G (y', z') ∈ tangentSubspace hN y' ∧ ‖G (y', z')‖ < δ ∧ exp hN y' (G (y', z')) = z'

/-- Lemma 10.3 read with the distance: around each `p` there are an open set `Ω ∋ p` and `s > 0`
such that points of `N ∩ Ω` are at distance `< s` from `p`, and any point `y ∈ N ∩ Ω` and any
`z` at distance `< δ ≤ s` from `y` are joined as in Corollary 10.8. -/
theorem exists_isShortJoin (p : N) :
    ∃ s > 0, ∃ Ω : Set V, IsOpen Ω ∧ (p : V) ∈ Ω ∧
      (∀ y : N, (y : V) ∈ Ω → riemDist (N := N) p y < ENNReal.ofReal s) ∧
      ∀ δ, 0 < δ → δ ≤ s → ∀ y z : N, (y : V) ∈ Ω → riemDist (N := N) y z < ENNReal.ofReal δ →
        IsShortJoin hN δ y z := by
  obtain ⟨O, hO, hpO, ε, hε, h1, ⟨O₂', hO₂', G', hG', h2⟩, h3⟩ := lemma_10_3 hN p
  obtain ⟨r, hr, hrO⟩ := (hasBasis_nhdsWithin_riemDist hN p).mem_iff.1
    (mem_nhdsWithin_of_mem_nhds (hO.mem_nhds hpO))
  obtain ⟨nc₀⟩ := h3 p hpO
  set s := min r ε / 2 with hs_def
  have hs : 0 < s := by positivity
  have hsε : s ≤ ε := by have := min_le_right r ε; linarith
  have hsr : 2 * s ≤ r := by have := min_le_left r ε; linarith
  refine ⟨s, hs, nc₀.ballSet s, nc₀.isOpen_ballSet s, (nc₀.mem_ballSet).2 ⟨nc₀.mem_U_self, by
    rw [nc₀.G_self, norm_zero]; exact hs⟩, fun y hy => (nc₀.riemDist_lt_iff hs hsε).2 ⟨y.2, hy⟩,
    fun δ hδ hδs y z hy hyz => ?_⟩
  -- `y` and `z` lie in `O`
  have hpy : riemDist (N := N) p y < ENNReal.ofReal s := (nc₀.riemDist_lt_iff hs hsε).2 ⟨y.2, hy⟩
  have hinO : ∀ w : N, riemDist (N := N) p w < ENNReal.ofReal (2 * s) → (w : V) ∈ O := fun w hw =>
    hrO (lt_of_lt_of_le hw (ENNReal.ofReal_le_ofReal hsr))
  have hyO : (y : V) ∈ O := hinO y (lt_of_lt_of_le hpy (ENNReal.ofReal_le_ofReal (by linarith)))
  have hzO : (z : V) ∈ O := by
    refine hinO z (lt_of_le_of_lt (riemDist_triangle (N := N) p y z) ?_)
    calc riemDist (N := N) p y + riemDist (N := N) y z
        < ENNReal.ofReal s + ENNReal.ofReal δ := ENNReal.add_lt_add hpy hyz
      _ ≤ ENNReal.ofReal (2 * s) := by
        rw [← ENNReal.ofReal_add hs.le hδ.le]
        exact ENNReal.ofReal_le_ofReal (by linarith)
  -- the distance of two points of `O` is the length of the geodesic of Lemma 10.3
  have hdist : ∀ y' z' : N, (y' : V) ∈ O → ∀ w ∈ tangentSubspace hN y', ‖w‖ < ε →
      exp hN y' w = z' → riemDist (N := N) y' z' = ENNReal.ofReal ‖w‖ := by
    intro y' z' hy' w hw hwε hexp
    obtain ⟨nc⟩ := h3 y' hy'
    rw [← hexp]
    exact nc.riemDist_exp hw hwε
  obtain ⟨v, ⟨hv, hvε, hexp⟩, huniq⟩ := h1 y z hyO hzO
  have hρ := hdist y z hyO v hv hvε hexp
  have hvδ : ‖v‖ < δ := by
    rw [hρ] at hyz
    exact (ENNReal.ofReal_lt_ofReal_iff hδ).1 hyz
  refine ⟨v, hv, hvδ, hexp, hρ, fun w hw hwδ hwexp =>
    huniq w ⟨hw, hwδ.trans_le (hδs.trans hsε), hwexp⟩, O₂' ∩ O ×ˢ O,
    hO₂'.inter (hO.prod hO), ⟨(h2 y z hyO hzO).1, hyO, hzO⟩, G', hG'.mono inter_subset_left,
    ?_, fun y' z' hyz' hρ' => ?_⟩
  · obtain ⟨-, hG1, hG2, hG3⟩ := h2 y z hyO hzO
    exact huniq _ ⟨hG1, hG2, hG3⟩
  · obtain ⟨-, hG1, hG2, hG3⟩ := h2 y' z' hyz'.2.1 hyz'.2.2
    refine ⟨hG1, ?_, hG3⟩
    rw [hdist y' z' hyz'.2.1 _ hG1 hG2 hG3] at hρ'
    exact (ENNReal.ofReal_lt_ofReal_iff hδ).1 hρ'

/-- **Corollary 10.8** (Milnor, p. 62).  Given a compact set `K ⊆ N` there is a number `δ > 0` such
that any two points `y, z` of `K` at distance `< δ` are joined by a unique geodesic of length
`< δ`; this geodesic is minimal and depends smoothly on its endpoints
(`Morse.IsShortJoin`). -/
theorem corollary_10_8 {K : Set V} (hK : IsCompact K) (hKN : K ⊆ N) :
    ∃ δ > 0, ∀ y z : N, (y : V) ∈ K → (z : V) ∈ K →
      riemDist (N := N) y z < ENNReal.ofReal δ → IsShortJoin hN δ y z := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨1, one_pos, fun y _ hy => absurd hy (notMem_empty _)⟩
  choose s hs Ω hΩ hpΩ _hball hjoin using fun x : K => exists_isShortJoin hN ⟨x, hKN x.2⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover Ω hΩ fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hpΩ _⟩
  have htne : t.Nonempty := by
    obtain ⟨x, hx⟩ := hKne
    obtain ⟨i, hi, -⟩ := mem_iUnion₂.1 (ht hx)
    exact ⟨i, hi⟩
  set δ := t.inf' htne s with hδ_def
  have hδ : 0 < δ := (Finset.lt_inf'_iff htne).2 fun i _ => hs i
  refine ⟨δ, hδ, fun y z hy _ hyz => ?_⟩
  obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 (ht hy)
  exact hjoin i δ hδ (Finset.inf'_le s hi) y z hyi hyz

end Morse
