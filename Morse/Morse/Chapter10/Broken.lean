import Morse.Chapter10.Product
import Morse.Chapter9.GeodesicVariation
import Morse.Chapter7.HopfRinow

/-!
Milnor, *Morse Theory*, §16, pp. 88–89 (Lemma 16.1), for a submanifold `N ⊆ ℝᴷ` with the induced
metric.

# The manifold of broken geodesics

## Milnor's text, paraphrased

(p. 88) `M` is a connected Riemannian manifold, `Ω = Ω(M; p, q)`, `E : Ω → ℝ` the energy;
`Ω^c = E⁻¹[0, c]` and `Int Ω^c = E⁻¹[0, c)`.  For a subdivision `0 = t₀ < t₁ < ⋯ < t_k = 1`,
`Ω(t₀, …, t_k)` is the set of `ω ∈ Ω` with `ω|[t_{i−1}, t_i]` a geodesic for each `i`, and
`Ω(t₀, …, t_k)^c = Ω^c ∩ Ω(t₀, …, t_k)`, `Int Ω(t₀, …, t_k)^c = (Int Ω^c) ∩ Ω(t₀, …, t_k)`.

**Lemma 16.1** (p. 88).  Let `M` be complete and `c > 0` with `Ω^c ≠ ∅`.  For all sufficiently
fine subdivisions the set `Int Ω(t₀, …, t_k)^c` can be given the structure of a smooth finite
dimensional manifold in a natural way.

*Proof* (p. 89).  Every `ω ∈ Ω^c` lies in the ball `S = {x : ρ(x, p) ≤ √c}`, since `L² ≤ E ≤ c`;
`S` is compact as `M` is complete; by 10.8 there is `ε > 0` such that any `x, y ∈ S` with
`ρ(x, y) < ε` are joined by a unique geodesic of length `< ε`, depending differentiably on
`x, y`.  Choose the subdivision with `t_i − t_{i−1} < ε²/c`.  For a broken geodesic `ω` in
`Ω(t₀, …, t_k)^c`, `(L_{t_{i−1}}^{t_i} ω)² = (t_i − t_{i−1}) E_{t_{i−1}}^{t_i} ω ≤
(t_i − t_{i−1}) c < ε²`, so `ω|[t_{i−1}, t_i]` is determined by its end points, and `ω` by
`(ω(t₁), …, ω(t_{k−1})) ∈ M × ⋯ × M`.  "Evidently" this defines a homeomorphism of
`Int Ω(t₀, …, t_k)^c` onto an open subset of the product, whose differentiable structure is taken
over.

## In the embedded setting

`N ⊆ V` is a slice submanifold with the induced metric and distance `ρ = Morse.riemDist`.  We
write `k = m + 1`: `m` interior break points.

* `Morse.Subdivision m`: `t : Fin (m + 2) → ℝ` strictly increasing from `0` to `1`;
  `Morse.Subdivision.len i = t_{i+1} − t_i`.
* `Morse.closedRiemBall N p r = {x ∈ N : ρ(p, x) ≤ r}` (Milnor's `S` for `r = √c`);
  `Morse.mem_closedRiemBall_of_energy_le` (**Step 1**: paths of energy `≤ c` lie in `S`);
  compactness from completeness: `Morse.isCompact_closedRiemBall_of_isClosed` (for `N` closed in
  `V`), `Morse.isCompact_closedRiemBall_of_isRiemComplete` (for `(N, ρ)` complete, Hopf–Rinow).
* `Morse.corollary_10_8'`: Corollary 10.8 together with a normal radius `≥ δ` at every point of
  the compact set (used in `Morse/Chapter10/BrokenIndex.lean` to exclude conjugate points on the
  segments).
* `Morse.BrokenSetup hN p q c m`: **Milnor's choices, made precise**: `p, q ∈ N`, `c > 0`, `S`
  compact, a number `δ > 0` (Milnor's `ε`) for which the conclusion of Corollary 10.8 holds on
  `S` (`Morse.IsShortJoin`) and which is at most a normal radius at every point of `S`, and a
  subdivision with `c (t_{i+1} − t_i) < δ²`.  **"Sufficiently fine"**: `Morse.exists_brokenSetup`
  — there is `η > 0` such that every subdivision with all `t_{i+1} − t_i < η` carries such data
  (`η = δ²/c`); `Morse.Subdivision.uniform` provides subdivisions of any mesh.
* For `B : BrokenSetup …`: `B.vert y` are the vertices `p, y₀, …, y_{m−1}, q`;
  `B.joinVec x x'` the initial vector of the short geodesic from `x` to `x'`; `B.energy' y =
  Σᵢ ρ(xᵢ, xᵢ₊₁)² / (t_{i+1} − tᵢ)`; `B.nodes = {y ∈ N^m : B.energy' y < c}` (Milnor's open
  subset `U`); `B.path y` the broken geodesic with break points `y`; `B.nodeVal ω` the break
  points `(ω(t₁), …, ω(t_m))` of a path.
* **Lemma 16.1**: `Morse.BrokenSetup.lemma_16_1`: `y ↦ B.path y` and `ω ↦ B.nodeVal ω` are
  inverse bijections between `B.nodes` and the broken geodesics in `Int Ω^c` (as paths on
  `[0, 1]`); `B.energy (B.path y) = B.energy' y` is formula (∗) of the exposition.

## What Milnor leaves implicit (see Exposition/Chapter10.md, §2)

* `Ω^c ≠ ∅` is not needed.  Completeness is used only through the compactness of `S`.
* **The image is `U`**: the break points of a path in `Int Ω(t₀, …, t_k)^c` lie in `S` and satisfy
  `Σ ρ²/(t_{i+1} − tᵢ) < c` (Schwarz's inequality `ρ² ≤ L² ≤ (t_{i+1} − tᵢ) E_{tᵢ}^{t_{i+1}}`),
  and conversely every `y ∈ U` has its vertices in `S` (Cauchy–Schwarz:
  `ρ(p, xᵢ) ≤ Σ ρ(x_j, x_{j+1}) ≤ (Σ (t_{j+1} − t_j))^{1/2} (Σ ρ²/(t_{j+1} − t_j))^{1/2} < √c`) and
  consecutive vertices at distance `< δ`, so the broken geodesic `B.path y` exists.
* **A segment is the short geodesic between its ends**: a geodesic on `[tᵢ, t_{i+1}]` is the
  radial geodesic `t ↦ exp_{xᵢ}((t − tᵢ)/(t_{i+1} − tᵢ) w)` (`Morse.exists_initial_ray`), and its
  initial vector `w` has `‖w‖² = (t_{i+1} − tᵢ) E_{tᵢ}^{t_{i+1}} < δ²`, so `w` is the short join
  vector by the uniqueness in Corollary 10.8.
* **Smoothness at the ends of a segment**: a piecewise smooth path which is a geodesic on
  `(tᵢ, t_{i+1})` is smooth on the closed interval (its own pieces at the ends).
-/

open Set Filter Topology Function Module Metric MeasureTheory
open scoped ContDiff Manifold RealInnerProductSpace ENNReal Interval

noncomputable section

namespace Morse

/-! ### Subdivisions of `[0, 1]` -/

/-- **A subdivision** `0 = t₀ < t₁ < ⋯ < t_{m+1} = 1` of `[0, 1]`, with `m` interior points
(Milnor's `k = m + 1` segments). -/
structure Subdivision (m : ℕ) where
  /-- The division points. -/
  t : Fin (m + 2) → ℝ
  strictMono : StrictMono t
  t_zero : t 0 = 0
  t_last : t (Fin.last (m + 1)) = 1

namespace Subdivision

variable {m : ℕ} (s : Subdivision m)

/-- The length `t_{i+1} − t_i` of the `i`-th segment. -/
def len (i : Fin (m + 1)) : ℝ := s.t i.succ - s.t i.castSucc

theorem len_pos (i : Fin (m + 1)) : 0 < s.len i :=
  sub_pos.2 (s.strictMono Fin.castSucc_lt_succ)

theorem t_nonneg (i : Fin (m + 2)) : 0 ≤ s.t i := by
  rw [← s.t_zero]; exact s.strictMono.monotone (Fin.zero_le i)

theorem t_le_one (i : Fin (m + 2)) : s.t i ≤ 1 := by
  rw [← s.t_last]; exact s.strictMono.monotone (Fin.le_last i)

theorem t_le_iff {i j : Fin (m + 2)} : s.t i ≤ s.t j ↔ i ≤ j := s.strictMono.le_iff_le

theorem t_lt_iff {i j : Fin (m + 2)} : s.t i < s.t j ↔ i < j := s.strictMono.lt_iff_lt

/-- The lengths of the segments add up to `1`. -/
theorem sum_len : ∑ i, s.len i = 1 := by
  have h1 := Fin.sum_univ_succ s.t
  have h2 := Fin.sum_univ_castSucc s.t
  simp only [len, Finset.sum_sub_distrib]
  linarith [s.t_zero, s.t_last]

/-- The interior break points `t₁, …, t_m`. -/
def breaks : Finset ℝ := Finset.univ.image fun j : Fin m => s.t j.castSucc.succ

theorem mem_breaks {x : ℝ} : x ∈ s.breaks ↔ ∃ j : Fin m, s.t j.castSucc.succ = x := by
  simp [breaks]

theorem breaks_subset {x : ℝ} (hx : x ∈ s.breaks) : x ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨j, rfl⟩ := s.mem_breaks.1 hx
  constructor
  · rw [← s.t_zero, s.t_lt_iff, Fin.lt_def]; simp
  · rw [← s.t_last, s.t_lt_iff, Fin.lt_def]; simp

/-- **The segment containing `τ`**: the first `i` with `τ < t_{i+1}` (the last segment if there is
none). -/
def segOf (τ : ℝ) : Fin (m + 1) :=
  if h : ∃ i : Fin (m + 1), τ < s.t i.succ then Fin.find (fun i => τ < s.t i.succ) h
  else Fin.last m

theorem segOf_eq {i : Fin (m + 1)} {τ : ℝ} (h1 : s.t i.castSucc ≤ τ) (h2 : τ < s.t i.succ) :
    s.segOf τ = i := by
  have hex : ∃ i : Fin (m + 1), τ < s.t i.succ := ⟨i, h2⟩
  rw [segOf, dif_pos hex]
  set j := Fin.find (fun i => τ < s.t i.succ) hex
  have hj : τ < s.t j.succ := Fin.find_spec hex
  rcases lt_trichotomy j i with hji | rfl | hij
  · exfalso
    have : s.t j.succ ≤ s.t i.castSucc := s.t_le_iff.2 (by
      rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; exact hji)
    linarith
  · rfl
  · exact absurd h2 (Fin.find_min hex hij)

theorem segOf_of_one_le {τ : ℝ} (h : 1 ≤ τ) : s.segOf τ = Fin.last m := by
  have hno : ¬∃ i : Fin (m + 1), τ < s.t i.succ := by
    rintro ⟨i, hi⟩
    linarith [s.t_le_one i.succ]
  rw [segOf, dif_neg hno]

/-- Every `τ ∈ [0, 1]` lies in its segment. -/
theorem mem_Icc_segOf {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    τ ∈ Icc (s.t (s.segOf τ).castSucc) (s.t (s.segOf τ).succ) := by
  by_cases hex : ∃ i : Fin (m + 1), τ < s.t i.succ
  · rw [segOf, dif_pos hex]
    set j := Fin.find (fun i => τ < s.t i.succ) hex
    refine ⟨?_, (Fin.find_spec hex).le⟩
    by_cases hj0 : j = 0
    · rw [hj0, Fin.castSucc_zero, s.t_zero]; exact hτ.1
    · obtain ⟨k, hk⟩ := Fin.exists_succ_eq.2 hj0
      have hkj : k.castSucc < j := by rw [← hk]; exact Fin.castSucc_lt_succ
      have := Fin.find_min hex hkj
      push Not at this
      rw [← hk]
      exact this
  · rw [segOf, dif_neg hex]
    push Not at hex
    have h1 : 1 ≤ τ := by simpa [s.t_last] using hex (Fin.last m)
    have hτ1 : τ = 1 := le_antisymm hτ.2 h1
    refine ⟨?_, ?_⟩
    · rw [hτ1]; exact s.t_le_one _
    · rw [hτ1, Fin.succ_last, s.t_last]

/-- A closed interval `[a, b] ⊆ [0, 1]` with no break point in its interior lies in one
segment. -/
theorem exists_seg_of_piece {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hB : ∀ x ∈ s.breaks, x ∉ Ioo a b) :
    ∃ i : Fin (m + 1), s.t i.castSucc ≤ a ∧ b ≤ s.t i.succ := by
  obtain ⟨i, hi⟩ : ∃ i, s.segOf a = i := ⟨_, rfl⟩
  have hai := s.mem_Icc_segOf ⟨ha, hab.le.trans hb⟩
  rw [hi] at hai
  refine ⟨i, hai.1, ?_⟩
  by_contra hlt
  push Not at hlt
  -- `t_{i+1}` is an interior break point in `(a, b)`
  have hil : i ≠ Fin.last m := by
    rintro rfl
    rw [Fin.succ_last, s.t_last] at hlt
    linarith
  obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 hil
  have hmem : s.t j.castSucc.succ ∈ s.breaks := s.mem_breaks.2 ⟨j, rfl⟩
  have hai' : a < s.t j.castSucc.succ := by
    rcases eq_or_lt_of_le hai.2 with h | h
    · -- `a = t_{i+1}` is impossible: then `segOf a` would be `i + 1`
      exfalso
      have hj' : s.segOf a = j.succ := s.segOf_eq (i := j.succ) (le_of_eq h.symm) (by
        rw [h, s.t_lt_iff]; exact Fin.castSucc_lt_succ (i := j.succ))
      rw [hi] at hj'
      exact absurd (congrArg Fin.val hj') (by simp)
    · exact h
  exact hB _ hmem ⟨hai', hlt⟩

/-- **The uniform subdivision** `t_i = i/(m + 1)`. -/
def uniform (m : ℕ) : Subdivision m where
  t i := (i : ℝ) / (m + 1)
  strictMono := fun i j hij => by
    have : (i : ℝ) < j := by exact_mod_cast hij
    exact div_lt_div_of_pos_right this (by positivity)
  t_zero := by simp
  t_last := by simp [div_self (show (m : ℝ) + 1 ≠ 0 by positivity)]

theorem uniform_len (m : ℕ) (i : Fin (m + 1)) : (uniform m).len i = 1 / (m + 1) := by
  simp only [len, uniform, Fin.val_succ, Fin.val_castSucc]
  push_cast
  ring

end Subdivision

/-! ### Vertices -/

section Vertices

variable {V : Type*} {m : ℕ}

/-- **The vertices** `x₀ = p, x₁ = y₀, …, x_m = y_{m−1}, x_{m+1} = q` of a broken path with
break points `y`. -/
def vert (p q : V) (y : Fin m → V) : Fin (m + 2) → V := Fin.cons p (Fin.snoc y q)

@[simp] theorem vert_zero (p q : V) (y : Fin m → V) : vert p q y 0 = p := rfl

@[simp] theorem vert_last (p q : V) (y : Fin m → V) : vert p q y (Fin.last (m + 1)) = q := by
  simp [vert, ← Fin.succ_last]

@[simp] theorem vert_inner (p q : V) (y : Fin m → V) (j : Fin m) :
    vert p q y j.castSucc.succ = y j := by
  simp [vert]

end Vertices

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

/-! ### Corollary 10.8, with normal radii -/

/-- Lemma 10.3 read with the distance, as in `Morse.exists_isShortJoin`, recording also that the
`ε` of Lemma 10.3, a normal radius at every point near `p`, is at least `s`. -/
theorem exists_isShortJoin' (p : N) :
    ∃ s > 0, ∃ Ω : Set V, IsOpen Ω ∧ (p : V) ∈ Ω ∧
      (∀ y : N, (y : V) ∈ Ω → ∃ ε, s ≤ ε ∧ IsNormalRadius hN y ε) ∧
      ∀ δ, 0 < δ → δ ≤ s → ∀ y z : N, (y : V) ∈ Ω → riemDist (N := N) y z < ENNReal.ofReal δ →
        IsShortJoin hN δ y z := by
  obtain ⟨s, hs, Ω, hΩ, hpΩ, -, hjoin⟩ := exists_isShortJoin hN p
  obtain ⟨O, hO, hpO, ε, hε, -, -, h3⟩ := lemma_10_3 hN p
  -- shrink `Ω` into `O`, and `s` below `ε`
  refine ⟨min s ε, lt_min hs hε, Ω ∩ O, hΩ.inter hO, ⟨hpΩ, hpO⟩,
    fun y hy => ⟨ε, min_le_right _ _, h3 y hy.2⟩,
    fun δ hδ hδs y z hy hyz => hjoin δ hδ (hδs.trans (min_le_left _ _)) y z hy.1 hyz⟩

/-- **Corollary 10.8** (Milnor, p. 62), with normal radii: for a compact `K ⊆ N` there is `δ > 0`
such that any two points of `K` at distance `< δ` are joined as in Corollary 10.8
(`Morse.IsShortJoin`), and every point of `K` has a normal radius `≥ δ`. -/
theorem corollary_10_8' {K : Set V} (hK : IsCompact K) (hKN : K ⊆ N) :
    ∃ δ > 0, (∀ y z : N, (y : V) ∈ K → (z : V) ∈ K →
      riemDist (N := N) y z < ENNReal.ofReal δ → IsShortJoin hN δ y z) ∧
      ∀ y : N, (y : V) ∈ K → ∃ ε, δ ≤ ε ∧ IsNormalRadius hN y ε := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨1, one_pos, fun y _ hy => absurd hy (notMem_empty _), fun y hy => absurd hy
      (notMem_empty _)⟩
  choose s hs Ω hΩ hpΩ hnormal hjoin using fun x : K => exists_isShortJoin' hN ⟨x, hKN x.2⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover Ω hΩ fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hpΩ _⟩
  have htne : t.Nonempty := by
    obtain ⟨x, hx⟩ := hKne
    obtain ⟨i, hi, -⟩ := mem_iUnion₂.1 (ht hx)
    exact ⟨i, hi⟩
  set δ := t.inf' htne s with hδ_def
  have hδ : 0 < δ := (Finset.lt_inf'_iff htne).2 fun i _ => hs i
  refine ⟨δ, hδ, fun y z hy _ hyz => ?_, fun y hy => ?_⟩
  · obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 (ht hy)
    exact hjoin i δ hδ (Finset.inf'_le s hi) y z hyi hyz
  · obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 (ht hy)
    obtain ⟨ε, hsε, hε⟩ := hnormal i y hyi
    exact ⟨ε, (Finset.inf'_le s hi).trans hsε, hε⟩

/-! ### Milnor's ball `S` -/

variable (N) in
/-- **The ball** `S = {x ∈ N : ρ(p, x) ≤ r}` (Milnor p. 89, with `r = √c`). -/
def closedRiemBall (p : V) (r : ℝ) : Set V :=
  {x | x ∈ N ∧ riemDist (N := N) p x ≤ ENNReal.ofReal r}

omit [FiniteDimensional ℝ V] in
theorem closedRiemBall_subset (p : V) (r : ℝ) : closedRiemBall N p r ⊆ N := fun _ hx => hx.1

include hN in
/-- **`S` is compact if `N` is closed in `V`** (the completeness of `M` in Milnor's Lemma 16.1, in
the embedded setting): `S` is closed (`ρ(p, ·)` is continuous on `N`) and bounded
(`‖x − p‖ ≤ ρ(p, x)`). -/
theorem isCompact_closedRiemBall_of_isClosed (hcl : IsClosed N) (p : V) (r : ℝ) :
    IsCompact (closedRiemBall N p r) := by
  by_cases hp : p ∈ N
  · have hcont : ContinuousOn (fun x => riemDist (N := N) p x) N := by
      have := continuousOn_riemDist_left hN p
      exact this.congr fun x _ => riemDist_comm _ _
    have hclosed : IsClosed (closedRiemBall N p r) :=
      hcont.preimage_isClosed_of_isClosed hcl isClosed_Iic
    refine (isCompact_closedBall p (max r 0)).of_isClosed_subset hclosed fun x hx => ?_
    rw [mem_closedBall, dist_eq_norm]
    have h := (ofReal_norm_sub_le_riemDist (N := N) p x).trans hx.2
    rcases ENNReal.ofReal_le_ofReal_iff'.1 h with h1 | h1
    · exact h1.trans (le_max_left _ _)
    · exact h1.trans (le_max_right _ _)
  · have : closedRiemBall N p r = ∅ := by
      ext x
      simp only [closedRiemBall, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro hx h
      rw [riemDist_comm, riemDist_eq_top_of_notMem hp] at h
      exact ENNReal.ofReal_ne_top (top_le_iff.1 h)
    rw [this]
    exact isCompact_empty

include hN in
/-- **`S` is compact if `(N, ρ)` is complete** (Milnor's hypothesis in Lemma 16.1), by the
Hopf–Rinow theorem: closed `ρ`-bounded sets are compact. -/
theorem isCompact_closedRiemBall_of_isRiemComplete (hconn : IsPreconnected N)
    (hcomp : IsRiemComplete N) (p : V) (r : ℝ) : IsCompact (closedRiemBall N p r) := by
  by_cases hp : p ∈ N
  · obtain ⟨-, -, -, hbdd⟩ := hopf_rinow_of_isRiemComplete hN hconn hcomp
    set X : Set N := {x | riemDist (N := N) p x ≤ ENNReal.ofReal r}
    have hXc : IsClosed X := by
      have hcont : Continuous fun x : N => riemDist (N := N) p x := by
        have := continuousOn_riemDist_left hN p
        refine continuousOn_iff_continuous_domRestrict.1 (this.congr fun x _ => riemDist_comm _ _)
      exact isClosed_le hcont continuous_const
    have hXb : IsRiemBounded N (Subtype.val '' X) := by
      refine ⟨2 * r, ?_⟩
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      calc riemDist (N := N) (x : V) y ≤ riemDist (N := N) (x : V) p + riemDist (N := N) p y :=
            riemDist_triangle _ _ _
        _ ≤ ENNReal.ofReal r + ENNReal.ofReal r := by
            rw [riemDist_comm]; exact add_le_add hx hy
        _ = ENNReal.ofReal (2 * r) := by
            rcases le_or_gt 0 r with hr | hr
            · rw [← ENNReal.ofReal_add hr hr, two_mul]
            · simp [ENNReal.ofReal_of_nonpos hr.le,
                ENNReal.ofReal_of_nonpos (by linarith : 2 * r ≤ 0)]
    have h := (hbdd X hXc hXb).image continuous_subtype_val
    convert h using 1
    ext x
    simp only [closedRiemBall, mem_ofPred_eq, mem_image, X]
    constructor
    · rintro ⟨hxN, hx⟩; exact ⟨⟨x, hxN⟩, hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y.2, hy⟩
  · have : closedRiemBall N p r = ∅ := by
      ext x
      simp only [closedRiemBall, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro hx h
      rw [riemDist_comm, riemDist_eq_top_of_notMem hp] at h
      exact ENNReal.ofReal_ne_top (top_le_iff.1 h)
    rw [this]
    exact isCompact_empty

omit [FiniteDimensional ℝ V] in
/-- **Step 1 of Lemma 16.1** (Milnor p. 89: "every path `ω ∈ Ω^c` lies within `S`", from
`L² ≤ E ≤ c`): if `ω ∈ Ω(N; p, q)` has energy `≤ c`, then `ρ(p, ω(t)) ≤ √c` for `t ∈ [0, 1]`. -/
theorem mem_closedRiemBall_of_energy_le {γ : ℝ → V} {p q : V} (hγ : γ ∈ pathSpace N p q)
    {c : ℝ} (hE : energy γ 0 1 ≤ c) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    γ t ∈ closedRiemBall N p √c := by
  obtain ⟨hγs, hγN, hγ0, -⟩ := hγ
  refine ⟨hγN t ht, ?_⟩
  have hst : IsPiecewiseSmooth γ 0 t := hγs.mono le_rfl ht.1 ht.2
  have h1 := riemDist_le_pathLength (N := N) hst fun τ hτ => hγN τ ⟨hτ.1, hτ.2.trans ht.2⟩
  rw [hγ0] at h1
  refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
  have h2 := pathLength_sq_le_energy hst
  have hE' : energy γ 0 t ≤ energy γ 0 1 := by
    refine intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (Eventually.of_forall fun _ => sq_nonneg _) ?_
    exact hγs.intervalIntegrable_norm_deriv_sq
  have hE0 : 0 ≤ energy γ 0 t :=
    intervalIntegral.integral_nonneg ht.1 fun _ _ => sq_nonneg _
  have hL0 : 0 ≤ pathLength γ 0 t := hst.isAdmissible.pathLength_nonneg
  refine Real.le_sqrt_of_sq_le ?_
  have : pathLength γ 0 t ^ 2 ≤ energy γ 0 t := by
    calc pathLength γ 0 t ^ 2 ≤ (t - 0) * energy γ 0 t := h2
      _ ≤ 1 * energy γ 0 t := by gcongr; linarith [ht.2]
      _ = energy γ 0 t := one_mul _
  linarith

/-! ### Two elementary lemmas -/

omit [FiniteDimensional ℝ V] in
/-- **The triangle inequality along a chain**: `ρ(x₀, x_k) ≤ Σ_{i < k} ρ(xᵢ, xᵢ₊₁)`. -/
theorem riemDist_le_sum_filter {n : ℕ} (x : Fin (n + 1) → V) (hx : ∀ k, x k ∈ N)
    (k : Fin (n + 1)) :
    riemDist (N := N) (x 0) (x k) ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.castSucc < k),
      riemDist (N := N) (x i.castSucc) (x i.succ) := by
  induction k using Fin.induction with
  | zero => simp [riemDist_self (hx 0)]
  | succ j ih =>
    have hset : Finset.univ.filter (fun i : Fin n => i.castSucc < j.succ) =
        insert j (Finset.univ.filter (fun i : Fin n => i.castSucc < j.castSucc)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.lt_def,
        Fin.val_castSucc, Fin.val_succ, Fin.ext_iff]
      omega
    rw [hset, Finset.sum_insert (by simp)]
    calc riemDist (N := N) (x 0) (x j.succ)
        ≤ riemDist (N := N) (x 0) (x j.castSucc) + riemDist (N := N) (x j.castSucc) (x j.succ) :=
          riemDist_triangle _ _ _
      _ ≤ _ := by rw [add_comm]; gcongr

omit [FiniteDimensional ℝ V] in
theorem riemDist_le_sum {n : ℕ} (x : Fin (n + 1) → V) (hx : ∀ k, x k ∈ N) (k : Fin (n + 1)) :
    riemDist (N := N) (x 0) (x k) ≤ ∑ i : Fin n, riemDist (N := N) (x i.castSucc) (x i.succ) :=
  (riemDist_le_sum_filter x hx k).trans (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))

/-- **Additivity of the integral over a subdivision** indexed by `Fin`. -/
theorem sum_integral_fin {f : ℝ → ℝ} : ∀ {n : ℕ} (t : Fin (n + 1) → ℝ),
    (∀ i j, IntervalIntegrable f volume (t i) (t j)) →
    ∑ i : Fin n, ∫ x in t i.castSucc..t i.succ, f x = ∫ x in t 0..t (Fin.last n), f x
  | 0, t, _ => by simp
  | n + 1, t, h => by
    rw [Fin.sum_univ_castSucc]
    have ih := sum_integral_fin (n := n) (fun i => t i.castSucc) (fun i j => h _ _)
    simp only [Fin.succ_castSucc] at ih ⊢
    rw [ih, Fin.castSucc_zero, ← Fin.succ_last]
    exact intervalIntegral.integral_add_adjacent_intervals (h _ _) (h _ _)

/-! ### Milnor's data -/

variable (p q : V) (c : ℝ) (m : ℕ) in
/-- **The data of Milnor's §16, made precise** (p. 89): end points `p, q ∈ N`; an energy bound
`c > 0` such that the ball `S = {x ∈ N : ρ(p, x) ≤ √c}` is compact (Milnor: `M` complete); a number
`δ > 0` (Milnor's `ε`) for which the conclusion of Corollary 10.8 holds on `S` — two points of `S`
at distance `< δ` are joined by a unique geodesic of length `< δ`, which is minimal and depends
smoothly on its end points (`Morse.IsShortJoin`) — and which is at most a normal radius at every
point of `S`; and a subdivision `0 = t₀ < ⋯ < t_{m+1} = 1` with `c (t_{i+1} − tᵢ) < δ²` (Milnor:
`tᵢ − t_{i−1} < ε²/c`). -/
structure BrokenSetup extends Subdivision m where
  mem_p : p ∈ N
  mem_q : q ∈ N
  c_pos : 0 < c
  isCompact_ball : IsCompact (closedRiemBall N p √c)
  /-- Milnor's `ε`. -/
  δ : ℝ
  δ_pos : 0 < δ
  join : ∀ y z : N, (y : V) ∈ closedRiemBall N p √c → (z : V) ∈ closedRiemBall N p √c →
    riemDist (N := N) y z < ENNReal.ofReal δ → IsShortJoin hN δ y z
  normal : ∀ y : N, (y : V) ∈ closedRiemBall N p √c → ∃ ε, δ ≤ ε ∧ IsNormalRadius hN y ε
  fine : ∀ i, c * toSubdivision.len i < δ ^ 2

/-- **"For all sufficiently fine subdivisions"** (Lemma 16.1), made precise: if `S` is compact,
there is `η > 0` (namely `δ²/c`, `δ` from Corollary 10.8 on `S`) such that every subdivision with
all `t_{i+1} − tᵢ < η` is part of a `Morse.BrokenSetup`. -/
theorem exists_brokenSetup {p q : V} (hp : p ∈ N) (hq : q ∈ N) {c : ℝ} (hc : 0 < c)
    (hS : IsCompact (closedRiemBall N p √c)) :
    ∃ η > 0, ∀ {m : ℕ} (s : Subdivision m), (∀ i, s.len i < η) →
      ∃ B : BrokenSetup hN p q c m, B.toSubdivision = s := by
  obtain ⟨δ, hδ, hjoin, hnormal⟩ := corollary_10_8' hN hS (closedRiemBall_subset p √c)
  refine ⟨δ ^ 2 / c, by positivity, fun s hs => ⟨{ s with
    mem_p := hp, mem_q := hq, c_pos := hc, isCompact_ball := hS, δ := δ, δ_pos := hδ,
    join := hjoin, normal := hnormal, fine := fun i => ?_ }, rfl⟩⟩
  have := hs i
  calc c * s.len i < c * (δ ^ 2 / c) := by gcongr
    _ = δ ^ 2 := by field_simp

/-- **Fine subdivisions exist**: for compact `S`, some uniform subdivision carries the data of
§16. -/
theorem exists_brokenSetup_uniform {p q : V} (hp : p ∈ N) (hq : q ∈ N) {c : ℝ} (hc : 0 < c)
    (hS : IsCompact (closedRiemBall N p √c)) : ∃ m, Nonempty (BrokenSetup hN p q c m) := by
  obtain ⟨η, hη, h⟩ := exists_brokenSetup hN hp hq hc hS
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hη
  obtain ⟨B, -⟩ := h (Subdivision.uniform m) fun i => by
    rw [Subdivision.uniform_len]; exact hm
  exact ⟨m, ⟨B⟩⟩

namespace BrokenSetup

variable {hN} {p q : V} {c : ℝ} {m : ℕ} (B : BrokenSetup hN p q c m)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
include B in
theorem p_mem_ball : p ∈ closedRiemBall N p √c :=
  ⟨B.mem_p, by rw [riemDist_self B.mem_p]; exact bot_le⟩

/-! ### Short join vectors -/

open Classical in
/-- **The initial vector of the short geodesic from `x` to `x'`**: the unique `v ∈ T_xN` with
`‖v‖ < δ` and `exp_x v = x'` (`0` if there is none). -/
def joinVec (x x' : V) : V :=
  if h : ∃ v, prj hN x v = v ∧ ‖v‖ < B.δ ∧ exp hN x v = x' then h.choose else 0

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **Corollary 10.8 through `joinVec`**: for `x, x' ∈ S` at distance `< δ`, `joinVec x x'` is
tangent, of norm `ρ(x, x') < δ`, `exp_x (joinVec x x') = x'`, and it is the only such vector. -/
theorem joinVec_spec {x x' : V} (hx : x ∈ closedRiemBall N p √c)
    (hx' : x' ∈ closedRiemBall N p √c) (hxx' : riemDist (N := N) x x' < ENNReal.ofReal B.δ) :
    prj hN x (B.joinVec x x') = B.joinVec x x' ∧ ‖B.joinVec x x'‖ < B.δ ∧
      exp hN x (B.joinVec x x') = x' ∧
      riemDist (N := N) x x' = ENNReal.ofReal ‖B.joinVec x x'‖ ∧
      ∀ w, prj hN x w = w → ‖w‖ < B.δ → exp hN x w = x' → w = B.joinVec x x' := by
  obtain ⟨v, hv, hvδ, hexp, hρ, huniq, -⟩ :=
    B.join ⟨x, hx.1⟩ ⟨x', hx'.1⟩ hx hx' hxx'
  have hvT : prj hN x v = v := (prj_eq_self_iff hN hx.1).2 hv
  have hex : ∃ v, prj hN x v = v ∧ ‖v‖ < B.δ ∧ exp hN x v = x' := ⟨v, hvT, hvδ, hexp⟩
  have hj : B.joinVec x x' = v := by
    rw [joinVec, dif_pos hex]
    obtain ⟨h1, h2, h3⟩ := hex.choose_spec
    exact huniq _ ((prj_eq_self_iff hN hx.1).1 h1) h2 h3
  rw [hj]
  exact ⟨hvT, hvδ, hexp, hρ, fun w hw hwδ hwexp =>
    huniq w ((prj_eq_self_iff hN hx.1).1 hw) hwδ hwexp⟩

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- The short join vector is in the domain of `exp`. -/
theorem mem_expDom_joinVec {x x' : V} (hx : x ∈ closedRiemBall N p √c)
    (hx' : x' ∈ closedRiemBall N p √c) (hxx' : riemDist (N := N) x x' < ENNReal.ofReal B.δ) :
    (x, B.joinVec x x') ∈ expDom hN := by
  obtain ⟨-, -, hexp, hρ, -⟩ := B.joinVec_spec hx hx' hxx'
  by_contra hdom
  have h1 : exp hN x (B.joinVec x x') = x := by
    rw [exp, dif_neg]
    exact hdom
  rw [h1] at hexp
  have h00 : riemDist (N := N) x x' = 0 := by rw [← hexp]; exact riemDist_self hx.1
  rw [h00] at hρ
  have h0 : B.joinVec x x' = 0 := by
    have := (ENNReal.ofReal_eq_zero.1 hρ.symm)
    exact norm_le_zero_iff.1 this
  rw [h0] at hdom
  exact hdom (zero_mem_expDom hx.1)

/-! ### The open set `U` of break points -/

/-- **The energy of the broken geodesic with break points `y`** (formula (∗) of the exposition,
Milnor p. 90): `Σᵢ ρ(xᵢ, xᵢ₊₁)² / (t_{i+1} − tᵢ)`. -/
def energy' (y : Fin m → V) : ℝ :=
  ∑ i, (riemDist (N := N) (vert p q y i.castSucc) (vert p q y i.succ)).toReal ^ 2 / B.len i

/-- **Milnor's open set of break points** (p. 89): the `y ∈ N^m` for which
`Σᵢ ρ(xᵢ, xᵢ₊₁)² / (t_{i+1} − tᵢ) < c` (with all distances finite). -/
def nodes : Set (Fin m → V) :=
  {y | (∀ j, y j ∈ N) ∧
    (∀ i : Fin (m + 1), riemDist (N := N) (vert p q y i.castSucc) (vert p q y i.succ) ≠ ⊤) ∧
    B.energy' y < c}

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
include B in
theorem vert_mem {y : Fin m → V} (hy : ∀ j, y j ∈ N) (k : Fin (m + 2)) : vert p q y k ∈ N := by
  induction k using Fin.cases with
  | zero => exact B.mem_p
  | succ k =>
    induction k using Fin.lastCases with
    | last => rw [Fin.succ_last, vert_last]; exact B.mem_q
    | cast j => rw [vert_inner]; exact hy j

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem energy'_nonneg_terms (y : Fin m → V) (i : Fin (m + 1)) :
    0 ≤ (riemDist (N := N) (vert p q y i.castSucc) (vert p q y i.succ)).toReal ^ 2 / B.len i :=
  div_nonneg (sq_nonneg _) (B.len_pos i).le

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **Consecutive vertices are at distance `< δ`** (from `ρ² < c (t_{i+1} − tᵢ) < δ²`). -/
theorem riemDist_vert_lt {y : Fin m → V} (hy : y ∈ B.nodes) (i : Fin (m + 1)) :
    riemDist (N := N) (vert p q y i.castSucc) (vert p q y i.succ) < ENNReal.ofReal B.δ := by
  obtain ⟨-, hfin, hE⟩ := hy
  set ρ := riemDist (N := N) (vert p q y i.castSucc) (vert p q y i.succ)
  have h1 : ρ.toReal ^ 2 / B.len i < c :=
    lt_of_le_of_lt (Finset.single_le_sum (fun j _ => B.energy'_nonneg_terms y j)
      (Finset.mem_univ i)) hE
  have h2 : ρ.toReal ^ 2 < B.δ ^ 2 := by
    have hl := B.len_pos i
    have := B.fine i
    rw [div_lt_iff₀ hl] at h1
    linarith
  have h3 : ρ.toReal < B.δ := lt_of_pow_lt_pow_left₀ 2 B.δ_pos.le h2
  have hρfin : ρ ≠ ⊤ := hfin i
  rw [← ENNReal.ofReal_toReal hρfin]
  exact (ENNReal.ofReal_lt_ofReal_iff B.δ_pos).2 h3

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **Step 4 of the exposition: the vertices lie in `S`**:
`ρ(p, x_k) ≤ Σ ρ(xᵢ, xᵢ₊₁) ≤ (Σ (t_{i+1} − tᵢ))^{1/2} (Σ ρ²/(t_{i+1} − tᵢ))^{1/2} < √c`. -/
theorem vert_mem_ball {y : Fin m → V} (hy : y ∈ B.nodes) (k : Fin (m + 2)) :
    vert p q y k ∈ closedRiemBall N p √c := by
  refine ⟨B.vert_mem hy.1 k, ?_⟩
  have h1 := riemDist_le_sum (N := N) (vert p q y) (B.vert_mem hy.1) k
  rw [vert_zero] at h1
  refine h1.trans ?_
  rw [← ENNReal.ofReal_toReal (a := ∑ i : Fin (m + 1), _) (by
    rw [ENNReal.sum_ne_top]; exact fun i _ => hy.2.1 i), ENNReal.toReal_sum (fun i _ => hy.2.1 i)]
  refine ENNReal.ofReal_le_ofReal ?_
  -- Cauchy–Schwarz (Sedrakyan's form)
  have hCS := Finset.sq_sum_div_le_sum_sq_div Finset.univ
    (fun i : Fin (m + 1) =>
      (riemDist (N := N) (vert p q y i.castSucc) (vert p q y i.succ)).toReal)
    (g := B.len) fun i _ => B.len_pos i
  rw [B.sum_len, div_one] at hCS
  have hE : B.energy' y < c := hy.2.2
  refine Real.le_sqrt_of_sq_le ?_
  exact hCS.trans (le_of_lt hE)

/-! ### The broken geodesic with given break points -/

/-- The `i`-th segment of the broken geodesic with break points `y`:
`τ ↦ exp_{xᵢ}(((τ − tᵢ)/(t_{i+1} − tᵢ)) vᵢ)`, `vᵢ` the short join vector from `xᵢ` to `xᵢ₊₁`. -/
def segPath (y : Fin m → V) (i : Fin (m + 1)) (τ : ℝ) : V :=
  exp hN (vert p q y i.castSucc)
    (((τ - B.t i.castSucc) / B.len i) • B.joinVec (vert p q y i.castSucc) (vert p q y i.succ))

/-- **The broken geodesic with break points `y`** (Milnor p. 89): on `[tᵢ, t_{i+1}]` the short
geodesic from `xᵢ` to `xᵢ₊₁`, run at constant speed. -/
def path (y : Fin m → V) (τ : ℝ) : V := B.segPath y (B.segOf τ) τ

/-- **The break points** `(γ(t₁), …, γ(t_m))` of a path. -/
def nodeVal (γ : ℝ → V) : Fin m → V := fun j => γ (B.t j.castSucc.succ)

/-- **`γ` is a broken geodesic for the subdivision** (Milnor's `Ω(t₀, …, t_k)`, p. 88): a geodesic
on each `(tᵢ, t_{i+1})`. -/
def IsBroken (γ : ℝ → V) : Prop :=
  ∀ i : Fin (m + 1), IsGeodesicOn hN γ (Ioo (B.t i.castSucc) (B.t i.succ))

section Path

variable {y : Fin m → V} (hy : y ∈ B.nodes)
include hy

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem joinVec_vert (i : Fin (m + 1)) :
    prj hN (vert p q y i.castSucc) (B.joinVec (vert p q y i.castSucc) (vert p q y i.succ)) =
        B.joinVec (vert p q y i.castSucc) (vert p q y i.succ) ∧
      ‖B.joinVec (vert p q y i.castSucc) (vert p q y i.succ)‖ < B.δ ∧
      exp hN (vert p q y i.castSucc) (B.joinVec (vert p q y i.castSucc) (vert p q y i.succ)) =
        vert p q y i.succ ∧
      riemDist (N := N) (vert p q y i.castSucc) (vert p q y i.succ) =
        ENNReal.ofReal ‖B.joinVec (vert p q y i.castSucc) (vert p q y i.succ)‖ :=
  let h := B.joinVec_spec (B.vert_mem_ball hy i.castSucc) (B.vert_mem_ball hy i.succ)
    (B.riemDist_vert_lt hy i)
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem segPath_start (i : Fin (m + 1)) :
    B.segPath y i (B.t i.castSucc) = vert p q y i.castSucc := by
  simp [segPath, exp_zero (B.vert_mem hy.1 _)]

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem segPath_end (i : Fin (m + 1)) : B.segPath y i (B.t i.succ) = vert p q y i.succ := by
  have h1 : (B.t i.succ - B.t i.castSucc) / B.len i = 1 := div_self (B.len_pos i).ne'
  simp only [segPath, h1, one_smul]
  exact (B.joinVec_vert hy i).2.2.1

/-- **Each segment is a geodesic** on an open interval containing `[tᵢ, t_{i+1}]`, with velocity
`vᵢ/(t_{i+1} − tᵢ)` at `tᵢ`. -/
theorem segPath_isGeodesicOn (i : Fin (m + 1)) :
    ∃ η > 0, IsGeodesicOn hN (B.segPath y i) (Ioo (B.t i.castSucc - η) (B.t i.succ + η)) ∧
      HasDerivAt (B.segPath y i)
        ((1 / B.len i) • B.joinVec (vert p q y i.castSucc) (vert p q y i.succ))
        (B.t i.castSucc) := by
  set x := vert p q y i.castSucc
  set v := B.joinVec x (vert p q y i.succ)
  have hxN : x ∈ N := B.vert_mem hy.1 _
  have hvT : prj hN x v = v := (B.joinVec_vert hy i).1
  obtain ⟨γ, hγ⟩ := B.mem_expDom_joinVec (B.vert_mem_ball hy i.castSucc)
    (B.vert_mem_ball hy i.succ) (B.riemDist_vert_lt hy i)
  obtain ⟨δ', hδ', hgeo, -⟩ := hγ.isGeodesicOn_exp_smul
  have hl := B.len_pos i
  set a := 1 / B.len i
  set b := -(B.t i.castSucc / B.len i)
  have haff : ∀ τ, a * τ + b = (τ - B.t i.castSucc) / B.len i := fun τ => by
    simp only [a, b]; field_simp; ring
  have h := hgeo.comp_mul_add a b
  have hEq : EqOn (fun τ => exp hN x ((a * τ + b) • v)) (B.segPath y i) univ := fun τ _ => by
    simp only [segPath, haff]; rfl
  refine ⟨δ' * B.len i, by positivity, (h.mono isOpen_Ioo fun τ hτ => ?_).congr
    (hEq.mono (subset_univ _)), ?_⟩
  · simp only [mem_preimage, mem_Ioo, haff]
    have hτ1 := hτ.1
    have hτ2 := hτ.2
    constructor
    · rw [lt_div_iff₀ hl]; nlinarith
    · rw [div_lt_iff₀ hl]
      have : B.t i.succ = B.t i.castSucc + B.len i := by simp [Subdivision.len]
      nlinarith
  · have hd0 : HasDerivAt (fun s => exp hN x (s • v)) v (a * B.t i.castSucc + b) := by
      rw [haff, sub_self, zero_div]
      exact hasDerivAt_exp_smul_zero ⟨x, hxN⟩ ((prj_eq_self_iff hN hxN).1 hvT)
    have haffd : HasDerivAt (fun τ : ℝ => a * τ + b) a (B.t i.castSucc) := by
      simpa using ((hasDerivAt_id (B.t i.castSucc)).const_mul a).add_const b
    have := hd0.scomp (B.t i.castSucc) haffd
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun τ => ?_)
    exact (hEq (mem_univ τ)).symm

theorem path_eq_segPath (i : Fin (m + 1)) {τ : ℝ}
    (hτ : τ ∈ Icc (B.t i.castSucc) (B.t i.succ)) : B.path y τ = B.segPath y i τ := by
  rcases eq_or_lt_of_le hτ.2 with h | h
  · subst h
    by_cases hi : i = Fin.last m
    · subst hi
      rw [path, B.segOf_of_one_le (by rw [Fin.succ_last, B.t_last])]
    · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 hi
      have hseg : B.segOf (B.t j.castSucc.succ) = j.succ :=
        B.segOf_eq le_rfl (by rw [B.t_lt_iff]; exact Fin.castSucc_lt_succ (i := j.succ))
      rw [path, hseg]
      exact (B.segPath_start hy j.succ).trans (B.segPath_end hy j.castSucc).symm
  · rw [path, B.segOf_eq hτ.1 h]

/-- On every piece free of break points, the broken geodesic is smooth. -/
theorem contDiffOn_path {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hB : ∀ x ∈ B.breaks, x ∉ Ioo a b) : ContDiffOn ℝ ∞ (B.path y) (Icc a b) := by
  obtain ⟨i, hai, hbi⟩ := B.exists_seg_of_piece ha hab hb hB
  obtain ⟨η, hη, hgeo, -⟩ := B.segPath_isGeodesicOn hy i
  refine (hgeo.contDiffOn.mono fun τ hτ => ⟨by linarith [hτ.1], by linarith [hτ.2]⟩).congr
    fun τ hτ => B.path_eq_segPath hy i ⟨hai.trans hτ.1, hτ.2.trans hbi⟩

theorem path_mem (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) : B.path y τ ∈ N := by
  have h := B.mem_Icc_segOf hτ
  obtain ⟨η, hη, hgeo, -⟩ := B.segPath_isGeodesicOn hy (B.segOf τ)
  rw [B.path_eq_segPath hy _ h]
  exact hgeo.mem τ ⟨by linarith [h.1], by linarith [h.2]⟩

/-- **The broken geodesic is a path from `p` to `q`**: `B.path y ∈ Ω(N; p, q)`. -/
theorem path_mem_pathSpace : B.path y ∈ pathSpace N p q := by
  refine ⟨⟨zero_le_one, continuousOn_of_piecewise (B := B.breaks) fun a b ha hab hb hB =>
    (B.contDiffOn_path hy ha hab hb hB).continuousOn, B.breaks, fun a b ha hab hb hB =>
    B.contDiffOn_path hy ha hab hb hB⟩, B.path_mem hy, ?_, ?_⟩
  · have h0 : B.t (0 : Fin (m + 1)).castSucc ≤ B.t (0 : Fin (m + 1)).succ :=
      B.t_le_iff.2 Fin.castSucc_lt_succ.le
    calc B.path y 0 = B.path y (B.t (0 : Fin (m + 1)).castSucc) := by
          rw [Fin.castSucc_zero, B.t_zero]
      _ = vert p q y (0 : Fin (m + 1)).castSucc :=
          (B.path_eq_segPath hy 0 ⟨le_rfl, h0⟩).trans (B.segPath_start hy 0)
      _ = p := by rw [Fin.castSucc_zero, vert_zero]
  · have h1 : B.t (Fin.last m).castSucc ≤ B.t (Fin.last m).succ :=
      B.t_le_iff.2 Fin.castSucc_lt_succ.le
    calc B.path y 1 = B.path y (B.t (Fin.last m).succ) := by rw [Fin.succ_last, B.t_last]
      _ = vert p q y (Fin.last m).succ :=
          (B.path_eq_segPath hy _ ⟨h1, le_rfl⟩).trans (B.segPath_end hy _)
      _ = q := by rw [Fin.succ_last, vert_last]

/-- **The broken geodesic is a broken geodesic**: a geodesic on every `(tᵢ, t_{i+1})`. -/
theorem isBroken_path : B.IsBroken (B.path y) := fun i => by
  obtain ⟨η, hη, hgeo, -⟩ := B.segPath_isGeodesicOn hy i
  exact (hgeo.mono isOpen_Ioo (Ioo_subset_Ioo (by linarith) (by linarith))).congr
    fun τ hτ => (B.path_eq_segPath hy i (Ioo_subset_Icc_self hτ)).symm

/-- **Its break points are `y`**. -/
theorem nodeVal_path : B.nodeVal (B.path y) = y := funext fun j => by
  rw [nodeVal, B.path_eq_segPath hy j.succ (τ := B.t j.castSucc.succ)
    ⟨le_rfl, (B.t_le_iff.2 (Fin.castSucc_lt_succ (i := j.succ)).le)⟩]
  exact (B.segPath_start hy j.succ).trans (vert_inner p q y j)

/-- **The speed of the broken geodesic** on `(tᵢ, t_{i+1})` is `ρ(xᵢ, xᵢ₊₁)/(t_{i+1} − tᵢ)`. -/
theorem norm_deriv_path (i : Fin (m + 1)) {τ : ℝ} (hτ : τ ∈ Ioo (B.t i.castSucc) (B.t i.succ)) :
    ‖deriv (B.path y) τ‖ =
      ‖B.joinVec (vert p q y i.castSucc) (vert p q y i.succ)‖ / B.len i := by
  obtain ⟨η, hη, hgeo, hd⟩ := B.segPath_isGeodesicOn hy i
  have hev : B.path y =ᶠ[𝓝 τ] B.segPath y i :=
    eventually_of_mem (Ioo_mem_nhds hτ.1 hτ.2) fun σ hσ =>
      B.path_eq_segPath hy i (Ioo_subset_Icc_self hσ)
  have hs : τ ∈ Ioo (B.t i.castSucc - η) (B.t i.succ + η) :=
    ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have h0 : B.t i.castSucc ∈ Ioo (B.t i.castSucc - η) (B.t i.succ + η) :=
    ⟨by linarith, by linarith [B.len_pos i, show B.len i = B.t i.succ - B.t i.castSucc from rfl]⟩
  rw [hev.deriv_eq, hgeo.norm_deriv_eq isPreconnected_Ioo hs h0, hd.deriv, norm_smul,
    Real.norm_eq_abs, abs_of_pos (by have := B.len_pos i; positivity)]
  ring

/-- **Formula (∗)** (Milnor p. 90): `E(B.path y) = Σᵢ ρ(xᵢ, xᵢ₊₁)²/(t_{i+1} − tᵢ)`. -/
theorem energy_path : energy (B.path y) 0 1 = B.energy' y := by
  have hps := (B.path_mem_pathSpace hy).1
  have hint : ∀ i j, IntervalIntegrable (fun τ => ‖deriv (B.path y) τ‖ ^ 2) volume
      (B.t i) (B.t j) := by
    have hmem : ∀ i, B.t i ∈ uIcc (0 : ℝ) 1 := fun i => by
      rw [uIcc_of_le zero_le_one]; exact ⟨B.t_nonneg i, B.t_le_one i⟩
    exact fun i j => hps.intervalIntegrable_norm_deriv_sq.mono_set
      (uIcc_subset_uIcc (hmem i) (hmem j))
  have hsum := sum_integral_fin B.t hint
  rw [B.t_zero, B.t_last] at hsum
  rw [energy, ← hsum, energy']
  refine Finset.sum_congr rfl fun i _ => ?_
  have hadm : IsAdmissible (B.path y) (B.t i.castSucc) (B.t i.succ) :=
    (hps.mono (B.t_nonneg _) (B.t_le_iff.2 Fin.castSucc_lt_succ.le) (B.t_le_one _)).isAdmissible
  have h := energy_eq_of_norm_deriv hadm (k := ‖B.joinVec (vert p q y i.castSucc)
    (vert p q y i.succ)‖ / B.len i) fun τ hτ _ => B.norm_deriv_path hy i hτ
  rw [energy] at h
  rw [h, (B.joinVec_vert hy i).2.2.2, ENNReal.toReal_ofReal (norm_nonneg _)]
  have hl := (B.len_pos i).ne'
  change _ * B.len i = _
  field_simp

end Path

end BrokenSetup

end Morse
