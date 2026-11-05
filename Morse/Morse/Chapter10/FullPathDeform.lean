import Morse.Chapter10.FullPathSpace

/-!
Milnor, *Morse Theory*, §17, pp. 93–94, as repaired in Exposition/Chapter10.md, §5 ("A proof that
works", Lemma 17.C): the open sets `Y_k ⊆ Ω*` of paths whose dyadic pieces lie in good balls, and
a deformation of `Y_k` onto broken geodesics.

# Dyadic pieces in good sets, and the deformation onto broken geodesics

## Milnor's text, paraphrased

(p. 94) For `ω ∈ Ω*`, Milnor joins the points `ω(0), ω(A), ω(2A), …, ω(kA), ω(1)` (`A = A(ω)`
continuous in `ω`) by minimal geodesics to get `h(ω) ∈ Ω`, says that `h` is clearly continuous, and
that the arguments of §16 show `h ∘ i ≃ id` and `i ∘ h ≃ id`.  The exposition shows that `h` is not
continuous for `d`, and repairs the proof with fixed dyadic subdivisions and good balls.

## In the embedded setting

* `Morse.JoinSystem N`: **an abstract system of minimal joins**: a join `geo y z u` and a family of
  open good sets in which joins exist, stay (convexity), and depend smoothly on their end points;
  it is provided by the good balls of `Morse/Chapter10/GoodBalls.lean`
  (`Morse/Chapter10/GoodJoin.lean`).
* `Morse.JoinSystem.IsGood J k c`: every dyadic piece `c([j/2^k, (j+1)/2^k])` lies in a good set;
  `Morse.JoinSystem.YSet J k`: the corresponding open subset `Y_k` of `Ω*`
  (`Morse.JoinSystem.isOpen_YSet`, `Morse.JoinSystem.YSet_mono`, and every continuous path lies in
  some `Y_k`: `Morse.JoinSystem.exists_mem_YSet`).
* `Morse.JoinSystem.broken J k c`: the broken geodesic with vertices `c(j/2^k)`;
  `Morse.JoinSystem.interp J k c u s`: the point at time `u` on the minimal geodesic from `c(s)` to
  `broken J k c s`, a deformation from `c` (`u = 0`) to its broken geodesic (`u = 1`) which stays in
  the good sets of the pieces (`Morse.JoinSystem.IsGood.interp`, by convexity).
* `Morse.JoinSystem.interpStar`: the deformation as a continuous map `Y_k × [0, 1] → Y_k` for the
  uniform topology (`Morse.JoinSystem.continuous_interp_star`).

## What Milnor leaves implicit

* **Convexity.**  Joining points of a piece by minimal geodesics keeps the deformed path in the
  same good set only if minimal geodesics between points of a good set stay in it; this is the
  convexity of small balls (J. H. C. Whitehead), proved in `Morse/Chapter10/GoodBalls.lean`.
* **The deformation.**  Instead of Milnor's (and the exposition's) `r_u`, which moves a break point
  along the path, the deformation here moves every point of the path along the minimal geodesic to
  the corresponding point of the broken geodesic; its continuity for Milnor's metric then follows
  from smoothness of the joins and the `L²` control of velocities
  (`Morse.PathSp.tendsto_integral_norm_deriv_sub_sq`).
-/

open Set Filter Topology Function Module Metric MeasureTheory
open scoped ContDiff Manifold RealInnerProductSpace ENNReal Interval NNReal

noncomputable section

namespace Morse

theorem dseg_dy {k j : ℕ} (hj : j < 2 ^ k) : dseg k (dy k j) = j := by
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  unfold dseg dy
  rw [div_mul_cancel₀ _ h2.ne', Nat.floor_natCast]
  omega

theorem dseg_eq_or {k j : ℕ} (hj : j < 2 ^ k) {s : ℝ} (hs : s ∈ Icc (dy k j) (dy k (j + 1))) :
    dseg k s = j ∨ (s = dy k (j + 1) ∧ dseg k s = j + 1) := by
  have hs01 : s ∈ Icc (0 : ℝ) 1 :=
    ⟨(dy_nonneg k j).trans hs.1, hs.2.trans (dy_le_one (by omega))⟩
  have hm := mem_Icc_dseg (k := k) hs01
  have hlt := dseg_lt k s
  set d := dseg k s with hd
  rcases lt_trichotomy d j with h | h | h
  · -- `d < j`: then `s = dy k j = dy k (d + 1)`, so `d + 1 = j` and `dseg k s = j`
    exfalso
    have h1 : dy k (d + 1) ≤ dy k j := dy_mono k (by omega)
    have h2 : s = dy k j := le_antisymm (hm.2.trans h1) hs.1
    have := dseg_dy hj
    rw [← h2] at this
    omega
  · exact Or.inl h
  · rcases eq_or_lt_of_le (show j + 1 ≤ d by omega) with h' | h'
    · right
      refine ⟨le_antisymm hs.2 ?_, h'.symm⟩
      rw [h']
      exact hm.1
    · exfalso
      have h1 : dy k (j + 2) ≤ dy k d := dy_mono k (by omega)
      have h2 := dy_lt_succ k (j + 1)
      linarith [hm.1, hs.2]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

variable (N : Set V) in
/-- **A system of minimal joins with good sets** (Lemma 17.B of the exposition, abstracted): a
join `geo y z u` (the minimal geodesic from `y` to `z` at time `u`), and a family of open "good"
sets in which joins exist, stay, and depend smoothly on their end points. -/
structure JoinSystem where
  geo : V → V → ℝ → V
  good : Set (Set V)
  isOpen : ∀ O ∈ good, IsOpen O
  convex : ∀ O ∈ good, ∀ y ∈ N ∩ O, ∀ z ∈ N ∩ O, ∀ u ∈ Icc (0 : ℝ) 1, geo y z u ∈ N ∩ O
  geo_zero : ∀ y ∈ N, ∀ z, geo y z 0 = y
  geo_one : ∀ O ∈ good, ∀ y ∈ N ∩ O, ∀ z ∈ N ∩ O, geo y z 1 = z
  geo_self : ∀ y ∈ N, ∀ u, geo y y u = y
  smooth : ∀ O ∈ good, ∃ U : Set (V × V), IsOpen U ∧ (N ∩ O) ×ˢ (N ∩ O) ⊆ U ∧
    ∃ ε > 0, ∃ Φ : (V × V) × ℝ → V, ContDiffOn ℝ ∞ Φ (U ×ˢ Ioo (-ε) (1 + ε)) ∧
      ∀ y ∈ N ∩ O, ∀ z ∈ N ∩ O, ∀ u ∈ Ioo (-ε) (1 + ε), Φ ((y, z), u) = geo y z u
  lebesgue : ∀ K : Set V, IsCompact K → K ⊆ N → ∃ ε > 0, ∀ x ∈ K, ∃ O ∈ good, ball x ε ⊆ O

namespace JoinSystem

variable {N : Set V} (J : JoinSystem N)

/-- **`c` is good at level `k`** (the sets `Y_k` of the exposition): each dyadic piece
`c([j/2^k, (j+1)/2^k])` lies in a good set. -/
def IsGood (k : ℕ) (c : ℝ → V) : Prop :=
  ∀ j < 2 ^ k, ∃ O ∈ J.good, ∀ s ∈ Icc (dy k j) (dy k (j + 1)), c s ∈ N ∩ O

/-- **The dyadic broken geodesic** of `c` at level `k`: on `[j/2^k, (j+1)/2^k]` the join of
`c(j/2^k)` and `c((j+1)/2^k)`. -/
def broken (k : ℕ) (c : ℝ → V) (s : ℝ) : V :=
  J.geo (c (dy k (dseg k s))) (c (dy k (dseg k s + 1))) (s * 2 ^ k - dseg k s)

/-- **The deformation**: `c(s)` joined to `broken k c s` along the minimal geodesic, at time
`u`. -/
def interp (k : ℕ) (c : ℝ → V) (u s : ℝ) : V := J.geo (c s) (J.broken k c s) u

variable {J} {k : ℕ} {c : ℝ → V}

theorem IsGood.mem (hc : J.IsGood k c) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : c s ∈ N := by
  obtain ⟨O, -, hO⟩ := hc (dseg k s) (dseg_lt k s)
  exact (hO s (mem_Icc_dseg hs)).1

theorem dy_mem_Icc {j : ℕ} (hj : j ≤ 2 ^ k) : dy k j ∈ Icc (0 : ℝ) 1 :=
  ⟨dy_nonneg k j, dy_le_one hj⟩

/-- On the `j`-th piece the broken geodesic is the join of the end points of the piece. -/
theorem IsGood.broken_eq (hc : J.IsGood k c) {j : ℕ} (hj : j < 2 ^ k) {s : ℝ}
    (hs : s ∈ Icc (dy k j) (dy k (j + 1))) :
    J.broken k c s = J.geo (c (dy k j)) (c (dy k (j + 1))) (s * 2 ^ k - j) := by
  rcases dseg_eq_or hj hs with h | ⟨hs', h⟩
  · rw [broken, h]
  · obtain ⟨O, hO, hOc⟩ := hc j hj
    have hy := hOc _ ⟨le_rfl, (dy_lt_succ k j).le⟩
    have hz := hOc _ ⟨(dy_lt_succ k j).le, le_rfl⟩
    have h2k : (0 : ℝ) < 2 ^ k := by positivity
    have h1 : s * 2 ^ k - (j : ℝ) = 1 := by
      rw [hs', dy]
      field_simp
      push_cast
      ring
    have h2 : s * 2 ^ k - ((j + 1 : ℕ) : ℝ) = 0 := by
      rw [hs', dy]
      field_simp
      ring
    rw [h1, J.geo_one O hO _ hy _ hz, broken, h, h2,
      J.geo_zero _ (hc.mem (dy_mem_Icc (by omega)))]

theorem mem_piece_of_mem_Icc {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    s ∈ Icc (dy k (dseg k s)) (dy k (dseg k s + 1)) := mem_Icc_dseg hs

theorem param_mem_Icc {j : ℕ} {s : ℝ} (hs : s ∈ Icc (dy k j) (dy k (j + 1))) :
    s * 2 ^ k - j ∈ Icc (0 : ℝ) 1 := by
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have h1 := hs.1
  have h2 := hs.2
  simp only [dy] at h1 h2
  rw [div_le_iff₀ h2k] at h1
  rw [le_div_iff₀ h2k] at h2
  push_cast at h2
  constructor <;> linarith

/-- The broken geodesic stays in the good set of each piece. -/
theorem broken_mem_of (hc : J.IsGood k c) {j : ℕ} (hj : j < 2 ^ k) {O : Set V} (hO : O ∈ J.good)
    (hOc : ∀ s ∈ Icc (dy k j) (dy k (j + 1)), c s ∈ N ∩ O) {s : ℝ}
    (hs : s ∈ Icc (dy k j) (dy k (j + 1))) : J.broken k c s ∈ N ∩ O := by
  rw [hc.broken_eq hj hs]
  exact J.convex O hO _ (hOc _ ⟨le_rfl, (dy_lt_succ k j).le⟩) _
    (hOc _ ⟨(dy_lt_succ k j).le, le_rfl⟩) _ (param_mem_Icc hs)

/-- The deformation stays in the good set of each piece. -/
theorem interp_mem_of (hc : J.IsGood k c) {j : ℕ} (hj : j < 2 ^ k) {O : Set V} (hO : O ∈ J.good)
    (hOc : ∀ s ∈ Icc (dy k j) (dy k (j + 1)), c s ∈ N ∩ O) {s : ℝ}
    (hs : s ∈ Icc (dy k j) (dy k (j + 1))) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    J.interp k c u s ∈ N ∩ O :=
  J.convex O hO _ (hOc s hs) _ (broken_mem_of hc hj hO hOc hs) u hu

theorem IsGood.broken (hc : J.IsGood k c) : J.IsGood k (J.broken k c) := fun j hj => by
  obtain ⟨O, hO, hOc⟩ := hc j hj
  exact ⟨O, hO, fun s hs => broken_mem_of hc hj hO hOc hs⟩

theorem IsGood.interp (hc : J.IsGood k c) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    J.IsGood k (J.interp k c u) := fun j hj => by
  obtain ⟨O, hO, hOc⟩ := hc j hj
  exact ⟨O, hO, fun s hs => interp_mem_of hc hj hO hOc hs hu⟩

theorem interp_zero (hc : J.IsGood k c) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    J.interp k c 0 s = c s :=
  J.geo_zero _ (hc.mem hs) _

theorem interp_one (hc : J.IsGood k c) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    J.interp k c 1 s = J.broken k c s := by
  obtain ⟨O, hO, hOc⟩ := hc (dseg k s) (dseg_lt k s)
  exact J.geo_one O hO _ (hOc s (mem_Icc_dseg hs)) _
    (broken_mem_of hc (dseg_lt k s) hO hOc (mem_Icc_dseg hs))

/-- The broken geodesic passes through the dyadic points of `c`. -/
theorem broken_dy (hc : J.IsGood k c) {j : ℕ} (hj : j ≤ 2 ^ k) :
    J.broken k c (dy k j) = c (dy k j) := by
  rcases lt_or_eq_of_le hj with hj | rfl
  · rw [hc.broken_eq hj ⟨le_rfl, (dy_lt_succ k j).le⟩]
    have : dy k j * 2 ^ k - (j : ℝ) = 0 := by
      simp only [dy]
      field_simp
      ring
    rw [this, J.geo_zero _ (hc.mem (dy_mem_Icc hj.le))]
  · have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hj' : 2 ^ k - 1 < 2 ^ k := by omega
    have hmem : dy k (2 ^ k) ∈ Icc (dy k (2 ^ k - 1)) (dy k (2 ^ k - 1 + 1)) := by
      rw [Nat.sub_add_cancel h1]
      exact ⟨(dy_mono k (by omega)), le_rfl⟩
    rw [hc.broken_eq hj' hmem]
    obtain ⟨O, hO, hOc⟩ := hc _ hj'
    have hpar : dy k (2 ^ k) * 2 ^ k - ((2 ^ k - 1 : ℕ) : ℝ) = 1 := by
      rw [dy_two_pow, Nat.cast_sub h1]
      push_cast
      ring
    rw [hpar, J.geo_one O hO _ (hOc _ ⟨le_rfl, (dy_lt_succ k _).le⟩) _ (hOc _ ⟨(dy_lt_succ k _).le,
      le_rfl⟩), Nat.sub_add_cancel h1]

theorem broken_zero (hc : J.IsGood k c) : J.broken k c 0 = c 0 := by
  have := broken_dy hc (j := 0) (Nat.zero_le _)
  rwa [dy_zero] at this

theorem broken_one (hc : J.IsGood k c) : J.broken k c 1 = c 1 := by
  have := broken_dy hc (j := 2 ^ k) le_rfl
  rwa [dy_two_pow] at this

theorem interp_zero_right (hc : J.IsGood k c) (u : ℝ) : J.interp k c u 0 = c 0 := by
  rw [interp, broken_zero hc, J.geo_self _ (hc.mem ⟨le_rfl, zero_le_one⟩)]

theorem interp_one_right (hc : J.IsGood k c) (u : ℝ) : J.interp k c u 1 = c 1 := by
  rw [interp, broken_one hc, J.geo_self _ (hc.mem ⟨zero_le_one, le_rfl⟩)]

/-- `IsGood`, `broken` and `interp` only see the values on `[0, 1]`. -/
theorem isGood_congr {c' : ℝ → V} (h : EqOn c c' (Icc 0 1)) : J.IsGood k c ↔ J.IsGood k c' := by
  constructor <;> intro hc j hj <;> obtain ⟨O, hO, hOc⟩ := hc j hj <;>
    refine ⟨O, hO, fun s hs => ?_⟩
  · have hs01 : s ∈ Icc (0 : ℝ) 1 :=
      ⟨(dy_nonneg k j).trans hs.1, hs.2.trans (dy_le_one (by omega))⟩
    rw [← h hs01]
    exact hOc s hs
  · have hs01 : s ∈ Icc (0 : ℝ) 1 :=
      ⟨(dy_nonneg k j).trans hs.1, hs.2.trans (dy_le_one (by omega))⟩
    rw [h hs01]
    exact hOc s hs

theorem broken_congr {c' : ℝ → V} (h : EqOn c c' (Icc 0 1)) {s : ℝ} :
    J.broken k c s = J.broken k c' s := by
  rw [broken, broken, h (dy_mem_Icc (dseg_lt k s).le), h (dy_mem_Icc (dseg_lt k s))]

theorem interp_congr {c' : ℝ → V} (h : EqOn c c' (Icc 0 1)) {u s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : J.interp k c u s = J.interp k c' u s := by
  rw [interp, interp, h hs, broken_congr h]

theorem IsGood.mono (hc : J.IsGood k c) : J.IsGood (k + 1) c := fun j hj => by
  obtain ⟨O, hO, hOc⟩ := hc (j / 2) (by rw [pow_succ] at hj; omega)
  exact ⟨O, hO, fun s hs => hOc s (Icc_dy_succ_subset k j hs)⟩

/-! ### The sets `Y_k ⊆ Ω*` -/

section Star

open scoped unitInterval

variable {p q : V}

/-- A path `γ : [0, 1] → V`, extended to `ℝ` by constants. -/
abbrev ext (γ : PathC N p q) : ℝ → V := IccExtend zero_le_one (γ : C(I, V))

omit [InnerProductSpace ℝ V] in
theorem ext_of_mem (γ : PathC N p q) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ext γ s = (γ : C(I, V)) ⟨s, hs⟩ := IccExtend_of_mem _ _ hs

omit [InnerProductSpace ℝ V] in
theorem ext_mem (γ : PathC N p q) (s : ℝ) : ext γ s ∈ N := γ.2.1 _

variable (J) in
/-- **The sets `Y_k`** (Lemma 17.C of the exposition): the continuous paths whose dyadic pieces of
level `k` lie in good sets. -/
def YSet (k : ℕ) : Set (PathC N p q) := {γ | J.IsGood k (ext γ)}

/-- The `j`-th dyadic piece of `[0, 1]`, as a compact subset of `I`. -/
def piece (k j : ℕ) : Set I := {t | (t : ℝ) ∈ Icc (dy k j) (dy k (j + 1))}

theorem isCompact_piece (k j : ℕ) : IsCompact (piece k j) :=
  (isClosed_Icc.preimage continuous_subtype_val).isCompact

theorem mem_YSet_iff {γ : PathC N p q} : γ ∈ J.YSet k ↔
    ∀ j < 2 ^ k, ∃ O ∈ J.good, MapsTo (γ : C(I, V)) (piece k j) O := by
  constructor
  · intro h j hj
    obtain ⟨O, hO, hOγ⟩ := h j hj
    refine ⟨O, hO, fun t ht => ?_⟩
    have := (hOγ t ht).2
    rwa [ext_of_mem γ t.2] at this
  · intro h j hj
    obtain ⟨O, hO, hOγ⟩ := h j hj
    refine ⟨O, hO, fun s hs => ⟨ext_mem γ s, ?_⟩⟩
    have hs01 : s ∈ Icc (0 : ℝ) 1 :=
      ⟨(dy_nonneg k j).trans hs.1, hs.2.trans (dy_le_one (by omega))⟩
    rw [ext_of_mem γ hs01]
    exact hOγ (show (⟨s, hs01⟩ : I) ∈ piece k j from hs)

/-- `Y_k` is open in `Ω*`. -/
theorem isOpen_YSet (k : ℕ) : IsOpen (J.YSet k (p := p) (q := q)) := by
  rw [isOpen_iff_mem_nhds]
  intro γ hγ
  rw [mem_YSet_iff] at hγ
  choose! O hO hOγ using hγ
  have hev : ∀ j < 2 ^ k, ∀ᶠ γ' in 𝓝 γ, MapsTo ((γ' : PathC N p q) : C(I, V)) (piece k j) (O j) :=
    fun j hj => (continuous_subtype_val.tendsto γ).eventually
      (ContinuousMap.eventually_mapsTo (isCompact_piece k j) (J.isOpen _ (hO j hj)) (hOγ j hj))
  have hall : ∀ᶠ γ' in 𝓝 γ, ∀ j ∈ Finset.range (2 ^ k),
      MapsTo ((γ' : PathC N p q) : C(I, V)) (piece k j) (O j) :=
    (Finset.eventually_all _).2 fun j hj => hev j (Finset.mem_range.1 hj)
  filter_upwards [hall] with γ' hγ'
  rw [mem_YSet_iff]
  exact fun j hj => ⟨O j, hO j hj, hγ' j (Finset.mem_range.2 hj)⟩

theorem YSet_mono : Monotone (J.YSet (p := p) (q := q)) :=
  monotone_nat_of_le_succ fun _ _ hγ => IsGood.mono hγ

/-- **Every continuous path lies in some `Y_k`** (Lemma 17.C (i) of the exposition: a Lebesgue
number for the cover of `γ([0, 1])` by good sets, and uniform continuity). -/
theorem exists_mem_YSet (γ : PathC N p q) : ∃ k, γ ∈ J.YSet k := by
  have hK : IsCompact (range (γ : C(I, V))) := isCompact_range (γ : C(I, V)).continuous
  obtain ⟨ε, hε, hleb⟩ := J.lebesgue _ hK (range_subset_iff.2 fun t => γ.2.1 t)
  have huc := CompactSpace.uniformContinuous_of_continuous (γ : C(I, V)).continuous
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuous_iff.1 huc ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨k, mem_YSet_iff.2 fun j hj => ?_⟩
  have hj01 : dy k j ∈ Icc (0 : ℝ) 1 := dy_mem_Icc hj.le
  obtain ⟨O, hO, hball⟩ := hleb _ ⟨⟨dy k j, hj01⟩, rfl⟩
  refine ⟨O, hO, fun t ht => hball ?_⟩
  rw [mem_ball]
  refine hδε ?_
  rw [Subtype.dist_eq, Real.dist_eq]
  have h1 : (t : ℝ) - dy k j ≤ 1 / 2 ^ k := by
    have := ht.2
    rw [← dy_succ_sub k j]
    linarith
  have h2 : (1 : ℝ) / 2 ^ k = (1 / 2) ^ k := by rw [one_div_pow]
  rw [abs_of_nonneg (by linarith [ht.1])]
  linarith

omit [InnerProductSpace ℝ V] in
theorem continuous_ext : Continuous fun x : PathC N p q × ℝ => ext x.1 x.2 :=
  continuous_eval.comp ((continuous_subtype_val.comp continuous_fst).prodMk
    ((continuous_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one)).comp continuous_snd))

omit [InnerProductSpace ℝ V] in
theorem continuous_ext_comp {X : Type*} [TopologicalSpace X] {f : X → PathC N p q} {g : X → ℝ}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => ext (f x) (g x) :=
  continuous_ext.comp (hf.prodMk hg)

/-- **The deformation of `Y_k` is continuous** (for the uniform topology): `(γ, u, s) ↦ H(γ, u)(s)`
on `Y_k × [0, 1] × [0, 1]`. -/
theorem continuous_interp_star (k : ℕ) :
    Continuous fun x : (↥(J.YSet k (p := p) (q := q)) × I) × I =>
      J.interp k (ext x.1.1.1) x.1.2 x.2 := by
  set f : Fin (2 ^ k) → Set ((↥(J.YSet k (p := p) (q := q)) × I) × I) :=
    fun j => {x | (x.2 : ℝ) ∈ Icc (dy k j) (dy k (j + 1))} with hf
  refine LocallyFinite.continuous (f := f) (locallyFinite_of_finite _) ?_ (fun j => ?_)
    (fun j => ?_)
  · refine eq_univ_of_forall fun x => mem_iUnion.2 ⟨⟨dseg k x.2, dseg_lt k _⟩, ?_⟩
    exact mem_Icc_dseg x.2.2
  · exact isClosed_Icc.preimage (continuous_subtype_val.comp continuous_snd)
  · intro x₀ hx₀
    obtain ⟨O, hO, hOγ⟩ := x₀.1.1.2 j j.2
    obtain ⟨U, hU, hNU, ε, hε, Φ, hΦ, hΦeq⟩ := J.smooth O hO
    -- near `x₀`, the `j`-th piece of `γ` stays in `O`
    have hmaps : MapsTo ((x₀.1.1 : PathC N p q) : C(I, V)) (piece k j) O := by
      intro t ht
      have := (hOγ t ht).2
      rwa [ext_of_mem _ t.2] at this
    have hev : ∀ᶠ x in 𝓝 x₀, MapsTo ((x.1.1 : PathC N p q) : C(I, V)) (piece k j) O :=
      ((continuous_subtype_val.comp (continuous_subtype_val.comp
        (continuous_fst.comp continuous_fst))).tendsto x₀).eventually
        (ContinuousMap.eventually_mapsTo (isCompact_piece k j) (J.isOpen O hO) hmaps)
    -- the formula through `Φ` on the piece
    set G : (↥(J.YSet k (p := p) (q := q)) × I) × I → V := fun x =>
      Φ ((ext x.1.1.1 x.2, Φ ((ext x.1.1.1 (dy k j), ext x.1.1.1 (dy k (j + 1))),
        (x.2 : ℝ) * 2 ^ k - j)), (x.1.2 : ℝ)) with hG
    have hmemO : ∀ x : (↥(J.YSet k (p := p) (q := q)) × I) × I,
        MapsTo ((x.1.1 : PathC N p q) : C(I, V)) (piece k j) O → ∀ s ∈ Icc (dy k j) (dy k (j + 1)),
          ext x.1.1.1 s ∈ N ∩ O := by
      intro x hx s hs
      have hs01 : s ∈ Icc (0 : ℝ) 1 :=
        ⟨(dy_nonneg k j).trans hs.1, hs.2.trans (dy_le_one (by omega))⟩
      refine ⟨ext_mem _ s, ?_⟩
      rw [ext_of_mem _ hs01]
      exact hx (show (⟨s, hs01⟩ : I) ∈ piece k j from hs)
    have hIoo : ∀ u ∈ Icc (0 : ℝ) 1, u ∈ Ioo (-ε) (1 + ε) := fun u hu =>
      ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have heq : ∀ x ∈ f j, MapsTo ((x.1.1 : PathC N p q) : C(I, V)) (piece k j) O →
        J.interp k (ext x.1.1.1) x.1.2 x.2 = G x := by
      intro x hx hxO
      have hgood : J.IsGood k (ext x.1.1.1) := x.1.1.2
      have hyj := hmemO x hxO _ ⟨le_rfl, (dy_lt_succ k j).le⟩
      have hzj := hmemO x hxO _ ⟨(dy_lt_succ k j).le, le_rfl⟩
      have hpar := param_mem_Icc hx
      have hb : J.broken k (ext x.1.1.1) x.2 = Φ ((ext x.1.1.1 (dy k j),
          ext x.1.1.1 (dy k (j + 1))), (x.2 : ℝ) * 2 ^ k - j) := by
        rw [hgood.broken_eq j.2 hx, hΦeq _ hyj _ hzj _ (hIoo _ hpar)]
      have hbO : J.broken k (ext x.1.1.1) x.2 ∈ N ∩ O :=
        broken_mem_of hgood j.2 hO (hmemO x hxO) hx
      rw [interp, ← hΦeq _ (hmemO x hxO _ hx) _ hbO _ (hIoo _ x.1.2.2), hb]
    refine (ContinuousWithinAt.congr_of_eventuallyEq (f := G) ?_ ?_ (heq x₀ hx₀ hmaps))
    · -- continuity of the formula
      have hc1 : Continuous fun x : (↥(J.YSet k (p := p) (q := q)) × I) × I =>
          ((ext x.1.1.1 (dy k j), ext x.1.1.1 (dy k (j + 1))), (x.2 : ℝ) * 2 ^ k - j) := by
        refine ((continuous_ext_comp (continuous_subtype_val.comp (continuous_fst.comp
          continuous_fst)) continuous_const).prodMk (continuous_ext_comp
            (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))
            continuous_const)).prodMk ?_
        exact ((continuous_subtype_val.comp continuous_snd).mul continuous_const).sub
          continuous_const
      have hin1 : ∀ x ∈ f j ∩ {x | MapsTo ((x.1.1 : PathC N p q) : C(I, V)) (piece k j) O},
          ((ext x.1.1.1 (dy k j), ext x.1.1.1 (dy k (j + 1))), (x.2 : ℝ) * 2 ^ k - j) ∈
            U ×ˢ Ioo (-ε) (1 + ε) := fun x hx =>
        ⟨hNU ⟨hmemO x hx.2 _ ⟨le_rfl, (dy_lt_succ k j).le⟩,
          hmemO x hx.2 _ ⟨(dy_lt_succ k j).le, le_rfl⟩⟩, hIoo _ (param_mem_Icc hx.1)⟩
      have hc2 := hΦ.continuousOn.comp hc1.continuousOn hin1
      have hc3 : ContinuousOn (fun x : (↥(J.YSet k (p := p) (q := q)) × I) × I =>
          ((ext x.1.1.1 x.2, Φ ((ext x.1.1.1 (dy k j), ext x.1.1.1 (dy k (j + 1))),
            (x.2 : ℝ) * 2 ^ k - j)), (x.1.2 : ℝ)))
          (f j ∩ {x | MapsTo ((x.1.1 : PathC N p q) : C(I, V)) (piece k j) O}) :=
        (((continuous_ext_comp (continuous_subtype_val.comp (continuous_fst.comp
          continuous_fst)) (continuous_subtype_val.comp continuous_snd)).continuousOn.prodMk
          hc2).prodMk (continuous_subtype_val.comp (continuous_snd.comp
            continuous_fst)).continuousOn)
      have hin2 : ∀ x ∈ f j ∩ {x | MapsTo ((x.1.1 : PathC N p q) : C(I, V)) (piece k j) O},
          ((ext x.1.1.1 x.2, Φ ((ext x.1.1.1 (dy k j), ext x.1.1.1 (dy k (j + 1))),
            (x.2 : ℝ) * 2 ^ k - j)), (x.1.2 : ℝ)) ∈ U ×ˢ Ioo (-ε) (1 + ε) := by
        intro x hx
        have hgood : J.IsGood k (ext x.1.1.1) := x.1.1.2
        have hyj := hmemO x hx.2 _ ⟨le_rfl, (dy_lt_succ k j).le⟩
        have hzj := hmemO x hx.2 _ ⟨(dy_lt_succ k j).le, le_rfl⟩
        have hb : Φ ((ext x.1.1.1 (dy k j), ext x.1.1.1 (dy k (j + 1))),
            (x.2 : ℝ) * 2 ^ k - j) = J.broken k (ext x.1.1.1) x.2 := by
          rw [hgood.broken_eq j.2 hx.1, hΦeq _ hyj _ hzj _ (hIoo _ (param_mem_Icc hx.1))]
        rw [hb]
        exact ⟨hNU ⟨hmemO x hx.2 _ hx.1, broken_mem_of hgood j.2 hO (hmemO x hx.2) hx.1⟩,
          hIoo _ x.1.2.2⟩
      have hc4 := hΦ.continuousOn.comp hc3 hin2
      have := hc4 x₀ ⟨hx₀, hmaps⟩
      exact this.mono_of_mem_nhdsWithin (inter_mem_nhdsWithin _ hev)
    · filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with x hx hxj
      exact heq x hxj hx

theorem ext_congr_interp {k : ℕ} (γ : ↥(J.YSet k (p := p) (q := q))) (u : I) :
    ∀ t : I, J.interp k (ext γ.1) u t ∈ N := fun t => by
  have hgood : J.IsGood k (ext γ.1) := γ.2
  obtain ⟨O, hO, hOc⟩ := hgood (dseg k t) (dseg_lt k t)
  exact (interp_mem_of hgood (dseg_lt k t) hO hOc (mem_Icc_dseg t.2) u.2).1

variable (J) in
/-- **The deformation `H` of `Y_k`** (the exposition's `D`, here by interpolation along minimal
geodesics): `H(γ, u)(s)` is the point at time `u` on the minimal geodesic from `γ(s)` to the
broken geodesic `b_k(γ)(s)`. -/
def interpStar (k : ℕ) : C(↥(J.YSet k (p := p) (q := q)) × I, ↥(J.YSet k (p := p) (q := q))) where
  toFun x := ⟨⟨(ContinuousMap.curry ⟨_, J.continuous_interp_star k⟩ x),
    fun t => ext_congr_interp x.1 x.2 t, by
      change J.interp k (ext x.1.1) x.2 ((0 : I) : ℝ) = p
      rw [show ((0 : I) : ℝ) = 0 from rfl, interp_zero_right x.1.2,
        ext_of_mem _ ⟨le_rfl, zero_le_one⟩]
      exact x.1.1.2.2.1, by
      change J.interp k (ext x.1.1) x.2 ((1 : I) : ℝ) = q
      rw [show ((1 : I) : ℝ) = 1 from rfl, interp_one_right x.1.2,
        ext_of_mem _ ⟨zero_le_one, le_rfl⟩]
      exact x.1.1.2.2.2⟩, by
    change J.IsGood k (ext _)
    have hgood : J.IsGood k (ext x.1.1) := x.1.2
    refine (isGood_congr fun s hs => ?_).1 (hgood.interp x.2.2)
    rw [ext_of_mem _ hs]
    rfl⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact (ContinuousMap.curry ⟨_, J.continuous_interp_star k⟩).continuous

theorem interpStar_apply {k : ℕ} (x : ↥(J.YSet k (p := p) (q := q)) × I) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : ext (J.interpStar k x).1 s = J.interp k (ext x.1.1) x.2 s := by
  rw [ext_of_mem _ hs]
  rfl

theorem interpStar_zero {k : ℕ} (γ : ↥(J.YSet k (p := p) (q := q))) :
    J.interpStar k (γ, 0) = γ := by
  have hgood : J.IsGood k (ext γ.1) := γ.2
  refine Subtype.ext (Subtype.ext (ContinuousMap.ext fun t => ?_))
  change J.interp k (ext γ.1) ((0 : I) : ℝ) t = _
  rw [show ((0 : I) : ℝ) = 0 from rfl, interp_zero hgood t.2, ext_of_mem _ t.2]

end Star

end JoinSystem

end Morse
