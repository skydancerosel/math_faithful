import Morse.Chapter10.BrokenPaths

/-!
Milnor, *Morse Theory*, §16, pp. 89–91: the manifold of broken geodesics, its energy function
`E'`, and the compactness of its sublevel sets (Theorem 16.2, first assertion, and the compactness
of `B^a`), for a submanifold `N ⊆ ℝᴷ` with the induced metric.

# The energy on the manifold of broken geodesics

## Milnor's text, paraphrased

(p. 89) The correspondence `ω ↦ (ω(t₁), …, ω(t_{k−1}))` is a homeomorphism of
`B = Int Ω(t₀, …, t_k)^c` onto an open subset of `M × ⋯ × M`; "taking over the differentiable
structure from this product", `B` is a smooth manifold.  `E' : B → ℝ` is the restriction of `E`.

**Theorem 16.2** (p. 90, first assertions).  `E'` is smooth.  For each `a < c` the set
`B^a = (E')⁻¹[0, a]` is compact.

*Proof* (pp. 90–91).  `E'(ω) = Σ ρ(ω(t_{i−1}), ω(t_i))²/(t_i − t_{i−1})` depends smoothly on the
break points.  `B^a` is homeomorphic to the set of `(p₁, …, p_{k−1}) ∈ S × ⋯ × S` with
`Σ ρ(p_{i−1}, p_i)²/(t_i − t_{i−1}) ≤ a`, a closed subset of a compact set.

## In the embedded setting

For `B : Morse.BrokenSetup hN p q c m` (the manifold of broken geodesics is represented by the set
`U = B.nodes ⊆ N^m` of break points, Lemma 16.1, `Morse/Chapter10/BrokenPaths.lean`):

* `Morse.BrokenSetup.exists_isOpen_nodes`: `U = N^m ∩ O` for an open `O ⊆ V^m` — **`U` is an
  open subset of `N^m`**, hence a slice submanifold of `V^m` (`Morse.isSliceSubmanifold_pi_inter`),
  whose tangent space at `y` is `∏_j T_{y_j}N` (`Morse.tangentSubspace_pi_inter`).
* `Morse.BrokenSetup.exists_smooth_energy'`: **`E'` is smooth** in Milnor's sense: near every
  point of `U` it is the restriction of a smooth function on an open set of `V^m`, namely
  `Σ ‖Gᵢ(xᵢ, xᵢ₊₁)‖²/(t_{i+1} − tᵢ)`, `Gᵢ` the smooth local representative of the short join
  vector (Corollary 10.8); `Morse.BrokenSetup.contMDiff_energy'`: smooth as a function on the
  manifold `N^m ∩ O` for any open `O` with `N^m ∩ O ⊆ U`.
* `Morse.BrokenSetup.continuousOn_energy'`: `E'` is continuous on `U`.
* `Morse.BrokenSetup.isCompact_sublevel`: **`B^a` is compact for `a < c`**.

## What Milnor leaves implicit

* **The description of `B^a`** (p. 91): the condition printed in the scan is
  `ρ(p_{i−1}, p_i)^c/(t_i − t_{i−1}) ≤ a` (exponent `c`, no summation sign); the correct
  condition is `Σ ρ(p_{i−1}, p_i)²/(t_i − t_{i−1}) ≤ a`, formula (∗).
* **Closedness of `B^a` in `S × ⋯ × S`** needs the finiteness of the distances: on `S^m` all
  distances between consecutive vertices are finite except possibly `ρ(x_m, q)`, which is finite
  iff `ρ(p, q)` is (for connected `M`, always).
* **"Depends smoothly"**: the distance `ρ` itself is not smooth on the diagonal; `E'` is smooth
  because `ρ(x, x')² = ‖v(x, x')‖²` with `v` the smooth initial vector of the short geodesic.
-/

open Set Filter Topology Function Module Metric MeasureTheory
open scoped ContDiff Manifold RealInnerProductSpace ENNReal Interval

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- The vertices depend smoothly (in fact affinely) on the break points. -/
theorem contDiff_vert {m : ℕ} (p q : V) (k : Fin (m + 2)) :
    ContDiff ℝ ∞ (fun y : Fin m → V => vert p q y k) := by
  induction k using Fin.cases with
  | zero => exact contDiff_const
  | succ k =>
    induction k using Fin.lastCases with
    | last =>
      have : (fun y : Fin m → V => vert p q y (Fin.last m).succ) = fun _ => q := by
        funext y; rw [Fin.succ_last, vert_last]
      rw [this]; exact contDiff_const
    | cast j =>
      have : (fun y : Fin m → V => vert p q y j.castSucc.succ) = fun y => y j := by
        funext y; rw [vert_inner]
      rw [this]; exact contDiff_apply ℝ V j

namespace BrokenSetup

variable {p q : V} {c : ℝ} {m : ℕ} (B : BrokenSetup hN p q c m)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
variable (N) in
/-- The distances between consecutive vertices, as a function of the break points. -/
def gaps (p q : V) (y : Fin m → V) (i : Fin (m + 1)) : ℝ≥0∞ :=
  riemDist (N := N) (vert p q y i.castSucc) (vert p q y i.succ)

include B in
theorem continuousOn_gaps :
    ContinuousOn (gaps N p q : (Fin m → V) → Fin (m + 1) → ℝ≥0∞) (Set.pi univ fun _ => N) := by
  refine continuousOn_pi.2 fun i => ?_
  exact (continuousOn_riemDist hN).comp (((contDiff_vert p q i.castSucc).continuous.prodMk
    (contDiff_vert p q i.succ).continuous).continuousOn)
    fun y (hy : y ∈ Set.pi univ fun _ => N) =>
      ⟨B.vert_mem (fun j => hy j trivial) i.castSucc, B.vert_mem (fun j => hy j trivial) i.succ⟩

/-- **`U` is an open subset of `N^m`** (Milnor p. 89): `U = N^m ∩ O` for an open `O ⊆ V^m`. -/
theorem exists_isOpen_nodes :
    ∃ O : Set (Fin m → V), IsOpen O ∧ B.nodes = (Set.pi univ fun _ => N) ∩ O := by
  set T : Set (Fin (m + 1) → ℝ≥0∞) :=
    {r | (∀ i, r i ≠ ⊤) ∧ ∑ i, (r i).toReal ^ 2 / B.len i < c}
  have hfin : IsOpen {r : Fin (m + 1) → ℝ≥0∞ | ∀ i, r i ≠ ⊤} := by
    have : {r : Fin (m + 1) → ℝ≥0∞ | ∀ i, r i ≠ ⊤} = ⋂ i, (fun r => r i) ⁻¹' {x | x ≠ ⊤} := by
      ext r; simp
    rw [this]
    exact isOpen_iInter_of_finite fun i => ENNReal.isOpen_ne_top.preimage (continuous_apply i)
  have hcont : ContinuousOn (fun r : Fin (m + 1) → ℝ≥0∞ => ∑ i, (r i).toReal ^ 2 / B.len i)
      {r | ∀ i, r i ≠ ⊤} := by
    refine continuousOn_finsetSum _ fun i _ => ?_
    refine ((ENNReal.continuousOn_toReal.comp (continuous_apply i).continuousOn
      fun (r : Fin (m + 1) → ℝ≥0∞) (hr : r ∈ {r : Fin (m + 1) → ℝ≥0∞ | ∀ i, r i ≠ ⊤}) =>
        hr i).pow 2).div_const _
  have hT : IsOpen T := hcont.isOpen_inter_preimage hfin isOpen_Iio
  obtain ⟨O, hO, hOeq⟩ := continuousOn_iff'.1 B.continuousOn_gaps T hT
  refine ⟨O, hO, ?_⟩
  rw [inter_comm, ← hOeq]
  ext y
  simp only [nodes, mem_ofPred_eq, mem_inter_iff, mem_preimage, Set.mem_pi, mem_univ,
    true_implies, T, gaps, energy']
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h2, h3⟩, h1⟩
  · rintro ⟨⟨h2, h3⟩, h1⟩; exact ⟨h1, h2, h3⟩

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **`E'` is smooth** (Theorem 16.2, Milnor p. 90), in Milnor's sense for subsets of Euclidean
space: near every `y₀ ∈ U` it is the restriction of a smooth function on an open subset of
`V^m`, namely `y ↦ Σ ‖Gᵢ(xᵢ, xᵢ₊₁)‖²/(t_{i+1} − tᵢ)` with `Gᵢ` the smooth local representative of
the short join vector given by Corollary 10.8. -/
theorem exists_smooth_energy' {y₀ : Fin m → V} (hy₀ : y₀ ∈ B.nodes) :
    ∃ O : Set (Fin m → V), IsOpen O ∧ y₀ ∈ O ∧ ∃ F : (Fin m → V) → ℝ, ContDiffOn ℝ ∞ F O ∧
      ∀ y ∈ B.nodes ∩ O, B.energy' y = F y := by
  have hj : ∀ i : Fin (m + 1), IsShortJoin hN B.δ
      ⟨vert p q y₀ i.castSucc, B.vert_mem hy₀.1 _⟩ ⟨vert p q y₀ i.succ, B.vert_mem hy₀.1 _⟩ :=
    fun i => B.join _ _ (B.vert_mem_ball hy₀ i.castSucc) (B.vert_mem_ball hy₀ i.succ)
      (B.riemDist_vert_lt hy₀ i)
  choose v hv hvδ hvexp hvρ hvuniq O₂ hO₂ hmem G hG hG0 hGspec using hj
  set φ : Fin (m + 1) → (Fin m → V) → V × V :=
    fun i y => (vert p q y i.castSucc, vert p q y i.succ)
  have hφ : ∀ i, ContDiff ℝ ∞ (φ i) := fun i =>
    (contDiff_vert p q _).prodMk (contDiff_vert p q _)
  refine ⟨⋂ i, φ i ⁻¹' O₂ i, isOpen_iInter_of_finite fun i => (hO₂ i).preimage (hφ i).continuous,
    mem_iInter.2 fun i => hmem i, fun y => ∑ i, ‖G i (φ i y)‖ ^ 2 / B.len i, ?_, ?_⟩
  · refine ContDiffOn.sum fun i _ => ?_
    refine (((contDiff_norm_sq ℝ).comp_contDiffOn ((hG i).comp (hφ i).contDiffOn
      fun y hy => mem_iInter.1 hy i)).div_const _)
  · rintro y ⟨hy, hyO⟩
    refine Finset.sum_congr rfl fun i _ => ?_
    -- the join vector is `Gᵢ(xᵢ, xᵢ₊₁)`, by uniqueness
    obtain ⟨hGT, hGδ, hGexp⟩ := hGspec i ⟨vert p q y i.castSucc, B.vert_mem hy.1 _⟩
      ⟨vert p q y i.succ, B.vert_mem hy.1 _⟩ (mem_iInter.1 hyO i) (B.riemDist_vert_lt hy i)
    have hspec := B.joinVec_spec (B.vert_mem_ball hy i.castSucc) (B.vert_mem_ball hy i.succ)
      (B.riemDist_vert_lt hy i)
    have heq := hspec.2.2.2.2 _ ((prj_eq_self_iff hN (B.vert_mem hy.1 _)).2 hGT) hGδ hGexp
    rw [hspec.2.2.2.1, ENNReal.toReal_ofReal (norm_nonneg _), ← heq]

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **`E'` is continuous on `U`.** -/
theorem continuousOn_energy' : ContinuousOn B.energy' B.nodes := by
  intro y₀ hy₀
  obtain ⟨O, hO, hy₀O, F, hF, hEF⟩ := B.exists_smooth_energy' hy₀
  have hc : ContinuousWithinAt F (B.nodes ∩ O) y₀ :=
    (hF.continuousOn.continuousAt (hO.mem_nhds hy₀O)).continuousWithinAt
  have h1 : ContinuousWithinAt B.energy' (B.nodes ∩ O) y₀ :=
    hc.congr (fun y hy => hEF y hy) (hEF y₀ ⟨hy₀, hy₀O⟩)
  exact (continuousWithinAt_inter (hO.mem_nhds hy₀O)).1 h1

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **`E'` is a smooth function on the manifold** `N^m ∩ O` of break points, for any open `O`
with `N^m ∩ O ⊆ U` (for instance `U` itself, `Morse.BrokenSetup.exists_isOpen_nodes`). -/
theorem contMDiff_energy' {O : Set (Fin m → V)} (hO : IsOpen O)
    (hOU : (Set.pi univ fun _ => N) ∩ O ⊆ B.nodes) :
    letI := (isSliceSubmanifold_pi_inter hN hO).chartedSpace
    ContMDiff 𝓘(ℝ, Fin m → Z) 𝓘(ℝ, ℝ) ∞
      (fun y : ↥((Set.pi univ fun _ => N) ∩ O) => B.energy' y) := by
  intro y
  obtain ⟨O', hO', hyO', F, hF, hEF⟩ := B.exists_smooth_energy' (hOU y.2)
  exact contMDiffAt_of_locally_eq (isSliceSubmanifold_pi_inter hN hO) hO' hyO' hF
    fun x hx => hEF x ⟨hOU x.2, hx⟩

/-- **`B^a` is compact for `a < c`** (Theorem 16.2, Milnor p. 91): it is a closed subset of the
compact set `S^m`. -/
theorem isCompact_sublevel {a : ℝ} (ha : a < c) :
    IsCompact {y | y ∈ B.nodes ∧ B.energy' y ≤ a} := by
  set K : Set (Fin m → V) := Set.pi univ fun _ => closedRiemBall N p √c
  have hK : IsCompact K := isCompact_univ_pi fun _ => B.isCompact_ball
  have hsub : {y | y ∈ B.nodes ∧ B.energy' y ≤ a} ⊆ K := fun y hy j _ => by
    have := B.vert_mem_ball hy.1 j.castSucc.succ
    rwa [vert_inner] at this
  have hKN : K ⊆ Set.pi univ fun _ => N := fun y hy j _ => (hy j trivial).1
  by_cases hpq : riemDist (N := N) p q = ⊤
  · -- then no broken path from `p` to `q` has finite energy
    convert isCompact_empty
    refine eq_empty_of_forall_notMem fun y hy => ?_
    have hfin := hy.1.2.1 (Fin.last m)
    rw [Fin.succ_last, vert_last] at hfin
    have h1 := B.vert_mem_ball hy.1 (Fin.last m).castSucc
    have h2 : riemDist (N := N) p q ≤
        riemDist (N := N) p (vert p q y (Fin.last m).castSucc) +
          riemDist (N := N) (vert p q y (Fin.last m).castSucc) q := riemDist_triangle _ _ _
    rw [hpq, top_le_iff, ENNReal.add_eq_top] at h2
    rcases h2 with h2 | h2
    · exact ENNReal.ofReal_ne_top (top_le_iff.1 (h2 ▸ h1.2))
    · exact hfin h2
  · -- on `S^m` all distances between consecutive vertices are finite
    have hfinK : ∀ y ∈ K, ∀ i, gaps N p q y i ≠ ⊤ := by
      intro y hy i
      have hyN : ∀ j, y j ∈ N := fun j => (hy j trivial).1
      have hball : ∀ k : Fin (m + 2), k ≠ Fin.last (m + 1) →
          vert p q y k ∈ closedRiemBall N p √c := by
        intro k hk
        induction k using Fin.cases with
        | zero => exact B.p_mem_ball
        | succ k =>
          induction k using Fin.lastCases with
          | last => exact absurd (Fin.succ_last _) hk
          | cast j => rw [vert_inner]; exact hy j trivial
      have hpx : ∀ x ∈ closedRiemBall N p √c, riemDist (N := N) p x ≠ ⊤ := fun x hx =>
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top hx.2
      have hx1 : vert p q y i.castSucc ∈ closedRiemBall N p √c :=
        hball _ (Fin.castSucc_lt_last i).ne
      have hlast : riemDist (N := N) p (vert p q y i.succ) ≠ ⊤ := by
        by_cases hi : i.succ = Fin.last (m + 1)
        · rw [hi, vert_last]; exact hpq
        · exact hpx _ (hball _ hi)
      refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨?_, hlast⟩)
        (riemDist_triangle (N := N) _ p _)
      rw [riemDist_comm]
      exact hpx _ hx1
    have hcont : ContinuousOn B.energy' K := by
      refine continuousOn_finsetSum _ fun i _ => ?_
      refine ((ENNReal.continuousOn_toReal.comp
        ((continuousOn_pi.1 (B.continuousOn_gaps.mono hKN)) i) fun y hy => hfinK y hy i).pow
          2).div_const _
    have heq : {y | y ∈ B.nodes ∧ B.energy' y ≤ a} = K ∩ B.energy' ⁻¹' Iic a := by
      ext y
      refine ⟨fun hy => ⟨hsub hy, hy.2⟩, fun hy => ⟨⟨fun j => (hy.1 j trivial).1,
        hfinK y hy.1, lt_of_le_of_lt hy.2 ha⟩, hy.2⟩⟩
    rw [heq]
    exact hK.of_isClosed_subset (hcont.preimage_isClosed_of_isClosed hK.isClosed isClosed_Iic)
      inter_subset_left

end BrokenSetup

end Morse
