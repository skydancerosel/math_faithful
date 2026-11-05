import Morse.Chapter10.Deformation

/-!
Milnor, *Morse Theory*, §16, pp. 88–91: the two descriptions of `B^a` — as a subspace of the path
space `Ω` and as a subspace of `M × ⋯ × M` (break points) — and **Theorem 16.3 for `Ω^a`**, for a
submanifold `N ⊆ ℝᴷ` with the induced metric.

# `Ω^a` has the homotopy type of a finite cell complex

## Milnor's text, paraphrased

(p. 89) The correspondence `ω ↦ (ω(t₁), …, ω(t_{k−1}))` is a homeomorphism of
`Int Ω(t₀, …, t_k)^c` onto an open subset of `M × ⋯ × M`.  (p. 90) **Theorem 16.3**: if `p` and
`q` are not conjugate along any geodesic of length `≤ √a`, then `Ω^a` has the homotopy type of a
finite CW-complex with one cell of dimension `λ` for each geodesic in `Ω^a` from `p` to `q` of
index `λ`.  *Proof*: `Ω^a` has the homotopy type of `B^a` (Theorem 16.2), to which the Morse
theory of Part I applies (`E'` on the compact `B^a`).

## In the embedded setting

For `B : Morse.BrokenSetup hN p q c m`:

* `Morse.BrokenSetup.tendsto_path_apply`, `Morse.BrokenSetup.continuous_pathP`: the broken
  geodesic `B.path y` depends continuously on its break points `y ∈ U`, for Milnor's metric;
  `Morse.BrokenSetup.continuous_nodeVal`: the break points depend continuously on the path.
* `Morse.BrokenSetup.homotopyEquivNodes`: **`B^a ⊆ Ω` and `B^a ⊆ N^m` have the same homotopy type**
  (`a < c`); they are homeomorphic up to the identification of paths agreeing on `[0, 1]`.
* `Morse.BrokenSetup.theorem_16_3_Omega`: **Theorem 16.3 for `Ω^a`** (`a < c`): if `a` is not the
  energy of a geodesic from `p` to `q` and every geodesic from `p` to `q` of energy `≤ a` is
  non-degenerate (non-conjugate end points), then
  `Ω^a = {γ ∈ Ω : E(γ) ≤ a}`, with Milnor's metric, has the homotopy type of an iterated
  adjunction space with one cell of dimension `λ` for each geodesic of energy `≤ a` and index `λ`;
  `Morse.BrokenSetup.theorem_16_3_Omega_count` counts the cells.

## What Milnor leaves implicit

* **The two topologies on `B`** (p. 89, "homeomorphism"): continuity of `ω ↦ (ω(tᵢ))` needs that
  `ρ` dominates the distance of `ℝᴷ`; continuity of the inverse for the `L²` part of `d` needs
  the continuity of the speeds `ρ(xᵢ, xᵢ₊₁)/(t_{i+1} − tᵢ)`, and for the uniform part the
  continuity of the short geodesics in their end points (Corollary 10.8).  Here paths are
  functions on `ℝ`, so the correspondence is a homotopy equivalence (paths agreeing on `[0, 1]`
  are at distance `0`).
* **Regular value**: Milnor's statement does not exclude that `a` is the energy of a geodesic;
  the version here (as Theorem 16.3 for `B^a`, `Morse/Chapter10/Finite.lean`) assumes it.
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
/-- Paths agreeing on `[0, 1]` are at distance `0`. -/
theorem edist_eq_zero_of_eqOn {α β : PathSp N p q} (h : EqOn α β (Icc 0 1)) : edist α β = 0 := by
  rw [edist_def, supDist_congr h (fun _ _ => rfl), l2Dist_congr h (fun _ _ => rfl),
    supDist_self β.mem, l2Dist_self, ENNReal.ofReal_zero, add_zero]

end PathSp

namespace BrokenSetup

variable {p q : V} {c : ℝ} {m : ℕ} (B : BrokenSetup hN p q c m)

/-! ### The broken geodesics depend continuously on their break points -/

/-- **Pointwise continuity of `y ↦ B.path y`.** -/
theorem tendsto_path_apply {ι : Type*} {l : Filter ι} {ys : ι → Fin m → V} {y : Fin m → V}
    (hy : y ∈ B.nodes) (hys : ∀ᶠ j in l, ys j ∈ B.nodes) (h : Tendsto ys l (𝓝 y)) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : Tendsto (fun j => B.path (ys j) s) l (𝓝 (B.path y s)) := by
  set k := B.segOf s
  have hk := B.mem_Icc_segOf hs
  have hkk : B.t k.castSucc < B.t k.succ := B.t_lt_iff.2 Fin.castSucc_lt_succ
  have heq : ∀ y' ∈ B.nodes, B.path y' s = B.sgeoOver (vert p q y' k.castSucc)
      (vert p q y' k.succ) (B.t k.castSucc) (B.t k.succ) s := fun y' hy' => by
    rw [B.path_eq_segPath hy' k hk, segPath, sgeoOver]
    rfl
  rw [heq y hy]
  refine Tendsto.congr' (by filter_upwards [hys] with j hj; exact (heq _ hj).symm) ?_
  have hv : ∀ k', Tendsto (fun j => vert p q (ys j) k') l (𝓝 (vert p q y k')) := fun k' =>
    ((contDiff_vert p q k').continuous.tendsto y).comp h
  have hJ : ∀ y' ∈ B.nodes, (vert p q y' k.castSucc, vert p q y' k.succ) ∈ B.joinable :=
    fun y' hy' => ⟨B.vert_mem_ball hy' k.castSucc, B.vert_mem_ball hy' k.succ,
      B.riemDist_vert_lt hy' k⟩
  exact B.tendsto_sgeoOver (hv _) (hv _) (hys.mono fun j hj => hJ _ hj) (hJ y hy)
    tendsto_const_nhds hkk tendsto_const_nhds (Eventually.of_forall fun _ => hk) hk

/-- The broken geodesic with break points `y ∈ U`, as a point of `Ω`. -/
def pathP (y : B.nodes) : PathSp N p q := ⟨B.path y, B.path_mem_pathSpace y.2⟩

/-- **The broken geodesic depends continuously on its break points**, for Milnor's metric. -/
theorem continuous_pathP : Continuous B.pathP := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  rw [ContinuousAt, tendsto_iff_edist_tendsto_0, ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨r, -, hr, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hr' : 0 < r := ENNReal.ofReal_pos.1 hr
  have hval : Tendsto (fun y' : B.nodes => (y' : Fin m → V)) (𝓝 y) (𝓝 y) :=
    continuous_subtype_val.tendsto y
  have hnodes : ∀ᶠ y' : B.nodes in 𝓝 y, (y' : Fin m → V) ∈ B.nodes :=
    Eventually.of_forall fun y' => y'.2
  have h1 := PathSp.eventually_supDist_le_of_tendsto_apply hN (C := c) (l := 𝓝 y)
    (αs := fun y' : B.nodes => B.path y')
    (Eventually.of_forall fun y' => ⟨B.path_mem_pathSpace y'.2, by
      rw [B.energy_path y'.2]; exact y'.2.2.2.le⟩)
    (B.path_mem_pathSpace y.2) (by rw [B.energy_path y.2]; exact y.2.2.2.le)
    (fun _ hs => B.tendsto_path_apply y.2 hnodes hval hs) (e := r / 2) (by positivity)
  have h2 := (B.tendsto_integral_speed_path y.2 hnodes hval).eventually
    (ge_mem_nhds (show (0 : ℝ) < (r / 2) ^ 2 by positivity))
  filter_upwards [h1, h2] with y' h1 h2
  have h3 : PathSp.l2Dist (B.path y') (B.path y) ≤ r / 2 := by
    rw [PathSp.l2Dist]
    calc √(∫ τ in (0 : ℝ)..1, (PathSp.speed (B.path y') τ - PathSp.speed (B.path y) τ) ^ 2)
        ≤ √((r / 2) ^ 2) := Real.sqrt_le_sqrt h2
      _ = r / 2 := Real.sqrt_sq (by positivity)
  calc edist (B.pathP y') (B.pathP y)
      = PathSp.supDist N (B.path y') (B.path y) +
          ENNReal.ofReal (PathSp.l2Dist (B.path y') (B.path y)) := PathSp.edist_def _ _
    _ ≤ ENNReal.ofReal (r / 2) + ENNReal.ofReal (r / 2) :=
        add_le_add h1 (ENNReal.ofReal_le_ofReal h3)
    _ = ENNReal.ofReal r := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf
    _ ≤ ε := hrε.le

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **The break points depend continuously on the path**, for Milnor's metric. -/
theorem continuous_nodeVal : Continuous fun γ : PathSp N p q => B.nodeVal γ :=
  continuous_iff_continuousAt.2 fun γ =>
    B.tendsto_nodeVal (l := 𝓝 γ) (γs := fun γ' => γ') tendsto_id

/-! ### The two descriptions of `B^a` -/

/-- The break points, `B^a ⊆ Ω → B^a ⊆ N^m` (`a < c`). -/
def nodeMap (a : ℝ) :
    C({γ : PathSp N p q // energy γ 0 1 ≤ a ∧ (γ : ℝ → V) ∈ B.brokenPaths},
      {y | y ∈ B.nodes ∧ B.energy' y ≤ a}) where
  toFun γ := ⟨B.nodeVal γ.1, (B.nodeVal_mem_nodes_of_energy_lt γ.1.mem γ.2.2.2.2).1,
    (B.nodeVal_mem_nodes_of_energy_lt γ.1.mem γ.2.2.2.2).2.trans γ.2.1⟩
  continuous_toFun := (B.continuous_nodeVal.comp continuous_subtype_val).subtype_mk _

/-- The broken geodesics, `B^a ⊆ N^m → B^a ⊆ Ω`. -/
def pathMap (a : ℝ) :
    C({y | y ∈ B.nodes ∧ B.energy' y ≤ a},
      {γ : PathSp N p q // energy γ 0 1 ≤ a ∧ (γ : ℝ → V) ∈ B.brokenPaths}) where
  toFun y := ⟨B.pathP ⟨y.1, y.2.1⟩, by rw [pathP, B.energy_path y.2.1]; exact y.2.2,
    ((B.lemma_16_1).1 _ y.2.1).1⟩
  continuous_toFun := (B.continuous_pathP.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _

/-- **`B^a ⊆ Ω` and `B^a ⊆ N^m` have the same homotopy type** (Milnor p. 89: "a homeomorphism",
up to the identification of paths agreeing on `[0, 1]`). -/
def homotopyEquivNodes (a : ℝ) :
    ContinuousMap.HomotopyEquiv
      {γ : PathSp N p q // energy γ 0 1 ≤ a ∧ (γ : ℝ → V) ∈ B.brokenPaths}
      {y | y ∈ B.nodes ∧ B.energy' y ≤ a} where
  toFun := B.nodeMap a
  invFun := B.pathMap a
  left_inv := by
    classical
    refine ⟨{
      toFun := fun x => if (x.1 : ℝ) < 1 then B.pathMap a (B.nodeMap a x.2) else x.2
      continuous_toFun := PathSp.continuous_of_edist_eq_zero continuous_snd fun x => ?_
      map_zero_left := fun γ => by simp
      map_one_left := fun γ => by simp }⟩
    split_ifs
    · exact PathSp.edist_eq_zero_of_eqOn (B.path_nodeVal x.2.2.2)
    · exact edist_self _
  right_inv := by
    have : (B.nodeMap a).comp (B.pathMap a) = ContinuousMap.id _ := by
      ext y
      exact congrFun (B.nodeVal_path y.2.1) _
    rw [this]

/-! ### Theorem 16.3 for `Ω^a` -/

/-- **Theorem 16.3** (Milnor p. 90) **for `Ω^a`**: let `a < c` be such that no geodesic from `p` to
`q` has energy exactly `a`, and every geodesic from `p` to `q` of energy `≤ a` is non-degenerate
(nullity `0`, i.e. `p`, `q` not conjugate along it, Theorem 14.1).  Then the geodesics from `p` to
`q` of energy `≤ a` are finitely many — their break points form a list `ys` — and
`Ω^a = {γ ∈ Ω : E(γ) ≤ a}`, with Milnor's metric, has the homotopy type of an iterated adjunction
space with one cell of dimension `λ` for each of them, `λ` its index. -/
theorem theorem_16_3_Omega {a : ℝ} (ha : a < c)
    (hreg : ∀ γ ∈ pathSpace N p q, IsUnbrokenGeodesic hN γ → energy γ 0 1 ≠ a)
    (hnd : ∀ γ (hγ : γ ∈ pathSpace N p q), IsUnbrokenGeodesic hN γ → energy γ 0 1 ≤ a →
      hessNullity hN hγ = 0) :
    ∃ ys : List (Fin m → V), ys.Nodup ∧
      (∀ y, y ∈ ys ↔ y ∈ B.nodes ∧ IsUnbrokenGeodesic hN (B.path y) ∧ B.energy' y ≤ a) ∧
      (∀ y (hy : y ∈ B.nodes), y ∈ ys →
        (B.geodIndex y : ℕ∞) = formIndex (energyHessian hN (B.path_mem_pathSpace hy))) ∧
      IsFiniteCellComplexType {γ : PathSp N p q // energy γ 0 1 ≤ a} (ys.map B.geodIndex) := by
  obtain ⟨ys, h1, h2, h3, -, hcell⟩ := B.theorem_16_3 ha
    (fun y hy hgeo => by rw [← B.energy_path hy]; exact hreg _ (B.path_mem_pathSpace hy) hgeo)
    (fun y hy hgeo hya => hnd _ (B.path_mem_pathSpace hy) hgeo (by rwa [B.energy_path hy]))
  exact ⟨ys, h1, h2, h3, (hcell.of_homotopyEquiv (B.homotopyEquivNodes a)).of_homotopyEquiv
    (B.homotopyEquivBroken ha)⟩

/-- **Theorem 16.3 for `Ω^a`, counting cells**: under the hypotheses of
`Morse.BrokenSetup.theorem_16_3_Omega`, there are finitely many geodesics from `p` to `q` of energy
`≤ a` (each the broken geodesic of its break points), and `Ω^a` has the homotopy type of an
iterated adjunction space whose number of cells of dimension `λ` is the number of those of
index `λ`. -/
theorem theorem_16_3_Omega_count {a : ℝ} (ha : a < c)
    (hreg : ∀ γ ∈ pathSpace N p q, IsUnbrokenGeodesic hN γ → energy γ 0 1 ≠ a)
    (hnd : ∀ γ (hγ : γ ∈ pathSpace N p q), IsUnbrokenGeodesic hN γ → energy γ 0 1 ≤ a →
      hessNullity hN hγ = 0) :
    {y | y ∈ B.nodes ∧ IsUnbrokenGeodesic hN (B.path y) ∧ B.energy' y ≤ a}.Finite ∧
    ∃ cells : List ℕ, IsFiniteCellComplexType {γ : PathSp N p q // energy γ 0 1 ≤ a} cells ∧
      ∀ k : ℕ, cells.count k = {y | y ∈ B.nodes ∧ IsUnbrokenGeodesic hN (B.path y) ∧
        B.energy' y ≤ a ∧ B.geodIndex y = k}.ncard := by
  obtain ⟨hfin, cells, hcell, hcount⟩ := B.theorem_16_3_count ha
    (fun y hy hgeo => by rw [← B.energy_path hy]; exact hreg _ (B.path_mem_pathSpace hy) hgeo)
    (fun y hy hgeo hya => hnd _ (B.path_mem_pathSpace hy) hgeo (by rwa [B.energy_path hy]))
  exact ⟨hfin, cells, (hcell.of_homotopyEquiv (B.homotopyEquivNodes a)).of_homotopyEquiv
    (B.homotopyEquivBroken ha), hcount⟩

end BrokenSetup

end Morse
