import Morse.Chapter10.BrokenIndex
import Morse.Chapter10.SublevelCW

/-!
Milnor, *Morse Theory*, §16, p. 90: Theorem 16.3, for a submanifold `N ⊆ ℝᴷ` with the induced
metric, in the finite dimensional model `B^a`.

# Finitely many cells below each energy level

## Milnor's text, paraphrased

**Theorem 16.3** (p. 90).  Let `M` be complete and `p, q ∈ M` not conjugate along any geodesic of
length `≤ √a`.  Then `Ω^a` has the homotopy type of a finite CW-complex, with one cell of dimension
`λ` for each geodesic in `Ω^a` at which `E_**` has index `λ`.  (In particular `Ω^a` contains only
finitely many geodesics.)  *Proof*: "This follows from 16.2 together with §3.5."

## In the embedded setting

For `B : Morse.BrokenSetup hN p q c m` and `a < c`, the statement is proved for Milnor's
finite dimensional model `B^a = {y ∈ U : E'(y) ≤ a}` of `Ω^a` (Milnor's `B^a` is a deformation
retract of `Ω^a`, Theorem 16.2; that part, which needs the topology of `Ω`, is not formalized
here).

* `Morse.BrokenSetup.theorem_16_3`: **Theorem 16.3**.  If `a < c` is not a critical value of `E'`
  and the critical points of `E'` in `B^a` are non-degenerate — i.e. `E_**` has nullity `0` at
  every geodesic from `p` to `q` of energy `≤ a`, by Theorem 14.1: `p` and `q` are not conjugate
  along it — then the geodesics from `p` to `q` of energy `≤ a` are finitely many, `γ₁, …, γ_j`
  (listed by non-decreasing energy, through their break points), and `B^a` has the homotopy type
  of an iterated adjunction space (`Morse.IsFiniteCellComplexType`, Part I's substitute for a
  finite CW complex) with one cell of dimension `index(γᵢ)` for each `i`.
* `Morse.BrokenSetup.theorem_16_3_count`: the same, counted: for every `λ` the number of cells of
  dimension `λ` is the number of geodesics of energy `≤ a` and index `λ`.
* `Morse.BrokenSetup.theorem_16_3_nonconj`: the hypotheses as in Milnor: `p`, `q` not conjugate
  along any geodesic of energy `≤ a`, and `a` not the energy of a geodesic.
* `Morse.BrokenSetup.eqOn_path_nodeVal_of_isUnbrokenGeodesic`: every geodesic `γ ∈ Ω` of energy
  `< c` is the broken geodesic of its break points, so the geodesics counted are all the geodesics
  in `Ω^a`.
* `Morse.BrokenSetup.exists_energy_minimizing`: **Milnor's Remark on p. 92**: if `Ω^a ≠ ∅` for
  some `a < c`, the minimum of `E'` on the compact `B^a` is a geodesic minimizing the energy on
  all of `Ω` (a second proof of the existence part of Hopf–Rinow).  Milnor calls it "the required
  minimal geodesic"; that it minimizes `E` on `Ω` needs `E(ω) ≥ E'(ω(t₁), …)` for every `ω`
  (Schwarz's inequality), and that it is a geodesic needs "a minimum is a critical point".

## What Milnor leaves implicit

* **"16.2 together with §3.5"**: Theorem 3.5 needs a function with compact sublevel sets on a
  manifold, while `B` is not compact and `E'` is only defined on `B`.  Here: `E'` is extended
  from the compact set `B^{(a+c)/2}` to a smooth function on `V^m`
  (`Morse.exists_contDiff_eq_of_locally`), the manifold is `{y ∈ U : E'(y) < (a + c)/2}`, and the
  sublevel-set version of Theorem 3.5 (`Morse.isFiniteCellComplexType_sublevel_of_isCompact`)
  applies, needing non-degeneracy only in `B^a`.
* **`a` must not be a critical value** (Milnor's hypothesis "non-conjugate along geodesics of
  length `≤ √a`" does not exclude a geodesic of energy exactly `a`; then `B^a` is a critical
  sublevel set, covered by the Remark after 3.5 only through Remark 3.4).  The non-degenerate
  critical points in `B^a` are finitely many since they are isolated in the compact `B^a`.
-/

open Set Filter Topology Function Module Metric MeasureTheory
open scoped ContDiff Manifold RealInnerProductSpace ENNReal Interval

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

namespace BrokenSetup

variable {p q : V} {c : ℝ} {m : ℕ} (B : BrokenSetup hN p q c m)

/-- The sets `{y ∈ U : E'(y) < b}` are open in `N^m`. -/
theorem exists_isOpen_sublevel_lt (b : ℝ) :
    ∃ O : Set (Fin m → V), IsOpen O ∧
      {y | y ∈ B.nodes ∧ B.energy' y < b} = (Set.pi univ fun _ => N) ∩ O := by
  obtain ⟨O₀, hO₀, hO₀eq⟩ := B.exists_isOpen_nodes
  obtain ⟨O₁, hO₁, hO₁eq⟩ := continuousOn_iff'.1 B.continuousOn_energy' (Iio b) isOpen_Iio
  refine ⟨O₁ ∩ O₀, hO₁.inter hO₀, ?_⟩
  ext y
  have h := Set.ext_iff.1 hO₁eq y
  have h0 := Set.ext_iff.1 hO₀eq y
  simp only [mem_preimage, mem_Iio, mem_inter_iff] at h h0
  simp only [mem_ofPred_eq, mem_inter_iff]
  constructor
  · rintro ⟨hy, hyb⟩
    exact ⟨(h0.1 hy).1, (h.1 ⟨hyb, hy⟩).1, (h0.1 hy).2⟩
  · rintro ⟨hpi, hy1, hy0⟩
    have hy : y ∈ B.nodes := h0.2 ⟨hpi, hy0⟩
    exact ⟨hy, (h.2 ⟨hy1, hy⟩).1⟩

/-- **`E'` extends smoothly** from the compact set `B^b`, `b < c`, to all of `V^m`. -/
theorem exists_contDiff_eq_energy' {b : ℝ} (hb : b < c) :
    ∃ F : (Fin m → V) → ℝ, ContDiff ℝ ∞ F ∧
      ∀ y ∈ {y | y ∈ B.nodes ∧ B.energy' y ≤ b}, F y = B.energy' y :=
  exists_contDiff_eq_of_locally (B.isCompact_sublevel hb) (fun _ hy => hy.1) fun _ hy =>
    let ⟨O, hO, hyO, G, hG, hEG⟩ := B.exists_smooth_energy' hy.1
    ⟨O, hO, hyO, G, hG, hEG⟩

open Classical in
/-- **The index of the broken geodesic with break points `y`**, as a natural number: the index of
`E_**` at `B.path y` (`0` if `y ∉ U`; finite at a geodesic by Lemma 15.4). -/
def geodIndex (y : Fin m → V) : ℕ :=
  if hy : y ∈ B.nodes then (formIndex (energyHessian hN (B.path_mem_pathSpace hy))).toNat else 0

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- An unbroken geodesic is a broken geodesic for every subdivision. -/
theorem isBroken_of_isUnbrokenGeodesic {γ : ℝ → V} (hγ : IsUnbrokenGeodesic hN γ) :
    B.IsBroken γ := fun _ =>
  hγ.2.mono isOpen_Ioo (Ioo_subset_Ioo (B.t_nonneg _) (B.t_le_one _))

/-- **Every geodesic of energy `< c` is the broken geodesic of its break points** (so the
geodesics of `Ω^a`, `a < c`, are the `B.path y` with `y ∈ U` a critical point of `E'`). -/
theorem eqOn_path_nodeVal_of_isUnbrokenGeodesic {γ : ℝ → V} (hγ : γ ∈ pathSpace N p q)
    (hgeo : IsUnbrokenGeodesic hN γ) (hE : energy γ 0 1 < c) :
    B.nodeVal γ ∈ B.nodes ∧ EqOn (B.path (B.nodeVal γ)) γ (Icc 0 1) ∧
      IsUnbrokenGeodesic hN (B.path (B.nodeVal γ)) ∧ B.energy' (B.nodeVal γ) = energy γ 0 1 := by
  have hmem : γ ∈ B.brokenPaths := ⟨hγ, B.isBroken_of_isUnbrokenGeodesic hgeo, hE⟩
  obtain ⟨hy, heq⟩ := (B.lemma_16_1).2 γ hmem
  refine ⟨hy, heq, ⟨hgeo.1.congr fun t ht => heq ht, hgeo.2.congr fun t ht =>
    (heq (Ioo_subset_Icc_self ht)).symm⟩, ?_⟩
  rw [← B.energy_path hy]
  exact energy_congr heq

/-- **Theorem 16.3** (Milnor p. 90), for the finite dimensional model `B^a` of `Ω^a`: let `a < c`
be a regular value of `E'` — not the energy of a geodesic from `p` to `q` — and suppose `E_**` is
non-degenerate at every geodesic from `p` to `q` of energy `≤ a` (`p`, `q` not conjugate along it,
Theorem 14.1).  Then the geodesics from `p` to `q` of energy `≤ a` are finitely many — their break
points form a list `ys` — and `B^a = {y ∈ U : E'(y) ≤ a}` has the homotopy type of an iterated
adjunction space with one cell of dimension `λ` for each of them, `λ` its index. -/
theorem theorem_16_3 {a : ℝ} (ha : a < c)
    (hreg : ∀ y ∈ B.nodes, IsUnbrokenGeodesic hN (B.path y) → B.energy' y ≠ a)
    (hnd : ∀ y (hy : y ∈ B.nodes), IsUnbrokenGeodesic hN (B.path y) → B.energy' y ≤ a →
      hessNullity hN (B.path_mem_pathSpace hy) = 0) :
    ∃ ys : List (Fin m → V), ys.Nodup ∧
      (∀ y, y ∈ ys ↔ y ∈ B.nodes ∧ IsUnbrokenGeodesic hN (B.path y) ∧ B.energy' y ≤ a) ∧
      (∀ y (hy : y ∈ B.nodes), y ∈ ys →
        (B.geodIndex y : ℕ∞) = formIndex (energyHessian hN (B.path_mem_pathSpace hy))) ∧
      ys.Pairwise (fun y y' => B.energy' y ≤ B.energy' y') ∧
      IsFiniteCellComplexType {y | y ∈ B.nodes ∧ B.energy' y ≤ a} (ys.map B.geodIndex) := by
  classical
  set c₁ := (a + c) / 2 with hc₁
  have hac₁ : a < c₁ := by linarith
  have hc₁c : c₁ < c := by linarith
  obtain ⟨F, hF, hFE⟩ := B.exists_contDiff_eq_energy' hc₁c
  obtain ⟨O, hO, hOeq⟩ := B.exists_isOpen_sublevel_lt c₁
  set S := (Set.pi univ fun _ => N) ∩ O with hS_def
  have hSmem : ∀ y, y ∈ S ↔ y ∈ B.nodes ∧ B.energy' y < c₁ := fun y =>
    (Set.ext_iff.1 hOeq y).symm
  have hOU : S ⊆ B.nodes := fun y hy => ((hSmem y).1 hy).1
  have hFE' : ∀ y ∈ S, F y = B.energy' y := fun y hy =>
    hFE y ⟨((hSmem y).1 hy).1, ((hSmem y).1 hy).2.le⟩
  set hSm := isSliceSubmanifold_pi_inter hN hO
  let _ := hSm.chartedSpace
  -- the sublevel set of `F|S` at `a` is `B^a`
  have hBa : Subtype.val '' ((F ∘ Subtype.val : S → ℝ) ⁻¹' Iic a) =
      {y | y ∈ B.nodes ∧ B.energy' y ≤ a} := by
    ext y
    simp only [mem_image, mem_preimage, Function.comp_apply, mem_Iic, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨y, hy⟩, hya, rfl⟩
      exact ⟨hOU hy, by rw [← hFE' y hy]; exact hya⟩
    · rintro ⟨hy, hya⟩
      have hyS : y ∈ S := (hSmem y).2 ⟨hy, lt_of_le_of_lt hya hac₁⟩
      exact ⟨⟨y, hyS⟩, by rw [hFE' y hyS]; exact hya, rfl⟩
  have hK : IsCompact ((F ∘ Subtype.val : S → ℝ) ⁻¹' Iic a) := by
    rw [Topology.IsInducing.subtypeVal.isCompact_iff, hBa]
    exact B.isCompact_sublevel ha
  have hcrit : ∀ y : S, IsCriticalPointM (Fin m → Z) (F ∘ Subtype.val) y ↔
      IsUnbrokenGeodesic hN (B.path y) := fun y => B.isCriticalPointM_iff hO hOU hF hFE' y
  have hnd' : ∀ y : S, IsCriticalPointM (Fin m → Z) (F ∘ Subtype.val) y → F y ≤ a →
      IsNondegenerate (hessianM (Fin m → Z) (F ∘ Subtype.val) y) := by
    intro y hy hya
    have hgeo := (hcrit y).1 hy
    have h0 := hnd y (hOU y.2) hgeo (by rw [← hFE' y y.2]; exact hya)
    rw [isNondegenerate_iff_nullity_eq_zero]
    have := (B.theorem_16_2_index hO hOU hF hFE' y hgeo).2
    rw [nullityM] at this
    rw [this, h0]
  have ha' : ∀ y : S, IsCriticalPointM (Fin m → Z) (F ∘ Subtype.val) y → F y ≠ a := by
    intro y hy
    rw [hFE' y y.2]
    exact hreg y (hOU y.2) ((hcrit y).1 hy)
  obtain ⟨ps, hpsnd, hpsmem, hpssort, hcell⟩ :=
    isFiniteCellComplexType_sublevel_of_isCompact hSm hF hK hnd' ha'
  -- the indices
  have hidx : ∀ y ∈ ps, indexM (Fin m → Z) (F ∘ Subtype.val) y = B.geodIndex y := by
    intro y hy
    have hgeo := (hcrit y).1 ((hpsmem y).1 hy).1
    have h1 := (B.theorem_16_2_index hO hOU hF hFE' y hgeo).1
    rw [geodIndex, dif_pos (hOU y.2), ← h1]
    rfl
  refine ⟨ps.map Subtype.val, hpsnd.map Subtype.val_injective, fun y => ?_, fun y hy hys => ?_,
    ?_, ?_⟩
  · simp only [List.mem_map]
    constructor
    · rintro ⟨y', hy', rfl⟩
      obtain ⟨hc, hlt⟩ := (hpsmem y').1 hy'
      exact ⟨hOU y'.2, (hcrit y').1 hc, by rw [← hFE' y' y'.2]; exact hlt.le⟩
    · rintro ⟨hy, hgeo, hya⟩
      have hyS : y ∈ S := (hSmem y).2 ⟨hy, lt_of_le_of_lt hya hac₁⟩
      refine ⟨⟨y, hyS⟩, (hpsmem _).2 ⟨(hcrit ⟨y, hyS⟩).2 hgeo, ?_⟩, rfl⟩
      change F y < a
      rw [hFE' y hyS]
      exact lt_of_le_of_ne hya (hreg y hy hgeo)
  · obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hys
    have hgeo := (hcrit y').1 ((hpsmem y').1 hy').1
    have h1 := (B.theorem_16_2_index hO hOU hF hFE' y' hgeo).1
    rw [← hidx y' hy', ← h1]
  · refine List.Pairwise.map _ (fun y y' h => ?_) hpssort
    rw [← hFE' y y.2, ← hFE' y' y'.2]
    exact h
  · -- transport the cell structure along `F|S ≤ a` ≃ `B^a`
    have hmap : ps.map (indexM (Fin m → Z) (F ∘ Subtype.val)) =
        (ps.map Subtype.val).map B.geodIndex := by
      rw [List.map_map]
      exact List.map_congr_left fun y hy => hidx y hy
    rw [← hmap]
    let e : ↥{y | y ∈ B.nodes ∧ B.energy' y ≤ a} ≃ₜ
        ↥(sublevel (F ∘ Subtype.val : S → ℝ) a) :=
      { toFun := fun y => ⟨⟨y.1, (hSmem y.1).2 ⟨y.2.1, lt_of_le_of_lt y.2.2 hac₁⟩⟩, by
          change F y.1 ≤ a
          rw [hFE' y.1 ((hSmem y.1).2 ⟨y.2.1, lt_of_le_of_lt y.2.2 hac₁⟩)]
          exact y.2.2⟩
        invFun := fun y => ⟨y.1.1, hOU y.1.2, by
          have h2 : F y.1.1 ≤ a := y.2
          rwa [hFE' _ y.1.2] at h2⟩
        left_inv := fun y => rfl
        right_inv := fun y => rfl
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    exact hcell.of_homotopyEquiv e.toHomotopyEquiv

/-- **Theorem 16.3, counting cells** (Milnor p. 90: "one cell of dimension `λ` for each geodesic
in `Ω^a` at which `E_**` has index `λ`"): under the hypotheses of `Morse.BrokenSetup.theorem_16_3`,
`B^a` has the homotopy type of an iterated adjunction space whose number of cells of each
dimension `λ` is the number of geodesics from `p` to `q` of energy `≤ a` and index `λ`; in
particular there are finitely many such geodesics. -/
theorem theorem_16_3_count {a : ℝ} (ha : a < c)
    (hreg : ∀ y ∈ B.nodes, IsUnbrokenGeodesic hN (B.path y) → B.energy' y ≠ a)
    (hnd : ∀ y (hy : y ∈ B.nodes), IsUnbrokenGeodesic hN (B.path y) → B.energy' y ≤ a →
      hessNullity hN (B.path_mem_pathSpace hy) = 0) :
    {y | y ∈ B.nodes ∧ IsUnbrokenGeodesic hN (B.path y) ∧ B.energy' y ≤ a}.Finite ∧
    ∃ cells : List ℕ, IsFiniteCellComplexType {y | y ∈ B.nodes ∧ B.energy' y ≤ a} cells ∧
      ∀ k : ℕ, cells.count k = {y | y ∈ B.nodes ∧ IsUnbrokenGeodesic hN (B.path y) ∧
        B.energy' y ≤ a ∧ B.geodIndex y = k}.ncard := by
  classical
  obtain ⟨ys, hnd', hmem, -, -, hcell⟩ := B.theorem_16_3 ha hreg hnd
  refine ⟨(ys.toFinset.finite_toSet).subset fun y hy => by simpa using (hmem y).2 hy,
    _, hcell, fun k => ?_⟩
  have hset : {y | y ∈ B.nodes ∧ IsUnbrokenGeodesic hN (B.path y) ∧ B.energy' y ≤ a ∧
      B.geodIndex y = k} = ↑(ys.filter (fun y => B.geodIndex y = k)).toFinset := by
    ext y
    simp only [mem_ofPred_eq, List.coe_toFinset, List.mem_filter, decide_eq_true_eq, hmem]
    tauto
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup (hnd'.filter _), List.count,
    List.countP_map, List.countP_eq_length_filter]
  rfl

/-- **Theorem 16.3 with Milnor's hypothesis** (p. 90): if `p` and `q` are not conjugate along any
geodesic from `p` to `q` of energy `≤ a` (length `≤ √a`), and `a < c` is not the energy of a
geodesic, then `B^a` has the homotopy type of an iterated adjunction space with one cell of
dimension `λ` for each geodesic of energy `≤ a` and index `λ` (non-conjugacy gives nullity `0` by
Theorem 14.1). -/
theorem theorem_16_3_nonconj {a : ℝ} (ha : a < c)
    (hreg : ∀ y ∈ B.nodes, IsUnbrokenGeodesic hN (B.path y) → B.energy' y ≠ a)
    (hnc : ∀ y ∈ B.nodes, IsUnbrokenGeodesic hN (B.path y) → B.energy' y ≤ a →
      ¬IsConjugate hN (B.path y) 0 1) :
    ∃ ys : List (Fin m → V), ys.Nodup ∧
      (∀ y, y ∈ ys ↔ y ∈ B.nodes ∧ IsUnbrokenGeodesic hN (B.path y) ∧ B.energy' y ≤ a) ∧
      (∀ y (hy : y ∈ B.nodes), y ∈ ys →
        (B.geodIndex y : ℕ∞) = formIndex (energyHessian hN (B.path_mem_pathSpace hy))) ∧
      ys.Pairwise (fun y y' => B.energy' y ≤ B.energy' y') ∧
      IsFiniteCellComplexType {y | y ∈ B.nodes ∧ B.energy' y ≤ a} (ys.map B.geodIndex) := by
  refine B.theorem_16_3 ha hreg fun y hy hgeo hya => ?_
  have hγ := B.path_mem_pathSpace hy
  have hc := hgeo.isSmoothCurveIn hN hγ
  rw [theorem_14_1_nullity hγ hgeo]
  by_contra hne
  exact hnc y hy hgeo hya ((isConjugate_iff hc).2 ⟨⟨le_rfl, zero_le_one⟩, ⟨zero_le_one, le_rfl⟩,
    zero_ne_one, Nat.pos_of_ne_zero hne⟩)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- The break points of a path of energy `< c` lie in `U`, and their broken geodesic has at most
the energy of the path (Schwarz's inequality on each segment). -/
theorem nodeVal_mem_nodes_of_energy_lt {γ : ℝ → V} (hγ : γ ∈ pathSpace N p q)
    (hE : energy γ 0 1 < c) : B.nodeVal γ ∈ B.nodes ∧ B.energy' (B.nodeVal γ) ≤ energy γ 0 1 := by
  have hle := B.energy'_nodeVal_le hγ
  refine ⟨⟨fun j => hγ.2.1 _ ⟨B.t_nonneg _, B.t_le_one _⟩, fun i => ?_, lt_of_le_of_lt hle hE⟩,
    hle⟩
  rw [B.vert_nodeVal hγ, B.vert_nodeVal hγ]
  have h0 := B.t_nonneg i.castSucc
  have hle' := B.t_le_iff.2 (Fin.castSucc_lt_succ (i := i)).le
  have h1 := B.t_le_one i.succ
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (riemDist_le_pathLength (N := N)
    (hγ.1.mono h0 hle' h1) fun τ hτ => hγ.2.1 τ ⟨h0.trans hτ.1, hτ.2.trans h1⟩)

/-- **Milnor's Remark after Theorem 16.2** (p. 92): if some path from `p` to `q` has energy `< c`,
then `E'` attains its minimum on the compact non-empty set `B^a`, and the corresponding broken
geodesic minimizes the energy on all of `Ω(N; p, q)`; it is therefore an unbroken geodesic
(a minimum is a critical point, Corollary 12.3).  This is a second proof of the existence of a
geodesic of minimal energy (Hopf–Rinow, 10.9). -/
theorem exists_energy_minimizing {γ₀ : ℝ → V} (hγ₀ : γ₀ ∈ pathSpace N p q)
    (hE₀ : energy γ₀ 0 1 < c) :
    ∃ y ∈ B.nodes, IsUnbrokenGeodesic hN (B.path y) ∧
      ∀ γ ∈ pathSpace N p q, energy (B.path y) 0 1 ≤ energy γ 0 1 := by
  set a := energy γ₀ 0 1
  obtain ⟨hy₁, hy₁a⟩ := B.nodeVal_mem_nodes_of_energy_lt hγ₀ hE₀
  have hK := B.isCompact_sublevel hE₀
  obtain ⟨y, hyK, hmin⟩ := hK.exists_isMinOn ⟨B.nodeVal γ₀, hy₁, hy₁a⟩
    (B.continuousOn_energy'.mono fun y hy => hy.1)
  have hy : y ∈ B.nodes := hyK.1
  have hlow : ∀ γ ∈ pathSpace N p q, energy (B.path y) 0 1 ≤ energy γ 0 1 := by
    intro γ hγ
    rw [B.energy_path hy]
    by_cases hγc : energy γ 0 1 < c
    · obtain ⟨hyγ, hyγE⟩ := B.nodeVal_mem_nodes_of_energy_lt hγ hγc
      by_cases hγa : B.energy' (B.nodeVal γ) ≤ a
      · exact (hmin ⟨hyγ, hγa⟩).trans hyγE
      · exact (hyK.2.trans (le_of_lt (not_le.1 hγa))).trans hyγE
    · exact hyK.2.trans (hE₀.le.trans (not_lt.1 hγc))
  have hγy := B.path_mem_pathSpace hy
  refine ⟨y, hy, ?_, hlow⟩
  rw [← corollary_12_3 hN hγy]
  intro U α Bv hα hαγ
  have hmin' : IsLocalMin (fun u => energy (α u) 0 1) 0 := by
    filter_upwards [hα.isOpen.mem_nhds hα.zero_mem] with u hu
    have hpath := hα.mem_pathSpace hu
    rw [show α 0 0 = p from (hαγ 0 ⟨le_rfl, zero_le_one⟩).trans hγy.2.2.1,
      show α 0 1 = q from (hαγ 1 ⟨zero_le_one, le_rfl⟩).trans hγy.2.2.2] at hpath
    calc energy (α 0) 0 1 = energy (B.path y) 0 1 := energy_congr hαγ
      _ ≤ energy (α u) 0 1 := hlow _ hpath
  have hd := hα.hasDerivAt_energy hN hα.zero_mem
  rw [hmin'.hasDerivAt_eq_zero hd] at hd
  exact hd

end BrokenSetup

end Morse
