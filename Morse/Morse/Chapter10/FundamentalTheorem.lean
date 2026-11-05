import Morse.Chapter10.RelativeCells
import Morse.Chapter10.Omega
import Morse.Chapter9.IndexTheorem
import Morse.Chapter11.NonConjugate

/-!
Milnor, *Morse Theory*, §17, pp. 95–96: **Theorem 17.3, the fundamental theorem of Morse theory**,
for a submanifold `N ⊆ ℝᴷ`, closed in `ℝᴷ` (so complete), with the induced metric.

# The fundamental theorem of Morse theory

## Milnor's text, paraphrased

**Theorem 17.3** (p. 95).  If `M` is complete and `p, q ∈ M` are not conjugate along any geodesic,
then `Ω(M; p, q)` has the homotopy type of a countable CW-complex with one cell of dimension `λ`
for each geodesic from `p` to `q` of index `λ`.  *Proof* (pp. 95–96): by 16.3 the critical values
of `E` are discrete; choose levels `a₀ < a₁ < ⋯`, not critical values, with one critical value in
each interval; by 16.3, and "just as in the proof of 3.5", there are CW-complexes `K₀ ⊂ K₁ ⊂ ⋯`
and homotopy equivalences `Ω^{a_i} → K_i`, each extending the previous one; the limit map
`Ω → K = ⋃ K_i` induces isomorphisms of homotopy groups (compact sets lie in some `Ω^{a_i}`), so by
Whitehead's theorem and 17.2 it is a homotopy equivalence.  (p. 150: alternatively, Theorem A of
the Appendix applies directly.)

## In the embedded setting

* `Morse.PathSp.energyC`: the energy `E : Ω → ℝ`, continuous for Milnor's metric.
* `Morse.BrokenSetup.isRelCellComplexType_nodes`, `Morse.BrokenSetup.isRelCellComplexType_Omega`:
  for a manifold of broken geodesics `B` (energy bound `c`) and levels `a ≤ b < c` which are not
  energies of geodesics, **the inclusion `Ω^a → Ω^b` is, up to homotopy, the inclusion of `Ω^a`
  into `Ω^a` with one cell of dimension `λ` attached for each geodesic of energy in `(a, b)` and
  index `λ`**: the relative Theorem 3.5 (`Morse.isRelCellComplexType_sublevel_of_isCompact`) for
  `E'` on `B`, transported along the homotopy equivalences `Ω^t ≃ B^t` of Theorem 16.2, which for
  `t = a` and `t = b` are given by one formula (`Morse.BrokenSetup.omegaEquivNodes`).
* `Morse.BrokenSetup.finite_geodesics`, `Morse.finite_geodesicEnergies`: finitely many geodesics
  below each level.
* `Morse.geodesicIndex`, `Morse.geodesicIndex_eq`: the index of a geodesic as a natural number
  (finite by Theorem 15.1).
* `Morse.theorem_17_3_of_levels`: Theorem 17.3 for any levels `a₀ < 0`, `a₀ ≤ a₁ ≤ ⋯ → ∞`, none
  the energy of a geodesic: the cells of the `(n + 1)`-st stage are those of the geodesics with
  energy in `(a_n, a_{n+1})`, in order of non-decreasing energy.
* `Morse.theorem_17_3`: **Theorem 17.3**: if `N` is closed in `V` and every geodesic from `p` to
  `q` is non-degenerate, there are lists `geo n` of geodesics from `p` to `q` such that every
  geodesic agrees on `[0, 1]` with exactly one entry of exactly one list, and `Ω(N; p, q)` has the
  homotopy type of the countable cell complex (`Morse.IsCountableCellComplexType`) whose cells are
  of the dimensions the indices of the entries of `geo 0`, `geo 1`, …: **one cell of dimension `λ`
  for each geodesic of index `λ`**, attached in order of increasing energy.
* `Morse.theorem_17_3_nonconj`: the same under Milnor's hypothesis, `q` not conjugate to `p` along
  any geodesic (non-degeneracy by Theorem 14.1).

## What Milnor leaves implicit (see Exposition/Chapter10.md, §6)

* **The levels.**  `a_i → ∞` is needed for `Ω = ⋃ Ω^{a_i}`, and "precisely one critical value" in
  each interval is impossible when there are finitely many geodesics.  Here an interval may
  contain any finite number of critical values: the relative Theorem 3.5 attaches their cells in
  order of energy.
* **The compatible tower.**  Strict compatibility ("each extending the previous one") is not
  needed: the Appendix's comparison of telescopes works with homotopy-commutative squares, which
  is what Lemma 3.7 produces (`Morse/Chapter10/RelativeCells.lean`).  Each inclusion
  `Ω^{a_i} → Ω^{a_{i+1}}` is analysed with its own manifold of broken geodesics (energy bound
  `c > a_{i+1}`); no nested subdivisions are needed (compare Lemma 17.E of the exposition).
* **Weak equivalence and CW type.**  Milnor's main route needs Whitehead's theorem and
  Corollary 17.2 (which rests on 17.1, whose printed proof has a gap); this formalization takes his
  second route, Theorem A of the Appendix through the mapping telescope
  (`Morse.isCountableCellComplexType_of_tower`), which needs neither.
* **"Countable CW-complex".**  The cell complex is the mapping telescope of a tower of iterated
  adjunction spaces (`Morse.IsCountableCellComplexType`); attaching maps are not made cellular
  (cellular approximation is not in Mathlib), see `Morse/Chapter2/CWType.lean`.
* **Geodesics are counted by their values on `[0, 1]`**: paths are functions on `ℝ`, and the
  broken geodesics representing the cells agree with the given geodesics on `[0, 1]`.
* **Completeness** is used only through the compactness of the balls `{x : ρ(p, x) ≤ r}`, which
  holds for `N` closed in `V`; connectedness is not needed.
-/

open Set Filter Topology Function Module Metric MeasureTheory
open scoped ContDiff Manifold RealInnerProductSpace ENNReal Interval NNReal

universe u

noncomputable section

namespace Morse

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

namespace PathSp

variable (N) in
/-- **The energy `E : Ω → ℝ`** (Milnor p. 70), continuous for Milnor's metric (p. 88). -/
def energyC (p q : V) : C(PathSp N p q, ℝ) :=
  ⟨fun γ => energy γ 0 1, continuous_energy le_rfl zero_le_one le_rfl⟩

omit [FiniteDimensional ℝ V] in
@[simp]
theorem energyC_apply {p q : V} (γ : PathSp N p q) : energyC N p q γ = energy γ 0 1 := rfl

end PathSp

namespace BrokenSetup

variable {p q : V} {c : ℝ} {m : ℕ} (B : BrokenSetup hN p q c m)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- `B^a ⊆ B^b` for `a ≤ b`, in the space of break points. -/
theorem nodesSublevel_mono {a b : ℝ} (hab : a ≤ b) :
    {y | y ∈ B.nodes ∧ B.energy' y ≤ a} ⊆ {y | y ∈ B.nodes ∧ B.energy' y ≤ b} :=
  fun _ hy => ⟨hy.1, hy.2.trans hab⟩

/-- **The relative Theorem 16.3 in the space of break points**: for levels `a ≤ b < c` which are
not energies of geodesics, with every geodesic of energy `≤ b` non-degenerate, the geodesics with
energy in `(a, b)` are finitely many — their break points form a list `ys`, in order of
non-decreasing energy — and the inclusion `B^a → B^b` is, up to homotopy, the inclusion of `B^a`
into `B^a` with one cell of dimension `index(γ)` attached for each of them. -/
theorem isRelCellComplexType_nodes {a b : ℝ} (hab : a ≤ b) (hb : b < c)
    (hreg : ∀ y ∈ B.nodes, IsUnbrokenGeodesic hN (B.path y) → B.energy' y ≠ a ∧ B.energy' y ≠ b)
    (hnd : ∀ y (hy : y ∈ B.nodes), IsUnbrokenGeodesic hN (B.path y) → B.energy' y ≤ b →
      hessNullity hN (B.path_mem_pathSpace hy) = 0) :
    ∃ ys : List (Fin m → V), ys.Nodup ∧
      (∀ y, y ∈ ys ↔ y ∈ B.nodes ∧ IsUnbrokenGeodesic hN (B.path y) ∧ a < B.energy' y ∧
        B.energy' y < b) ∧
      ys.Pairwise (fun y y' => B.energy' y ≤ B.energy' y') ∧
      IsRelCellComplexType (inclC (B.nodesSublevel_mono hab)) (ys.map B.geodIndex) := by
  classical
  set c₁ := (b + c) / 2 with hc₁
  have hbc₁ : b < c₁ := by linarith
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
  -- the sublevel set of `F|S` at `t ≤ b` is `B^t`
  have hmemS : ∀ {t : ℝ}, t ≤ b → ∀ y, y ∈ B.nodes → B.energy' y ≤ t → y ∈ S := fun ht y hy hyt =>
    (hSmem y).2 ⟨hy, by linarith⟩
  have hBt : Subtype.val '' ((F ∘ Subtype.val : S → ℝ) ⁻¹' Iic b) =
      {y | y ∈ B.nodes ∧ B.energy' y ≤ b} := by
    ext y
    simp only [mem_image, mem_preimage, Function.comp_apply, mem_Iic, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨y, hy⟩, hya, rfl⟩
      exact ⟨hOU hy, by rw [← hFE' y hy]; exact hya⟩
    · rintro ⟨hy, hya⟩
      have hyS : y ∈ S := hmemS le_rfl y hy hya
      exact ⟨⟨y, hyS⟩, by rw [hFE' y hyS]; exact hya, rfl⟩
  have hK : IsCompact ((F ∘ Subtype.val : S → ℝ) ⁻¹' Iic b) := by
    rw [Topology.IsInducing.subtypeVal.isCompact_iff, hBt]
    exact B.isCompact_sublevel hb
  have hcrit : ∀ y : S, IsCriticalPointM (Fin m → Z) (F ∘ Subtype.val) y ↔
      IsUnbrokenGeodesic hN (B.path y) := fun y => B.isCriticalPointM_iff hO hOU hF hFE' y
  have hnd' : ∀ y : S, IsCriticalPointM (Fin m → Z) (F ∘ Subtype.val) y → F y ≤ b →
      IsNondegenerate (hessianM (Fin m → Z) (F ∘ Subtype.val) y) := by
    intro y hy hya
    have hgeo := (hcrit y).1 hy
    have h0 := hnd y (hOU y.2) hgeo (by rw [← hFE' y y.2]; exact hya)
    rw [isNondegenerate_iff_nullity_eq_zero]
    have := (B.theorem_16_2_index hO hOU hF hFE' y hgeo).2
    rw [nullityM] at this
    rw [this, h0]
  have hreg' : ∀ t, t = a ∨ t = b → ∀ y : S, IsCriticalPointM (Fin m → Z) (F ∘ Subtype.val) y →
      F y ≠ t := by
    intro t ht y hy
    rw [hFE' y y.2]
    rcases ht with rfl | rfl
    · exact (hreg y (hOU y.2) ((hcrit y).1 hy)).1
    · exact (hreg y (hOU y.2) ((hcrit y).1 hy)).2
  obtain ⟨ps, hpsnd, hpsmem, hpssort, hcell⟩ :=
    isRelCellComplexType_sublevel_of_isCompact hSm hF hK hnd' hab (hreg' a (Or.inl rfl))
      (hreg' b (Or.inr rfl))
  -- the indices
  have hidx : ∀ y ∈ ps, indexM (Fin m → Z) (F ∘ Subtype.val) y = B.geodIndex y := by
    intro y hy
    have hgeo := (hcrit y).1 ((hpsmem y).1 hy).1
    have h1 := (B.theorem_16_2_index hO hOU hF hFE' y hgeo).1
    rw [geodIndex, dif_pos (hOU y.2), ← h1]
    rfl
  refine ⟨ps.map Subtype.val, hpsnd.map Subtype.val_injective, fun y => ?_, ?_, ?_⟩
  · simp only [List.mem_map]
    constructor
    · rintro ⟨y', hy', rfl⟩
      obtain ⟨hc, hlt, hgt⟩ := (hpsmem y').1 hy'
      exact ⟨hOU y'.2, (hcrit y').1 hc, by rw [← hFE' y' y'.2]; exact hlt,
        by rw [← hFE' y' y'.2]; exact hgt⟩
    · rintro ⟨hy, hgeo, hya, hyb⟩
      have hyS : y ∈ S := hmemS le_rfl y hy hyb.le
      refine ⟨⟨y, hyS⟩, (hpsmem _).2 ⟨(hcrit ⟨y, hyS⟩).2 hgeo, ?_, ?_⟩, rfl⟩
      · change a < F y
        rw [hFE' y hyS]
        exact hya
      · change F y < b
        rw [hFE' y hyS]
        exact hyb
  · refine List.Pairwise.map _ (fun y y' h => ?_) hpssort
    rw [← hFE' y y.2, ← hFE' y' y'.2]
    exact h
  · -- transport along the identifications `B^t ≃ (F|S)^t`
    have hmap : ps.map (indexM (Fin m → Z) (F ∘ Subtype.val)) =
        (ps.map Subtype.val).map B.geodIndex := by
      rw [List.map_map]
      exact List.map_congr_left fun y hy => hidx y hy
    rw [← hmap]
    let e : ∀ t, t ≤ b → ↥{y | y ∈ B.nodes ∧ B.energy' y ≤ t} ≃ₜ
        ↥(sublevel (F ∘ Subtype.val : S → ℝ) t) := fun t ht =>
      { toFun := fun y => ⟨⟨y.1, hmemS ht y.1 y.2.1 y.2.2⟩, by
          change F y.1 ≤ t
          rw [hFE' y.1 (hmemS ht y.1 y.2.1 y.2.2)]
          exact y.2.2⟩
        invFun := fun y => ⟨y.1.1, hOU y.1.2, by
          have h2 : F y.1.1 ≤ t := y.2
          rwa [hFE' _ y.1.2] at h2⟩
        left_inv := fun y => rfl
        right_inv := fun y => rfl
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    refine hcell.of_square (e a hab).toHomotopyEquiv (e b le_rfl).toHomotopyEquiv ?_
    have : ((e b le_rfl).toHomotopyEquiv.toFun.comp (inclC (B.nodesSublevel_mono hab))) =
        (inclC (sublevel_mono (F ∘ Subtype.val : S → ℝ) hab)).comp
          (e a hab).toHomotopyEquiv.toFun := rfl
    rw [this]

/-- `Ω^a ≃ B^a`, `B^a` in the space of break points: Milnor's retraction followed by the break
points, `γ ↦ (r_1 γ)(t₁, …, t_m)`, a formula independent of `a`. -/
def omegaEquivNodes {a : ℝ} (ha : a < c) :
    ContinuousMap.HomotopyEquiv ↥(sublevel (PathSp.energyC N p q) a)
      ↥{y | y ∈ B.nodes ∧ B.energy' y ≤ a} :=
  (B.homotopyEquivBroken ha).trans (B.homotopyEquivNodes a)

theorem omegaEquivNodes_apply {a : ℝ} (ha : a < c) (γ : ↥(sublevel (PathSp.energyC N p q) a)) :
    (B.omegaEquivNodes ha γ : Fin m → V) = B.nodeVal (B.deform 1 γ.1) := rfl

/-- **The relative Theorem 16.3 for `Ω`** (the step of Milnor's proof of 17.3, p. 95): as
`Morse.BrokenSetup.isRelCellComplexType_nodes`, for the inclusion `Ω^a → Ω^b` of sublevel sets of
the energy on `Ω` with Milnor's metric. -/
theorem isRelCellComplexType_Omega {a b : ℝ} (hab : a ≤ b) (hb : b < c)
    (hreg : ∀ y ∈ B.nodes, IsUnbrokenGeodesic hN (B.path y) → B.energy' y ≠ a ∧ B.energy' y ≠ b)
    (hnd : ∀ y (hy : y ∈ B.nodes), IsUnbrokenGeodesic hN (B.path y) → B.energy' y ≤ b →
      hessNullity hN (B.path_mem_pathSpace hy) = 0) :
    ∃ ys : List (Fin m → V), ys.Nodup ∧
      (∀ y, y ∈ ys ↔ y ∈ B.nodes ∧ IsUnbrokenGeodesic hN (B.path y) ∧ a < B.energy' y ∧
        B.energy' y < b) ∧
      ys.Pairwise (fun y y' => B.energy' y ≤ B.energy' y') ∧
      IsRelCellComplexType (inclC (sublevel_mono (PathSp.energyC N p q) hab))
        (ys.map B.geodIndex) := by
  obtain ⟨ys, h1, h2, h3, h4⟩ := B.isRelCellComplexType_nodes hab hb hreg hnd
  refine ⟨ys, h1, h2, h3, h4.of_square (B.omegaEquivNodes (lt_of_le_of_lt hab hb))
    (B.omegaEquivNodes hb) ?_⟩
  have : ((B.omegaEquivNodes hb).toFun.comp (inclC (sublevel_mono (PathSp.energyC N p q) hab))) =
      (inclC (B.nodesSublevel_mono hab)).comp (B.omegaEquivNodes (lt_of_le_of_lt hab hb)).toFun :=
    rfl
  rw [this]

/-- **Finitely many geodesics below each level** (Theorem 16.3, "in particular"): if every geodesic
from `p` to `q` of energy `≤ b < c` is non-degenerate, there are finitely many of them (the
critical points of `E'` in the compact `B^b` are isolated). -/
theorem finite_geodesics {b : ℝ} (hb : b < c)
    (hnd : ∀ y (hy : y ∈ B.nodes), IsUnbrokenGeodesic hN (B.path y) → B.energy' y ≤ b →
      hessNullity hN (B.path_mem_pathSpace hy) = 0) :
    {y | y ∈ B.nodes ∧ IsUnbrokenGeodesic hN (B.path y) ∧ B.energy' y ≤ b}.Finite := by
  classical
  set c₁ := (b + c) / 2 with hc₁
  have hbc₁ : b < c₁ := by linarith
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
  have := hSm.isManifold
  have hBt : Subtype.val '' ((F ∘ Subtype.val : S → ℝ) ⁻¹' Iic b) =
      {y | y ∈ B.nodes ∧ B.energy' y ≤ b} := by
    ext y
    simp only [mem_image, mem_preimage, Function.comp_apply, mem_Iic, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨y, hy⟩, hya, rfl⟩
      exact ⟨hOU hy, by rw [← hFE' y hy]; exact hya⟩
    · rintro ⟨hy, hya⟩
      have hyS : y ∈ S := (hSmem y).2 ⟨hy, by linarith⟩
      exact ⟨⟨y, hyS⟩, by rw [hFE' y hyS]; exact hya, rfl⟩
  have hK : IsCompact ((F ∘ Subtype.val : S → ℝ) ⁻¹' Iic b) := by
    rw [Topology.IsInducing.subtypeVal.isCompact_iff, hBt]
    exact B.isCompact_sublevel hb
  have hcrit : ∀ y : S, IsCriticalPointM (Fin m → Z) (F ∘ Subtype.val) y ↔
      IsUnbrokenGeodesic hN (B.path y) := fun y => B.isCriticalPointM_iff hO hOU hF hFE' y
  have hfs : ContMDiff 𝓘(ℝ, Fin m → Z) 𝓘(ℝ, ℝ) ∞ (F ∘ Subtype.val : S → ℝ) :=
    contMDiff_comp_val hSm hF
  have hfin : ((F ∘ Subtype.val : S → ℝ) ⁻¹' Iic b ∩
      {y | IsCriticalPointM (Fin m → Z) (F ∘ Subtype.val) y}).Finite := by
    have hC : IsCompact ((F ∘ Subtype.val : S → ℝ) ⁻¹' Iic b ∩
        {y | IsCriticalPointM (Fin m → Z) (F ∘ Subtype.val) y}) :=
      hK.inter_right (isClosed_setOf_isCriticalPointM (hfs.of_le (by norm_cast)))
    have hD : IsDiscrete ((F ∘ Subtype.val : S → ℝ) ⁻¹' Iic b ∩
        {y | IsCriticalPointM (Fin m → Z) (F ∘ Subtype.val) y}) := by
      refine isDiscrete_inter_setOf_isCriticalPointM (fun x _ => (hfs x).of_le (by norm_cast))
        fun y hy hc => ?_
      have hgeo := (hcrit y).1 hc
      have h0 := hnd y (hOU y.2) hgeo (by rw [← hFE' y y.2]; exact hy)
      rw [isNondegenerate_iff_nullity_eq_zero]
      have := (B.theorem_16_2_index hO hOU hF hFE' y hgeo).2
      rw [nullityM] at this
      rw [this, h0]
    exact hC.finite hD
  refine (hfin.image Subtype.val).subset ?_
  rintro y ⟨hy, hgeo, hyb⟩
  have hyS : y ∈ S := (hSmem y).2 ⟨hy, by linarith⟩
  exact ⟨⟨y, hyS⟩, ⟨by change F y ≤ b; rw [hFE' y hyS]; exact hyb, (hcrit ⟨y, hyS⟩).2 hgeo⟩, rfl⟩

/-- A broken geodesic is determined by its values on `[0, 1]`. -/
theorem eq_of_eqOn_path {y y' : Fin m → V} (hy : y ∈ B.nodes) (hy' : y' ∈ B.nodes)
    (h : EqOn (B.path y) (B.path y') (Icc 0 1)) : y = y' := by
  rw [← B.nodeVal_path hy, ← B.nodeVal_path hy']
  funext j
  exact h ⟨B.t_nonneg _, B.t_le_one _⟩

end BrokenSetup

open Classical in
variable (hN) in
/-- **The index of a geodesic** `γ ∈ Ω(N; p, q)`, as a natural number: the index of `E_**` at `γ`
(finite for a geodesic, by Theorem 15.1; `0` if `γ ∉ Ω`). -/
def geodesicIndex (p q : V) (γ : ℝ → V) : ℕ :=
  if h : γ ∈ pathSpace N p q then (formIndex (energyHessian hN h)).toNat else 0

/-- The index of a geodesic is finite (Theorem 15.1), so `Morse.geodesicIndex` is the index. -/
theorem geodesicIndex_eq {p q : V} {γ : ℝ → V} (hγ : γ ∈ pathSpace N p q)
    (hgeo : IsUnbrokenGeodesic hN γ) :
    (geodesicIndex hN p q γ : ℕ∞) = formIndex (energyHessian hN hγ) := by
  rw [geodesicIndex, dif_pos hγ, (theorem_15_1 hN hγ hgeo).2, ENat.toNat_natCast]

theorem BrokenSetup.geodIndex_eq_geodesicIndex {p q : V} {c : ℝ} {m : ℕ}
    (B : BrokenSetup hN p q c m) {y : Fin m → V} (hy : y ∈ B.nodes) :
    B.geodIndex y = geodesicIndex hN p q (B.path y) := by
  rw [BrokenSetup.geodIndex, dif_pos hy, geodesicIndex, dif_pos (B.path_mem_pathSpace hy)]

/-- **Theorem 17.3 with given levels** (Milnor p. 95): let `N` be closed in `V`, every geodesic
from `p` to `q` non-degenerate, and `a₀ < 0`, `a₀ ≤ a₁ ≤ ⋯ → ∞` levels none of which is the energy
of a geodesic.  Then there are lists `geo (n + 1)` of the geodesics with energy in
`(a_n, a_{n+1})` (each geodesic in that range agreeing on `[0, 1]` with exactly one entry, in
order of non-decreasing energy), and `Ω(N; p, q)` has the homotopy type of the countable cell
complex with the cells of dimension `index(γ)`, `γ` in `geo 1`, then `geo 2`, …. -/
theorem theorem_17_3_of_levels (hcl : IsClosed N) {p q : V} (hp : p ∈ N) (hq : q ∈ N)
    (hnd : ∀ γ (hγ : γ ∈ pathSpace N p q), IsUnbrokenGeodesic hN γ → hessNullity hN hγ = 0)
    {a : ℕ → ℝ} (ha : Monotone a) (ha' : Tendsto a atTop atTop) (ha0 : a 0 < 0)
    (hreg : ∀ n, ∀ γ ∈ pathSpace N p q, IsUnbrokenGeodesic hN γ → energy γ 0 1 ≠ a n) :
    ∃ geo : ℕ → List (ℝ → V), geo 0 = [] ∧
      (∀ n, ∀ γ ∈ geo (n + 1), γ ∈ pathSpace N p q ∧ IsUnbrokenGeodesic hN γ ∧
        a n < energy γ 0 1 ∧ energy γ 0 1 < a (n + 1)) ∧
      (∀ n, ∀ γ ∈ pathSpace N p q, IsUnbrokenGeodesic hN γ → a n < energy γ 0 1 →
        energy γ 0 1 < a (n + 1) → ∃ γ' ∈ geo (n + 1), EqOn γ' γ (Icc 0 1)) ∧
      (∀ n, (geo n).Pairwise fun γ γ' => ¬ EqOn γ γ' (Icc 0 1)) ∧
      (∀ n, (geo n).Pairwise fun γ γ' => energy γ 0 1 ≤ energy γ' 0 1) ∧
      IsCountableCellComplexType (PathSp N p q) fun n => (geo n).map (geodesicIndex hN p q) := by
  classical
  set E := PathSp.energyC N p q with hE_def
  have hE0 : ∀ γ : ℝ → V, 0 ≤ energy γ 0 1 := fun γ => PathSp.energy_nonneg_of_le zero_le_one
  -- a manifold of broken geodesics for each level
  have hB : ∀ n, ∃ m, Nonempty (BrokenSetup hN p q (max (a (n + 1)) 0 + 1) m) := fun n =>
    exists_brokenSetup_uniform hN hp hq (by positivity)
      (isCompact_closedRiemBall_of_isClosed hN hcl p _)
  choose m hm using hB
  let B : ∀ n, BrokenSetup hN p q (max (a (n + 1)) 0 + 1) (m n) := fun n => (hm n).some
  have hlt : ∀ n, a (n + 1) < max (a (n + 1)) 0 + 1 := fun n => by
    linarith [le_max_left (a (n + 1)) 0]
  -- the relative cell structure of each inclusion `Ω^{a_n} ⊆ Ω^{a_{n+1}}`
  have hrel : ∀ n, ∃ ys : List (Fin (m n) → V), ys.Nodup ∧
      (∀ y, y ∈ ys ↔ y ∈ (B n).nodes ∧ IsUnbrokenGeodesic hN ((B n).path y) ∧
        a n < (B n).energy' y ∧ (B n).energy' y < a (n + 1)) ∧
      ys.Pairwise (fun y y' => (B n).energy' y ≤ (B n).energy' y') ∧
      IsRelCellComplexType (inclC (sublevel_mono E (ha (Nat.le_succ n))))
        (ys.map (B n).geodIndex) := fun n =>
    (B n).isRelCellComplexType_Omega (ha (Nat.le_succ n)) (hlt n)
      (fun y hy hgeo => by
        rw [← (B n).energy_path hy]
        exact ⟨hreg n _ ((B n).path_mem_pathSpace hy) hgeo,
          hreg (n + 1) _ ((B n).path_mem_pathSpace hy) hgeo⟩)
      (fun y hy hgeo _ => hnd _ _ hgeo)
  choose ys hys_nd hys_mem hys_sort hys_cell using hrel
  let geo : ℕ → List (ℝ → V) := fun n => match n with
    | 0 => []
    | n + 1 => (ys n).map (B n).path
  have hgeo0 : geo 0 = [] := rfl
  have hgeoS : ∀ n, geo (n + 1) = (ys n).map (B n).path := fun n => rfl
  have hmemS : ∀ n γ, γ ∈ geo (n + 1) ↔ ∃ y ∈ ys n, (B n).path y = γ := fun n γ => by
    rw [hgeoS, List.mem_map]
  refine ⟨geo, hgeo0, fun n γ hγ => ?_, fun n γ hγ hgeo h1 h2 => ?_, fun n => ?_, fun n => ?_, ?_⟩
  · obtain ⟨y, hy, rfl⟩ := (hmemS n γ).1 hγ
    obtain ⟨hyN, hgeo, h1, h2⟩ := (hys_mem n y).1 hy
    refine ⟨(B n).path_mem_pathSpace hyN, hgeo, ?_, ?_⟩ <;> rw [(B n).energy_path hyN]
    exacts [h1, h2]
  · obtain ⟨hy, heq, hgeo', hE⟩ := (B n).eqOn_path_nodeVal_of_isUnbrokenGeodesic hγ hgeo
      (lt_trans h2 (hlt n))
    refine ⟨(B n).path ((B n).nodeVal γ), (hmemS n _).2 ⟨_, (hys_mem n _).2
      ⟨hy, hgeo', by rw [hE]; exact h1, by rw [hE]; exact h2⟩, rfl⟩, heq⟩
  · cases n with
    | zero => exact List.Pairwise.nil
    | succ n =>
      rw [hgeoS, List.pairwise_map]
      refine (hys_nd n).imp_of_mem fun {y y'} hy hy' hne heq => hne ?_
      exact (B n).eq_of_eqOn_path ((hys_mem n y).1 hy).1 ((hys_mem n y').1 hy').1 heq
  · cases n with
    | zero => exact List.Pairwise.nil
    | succ n =>
      rw [hgeoS, List.pairwise_map]
      refine (hys_sort n).imp_of_mem fun {y y'} hy hy' hle => ?_
      rwa [(B n).energy_path ((hys_mem n y).1 hy).1, (B n).energy_path ((hys_mem n y').1 hy').1]
  · refine isCountableCellComplexType_of_relSublevel E ha ha' ?_ fun n => ?_
    · have : IsEmpty ↥(sublevel E (a 0)) :=
        ⟨fun γ => by
          have h1 : energy (γ.1 : ℝ → V) 0 1 ≤ a 0 := γ.2
          linarith [hE0 γ.1]⟩
      exact IsFiniteCellComplexType.of_isEmpty _
    · have hcells : (geo (n + 1)).map (geodesicIndex hN p q) = (ys n).map (B n).geodIndex := by
        rw [hgeoS, List.map_map]
        exact (List.map_congr_left fun y hy =>
          ((B n).geodIndex_eq_geodesicIndex ((hys_mem n y).1 hy).1).symm)
      rw [hcells]
      exact hys_cell n

/-- If `c` is not a value of `a` and `a 0 < c < a n`, then `c` lies in some
`(a k, a (k + 1))`. -/
theorem exists_mem_Ioo_succ_of_lt {a : ℕ → ℝ} {n : ℕ} {c : ℝ} (h0 : a 0 < c) (hn : c < a n)
    (hne : ∀ k, a k ≠ c) : ∃ k, a k < c ∧ c < a (k + 1) := by
  classical
  have hex : ∃ j, c < a j := ⟨n, hn⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (fun h : Nat.find hex = 0 ↦ by
    have := Nat.find_spec hex
    rw [h] at this
    linarith)
  refine ⟨k, ?_, ?_⟩
  · exact lt_of_le_of_ne (not_lt.1 (Nat.find_min hex (show k < Nat.find hex by omega))) (hne k)
  · have := Nat.find_spec hex
    rwa [hk] at this

/-- **The energies of the geodesics below any level are finitely many** (Theorem 16.3), when all
geodesics from `p` to `q` are non-degenerate and `N` is closed in `V` (complete). -/
theorem finite_geodesicEnergies (hcl : IsClosed N) {p q : V} (hp : p ∈ N) (hq : q ∈ N)
    (hnd : ∀ γ (hγ : γ ∈ pathSpace N p q), IsUnbrokenGeodesic hN γ → hessNullity hN hγ = 0)
    (b : ℝ) :
    {e | ∃ γ ∈ pathSpace N p q, IsUnbrokenGeodesic hN γ ∧ energy γ 0 1 = e ∧ e ≤ b}.Finite := by
  obtain ⟨m, ⟨B⟩⟩ := exists_brokenSetup_uniform hN hp hq (c := max b 0 + 1) (by positivity)
    (isCompact_closedRiemBall_of_isClosed hN hcl p _)
  have hbc : b < max b 0 + 1 := by linarith [le_max_left b 0]
  refine ((B.finite_geodesics hbc (fun y hy hgeo _ => hnd _ _ hgeo)).image B.energy').subset ?_
  rintro e ⟨γ, hγ, hgeo, rfl, hb⟩
  obtain ⟨hy, -, hgeo', hE⟩ := B.eqOn_path_nodeVal_of_isUnbrokenGeodesic hγ hgeo
    (lt_of_le_of_lt hb hbc)
  exact ⟨B.nodeVal γ, ⟨hy, hgeo', hE ▸ hb⟩, hE⟩

/-- **Theorem 17.3, the fundamental theorem of Morse theory** (Milnor p. 95), for `N ⊆ V` closed
(complete): if every geodesic from `p` to `q` is non-degenerate (`p`, `q` not conjugate along any
geodesic), there are lists `geo 0, geo 1, …` of geodesics from `p` to `q` such that every geodesic
from `p` to `q` agrees on `[0, 1]` with an entry of exactly one list, the entries of each list are
distinct on `[0, 1]`, the energies increase from one list to the next and weakly within each list,
and `Ω(N; p, q)`, with Milnor's metric, has the homotopy type of the countable cell complex with
cells of dimensions the indices of the entries of `geo 0`, then `geo 1`, …: one cell of dimension
`λ` for each geodesic of index `λ`. -/
theorem theorem_17_3 (hcl : IsClosed N) {p q : V} (hp : p ∈ N) (hq : q ∈ N)
    (hnd : ∀ γ (hγ : γ ∈ pathSpace N p q), IsUnbrokenGeodesic hN γ → hessNullity hN hγ = 0) :
    ∃ geo : ℕ → List (ℝ → V),
      (∀ n, ∀ γ ∈ geo n, γ ∈ pathSpace N p q ∧ IsUnbrokenGeodesic hN γ) ∧
      (∀ γ ∈ pathSpace N p q, IsUnbrokenGeodesic hN γ → ∃ n, ∃ γ' ∈ geo n, EqOn γ' γ (Icc 0 1)) ∧
      (∀ n n', ∀ γ ∈ geo n, ∀ γ' ∈ geo n', EqOn γ γ' (Icc 0 1) → n = n') ∧
      (∀ n, (geo n).Pairwise fun γ γ' => ¬ EqOn γ γ' (Icc 0 1)) ∧
      (∀ n n', n < n' → ∀ γ ∈ geo n, ∀ γ' ∈ geo n', energy γ 0 1 < energy γ' 0 1) ∧
      (∀ n, (geo n).Pairwise fun γ γ' => energy γ 0 1 ≤ energy γ' 0 1) ∧
      IsCountableCellComplexType (PathSp N p q) fun n => (geo n).map (geodesicIndex hN p q) := by
  classical
  have hE0 : ∀ γ : ℝ → V, 0 ≤ energy γ 0 1 := fun γ => PathSp.energy_nonneg_of_le zero_le_one
  -- regular levels `a_{n+1} ∈ (n, n + 1)`
  have hlev : ∀ n : ℕ, ∃ x ∈ Ioo (n : ℝ) (n + 1), x ∉ {e | ∃ γ ∈ pathSpace N p q,
      IsUnbrokenGeodesic hN γ ∧ energy γ 0 1 = e ∧ e ≤ n + 1} := fun n =>
    ((Ioo_infinite (by linarith : (n : ℝ) < n + 1)).sdiff
      (finite_geodesicEnergies hcl hp hq hnd (n + 1))).nonempty
  choose x hx hxreg using hlev
  let a : ℕ → ℝ := fun n => match n with
    | 0 => -1
    | n + 1 => x n
  have ha0 : a 0 = -1 := rfl
  have haS : ∀ n, a (n + 1) = x n := fun n => rfl
  have ha_gt : ∀ n : ℕ, (n : ℝ) - 1 ≤ a n := by
    intro n
    cases n with
    | zero => simp [ha0]
    | succ n => rw [haS]; push_cast; linarith [(hx n).1]
  have ha_lt : ∀ n, a n < n := by
    intro n
    cases n with
    | zero => simp [ha0]
    | succ n => rw [haS]; push_cast; exact (hx n).2
  have ha : Monotone a := monotone_nat_of_le_succ fun n => by
    have h1 := ha_lt n
    have h2 := ha_gt (n + 1)
    push_cast at h2
    linarith
  have ha' : Tendsto a atTop atTop :=
    tendsto_atTop_mono ha_gt (tendsto_atTop_add_const_right _ (-1) tendsto_natCast_atTop_atTop)
  have hreg : ∀ n, ∀ γ ∈ pathSpace N p q, IsUnbrokenGeodesic hN γ → energy γ 0 1 ≠ a n := by
    intro n γ hγ hgeo heq
    cases n with
    | zero => linarith [hE0 γ, ha0 ▸ heq]
    | succ n =>
      rw [haS] at heq
      exact hxreg n ⟨γ, hγ, hgeo, heq, (hx n).2.le⟩
  obtain ⟨geo, hgeo0, hmem, hex, hpw, hsort, hcell⟩ :=
    theorem_17_3_of_levels hcl hp hq hnd ha ha' (by rw [ha0]; norm_num) hreg
  -- every geodesic lies in exactly one interval `(a_n, a_{n+1})`
  have hmem' : ∀ n, ∀ γ ∈ geo n, ∃ k, n = k + 1 := fun n γ hγ => by
    cases n with
    | zero => rw [hgeo0] at hγ; exact absurd hγ List.not_mem_nil
    | succ k => exact ⟨k, rfl⟩
  refine ⟨geo, fun n γ hγ => ?_, fun γ hγ hgeo => ?_, fun n n' γ hγ γ' hγ' heq => ?_, hpw,
    fun n n' hnn' γ hγ γ' hγ' => ?_, hsort, hcell⟩
  · obtain ⟨k, rfl⟩ := hmem' n γ hγ
    exact ⟨(hmem k γ hγ).1, (hmem k γ hγ).2.1⟩
  · obtain ⟨K, hK⟩ := exists_nat_gt (energy γ 0 1 + 1)
    obtain ⟨k, hk1, hk2⟩ := exists_mem_Ioo_succ_of_lt (n := K)
      (show a 0 < energy γ 0 1 by rw [ha0]; linarith [hE0 γ])
      (by linarith [ha_gt K]) fun k h => hreg k γ hγ hgeo h.symm
    obtain ⟨γ', hγ', heq⟩ := hex k γ hγ hgeo hk1 hk2
    exact ⟨k + 1, γ', hγ', heq⟩
  · obtain ⟨k, rfl⟩ := hmem' n γ hγ
    obtain ⟨k', rfl⟩ := hmem' n' γ' hγ'
    have hE : energy γ 0 1 = energy γ' 0 1 := energy_congr heq
    obtain ⟨-, -, h1, h2⟩ := hmem k γ hγ
    obtain ⟨-, -, h1', h2'⟩ := hmem k' γ' hγ'
    rw [hE] at h1 h2
    by_contra hne
    rcases lt_or_gt_of_ne (show k ≠ k' by omega) with h | h
    · linarith [ha (show k + 1 ≤ k' by omega)]
    · linarith [ha (show k' + 1 ≤ k by omega)]
  · obtain ⟨k, rfl⟩ := hmem' n γ hγ
    obtain ⟨k', rfl⟩ := hmem' n' γ' hγ'
    obtain ⟨-, -, -, h2⟩ := hmem k γ hγ
    obtain ⟨-, -, h1', -⟩ := hmem k' γ' hγ'
    linarith [ha (show k + 1 ≤ k' by omega)]

/-- **Theorem 17.3 with Milnor's hypothesis** (p. 95): `N` closed in `V` and `q` not conjugate to
`p` along any geodesic (`Morse.conjLocus`; by Corollary 18.2 this holds for almost every `q`). -/
theorem theorem_17_3_nonconj (hcl : IsClosed N) {p q : V} (hp : p ∈ N) (hq : q ∈ N)
    (hnc : q ∉ conjLocus hN p) :
    ∃ geo : ℕ → List (ℝ → V),
      (∀ n, ∀ γ ∈ geo n, γ ∈ pathSpace N p q ∧ IsUnbrokenGeodesic hN γ) ∧
      (∀ γ ∈ pathSpace N p q, IsUnbrokenGeodesic hN γ → ∃ n, ∃ γ' ∈ geo n, EqOn γ' γ (Icc 0 1)) ∧
      (∀ n n', ∀ γ ∈ geo n, ∀ γ' ∈ geo n', EqOn γ γ' (Icc 0 1) → n = n') ∧
      (∀ n, (geo n).Pairwise fun γ γ' => ¬ EqOn γ γ' (Icc 0 1)) ∧
      (∀ n n', n < n' → ∀ γ ∈ geo n, ∀ γ' ∈ geo n', energy γ 0 1 < energy γ' 0 1) ∧
      (∀ n, (geo n).Pairwise fun γ γ' => energy γ 0 1 ≤ energy γ' 0 1) ∧
      IsCountableCellComplexType (PathSp N p q) fun n => (geo n).map (geodesicIndex hN p q) :=
  theorem_17_3 hcl hp hq fun _ hγ hgeo => hessNullity_eq_zero_of_notMem_conjLocus hnc hγ hgeo

end Morse
