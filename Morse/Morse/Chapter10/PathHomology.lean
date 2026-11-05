import Morse.Chapter10.FundamentalTheorem
import Morse.Chapter10.SublevelHomology

/-!
Milnor, *Morse Theory*, §17, p. 96: the homology of the path space read off from its geodesics
(used for `ΩSⁿ`, `n ≥ 3`), for a submanifold `N ⊆ ℝᴷ` closed in `ℝᴷ`, with the induced metric.

# The homology of the path space

## Milnor's text, paraphrased

(p. 96) For `n > 2` the cells of the CW-complex of Corollary 17.4 have dimensions `0, n − 1,
2(n − 1), …`, no two consecutive; so the boundary maps of its cellular chain complex vanish, and
`H_i(ΩSⁿ; ℤ)` is free of rank `1` for `i` a multiple of `n − 1` and `0` otherwise.

## In the embedded setting

The homology is computed from the filtration of `Ω` by the sublevel sets `Ω^a` of the energy,
not from a cellular chain complex (the cell complexes of `Morse.IsCountableCellComplexType` have
non-cellular attaching maps):

* `Morse.BrokenSetup.finrank_subsetHomology_Omega`: **the homology of a slab of `Ω`** (Milnor
  p. 29, in the path space): for regular levels `a ≤ b < c` with at most one critical value in
  `(a, b)`, `H_j(Ω^b, Ω^a; 𝕜)` is finite-dimensional of dimension the number of geodesics with
  energy in `(a, b)` and index `j` — the slab homology of `E'` on the manifold `B` of broken
  geodesics (`Morse.Homology.sublevel_step_of_isCompact`), transported along the pair of homotopy
  equivalences `Ω^t ≃ B^t`, `t = a, b`, which commute with the inclusions.
* `Morse.windowLevels`: levels separating the energies of a sequence of geodesics.
* `Morse.omega_cells_of_unique`: **one cell for each geodesic, one geodesic per window**: if the
  geodesics from `p` to `q` are, up to their values on `[0, 1]`, a sequence `g k` with strictly
  increasing energies tending to `∞`, `g k` of index `d k`, then `Ω(N; p, q)` has the homotopy type
  of the countable cell complex with one cell of dimension `d k` at the stage `k + 1`
  (`Morse.oneCellEach`).
* `Morse.finrank_window`: then `H_j(Ω^{a_{k+1}}, Ω^{a_k}; 𝕜)` is `𝕜` for `j = d k`, else `0`.
* `Morse.bettiNumber_omega_of_unique`: **if moreover `d k = k r` with `r ≥ 2`, the Betti numbers
  of `Ω(N; p, q)` over any field `𝕜` are `1` in the degrees divisible by `r` and `0` otherwise**:
  the lacunary principle (Corollary 5.4, `Morse.eq_of_altSum_le_of_lacunary`) on the finite stages
  `Ω^{a_K}`, and the passage to the union (`Morse.Homology.bettiNumber_eq_of_steps`).

## What Milnor leaves implicit

* **Cellular homology** of the countable complex needs cellular attaching maps; here the
  homology is obtained directly from the Morse filtration of `Ω`, as in Milnor's §5, so the
  cellular structure of the complex of 17.3 is not needed.
* **From the finite stages to `Ω`.**  The homology of `Ω` is the direct limit of that of the
  `Ω^{a_K}`: a singular chain has compact support, and a compact subset of `Ω` lies in some
  `Ω^{a_K}` because the energy is continuous for Milnor's metric (`Morse.PathSp.continuous_energy`);
  in degree `i` the groups stabilize once `K r > i + 1`.
* **Coefficients.**  Milnor computes integral homology; over a field the dimension statement is
  what the lacunary principle gives (the integral statement needs that the free groups do not
  acquire torsion, which follows from the same filtration but is not formalized).
-/

open Set Filter Topology Function Module Metric CategoryTheory
open scoped ContDiff Manifold RealInnerProductSpace ENNReal

universe u

noncomputable section

namespace Morse

open Morse.Homology

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

namespace BrokenSetup

variable {p q : V} {c : ℝ} {m : ℕ} (B : BrokenSetup hN p q c m)

/-- **The homology of a slab of `Ω`** (Milnor p. 29, for the energy on `Ω`): let `a ≤ b < c` be
levels which are not energies of geodesics, every geodesic of energy `≤ b` non-degenerate, and all
the geodesics with energy in `(a, b)` of the same energy.  Then `H_j(Ω^b, Ω^a; 𝕜)` is
finite-dimensional, of dimension the number of these geodesics of index `j` (counted through
their break points). -/
theorem finrank_subsetHomology_Omega {𝕜 : Type u} [Field 𝕜] {a b : ℝ} (hab : a ≤ b) (hb : b < c)
    (hreg : ∀ y ∈ B.nodes, IsUnbrokenGeodesic hN (B.path y) → B.energy' y ≠ a ∧ B.energy' y ≠ b)
    (hnd : ∀ y (hy : y ∈ B.nodes), IsUnbrokenGeodesic hN (B.path y) → B.energy' y ≤ b →
      hessNullity hN (B.path_mem_pathSpace hy) = 0)
    (hone : ∀ y y', y ∈ B.nodes → y' ∈ B.nodes → IsUnbrokenGeodesic hN (B.path y) →
      IsUnbrokenGeodesic hN (B.path y') → a < B.energy' y → B.energy' y < b → a < B.energy' y' →
      B.energy' y' < b → B.energy' y = B.energy' y') (i : ℕ) :
    FiniteDimensional 𝕜 (subsetHomology 𝕜 i (sublevel_mono (PathSp.energyC N p q) hab)) ∧
      finrank 𝕜 (subsetHomology 𝕜 i (sublevel_mono (PathSp.energyC N p q) hab)) =
        {y | y ∈ B.nodes ∧ IsUnbrokenGeodesic hN (B.path y) ∧ a < B.energy' y ∧
          B.energy' y < b ∧ B.geodIndex y = i}.ncard := by
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
  have hfs : ContMDiff 𝓘(ℝ, Fin m → Z) 𝓘(ℝ, ℝ) ∞ (F ∘ Subtype.val : S → ℝ) :=
    contMDiff_comp_val hSm hF
  have hfin : ((F ∘ Subtype.val : S → ℝ) ⁻¹' Iic b ∩
      {y | IsCriticalPointM (Fin m → Z) (F ∘ Subtype.val) y}).Finite := by
    have hC : IsCompact ((F ∘ Subtype.val : S → ℝ) ⁻¹' Iic b ∩
        {y | IsCriticalPointM (Fin m → Z) (F ∘ Subtype.val) y}) :=
      hK.inter_right (isClosed_setOf_isCriticalPointM (hfs.of_le (by norm_cast)))
    have hD : IsDiscrete ((F ∘ Subtype.val : S → ℝ) ⁻¹' Iic b ∩
        {y | IsCriticalPointM (Fin m → Z) (F ∘ Subtype.val) y}) :=
      isDiscrete_inter_setOf_isCriticalPointM (fun x _ => (hfs x).of_le (by norm_cast))
        fun y hy hc => hnd' y hc hy
    exact hC.finite hD
  set P := hfin.toFinset with hP_def
  have hP : ∀ y : S, F y ≤ b → (y ∈ P ↔ IsCriticalPointM (Fin m → Z) (F ∘ Subtype.val) y) :=
    fun y hy => by
      rw [hP_def, Set.Finite.mem_toFinset]
      exact ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩
  have hPmem : ∀ y ∈ P, F y ≤ b ∧ IsCriticalPointM (Fin m → Z) (F ∘ Subtype.val) y :=
    fun y hy => by
      rw [hP_def, Set.Finite.mem_toFinset] at hy
      exact hy
  have hreg' : ∀ y ∈ P, F y ≠ a ∧ F y ≠ b := fun y hy => by
    rw [hFE' y y.2]
    exact hreg y (hOU y.2) ((hcrit y).1 (hPmem y hy).2)
  have hone' : ∀ y ∈ P, ∀ y' ∈ P, a < F y → F y < b → a < F y' → F y' < b → F y = F y' := by
    intro y hy y' hy' h1 h2 h3 h4
    rw [hFE' y y.2, hFE' y' y'.2] at *
    exact hone y y' (hOU y.2) (hOU y'.2) ((hcrit y).1 (hPmem y hy).2)
      ((hcrit y').1 (hPmem y' hy').2) h1 h2 h3 h4
  obtain ⟨hfd, hfr⟩ := sublevel_step_of_isCompact (𝕜 := 𝕜) hSm hF hK hnd' (Homeomorph.refl S)
    hab le_rfl hP (fun y hy => (hreg' y hy).1) (fun y hy => (hreg' y hy).2) hone' i
  -- the identifications `Ω^t ≃ (F|S)^t`, `t = a, b`
  let e : ∀ t, t ≤ b → ↥{y | y ∈ B.nodes ∧ B.energy' y ≤ t} ≃ₜ
      ↥((Homeomorph.refl S) ⁻¹' sublevel (F ∘ Subtype.val : S → ℝ) t) := fun t ht =>
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
  set α := (B.omegaEquivNodes (lt_of_le_of_lt hab hb)).trans (e a hab).toHomotopyEquiv
  set β := (B.omegaEquivNodes hb).trans (e b le_rfl).toHomotopyEquiv
  let φ : subsetPair (sublevel_mono (PathSp.energyC N p q) hab) ⟶
      subsetPair (preimage_mono (f := Homeomorph.refl S)
        (sublevel_mono (F ∘ Subtype.val : S → ℝ) hab)) :=
    TopPair.ofHom (TopCat.ofHom β.toFun) (TopCat.ofHom α.toFun) rfl
  have hiso := isIso_relHomology_map_of_homotopyEquiv (ModuleCat.of 𝕜 𝕜) φ α rfl β rfl i
  let L := (asIso ((relHomology (ModuleCat.of 𝕜 𝕜) i).map φ)).toLinearEquiv
  have hfd' : FiniteDimensional 𝕜 (subsetHomology 𝕜 i (sublevel_mono (PathSp.energyC N p q) hab)) :=
    LinearEquiv.finiteDimensional L.symm
  refine ⟨hfd', L.finrank_eq.trans (hfr.trans ?_)⟩
  -- count the critical points
  rw [← Set.ncard_coe_finset]
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
  congr 1
  ext y
  simp only [Finset.coe_filter, mem_image, mem_ofPred_eq]
  constructor
  · rintro ⟨y', ⟨hy'P, ⟨h1, h2⟩, hidx⟩, rfl⟩
    have hgeo := (hcrit y').1 (hPmem y' hy'P).2
    refine ⟨hOU y'.2, hgeo, by rw [← hFE' y' y'.2]; exact h1, by rw [← hFE' y' y'.2]; exact h2, ?_⟩
    have h3 := (B.theorem_16_2_index hO hOU hF hFE' y' hgeo).1
    rw [geodIndex, dif_pos (hOU y'.2), ← h3, ← hidx]
    rfl
  · rintro ⟨hy, hgeo, h1, h2, hidx⟩
    have hyS : y ∈ S := hmemS le_rfl y hy h2.le
    have hFy : F y = B.energy' y := hFE' y hyS
    have hc : IsCriticalPointM (Fin m → Z) (F ∘ Subtype.val) ⟨y, hyS⟩ := (hcrit ⟨y, hyS⟩).2 hgeo
    refine ⟨⟨y, hyS⟩, ⟨(hP ⟨y, hyS⟩ (by change F y ≤ b; rw [hFy]; exact h2.le)).2 hc,
      ⟨by change a < F y; rw [hFy]; exact h1, by change F y < b; rw [hFy]; exact h2⟩, ?_⟩, rfl⟩
    have h3 := (B.theorem_16_2_index hO hOU hF hFE' ⟨y, hyS⟩ hgeo).1
    rw [geodIndex, dif_pos hy] at hidx
    have h4 : (indexM (Fin m → Z) (F ∘ Subtype.val) ⟨y, hyS⟩ : ℕ∞) = (i : ℕ∞) := by
      rw [h3, ← hidx, ENat.natCast_toNat]
      rw [← h3]
      exact ENat.natCast_ne_top _
    exact_mod_cast h4

end BrokenSetup

/-! ### One geodesic in each window of energies -/

section Windows

variable {p q : V} {g : ℕ → ℝ → V}

/-- The levels between the energies `E_k = E(g_k)` of a sequence of geodesics: `a₀ = −1`,
`a_{k+1} = (E_k + E_{k+1})/2`. -/
def windowLevels (g : ℕ → ℝ → V) : ℕ → ℝ
  | 0 => -1
  | k + 1 => (energy (g k) 0 1 + energy (g (k + 1)) 0 1) / 2

omit [FiniteDimensional ℝ V] in
theorem windowLevels_zero : windowLevels g 0 = -1 := rfl

omit [FiniteDimensional ℝ V] in
theorem windowLevels_succ (k : ℕ) :
    windowLevels g (k + 1) = (energy (g k) 0 1 + energy (g (k + 1)) 0 1) / 2 := rfl

variable (hE : StrictMono fun k => energy (g k) 0 1)
include hE

omit [FiniteDimensional ℝ V] in
theorem lt_windowLevels_succ (k : ℕ) : energy (g k) 0 1 < windowLevels g (k + 1) := by
  rw [windowLevels_succ]
  have := hE (Nat.lt_succ_self k)
  simp only at this
  linarith

omit [FiniteDimensional ℝ V] in
theorem windowLevels_succ_lt (k : ℕ) : windowLevels g (k + 1) < energy (g (k + 1)) 0 1 := by
  rw [windowLevels_succ]
  have := hE (Nat.lt_succ_self k)
  simp only at this
  linarith

omit [FiniteDimensional ℝ V] in
/-- `E_j` lies in the window `(a_k, a_{k+1})` iff `j = k`. -/
theorem mem_window_iff (j k : ℕ) :
    (windowLevels g k < energy (g j) 0 1 ∧ energy (g j) 0 1 < windowLevels g (k + 1)) ↔ j = k := by
  have hE0 : ∀ j, 0 ≤ energy (g j) 0 1 := fun j => PathSp.energy_nonneg_of_le zero_le_one
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hjk
    rcases lt_or_gt_of_ne hjk with h | h
    · -- `j < k`: `E_j ≤ E_{k-1} < a_k`
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have h3 := lt_windowLevels_succ hE k'
      have h4 : energy (g j) 0 1 ≤ energy (g k') 0 1 := hE.monotone (by omega)
      linarith
    · -- `k < j`: `a_{k+1} < E_{k+1} ≤ E_j`
      have h3 := windowLevels_succ_lt hE k
      have h4 : energy (g (k + 1)) 0 1 ≤ energy (g j) 0 1 := hE.monotone (by omega)
      linarith
  · rintro rfl
    refine ⟨?_, lt_windowLevels_succ hE j⟩
    cases j with
    | zero => rw [windowLevels_zero]; linarith [hE0 0]
    | succ j => exact windowLevels_succ_lt hE j

omit [FiniteDimensional ℝ V] in
theorem windowLevels_monotone : Monotone (windowLevels g) := by
  refine monotone_nat_of_le_succ fun k => ?_
  cases k with
  | zero =>
    rw [windowLevels_zero]
    linarith [lt_windowLevels_succ hE 0, PathSp.energy_nonneg_of_le (γ := g 0) zero_le_one]
  | succ k => exact ((windowLevels_succ_lt hE k).trans (lt_windowLevels_succ hE (k + 1))).le

omit [FiniteDimensional ℝ V] in
theorem tendsto_windowLevels (htop : Tendsto (fun k => energy (g k) 0 1) atTop atTop) :
    Tendsto (windowLevels g) atTop atTop := by
  have h : ∀ k, energy (g k) 0 1 ≤ windowLevels g (k + 1) := fun k =>
    (lt_windowLevels_succ hE k).le
  exact (tendsto_add_atTop_iff_nat 1).1 (tendsto_atTop_mono h htop)

end Windows

/-- A list in which no two entries are related by `R`, pairwise, but any two entries are, has at
most one entry. -/
theorem List.eq_singleton_of_pairwise_not {α : Type*} {R : α → α → Prop} {l : List α} {a : α}
    (hR : l.Pairwise fun x y => ¬ R x y) (ha : a ∈ l) (hall : ∀ x ∈ l, ∀ y ∈ l, R x y) :
    l = [a] := by
  match l, hR, ha, hall with
  | [x], _, ha, _ => rw [List.mem_singleton.1 ha]
  | x :: y :: t, hR, _, hall =>
    rw [List.pairwise_cons] at hR
    exact absurd (hall x (List.mem_cons_self ..) y (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (hR.1 y (List.mem_cons_self ..))

/-- The cells of a path space with one geodesic of index `d k` in the `k`-th window: no cell at
stage `0`, one cell of dimension `d k` at stage `k + 1`. -/
def oneCellEach (d : ℕ → ℕ) : ℕ → List ℕ
  | 0 => []
  | k + 1 => [d k]

section Unique

variable {p q : V} {g : ℕ → ℝ → V}

theorem omega_cells_of_unique (hcl : IsClosed N) (hp : p ∈ N) (hq : q ∈ N)
    (hnd : ∀ γ (hγ : γ ∈ pathSpace N p q), IsUnbrokenGeodesic hN γ → hessNullity hN hγ = 0)
    (hg : ∀ k, g k ∈ pathSpace N p q) (hgeo : ∀ k, IsUnbrokenGeodesic hN (g k))
    (hall : ∀ γ ∈ pathSpace N p q, IsUnbrokenGeodesic hN γ → ∃ k, EqOn γ (g k) (Icc 0 1))
    (hE : StrictMono fun k => energy (g k) 0 1)
    (htop : Tendsto (fun k => energy (g k) 0 1) atTop atTop) (d : ℕ → ℕ)
    (hd : ∀ k γ (hγ : γ ∈ pathSpace N p q), IsUnbrokenGeodesic hN γ → EqOn γ (g k) (Icc 0 1) →
      formIndex (energyHessian hN hγ) = d k) :
    IsCountableCellComplexType (PathSp N p q) (oneCellEach d) := by
  have hE0 : ∀ γ : ℝ → V, 0 ≤ energy γ 0 1 := fun γ => PathSp.energy_nonneg_of_le zero_le_one
  have hreg : ∀ n, ∀ γ ∈ pathSpace N p q, IsUnbrokenGeodesic hN γ →
      energy γ 0 1 ≠ windowLevels g n := by
    intro n γ hγ hγg heq
    obtain ⟨j, hj⟩ := hall γ hγ hγg
    rw [energy_congr hj] at heq
    cases n with
    | zero => rw [windowLevels_zero] at heq; linarith [hE0 (g j)]
    | succ n =>
      rcases le_or_gt j n with h | h
      · have h1 : energy (g j) 0 1 ≤ energy (g n) 0 1 := hE.monotone h
        linarith [lt_windowLevels_succ hE n]
      · have h1 : energy (g (n + 1)) 0 1 ≤ energy (g j) 0 1 := hE.monotone h
        linarith [windowLevels_succ_lt hE n]
  obtain ⟨geo, hgeo0, hmem, hex, hpw, -, hcell⟩ := theorem_17_3_of_levels hcl hp hq hnd
    (windowLevels_monotone hE) (tendsto_windowLevels hE htop)
    (by rw [windowLevels_zero]; norm_num) hreg
  convert hcell using 1
  funext n
  cases n with
  | zero => simp [oneCellEach, hgeo0]
  | succ k =>
    have hall' : ∀ γ ∈ geo (k + 1), EqOn γ (g k) (Icc 0 1) := by
      intro γ hγ
      obtain ⟨hγp, hγg, h1, h2⟩ := hmem k γ hγ
      obtain ⟨j, hj⟩ := hall γ hγp hγg
      rw [energy_congr hj] at h1 h2
      rwa [(mem_window_iff hE j k).1 ⟨h1, h2⟩] at hj
    obtain ⟨γ', hγ', -⟩ := hex k (g k) (hg k) (hgeo k) ((mem_window_iff hE k k).2 rfl).1
      ((mem_window_iff hE k k).2 rfl).2
    have hlist : geo (k + 1) = [γ'] :=
      List.eq_singleton_of_pairwise_not (hpw (k + 1)) hγ' fun x hx y hy =>
        (hall' x hx).trans (hall' y hy).symm
    rw [hlist]
    obtain ⟨hγ'p, hγ'g, -, -⟩ := hmem k γ' hγ'
    have h1 := geodesicIndex_eq hγ'p hγ'g
    rw [hd k γ' hγ'p hγ'g (hall' γ' hγ')] at h1
    simp only [oneCellEach, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    exact_mod_cast h1.symm

/-- **The homology of each window** (Milnor p. 29 in the path space): with one geodesic `g k` in the
`k`-th window, of index `d k`, `H_j(Ω^{a_{k+1}}, Ω^{a_k}; 𝕜)` is `𝕜` for `j = d k` and `0`
otherwise. -/
theorem finrank_window {𝕜 : Type u} [Field 𝕜] (hcl : IsClosed N) (hp : p ∈ N) (hq : q ∈ N)
    (hnd : ∀ γ (hγ : γ ∈ pathSpace N p q), IsUnbrokenGeodesic hN γ → hessNullity hN hγ = 0)
    (hg : ∀ k, g k ∈ pathSpace N p q) (hgeo : ∀ k, IsUnbrokenGeodesic hN (g k))
    (hall : ∀ γ ∈ pathSpace N p q, IsUnbrokenGeodesic hN γ → ∃ k, EqOn γ (g k) (Icc 0 1))
    (hE : StrictMono fun k => energy (g k) 0 1) (d : ℕ → ℕ)
    (hd : ∀ k γ (hγ : γ ∈ pathSpace N p q), IsUnbrokenGeodesic hN γ → EqOn γ (g k) (Icc 0 1) →
      formIndex (energyHessian hN hγ) = d k) (k j : ℕ) :
    FiniteDimensional 𝕜 (subsetHomology 𝕜 j (sublevel_mono (PathSp.energyC N p q)
      (windowLevels_monotone hE (Nat.le_succ k)))) ∧
    finrank 𝕜 (subsetHomology 𝕜 j (sublevel_mono (PathSp.energyC N p q)
      (windowLevels_monotone hE (Nat.le_succ k)))) = if j = d k then 1 else 0 := by
  classical
  have hE0 : ∀ γ : ℝ → V, 0 ≤ energy γ 0 1 := fun γ => PathSp.energy_nonneg_of_le zero_le_one
  set a := windowLevels g with ha_def
  obtain ⟨m, ⟨B⟩⟩ := exists_brokenSetup_uniform hN hp hq (c := max (a (k + 1)) 0 + 1)
    (by positivity) (isCompact_closedRiemBall_of_isClosed hN hcl p _)
  have hb : a (k + 1) < max (a (k + 1)) 0 + 1 := by linarith [le_max_left (a (k + 1)) 0]
  -- the window `(a_k, a_{k+1})` contains the energy of `g k` only
  have hwin : ∀ γ ∈ pathSpace N p q, IsUnbrokenGeodesic hN γ → a k < energy γ 0 1 →
      energy γ 0 1 < a (k + 1) → EqOn γ (g k) (Icc 0 1) := by
    intro γ hγ hγg h1 h2
    obtain ⟨j, hj⟩ := hall γ hγ hγg
    rw [energy_congr hj] at h1 h2
    rwa [(mem_window_iff hE j k).1 ⟨h1, h2⟩] at hj
  have hreg : ∀ n, ∀ γ ∈ pathSpace N p q, IsUnbrokenGeodesic hN γ → energy γ 0 1 ≠ a n := by
    intro n γ hγ hγg heq
    obtain ⟨j, hj⟩ := hall γ hγ hγg
    rw [energy_congr hj] at heq
    cases n with
    | zero => rw [ha_def, windowLevels_zero] at heq; linarith [hE0 (g j)]
    | succ n =>
      rcases le_or_gt j n with h | h
      · have h1 : energy (g j) 0 1 ≤ energy (g n) 0 1 := hE.monotone h
        linarith [lt_windowLevels_succ hE n]
      · have h1 : energy (g (n + 1)) 0 1 ≤ energy (g j) 0 1 := hE.monotone h
        linarith [windowLevels_succ_lt hE n]
  obtain ⟨hfd, hfr⟩ := B.finrank_subsetHomology_Omega (𝕜 := 𝕜)
    (windowLevels_monotone hE (Nat.le_succ k)) hb
    (fun y hy hyg => by
      rw [← B.energy_path hy]
      exact ⟨hreg k _ (B.path_mem_pathSpace hy) hyg, hreg (k + 1) _ (B.path_mem_pathSpace hy) hyg⟩)
    (fun y hy hyg _ => hnd _ _ hyg)
    (fun y y' hy hy' hyg hyg' h1 h2 h3 h4 => by
      rw [← B.energy_path hy, ← B.energy_path hy'] at *
      rw [energy_congr (hwin _ (B.path_mem_pathSpace hy) hyg h1 h2),
        energy_congr (hwin _ (B.path_mem_pathSpace hy') hyg' h3 h4)]) j
  refine ⟨hfd, hfr.trans ?_⟩
  -- the only broken geodesic in the window is that of `g k`
  have hgk : energy (g k) 0 1 < max (a (k + 1)) 0 + 1 :=
    (lt_windowLevels_succ hE k).trans hb
  obtain ⟨hy₀, heq₀, hgeo₀, hE₀⟩ := B.eqOn_path_nodeVal_of_isUnbrokenGeodesic (hg k) (hgeo k) hgk
  have hidx₀ : B.geodIndex (B.nodeVal (g k)) = d k := by
    rw [B.geodIndex_eq_geodesicIndex hy₀]
    have h1 := geodesicIndex_eq (B.path_mem_pathSpace hy₀) hgeo₀
    rw [hd k _ (B.path_mem_pathSpace hy₀) hgeo₀ heq₀] at h1
    exact_mod_cast h1
  have hset : {y | y ∈ B.nodes ∧ IsUnbrokenGeodesic hN (B.path y) ∧ a k < B.energy' y ∧
      B.energy' y < a (k + 1) ∧ B.geodIndex y = j} =
      if j = d k then {B.nodeVal (g k)} else ∅ := by
    ext y
    constructor
    · rintro ⟨hy, hyg, h1, h2, hyj⟩
      rw [← B.energy_path hy] at h1 h2
      have h3 := hwin _ (B.path_mem_pathSpace hy) hyg h1 h2
      have hyk : y = B.nodeVal (g k) := by
        rw [← B.nodeVal_path hy]
        funext i
        exact h3 ⟨B.t_nonneg _, B.t_le_one _⟩
      subst hyk
      rw [hidx₀] at hyj
      rw [if_pos hyj.symm]
      exact rfl
    · intro hy
      split_ifs at hy with hj
      · rw [mem_singleton_iff] at hy
        subst hy
        refine ⟨hy₀, hgeo₀, ?_, ?_, by rw [hidx₀, hj]⟩ <;> rw [hE₀]
        exacts [((mem_window_iff hE k k).2 rfl).1, ((mem_window_iff hE k k).2 rfl).2]
      · exact absurd hy (notMem_empty y)
  rw [hset]
  split_ifs <;> simp

/-- **The homology of the path space when the indices are lacunary** (Milnor p. 96, for `ΩSⁿ`,
`n ≥ 3`): with one geodesic `g k` in the `k`-th window, of index `k r` with `r ≥ 2`, the Betti
numbers of `Ω(N; p, q)` over any field are `1` in the degrees divisible by `r` and `0` otherwise.
On each finite stage `Ω^{a_K}` this is the lacunary principle (Corollary 5.4); the passage to
`Ω = ⋃ Ω^{a_K}` uses that singular chains have compact support and the energy is continuous
(`Morse.Homology.bettiNumber_eq_of_steps`). -/
theorem bettiNumber_omega_of_unique {𝕜 : Type u} [Field 𝕜] (hcl : IsClosed N) (hp : p ∈ N)
    (hq : q ∈ N)
    (hnd : ∀ γ (hγ : γ ∈ pathSpace N p q), IsUnbrokenGeodesic hN γ → hessNullity hN hγ = 0)
    (hg : ∀ k, g k ∈ pathSpace N p q) (hgeo : ∀ k, IsUnbrokenGeodesic hN (g k))
    (hall : ∀ γ ∈ pathSpace N p q, IsUnbrokenGeodesic hN γ → ∃ k, EqOn γ (g k) (Icc 0 1))
    (hE : StrictMono fun k => energy (g k) 0 1)
    (htop : Tendsto (fun k => energy (g k) 0 1) atTop atTop) {r : ℕ} (hr : 2 ≤ r)
    (hd : ∀ k γ (hγ : γ ∈ pathSpace N p q), IsUnbrokenGeodesic hN γ → EqOn γ (g k) (Icc 0 1) →
      formIndex (energyHessian hN hγ) = (k * r : ℕ)) (i : ℕ) :
    bettiNumber 𝕜 (PathSp N p q) i = if r ∣ i then 1 else 0 := by
  classical
  set a := windowLevels g with ha_def
  set E := PathSp.energyC N p q with hE_def
  set X : ℕ → Set (PathSp N p q) := fun k => sublevel E (a k) with hX_def
  have hX : Monotone X := fun j k h => sublevel_mono E (windowLevels_monotone hE h)
  have hstep := finrank_window (𝕜 := 𝕜) hcl hp hq hnd hg hgeo hall hE (fun k => k * r) hd
  have hstep' : ∀ k j, finrank 𝕜 (subsetHomology 𝕜 j (hX (Nat.le_succ k))) =
      if j = k * r then 1 else 0 := fun k j => (hstep k j).2
  have hfin : ∀ k j, FiniteDimensional 𝕜 (subsetHomology 𝕜 j (hX (Nat.le_succ k))) :=
    fun k j => (hstep k j).1
  have hX0 : X 0 = ∅ := by
    ext γ
    simp only [hX_def, ha_def, windowLevels_zero, mem_sublevel, mem_empty_iff_false, iff_false,
      not_le, hE_def, PathSp.energyC_apply]
    linarith [PathSp.energy_nonneg_of_le (γ := (γ : ℝ → V)) zero_le_one]
  -- a stage beyond the degrees `i`, `i + 1`
  set K := i + 2 with hK_def
  have hKr : i + 1 < K * r := by nlinarith
  have hsub : ∀ k j, K ≤ k → j ≤ i + 1 →
      Subsingleton (subsetHomology 𝕜 j (hX (Nat.le_succ k))) := by
    intro k j hk hj
    have h0 : finrank 𝕜 (subsetHomology 𝕜 j (hX (Nat.le_succ k))) = 0 := by
      rw [hstep' k j, if_neg]
      intro h
      have : K * r ≤ k * r := Nat.mul_le_mul_right r hk
      omega
    have := hfin k j
    exact Module.finrank_zero_iff.1 h0
  have hcpt : ∀ K' : Set (PathSp N p q), IsCompact K' → ∃ k, K' ⊆ X k := fun K' hK' =>
    exists_subset_sublevel_of_isCompact E.continuous
      (fun t => ((tendsto_windowLevels hE htop).eventually_ge_atTop t).exists) hK'
  rw [bettiNumber_eq_of_steps hX hcpt (k₀ := K) (fun k hk => hsub k i hk (by omega))
    (fun k hk => hsub k (i + 1) hk le_rfl)]
  rw [finrank_subsetHomology_congr (Set.empty_subset (X K)) (hX (Nat.zero_le K)) hX0.symm rfl]
  -- the lacunary principle on the finite filtration `X_0 ⊆ ⋯ ⊆ X_K`
  have hC : ∀ j, singularMorseNumber 𝕜 hX K j = if r ∣ j ∧ j / r < K then 1 else 0 := by
    intro j
    simp only [singularMorseNumber, hstep']
    rw [Finset.sum_boole, Nat.cast_id]
    have hr0 : 0 < r := by omega
    split_ifs with h
    · rw [Finset.card_eq_one]
      refine ⟨j / r, ?_⟩
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨-, hk⟩
        rw [hk, Nat.mul_div_cancel _ hr0]
      · rintro rfl
        exact ⟨h.2, (Nat.div_mul_cancel h.1).symm⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k hk hjk
      apply h
      refine ⟨⟨k, by rw [hjk, mul_comm]⟩, ?_⟩
      rw [hjk, Nat.mul_div_cancel _ hr0]
      exact Finset.mem_range.1 hk
  have hlac := eq_of_altSum_le_of_lacunary
    (b := fun j => (finrank 𝕜 (subsetHomology 𝕜 j (hX (Nat.zero_le K))) : ℤ))
    (c := fun j => (singularMorseNumber 𝕜 hX K j : ℤ)) (fun _ => Nat.cast_nonneg _)
    (singular_morse_inequality 𝕜 hX (n := K) (fun k _ j => hfin k j) (by omega))
    (fun j => by
      simp only [hC]
      by_cases h : r ∣ j
      · right
        rw [if_neg]
        · simp
        · rintro ⟨h', -⟩
          have : r ∣ 1 := (Nat.dvd_add_right h).1 h'
          have := Nat.le_of_dvd one_pos this
          omega
      · left
        rw [if_neg (fun h' => h h'.1)]
        simp) i
  simp only [hC] at hlac
  have hi : r ∣ i → i / r < K := fun _ => by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    omega
  by_cases h : r ∣ i
  · rw [if_pos ⟨h, hi h⟩] at hlac
    rw [if_pos h]
    exact_mod_cast hlac
  · rw [if_neg (fun h' => h h'.1)] at hlac
    rw [if_neg h]
    exact_mod_cast hlac

end Unique

end Morse
