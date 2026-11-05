import Morse.Appendix.TheoremA
import Morse.Appendix.MappingTelescope
import Morse.Appendix.Examples
import Morse.Chapter2.CWType

/-!
Milnor, *Morse Theory*, Appendix, p. 150 (the alternative proof of Theorem 17.3), p. 150 (the
Remark) and p. 153 (the Corollary).

# The homotopy type of a monotone union

**The application to Theorem 17.3** (p. 150), paraphrased: in the proof of Theorem 17.3 there are
subsets `Ω^{a₀} ⊆ Ω^{a₁} ⊆ ⋯` of the path space and CW-complexes `K₀ ⊆ K₁ ⊆ ⋯`, with homotopy
equivalences `Ω^{a_i} → K_i` forming a commutative ladder. Since `Ω` and `K = ⋃ K_i` are the
homotopy direct limits of these sequences (Examples 1 and 2), Theorem A shows that the limit map
`Ω → K` is a homotopy equivalence.

**The Remark** (p. 150), paraphrased: under the hypotheses of Case 1 one might conjecture that
`f_Σ` is homotopic to the identity; Milnor says that counterexamples can be given. **Not
formalized.** The exposition gives one, built from a phantom map `T → ℂP^∞` on the telescope `T` of
`S¹ → S¹ → ⋯` (`z ↦ z²`), which is null-homotopic on every finite stage but not globally (it is
detected by `H²(T; ℤ) ≠ 0`); it needs cellular cohomology and `ℂP^∞`, not available here. What is
formalized is the positive statement that `f_Σ` is a homotopy equivalence
(`Morse.theoremA_case1`).

**The Corollary** (p. 153), paraphrased: if `X` is the homotopy direct limit of `{X_i}` and each
`X_i` has the homotopy type of a CW-complex, so does `X`. "The proof is not difficult."

## What is proved here, and in which topology

* **Subspace form** (`Morse.nonempty_homotopyEquiv_telescope`): if the `K_i` are closed subspaces of
  a space `K` and `f : X → K` restricts to homotopy equivalences `X_i → K_i` ("`f_{i+1}` extends
  `f_i`"), then `X` is homotopy equivalent to Milnor's telescope `K_Σ = ⋃ K_i × [i, i+1] ⊆ K × ℝ`.
  Its topology is the subspace topology of `K × ℝ`, which by (T3) is the colimit topology of the
  strips `K_i × [i, i+1]`: it depends only on the topologies of the `K_i`. If moreover `K` is the
  homotopy direct limit of the `K_i`, `f` itself is a homotopy equivalence (Theorem A). For a
  CW-complex `K = ⋃ K_i` with the weak topology this is Example 2 (Whitehead's theorem), not
  formalized; that is why the telescope, not the weak topology, appears in the conclusion.
* **Mapping telescope form** (`Morse.nonempty_homotopyEquiv_mappingTelescope`): the `K_i` need
  not be subspaces of one space; given maps `c_i : K_i → K_{i+1}` (a functor `ℕ ⥤ TopCat`) and
  homotopy equivalences `g_i : X_i → K_i` with `c_i g_i ≃ g_{i+1}` on `X_i` (homotopy commutative
  squares; Milnor's ladder commutes strictly), `X` is homotopy equivalent to the mapping telescope
  of the `K_i` (`Morse.MappingTelescope`). The proof uses Milnor's map `G` of Case 2, from the
  telescope of the `K_i` to that of the `X_i` and built from homotopy inverses of the `g_i`
  (`Morse.compareMap`), rather than the exposition's map `X_Σ → K_Σ`: it is defined out of the
  mapping telescope, where pasting is automatic, and Theorem A is applied to the truncations, which
  are closed. So **no closedness of the `X_i` is needed**, in the Corollary either.
* **The Corollary** (`Morse.corollary_appendix`): with `c_i = e_{i+1} ∘ ι_i ∘ e_i⁻¹` for homotopy
  equivalences `e_i : X_i → K_i`, `X` is homotopy equivalent to the mapping telescope of the `K_i`.
  In the project's sense (`Morse.IsFiniteCellComplexType`), if each `X_i` has the homotopy type of
  a finite iterated adjunction space, then `X` has the homotopy type of the mapping telescope of
  such spaces (`Morse.corollary_cellComplex`). That this telescope is itself a CW-complex needs
  cellular approximation (to make the `c_i` cellular) and the CW structure of mapping telescopes,
  neither in Mathlib; the exposition's proof uses both.
* **Countable cell complexes, ready for §17** (`Morse.CellTower`,
  `Morse.IsCountableCellComplexType`): a tower `K₀ → K₁ → ⋯` in which `K₀` is an iterated
  adjunction space with cells `cells 0` and each `K_{n+1}` is obtained from `K_n` by attaching the
  cells `cells (n+1)` one at a time (`Morse.IsRelCellAttachment`), the maps being the inclusions
  `K_n → K_n ∪ e^λ`. `X` has the homotopy type of the countable cell complex if it is homotopy
  equivalent to the mapping telescope of the tower. Each stage is a finite cell complex
  (`Morse.CellTower.isCellAttachment`); a tower may be given by its stages and inclusions
  (`Morse.CellTower.ofSequence`). The topological part of Theorem 17.3 is then
  `Morse.isCountableCellComplexType_of_sublevel` (and `…_of_sublevel'`, for a tower given by its
  stages): if `X^{a_n} = {E ≤ a_n}` for a continuous `E` and `a_n ↗ ∞`, and `g_n : X^{a_n} → K_n`
  are homotopy equivalences with `c_n g_n = g_{n+1}` on `X^{a_n}` (Milnor's `f_{i+1}` extends
  `f_i`), then `X` has the homotopy type of the countable cell complex with cells
  `cells 0, cells 1, …`.
* **Theorem A with no closedness hypothesis** (`Morse.theoremA_general`). Milnor's statement of
  Theorem A has no closedness hypothesis, and it is true as stated: compare `X` with the mapping
  telescope of the inclusions `X_i → X_{i+1}` (`Morse.isHomotopyEquiv_telescopeProj'`), where the
  strips are always "closed", and apply Milnor's proof there. Only Milnor's *proof* needs closed
  sets. For closed `X_i` the mapping telescope of the inclusions is homeomorphic to `X_Σ`
  (`Morse.telescopeComparisonHomeomorph`).

## Main results

* `Morse.nonempty_homotopyEquiv_telescope`: the subspace form.
* `Morse.compareMap`, `Morse.nonempty_homotopyEquiv_mappingTelescope`: the mapping telescope form.
* `Morse.corollary_appendix`, `Morse.corollary_cellComplex`: **the Corollary**.
* `Morse.IsRelCellAttachment`, `Morse.CellTower`, `Morse.IsCountableCellComplexType`,
  `Morse.isCountableCellComplexType_of_tower`, `Morse.isCountableCellComplexType_of_sublevel`:
  countable cell complexes and the topological part of Theorem 17.3.
* `Morse.subspaceFunctor`, `Morse.telescopeComparison`, `Morse.theoremA_general`: **Theorem A**
  without closedness.

## What Milnor's text leaves implicit

* The application cites "Theorem 17.2"; the statement used is Corollary 17.2 (p. 95).
* `Ω = ⋃ Ω^{a_i}` needs `a_i → ∞`; each point of `Ω` is interior to some `Ω^{a_i}` because the
  energy is continuous; "`f_{i+1}` extends `f_i`" is needed for the limit map to exist.
* For sublevel sets of a continuous function, Example 1 holds without paracompactness
  (`Morse.isHomotopyDirectLimit_sublevel`).
-/

open Set Filter Topology Function CategoryTheory TopCat
open scoped unitInterval

universe u v

noncomputable section

namespace Morse

/-! ### Homotopy-commutative squares of homotopy equivalences -/

/-- If `j ∘ a ≃ a' ∘ i` and `b`, `b'` are homotopy inverses of `a`, `a'`, then `i ∘ b ≃ b' ∘ j`:
`i b ≃ b' a' i b ≃ b' j a b ≃ b' j` (Milnor, p. 152). -/
theorem homotopic_inverse_square {P Q P' Q' : Type*} [TopologicalSpace P] [TopologicalSpace Q]
    [TopologicalSpace P'] [TopologicalSpace Q'] {a : C(P, Q)} {a' : C(P', Q')} {i : C(P, P')}
    {j : C(Q, Q')} {b : C(Q, P)} {b' : C(Q', P')} (hsq : (j.comp a).Homotopic (a'.comp i))
    (hb : (a.comp b).Homotopic (ContinuousMap.id Q))
    (hb' : (b'.comp a').Homotopic (ContinuousMap.id P')) : (i.comp b).Homotopic (b'.comp j) := by
  have h1 : (i.comp b).Homotopic ((b'.comp a').comp (i.comp b)) := by
    have := hb'.symm.comp (ContinuousMap.Homotopic.refl (i.comp b))
    rwa [ContinuousMap.id_comp] at this
  have h2 : ((b'.comp a').comp (i.comp b)).Homotopic ((b'.comp j).comp (a.comp b)) := by
    have := (ContinuousMap.Homotopic.refl b').comp
      (hsq.symm.comp (ContinuousMap.Homotopic.refl b))
    simpa only [ContinuousMap.comp_assoc] using this
  have h3 : ((b'.comp j).comp (a.comp b)).Homotopic (b'.comp j) := by
    have := (ContinuousMap.Homotopic.refl (b'.comp j)).comp hb
    rwa [ContinuousMap.comp_id] at this
  exact (h1.trans h2).trans h3

/-! ### The subspace form -/

section Subspace

variable {X : Type*} [TopologicalSpace X] {A : ℕ → Set X} {Y : Type*} [TopologicalSpace Y]
  {B : ℕ → Set Y}

/-- **Monotone unions, subspace form** (Milnor, p. 150). If `X` is the homotopy direct limit of
`{X_i}`, the `Y_i ⊆ Y` are closed, and `f : X → Y` carries each `X_i` into `Y_i` by a homotopy
equivalence, then `X` is homotopy equivalent to the telescope `Y_Σ ⊆ Y × ℝ` of the `Y_i`. -/
theorem nonempty_homotopyEquiv_telescope (hA : Monotone A) (hB : Monotone B)
    (hBc : ∀ n, IsClosed (B n)) (hX : IsHomotopyDirectLimit A) (f : C(X, Y))
    (hf : ∀ n, MapsTo f (A n) (B n)) (hfe : ∀ n, IsHomotopyEquiv (restrictTo f (hf n))) :
    Nonempty (ContinuousMap.HomotopyEquiv X (telescope B)) := by
  obtain ⟨e₁⟩ := hX.nonempty
  obtain ⟨e₂⟩ := (theoremA_telescope hA hB hBc f hf hfe).nonempty
  exact ⟨e₁.symm.trans e₂⟩

end Subspace

/-! ### Comparison with a mapping telescope -/

section Comparison

variable {X : Type*} [TopologicalSpace X] {A : ℕ → Set X} (F : ℕ ⥤ TopCat.{v})

/-- The block formula of the comparison map `K_Σ → X_Σ` (Milnor's `G` of Case 2, p. 152, for the
mapping telescope): `(k, t)_n ↦ (g'_n(k), n + 2t)` for `t ≤ 1/2` and `(H^n_{2t-1}(k), n + 1)` for
`t ≥ 1/2`, where `H^n : i_n g'_n ≃ g'_{n+1} c_n`. -/
def compareStrip (hA : Monotone A) (g' : ∀ n, C(F.obj n, A n))
    (H : ∀ n, ((up hA n).comp (g' n)).Homotopy
      ((g' (n + 1)).comp (tmap F (Nat.le_add_right n 1)))) (n : ℕ) :
    C(F.obj n × I, telescope A) where
  toFun q := if (q.2 : ℝ) ≤ 1 / 2 then stripMap A n (g' n q.1, clampI (2 * q.2))
    else stripMap A (n + 1) (H n (clampI (2 * q.2 - 1), q.1), 0)
  continuous_toFun := by
    have ht : Continuous fun q : F.obj n × I => ((q.2 : I) : ℝ) :=
      continuous_subtype_val.comp continuous_snd
    refine Continuous.if_le ?_ ?_ ht continuous_const ?_
    · exact (stripMap A n).continuous.comp (((g' n).continuous.comp continuous_fst).prodMk
        (continuous_clampI.comp (continuous_const.mul ht)))
    · exact (stripMap A (n + 1)).continuous.comp (((H n).continuous.comp
        ((continuous_clampI.comp ((continuous_const.mul ht).sub continuous_const)).prodMk
          continuous_fst)).prodMk continuous_const)
    · intro q hq
      rw [hq, show (2 : ℝ) * (1 / 2) = 1 by norm_num, show (1 : ℝ) - 1 = 0 by norm_num,
        clampI_one, clampI_zero, (H n).apply_zero, stripMap_one hA]
      rfl

/-- **The comparison map** `Ψ : K_Σ → X_Σ` from the mapping telescope of the `K_n`. -/
def compareMap (hA : Monotone A) (g' : ∀ n, C(F.obj n, A n))
    (H : ∀ n, ((up hA n).comp (g' n)).Homotopy
      ((g' (n + 1)).comp (tmap F (Nat.le_add_right n 1)))) :
    C(MappingTelescope F, telescope A) :=
  MappingTelescope.desc F (compareStrip F hA g' H) fun n k => by
    change (if ((0 : I) : ℝ) ≤ 1 / 2 then stripMap A (n + 1) (g' (n + 1) (tmap F _ k),
        clampI (2 * (0 : I))) else stripMap A (n + 1 + 1) (H (n + 1) (clampI (2 * (0 : I) - 1),
          tmap F _ k), 0)) =
      (if ((1 : I) : ℝ) ≤ 1 / 2 then stripMap A n (g' n k, clampI (2 * (1 : I)))
      else stripMap A (n + 1) (H n (clampI (2 * (1 : I) - 1), k), 0))
    rw [if_pos (by norm_num), if_neg (by norm_num)]
    simp only [Set.Icc.coe_zero, Set.Icc.coe_one, mul_zero, clampI_zero]
    rw [show (2 : ℝ) * 1 - 1 = 1 by norm_num, clampI_one, (H n).apply_one]
    rfl

theorem compareMap_mk (hA : Monotone A) (g' : ∀ n, C(F.obj n, A n))
    (H : ∀ n, ((up hA n).comp (g' n)).Homotopy
      ((g' (n + 1)).comp (tmap F (Nat.le_add_right n 1)))) (n : ℕ) (k : F.obj n) (t : I) :
    compareMap F hA g' H (MappingTelescope.mk F n k t) = compareStrip F hA g' H n (k, t) :=
  rfl

theorem compareMap_mk_zero (hA : Monotone A) (g' : ∀ n, C(F.obj n, A n))
    (H : ∀ n, ((up hA n).comp (g' n)).Homotopy
      ((g' (n + 1)).comp (tmap F (Nat.le_add_right n 1)))) (n : ℕ) (k : F.obj n) :
    compareMap F hA g' H (MappingTelescope.mk F n k 0) = stripMap A n (g' n k, 0) := by
  rw [compareMap_mk]
  change (if ((0 : I) : ℝ) ≤ 1 / 2 then stripMap A n (g' n k, clampI (2 * (0 : I))) else _) = _
  rw [if_pos (by norm_num)]
  exact stripMap_congr rfl (by simp)

theorem compareMap_mapsTo (hA : Monotone A) (g' : ∀ n, C(F.obj n, A n))
    (H : ∀ n, ((up hA n).comp (g' n)).Homotopy
      ((g' (n + 1)).comp (tmap F (Nat.le_add_right n 1)))) (m : ℕ) :
    MapsTo (compareMap F hA g' H) (MappingTelescope.trunc F m) (truncation A m) := by
  intro z hz
  obtain ⟨n, k, t, rfl⟩ := MappingTelescope.exists_mk F z
  have hz' : (n : ℝ) + t ≤ m := hz
  change (compareMap F hA g' H (MappingTelescope.mk F n k t) : X × ℝ).2 ≤ m
  rcases eq_or_lt_of_le t.2.1 with ht | ht
  · have : t = 0 := Subtype.ext ht.symm
    subst this
    rw [compareMap_mk_zero]
    simpa using hz'
  · have hnm : (n : ℝ) < m := by linarith
    have hnm' : n + 1 ≤ m := by exact_mod_cast hnm
    have hle : ((n + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hnm'
    rw [compareMap_mk]
    change ((if (t : ℝ) ≤ 1 / 2 then stripMap A n (g' n k, clampI (2 * t))
      else stripMap A (n + 1) (H n (clampI (2 * t - 1), k), 0) : telescope A) : X × ℝ).2 ≤ m
    split_ifs
    · simp only [stripMap_apply_snd]
      push_cast at hle
      linarith [(clampI (2 * t)).2.2]
    · simpa using hle

/-- **The comparison map is a homotopy equivalence** (Theorem A for the mapping telescope and its
truncations, and for `X_Σ` and its truncations; both are closed). -/
theorem isHomotopyEquiv_compareMap (hA : Monotone A) (g' : ∀ n, C(F.obj n, A n))
    (hg' : ∀ n, IsHomotopyEquiv (g' n))
    (H : ∀ n, ((up hA n).comp (g' n)).Homotopy
      ((g' (n + 1)).comp (tmap F (Nat.le_add_right n 1)))) :
    IsHomotopyEquiv (compareMap F hA g' H) := by
  refine theoremA (MappingTelescope.monotone_trunc F) monotone_truncation isClosed_truncation
    (MappingTelescope.isHomotopyDirectLimit_trunc F) isHomotopyDirectLimit_truncation _
    (compareMap_mapsTo F hA g' H) fun m => ?_
  set R := restrictTo (compareMap F hA g' H) (compareMap_mapsTo F hA g' H m)
  have hR : R.comp (MappingTelescope.levelIncl F m) = (truncIncl A m).comp (g' m) :=
    ContinuousMap.ext fun k => Subtype.ext (compareMap_mk_zero F hA g' H m k)
  have h1 : R.Homotopic
      (((truncIncl A m).comp (g' m)).comp (MappingTelescope.levelRetract F m)) := by
    have := (ContinuousMap.Homotopic.refl R).comp
      (MappingTelescope.levelIncl_comp_levelRetract F m).symm
    rwa [ContinuousMap.comp_id, ← ContinuousMap.comp_assoc, hR] at this
  exact (((MappingTelescope.isHomotopyEquiv_levelRetract F m).comp (hg' m)).comp
    (isHomotopyEquiv_truncIncl hA m)).of_homotopic h1.symm

/-- **A homotopy direct limit is homotopy equivalent to the mapping telescope of any sequence
homotopy equivalent to its terms** (the form of the Appendix used for Theorem 17.3). If `X` is the
homotopy direct limit of `{X_n}` (no closedness needed), `F : ℕ ⥤ TopCat` is a sequence
`K₀ → K₁ → ⋯`, and `g_n : X_n → K_n` are homotopy equivalences with `c_n g_n ≃ g_{n+1}` on `X_n`,
then `X` is homotopy equivalent to the mapping telescope of `F`. -/
theorem nonempty_homotopyEquiv_mappingTelescope (hA : Monotone A) (hX : IsHomotopyDirectLimit A)
    (g : ∀ n, C(A n, F.obj n)) (hg : ∀ n, IsHomotopyEquiv (g n))
    (hsq : ∀ n, ((tmap F (Nat.le_add_right n 1)).comp (g n)).Homotopic
      ((g (n + 1)).comp (up hA n))) :
    Nonempty (ContinuousMap.HomotopyEquiv X (MappingTelescope F)) := by
  choose g' hg'₁ hg'₂ using hg
  have hsq' : ∀ n, ((up hA n).comp (g' n)).Homotopic
      ((g' (n + 1)).comp (tmap F (Nat.le_add_right n 1))) := fun n =>
    homotopic_inverse_square (hsq n) (hg'₂ n) (hg'₁ (n + 1))
  have hΨ := isHomotopyEquiv_compareMap F hA g'
    (fun n => IsHomotopyEquiv.of_inverse (hg'₁ n) (hg'₂ n)) fun n => (hsq' n).some
  obtain ⟨e₁⟩ := hΨ.nonempty
  obtain ⟨e₂⟩ := hX.nonempty
  exact ⟨(e₁.trans e₂).symm⟩

/-- **The Corollary** (Milnor, p. 153), in the telescope model: if `X` is the homotopy direct limit
of `{X_n}` and each `X_n` is homotopy equivalent to `K_n`, then `X` is homotopy equivalent to the
mapping telescope of `K₀ → K₁ → ⋯`, the maps being `e_{n+1} ∘ (X_n ⊆ X_{n+1}) ∘ e_n⁻¹`. -/
theorem corollary_appendix (hA : Monotone A) (hX : IsHomotopyDirectLimit A) (K : ℕ → TopCat.{v})
    (e : ∀ n, ContinuousMap.HomotopyEquiv (A n) (K n)) :
    ∃ F : ℕ ⥤ TopCat.{v}, (∀ n, F.obj n = K n) ∧
      Nonempty (ContinuousMap.HomotopyEquiv X (MappingTelescope F)) := by
  let c : ∀ n, K n ⟶ K (n + 1) := fun n =>
    TopCat.ofHom ((e (n + 1)).toFun.comp ((up hA n).comp (e n).invFun))
  refine ⟨Functor.ofSequence c, fun n => rfl, nonempty_homotopyEquiv_mappingTelescope _ hA hX
    (fun n => (e n).toFun) (fun n => IsHomotopyEquiv.of_homotopyEquiv (e n)) fun n => ?_⟩
  have hc : tmap (Functor.ofSequence c) (Nat.le_add_right n 1) =
      (e (n + 1)).toFun.comp ((up hA n).comp (e n).invFun) := by
    simp only [tmap, Functor.ofSequence_map_homOfLE_succ]
    rfl
  rw [hc]
  change ((((e (n + 1)).toFun.comp ((up hA n).comp (e n).invFun)).comp (e n).toFun :
    C(A n, K (n + 1)))).Homotopic ((e (n + 1)).toFun.comp (up hA n))
  have := (ContinuousMap.Homotopic.refl ((e (n + 1)).toFun.comp (up hA n))).comp (e n).left_inv
  simpa only [ContinuousMap.comp_assoc, ContinuousMap.comp_id] using this

end Comparison

/-- **The Corollary for finite cell complexes**: if `X` is the homotopy direct limit of `{X_n}` and
each `X_n` has the homotopy type of a finite iterated adjunction space with cells `cells n`
(`Morse.IsFiniteCellComplexType`), then `X` is homotopy equivalent to the mapping telescope of a
sequence of such spaces. -/
theorem corollary_cellComplex {X : Type u} [TopologicalSpace X] {A : ℕ → Set X}
    (hA : Monotone A) (hX : IsHomotopyDirectLimit A) (cells : ℕ → List ℕ)
    (h : ∀ n, IsFiniteCellComplexType (A n) (cells n)) :
    ∃ F : ℕ ⥤ TopCat.{u}, (∀ n, IsCellAttachment (F.obj n) (cells n)) ∧
      Nonempty (ContinuousMap.HomotopyEquiv X (MappingTelescope F)) := by
  choose K hK e using h
  obtain ⟨F, hF, he⟩ := corollary_appendix hA hX K fun n => (e n).some
  exact ⟨F, fun n => hF n ▸ hK n, he⟩

/-! ### Countable cell complexes -/

/-- **Relative iterated adjunction spaces.** `IsRelCellAttachment L K j cells`: `K` is obtained
from `L` by attaching cells of the dimensions listed in `cells`, one at a time and in this order,
each along an arbitrary continuous map, and `j : L → K` is the composite of the inclusions
`K' → K' ∪_φ e^λ` (`Morse.cellInl`). -/
inductive IsRelCellAttachment (L : TopCat.{u}) : (K : TopCat.{u}) → (L ⟶ K) → List ℕ → Prop
  | refl : IsRelCellAttachment L L (𝟙 L) []
  | attach {K : TopCat.{u}} {j : L ⟶ K} {cells : List ℕ} (h : IsRelCellAttachment L K j cells)
      (n : ℕ) (φ : ∂𝔻 n ⟶ K) : IsRelCellAttachment L (AttachCell φ) (j ≫ cellInl φ) (cells ++ [n])

theorem IsCellAttachment.of_rel {L K : TopCat.{u}} {j : L ⟶ K} {c c' : List ℕ}
    (hL : IsCellAttachment L c) (h : IsRelCellAttachment L K j c') :
    IsCellAttachment K (c ++ c') := by
  induction h with
  | refl => simpa using hL
  | attach _ n φ ih =>
    rw [← List.append_assoc]
    exact ih.attach n φ

/-- **A countable cell complex, given by its finite stages** (the Lean model of the countable
CW-complexes of Theorem 17.3): `K₀` is an iterated adjunction space with cells `cells 0`, and
`K_{n+1}` is obtained from `K_n` by attaching the cells `cells (n + 1)`, the map `K_n → K_{n+1}`
being the inclusion. -/
structure CellTower (cells : ℕ → List ℕ) where
  /-- The finite stages and the inclusions between them. -/
  K : ℕ ⥤ TopCat.{u}
  zero : IsCellAttachment (K.obj 0) (cells 0)
  step : ∀ n, IsRelCellAttachment (K.obj n) (K.obj (n + 1))
    (K.map (homOfLE (Nat.le_add_right n 1))) (cells (n + 1))

/-- Each stage of a cell tower is a finite cell complex, with the cells of the stages `≤ n`. -/
theorem CellTower.isCellAttachment {cells : ℕ → List ℕ} (T : CellTower.{u} cells) (n : ℕ) :
    IsCellAttachment (T.K.obj n) ((List.range (n + 1)).flatMap cells) := by
  induction n with
  | zero => simpa using T.zero
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append]
    simpa using ih.of_rel (T.step n)

/-- A cell tower given by its stages `K n` and the inclusions `c n : K n → K (n + 1)`, as produced
by an inductive construction (`CategoryTheory.Functor.ofSequence`). -/
def CellTower.ofSequence {cells : ℕ → List ℕ} (K : ℕ → TopCat.{u}) (c : ∀ n, K n ⟶ K (n + 1))
    (h₀ : IsCellAttachment (K 0) (cells 0))
    (hstep : ∀ n, IsRelCellAttachment (K n) (K (n + 1)) (c n) (cells (n + 1))) :
    CellTower.{u} cells where
  K := Functor.ofSequence c
  zero := h₀
  step n := by
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact hstep n

theorem CellTower.tmap_ofSequence {cells : ℕ → List ℕ} (K : ℕ → TopCat.{u})
    (c : ∀ n, K n ⟶ K (n + 1)) (h₀ : IsCellAttachment (K 0) (cells 0))
    (hstep : ∀ n, IsRelCellAttachment (K n) (K (n + 1)) (c n) (cells (n + 1))) (n : ℕ) :
    tmap (CellTower.ofSequence K c h₀ hstep).K (Nat.le_add_right n 1) = (c n).hom := by
  simp only [tmap, CellTower.ofSequence, Functor.ofSequence_map_homOfLE_succ]
  rfl

/-- **`X` has the homotopy type of a countable cell complex with cells `cells 0, cells 1, …`**
(attached in this order): `X` is homotopy equivalent to the mapping telescope of a cell tower with
these cells. The telescope stands for the union of the stages with the weak topology; the two are
homotopy equivalent by Example 2 of the Appendix (Whitehead's theorem), which is not formalized. -/
def IsCountableCellComplexType (X : Type u) [TopologicalSpace X] (cells : ℕ → List ℕ) : Prop :=
  ∃ T : CellTower.{u} cells, Nonempty (ContinuousMap.HomotopyEquiv X (MappingTelescope T.K))

theorem IsCountableCellComplexType.of_homotopyEquiv {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] {cells : ℕ → List ℕ} (h : IsCountableCellComplexType Y cells)
    (e : ContinuousMap.HomotopyEquiv X Y) : IsCountableCellComplexType X cells := by
  obtain ⟨T, ⟨e'⟩⟩ := h
  exact ⟨T, ⟨e.trans e'⟩⟩

section Tower

variable {X : Type u} [TopologicalSpace X] {A : ℕ → Set X} {cells : ℕ → List ℕ}

/-- **The alternative final step of Theorem 17.3** (Milnor, p. 150), with homotopy-commutative
squares: if `X` is the homotopy direct limit of `{X_n}`, and `g_n : X_n → K_n` are homotopy
equivalences to the stages of a cell tower with `c_n g_n ≃ g_{n+1}` on `X_n`, then `X` has the
homotopy type of the countable cell complex. -/
theorem isCountableCellComplexType_of_tower (hA : Monotone A) (hX : IsHomotopyDirectLimit A)
    (T : CellTower.{u} cells) (g : ∀ n, C(A n, T.K.obj n)) (hg : ∀ n, IsHomotopyEquiv (g n))
    (hsq : ∀ n, ((tmap T.K (Nat.le_add_right n 1)).comp (g n)).Homotopic
      ((g (n + 1)).comp (up hA n))) :
    IsCountableCellComplexType X cells :=
  ⟨T, nonempty_homotopyEquiv_mappingTelescope T.K hA hX g hg hsq⟩

/-- **Theorem 17.3, the topological part** (Milnor, p. 150): let `E : X → ℝ` be continuous,
`a₀ ≤ a₁ ≤ ⋯` with `a_n → ∞`, and let `g_n : X^{a_n} → K_n` be homotopy equivalences from the
sublevel sets `X^{a_n} = {E ≤ a_n}` to the stages of a cell tower, with `g_{n+1}` extending `g_n`
(`c_n ∘ g_n = g_{n+1}` on `X^{a_n}`). Then `X` has the homotopy type of the countable cell complex
with cells `cells 0, cells 1, …`. No paracompactness is needed
(`Morse.isHomotopyDirectLimit_sublevel`). -/
theorem isCountableCellComplexType_of_sublevel (E : C(X, ℝ)) {a : ℕ → ℝ} (ha : Monotone a)
    (ha' : Tendsto a atTop atTop) (T : CellTower.{u} cells)
    (g : ∀ n, C(sublevel E (a n), T.K.obj n)) (hg : ∀ n, IsHomotopyEquiv (g n))
    (hcompat : ∀ n (x : sublevel E (a n)), tmap T.K (Nat.le_add_right n 1) (g n x) =
      g (n + 1) ⟨x, sublevel_mono E (ha (Nat.le_add_right n 1)) x.2⟩) :
    IsCountableCellComplexType X cells := by
  have hA : Monotone fun n => sublevel E (a n) := fun m n h => sublevel_mono E (ha h)
  refine isCountableCellComplexType_of_tower hA (isHomotopyDirectLimit_sublevel E ha ha') T g hg
    fun n => ?_
  have : (tmap T.K (Nat.le_add_right n 1)).comp (g n) = (g (n + 1)).comp (up hA n) :=
    ContinuousMap.ext fun x => hcompat n x
  rw [this]

/-- **Theorem 17.3, the topological part, with the tower given by its stages** (the form produced
by the inductive construction of Lemma 17.E of the exposition): stages `K n`, inclusions
`c n : K n → K n ∪ cells`, and homotopy equivalences `g n : X^{a_n} → K n` with
`c n ∘ g n = g (n + 1)` on `X^{a_n}`. -/
theorem isCountableCellComplexType_of_sublevel' (E : C(X, ℝ)) {a : ℕ → ℝ} (ha : Monotone a)
    (ha' : Tendsto a atTop atTop) (K : ℕ → TopCat.{u}) (c : ∀ n, K n ⟶ K (n + 1))
    (h₀ : IsCellAttachment (K 0) (cells 0))
    (hstep : ∀ n, IsRelCellAttachment (K n) (K (n + 1)) (c n) (cells (n + 1)))
    (g : ∀ n, C(sublevel E (a n), K n)) (hg : ∀ n, IsHomotopyEquiv (g n))
    (hcompat : ∀ n (x : sublevel E (a n)),
      c n (g n x) = g (n + 1) ⟨x, sublevel_mono E (ha (Nat.le_add_right n 1)) x.2⟩) :
    IsCountableCellComplexType X cells :=
  isCountableCellComplexType_of_sublevel E ha ha' (CellTower.ofSequence K c h₀ hstep) g hg
    fun n x => by
      rw [CellTower.tmap_ofSequence]
      exact hcompat n x

end Tower

/-! ### Theorem A without closedness -/

section General

variable {X : Type u} [TopologicalSpace X] {A : ℕ → Set X}

/-- The inclusions `X₀ ⊆ X₁ ⊆ ⋯`, as a functor `ℕ ⥤ TopCat`. -/
def subspaceFunctor (hA : Monotone A) : ℕ ⥤ TopCat.{u} where
  obj n := TopCat.of (A n)
  map h := TopCat.ofHom ⟨Set.inclusion (hA (leOfHom h)), continuous_inclusion _⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The canonical map from the mapping telescope of the inclusions to Milnor's telescope,
`(x, t)_n ↦ (x, n + t)`. -/
def telescopeComparison (hA : Monotone A) :
    C(MappingTelescope (subspaceFunctor hA), telescope A) :=
  MappingTelescope.desc _ (fun n => stripMap A n) fun n x => (stripMap_one hA n x).symm

theorem telescopeComparison_mk (hA : Monotone A) (n : ℕ) (x : A n) (t : I) :
    telescopeComparison hA (MappingTelescope.mk _ n x t) = stripMap A n (x, t) :=
  rfl

/-- **For closed `X_n` the mapping telescope of the inclusions is Milnor's telescope**: the
comparison map is a homeomorphism, its inverse being given strip by strip by (T3). -/
def telescopeComparisonHomeomorph (hA : Monotone A) (hAc : ∀ n, IsClosed (A n)) :
    MappingTelescope (subspaceFunctor hA) ≃ₜ telescope A where
  toFun := telescopeComparison hA
  invFun := telescopeDesc hA hAc (fun n => ⟨fun q => MappingTelescope.mk (subspaceFunctor hA) n
    q.1 q.2, MappingTelescope.continuous_mk _ n⟩) fun n x =>
      (MappingTelescope.mk_one (subspaceFunctor hA) n x).symm
  left_inv z := by
    obtain ⟨n, k, t, rfl⟩ := MappingTelescope.exists_mk _ z
    exact telescopeDesc_stripMap hA hAc _ _ n k t
  right_inv z := by
    obtain ⟨n, x, t, rfl⟩ := exists_stripMap z
    exact (congrArg (telescopeComparison hA) (telescopeDesc_stripMap hA hAc _ _ n x t)).trans rfl
  continuous_toFun := (telescopeComparison hA).continuous
  continuous_invFun := (telescopeDesc hA hAc _ _).continuous

/-- **The mapping telescope of the inclusions is homotopy equivalent to Milnor's telescope**, with
no closedness hypothesis (Theorem A for the closed truncations of both). -/
theorem isHomotopyEquiv_telescopeComparison (hA : Monotone A) :
    IsHomotopyEquiv (telescopeComparison hA) := by
  have hmaps : ∀ m, MapsTo (telescopeComparison hA) (MappingTelescope.trunc _ m)
      (truncation A m) := by
    intro m z hz
    obtain ⟨n, k, t, rfl⟩ := MappingTelescope.exists_mk _ z
    exact hz
  refine theoremA (MappingTelescope.monotone_trunc _) monotone_truncation isClosed_truncation
    (MappingTelescope.isHomotopyDirectLimit_trunc _) isHomotopyDirectLimit_truncation _ hmaps
    fun m => ?_
  set R := restrictTo (telescopeComparison hA) (hmaps m)
  have hR : R.comp (MappingTelescope.levelIncl _ m) = truncIncl A m := rfl
  have h1 : R.Homotopic ((truncIncl A m).comp (MappingTelescope.levelRetract _ m)) := by
    have := (ContinuousMap.Homotopic.refl R).comp
      (MappingTelescope.levelIncl_comp_levelRetract (subspaceFunctor hA) m).symm
    rwa [ContinuousMap.comp_id, ← ContinuousMap.comp_assoc, hR] at this
  exact ((MappingTelescope.isHomotopyEquiv_levelRetract _ m).comp
    (isHomotopyEquiv_truncIncl hA m)).of_homotopic h1.symm

/-- The map `(x, t)_n ↦ x` from the mapping telescope of the inclusions to `X`. -/
def telescopeProj' (hA : Monotone A) : C(MappingTelescope (subspaceFunctor hA), X) :=
  (telescopeProj A).comp (telescopeComparison hA)

/-- If `X` is the homotopy direct limit of `{X_n}` (no closedness), the mapping telescope of the
inclusions is homotopy equivalent to `X` by `(x, t)_n ↦ x`. -/
theorem isHomotopyEquiv_telescopeProj' (hA : Monotone A) (hX : IsHomotopyDirectLimit A) :
    IsHomotopyEquiv (telescopeProj' hA) :=
  (isHomotopyEquiv_telescopeComparison hA).comp hX

variable {Y : Type v} [TopologicalSpace Y] {B : ℕ → Set Y}

/-- The map of mapping telescopes induced by `f`, `(x, t)_n ↦ (f(x), t)_n`. -/
def mappingTelescopeMap (hA : Monotone A) (hB : Monotone B) (f : C(X, Y))
    (hf : ∀ n, MapsTo f (A n) (B n)) :
    C(MappingTelescope (subspaceFunctor hA), MappingTelescope (subspaceFunctor hB)) :=
  MappingTelescope.desc _ (fun n => ⟨fun q => MappingTelescope.mk (subspaceFunctor hB) n
    (restrictTo f (hf n) q.1) q.2, (MappingTelescope.continuous_mk (subspaceFunctor hB) n).comp
      (((restrictTo f (hf n)).continuous.comp continuous_fst).prodMk continuous_snd)⟩)
    fun n x => (MappingTelescope.mk_one (subspaceFunctor hB) n (restrictTo f (hf n) x)).symm

theorem mappingTelescopeMap_mk (hA : Monotone A) (hB : Monotone B) (f : C(X, Y))
    (hf : ∀ n, MapsTo f (A n) (B n)) (n : ℕ) (x : A n) (t : I) :
    mappingTelescopeMap hA hB f hf (MappingTelescope.mk (subspaceFunctor hA) n x t) =
      MappingTelescope.mk (subspaceFunctor hB) n (restrictTo f (hf n) x) t :=
  rfl

theorem mapsTo_mappingTelescopeMap (hA : Monotone A) (hB : Monotone B) (f : C(X, Y))
    (hf : ∀ n, MapsTo f (A n) (B n)) (m : ℕ) :
    MapsTo (mappingTelescopeMap hA hB f hf) (MappingTelescope.trunc _ m)
      (MappingTelescope.trunc _ m) := by
  intro z hz
  obtain ⟨n, k, t, rfl⟩ := MappingTelescope.exists_mk _ z
  exact hz

/-- **Theorem A as Milnor states it** (p. 150), with no closedness hypothesis: if `X` and `Y` are
the homotopy direct limits of `{X_n}` and `{Y_n}`, and `f : X → Y` carries each `X_n` into `Y_n`
by a homotopy equivalence, then `f` is a homotopy equivalence. Milnor's proof needs closed
`X_n`, `Y_n`; here it is applied to the mapping telescopes of the inclusions, whose truncations
are closed, and compared with `X` and `Y` by `Morse.isHomotopyEquiv_telescopeProj'`. -/
theorem theoremA_general (hA : Monotone A) (hB : Monotone B) (hX : IsHomotopyDirectLimit A)
    (hY : IsHomotopyDirectLimit B) (f : C(X, Y)) (hf : ∀ n, MapsTo f (A n) (B n))
    (hfe : ∀ n, IsHomotopyEquiv (restrictTo f (hf n))) : IsHomotopyEquiv f := by
  have hΦ : IsHomotopyEquiv (mappingTelescopeMap hA hB f hf) := by
    refine theoremA (MappingTelescope.monotone_trunc _) (MappingTelescope.monotone_trunc _)
      (MappingTelescope.isClosed_trunc _) (MappingTelescope.isHomotopyDirectLimit_trunc _)
      (MappingTelescope.isHomotopyDirectLimit_trunc _) _ (mapsTo_mappingTelescopeMap hA hB f hf)
      fun m => ?_
    have hR : (restrictTo (mappingTelescopeMap hA hB f hf)
        (mapsTo_mappingTelescopeMap hA hB f hf m)).comp
          (MappingTelescope.levelIncl (subspaceFunctor hA) m) =
        (MappingTelescope.levelIncl (subspaceFunctor hB) m).comp (restrictTo f (hf m)) :=
      ContinuousMap.ext fun k => Subtype.ext (mappingTelescopeMap_mk hA hB f hf m k 0)
    have h1 := (ContinuousMap.Homotopic.refl (restrictTo (mappingTelescopeMap hA hB f hf)
      (mapsTo_mappingTelescopeMap hA hB f hf m))).comp
        (MappingTelescope.levelIncl_comp_levelRetract (subspaceFunctor hA) m).symm
    rw [ContinuousMap.comp_id, ← ContinuousMap.comp_assoc, hR] at h1
    have hcomp : IsHomotopyEquiv ((MappingTelescope.levelIncl (subspaceFunctor hB) m).comp
        ((restrictTo f (hf m)).comp (MappingTelescope.levelRetract (subspaceFunctor hA) m))) :=
      ((MappingTelescope.isHomotopyEquiv_levelRetract _ m).comp (hfe m)).comp
        (MappingTelescope.isHomotopyEquiv_levelIncl _ m)
    exact hcomp.of_homotopic h1.symm
  -- `f ∘ π_X = π_Y ∘ Φ`, and `π_X`, `π_Y` are homotopy equivalences
  have hcomm : f.comp (telescopeProj' hA) =
      (telescopeProj' hB).comp (mappingTelescopeMap hA hB f hf) :=
    MappingTelescope.ext _ fun n x t => rfl
  obtain ⟨s, hs₁, hs₂⟩ := isHomotopyEquiv_telescopeProj' hA hX
  have h1 : IsHomotopyEquiv (((telescopeProj' hB).comp (mappingTelescopeMap hA hB f hf)).comp s) :=
    (IsHomotopyEquiv.of_inverse hs₁ hs₂).comp (hΦ.comp (isHomotopyEquiv_telescopeProj' hB hY))
  refine h1.of_homotopic ?_
  rw [← hcomm, ContinuousMap.comp_assoc]
  have := (ContinuousMap.Homotopic.refl f).comp hs₂
  rwa [ContinuousMap.comp_id] at this

end General

end Morse
