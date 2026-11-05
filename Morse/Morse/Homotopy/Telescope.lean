import Mathlib
import Morse.Homotopy.CellAttach
import Morse.Appendix.MonotoneUnion

/-!
# Homotopy groups of increasing unions and of mapping telescopes

Milnor's countable cell complexes (Theorem 17.3, Theorem 22.1, the Bott periodicity theorems) are
increasing unions `X₀ ⊆ X₁ ⊆ ⋯`, in this project mapping telescopes of towers of iterated adjunction
spaces (`Morse.CellTower`, `Morse.IsCountableCellComplexType`). Their homotopy groups are computed
by **compactness**: a map from a cube, or from a cube times `I`, lands in a finite stage.

## Main results

* `Morse.Homotopy.surjective_homotopyGroupMap_of_exhaustion`,
  `Morse.Homotopy.injective_homotopyGroupMap_of_exhaustion`: let `A₀ ⊆ A₁ ⊆ ⋯ ⊆ X` be such that
  every compact subset of `X` lies in some `A n` (for instance when the interiors of the `A n`
  cover `X`, `Morse.Homotopy.exists_subset_of_isCompact`), and `ι : Y → X` a map into all the
  `A n`. If every corestriction `Y → A n` is onto (one-to-one) on `π_N` at `y`, so is `ι`.
* `Morse.Homotopy.bijective_homotopyGroupMap_valC_of_step`: **increasing unions**: if every step
  `A n → A (n + 1)` is bijective on `π_N` (at all basepoints), so is `A₀ → X`.
* `Morse.Homotopy.bijective_homotopyGroupMap_telescopeIncl`: **mapping telescopes**: if every step
  `F_n → F_{n+1}` of a sequence is bijective on `π_N`, so is the inclusion `F₀ → Tel(F)` of the
  bottom of the telescope. The compact sets of the telescope lie in the truncations `T_n`
  (the level is bounded on them); `F₀ → T_n` is freely homotopic, by Milnor's push to level `n`
  (`Morse.MappingTelescope.push`), to `F₀ → F_n → T_n`, and `F_n → T_n` is a homotopy equivalence
  (`Morse.MappingTelescope.isHomotopyEquiv_levelIncl`); the basepoint moves along the homotopy, so
  the change of basepoint of `Morse/Homotopy/ChangeOfBase.lean` is needed.
* `Morse.Homotopy.bijective_homotopyGroupMap_of_cellTower`, `…surjective…`: **countable cell
  complexes**: if every cell attached after the bottom stage `K₀` of a cell tower has dimension
  `≥ λ`, then `K₀ → Tel(K)` is bijective on `π_i` for `i ≤ λ - 2` and onto for `i = λ - 1`.
-/

open Set Function Topology CategoryTheory
open scoped unitInterval Topology.Homotopy

universe u

noncomputable section

namespace Morse.Homotopy

open Morse (MappingTelescope tmap tmap_tmap tmap_refl CellTower IsRelCellAttachment clampI_one)

variable {N : Type*}

/-! ### Exhaustions -/

section Exhaustion

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : ℕ → Set X}

/-- If the interiors of the increasing sets `A n` cover `X`, every compact set lies in some
`A n`. -/
theorem exists_subset_of_isCompact (hA : Monotone A) (hcov : ∀ x, ∃ n, A n ∈ 𝓝 x) {K : Set X}
    (hK : IsCompact K) : ∃ n, K ⊆ A n := by
  obtain ⟨n, hn⟩ := hK.elim_directed_cover (fun n => interior (A n)) (fun n => isOpen_interior)
    (fun x _ => mem_iUnion.2 (let ⟨n, hn⟩ := hcov x; ⟨n, mem_interior_iff_mem_nhds.2 hn⟩))
    (Monotone.directed_le fun _ _ h => interior_mono (hA h))
  exact ⟨n, hn.trans interior_subset⟩

/-- The corestriction of `f : Y → X` to a set containing its range. -/
def corestrict (f : C(Y, X)) {s : Set X} (h : ∀ y, f y ∈ s) : C(Y, s) :=
  ⟨fun y => ⟨f y, h y⟩, f.continuous.subtype_mk _⟩

/-- The inclusion of a subset, as a continuous map. -/
def valC (s : Set X) : C(s, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- **Compactness gives surjectivity**: if every compact subset of `X` lies in some `A n`, and
`ι : Y → X` lands in every `A n` by maps `Y → A n` onto on `π_N` at `y`, then `ι` is onto on
`π_N` at `y`. -/
theorem surjective_homotopyGroupMap_of_exhaustion (hK : ∀ K, IsCompact K → ∃ n, K ⊆ A n)
    (ι : C(Y, X)) (hι : ∀ n y, ι y ∈ A n) (y₀ : Y)
    (h : ∀ n, Surjective (homotopyGroupMap (N := N) (corestrict ι (hι n)) y₀)) :
    Surjective (homotopyGroupMap (N := N) ι y₀) := by
  intro c
  induction c using Quotient.inductionOn with
  | h γ =>
  obtain ⟨n, hn⟩ := hK (range γ.1) (isCompact_range γ.1.continuous)
  let γ' : Ω^ N (A n) (corestrict ι (hι n) y₀) :=
    ⟨corestrict γ.1 fun y => hn ⟨y, rfl⟩, fun y hy => Subtype.ext (γ.2 y hy)⟩
  obtain ⟨c', hc'⟩ := h n ⟦γ'⟧
  refine ⟨c', ?_⟩
  have key : homotopyGroupMap (N := N) ι y₀ =
      homotopyGroupMap (valC (A n)) _ ∘ homotopyGroupMap (corestrict ι (hι n)) y₀ :=
    homotopyGroupMap_comp (valC (A n)) (corestrict ι (hι n)) y₀
  rw [key, Function.comp_apply, hc']
  rfl

/-- **Compactness gives injectivity**: if every compact subset of `X` lies in some `A n`, and
`ι : Y → X` lands in every `A n` by maps `Y → A n` one-to-one on `π_N` at `y`, then `ι` is
one-to-one on `π_N` at `y`. -/
theorem injective_homotopyGroupMap_of_exhaustion (hK : ∀ K, IsCompact K → ∃ n, K ⊆ A n)
    (ι : C(Y, X)) (hι : ∀ n y, ι y ∈ A n) (y₀ : Y)
    (h : ∀ n, Injective (homotopyGroupMap (N := N) (corestrict ι (hι n)) y₀)) :
    Injective (homotopyGroupMap (N := N) ι y₀) := by
  intro c c'
  induction c using Quotient.inductionOn with
  | h α =>
  induction c' using Quotient.inductionOn with
  | h α' =>
  intro hcc
  obtain ⟨F⟩ := Quotient.exact hcc
  obtain ⟨n, hn⟩ := hK (range F) (isCompact_range F.continuous)
  apply h n
  refine Quotient.sound ⟨?_⟩
  exact
    { toFun := fun q => ⟨F q, hn ⟨q, rfl⟩⟩
      continuous_toFun := F.continuous.subtype_mk _
      map_zero_left := fun y => Subtype.ext (F.apply_zero y)
      map_one_left := fun y => Subtype.ext (F.apply_one y)
      prop' := fun t y hy => Subtype.ext (F.eq_fst t hy) }

theorem bijective_homotopyGroupMap_of_exhaustion (hK : ∀ K, IsCompact K → ∃ n, K ⊆ A n)
    (ι : C(Y, X)) (hι : ∀ n y, ι y ∈ A n) (y₀ : Y)
    (h : ∀ n, Bijective (homotopyGroupMap (N := N) (corestrict ι (hι n)) y₀)) :
    Bijective (homotopyGroupMap (N := N) ι y₀) :=
  ⟨injective_homotopyGroupMap_of_exhaustion hK ι hι y₀ fun n => (h n).1,
    surjective_homotopyGroupMap_of_exhaustion hK ι hι y₀ fun n => (h n).2⟩

/-- **Increasing unions**: if `A₀ ⊆ A₁ ⊆ ⋯ ⊆ X`, every compact subset of `X` lies in some `A n`,
and every inclusion `A n → A (n + 1)` is bijective on `π_N` at every basepoint, then so is
`A₀ → X`. -/
theorem bijective_homotopyGroupMap_valC_of_step (hA : Monotone A)
    (hK : ∀ K, IsCompact K → ∃ n, K ⊆ A n)
    (hstep : ∀ n (x : A n),
      Bijective (homotopyGroupMap (N := N) (ContinuousMap.inclusion (hA n.le_succ)) x))
    (x₀ : A 0) : Bijective (homotopyGroupMap (N := N) (valC (A 0)) x₀) := by
  refine bijective_homotopyGroupMap_of_exhaustion hK (valC (A 0))
    (fun n y => hA (Nat.zero_le n) y.2) x₀ fun n => ?_
  induction n with
  | zero =>
    have : corestrict (valC (A 0)) (fun y => hA (Nat.zero_le 0) y.2) = ContinuousMap.id _ :=
      ContinuousMap.ext fun _ => rfl
    rw [this, homotopyGroupMap_id]
    exact bijective_id
  | succ n ih =>
    have : corestrict (valC (A 0)) (fun y => hA (Nat.zero_le (n + 1)) y.2) =
        (ContinuousMap.inclusion (hA n.le_succ)).comp
          (corestrict (valC (A 0)) (fun y => hA (Nat.zero_le n) y.2)) :=
      ContinuousMap.ext fun _ => rfl
    rw [this, homotopyGroupMap_comp]
    exact (hstep n _).comp ih

/-- **Increasing unions, surjectivity**: if every inclusion `A n → A (n + 1)` is onto on `π_N` at
every basepoint, so is `A₀ → X`. -/
theorem surjective_homotopyGroupMap_valC_of_step (hA : Monotone A)
    (hK : ∀ K, IsCompact K → ∃ n, K ⊆ A n)
    (hstep : ∀ n (x : A n),
      Surjective (homotopyGroupMap (N := N) (ContinuousMap.inclusion (hA n.le_succ)) x))
    (x₀ : A 0) : Surjective (homotopyGroupMap (N := N) (valC (A 0)) x₀) := by
  refine surjective_homotopyGroupMap_of_exhaustion hK (valC (A 0))
    (fun n y => hA (Nat.zero_le n) y.2) x₀ fun n => ?_
  induction n with
  | zero =>
    have : corestrict (valC (A 0)) (fun y => hA (Nat.zero_le 0) y.2) = ContinuousMap.id _ :=
      ContinuousMap.ext fun _ => rfl
    rw [this, homotopyGroupMap_id]
    exact surjective_id
  | succ n ih =>
    have : corestrict (valC (A 0)) (fun y => hA (Nat.zero_le (n + 1)) y.2) =
        (ContinuousMap.inclusion (hA n.le_succ)).comp
          (corestrict (valC (A 0)) (fun y => hA (Nat.zero_le n) y.2)) :=
      ContinuousMap.ext fun _ => rfl
    rw [this, homotopyGroupMap_comp]
    exact (hstep n _).comp ih

end Exhaustion

/-! ### Mapping telescopes -/

section Telescope

variable (F : ℕ ⥤ TopCat.{u})

/-- `k ↦ (k, 0)_m`: the `m`-th space of a sequence, at the bottom of its block of the mapping
telescope. -/
def telescopeIncl (m : ℕ) : C(F.obj m, MappingTelescope F) :=
  ⟨fun k => MappingTelescope.mk F m k 0,
    (MappingTelescope.continuous_mk F m).comp (continuous_id.prodMk continuous_const)⟩

/-- Along its trajectory, the point `(k, 0)_m` reaches level `m + d` at `(c(k), 0)_{m+d}`. -/
theorem traj_self (d : ℕ) : ∀ (m : ℕ) (k : F.obj m) (n : ℕ) (h : m ≤ n), n = m + d →
    MappingTelescope.traj F d m k d = MappingTelescope.mk F n (tmap F h k) 0 := by
  induction d with
  | zero =>
    intro m k n h hn
    obtain rfl : n = m := by omega
    rw [Nat.cast_zero, MappingTelescope.traj_zero_right, tmap_refl]
  | succ d ih =>
    intro m k n h hn
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · obtain rfl : n = m + 1 := by omega
      rw [MappingTelescope.traj, if_pos (by norm_num), zero_add, Nat.cast_one, clampI_one,
        MappingTelescope.mk_one]
    · have h1 : ¬ ((d + 1 : ℕ) : ℝ) ≤ 1 := by
        have : (1 : ℝ) ≤ d := by exact_mod_cast hd
        push_cast
        linarith
      rw [MappingTelescope.traj, if_neg h1, show ((d + 1 : ℕ) : ℝ) - 1 = d by push_cast; ring,
        ih (m + 1) _ n (by omega) (by omega), tmap_tmap]

/-- Milnor's push to level `n` moves `(k, 0)_m` to `(c(k), 0)_n`. -/
theorem push_one_mk_zero {m n : ℕ} (h : m ≤ n) (k : F.obj m) :
    MappingTelescope.push F n (1, MappingTelescope.mk F m k 0) =
      MappingTelescope.mk F n (tmap F h k) 0 := by
  rw [MappingTelescope.push_mk]
  unfold MappingTelescope.pushFun
  have hmn : (m : ℝ) ≤ n := by exact_mod_cast h
  simp only [Set.Icc.coe_one, Set.Icc.coe_zero, one_mul, zero_add, sub_zero]
  rw [max_eq_right (by linarith), show (n : ℝ) - m = ((n - m : ℕ) : ℝ) by rw [Nat.cast_sub h]]
  exact traj_self F (n - m) m k n h (by omega)

theorem telescopeIncl_mem_trunc (n : ℕ) (k : F.obj 0) :
    telescopeIncl F 0 k ∈ MappingTelescope.trunc F n := by
  change MappingTelescope.level F (MappingTelescope.mk F 0 k 0) ≤ n
  simp

/-- `F₀ → T_n` is freely homotopic to `F₀ → F_n → T_n`, by the push to level `n`. -/
theorem homotopic_corestrict_telescopeIncl (n : ℕ) :
    (corestrict (telescopeIncl F 0) (telescopeIncl_mem_trunc F n)).Homotopic
      ((MappingTelescope.levelIncl F n).comp (tmap F (Nat.zero_le n))) :=
  ⟨{ toFun := fun q => ⟨MappingTelescope.push F n (q.1, MappingTelescope.mk F 0 q.2 0),
        MappingTelescope.push_mem_trunc F (telescopeIncl_mem_trunc F n q.2) q.1⟩
     continuous_toFun := ((MappingTelescope.push F n).continuous.comp (continuous_fst.prodMk
        ((telescopeIncl F 0).continuous.comp continuous_snd))).subtype_mk _
     map_zero_left := fun _ => Subtype.ext (MappingTelescope.push_zero F n _)
     map_one_left := fun k => Subtype.ext (push_one_mk_zero F (Nat.zero_le n) k) }⟩

variable [Finite N]

/-- **Mapping telescopes**: if every composite `F₀ → F_n` of a sequence is bijective on `π_N` at
`x₀`, so is `F₀ → Tel(F)`, `k ↦ (k, 0)_0`. -/
theorem bijective_homotopyGroupMap_telescopeIncl (x₀ : F.obj 0)
    (h : ∀ n, Bijective (homotopyGroupMap (N := N) (tmap F (Nat.zero_le n)) x₀)) :
    Bijective (homotopyGroupMap (N := N) (telescopeIncl F 0) x₀) := by
  refine bijective_homotopyGroupMap_of_exhaustion (fun K hK => ?_) (telescopeIncl F 0)
    (telescopeIncl_mem_trunc F) x₀ fun n => ?_
  · obtain ⟨b, hb⟩ := hK.bddAbove_image (MappingTelescope.level F).continuous.continuousOn
    obtain ⟨n, hn⟩ := exists_nat_ge b
    exact ⟨n, fun z hz => (hb ⟨z, hz, rfl⟩).trans hn⟩
  · rw [bijective_homotopyGroupMap_iff (homotopic_corestrict_telescopeIncl F n),
      homotopyGroupMap_comp]
    obtain ⟨e, he⟩ := (MappingTelescope.isHomotopyEquiv_levelIncl F n).exists_homotopyEquiv
    have hL := bijective_homotopyGroupMap_of_homotopyEquiv (N := N) e (tmap F (Nat.zero_le n) x₀)
    rw [he] at hL
    exact hL.comp (h n)

/-- **Mapping telescopes, surjectivity**: if every composite `F₀ → F_n` is onto on `π_N` at `x₀`,
so is `F₀ → Tel(F)`. -/
theorem surjective_homotopyGroupMap_telescopeIncl (x₀ : F.obj 0)
    (h : ∀ n, Surjective (homotopyGroupMap (N := N) (tmap F (Nat.zero_le n)) x₀)) :
    Surjective (homotopyGroupMap (N := N) (telescopeIncl F 0) x₀) := by
  refine surjective_homotopyGroupMap_of_exhaustion (fun K hK => ?_) (telescopeIncl F 0)
    (telescopeIncl_mem_trunc F) x₀ fun n => ?_
  · obtain ⟨b, hb⟩ := hK.bddAbove_image (MappingTelescope.level F).continuous.continuousOn
    obtain ⟨n, hn⟩ := exists_nat_ge b
    exact ⟨n, fun z hz => (hb ⟨z, hz, rfl⟩).trans hn⟩
  · rw [surjective_homotopyGroupMap_iff (homotopic_corestrict_telescopeIncl F n),
      homotopyGroupMap_comp]
    obtain ⟨e, he⟩ := (MappingTelescope.isHomotopyEquiv_levelIncl F n).exists_homotopyEquiv
    have hL := bijective_homotopyGroupMap_of_homotopyEquiv (N := N) e (tmap F (Nat.zero_le n) x₀)
    rw [he] at hL
    exact hL.2.comp (h n)

omit [Finite N] in
/-- Bijectivity of the steps `F_n → F_{n+1}` gives bijectivity of the composites `F₀ → F_n`. -/
theorem bijective_homotopyGroupMap_tmap_of_step
    (h : ∀ n (x : F.obj n), Bijective (homotopyGroupMap (N := N) (tmap F (Nat.le_succ n)) x))
    (x₀ : F.obj 0) (n : ℕ) : Bijective (homotopyGroupMap (N := N) (tmap F (Nat.zero_le n)) x₀) := by
  induction n with
  | zero =>
    have : tmap F (Nat.zero_le 0) = ContinuousMap.id _ := ContinuousMap.ext (tmap_refl F 0)
    rw [this, homotopyGroupMap_id]
    exact bijective_id
  | succ n ih =>
    have : tmap F (Nat.zero_le (n + 1)) = (tmap F (Nat.le_succ n)).comp (tmap F (Nat.zero_le n)) :=
      ContinuousMap.ext fun k => (tmap_tmap F _ _ k).symm
    rw [this, homotopyGroupMap_comp]
    exact (h n _).comp ih

omit [Finite N] in
/-- Surjectivity of the steps `F_n → F_{n+1}` gives surjectivity of the composites `F₀ → F_n`. -/
theorem surjective_homotopyGroupMap_tmap_of_step
    (h : ∀ n (x : F.obj n), Surjective (homotopyGroupMap (N := N) (tmap F (Nat.le_succ n)) x))
    (x₀ : F.obj 0) (n : ℕ) :
    Surjective (homotopyGroupMap (N := N) (tmap F (Nat.zero_le n)) x₀) := by
  induction n with
  | zero =>
    have : tmap F (Nat.zero_le 0) = ContinuousMap.id _ := ContinuousMap.ext (tmap_refl F 0)
    rw [this, homotopyGroupMap_id]
    exact surjective_id
  | succ n ih =>
    have : tmap F (Nat.zero_le (n + 1)) = (tmap F (Nat.le_succ n)).comp (tmap F (Nat.zero_le n)) :=
      ContinuousMap.ext fun k => (tmap_tmap F _ _ k).symm
    rw [this, homotopyGroupMap_comp]
    exact (h n _).comp ih

end Telescope

/-! ### Countable cell complexes -/

variable [Fintype N] {cells : ℕ → List ℕ}

/-- **Countable cell complexes**: if all the cells attached to the bottom stage `K₀` of a cell
tower (`Morse.CellTower`) have dimension `≥ |N| + 2`, the inclusion `K₀ → Tel(K)` of `K₀` into
the mapping telescope (the countable complex) is bijective on `π_N`, at every basepoint. -/
theorem bijective_homotopyGroupMap_of_cellTower (T : CellTower.{u} cells)
    (hcells : ∀ n, ∀ c ∈ cells (n + 1), Fintype.card N + 2 ≤ c) (x₀ : T.K.obj 0) :
    Bijective (homotopyGroupMap (N := N) (telescopeIncl T.K 0) x₀) :=
  bijective_homotopyGroupMap_telescopeIncl T.K x₀
    (bijective_homotopyGroupMap_tmap_of_step T.K
      (fun n x => bijective_homotopyGroupMap_of_isRelCellAttachment (T.step n) (hcells n) x)
      x₀)

/-- **Countable cell complexes, surjectivity**: if all the cells attached to `K₀` have dimension
`> |N|`, the inclusion `K₀ → Tel(K)` is onto on `π_N`. -/
theorem surjective_homotopyGroupMap_of_cellTower (T : CellTower.{u} cells)
    (hcells : ∀ n, ∀ c ∈ cells (n + 1), Fintype.card N < c) (x₀ : T.K.obj 0) :
    Surjective (homotopyGroupMap (N := N) (telescopeIncl T.K 0) x₀) :=
  surjective_homotopyGroupMap_telescopeIncl T.K x₀
    (surjective_homotopyGroupMap_tmap_of_step T.K
      (fun n x => surjective_homotopyGroupMap_of_isRelCellAttachment (T.step n) (hcells n) x)
      x₀)

end Morse.Homotopy
