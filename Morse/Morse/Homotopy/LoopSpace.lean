import Mathlib
import Morse.Homotopy.ChangeOfBase

/-!
# Loop spaces and path spaces

Milnor (§17, §22 and Part IV) passes freely between the homotopy groups of a space `X`, those of
its loop space `Ω(X; p, p)`, and those of the path space `Ω(X; p, q)`: `π_i(Ω) ≅ π_{i+1}(X)`, and
`Ω(X; p, q) ≃ Ω(X; p, p)` when `X` is path-connected. This file proves both, for Mathlib's spaces
of paths `Path p q` (compact-open topology) and Mathlib's homotopy groups.

## Main results

* `Morse.Homotopy.homotopyGroupCongr`: `π_M(X, x) ≃ π_N(X, x)` for `M ≃ N` (reindexing the cube).
* `Morse.Homotopy.homotopyGroupLoopEquiv`: **`π_M(Ω(X; x, x), const) ≃ π_{Option M}(X, x)`**, by
  uncurrying: a family of loops parametrized by the cube `I^M` is a map from the cube
  `I^{Option M} = I × I^M`, the extra coordinate being the loop parameter; the boundary conditions,
  and homotopies relative to the boundaries, correspond. Hence
  `Morse.Homotopy.homotopyGroupPiLoopEquiv`: `π_i(Ω(X; x, x)) ≃ π_{i+1}(X, x)`.
* `Morse.Homotopy.pathTransHomotopyEquiv`: for a path `ω` from `q` to `r`, `γ ↦ γ · ω` is a
  homotopy equivalence `Ω(X; p, q) → Ω(X; p, r)`, with homotopy inverse `δ ↦ δ · ω⁻¹`; and
  `Morse.Homotopy.pathHomotopyEquivLoop`: `Ω(X; p, q) ≃ Ω(X; p, p)` for path-connected `X`. The
  homotopy `(γ · ω) · ω⁻¹ ≃ γ` (`Morse.Homotopy.cancelFamily`) is explicit, so that it depends
  continuously on `γ`: at time `s` it runs through `γ` on `[0, a]`, `a = (1 + 3s)/4`, then out
  along `ω` and back, to the parameter `min(4(t - a), 2 - 2t)`.

For nonempty `M` the bijection is a group isomorphism (`Morse.Homotopy.homotopyGroupLoopMulEquiv`,
`Morse.Homotopy.homotopyGroupPiLoopMulEquiv`): uncurrying carries concatenation along a coordinate
`m` of `M` in `π_M(Ω)` to concatenation along the coordinate `some m` in `π_{Option M}(X)`.
-/

open Set Function Topology
open scoped unitInterval Topology.Homotopy

noncomputable section

namespace Morse.Homotopy

variable {X : Type*} [TopologicalSpace X]

/-! ### Reindexing the cube -/

section Congr

variable {M N : Type*} {x : X}

theorem genLoop_homotopic_congr (e : M ≃ N) {p p' : Ω^ M X x} (h : GenLoop.Homotopic p p') :
    GenLoop.Homotopic (GenLoop.congr x e p) (GenLoop.congr x e p') := by
  obtain ⟨F⟩ := h
  have hc : Continuous fun t : I^N => fun m => t (e m) :=
    continuous_pi fun m => continuous_apply (e m)
  refine ⟨
    { toFun := fun q => F (q.1, fun m => q.2 (e m))
      continuous_toFun := F.continuous.comp (continuous_fst.prodMk (hc.comp continuous_snd))
      map_zero_left := fun t => F.apply_zero _
      map_one_left := fun t => F.apply_one _
      prop' := fun s t ht => ?_ }⟩
  obtain ⟨n, hn⟩ := ht
  have hb : (fun m => t (e m)) ∈ Cube.boundary M := ⟨e.symm n, by simpa using hn⟩
  exact F.eq_fst s hb

theorem genLoop_congr_symm_congr (e : M ≃ N) (p : Ω^ M X x) :
    GenLoop.congr x e.symm (GenLoop.congr x e p) = p := by
  ext t
  simp [GenLoop.congr]

/-- **Reindexing the cube**: `π_M(X, x) ≃ π_N(X, x)` for `M ≃ N`. -/
def homotopyGroupCongr (e : M ≃ N) : HomotopyGroup M X x ≃ HomotopyGroup N X x :=
  Quotient.congr (GenLoop.congr x e).toEquiv fun p p' => by
    refine ⟨genLoop_homotopic_congr e, fun h => ?_⟩
    have := genLoop_homotopic_congr e.symm h
    change GenLoop.Homotopic (GenLoop.congr x e.symm (GenLoop.congr x e p))
      (GenLoop.congr x e.symm (GenLoop.congr x e p')) at this
    rwa [genLoop_congr_symm_congr, genLoop_congr_symm_congr] at this

theorem genLoop_congr_transAt [DecidableEq M] [DecidableEq N] (e : M ≃ N) (m : M)
    (p q : Ω^ M X x) : GenLoop.congr x e (GenLoop.transAt m p q) =
      GenLoop.transAt (e m) (GenLoop.congr x e p) (GenLoop.congr x e q) := by
  have hu : ∀ (t : I^N) (v : I),
      (fun m' => Function.update t (e m) v (e m')) = Function.update (fun m' => t (e m')) m v := by
    intro t v
    funext m'
    by_cases hm : m' = m
    · subst hm
      simp
    · rw [Function.update_of_ne hm, Function.update_of_ne (e.injective.ne hm)]
  ext t
  change (GenLoop.transAt m p q) (fun m' => t (e m')) =
    GenLoop.transAt (e m) (GenLoop.congr x e p) (GenLoop.congr x e q) t
  simp only [GenLoop.transAt, GenLoop.coe_copy]
  split_ifs with h
  · change _ = p (fun m' => Function.update t (e m) _ (e m'))
    rw [hu]
  · change _ = q (fun m' => Function.update t (e m) _ (e m'))
    rw [hu]

/-- Reindexing the cube is an isomorphism of homotopy groups. -/
def homotopyGroupCongrMulEquiv [DecidableEq M] [DecidableEq N] [Nonempty M] [Nonempty N]
    (e : M ≃ N) : HomotopyGroup M X x ≃* HomotopyGroup N X x where
  toEquiv := homotopyGroupCongr e
  map_mul' a b := Quotient.inductionOn₂ a b fun p q => by
    let m : M := Classical.arbitrary M
    simp only [HomotopyGroup.mul_spec (i := m)]
    change (⟦GenLoop.congr x e (GenLoop.transAt m q p)⟧ : HomotopyGroup N X x) =
      ((· * ·) : _ → _ → HomotopyGroup N X x) ⟦GenLoop.congr x e p⟧ ⟦GenLoop.congr x e q⟧
    simp only [HomotopyGroup.mul_spec (i := e m)]
    rw [genLoop_congr_transAt]

end Congr

/-! ### The loop space -/

section Loop

variable {M : Type*} {x : X}

/-- The point of `I^{Option M}` with loop parameter `t` and cube coordinates `z`. -/
def optionPoint (t : I) (z : I^M) : I^(Option M) :=
  fun j => j.elim t z

theorem continuous_optionPoint : Continuous fun q : I × (I^M) => optionPoint q.1 q.2 :=
  continuous_pi fun j => by
    cases j with
    | none => exact continuous_fst
    | some m => exact (continuous_apply m).comp continuous_snd

theorem optionPoint_mem_boundary_of_left {t : I} (ht : t = 0 ∨ t = 1) (z : I^M) :
    optionPoint t z ∈ Cube.boundary (Option M) :=
  ⟨none, ht⟩

theorem optionPoint_mem_boundary_of_right (t : I) {z : I^M} (hz : z ∈ Cube.boundary M) :
    optionPoint t z ∈ Cube.boundary (Option M) := by
  obtain ⟨m, hm⟩ := hz
  exact ⟨some m, hm⟩

theorem optionPoint_eta (y : I^(Option M)) : optionPoint (y none) (fun m => y (some m)) = y := by
  funext j
  cases j <;> rfl

/-- A generalized loop in the loop space, uncurried to a generalized loop in `X`. -/
def loopUncurry (γ : Ω^ M (Path x x) (Path.refl x)) : Ω^ (Option M) X x :=
  ⟨⟨fun y => γ (fun m => y (some m)) (y none), continuous_eval.comp
      ((γ.1.continuous.comp (continuous_pi fun m => continuous_apply (some m))).prodMk
        (continuous_apply none))⟩,
    fun y hy => by
      obtain ⟨j, hj⟩ := hy
      cases j with
      | none =>
        rcases hj with hj | hj
        · change γ _ (y none) = x
          rw [hj, Path.source]
        · change γ _ (y none) = x
          rw [hj, Path.target]
      | some m =>
        change γ _ (y none) = x
        rw [GenLoop.boundary γ _ ⟨m, hj⟩]
        rfl⟩

/-- The path `t ↦ β(t, z)` of a generalized loop `β` in `X` at `x`, for `z ∈ I^M`. -/
def loopCurryPath (β : Ω^ (Option M) X x) (z : I^M) : Path x x where
  toFun t := β (optionPoint t z)
  continuous_toFun := β.1.continuous.comp (continuous_optionPoint.comp
    (continuous_id.prodMk continuous_const))
  source' := GenLoop.boundary β _ (optionPoint_mem_boundary_of_left (Or.inl rfl) z)
  target' := GenLoop.boundary β _ (optionPoint_mem_boundary_of_left (Or.inr rfl) z)

theorem continuous_loopCurryPath (β : Ω^ (Option M) X x) : Continuous (loopCurryPath β) :=
  Path.continuous_uncurry_iff.1 (β.1.continuous.comp (continuous_optionPoint.comp
    (continuous_snd.prodMk continuous_fst)))

/-- A generalized loop in `X`, curried to a generalized loop in the loop space. -/
def loopCurry (β : Ω^ (Option M) X x) : Ω^ M (Path x x) (Path.refl x) :=
  ⟨⟨loopCurryPath β, continuous_loopCurryPath β⟩, fun z hz => by
    ext t
    exact GenLoop.boundary β _ (optionPoint_mem_boundary_of_right t hz)⟩

theorem loopCurry_loopUncurry (γ : Ω^ M (Path x x) (Path.refl x)) :
    loopCurry (loopUncurry γ) = γ := by
  ext z t
  rfl

theorem loopUncurry_loopCurry (β : Ω^ (Option M) X x) : loopUncurry (loopCurry β) = β := by
  ext y
  change β (optionPoint (y none) fun m => y (some m)) = β y
  rw [optionPoint_eta]

theorem loopUncurry_homotopic {γ γ' : Ω^ M (Path x x) (Path.refl x)}
    (h : GenLoop.Homotopic γ γ') : GenLoop.Homotopic (loopUncurry γ) (loopUncurry γ') := by
  obtain ⟨F⟩ := h
  refine ⟨
    { toFun := fun q => F (q.1, fun m => q.2 (some m)) (q.2 none)
      continuous_toFun := continuous_eval.comp ((F.continuous.comp (continuous_fst.prodMk
        ((continuous_pi fun m => continuous_apply (some m)).comp continuous_snd))).prodMk
          ((continuous_apply none).comp continuous_snd))
      map_zero_left := fun y => by
        change F (0, _) _ = γ _ _
        rw [F.apply_zero]
        rfl
      map_one_left := fun y => by
        change F (1, _) _ = γ' _ _
        rw [F.apply_one]
        rfl
      prop' := fun s y hy => ?_ }⟩
  change F (s, fun m => y (some m)) (y none) = γ (fun m => y (some m)) (y none)
  obtain ⟨j, hj⟩ := hy
  cases j with
  | none => rcases hj with hj | hj <;> simp [hj]
  | some m => rw [F.eq_fst s ⟨m, hj⟩]; rfl

theorem loopCurry_homotopic {β β' : Ω^ (Option M) X x} (h : GenLoop.Homotopic β β') :
    GenLoop.Homotopic (loopCurry β) (loopCurry β') := by
  obtain ⟨F⟩ := h
  have hF : ∀ q : I × (I^M), Continuous fun t : I => F (q.1, optionPoint t q.2) := fun q =>
    F.continuous.comp (continuous_const.prodMk (continuous_optionPoint.comp
      (continuous_id.prodMk continuous_const)))
  let G : I × (I^M) → Path x x := fun q =>
    { toFun := fun t => F (q.1, optionPoint t q.2)
      continuous_toFun := hF q
      source' := by
        rw [F.eq_fst _ (optionPoint_mem_boundary_of_left (Or.inl rfl) _)]
        exact GenLoop.boundary β _ (optionPoint_mem_boundary_of_left (Or.inl rfl) _)
      target' := by
        rw [F.eq_fst _ (optionPoint_mem_boundary_of_left (Or.inr rfl) _)]
        exact GenLoop.boundary β _ (optionPoint_mem_boundary_of_left (Or.inr rfl) _) }
  have hG : Continuous G := Path.continuous_uncurry_iff.1 (F.continuous.comp
    ((continuous_fst.comp continuous_fst).prodMk (continuous_optionPoint.comp
      (continuous_snd.prodMk (continuous_snd.comp continuous_fst)))))
  refine ⟨
    { toFun := G
      continuous_toFun := hG
      map_zero_left := fun z => by ext t; exact F.apply_zero _
      map_one_left := fun z => by ext t; exact F.apply_one _
      prop' := fun s z hz => by
        ext t
        exact F.eq_fst s (optionPoint_mem_boundary_of_right t hz) }⟩

/-- **The homotopy groups of the loop space**: `π_M(Ω(X; x, x), const) ≃ π_{Option M}(X, x)`, by
uncurrying. -/
def homotopyGroupLoopEquiv :
    HomotopyGroup M (Path x x) (Path.refl x) ≃ HomotopyGroup (Option M) X x where
  toFun := Quotient.map loopUncurry fun _ _ h => loopUncurry_homotopic h
  invFun := Quotient.map loopCurry fun _ _ h => loopCurry_homotopic h
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h γ => exact congrArg _ (loopCurry_loopUncurry γ)
  right_inv c := by
    induction c using Quotient.inductionOn with
    | h β => exact congrArg _ (loopUncurry_loopCurry β)

/-- **`π_i(ΩX) ≃ π_{i+1}(X)`** for the loop space `Ω(X; x, x)` (Mathlib's `Path x x`). -/
def homotopyGroupPiLoopEquiv (i : ℕ) :
    HomotopyGroup.Pi i (Path x x) (Path.refl x) ≃ HomotopyGroup.Pi (i + 1) X x :=
  homotopyGroupLoopEquiv.trans (homotopyGroupCongr (finSuccEquiv i).symm)

theorem update_some_comp [DecidableEq M] (y : I^(Option M)) (m : M) (v : I) :
    (fun m' => Function.update y (some m) v (some m')) =
      Function.update (fun m' => y (some m')) m v := by
  funext m'
  by_cases hm : m' = m
  · subst hm
    simp
  · rw [Function.update_of_ne hm, Function.update_of_ne (Option.some_injective _ |>.ne hm)]

theorem loopUncurry_transAt [DecidableEq M] (m : M) (p q : Ω^ M (Path x x) (Path.refl x)) :
    loopUncurry (GenLoop.transAt m p q) =
      GenLoop.transAt (some m) (loopUncurry p) (loopUncurry q) := by
  ext y
  simp only [GenLoop.transAt, GenLoop.coe_copy, loopUncurry, GenLoop.mk_apply,
    ContinuousMap.coe_mk]
  split_ifs with h
  · change _ = p (fun m' => Function.update y (some m) _ (some m'))
      (Function.update y (some m) _ none)
    rw [update_some_comp, Function.update_of_ne (Option.some_ne_none m).symm]
  · change _ = q (fun m' => Function.update y (some m) _ (some m'))
      (Function.update y (some m) _ none)
    rw [update_some_comp, Function.update_of_ne (Option.some_ne_none m).symm]

/-- **`π_M(ΩX) ≅ π_{Option M}(X)` as groups** (`M` nonempty): uncurrying carries concatenation
along a coordinate `m` of the loops of loops to concatenation along the coordinate `m` of the
cube `I^{Option M}`. -/
def homotopyGroupLoopMulEquiv [DecidableEq M] [Nonempty M] :
    HomotopyGroup M (Path x x) (Path.refl x) ≃* HomotopyGroup (Option M) X x where
  toEquiv := homotopyGroupLoopEquiv
  map_mul' a b := Quotient.inductionOn₂ a b fun p q => by
    let m : M := Classical.arbitrary M
    simp only [HomotopyGroup.mul_spec (i := m)]
    change (⟦loopUncurry (GenLoop.transAt m q p)⟧ : HomotopyGroup (Option M) X x) =
      ((· * ·) : _ → _ → HomotopyGroup (Option M) X x) ⟦loopUncurry p⟧ ⟦loopUncurry q⟧
    simp only [HomotopyGroup.mul_spec (i := some m)]
    rw [loopUncurry_transAt]

/-- **`π_{i+1}(ΩX) ≅ π_{i+2}(X)` as groups.** -/
def homotopyGroupPiLoopMulEquiv (i : ℕ) :
    HomotopyGroup.Pi (i + 1) (Path x x) (Path.refl x) ≃* HomotopyGroup.Pi (i + 2) X x :=
  homotopyGroupLoopMulEquiv.trans (homotopyGroupCongrMulEquiv (finSuccEquiv (i + 1)).symm)

end Loop

/-! ### Path spaces between different endpoints -/

section PathSpace

variable {a b c : X}

/-- The cancellation family: at time `s`, the path running through `γ` on `[0, a]`,
`a = (1 + 3s)/4`, then out along `ω` and back, to the parameter `min(4(t - a), 2 - 2t)`. At
`s = 0` it is `(γ · ω) · ω⁻¹`, at `s = 1` it is `γ`. -/
def cancelFamily (ω : Path b c) (q : I × Path a b) : Path a b where
  toFun t := if (t : ℝ) ≤ (1 + 3 * (q.1 : ℝ)) / 4 then q.2.extend (t / ((1 + 3 * (q.1 : ℝ)) / 4))
    else ω.extend (min (4 * (t - (1 + 3 * (q.1 : ℝ)) / 4)) (2 - 2 * t))
  continuous_toFun := by
    have ha : Continuous fun _ : I => (1 + 3 * (q.1 : ℝ)) / 4 := continuous_const
    refine Continuous.if_le ?_ ?_ continuous_subtype_val ha ?_
    · exact q.2.continuous_extend.comp (continuous_subtype_val.div_const _)
    · exact ω.continuous_extend.comp ((continuous_const.mul (continuous_subtype_val.sub
        continuous_const)).min (continuous_const.sub (continuous_const.mul
          continuous_subtype_val)))
    · intro t ht
      have ha0 : (0 : ℝ) < (1 + 3 * (q.1 : ℝ)) / 4 := by have := q.1.2.1; positivity
      rw [ht, div_self ha0.ne', Path.extend_one, sub_self, mul_zero, min_eq_left (by
        have := q.1.2.2; linarith), Path.extend_zero]
  source' := by
    have ha0 : (0 : ℝ) ≤ (1 + 3 * (q.1 : ℝ)) / 4 := by have := q.1.2.1; positivity
    simp only [Set.Icc.coe_zero, zero_div]
    rw [if_pos ha0, Path.extend_zero]
  target' := by
    simp only [Set.Icc.coe_one]
    split_ifs with h
    · have h1 : (1 + 3 * (q.1 : ℝ)) / 4 = 1 := le_antisymm (by linarith [q.1.2.2]) h
      rw [h1, div_one, Path.extend_one]
    · rw [min_eq_right (by linarith), show (2 : ℝ) - 2 * 1 = 0 by norm_num, Path.extend_zero]

theorem continuous_cancelFamily (ω : Path b c) : Continuous (cancelFamily (a := a) ω) := by
  refine Path.continuous_uncurry_iff.1 ?_
  have ha : Continuous fun q : (I × Path a b) × I => (1 + 3 * (q.1.1 : ℝ)) / 4 :=
    (continuous_const.add (continuous_const.mul (continuous_subtype_val.comp
      (continuous_fst.comp continuous_fst)))).div_const _
  have ht : Continuous fun q : (I × Path a b) × I => (q.2 : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  refine Continuous.if_le ?_ ?_ ht ha ?_
  · refine Continuous.pathExtend (γ := fun q : (I × Path a b) × I => q.1.2) ?_
      (ht.div ha fun q => by have := q.1.1.2.1; positivity)
    exact continuous_eval.comp ((continuous_snd.comp (continuous_fst.comp continuous_fst)).prodMk
      continuous_snd)
  · exact ω.continuous_extend.comp ((continuous_const.mul (ht.sub ha)).min
      (continuous_const.sub (continuous_const.mul ht)))
  · intro q hq
    have ha0 : (0 : ℝ) < (1 + 3 * (q.1.1 : ℝ)) / 4 := by have := q.1.1.2.1; positivity
    rw [hq, div_self ha0.ne', Path.extend_one, sub_self, mul_zero, min_eq_left (by
      have := q.1.1.2.2; linarith), Path.extend_zero]

theorem cancelFamily_zero (ω : Path b c) (γ : Path a b) :
    cancelFamily ω (0, γ) = (γ.trans ω).trans ω.symm := by
  ext t
  change (if (t : ℝ) ≤ (1 + 3 * ((0 : I) : ℝ)) / 4 then _ else _) = _
  simp only [Set.Icc.coe_zero, mul_zero, add_zero, Path.trans_apply, Path.symm_apply,
    Function.comp_apply]
  by_cases h1 : (t : ℝ) ≤ 1 / 4
  · rw [if_pos (by linarith), dif_pos (by linarith), dif_pos (by linarith),
      Path.extend_apply _ (show (t : ℝ) / (1 / 4) ∈ Icc (0 : ℝ) 1 from
        ⟨div_nonneg t.2.1 (by norm_num), by rw [div_le_one (by norm_num)]; exact h1⟩)]
    congr 1
    apply Subtype.ext
    push_cast
    ring
  · rw [if_neg (by linarith)]
    by_cases h2 : (t : ℝ) ≤ 1 / 2
    · rw [dif_pos h2, dif_neg (by linarith), min_eq_left (by linarith),
        Path.extend_apply _ (show 4 * ((t : ℝ) - 1 / 4) ∈ Icc (0 : ℝ) 1 from
          ⟨by linarith, by linarith⟩)]
      congr 1
      apply Subtype.ext
      push_cast
      ring
    · rw [dif_neg h2, min_eq_right (by linarith), Path.extend_apply]
      · congr 1
        apply Subtype.ext
        simp only [unitInterval.coe_symm_eq]
        ring
      · constructor <;> linarith [t.2.2]

theorem cancelFamily_one (ω : Path b c) (γ : Path a b) : cancelFamily ω (1, γ) = γ := by
  ext t
  change (if (t : ℝ) ≤ (1 + 3 * ((1 : I) : ℝ)) / 4 then _ else _) = _
  simp only [Set.Icc.coe_one]
  rw [if_pos (by linarith [t.2.2]), show (1 + 3 * 1 : ℝ) / 4 = 1 by norm_num, div_one,
    Path.extend_extends']

/-- `(γ · ω) · ω⁻¹ ≃ γ`, continuously in `γ`. -/
theorem homotopic_trans_trans_symm (ω : Path b c) :
    (⟨fun γ : Path a b => (γ.trans ω).trans ω.symm,
      (continuous_id.path_trans continuous_const).path_trans continuous_const⟩ :
        C(Path a b, Path a b)).Homotopic (ContinuousMap.id _) :=
  ⟨{ toFun := cancelFamily ω
     continuous_toFun := continuous_cancelFamily ω
     map_zero_left := cancelFamily_zero ω
     map_one_left := cancelFamily_one ω }⟩

/-- **Changing the endpoint**: for a path `ω` from `b` to `c`, `γ ↦ γ · ω` is a homotopy
equivalence `Ω(X; a, b) → Ω(X; a, c)`, with homotopy inverse `δ ↦ δ · ω⁻¹`. -/
def pathTransHomotopyEquiv (ω : Path b c) : ContinuousMap.HomotopyEquiv (Path a b) (Path a c) where
  toFun := ⟨fun γ => γ.trans ω, continuous_id.path_trans continuous_const⟩
  invFun := ⟨fun δ => δ.trans ω.symm, continuous_id.path_trans continuous_const⟩
  left_inv := homotopic_trans_trans_symm ω
  right_inv := by
    have := homotopic_trans_trans_symm (a := a) ω.symm
    rwa [Path.symm_symm] at this

/-- **`Ω(X; p, q) ≃ Ω(X; p, p)`** for a path-connected space `X`. -/
def pathHomotopyEquivLoop [PathConnectedSpace X] (p q : X) :
    ContinuousMap.HomotopyEquiv (Path p q) (Path p p) :=
  pathTransHomotopyEquiv (PathConnectedSpace.somePath q p)

end PathSpace

end Morse.Homotopy
