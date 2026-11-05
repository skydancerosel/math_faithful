import Mathlib
import Morse.Homotopy.Basic

/-!
# Change of basepoint, and the homotopy invariance of homotopy groups

A map `f : X → Y` which is only *freely* homotopic to `g` (the basepoint `x₀` is allowed to move,
along the path `γ(t) = H(t, x₀)`) does not induce the same map on homotopy groups as `g`: the two
differ by the change of basepoint along `γ`. This file constructs the change of basepoint for the
homotopy groups `π_N(Y, y) = HomotopyGroup N Y y` of Mathlib, for a finite index type `N`, and
deduces that homotopy equivalences induce bijections on all homotopy groups, at all basepoints.
It is what makes the cell-attachment theorems (`Morse/Homotopy/CellAttach.lean`) usable for spaces
which only have the homotopy type of a cell complex (Milnor, Theorem 22.1).

## The frame construction

Measure the distance of `y ∈ I^N` from the centre of the cube in the sup norm,
`d(y) = max_j |y_j - 1/2| ∈ [0, 1/2]` (`Morse.Homotopy.cubeDist`); `d(y) = 1/2` exactly on the
boundary `∂I^N`. For `0 < r ≤ 1/2`, `Morse.Homotopy.frame` glues a map `inner` on the cube
`{d ≤ r}`, rescaled to the whole cube (`Morse.Homotopy.cubeScale`), to a map `outer(d(y))` on the
"annulus" `{r ≤ d ≤ 1/2}`, constant on each level set of `d`; the two agree on `{d = r}` when
`inner` is constant on `∂I^N` with value `outer(r)`. All homotopies below are frames depending
continuously on a parameter.

* **Change of basepoint** along a path `γ` from `y₀` to `y₁` (`Morse.Homotopy.changeBase`): `α` on
  the cube of radius `1/4`, and `γ(4d - 1)` on the annulus. It is compatible with homotopies
  relative to `∂I^N`, and the change along `γ⁻¹` is a homotopy inverse
  (`Morse.Homotopy.changeBase_symm_changeBase`): the composite runs out along `γ` and back on the
  annulus, and the frame with inner radius `(1 + 3s)/8` and outer part
  `γ(min(8(d - r), 2 - 4d))` shrinks the excursion. So the change of basepoint is a bijection
  `π_N(Y, y₀) ≃ π_N(Y, y₁)` (`Morse.Homotopy.changeBaseEquiv`).
* **Free homotopies** (`Morse.Homotopy.homotopyGroupMap_eq_changeBaseMap`): if `H : f ≃ g`, then
  `g_* = (change along t ↦ H(t, x₀)) ∘ f_*`. The homotopy is the frame with inner radius
  `(1 + s)/4`, inner part `H(s, α(·))` and outer part `t ↦ H(4t - 1, x₀)`: at `s = 1` the annulus
  has disappeared and the frame is `g ∘ α`.

## Main results

* `Morse.Homotopy.bijective_homotopyGroupMap_iff`, `injective_…`, `surjective_…`: homotopic maps
  have bijective (injective, surjective) induced maps together.
* `Morse.Homotopy.bijective_homotopyGroupMap_of_homotopyEquiv`: a homotopy equivalence induces
  bijections `π_N(X, x) → π_N(Y, f x)` for every `x`.
* `Morse.Homotopy.bijective_homotopyGroupMap_iff_of_square` (and the injective and surjective
  versions): **transfer along homotopy-commutative squares** of homotopy equivalences: if
  `e ∘ ι ≃ j ∘ a` with `a`, `e` homotopy equivalences, then `ι_*` is bijective at `x` iff `j_*` is
  bijective at `a x`.
-/

open Set Function Topology
open scoped unitInterval Topology.Homotopy

noncomputable section

namespace Morse.Homotopy

variable {N : Type*} [Fintype N] {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-! ### The sup-distance from the centre of the cube -/

/-- The distance `max_j |y_j - 1/2|` of `y ∈ I^N` from the centre of the cube (sup norm). -/
def cubeDist (y : I^N) : ℝ :=
  ‖fun j => (y j : ℝ) - 1 / 2‖

theorem continuous_cubeDist : Continuous (cubeDist (N := N)) :=
  continuous_norm.comp (continuous_pi fun j =>
    (continuous_subtype_val.comp (continuous_apply j)).sub continuous_const)

theorem abs_le_cubeDist (y : I^N) (j : N) : |(y j : ℝ) - 1 / 2| ≤ cubeDist y := by
  have := norm_le_pi_norm (fun j => (y j : ℝ) - 1 / 2) j
  rwa [Real.norm_eq_abs] at this

theorem cubeDist_le_half (y : I^N) : cubeDist y ≤ 1 / 2 :=
  (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun j => by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [(y j).2.1, (y j).2.2]

theorem cubeDist_of_mem_boundary {y : I^N} (hy : y ∈ Cube.boundary N) : cubeDist y = 1 / 2 := by
  obtain ⟨j, hj⟩ := hy
  refine le_antisymm (cubeDist_le_half y) ?_
  have h := abs_le_cubeDist y j
  rcases hj with h' | h' <;> rw [h'] at h <;> norm_num at h <;> linarith

theorem cubeDist_of_isEmpty [IsEmpty N] (y : I^N) : cubeDist y = 0 := by
  have : (fun j => (y j : ℝ) - 1 / 2) = 0 := funext fun j => isEmptyElim j
  rw [cubeDist, this, norm_zero]

theorem exists_abs_eq_cubeDist [Nonempty N] (y : I^N) :
    ∃ j, |(y j : ℝ) - 1 / 2| = cubeDist y := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun b => ‖(y b : ℝ) - 1 / 2‖₊)
  refine ⟨j, ?_⟩
  rw [cubeDist, Pi.norm_def, hj, coe_nnnorm, Real.norm_eq_abs]

/-! ### Rescaling the cube of radius `r` -/

/-- The affine map from the cube of radius `r` about the centre onto `I^N` (clamped outside). -/
def cubeScale (r : ℝ) (y : I^N) : I^N :=
  fun j => Set.projIcc 0 1 zero_le_one (((y j : ℝ) - 1 / 2) / (2 * r) + 1 / 2)

omit [Fintype N] in
theorem continuous_cubeScale {P : Type*} [TopologicalSpace P] {r : P → ℝ} (hr : Continuous r)
    (hr0 : ∀ p, 0 < r p) : Continuous fun q : P × (I^N) => cubeScale (r q.1) q.2 :=
  continuous_pi fun j => continuous_projIcc.comp
    ((((continuous_subtype_val.comp ((continuous_apply j).comp continuous_snd)).sub
      continuous_const).div (continuous_const.mul (hr.comp continuous_fst))
        fun q => (mul_pos two_pos (hr0 q.1)).ne').add continuous_const)

theorem coe_cubeScale {r : ℝ} (hr : 0 < r) {y : I^N} (hy : cubeDist y ≤ r) (j : N) :
    (cubeScale r y j : ℝ) = ((y j : ℝ) - 1 / 2) / (2 * r) + 1 / 2 := by
  have h := (abs_le_cubeDist y j).trans hy
  rw [abs_le] at h
  have h2r : 0 < 2 * r := by positivity
  have h1 : -(1 / 2) ≤ ((y j : ℝ) - 1 / 2) / (2 * r) := by
    rw [le_div_iff₀ h2r]
    linarith
  have h2 : ((y j : ℝ) - 1 / 2) / (2 * r) ≤ 1 / 2 := by
    rw [div_le_iff₀ h2r]
    linarith
  simp only [cubeScale]
  rw [Set.projIcc_of_mem _ ⟨by linarith, by linarith⟩]

omit [Fintype N] in
theorem cubeScale_half [Finite N] (y : I^N) : cubeScale (1 / 2) y = y := by
  have := Fintype.ofFinite N
  funext j
  apply Subtype.ext
  rw [coe_cubeScale (by norm_num) (cubeDist_le_half y)]
  ring

theorem cubeDist_cubeScale {r : ℝ} (hr : 0 < r) {y : I^N} (hy : cubeDist y ≤ r) :
    cubeDist (cubeScale r y) = cubeDist y / (2 * r) := by
  have : (fun j => (cubeScale r y j : ℝ) - 1 / 2) = (2 * r)⁻¹ • fun j => (y j : ℝ) - 1 / 2 := by
    funext j
    rw [coe_cubeScale hr hy, Pi.smul_apply, smul_eq_mul]
    ring
  rw [cubeDist, this, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), cubeDist]
  ring

theorem cubeScale_mem_boundary {r : ℝ} (hr : 0 < r) {y : I^N} (hy : cubeDist y = r) :
    cubeScale r y ∈ Cube.boundary N := by
  have hN : Nonempty N := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [cubeDist_of_isEmpty] at hy
    linarith
  obtain ⟨j, hj⟩ := exists_abs_eq_cubeDist y
  refine ⟨j, ?_⟩
  have hc := coe_cubeScale hr hy.le j
  rw [hy] at hj
  rcases (abs_eq hr.le).1 hj with h | h
  · right
    apply Subtype.ext
    rw [hc, h, Set.Icc.coe_one]
    field_simp
    ring
  · left
    apply Subtype.ext
    rw [hc, h, Set.Icc.coe_zero]
    field_simp
    ring

theorem cubeScale_cubeScale {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') (hr1 : r ≤ 1 / 2) {y : I^N}
    (hy : cubeDist y ≤ 2 * r * r') : cubeScale r (cubeScale r' y) = cubeScale (2 * r * r') y := by
  have hy' : cubeDist y ≤ r' := hy.trans (by nlinarith)
  have h2 : cubeDist (cubeScale r' y) ≤ r := by
    rw [cubeDist_cubeScale hr' hy', div_le_iff₀ (by positivity)]
    linarith
  funext j
  apply Subtype.ext
  rw [coe_cubeScale hr h2, coe_cubeScale hr' hy', coe_cubeScale (by positivity) hy]
  field_simp
  ring

/-! ### Frames -/

/-- **The frame construction**: for a parameter `p`, the map which is `inner(p, ·)`, rescaled, on
the cube `{d ≤ r(p)}` about the centre, and `outer(p, d(y))` on `{d ≥ r(p)}`, where `d` is the
sup-distance from the centre (`Morse.Homotopy.cubeDist`). -/
def frame {P : Type*} (r : P → ℝ) (inner : P × (I^N) → Y) (outer : P × ℝ → Y) (q : P × I^N) : Y :=
  if cubeDist q.2 ≤ r q.1 then inner (q.1, cubeScale (r q.1) q.2) else outer (q.1, cubeDist q.2)

omit [TopologicalSpace Y] in
theorem frame_apply {P : Type*} (r : P → ℝ) (inner : P × (I^N) → Y) (outer : P × ℝ → Y) (p : P)
    (y : I^N) : frame r inner outer (p, y) =
      if cubeDist y ≤ r p then inner (p, cubeScale (r p) y) else outer (p, cubeDist y) :=
  rfl

theorem continuous_frame {P : Type*} [TopologicalSpace P] {r : P → ℝ} (hr : Continuous r)
    (hr0 : ∀ p, 0 < r p) {inner : P × (I^N) → Y} (hin : Continuous inner) {outer : P × ℝ → Y}
    (hout : Continuous outer) (hc : ∀ p, ∀ y ∈ Cube.boundary N, inner (p, y) = outer (p, r p)) :
    Continuous (frame r inner outer) := by
  refine Continuous.if_le (hin.comp (continuous_fst.prodMk (continuous_cubeScale hr hr0)))
    (hout.comp (continuous_fst.prodMk (continuous_cubeDist.comp continuous_snd)))
    (continuous_cubeDist.comp continuous_snd) (hr.comp continuous_fst) fun q hq => ?_
  rw [hc _ _ (cubeScale_mem_boundary (hr0 _) hq), hq]

omit [TopologicalSpace Y] in
theorem frame_of_mem_boundary {P : Type*} {r : P → ℝ} (hr1 : ∀ p, r p ≤ 1 / 2)
    {inner : P × (I^N) → Y} {outer : P × ℝ → Y}
    (hc : ∀ p, ∀ y ∈ Cube.boundary N, inner (p, y) = outer (p, r p)) (p : P) {y : I^N}
    (hy : y ∈ Cube.boundary N) : frame r inner outer (p, y) = outer (p, 1 / 2) := by
  have hd := cubeDist_of_mem_boundary hy
  rw [frame_apply]
  split_ifs with h
  · have hr : r p = 1 / 2 := le_antisymm (hr1 p) (hd ▸ h)
    rw [hr, cubeScale_half, hc p y hy, hr]
  · rw [hd]

/-- **A frame with a parameter in `I` is a homotopy relative to `∂I^N`.** -/
theorem homotopic_of_frame {y₁ : Y} {α β : Ω^ N Y y₁} {r : I → ℝ} (hr : Continuous r)
    (hr0 : ∀ s, 0 < r s) (hr1 : ∀ s, r s ≤ 1 / 2) {inner : I × (I^N) → Y} (hin : Continuous inner)
    {outer : I × ℝ → Y} (hout : Continuous outer)
    (hc : ∀ s, ∀ y ∈ Cube.boundary N, inner (s, y) = outer (s, r s))
    (hbd : ∀ s, outer (s, 1 / 2) = y₁)
    (h0 : ∀ y, frame r inner outer (0, y) = α y) (h1 : ∀ y, frame r inner outer (1, y) = β y) :
    GenLoop.Homotopic α β :=
  ⟨{ toFun := frame r inner outer
     continuous_toFun := continuous_frame hr hr0 hin hout hc
     map_zero_left := h0
     map_one_left := h1
     prop' := fun s y hy => by
       change frame r inner outer (s, y) = α y
       rw [frame_of_mem_boundary hr1 hc s hy, hbd]
       exact (GenLoop.boundary α y hy).symm }⟩

/-! ### Change of basepoint -/

variable {y₀ y₁ : Y}

theorem continuous_changeBaseOuter (γ : Path y₀ y₁) {P : Type*} [TopologicalSpace P] :
    Continuous fun q : P × ℝ => γ.extend (4 * q.2 - 1) :=
  γ.continuous_extend.comp ((continuous_const.mul continuous_snd).sub continuous_const)

/-- **Change of basepoint along a path** `γ` from `y₀` to `y₁`: the generalized loop `α` at `y₀`
on the cube of radius `1/4` about the centre, and `γ(4d - 1)` at sup-distance `d ≥ 1/4` from the
centre. -/
def changeBase (γ : Path y₀ y₁) (α : Ω^ N Y y₀) : Ω^ N Y y₁ :=
  ⟨⟨fun y => frame (fun _ : Unit => (1 / 4 : ℝ)) (fun q => α q.2)
      (fun q => γ.extend (4 * q.2 - 1)) ((), y),
    (continuous_frame (inner := fun q : Unit × (I^N) => α q.2) continuous_const
      (fun _ => by norm_num) (α.1.continuous.comp continuous_snd)
      (continuous_changeBaseOuter γ) (fun _ y hy => by
        change α y = γ.extend (4 * (1 / 4) - 1)
        rw [GenLoop.boundary α y hy, show (4 : ℝ) * (1 / 4) - 1 = 0 by norm_num,
          Path.extend_zero])).comp (continuous_const.prodMk continuous_id)⟩,
    fun y hy => by
      change frame (fun _ : Unit => (1 / 4 : ℝ)) (fun q : Unit × (I^N) => α q.2)
        (fun q => γ.extend (4 * q.2 - 1)) ((), y) = y₁
      rw [frame_of_mem_boundary (inner := fun q : Unit × (I^N) => α q.2)
        (fun _ => by norm_num) (fun _ y hy => by
        change α y = γ.extend (4 * (1 / 4) - 1)
        rw [GenLoop.boundary α y hy, show (4 : ℝ) * (1 / 4) - 1 = 0 by norm_num,
          Path.extend_zero]) () hy]
      simp only
      rw [show (4 : ℝ) * (1 / 2) - 1 = 1 by norm_num, Path.extend_one]⟩

theorem changeBase_apply (γ : Path y₀ y₁) (α : Ω^ N Y y₀) (y : I^N) :
    changeBase γ α y = if cubeDist y ≤ 1 / 4 then α (cubeScale (1 / 4) y)
      else γ.extend (4 * cubeDist y - 1) :=
  rfl

theorem changeBase_homotopic (γ : Path y₀ y₁) {α α' : Ω^ N Y y₀}
    (h : GenLoop.Homotopic α α') : GenLoop.Homotopic (changeBase γ α) (changeBase γ α') := by
  obtain ⟨F⟩ := h
  refine homotopic_of_frame (r := fun _ => 1 / 4) continuous_const (fun _ => by norm_num)
    (fun _ => by norm_num) (inner := fun q => F q) F.continuous
    (outer := fun q => γ.extend (4 * q.2 - 1)) (continuous_changeBaseOuter γ) ?_ ?_ ?_ ?_
  · intro s y hy
    simp only
    rw [F.eq_fst s hy, show (α : C(I^N, Y)) y = α y from rfl, GenLoop.boundary α y hy,
      show (4 : ℝ) * (1 / 4) - 1 = 0 by norm_num, Path.extend_zero]
  · intro s
    simp only
    rw [show (4 : ℝ) * (1 / 2) - 1 = 1 by norm_num, Path.extend_one]
  · intro y
    rw [frame_apply, changeBase_apply, F.apply_zero]
    rfl
  · intro y
    rw [frame_apply, changeBase_apply, F.apply_one]
    rfl

/-- The change of basepoint on homotopy groups. -/
def changeBaseMap (γ : Path y₀ y₁) : HomotopyGroup N Y y₀ → HomotopyGroup N Y y₁ :=
  Quotient.map (changeBase γ) fun _ _ h => changeBase_homotopic γ h

theorem changeBaseMap_mk (γ : Path y₀ y₁) (α : Ω^ N Y y₀) :
    changeBaseMap γ ⟦α⟧ = ⟦changeBase γ α⟧ :=
  rfl

/-- **Changing the basepoint back**: `γ⁻¹ ∘ γ` is homotopic to the identity, relative to `∂I^N`. -/
theorem changeBase_symm_changeBase (γ : Path y₀ y₁) (α : Ω^ N Y y₀) :
    GenLoop.Homotopic (changeBase γ.symm (changeBase γ α)) α := by
  have hrc : Continuous fun s : I => (1 + 3 * (s : ℝ)) / 8 :=
    (continuous_const.add (continuous_const.mul continuous_subtype_val)).div_const _
  refine homotopic_of_frame (r := fun s => (1 + 3 * (s : ℝ)) / 8) hrc
    (fun s => by have := s.2.1; positivity) (fun s => by linarith [s.2.2])
    (inner := fun q => α q.2) (α.1.continuous.comp continuous_snd)
    (outer := fun q => γ.extend (min (8 * (q.2 - (1 + 3 * (q.1 : ℝ)) / 8)) (2 - 4 * q.2)))
    (γ.continuous_extend.comp ((continuous_const.mul (continuous_snd.sub
      (hrc.comp continuous_fst))).min (continuous_const.sub (continuous_const.mul continuous_snd))))
    ?_ ?_ ?_ ?_
  · intro s y hy
    simp only
    rw [GenLoop.boundary α y hy, sub_self, mul_zero,
      min_eq_left (by linarith [s.2.2]), Path.extend_zero]
  · intro s
    simp only
    rw [min_eq_right (by linarith [s.2.2]), show (2 : ℝ) - 4 * (1 / 2) = 0 by norm_num,
      Path.extend_zero]
  · intro y
    rw [frame_apply, changeBase_apply]
    simp only [Set.Icc.coe_zero, mul_zero, add_zero]
    by_cases h1 : cubeDist y ≤ 1 / 8
    · have h1' : cubeDist y ≤ 1 / 4 := by linarith
      have h2 : cubeDist (cubeScale (1 / 4) y) ≤ 1 / 4 := by
        rw [cubeDist_cubeScale (by norm_num) h1', show cubeDist y / (2 * (1 / 4)) =
          2 * cubeDist y by ring]
        linarith
      rw [if_pos (by linarith), if_pos h1', changeBase_apply, if_pos h2,
        cubeScale_cubeScale (by norm_num) (by norm_num) (by norm_num) (by linarith)]
      norm_num
    · rw [if_neg (by linarith)]
      by_cases h3 : cubeDist y ≤ 1 / 4
      · have h2 : ¬ cubeDist (cubeScale (1 / 4) y) ≤ 1 / 4 := by
          rw [cubeDist_cubeScale (by norm_num) h3, show cubeDist y / (2 * (1 / 4)) =
            2 * cubeDist y by ring]
          linarith
        rw [if_pos h3, changeBase_apply, if_neg h2, cubeDist_cubeScale (by norm_num) h3,
          min_eq_left (by linarith)]
        congr 1
        ring
      · rw [if_neg h3, Path.extend_symm_apply, min_eq_right (by linarith)]
        congr 1
        ring
  · intro y
    rw [frame_apply]
    simp only [Set.Icc.coe_one]
    rw [if_pos (by linarith [cubeDist_le_half y]), show (1 + 3 * 1 : ℝ) / 8 = 1 / 2 by norm_num,
      cubeScale_half]

theorem changeBaseMap_symm_comp (γ : Path y₀ y₁) :
    changeBaseMap (N := N) γ.symm ∘ changeBaseMap γ = id := by
  funext c
  induction c using Quotient.inductionOn with
  | h α => exact Quotient.sound (changeBase_symm_changeBase γ α)

/-- **Change of basepoint is a bijection** `π_N(Y, y₀) ≃ π_N(Y, y₁)`, with inverse the change of
basepoint along the reversed path. -/
def changeBaseEquiv (γ : Path y₀ y₁) : HomotopyGroup N Y y₀ ≃ HomotopyGroup N Y y₁ where
  toFun := changeBaseMap γ
  invFun := changeBaseMap γ.symm
  left_inv := congrFun (changeBaseMap_symm_comp γ)
  right_inv := by
    have := changeBaseMap_symm_comp (N := N) γ.symm
    rw [Path.symm_symm] at this
    exact congrFun this

/-! ### Free homotopies -/

/-- **A free homotopy changes the induced map by a change of basepoint**: if `H : f ≃ g`, then
`[g ∘ α]` is the change of basepoint of `[f ∘ α]` along `t ↦ H(t, x₀)`. -/
theorem changeBase_genLoopMap_homotopic {f g : C(X, Y)} (H : f.Homotopy g) {x₀ : X}
    (α : Ω^ N X x₀) :
    GenLoop.Homotopic (changeBase (H.evalAt x₀) (genLoopMap f α)) (genLoopMap g α) := by
  have hrc : Continuous fun s : I => (1 + (s : ℝ)) / 4 :=
    (continuous_const.add continuous_subtype_val).div_const _
  refine homotopic_of_frame (r := fun s => (1 + (s : ℝ)) / 4) hrc
    (fun s => by have := s.2.1; positivity) (fun s => by linarith [s.2.2])
    (inner := fun q => H (q.1, α q.2))
    (H.continuous.comp (continuous_fst.prodMk (α.1.continuous.comp continuous_snd)))
    (outer := fun q => (H.evalAt x₀).extend (4 * q.2 - 1)) (continuous_changeBaseOuter _)
    ?_ ?_ ?_ ?_
  · intro s y hy
    simp only
    rw [GenLoop.boundary α y hy, show 4 * ((1 + (s : ℝ)) / 4) - 1 = s by ring,
      Path.extend_extends']
    rfl
  · intro s
    simp only
    rw [show (4 : ℝ) * (1 / 2) - 1 = 1 by norm_num, Path.extend_one]
  · intro y
    rw [frame_apply, changeBase_apply]
    simp only [Set.Icc.coe_zero, add_zero, H.apply_zero]
    rfl
  · intro y
    rw [frame_apply]
    simp only [Set.Icc.coe_one]
    rw [if_pos (by linarith [cubeDist_le_half y]), show (1 + 1 : ℝ) / 4 = 1 / 2 by norm_num,
      cubeScale_half, H.apply_one]
    rfl

theorem homotopyGroupMap_eq_changeBaseMap {f g : C(X, Y)} (H : f.Homotopy g) (x₀ : X) :
    homotopyGroupMap (N := N) g x₀ = changeBaseMap (H.evalAt x₀) ∘ homotopyGroupMap f x₀ := by
  funext c
  induction c using Quotient.inductionOn with
  | h α => exact (Quotient.sound (changeBase_genLoopMap_homotopic H α)).symm

omit [Fintype N] in
/-- Homotopic maps have bijective induced maps together. -/
theorem bijective_homotopyGroupMap_iff [Finite N] {f g : C(X, Y)} (h : f.Homotopic g) (x₀ : X) :
    Bijective (homotopyGroupMap (N := N) f x₀) ↔ Bijective (homotopyGroupMap (N := N) g x₀) := by
  have := Fintype.ofFinite N
  obtain ⟨H⟩ := h
  rw [homotopyGroupMap_eq_changeBaseMap H x₀]
  exact (EquivLike.comp_bijective _ (changeBaseEquiv (H.evalAt x₀))).symm

omit [Fintype N] in
/-- Homotopic maps have injective induced maps together. -/
theorem injective_homotopyGroupMap_iff [Finite N] {f g : C(X, Y)} (h : f.Homotopic g) (x₀ : X) :
    Injective (homotopyGroupMap (N := N) f x₀) ↔ Injective (homotopyGroupMap (N := N) g x₀) := by
  have := Fintype.ofFinite N
  obtain ⟨H⟩ := h
  rw [homotopyGroupMap_eq_changeBaseMap H x₀]
  exact (EquivLike.comp_injective _ (changeBaseEquiv (H.evalAt x₀))).symm

omit [Fintype N] in
/-- Homotopic maps have surjective induced maps together. -/
theorem surjective_homotopyGroupMap_iff [Finite N] {f g : C(X, Y)} (h : f.Homotopic g) (x₀ : X) :
    Surjective (homotopyGroupMap (N := N) f x₀) ↔ Surjective (homotopyGroupMap (N := N) g x₀) := by
  have := Fintype.ofFinite N
  obtain ⟨H⟩ := h
  rw [homotopyGroupMap_eq_changeBaseMap H x₀]
  exact (EquivLike.comp_surjective _ (changeBaseEquiv (H.evalAt x₀))).symm

/-! ### Homotopy equivalences -/

omit [Fintype N] in
/-- **A homotopy equivalence induces bijections on all homotopy groups**, at every basepoint. -/
theorem bijective_homotopyGroupMap_of_homotopyEquiv [Finite N]
    (e : ContinuousMap.HomotopyEquiv X Y) (x₀ : X) :
    Bijective (homotopyGroupMap (N := N) e.toFun x₀) := by
  have h1 : Bijective (homotopyGroupMap (N := N) (e.invFun.comp e.toFun) x₀) := by
    rw [bijective_homotopyGroupMap_iff e.left_inv, homotopyGroupMap_id]
    exact bijective_id
  have h2 : Bijective (homotopyGroupMap (N := N) (e.toFun.comp e.invFun) (e.toFun x₀)) := by
    rw [bijective_homotopyGroupMap_iff e.right_inv, homotopyGroupMap_id]
    exact bijective_id
  rw [homotopyGroupMap_comp] at h1 h2
  have hinv : Bijective (homotopyGroupMap (N := N) e.invFun (e.toFun x₀)) :=
    ⟨h2.injective.of_comp, h1.surjective.of_comp⟩
  exact (EquivLike.comp_bijective _ (Equiv.ofBijective _ hinv)).1 h1

omit [Fintype N] in
/-- The homotopy equivalence `e` as a bijection `π_N(X, x₀) ≃ π_N(Y, e x₀)`. -/
def homotopyGroupEquivOfHomotopyEquiv [Finite N] (e : ContinuousMap.HomotopyEquiv X Y) (x₀ : X) :
    HomotopyGroup N X x₀ ≃ HomotopyGroup N Y (e.toFun x₀) :=
  Equiv.ofBijective _ (bijective_homotopyGroupMap_of_homotopyEquiv e x₀)

section Square

variable {A B K : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace K]
  {ι : C(A, X)} {j : C(B, K)} (a : ContinuousMap.HomotopyEquiv A B)
  (e : ContinuousMap.HomotopyEquiv X K)

omit [Fintype N] in
/-- **Transfer along a homotopy-commutative square of homotopy equivalences** (bijectivity): if
`e ∘ ι ≃ j ∘ a` with `a`, `e` homotopy equivalences, then `ι_*` is bijective at `x₀` iff `j_*` is
bijective at `a x₀`. -/
theorem bijective_homotopyGroupMap_iff_of_square [Finite N]
    (hsq : (e.toFun.comp ι).Homotopic (j.comp a.toFun)) (x₀ : A) :
    Bijective (homotopyGroupMap (N := N) ι x₀) ↔
      Bijective (homotopyGroupMap (N := N) j (a.toFun x₀)) := by
  rw [← EquivLike.comp_bijective _ (homotopyGroupEquivOfHomotopyEquiv (N := N) e (ι x₀)),
    ← EquivLike.bijective_comp (homotopyGroupEquivOfHomotopyEquiv (N := N) a x₀)]
  change Bijective (homotopyGroupMap e.toFun (ι x₀) ∘ homotopyGroupMap ι x₀) ↔
    Bijective (homotopyGroupMap j (a.toFun x₀) ∘ homotopyGroupMap a.toFun x₀)
  rw [← homotopyGroupMap_comp, ← homotopyGroupMap_comp]
  exact bijective_homotopyGroupMap_iff hsq x₀

omit [Fintype N] in
/-- Transfer of injectivity along a homotopy-commutative square of homotopy equivalences. -/
theorem injective_homotopyGroupMap_iff_of_square [Finite N]
    (hsq : (e.toFun.comp ι).Homotopic (j.comp a.toFun)) (x₀ : A) :
    Injective (homotopyGroupMap (N := N) ι x₀) ↔
      Injective (homotopyGroupMap (N := N) j (a.toFun x₀)) := by
  rw [← EquivLike.comp_injective _ (homotopyGroupEquivOfHomotopyEquiv (N := N) e (ι x₀)),
    ← EquivLike.injective_comp (homotopyGroupEquivOfHomotopyEquiv (N := N) a x₀)]
  change Injective (homotopyGroupMap e.toFun (ι x₀) ∘ homotopyGroupMap ι x₀) ↔
    Injective (homotopyGroupMap j (a.toFun x₀) ∘ homotopyGroupMap a.toFun x₀)
  rw [← homotopyGroupMap_comp, ← homotopyGroupMap_comp]
  exact injective_homotopyGroupMap_iff hsq x₀

omit [Fintype N] in
/-- Transfer of surjectivity along a homotopy-commutative square of homotopy equivalences. -/
theorem surjective_homotopyGroupMap_iff_of_square [Finite N]
    (hsq : (e.toFun.comp ι).Homotopic (j.comp a.toFun)) (x₀ : A) :
    Surjective (homotopyGroupMap (N := N) ι x₀) ↔
      Surjective (homotopyGroupMap (N := N) j (a.toFun x₀)) := by
  rw [← EquivLike.comp_surjective _ (homotopyGroupEquivOfHomotopyEquiv (N := N) e (ι x₀)),
    ← EquivLike.surjective_comp (homotopyGroupEquivOfHomotopyEquiv (N := N) a x₀)]
  change Surjective (homotopyGroupMap e.toFun (ι x₀) ∘ homotopyGroupMap ι x₀) ↔
    Surjective (homotopyGroupMap j (a.toFun x₀) ∘ homotopyGroupMap a.toFun x₀)
  rw [← homotopyGroupMap_comp, ← homotopyGroupMap_comp]
  exact surjective_homotopyGroupMap_iff hsq x₀

end Square

end Morse.Homotopy
