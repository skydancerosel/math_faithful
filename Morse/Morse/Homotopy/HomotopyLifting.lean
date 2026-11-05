import Mathlib
import Morse.Homotopy.Fibration
import Morse.Homotopy.LoopSpace

/-!
# Locally trivial maps are Serre fibrations

This file proves that a locally trivial map `p : E → B` (`Morse.Homotopy.IsLocallyTrivial`) is a
Serre fibration (`Morse.Homotopy.IsLocallyTrivial.isSerreFibration`; Hatcher, *Algebraic
Topology*, Proposition 4.48). In particular Mathlib's fibre bundles are Serre fibrations
(`Morse.Homotopy.isSerreFibration_proj`).

## The statement proved

Put the time coordinate of `Iⁿ × I` on the same footing as the others: `Iⁿ × I ≅ I^{Option n}`,
time being the coordinate `none`. Then the open box `Jⁿ` becomes the union `cubeFaces D` of the
faces `{w_c = 0}` (all `c`) and `{w_c = 1}` (`c ∈ D`) for `D = {c | c ≠ none}`. The theorem
(`Morse.Homotopy.IsLocallyTrivial.exists_lift_cubeFaces`) is: for any finite `N`, any `D ⊆ N`
missing some coordinate `c₀` and any `H : Iᴺ → B`, every lift of `H` given and continuous on
`cubeFaces D` extends to a lift on `Iᴺ`. (Some `c₀ ∉ D` is needed: for `D = N` the faces form the
whole boundary sphere, which is not a retract of the cube.)

## Proof

* **Subdivision** (`Morse.Homotopy.exists_gridBox_subset`). By the Lebesgue number lemma there
  is `m` such that `H` maps each box `B_κ = ∏_c [κ_c/m, (κ_c + 1)/m]` of the grid of mesh `1/m`
  (`κ : N → Fin m`, `Morse.Homotopy.gridBox`) into an open set `U` over which `p` is trivial.
* **Order.** Lift box by box, along any enumeration of the boxes in which `κ' ≤ κ` (pointwise)
  comes first: by strong induction on a finite lower set `S` of indices (removing a maximal
  element), construct a lift on `cubeFaces D ∪ ⋃_{κ ∈ S} B_κ`. When the box `B_κ` is added, `κ`
  maximal in `S`, the lift is already given exactly on the faces of `B_κ` which are *lower*
  faces `{w_c = κ_c/m}` (all `c`: they lie in the boxes `κ - e_c ∈ S`, or in `{w_c = 0}`) and the
  upper faces `{w_c = 1}` for `c ∈ D` with `κ_c = m - 1`
  (`Morse.Homotopy.gridCoord_mem_cubeFaces`, `Morse.Homotopy.gridEmb_mem_of_mem_cubeFaces`):
  in the coordinates of the box, a set of the same shape `cubeFaces D'`, `c₀ ∉ D'`.
* **The retraction** (`Morse.Homotopy.faceRetract`). `cubeFaces D'` is a retract of `Iᴺ` when
  `c₀ ∉ D'`: project radially from the point `P` with `P_c = 1/2` for `c ∈ D'` and `P_c = 2`
  for `c ∉ D'`. In formulas, with `τ_c(u) = 4|u_c - 1/2|` for `c ∈ D'` and `2 - u_c` otherwise,
  and `M(u) = max_c τ_c(u) ∈ [1, 2]`, the point `u` goes to `P + (2/M)(u - P)`; a coordinate
  where the maximum is attained lands on a face of `cubeFaces D'`, and on `cubeFaces D'` itself
  `M = 2`.
* **One box** (`Morse.Homotopy.exists_lift_union_gridBox`). With `φ : p⁻¹(U) ≃ₜ U × F` and `r`
  the retraction of the box onto its prescribed faces, the lift on the box is
  `w ↦ φ⁻¹(H(w), pr_F(φ(G(r(w)))))`; it agrees with the old lift `G` on the prescribed faces,
  where `r` is the identity, and the two paste along closed sets.
-/

open Set Function Topology Metric
open scoped unitInterval Topology.Homotopy

noncomputable section

namespace Morse.Homotopy

variable {E B F : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]

/-! ### Faces of the cube, and the radial retraction onto them -/

section Faces

variable {N : Type*}

/-- The union of the faces `{w_c = 0}` of the cube `Iᴺ` and of the faces `{w_c = 1}` for
`c ∈ D`. -/
def cubeFaces (D : Set N) : Set (N → I) :=
  {w | ∃ c, w c = 0 ∨ (c ∈ D ∧ w c = 1)}

theorem isClosed_cubeFaces [Finite N] (D : Set N) : IsClosed (cubeFaces D) := by
  have h : cubeFaces D = ⋃ c, ({w : N → I | w c = 0} ∪ {w | c ∈ D ∧ w c = 1}) := by
    ext w
    simp [cubeFaces]
  rw [h]
  refine isClosed_iUnion_of_finite fun c =>
    (isClosed_eq (continuous_apply c) continuous_const).union ?_
  by_cases hc : c ∈ D
  · simpa [hc] using isClosed_eq (continuous_apply c) continuous_const
  · simp [hc]

open Classical in
/-- The weights `τ_c(u)` of the radial retraction onto `cubeFaces D`: `4|u_c - 1/2|` for
`c ∈ D`, and `2 - u_c` otherwise. -/
def faceWeight (D : Set N) (u : N → I) (c : N) : ℝ :=
  if c ∈ D then 4 * |(u c : ℝ) - 1 / 2| else 2 - u c

theorem faceWeight_of_mem {D : Set N} {c : N} (hc : c ∈ D) (u : N → I) :
    faceWeight D u c = 4 * |(u c : ℝ) - 1 / 2| := by
  rw [faceWeight, if_pos hc]

theorem faceWeight_of_notMem {D : Set N} {c : N} (hc : c ∉ D) (u : N → I) :
    faceWeight D u c = 2 - u c := by
  rw [faceWeight, if_neg hc]

theorem faceWeight_nonneg (D : Set N) (u : N → I) (c : N) : 0 ≤ faceWeight D u c := by
  by_cases hc : c ∈ D
  · rw [faceWeight_of_mem hc]
    positivity
  · rw [faceWeight_of_notMem hc]
    linarith [(u c).2.2]

theorem faceWeight_le_two (D : Set N) (u : N → I) (c : N) : faceWeight D u c ≤ 2 := by
  by_cases hc : c ∈ D
  · rw [faceWeight_of_mem hc]
    have : |(u c : ℝ) - 1 / 2| ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith [(u c).2.1, (u c).2.2]
    linarith
  · rw [faceWeight_of_notMem hc]
    linarith [(u c).2.1]

theorem continuous_faceWeight (D : Set N) (c : N) :
    Continuous fun u : N → I => faceWeight D u c := by
  by_cases hc : c ∈ D
  · simp only [faceWeight_of_mem hc]
    exact continuous_const.mul (((continuous_subtype_val.comp (continuous_apply c)).sub
      continuous_const).abs)
  · simp only [faceWeight_of_notMem hc]
    exact continuous_const.sub (continuous_subtype_val.comp (continuous_apply c))

variable [Fintype N]

/-- `M(u) = max_c τ_c(u)`, as the sup norm of the vector of weights. -/
def faceMax (D : Set N) (u : N → I) : ℝ :=
  ‖faceWeight D u‖

theorem faceWeight_le_faceMax (D : Set N) (u : N → I) (c : N) :
    faceWeight D u c ≤ faceMax D u := by
  have h := norm_le_pi_norm (faceWeight D u) c
  rwa [Real.norm_eq_abs, abs_of_nonneg (faceWeight_nonneg D u c)] at h

theorem faceMax_le_two (D : Set N) (u : N → I) : faceMax D u ≤ 2 :=
  (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun c => by
    rw [Real.norm_eq_abs, abs_of_nonneg (faceWeight_nonneg D u c)]
    exact faceWeight_le_two D u c

theorem one_le_faceMax {D : Set N} {c₀ : N} (hc₀ : c₀ ∉ D) (u : N → I) : 1 ≤ faceMax D u := by
  have h := faceWeight_le_faceMax D u c₀
  rw [faceWeight_of_notMem hc₀] at h
  linarith [(u c₀).2.2]

theorem exists_faceWeight_eq_faceMax [Nonempty N] (D : Set N) (u : N → I) :
    ∃ c, faceWeight D u c = faceMax D u := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun b => ‖faceWeight D u b‖₊)
  refine ⟨j, ?_⟩
  rw [faceMax, Pi.norm_def, hj, coe_nnnorm, Real.norm_eq_abs,
    abs_of_nonneg (faceWeight_nonneg D u j)]

theorem continuous_faceMax (D : Set N) : Continuous (faceMax D) :=
  continuous_norm.comp (continuous_pi fun c => continuous_faceWeight D c)

theorem faceMax_of_mem {D : Set N} {u : N → I} (hu : u ∈ cubeFaces D) : faceMax D u = 2 := by
  refine le_antisymm (faceMax_le_two D u) ?_
  obtain ⟨c, hc⟩ := hu
  refine le_trans ?_ (faceWeight_le_faceMax D u c)
  rcases hc with h0 | ⟨hcD, h1⟩
  · by_cases hcD : c ∈ D
    · rw [faceWeight_of_mem hcD, h0]
      norm_num
    · rw [faceWeight_of_notMem hcD, h0]
      norm_num
  · rw [faceWeight_of_mem hcD, h1]
    norm_num

open Classical in
/-- **The radial retraction onto `cubeFaces D`** (for `D ≠ univ`): the projection from the point
`P` with `P_c = 1/2` for `c ∈ D` and `P_c = 2` otherwise, `u ↦ P + (2 / M(u)) (u - P)`. -/
def faceRetract (D : Set N) (u : N → I) : N → I := fun c =>
  Set.projIcc 0 1 zero_le_one
    (if c ∈ D then 1 / 2 + 2 / faceMax D u * ((u c : ℝ) - 1 / 2)
      else 2 - 2 / faceMax D u * (2 - u c))

theorem continuous_faceRetract {D : Set N} {c₀ : N} (hc₀ : c₀ ∉ D) :
    Continuous (faceRetract D) := by
  have hinv : Continuous fun u : N → I => 2 / faceMax D u :=
    continuous_const.div (continuous_faceMax D) fun u =>
      (zero_lt_one.trans_le (one_le_faceMax hc₀ u)).ne'
  refine continuous_pi fun c => continuous_projIcc.comp ?_
  by_cases hc : c ∈ D
  · simp only [hc, if_true]
    exact continuous_const.add (hinv.mul
      ((continuous_subtype_val.comp (continuous_apply c)).sub continuous_const))
  · simp only [hc, if_false]
    exact continuous_const.sub (hinv.mul
      (continuous_const.sub (continuous_subtype_val.comp (continuous_apply c))))

theorem faceRetract_mem {D : Set N} {c₀ : N} (hc₀ : c₀ ∉ D) (u : N → I) :
    faceRetract D u ∈ cubeFaces D := by
  have : Nonempty N := ⟨c₀⟩
  obtain ⟨c, hc⟩ := exists_faceWeight_eq_faceMax D u
  have hM := one_le_faceMax hc₀ u
  have hM0 : faceMax D u ≠ 0 := by linarith
  refine ⟨c, ?_⟩
  by_cases hcD : c ∈ D
  · rw [faceWeight_of_mem hcD] at hc
    have hx : (u c : ℝ) - 1 / 2 ≠ 0 := by
      intro h'
      apply hM0
      rw [← hc, h', abs_zero, mul_zero]
    have key : 2 / faceMax D u * ((u c : ℝ) - 1 / 2) = 1 / 2 ∨
        2 / faceMax D u * ((u c : ℝ) - 1 / 2) = -(1 / 2) := by
      rcases abs_choice ((u c : ℝ) - 1 / 2) with h | h
      · left
        rw [← hc, h, div_mul_eq_mul_div, div_eq_iff (mul_ne_zero four_ne_zero hx)]
        ring
      · right
        rw [← hc, h, div_mul_eq_mul_div,
          div_eq_iff (mul_ne_zero four_ne_zero (neg_ne_zero.2 hx))]
        ring
    rcases key with h | h
    · right
      refine ⟨hcD, Subtype.ext ?_⟩
      simp only [faceRetract, hcD, if_true, h]
      rw [Set.projIcc_of_right_le _ (by norm_num)]
      rfl
    · left
      apply Subtype.ext
      simp only [faceRetract, hcD, if_true, h]
      rw [Set.projIcc_of_le_left _ (by norm_num)]
      rfl
  · rw [faceWeight_of_notMem hcD] at hc
    left
    apply Subtype.ext
    simp only [faceRetract, hcD, if_false]
    rw [Set.projIcc_of_le_left]
    · rfl
    · rw [← hc, div_mul_cancel₀ _ (by rw [hc]; exact hM0)]
      norm_num

theorem faceRetract_of_mem {D : Set N} {u : N → I} (hu : u ∈ cubeFaces D) :
    faceRetract D u = u := by
  funext c
  have hM := faceMax_of_mem hu
  by_cases hc : c ∈ D
  · simp only [faceRetract, hc, if_true, hM]
    rw [show 1 / 2 + 2 / 2 * ((u c : ℝ) - 1 / 2) = u c by ring, Set.projIcc_val]
  · simp only [faceRetract, hc, if_false, hM]
    rw [show 2 - 2 / 2 * (2 - (u c : ℝ)) = u c by ring, Set.projIcc_val]

end Faces

/-! ### The grid of mesh `1/m` -/

section Grid

variable {N : Type*} (m : ℕ)

/-- The box `∏_c [κ_c/m, (κ_c + 1)/m]` of the grid of mesh `1/m` in `Iᴺ`. -/
def gridBox (κ : N → Fin m) : Set (N → I) :=
  {w | ∀ c, ((κ c : ℕ) : ℝ) / m ≤ w c ∧ (w c : ℝ) ≤ ((κ c : ℕ) + 1) / m}

theorem isClosed_gridBox (κ : N → Fin m) : IsClosed (gridBox m κ) := by
  have h : gridBox m κ = ⋂ c, ({w : N → I | ((κ c : ℕ) : ℝ) / m ≤ w c} ∩
      {w | (w c : ℝ) ≤ ((κ c : ℕ) + 1) / m}) := by
    ext w
    simp [gridBox]
  rw [h]
  exact isClosed_iInter fun c =>
    (isClosed_le continuous_const (continuous_subtype_val.comp (continuous_apply c))).inter
      (isClosed_le (continuous_subtype_val.comp (continuous_apply c)) continuous_const)

theorem natCast_add_one_le (k : Fin m) : ((k : ℕ) : ℝ) + 1 ≤ m := by
  exact_mod_cast k.isLt

/-- The affine parametrization `u ↦ (κ + u)/m` of the box `B_κ` by the unit cube. -/
def gridEmb (κ : N → Fin m) (u : N → I) : N → I := fun c =>
  ⟨(((κ c : ℕ) : ℝ) + u c) / m, by
    have hm : (0 : ℝ) < m := by exact_mod_cast (κ c).pos
    have h1 := natCast_add_one_le m (κ c)
    constructor
    · have := (u c).2.1
      positivity
    · rw [div_le_one hm]
      linarith [(u c).2.2]⟩

theorem coe_gridEmb (κ : N → Fin m) (u : N → I) (c : N) :
    (gridEmb m κ u c : ℝ) = (((κ c : ℕ) : ℝ) + u c) / m :=
  rfl

/-- The inverse `w ↦ m w - κ` of `Morse.Homotopy.gridEmb` (clamped to `[0, 1]`). -/
def gridCoord (κ : N → Fin m) (w : N → I) : N → I := fun c =>
  Set.projIcc 0 1 zero_le_one (m * w c - ((κ c : ℕ) : ℝ))

theorem continuous_gridEmb (κ : N → Fin m) : Continuous (gridEmb m κ) :=
  continuous_pi fun c => ((continuous_const.add (continuous_subtype_val.comp
    (continuous_apply c))).div_const _).subtype_mk _

theorem continuous_gridCoord (κ : N → Fin m) : Continuous (gridCoord m κ) :=
  continuous_pi fun c => continuous_projIcc.comp ((continuous_const.mul
    (continuous_subtype_val.comp (continuous_apply c))).sub continuous_const)

theorem gridEmb_mem (κ : N → Fin m) (u : N → I) : gridEmb m κ u ∈ gridBox m κ := by
  intro c
  have hm : (0 : ℝ) < m := by exact_mod_cast (κ c).pos
  rw [coe_gridEmb]
  constructor
  · gcongr
    linarith [(u c).2.1]
  · gcongr
    exact (u c).2.2

theorem coe_gridCoord_of_mem {κ : N → Fin m} {w : N → I} (hw : w ∈ gridBox m κ) (c : N) :
    (gridCoord m κ w c : ℝ) = m * w c - ((κ c : ℕ) : ℝ) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast (κ c).pos
  obtain ⟨h1, h2⟩ := hw c
  rw [div_le_iff₀ hm] at h1
  rw [le_div_iff₀ hm] at h2
  rw [gridCoord, Set.projIcc_of_mem]
  constructor <;> linarith

theorem gridEmb_gridCoord {κ : N → Fin m} {w : N → I} (hw : w ∈ gridBox m κ) :
    gridEmb m κ (gridCoord m κ w) = w := by
  funext c
  apply Subtype.ext
  have hm : (0 : ℝ) < m := by exact_mod_cast (κ c).pos
  rw [coe_gridEmb, coe_gridCoord_of_mem m hw]
  field_simp
  ring

theorem gridCoord_gridEmb (κ : N → Fin m) (u : N → I) : gridCoord m κ (gridEmb m κ u) = u := by
  funext c
  have hm : (0 : ℝ) < m := by exact_mod_cast (κ c).pos
  rw [gridCoord, coe_gridEmb, show (m : ℝ) * ((((κ c : ℕ) : ℝ) + u c) / m) - ((κ c : ℕ) : ℝ) =
    u c by field_simp; ring, Set.projIcc_val]

/-- Every point of the cube lies in a box of the grid. -/
theorem exists_mem_gridBox (hm : 0 < m) (w : N → I) : ∃ κ : N → Fin m, w ∈ gridBox m κ := by
  refine ⟨fun c => ⟨min (m - 1) ⌊(w c : ℝ) * m⌋₊, by omega⟩, fun c => ?_⟩
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hw0 : 0 ≤ (w c : ℝ) * m := mul_nonneg (w c).2.1 hm'.le
  simp only
  constructor
  · rw [div_le_iff₀ hm']
    calc ((min (m - 1) ⌊(w c : ℝ) * m⌋₊ : ℕ) : ℝ) ≤ (⌊(w c : ℝ) * m⌋₊ : ℝ) := by
          exact_mod_cast min_le_right _ _
      _ ≤ (w c : ℝ) * m := Nat.floor_le hw0
  · rw [le_div_iff₀ hm']
    rcases le_total (m - 1) ⌊(w c : ℝ) * m⌋₊ with h | h
    · rw [min_eq_left h]
      have : ((m - 1 : ℕ) : ℝ) + 1 = m := by
        rw [Nat.cast_sub (by omega)]
        push_cast
        ring
      rw [this]
      nlinarith [(w c).2.2]
    · rw [min_eq_right h]
      exact (Nat.lt_floor_add_one _).le

/-- **Subdivision** (Lebesgue number lemma): for an open cover of `Iᴺ`, every box of a fine
enough grid lies in one of the open sets. -/
theorem exists_gridBox_subset [Finite N] {ι : Type*} {U : ι → Set (N → I)} (hU : ∀ i, IsOpen (U i))
    (hcov : ∀ w, ∃ i, w ∈ U i) : ∃ m : ℕ, 0 < m ∧ ∀ κ : N → Fin m, ∃ i, gridBox m κ ⊆ U i := by
  have := Fintype.ofFinite N
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hU
    fun w _ => mem_iUnion.2 (hcov w)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  refine ⟨n + 1, n.succ_pos, fun κ => ?_⟩
  obtain ⟨i, hi⟩ := hball (gridEmb (n + 1) κ fun _ => 0) (mem_univ _)
  refine ⟨i, fun w hw => hi ?_⟩
  rw [mem_ball]
  refine lt_of_le_of_lt ((dist_pi_le_iff (by positivity)).2 fun c => ?_) hn
  rw [Subtype.dist_eq, coe_gridEmb, Real.dist_eq, abs_le]
  obtain ⟨h1, h2⟩ := hw c
  push_cast at h1 h2 ⊢
  simp only [add_zero]
  constructor
  · have : ((κ c : ℕ) : ℝ) / (n + 1) ≤ w c := h1
    have : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · rw [show ((κ c : ℕ) + 1 : ℝ) / (n + 1) = ((κ c : ℕ) : ℝ) / (n + 1) + 1 / (n + 1) by ring] at h2
    linarith

end Grid

/-! ### Lifting over one box -/

section OneBox

variable {p : E → B} {U : Set B} (φ : p ⁻¹' U ≃ₜ U × F)

/-- Moving a point `x` of `p⁻¹(U)` to the fibre over `b ∈ U`, keeping its `F`-coordinate. -/
def fiberMove (b : U) (x : p ⁻¹' U) : p ⁻¹' U :=
  φ.symm (b, (φ x).2)

variable {φ}

theorem fiberMove_proj (hφ : ∀ x, ((φ x).1 : B) = p x) (b : U) (x : p ⁻¹' U) :
    p (fiberMove φ b x) = b := by
  rw [← hφ, fiberMove, Homeomorph.apply_symm_apply]

theorem fiberMove_self (hφ : ∀ x, ((φ x).1 : B) = p x) {b : U} {x : p ⁻¹' U} (h : (b : B) = p x) :
    fiberMove φ b x = x := by
  rw [fiberMove]
  have : (b, (φ x).2) = φ x := Prod.ext (Subtype.ext (h.trans (hφ x).symm)) rfl
  rw [this, Homeomorph.symm_apply_apply]

theorem continuous_fiberMove : Continuous fun q : U × p ⁻¹' U => fiberMove φ q.1 q.2 :=
  φ.symm.continuous.comp (continuous_fst.prodMk (continuous_snd.comp
    (φ.continuous.comp continuous_snd)))

variable {N : Type*} [Finite N]

/-- **Lifting over one box**: if the lift `G'` is known on a closed set `A`, which meets the box
`B_κ` exactly in the image of `cubeFaces D'` (in the coordinates of the box), and `H` maps `B_κ`
into a set `U` over which `p` is trivial, then `G'` extends to a lift on `A ∪ B_κ`. -/
theorem exists_lift_union_gridBox (hφ : ∀ x, ((φ x).1 : B) = p x) (H : C(N → I, B)) {m : ℕ}
    {κ : N → Fin m} (hHU : ∀ w ∈ gridBox m κ, H w ∈ U) {D' : Set N} {c₀ : N} (hc₀ : c₀ ∉ D')
    {A : Set (N → I)} (hA : IsClosed A)
    (h1 : ∀ w ∈ gridBox m κ, w ∈ A → gridCoord m κ w ∈ cubeFaces D')
    (h2 : ∀ u ∈ cubeFaces D', gridEmb m κ u ∈ A) {G' : (N → I) → E} (hG' : ContinuousOn G' A)
    (hpG' : ∀ w ∈ A, p (G' w) = H w) :
    ∃ G : (N → I) → E, ContinuousOn G (A ∪ gridBox m κ) ∧
      (∀ w ∈ A ∪ gridBox m κ, p (G w) = H w) ∧ ∀ w ∈ A, G w = G' w := by
  classical
  have := Fintype.ofFinite N
  -- the retraction of the box onto its prescribed faces
  let r : (N → I) → (N → I) := fun w => gridEmb m κ (faceRetract D' (gridCoord m κ w))
  have hr : Continuous r := (continuous_gridEmb m κ).comp
    ((continuous_faceRetract hc₀).comp (continuous_gridCoord m κ))
  have hrA : ∀ w, r w ∈ A := fun w => h2 _ (faceRetract_mem hc₀ _)
  have hrB : ∀ w, r w ∈ gridBox m κ := fun w => gridEmb_mem m κ _
  have hrid : ∀ w ∈ gridBox m κ, w ∈ A → r w = w := fun w hw hwA => by
    change gridEmb m κ (faceRetract D' (gridCoord m κ w)) = w
    rw [faceRetract_of_mem (h1 w hw hwA), gridEmb_gridCoord m hw]
  have hGr : Continuous fun w => G' (r w) := hG'.comp_continuous hr hrA
  have hGrU : ∀ w, G' (r w) ∈ p ⁻¹' U := fun w => by
    change p (G' (r w)) ∈ U
    rw [hpG' _ (hrA w)]
    exact hHU _ (hrB w)
  -- the new lift on the box
  let L : gridBox m κ → E := fun w =>
    fiberMove φ ⟨H w, hHU w w.2⟩ ⟨G' (r w), hGrU w⟩
  have hL : Continuous L := continuous_subtype_val.comp (continuous_fiberMove.comp
    (((H.continuous.comp continuous_subtype_val).subtype_mk _).prodMk
      ((hGr.comp continuous_subtype_val).subtype_mk _)))
  have hLp : ∀ w, p (L w) = H w := fun w => fiberMove_proj hφ _ _
  have hLA : ∀ w : gridBox m κ, (w : N → I) ∈ A → L w = G' w := fun w hwA => by
    have hrw := hrid w w.2 hwA
    change ((fiberMove φ ⟨H w, hHU w w.2⟩ ⟨G' (r w), hGrU w⟩ : p ⁻¹' U) : E) = G' w
    rw [fiberMove_self hφ (by
      change H w = p (G' (r w))
      rw [hpG' _ (hrA w), hrw])]
    exact congrArg G' hrw
  let G : (N → I) → E := fun w => if h : w ∈ gridBox m κ then L ⟨w, h⟩ else G' w
  have hGA : ∀ w ∈ A, G w = G' w := fun w hwA => by
    by_cases h : w ∈ gridBox m κ
    · simp only [G, dif_pos h]
      exact hLA ⟨w, h⟩ hwA
    · simp only [G, dif_neg h]
  refine ⟨G, ContinuousOn.union_of_isClosed (hG'.congr hGA) ?_ hA (isClosed_gridBox m κ), ?_,
    hGA⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    convert hL using 1
    funext w
    simp only [domRestrict_apply, G, dif_pos w.2]
  · rintro w (hw | hw)
    · rw [hGA w hw, hpG' w hw]
    · simp only [G, dif_pos hw]
      exact hLp ⟨w, hw⟩

end OneBox

/-! ### The order of the boxes -/

section Order

variable {N : Type*} {m : ℕ}

/-- The coordinates in which the box `B_κ` has a prescribed upper face: `c ∈ D` with
`κ_c = m - 1`. -/
def upperFaces (D : Set N) (κ : N → Fin m) : Set N :=
  {c | c ∈ D ∧ (κ c : ℕ) + 1 = m}

/-- The part of the cube where the lift is known after the boxes in `S`. -/
def liftedPart (D : Set N) (S : Finset (N → Fin m)) : Set (N → I) :=
  cubeFaces D ∪ ⋃ κ ∈ S, gridBox m κ

theorem isClosed_liftedPart [Finite N] (D : Set N) (S : Finset (N → Fin m)) :
    IsClosed (liftedPart D S) :=
  (isClosed_cubeFaces D).union (isClosed_biUnion_finset fun κ _ => isClosed_gridBox m κ)

theorem liftedPart_insert [DecidableEq (N → Fin m)] (D : Set N) (S : Finset (N → Fin m))
    {κ : N → Fin m} (hκ : κ ∈ S) :
    liftedPart D S = liftedPart D (S.erase κ) ∪ gridBox m κ := by
  ext w
  simp only [liftedPart, mem_union, mem_iUnion, Finset.mem_erase, exists_prop]
  constructor
  · rintro (h | ⟨κ', hκ', hw⟩)
    · exact Or.inl (Or.inl h)
    · by_cases h : κ' = κ
      · subst h
        exact Or.inr hw
      · exact Or.inl (Or.inr ⟨κ', ⟨h, hκ'⟩, hw⟩)
  · rintro ((h | ⟨κ', ⟨-, hκ'⟩, hw⟩) | hw)
    · exact Or.inl h
    · exact Or.inr ⟨κ', hκ', hw⟩
    · exact Or.inr ⟨κ, hκ, hw⟩

/-- When the box `B_κ` is added, `κ` maximal in `S`, the known part meets `B_κ` only in lower
faces and in prescribed upper faces. -/
theorem gridCoord_mem_cubeFaces [DecidableEq (N → Fin m)] {D : Set N} {S : Finset (N → Fin m)}
    {κ : N → Fin m} (hκ : Maximal (· ∈ S) κ) {w : N → I} (hw : w ∈ gridBox m κ)
    (hwA : w ∈ liftedPart D (S.erase κ)) : gridCoord m κ w ∈ cubeFaces (upperFaces D κ) := by
  rcases hwA with ⟨c, hc⟩ | hwA
  · have hm : (0 : ℝ) < m := by exact_mod_cast (κ c).pos
    refine ⟨c, ?_⟩
    obtain ⟨h1, h2⟩ := hw c
    rcases hc with h0 | ⟨hcD, h1'⟩
    · -- `w_c = 0` forces `κ_c = 0`
      rw [h0, Set.Icc.coe_zero] at h1
      have hk : ((κ c : ℕ) : ℝ) = 0 := le_antisymm (by
        rwa [div_le_iff₀ hm, zero_mul] at h1) (Nat.cast_nonneg _)
      left
      apply Subtype.ext
      rw [coe_gridCoord_of_mem m hw, h0, hk]
      simp
    · -- `w_c = 1` forces `κ_c = m - 1`
      rw [h1', Set.Icc.coe_one, le_div_iff₀ hm, one_mul] at h2
      have hk : ((κ c : ℕ) : ℝ) + 1 = m := le_antisymm (natCast_add_one_le m (κ c)) h2
      right
      refine ⟨⟨hcD, by exact_mod_cast hk⟩, Subtype.ext ?_⟩
      rw [coe_gridCoord_of_mem m hw, h1', Set.Icc.coe_one, mul_one, ← hk]
      simp
  · simp only [mem_iUnion, Finset.mem_erase, exists_prop] at hwA
    obtain ⟨κ', ⟨hne, hκ'⟩, hw'⟩ := hwA
    -- `κ'` is not above `κ`, so `κ'_c < κ_c` for some `c`, and `w` lies on the lower face `c`
    have hnle : ¬ κ ≤ κ' := fun hle => hne (le_antisymm (hκ.2 hκ' hle) hle)
    simp only [Pi.le_def, not_forall, not_le] at hnle
    obtain ⟨c, hc⟩ := hnle
    have hm : (0 : ℝ) < m := by exact_mod_cast (κ c).pos
    refine ⟨c, Or.inl (Subtype.ext ?_)⟩
    have hlt : ((κ' c : ℕ) : ℝ) + 1 ≤ (κ c : ℕ) := by exact_mod_cast hc
    obtain ⟨h1, -⟩ := hw c
    obtain ⟨-, h2'⟩ := hw' c
    rw [div_le_iff₀ hm] at h1
    rw [le_div_iff₀ hm] at h2'
    rw [coe_gridCoord_of_mem m hw, Set.Icc.coe_zero]
    linarith

/-- The prescribed faces of the box `B_κ` lie in the known part (`S` a lower set). -/
theorem gridEmb_mem_of_mem_cubeFaces [DecidableEq (N → Fin m)] {D : Set N}
    {S : Finset (N → Fin m)} (hS : IsLowerSet (S : Set (N → Fin m))) {κ : N → Fin m}
    (hκ : κ ∈ S) {u : N → I} (hu : u ∈ cubeFaces (upperFaces D κ)) :
    gridEmb m κ u ∈ liftedPart D (S.erase κ) := by
  classical
  obtain ⟨c, hc⟩ := hu
  have hm : (0 : ℝ) < m := by exact_mod_cast (κ c).pos
  rcases hc with h0 | ⟨⟨hcD, hk⟩, h1⟩
  · by_cases hk : (κ c : ℕ) = 0
    · -- the lower face `c` of the box lies in the face `{w_c = 0}` of the cube
      refine Or.inl ⟨c, Or.inl (Subtype.ext ?_)⟩
      rw [coe_gridEmb, hk, h0]
      simp
    · -- the lower face `c` of the box lies in the box `κ - e_c`
      let κ' : N → Fin m := Function.update κ c ⟨(κ c : ℕ) - 1, by omega⟩
      have hle : κ' ≤ κ := fun d => by
        by_cases hd : d = c
        · subst hd
          simp only [κ', Function.update_self]
          exact Fin.le_iff_val_le_val.2 (Nat.sub_le _ _) |>.trans (le_refl _)
        · simp [κ', Function.update_of_ne hd]
      have hne : κ' ≠ κ := fun h => by
        have := congrFun h c
        simp only [κ', Function.update_self, Fin.ext_iff] at this
        omega
      refine Or.inr (mem_iUnion₂.2 ⟨κ', Finset.mem_erase.2 ⟨hne, hS hle hκ⟩, fun d => ?_⟩)
      by_cases hd : d = c
      · subst hd
        simp only [κ', Function.update_self]
        rw [coe_gridEmb, h0, Set.Icc.coe_zero, add_zero, Nat.cast_sub (by omega)]
        push_cast
        constructor
        · gcongr
          linarith
        · gcongr
          linarith
      · simp only [κ', Function.update_of_ne hd]
        exact gridEmb_mem m κ u d
  · -- a prescribed upper face lies in the face `{w_c = 1}` of the cube
    refine Or.inl ⟨c, Or.inr ⟨hcD, Subtype.ext ?_⟩⟩
    rw [coe_gridEmb, h1, Set.Icc.coe_one]
    have hk' : ((κ c : ℕ) : ℝ) + 1 = m := by exact_mod_cast hk
    rw [hk', div_self hm.ne']

end Order

/-! ### The lifting theorem -/

/-- **Locally trivial maps lift homotopies of cubes relative to faces**: let `p` be locally
trivial, `N` finite, and `D ⊆ N` with `c₀ ∉ D`. Every map `H : Iᴺ → B` with a lift `g` given and
continuous on the faces `cubeFaces D` (`{w_c = 0}` for all `c`, `{w_c = 1}` for `c ∈ D`) has a
lift `G : Iᴺ → E` extending `g`. -/
theorem IsLocallyTrivial.exists_lift_cubeFaces {p : E → B} (hp : IsLocallyTrivial p F)
    {N : Type*} [Finite N] {D : Set N} {c₀ : N} (hc₀ : c₀ ∉ D) (H : C(N → I, B))
    {g : (N → I) → E} (hg : ContinuousOn g (cubeFaces D)) (hpg : ∀ w ∈ cubeFaces D, p (g w) = H w) :
    ∃ G : C(N → I, E), (∀ w, p (G w) = H w) ∧ ∀ w ∈ cubeFaces D, G w = g w := by
  classical
  have := Fintype.ofFinite N
  choose U hUo hbU φ hφ using hp
  -- a grid whose boxes are mapped into trivializing open sets
  obtain ⟨m, hm, hbox⟩ := exists_gridBox_subset (U := fun b => H ⁻¹' U b)
    (fun b => (hUo b).preimage H.continuous) fun w => ⟨H w, hbU (H w)⟩
  choose b hb using hbox
  -- lift box by box, along lower sets of indices
  have key : ∀ S : Finset (N → Fin m), IsLowerSet (S : Set (N → Fin m)) →
      ∃ G : (N → I) → E, ContinuousOn G (liftedPart D S) ∧
        (∀ w ∈ liftedPart D S, p (G w) = H w) ∧ ∀ w ∈ cubeFaces D, G w = g w := by
    intro S
    induction S using Finset.eraseInduction with
    | H S ih =>
    intro hS
    rcases S.eq_empty_or_nonempty with rfl | hne
    · refine ⟨g, ?_, ?_, fun w _ => rfl⟩
      · simpa [liftedPart] using hg
      · intro w hw
        simp only [liftedPart, Finset.notMem_empty, iUnion_of_empty, iUnion_empty,
          union_empty] at hw
        exact hpg w hw
    · obtain ⟨κ, hκ⟩ := Finset.exists_maximal hne
      have hS' : IsLowerSet ((S.erase κ : Finset _) : Set (N → Fin m)) := by
        intro a a' hle ha
        simp only [Finset.coe_erase, mem_sdiff, Finset.mem_coe, mem_singleton_iff] at ha ⊢
        refine ⟨hS hle ha.1, fun h => ha.2 ?_⟩
        subst h
        exact le_antisymm (hκ.2 ha.1 hle) hle
      obtain ⟨G', hG', hpG', hG'g⟩ := ih κ hκ.1 hS'
      obtain ⟨G, hG, hpG, hGG'⟩ := exists_lift_union_gridBox (hφ (b κ)) H
        (fun w hw => hb κ hw) (D' := upperFaces D κ) (c₀ := c₀) (fun h => hc₀ h.1)
        (isClosed_liftedPart D (S.erase κ)) (fun w hw hwA => gridCoord_mem_cubeFaces hκ hw hwA)
        (fun u hu => gridEmb_mem_of_mem_cubeFaces hS hκ.1 hu) hG' hpG'
      rw [liftedPart_insert D S hκ.1]
      exact ⟨G, hG, hpG, fun w hw => (hGG' w (Or.inl hw)).trans (hG'g w hw)⟩
  obtain ⟨G, hG, hpG, hGg⟩ := key Finset.univ (by rw [Finset.coe_univ]; exact isLowerSet_univ)
  have huniv : liftedPart D (Finset.univ : Finset (N → Fin m)) = univ := by
    refine eq_univ_of_forall fun w => Or.inr ?_
    obtain ⟨κ, hκ⟩ := exists_mem_gridBox m hm w
    exact mem_iUnion₂.2 ⟨κ, Finset.mem_univ κ, hκ⟩
  rw [huniv] at hG hpG
  exact ⟨⟨G, continuousOn_univ.1 hG⟩, fun w => hpG w (mem_univ w), hGg⟩

/-! ### Serre fibrations -/

/-- `Iᴺ × I ≃ₜ I^{Option N}`, the time becoming the coordinate `none`. -/
def optionCubeHomeo (N : Type*) : (N → I) × I ≃ₜ (Option N → I) where
  toFun z := optionPoint z.2 z.1
  invFun w := (fun j => w (some j), w none)
  left_inv _ := rfl
  right_inv w := optionPoint_eta w
  continuous_toFun := continuous_optionPoint.comp (continuous_snd.prodMk continuous_fst)
  continuous_invFun :=
    (continuous_pi fun j => continuous_apply (some j)).prodMk (continuous_apply none)

theorem optionCubeHomeo_mem_cubeFaces_iff {N : Type*} (z : (N → I) × I) :
    optionCubeHomeo N z ∈ cubeFaces {c | c ≠ none} ↔ z ∈ openBox N := by
  obtain ⟨x, t⟩ := z
  constructor
  · rintro ⟨c, hc⟩
    cases c with
    | none =>
      rcases hc with h | ⟨h, -⟩
      · exact Or.inl h
      · exact absurd rfl h
    | some j =>
      rcases hc with h | ⟨-, h⟩
      · exact Or.inr ⟨j, Or.inl h⟩
      · exact Or.inr ⟨j, Or.inr h⟩
  · rintro (h | ⟨j, hj⟩)
    · exact ⟨none, Or.inl h⟩
    · rcases hj with h | h
      · exact ⟨some j, Or.inl h⟩
      · exact ⟨some j, Or.inr ⟨Option.some_ne_none j, h⟩⟩

/-- **A locally trivial map is a Serre fibration** (Hatcher, Proposition 4.48). -/
theorem IsLocallyTrivial.isSerreFibration {p : E → B} (hp : IsLocallyTrivial p F) :
    IsSerreFibration p := by
  intro n H g hg hpg
  let Θ := optionCubeHomeo (Fin n)
  have hΘ : ∀ w, w ∈ cubeFaces {c | c ≠ none} ↔ Θ.symm w ∈ openBox (Fin n) := fun w => by
    rw [← optionCubeHomeo_mem_cubeFaces_iff, Homeomorph.apply_symm_apply]
  obtain ⟨G, hG, hGg⟩ := hp.exists_lift_cubeFaces (D := {c | c ≠ none}) (c₀ := none)
    (by simp) (H.comp (Θ.symm : C(Option (Fin n) → I, (Fin n → I) × I))) (g := g ∘ Θ.symm)
    (hg.comp Θ.symm.continuous.continuousOn fun w hw => (hΘ w).1 hw)
    (fun w hw => hpg _ ((hΘ w).1 hw))
  refine ⟨G.comp (Θ : C((Fin n → I) × I, Option (Fin n) → I)), fun z => ?_, fun z hz => ?_⟩
  · simpa using hG (Θ z)
  · have := hGg (Θ z) ((hΘ (Θ z)).2 (by simpa using hz))
    simpa using this

/-- **Fibre bundles are Serre fibrations**: the projection of a Mathlib `FiberBundle`. -/
theorem isSerreFibration_proj {Z : B → Type*} [TopologicalSpace (Bundle.TotalSpace F Z)]
    [∀ b, TopologicalSpace (Z b)] [FiberBundle F Z] :
    IsSerreFibration (Bundle.TotalSpace.proj : Bundle.TotalSpace F Z → B) :=
  isLocallyTrivial_proj.isSerreFibration

end Morse.Homotopy
