import Morse.Chapter3.TorusSurface
import Morse.Chapter3.EulerChar
import Morse.Chapter2.Submanifold

/-!
Milnor, *Morse Theory*, §1, pp. 1–3: the height function on the torus of Diagram 1, made exact,
together with what Theorem 3.1 (§3, pp. 12–13) and formula (3) of §5 (p. 29) say about it.

# Milnor's opening example: the height function on an upright torus

## Milnor's text, paraphrased

A torus `M` touches a plane `V` (Diagram 1); `f : M → ℝ` is the height above `V` and
`M^a = {x ∈ M : f(x) ≤ a}`.  Milnor reads off the picture (pp. 1–2) that, with `p, q, r, s` the
points marked in Diagram 1 from the bottom up,
(1) `M^a` is empty for `a < 0` (printed "`a < 0 < f(p)`", see below); (2) a 2-cell for
`f(p) < a < f(q)`; (3) a cylinder for
`f(q) < a < f(r)`; (4) a compact genus-one surface bounded by a circle for `f(r) < a < f(s)`;
(5) all of `M` for `f(s) < a`.  Up to homotopy type, (1) → (2) attaches a 0-cell, (2) → (3) and
(3) → (4) a 1-cell each, (4) → (5) a 2-cell.  On p. 3: the points `p, q, r, s` where the homotopy
type changes are the critical points of `f`; in suitable coordinates `(x, y)` near them `f` is
`x² + y²` at `p`, `const + x² − y²` at `q` and `r`, `const − x² − y²` at `s`; the number of minus
signs is the dimension of the cell attached when `a < f(point) < b`.

## What is proved here

`T = Morse.torus R r` (`0 < r < R`) is the torus of revolution about the `x₃`-axis
(`Morse/Chapter3/TorusSurface.lean`), and `f = x₁ + R + r` (`Morse.Torus.height`), the height above
the plane `V = {x₁ = −(R + r)}` tangent to `T` at `p`.

* `Morse.Torus.isCriticalPointM_height_iff`: **`f|T` has exactly four critical points**,
  `p = (−(R + r), 0, 0)`, `q = (−(R − r), 0, 0)`, `r = (R − r, 0, 0)`, `s = (R + r, 0, 0)`
  (`Morse.Torus.pointP`, …, `Morse.Torus.pointS`), at heights `0, 2r, 2R, 2R + 2r`
  (`Morse.Torus.height_pointP`, …; `Morse.Torus.criticalValues_height`).
* `Morse.Torus.pointP_spec`, `Morse.Torus.pointQ_spec`, `Morse.Torus.pointR_spec`,
  `Morse.Torus.pointS_spec`: **all four are non-degenerate, of indices `0, 1, 1, 2`**;
  `Morse.Torus.isMorseFunction_height`: `f|T` is a Morse function;
  `Morse.Torus.critCount_height`: `C₀ = 1`, `C₁ = 2`, `C₂ = 1`.
* `Morse.isEulerNumber_torus`, `Morse.IsEulerNumber.eq_torus`: **the Euler number of `T` is
  `1 − 2 + 1 = 0`**: the integer of the Poincaré–Hopf theorem, by
  `Morse.exists_eulerNumber_eq_sum_critCount`.  Hence `Morse.sum_critCount_torus`: *every* Morse
  function on `T` has `C₀ − C₁ + C₂ = 0`.
  `Morse.IsEulerNumber.eq_torus_of_rotation` checks the value independently of Morse theory: the
  rotation field `(−x₂, x₁, 0)` is a tangent field on `T` without zeros.
* Milnor's (1) and (5): `Morse.Torus.sublevel_height_eq_empty` (`a < 0`) and
  `Morse.Torus.sublevel_height_eq_univ` (`a ≥ 2R + 2r = f(s)`).
* `Morse.theorem_3_1_torus`: **Theorem 3.1 on the torus**: if `[a, b]` contains none of the four
  critical values, a diffeomorphism of `T` carries `T^a` onto `T^b`, `T^a` is a strong deformation
  retract of `T^b`, and the inclusion `T^a → T^b` is a homotopy equivalence
  (`Morse.theorem_3_1_submanifold_of_isCompact`).  In particular all `T^a` with `a` in one of the
  intervals of (2), (3), (4) are diffeomorphic to one another.

## How the Hessian is computed: Lagrange's rule

`T = g⁻¹(0)` for the polynomial `g` of `Morse/Chapter3/TorusSurface.lean`, and `T_qT = ker dg_q`.

* *Critical points.*  `q` is critical iff `dx₁` vanishes on `ker dg_q`.  Testing on the tangent
  vectors `(−q₂, q₁, 0)` (rotation about the axis) and `(Q q₃, 0, −(Q − 2R²) q₁)`,
  `Q = ‖q‖² + R² − r² > 0`, gives `q₂ = q₃ = 0`, and then `T` forces `|q₁| = R ± r`.
* *Hessian.*  At `q = (a, 0, 0)`, `dg_q = κ dx₁` with `κ = 4a(a² − R² − r²) ≠ 0`.  The function
  `G = f − κ⁻¹ g` equals `f` on `T` and is critical at `q` as a function on `ℝ³`.  In any slice
  parametrization `x` of `T` at `q`, the second-order term `dG_q(d²x)` of the chain rule therefore
  vanishes (`Morse.hessian_comp_sliceParam_of_fderiv_eq_zero`), so the Hessian of `f|T` at `q` is
  `d²G_q` restricted to `T_qT = {v₁ = 0}`.  In the coordinates `(v₂, v₃)` it is
  `diag(−1/a, −(a² + R² − r²)/(a(a² − R² − r²)))` (`Morse.Torus.onAxis_spec`), that is
  `diag(1/(R+r), 1/r)` at `p`, `diag(1/(R−r), −1/r)` at `q`, `diag(−1/(R−r), 1/r)` at `r`,
  `diag(−1/(R+r), −1/r)` at `s`: the principal curvatures of `T`, with signs.  A diagonal form
  with nonzero entries on a plane is non-degenerate and its index is the number of negative
  entries (`Morse.isNondegenerate_and_index_of_diag`).

## What Milnor leaves implicit, and what is not done

* **(1) as printed** (p. 1) reads "`a < 0 < f(p)`"; since `V` is tangent to `M` at `p`,
  `f(p) = 0` (`Morse.Torus.height_pointP`) and the hypothesis is `a < 0 = f(p)` (already noted in
  `Exposition/Chapter1.md`).  Likewise (5) holds for `a = f(s)` too.
* **"They are the critical points of the function"** (p. 3) is asserted, not checked; it is
  `Morse.Torus.isCriticalPointM_height_iff`.  Nor are the normal forms at `p, q, r, s` justified:
  they are the Lemma of Morse (`Morse.morse_lemmaM`, `Morse.indexM_eq_of_morse_chart`) applied
  with the indices `0, 1, 1, 2` computed here, which are not restated in that form.
* **"where `a < f(point) < b`"** (p. 3) is not enough for the number of minus signs to be the
  dimension of *the* cell attached: `[a, b]` must contain no other critical value (as in the
  hypothesis of Theorem 3.2).  For `a < 0` and `b > 2R + 2r` one has `a < f(q) < b`, but `M^b`
  arises from `M^a = ∅` by attaching four cells.
* **The position of the torus and `r < R`**: see `Morse/Chapter3/TorusSurface.lean`.
* **Not done.**  That the sublevel sets in (2), (3), (4) are a disk, a cylinder and a punctured
  torus, and the cell attachments, are not proved for the torus: the identifications need explicit
  homeomorphisms, and the cell attachments would follow from Theorem 3.2 on submanifolds
  (`Morse.theorem_3_2_submanifold`, `Morse/Chapter2/CellAttachSubmanifold.lean`), which is not
  applied here.  Only what follows from Theorem 3.1 is stated.  The Euler number `0` is the integer of Poincaré–Hopf; its identification with the
  homological Euler characteristic of `T` needs homology (see `Morse/Chapter3/EulerChar.lean`).
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

/-! ### Lagrange's rule for the Hessian on a submanifold -/

section Lagrange

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

/-- A critical point of an ambient function `G : V → ℝ` at a point of `N` is a critical point of
`G|N`. -/
theorem isCriticalPointM_comp_val_of_fderiv_eq_zero {G : V → ℝ} {q : N}
    (hG : DifferentiableAt ℝ G q) (h0 : fderiv ℝ G q = 0) :
    letI := hN.chartedSpace
    IsCriticalPointM Z (G ∘ Subtype.val) q :=
  (isCriticalPointM_comp_val_iff_forall_tangent hN hG).2 fun v _ => by rw [h0]; rfl

/-- **The Hessian at an ambient critical point** (the device behind Lagrange's rule): if
`dG_q = 0`, then in any slice parametrization `x` of `N` at `q` the Hessian of `G ∘ x` is the
ambient Hessian `d²G_q(dx ·, dx ·)`; the term `dG_q(d²x)` of the chain rule vanishes.  For
`G = F − μ g`, `N = g⁻¹(0)` and `dF_q = μ dg_q`, this computes the Hessian of `F|N`. -/
theorem hessian_comp_sliceParam_of_fderiv_eq_zero (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N)
    {G : V → ℝ} {q : N} (hq : q.1 ∈ σ.φ.source) (hG : ContDiffAt ℝ 2 G q)
    (h0 : fderiv ℝ G q = 0) (v w : Z) :
    hessian (G ∘ sliceParam σ) (σ.φ q).1 v w =
      hessian G q (fderiv ℝ (sliceParam σ) (σ.φ q).1 v)
        (fderiv ℝ (sliceParam σ) (σ.φ q).1 w) := by
  have hx : sliceParam σ (σ.φ q).1 = q := sliceParam_toChart σ hq
  have hG' : ContDiffAt ℝ 2 G (sliceParam σ (σ.φ q).1) := by rw [hx]; exact hG
  have h0' : fderiv ℝ G (sliceParam σ (σ.φ q).1) = 0 := by rw [hx]; exact h0
  have hψ : ContDiffAt ℝ 2 (sliceParam σ) (σ.φ q).1 :=
    (contDiffAt_sliceParam σ (toChart_apply_mem_target σ hq)).of_le (by norm_cast)
  rw [hessian_comp hG' hψ h0', hx]

end Lagrange

/-! ### Diagonal forms on a plane -/

section Diag

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

/-- On a space of dimension `2`, a form taking a negative and a positive value has index `1`. -/
theorem index_eq_one_of_finrank_eq_two (hZ : finrank ℝ Z = 2) {B : Z →L[ℝ] Z →L[ℝ] ℝ}
    {u w : Z} (hu : B u u < 0) (hw : 0 < B w w) : index B = 1 := by
  apply le_antisymm
  · obtain ⟨W, hW, hneg⟩ := exists_negDef_finrank_eq_index B
    by_contra h
    replace h := not_le.1 h
    have hle : finrank ℝ W ≤ 2 := hZ ▸ Submodule.finrank_le W
    have htop : W = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw
    exact absurd (hneg w (htop ▸ Submodule.mem_top) hw0) (not_lt.2 hw.le)
  · have hu0 : u ≠ 0 := by rintro rfl; simp at hu
    have h := finrank_le_index_of_negDef B (W := ℝ ∙ u) fun v hv hv0 => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
      have hc : c ≠ 0 := by rintro rfl; simp at hv0
      simp only [map_smul, smul_apply, smul_eq_mul]
      have : 0 < c * c := mul_self_pos.2 hc
      nlinarith
    rwa [finrank_span_singleton hu0] at h

/-- **A diagonal form on a plane**: if `B(v, w) = α ℓ₁(v)ℓ₁(w) + β ℓ₂(v)ℓ₂(w)` with `α, β ≠ 0`, the
functionals `ℓ₁, ℓ₂` jointly injective and dual to vectors `v₁, v₂`, then `B` is non-degenerate
and its index is the number of negative coefficients. -/
theorem isNondegenerate_and_index_of_diag (hZ : finrank ℝ Z = 2) {B : Z →L[ℝ] Z →L[ℝ] ℝ}
    {ℓ₁ ℓ₂ : Z →L[ℝ] ℝ} {α β : ℝ}
    (hB : ∀ v w, B v w = α * (ℓ₁ v * ℓ₁ w) + β * (ℓ₂ v * ℓ₂ w))
    (hinj : ∀ v, ℓ₁ v = 0 → ℓ₂ v = 0 → v = 0) {v₁ v₂ : Z}
    (h₁ : ℓ₁ v₁ = 1) (h₁' : ℓ₂ v₁ = 0) (h₂ : ℓ₁ v₂ = 0) (h₂' : ℓ₂ v₂ = 1)
    (hα : α ≠ 0) (hβ : β ≠ 0) :
    IsNondegenerate B ∧ index B = (if α < 0 then 1 else 0) + (if β < 0 then 1 else 0) := by
  refine ⟨isNondegenerate_iff.2 fun v hv => hinj v ?_ ?_, ?_⟩
  · have := hv v₁
    rw [hB, h₁, h₁'] at this
    simpa [hα] using this
  · have := hv v₂
    rw [hB, h₂, h₂'] at this
    simpa [hβ] using this
  · have hBvv : ∀ v, B v v = α * ℓ₁ v ^ 2 + β * ℓ₂ v ^ 2 := fun v => by rw [hB]; ring
    rcases lt_or_gt_of_ne hα with hα' | hα' <;> rcases lt_or_gt_of_ne hβ with hβ' | hβ'
    · rw [if_pos hα', if_pos hβ', index_eq_finrank_of_negDef, hZ]
      intro v hv0
      rw [hBvv]
      by_cases h1 : ℓ₁ v = 0
      · have h2 : ℓ₂ v ≠ 0 := fun h2 => hv0 (hinj v h1 h2)
        rw [h1]
        nlinarith [sq_pos_of_ne_zero h2]
      · nlinarith [sq_pos_of_ne_zero h1, sq_nonneg (ℓ₂ v)]
    · rw [if_pos hα', if_neg (not_lt.2 hβ'.le)]
      exact index_eq_one_of_finrank_eq_two hZ (u := v₁) (w := v₂)
        (by rw [hBvv, h₁, h₁']; linarith) (by rw [hBvv, h₂, h₂']; linarith)
    · rw [if_neg (not_lt.2 hα'.le), if_pos hβ']
      exact index_eq_one_of_finrank_eq_two hZ (u := v₂) (w := v₁)
        (by rw [hBvv, h₂, h₂']; linarith) (by rw [hBvv, h₁, h₁']; linarith)
    · rw [if_neg (not_lt.2 hα'.le), if_neg (not_lt.2 hβ'.le)]
      exact index_eq_zero_of_nonneg fun v => by rw [hBvv]; positivity

end Diag

namespace Torus

local notation "𝔼" => EuclideanSpace ℝ (Fin 3)
local notation "𝔻" => EuclideanSpace ℝ (Fin 2)
local notation "π" => EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3)

variable {R r : ℝ}

/-! ### The height function and the four points -/

/-- **Milnor's height function** `f`: the height `x₁ + R + r` above the plane
`V = {x₁ = −(R + r)}`, which touches the torus at `p` (Diagram 1). -/
def height (R r : ℝ) (x : 𝔼) : ℝ := x 0 + R + r

theorem hasFDerivAt_height (x : 𝔼) : HasFDerivAt (height R r) (π 0) x :=
  ((hasFDerivAt_coord 0 x).add_const R).add_const r

theorem contDiff_height : ContDiff ℝ ∞ (height R r) := by
  unfold height
  fun_prop

/-- Milnor's `p = (−(R + r), 0, 0)`, the lowest point. -/
def pointP (R r : ℝ) : 𝔼 := onAxis (-(R + r))
/-- Milnor's `q = (−(R − r), 0, 0)`. -/
def pointQ (R r : ℝ) : 𝔼 := onAxis (-(R - r))
/-- Milnor's `r = (R − r, 0, 0)`. -/
def pointR (R r : ℝ) : 𝔼 := onAxis (R - r)
/-- Milnor's `s = (R + r, 0, 0)`, the highest point. -/
def pointS (R r : ℝ) : 𝔼 := onAxis (R + r)

theorem pointP_mem (hr : 0 < r) (hrR : r < R) : pointP R r ∈ torus R r :=
  onAxis_mem (Or.inl (by rw [abs_neg, abs_of_pos (by linarith)]))

theorem pointQ_mem (hrR : r < R) : pointQ R r ∈ torus R r :=
  onAxis_mem (Or.inr (by rw [abs_neg, abs_of_pos (by linarith)]))

theorem pointR_mem (hrR : r < R) : pointR R r ∈ torus R r :=
  onAxis_mem (Or.inr (abs_of_pos (by linarith)))

theorem pointS_mem (hr : 0 < r) (hrR : r < R) : pointS R r ∈ torus R r :=
  onAxis_mem (Or.inl (abs_of_pos (by linarith)))

/-- `f(p) = 0`: the plane `V` touches the torus at `p`. -/
theorem height_pointP : height R r (pointP R r) = 0 := by simp [height, pointP]
/-- `f(q) = 2r`. -/
theorem height_pointQ : height R r (pointQ R r) = 2 * r := by simp [height, pointQ]; ring
/-- `f(r) = 2R`. -/
theorem height_pointR : height R r (pointR R r) = 2 * R := by simp [height, pointR]; ring
/-- `f(s) = 2R + 2r`. -/
theorem height_pointS : height R r (pointS R r) = 2 * R + 2 * r := by
  simp [height, pointS]; ring

theorem vec3_apply_zero (a b c : ℝ) : (!₂[a, b, c] : 𝔼) 0 = a := rfl
theorem vec3_apply_one (a b c : ℝ) : (!₂[a, b, c] : 𝔼) 1 = b := rfl
theorem vec3_apply_two (a b c : ℝ) : (!₂[a, b, c] : 𝔼) 2 = c := rfl

/-- At the four points `a = ±(R ± r)`, `a ≠ 0` and `a² − R² − r² = ±2Rr ≠ 0`. -/
theorem coef_ne_zero (hr : 0 < r) (hrR : r < R) {a : ℝ}
    (ha : a = -(R + r) ∨ a = -(R - r) ∨ a = R - r ∨ a = R + r) :
    a ≠ 0 ∧ a ^ 2 - R ^ 2 - r ^ 2 ≠ 0 := by
  have hRr : 0 < R * r := mul_pos (hr.trans hrR) hr
  rcases ha with rfl | rfl | rfl | rfl
  · exact ⟨by linarith, by nlinarith⟩
  · exact ⟨by linarith, by nlinarith⟩
  · exact ⟨by linarith, by nlinarith⟩
  · exact ⟨by linarith, by nlinarith⟩

/-- On the torus, `0 ≤ f ≤ 2R + 2r`. -/
theorem height_mem_Icc (hr : 0 < r) {x : 𝔼} (hx : x ∈ torus R r) :
    height R r x ∈ Icc 0 (2 * R + 2 * r) := by
  have hx' : (√(x 0 ^ 2 + x 1 ^ 2) - R) ^ 2 + x 2 ^ 2 = r ^ 2 := hx
  set ρ := √(x 0 ^ 2 + x 1 ^ 2) with hρ
  have hρle : ρ ≤ R + r := by nlinarith [sq_nonneg (x 2)]
  have habs : |x 0| ≤ ρ := Real.abs_le_sqrt (by nlinarith [sq_nonneg (x 1)])
  have := abs_le.1 (habs.trans hρle)
  constructor <;> simp only [height] <;> linarith

/-- **Milnor's (1)**: `T^a` is empty for `a < 0 = f(p)`. -/
theorem sublevel_height_eq_empty (hr : 0 < r) {a : ℝ} (ha : a < 0) :
    sublevel (height R r ∘ (Subtype.val : torus R r → 𝔼)) a = ∅ := by
  ext x
  simp only [mem_sublevel, comp_apply, mem_empty_iff_false, iff_false, not_le]
  exact ha.trans_le (height_mem_Icc hr x.2).1

/-- **Milnor's (5)**: `T^a` is the whole torus for `a ≥ f(s) = 2R + 2r`. -/
theorem sublevel_height_eq_univ (hr : 0 < r) {a : ℝ} (ha : 2 * R + 2 * r ≤ a) :
    sublevel (height R r ∘ (Subtype.val : torus R r → 𝔼)) a = univ := by
  ext x
  simp only [mem_sublevel, comp_apply, mem_univ, iff_true]
  exact (height_mem_Icc hr x.2).2.trans ha

/-! ### Critical points, Hessians and indices -/

section Crit

variable (hr : 0 < r) (hrR : r < R)

local notation "hT" => isSliceSubmanifold_torus hr hrR

include hr hrR in
/-- `q` is a critical point of `f|T` iff `dx₁` vanishes on `T_qT = ker dg_q`. -/
theorem isCriticalPointM_height_iff_forall (q : torus R r) :
    letI := (hT).chartedSpace
    IsCriticalPointM 𝔻 (height R r ∘ Subtype.val) q ↔
      ∀ w : 𝔼, dpoly R r q w = 0 → w 0 = 0 := by
  rw [isCriticalPointM_comp_val_iff_forall_tangent hT (hasFDerivAt_height q.1).differentiableAt,
    (hasFDerivAt_height q.1).fderiv]
  simp only [mem_tangentSubspace_torus_iff hr hrR, proj_apply]

include hr hrR in
/-- **The critical points of the height function are exactly `p, q, r, s`** (Milnor, p. 3). -/
theorem isCriticalPointM_height_iff (q : torus R r) :
    letI := (hT).chartedSpace
    IsCriticalPointM 𝔻 (height R r ∘ Subtype.val) q ↔
      (q : 𝔼) = pointP R r ∨ (q : 𝔼) = pointQ R r ∨ (q : 𝔼) = pointR R r ∨
        (q : 𝔼) = pointS R r := by
  rw [isCriticalPointM_height_iff_forall hr hrR]
  constructor
  · intro h
    have hQ := quad_pos hr.le hrR q.1
    set Q := quad R r q.1 with hQdef
    -- the rotation vector and a vector in the meridian plane are tangent
    have h1 := h !₂[-q.1 1, q.1 0, 0] (by
      rw [dpoly_apply, vec3_apply_zero, vec3_apply_one, vec3_apply_two]; ring)
    have h2 := h !₂[Q * q.1 2, 0, -(Q - 2 * R ^ 2) * q.1 0] (by
      rw [dpoly_apply, vec3_apply_zero, vec3_apply_one, vec3_apply_two, ← hQdef]; ring)
    rw [vec3_apply_zero, neg_eq_zero] at h1
    rw [vec3_apply_zero] at h2
    have h1' : q.1 1 = 0 := h1
    have h2' : q.1 2 = 0 := (mul_eq_zero.1 h2).resolve_left hQ.ne'
    have hq : (|q.1 0| - R) ^ 2 = r ^ 2 := by
      have hq := q.2
      simp only [torus, mem_ofPred_eq, h1', h2'] at hq
      simpa [Real.sqrt_sq_eq_abs] using hq
    have hq' : |q.1 0| = R + r ∨ |q.1 0| = R - r := by
      have : (|q.1 0| - R - r) * (|q.1 0| - R + r) = 0 := by linear_combination hq
      rcases mul_eq_zero.1 this with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    have hext : (q : 𝔼) = onAxis (q.1 0) := by
      ext i
      fin_cases i <;> simp [h1', h2']
    rw [hext]
    rcases hq' with h | h
    · rcases (abs_eq (by linarith)).1 h with h' | h' <;> rw [h'] <;> simp [pointP, pointS]
    · rcases (abs_eq (by linarith)).1 h with h' | h' <;> rw [h'] <;> simp [pointQ, pointR]
  · intro h w hw
    obtain ⟨a, ha, hqa⟩ : ∃ a, (a = -(R + r) ∨ a = -(R - r) ∨ a = R - r ∨ a = R + r) ∧
        (q : 𝔼) = onAxis a := by
      rcases h with h | h | h | h
      · exact ⟨_, Or.inl rfl, h⟩
      · exact ⟨_, Or.inr (Or.inl rfl), h⟩
      · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), h⟩
      · exact ⟨_, Or.inr (Or.inr (Or.inr rfl)), h⟩
    obtain ⟨ha0, hc⟩ := coef_ne_zero hr hrR ha
    rw [hqa, dpoly_onAxis] at hw
    exact (mul_eq_zero.1 hw).resolve_left (mul_ne_zero (mul_ne_zero four_ne_zero ha0) hc)

include hr hrR in
/-- The critical points, as points of the manifold `T`. -/
theorem isCriticalPointM_height_iff' (q : torus R r) :
    letI := (hT).chartedSpace
    IsCriticalPointM 𝔻 (height R r ∘ Subtype.val) q ↔
      q = ⟨pointP R r, pointP_mem hr hrR⟩ ∨ q = ⟨pointQ R r, pointQ_mem hrR⟩ ∨
        q = ⟨pointR R r, pointR_mem hrR⟩ ∨ q = ⟨pointS R r, pointS_mem hr hrR⟩ := by
  rw [isCriticalPointM_height_iff hr hrR]
  simp only [Subtype.ext_iff]

include hr hrR in
/-- **The Hessian at a point `(a, 0, 0)` of the torus, by Lagrange's rule**: if `a ≠ 0` and
`a² ≠ R² + r²`, the point is a non-degenerate critical point of `f|T` whose index is the number of
negative entries of `diag(−1/a, −(a² + R² − r²)/(a(a² − R² − r²)))`. -/
theorem onAxis_spec {a : ℝ} (ha : onAxis a ∈ torus R r) (ha0 : a ≠ 0)
    (hc : a ^ 2 - R ^ 2 - r ^ 2 ≠ 0) :
    letI := (hT).chartedSpace
    IsCriticalPointM 𝔻 (height R r ∘ Subtype.val) ⟨onAxis a, ha⟩ ∧
      IsNondegenerate (hessianM 𝔻 (height R r ∘ Subtype.val) ⟨onAxis a, ha⟩) ∧
      indexM 𝔻 (height R r ∘ Subtype.val) ⟨onAxis a, ha⟩ =
        (if 0 < a then 1 else 0) + (if 0 < a * (a ^ 2 - R ^ 2 - r ^ 2) then 1 else 0) := by
  let _ := (hT).chartedSpace
  set P : torus R r := ⟨onAxis a, ha⟩ with hP
  set κ : ℝ := 4 * a * (a ^ 2 - R ^ 2 - r ^ 2) with hκdef
  have hκ : κ ≠ 0 := mul_ne_zero (mul_ne_zero four_ne_zero ha0) hc
  -- Lagrange: `G = f - κ⁻¹ g` agrees with `f` on the torus and is critical at `P` in `ℝ³`
  set G : 𝔼 → ℝ := fun x => height R r x - κ⁻¹ * poly R r x with hG
  have hGd : ∀ x, HasFDerivAt G (π 0 - κ⁻¹ • dpoly R r x) x := fun x =>
    (hasFDerivAt_height x).sub ((hasFDerivAt_poly x).const_mul κ⁻¹)
  have hGc2 : ContDiffAt ℝ 2 G P :=
    (contDiff_height.sub (contDiff_const.mul contDiff_poly)).contDiffAt.of_le (by norm_cast)
  have hGval : G ∘ Subtype.val = height R r ∘ (Subtype.val : torus R r → 𝔼) := by
    funext x
    simp [G, (mem_torus_iff hr hrR).1 x.2]
  have hdpolyP : dpoly R r (onAxis a) = κ • π 0 := by
    ext w
    rw [dpoly_onAxis]
    simp [hκdef]
  have hG0 : fderiv ℝ G P = 0 := by
    rw [(hGd _).fderiv]
    change π 0 - κ⁻¹ • dpoly R r (onAxis a) = 0
    rw [hdpolyP, smul_smul, inv_mul_cancel₀ hκ, one_smul, sub_self]
  have hGh : ∀ v w, hessian G P v w = -κ⁻¹ * d2poly R r (onAxis a) v w := by
    have h1 : fderiv ℝ G = fun x => π 0 - κ⁻¹ • dpoly R r x := funext fun x => (hGd x).fderiv
    have h2 : HasFDerivAt (fun x => π 0 - κ⁻¹ • dpoly R r x) (0 - κ⁻¹ • d2poly R r (onAxis a))
        (onAxis a) :=
      (hasFDerivAt_const (π 0) (onAxis a)).sub ((hasFDerivAt_dpoly (onAxis a)).const_smul κ⁻¹)
    intro v w
    rw [hessian, h1, h2.fderiv]
    simp
  have hcritG : IsCriticalPointM 𝔻 (G ∘ Subtype.val) P :=
    isCriticalPointM_comp_val_of_fderiv_eq_zero hT (hGd _).differentiableAt hG0
  -- a slice chart at `P`, and the derivative `L` of its parametrization: `range L = {w₁ = 0}`
  obtain ⟨σ, hσ⟩ := hT P.1 P.2
  set L := fderiv ℝ (sliceParam σ) (σ.φ P).1 with hL
  have hrange : ∀ w, w ∈ LinearMap.range (L : 𝔻 →ₗ[ℝ] 𝔼) ↔ w 0 = 0 := by
    intro w
    rw [← tangentSubspace_eq_range_fderiv_sliceParam hT σ hσ, mem_tangentSubspace_torus_iff hr hrR]
    change dpoly R r (onAxis a) w = 0 ↔ _
    rw [hdpolyP]
    simp [hκ]
  have hL0 : ∀ v, L v 0 = 0 := fun v => (hrange _).1 ⟨v, rfl⟩
  have hLinj : Injective L := by
    have hfr : finrank ℝ (LinearMap.range (L : 𝔻 →ₗ[ℝ] 𝔼)) = 2 := by
      rw [← tangentSubspace_eq_range_fderiv_sliceParam hT σ hσ]
      exact finrank_tangentSubspace_torus hr hrR P
    have h := LinearMap.finrank_range_add_finrank_ker (L : 𝔻 →ₗ[ℝ] 𝔼)
    rw [hfr, finrank_euclideanSpace_fin] at h
    have : LinearMap.ker (L : 𝔻 →ₗ[ℝ] 𝔼) = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
    exact LinearMap.ker_eq_bot.1 this
  obtain ⟨v₁, hv₁⟩ := (hrange !₂[0, 1, 0]).2 rfl
  obtain ⟨v₂, hv₂⟩ := (hrange !₂[0, 0, 1]).2 rfl
  have e₁ : L v₁ = !₂[0, 1, 0] := hv₁
  have e₂ : L v₂ = !₂[0, 0, 1] := hv₂
  -- the Hessian of `G ∘ x` is diagonal in the coordinates `x₂, x₃` of `dx`
  have hB : ∀ v w, hessian (G ∘ sliceParam σ) (σ.φ P).1 v w =
      (-a⁻¹) * ((π 1 ∘L L) v * (π 1 ∘L L) w) +
        (-(a ^ 2 + R ^ 2 - r ^ 2) / (a * (a ^ 2 - R ^ 2 - r ^ 2))) *
          ((π 2 ∘L L) v * (π 2 ∘L L) w) := by
    intro v w
    rw [hessian_comp_sliceParam_of_fderiv_eq_zero σ hσ hGc2 hG0, hGh, d2poly_onAxis _ (hL0 v)]
    simp only [ContinuousLinearMap.coe_comp, comp_apply, proj_apply, hκdef]
    field_simp
    ring
  have hpos : 0 < a ^ 2 + R ^ 2 - r ^ 2 := by nlinarith
  obtain ⟨hnd, hidx⟩ := isNondegenerate_and_index_of_diag (v₁ := v₁) (v₂ := v₂)
    finrank_euclideanSpace_fin hB
    (fun v h1 h2 => hLinj (by
      rw [map_zero]
      have h1' : L v 1 = 0 := h1
      have h2' : L v 2 = 0 := h2
      ext i
      fin_cases i <;> simp [hL0 v, h1', h2']))
    (by change L v₁ 1 = 1; rw [e₁]; rfl) (by change L v₁ 2 = 0; rw [e₁]; rfl)
    (by change L v₂ 1 = 0; rw [e₂]; rfl) (by change L v₂ 2 = 1; rw [e₂]; rfl)
    (by simpa using ha0) (div_ne_zero (by linarith) (mul_ne_zero ha0 hc))
  have hα : (-a⁻¹ < 0) ↔ 0 < a := by rw [neg_lt_zero, inv_pos]
  have hβ : (-(a ^ 2 + R ^ 2 - r ^ 2) / (a * (a ^ 2 - R ^ 2 - r ^ 2)) < 0) ↔
      0 < a * (a ^ 2 - R ^ 2 - r ^ 2) := by
    rw [neg_div, neg_lt_zero, div_pos_iff_of_pos_left hpos]
  simp only [hα, hβ] at hidx
  -- back from `G ∘ x` to `f|T`
  have hndG := (isNondegenerate_hessian_comp_sliceParam_iff hT σ hσ hGc2 hcritG).1 hnd
  have hidxG := index_hessian_comp_sliceParam hT σ hσ hGc2 hcritG
  rw [hGval] at hcritG hndG hidxG
  exact ⟨hcritG, hndG, hidxG ▸ hidx⟩

include hr hrR in
/-- **`p` is a non-degenerate critical point of index `0`** (the minimum; Milnor:
`f = x² + y²` near `p`). -/
theorem pointP_spec :
    letI := (hT).chartedSpace
    IsNondegenerateCriticalPointM 𝔻 (height R r ∘ Subtype.val) ⟨pointP R r, pointP_mem hr hrR⟩ ∧
      indexM 𝔻 (height R r ∘ Subtype.val) ⟨pointP R r, pointP_mem hr hrR⟩ = 0 := by
  have hRr : 0 < R * r := mul_pos (hr.trans hrR) hr
  obtain ⟨ha0, hc⟩ := coef_ne_zero hr hrR (a := -(R + r)) (Or.inl rfl)
  obtain ⟨h1, h2, h3⟩ := onAxis_spec hr hrR (pointP_mem hr hrR) ha0 hc
  refine ⟨⟨h1, h2⟩, h3.trans ?_⟩
  rw [if_neg (by linarith), if_neg (by nlinarith)]

include hr hrR in
/-- **`q` is a non-degenerate critical point of index `1`** (Milnor: `f = const + x² − y²`). -/
theorem pointQ_spec :
    letI := (hT).chartedSpace
    IsNondegenerateCriticalPointM 𝔻 (height R r ∘ Subtype.val) ⟨pointQ R r, pointQ_mem hrR⟩ ∧
      indexM 𝔻 (height R r ∘ Subtype.val) ⟨pointQ R r, pointQ_mem hrR⟩ = 1 := by
  have hRr : 0 < R * r * (R - r) := mul_pos (mul_pos (hr.trans hrR) hr) (by linarith)
  obtain ⟨ha0, hc⟩ := coef_ne_zero hr hrR (a := -(R - r)) (Or.inr (Or.inl rfl))
  obtain ⟨h1, h2, h3⟩ := onAxis_spec hr hrR (pointQ_mem hrR) ha0 hc
  refine ⟨⟨h1, h2⟩, h3.trans ?_⟩
  rw [if_neg (by linarith), if_pos (by nlinarith)]

include hr hrR in
/-- **`r` is a non-degenerate critical point of index `1`** (Milnor: `f = const + x² − y²`). -/
theorem pointR_spec :
    letI := (hT).chartedSpace
    IsNondegenerateCriticalPointM 𝔻 (height R r ∘ Subtype.val) ⟨pointR R r, pointR_mem hrR⟩ ∧
      indexM 𝔻 (height R r ∘ Subtype.val) ⟨pointR R r, pointR_mem hrR⟩ = 1 := by
  have hRr : 0 < R * r * (R - r) := mul_pos (mul_pos (hr.trans hrR) hr) (by linarith)
  obtain ⟨ha0, hc⟩ := coef_ne_zero hr hrR (a := R - r) (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨h1, h2, h3⟩ := onAxis_spec hr hrR (pointR_mem hrR) ha0 hc
  refine ⟨⟨h1, h2⟩, h3.trans ?_⟩
  rw [if_pos (by linarith), if_neg (by nlinarith)]

include hr hrR in
/-- **`s` is a non-degenerate critical point of index `2`** (the maximum; Milnor:
`f = const − x² − y²`). -/
theorem pointS_spec :
    letI := (hT).chartedSpace
    IsNondegenerateCriticalPointM 𝔻 (height R r ∘ Subtype.val) ⟨pointS R r, pointS_mem hr hrR⟩ ∧
      indexM 𝔻 (height R r ∘ Subtype.val) ⟨pointS R r, pointS_mem hr hrR⟩ = 2 := by
  have hRr : 0 < R * r * (R + r) := mul_pos (mul_pos (hr.trans hrR) hr) (by linarith)
  obtain ⟨ha0, hc⟩ := coef_ne_zero hr hrR (a := R + r) (Or.inr (Or.inr (Or.inr rfl)))
  obtain ⟨h1, h2, h3⟩ := onAxis_spec hr hrR (pointS_mem hr hrR) ha0 hc
  refine ⟨⟨h1, h2⟩, h3.trans ?_⟩
  rw [if_pos (by linarith), if_pos (by nlinarith)]

include hr hrR in
/-- **The height function is a Morse function on the torus.** -/
theorem isMorseFunction_height :
    letI := (hT).chartedSpace
    IsMorseFunction 𝔻 (height R r ∘ (Subtype.val : torus R r → 𝔼)) := by
  let _ := (hT).chartedSpace
  refine ⟨contMDiff_comp_val hT contDiff_height, fun q hq => ?_⟩
  rcases (isCriticalPointM_height_iff' hr hrR q).1 hq with rfl | rfl | rfl | rfl
  exacts [(pointP_spec hr hrR).1.2, (pointQ_spec hr hrR).1.2, (pointR_spec hr hrR).1.2,
    (pointS_spec hr hrR).1.2]

include hr hrR in
/-- **The critical values are `0, 2r, 2R, 2R + 2r`.** -/
theorem criticalValues_height :
    letI := (hT).chartedSpace
    {c | ∃ q : torus R r, IsCriticalPointM 𝔻 (height R r ∘ Subtype.val) q ∧ height R r q = c} =
      {0, 2 * r, 2 * R, 2 * R + 2 * r} := by
  ext c
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff,
    isCriticalPointM_height_iff' hr hrR]
  constructor
  · rintro ⟨q, h | h | h | h, rfl⟩ <;> subst h
    · exact Or.inl height_pointP
    · exact Or.inr (Or.inl height_pointQ)
    · exact Or.inr (Or.inr (Or.inl height_pointR))
    · exact Or.inr (Or.inr (Or.inr height_pointS))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨_, Or.inl rfl, height_pointP⟩
    · exact ⟨_, Or.inr (Or.inl rfl), height_pointQ⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), height_pointR⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr rfl)), height_pointS⟩

include hr hrR in
/-- **The Morse numbers of the height function**: `C₀ = 1`, `C₁ = 2`, `C₂ = 1`, and `C_λ = 0`
for `λ ≥ 3`. -/
theorem critCount_height (k : ℕ) :
    letI := (hT).chartedSpace
    critCount 𝔻 (height R r ∘ (Subtype.val : torus R r → 𝔼)) k =
      if k = 0 then 1 else if k = 1 then 2 else if k = 2 then 1 else 0 := by
  let _ := (hT).chartedSpace
  set P : torus R r := ⟨pointP R r, pointP_mem hr hrR⟩
  set Q : torus R r := ⟨pointQ R r, pointQ_mem hrR⟩
  set R' : torus R r := ⟨pointR R r, pointR_mem hrR⟩
  set S : torus R r := ⟨pointS R r, pointS_mem hr hrR⟩
  have hiP := (pointP_spec hr hrR).2
  have hiQ := (pointQ_spec hr hrR).2
  have hiR := (pointR_spec hr hrR).2
  have hiS := (pointS_spec hr hrR).2
  have hQR : Q ≠ R' := by
    intro h
    have := congrArg (fun x : torus R r => (x : 𝔼) 0) h
    simp [Q, R', pointQ, pointR] at this
    linarith
  have key : ∀ q : torus R r, (IsCriticalPointM 𝔻 (height R r ∘ Subtype.val) q ∧
      indexM 𝔻 (height R r ∘ Subtype.val) q = k) ↔
      (q = P ∧ k = 0) ∨ (q = Q ∧ k = 1) ∨ (q = R' ∧ k = 1) ∨ (q = S ∧ k = 2) := by
    intro q
    rw [isCriticalPointM_height_iff' hr hrR]
    constructor
    · rintro ⟨h | h | h | h, hk⟩ <;> subst h
      · exact Or.inl ⟨rfl, hk.symm.trans hiP⟩
      · exact Or.inr (Or.inl ⟨rfl, hk.symm.trans hiQ⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, hk.symm.trans hiR⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, hk.symm.trans hiS⟩))
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨Or.inl rfl, hiP⟩
      · exact ⟨Or.inr (Or.inl rfl), hiQ⟩
      · exact ⟨Or.inr (Or.inr (Or.inl rfl)), hiR⟩
      · exact ⟨Or.inr (Or.inr (Or.inr rfl)), hiS⟩
  unfold critCount
  rw [Set.ext key]
  rcases Nat.lt_or_ge k 3 with hk | hk
  · interval_cases k
    · simp
    · have hset : {q : torus R r | q = P ∧ 1 = 0 ∨ q = Q ∧ 1 = 1 ∨ q = R' ∧ 1 = 1 ∨
          q = S ∧ 1 = 2} = {Q, R'} := by
        ext q
        simp
      rw [hset, Set.ncard_pair hQR]
      rfl
    · simp
  · simp [show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega]

end Crit

end Torus

/-! ### The Euler number of the torus, and Theorem 3.1 -/

open Torus

local notation "𝔼" => EuclideanSpace ℝ (Fin 3)
local notation "𝔻" => EuclideanSpace ℝ (Fin 2)

section Consequences

variable {R r : ℝ} (hr : 0 < r) (hrR : r < R)

local notation "hT" => isSliceSubmanifold_torus hr hrR

/-- **The Euler number of the torus is `C₀ − C₁ + C₂ = 1 − 2 + 1 = 0`**: by
`Morse.exists_eulerNumber_eq_sum_critCount`, the integer of the Poincaré–Hopf theorem is the
alternating count of the critical points of the Morse function `f|T`. -/
theorem isEulerNumber_torus :
    IsEulerNumber (hT) (isCompact_torus hr hrR) (nonempty_torus hr hrR) 0 := by
  obtain ⟨χ, hχ, hsum⟩ := exists_eulerNumber_eq_sum_critCount (hT) (isCompact_torus hr hrR)
    (nonempty_torus hr hrR) (by norm_num)
  have h := hsum _ (isMorseFunction_height hr hrR)
  simp only [critCount_height hr hrR, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  exact h ▸ hχ

/-- **Every Euler number of the torus is `0`**, computed by Morse theory from the height
function. -/
theorem IsEulerNumber.eq_torus {χ : ℤ}
    (hχ : IsEulerNumber (hT) (isCompact_torus hr hrR) (nonempty_torus hr hrR) χ) : χ = 0 := by
  rw [hχ.eq_sum_critCount (hT) (isCompact_torus hr hrR) (nonempty_torus hr hrR) (by norm_num)
    (isMorseFunction_height hr hrR)]
  simp only [critCount_height hr hrR, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- **`C₀ − C₁ + C₂ = 0` for every Morse function on the torus** (Milnor, §5, formula (3)). -/
theorem sum_critCount_torus {f : torus R r → ℝ}
    (hf : letI := (hT).chartedSpace; IsMorseFunction 𝔻 f) :
    letI := (hT).chartedSpace
    ∑ k ∈ Finset.range 3, (-1 : ℤ) ^ k * critCount 𝔻 f k = 0 :=
  (isEulerNumber_torus hr hrR).sum_critCount_eq (hT) (isCompact_torus hr hrR)
    (nonempty_torus hr hrR) (by norm_num) hf

/-- The rotation field `(−x₂, x₁, 0)` about the axis of the torus. -/
def Torus.rotField (x : 𝔼) : 𝔼 :=
  (-x 1) • EuclideanSpace.single 0 1 + x 0 • EuclideanSpace.single 1 1

include hr hrR in
/-- **Independent check: every Euler number of the torus is `0`, without Morse theory.**  The
rotation field is a smooth tangent field on `T` with no zeros (on `T`, `x₁² + x₂² ≥ (R − r)²`), so
its index sum is the empty sum. -/
theorem IsEulerNumber.eq_torus_of_rotation {χ : ℤ}
    (hχ : IsEulerNumber (hT) (isCompact_torus hr hrR) (nonempty_torus hr hrR) χ) : χ = 0 := by
  let _ := (hT).chartedSpace
  have hsm : ContMDiff 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) ∞ (fun q : torus R r => rotField q.1) := by
    have : ContDiff ℝ ∞ rotField := by
      unfold rotField
      fun_prop
    exact this.contMDiff.comp (hT).contMDiff_val
  have htan : ∀ q : torus R r, rotField q.1 ∈ tangentSubspace hT q := fun q => by
    rw [mem_tangentSubspace_torus_iff hr hrR, dpoly_apply]
    have e0 : rotField q.1 0 = -q.1 1 := by simp [rotField]
    have e1 : rotField q.1 1 = q.1 0 := by simp [rotField]
    have e2 : rotField q.1 2 = 0 := by simp [rotField]
    rw [e0, e1, e2]
    ring
  have hne : ∀ q : torus R r, rotField q.1 ≠ 0 := by
    intro q h
    have h0 : q.1 1 = 0 := by simpa [rotField] using congrArg (fun x : 𝔼 => x 0) h
    have h1 : q.1 0 = 0 := by simpa [rotField] using congrArg (fun x : 𝔼 => x 1) h
    have hq : R ^ 2 + q.1 2 ^ 2 = r ^ 2 := by
      have hq := q.2
      simp only [torus, mem_ofPred_eq, h0, h1] at hq
      simpa using hq
    nlinarith [sq_nonneg (q.1 2)]
  have h := hχ (fun q : torus R r => rotField q.1) hsm htan (j := 0) Fin.elim0
    (fun i => i.elim0) fun q => ⟨fun h => absurd h (hne q), fun ⟨i, _⟩ => i.elim0⟩
  simpa using h.symm

/-- **Theorem 3.1 on the torus** (Milnor, §3, pp. 12–13, applied to §1): if the interval `[a, b]`
contains none of the critical values `0, 2r, 2R, 2R + 2r`, then a diffeomorphism of `T` carries
`T^a` onto `T^b`, `T^a` is a strong deformation retract of `T^b`, and the inclusion `T^a → T^b` is a
homotopy equivalence.  This is all that §3 says about Milnor's cases (2), (3), (4) without
Theorem 3.2: the sublevel sets `T^a`, for `a` in any one of the intervals `(0, 2r)`, `(2r, 2R)`,
`(2R, 2R + 2r)`, are all diffeomorphic to each other. -/
theorem theorem_3_1_torus {a b : ℝ} (hab : a ≤ b) (h0 : 0 ∉ Icc a b) (h1 : 2 * r ∉ Icc a b)
    (h2 : 2 * R ∉ Icc a b) (h3 : 2 * R + 2 * r ∉ Icc a b) :
    letI := (hT).chartedSpace
    (∃ Φ : Diffeomorph 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔻) (torus R r) (torus R r) ∞,
        Φ '' sublevel (height R r ∘ Subtype.val) a = sublevel (height R r ∘ Subtype.val) b) ∧
      IsStrongDeformationRetract (Subtype.val ⁻¹' sublevel (height R r ∘ Subtype.val) a :
        Set (sublevel (height R r ∘ (Subtype.val : torus R r → 𝔼)) b)) ∧
      ∃ e : ContinuousMap.HomotopyEquiv (sublevel (height R r ∘ (Subtype.val : torus R r → 𝔼)) a)
          (sublevel (height R r ∘ (Subtype.val : torus R r → 𝔼)) b),
        ⇑e = Set.inclusion (sublevel_mono _ hab) :=
  theorem_3_1_submanifold_of_isCompact (hT) (isCompact_torus hr hrR) contDiff_height hab
    fun q hq hcrit => by
      rcases (isCriticalPointM_height_iff' hr hrR q).1 hcrit with rfl | rfl | rfl | rfl
      · exact h0 (height_pointP (R := R) (r := r) ▸ hq)
      · exact h1 (height_pointQ (R := R) (r := r) ▸ hq)
      · exact h2 (height_pointR (R := R) (r := r) ▸ hq)
      · exact h3 (height_pointS (R := R) (r := r) ▸ hq)

end Consequences

end Morse
