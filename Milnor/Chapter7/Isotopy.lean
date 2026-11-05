import Milnor.Chapter6.DetSign
import Milnor.Chapter6.Hadamard
import Milnor.Chapter7.GLplus

/-!
# Milnor's Lemma 2 of §6: an orientation preserving diffeomorphism of `ℝᵐ` is isotopic to `1`

Milnor proves on p. 33 (§6, Lemma 2): *any orientation preserving diffeomorphism `f` of `ℝᵐ` is
smoothly isotopic to the identity.*  The proof is in three steps.

1. `f` is isotopic to the diffeomorphism `x ↦ f x - f 0`, which fixes the origin, by the
   translation isotopy `H (x, t) = f x - t · f 0`
   (`Milnor.smoothIsotopicMap_sub_apply_zero`).
2. A diffeomorphism `g` with `g 0 = 0` is isotopic to its derivative `d g₀` at the origin, by
   `H (x, t) = g (t x) / t` for `t ≠ 0` and `H (x, 0) = d g₀ (x)`
   (`Milnor.smoothIsotopicMap_fderiv`).  That this `H` is *smooth* at `t = 0` is Hadamard's lemma,
   proved in `Milnor.Chapter6.Hadamard` (`Milnor.contDiff_ite_smul_inv`).
3. A linear automorphism of `ℝᵐ` with positive determinant is isotopic to the identity, because
   `GL⁺(m, ℝ)` is connected by smooth paths (`Milnor.smoothIsotopicMap_id_of_det_pos`).  The path
   is `Milnor.GLp.exists_glPath`, proved in `Milnor.Chapter7.GLplus`.

The three steps are combined in `Milnor.smoothIsotopicMap_id`, and
`Milnor.smoothIsotopicMap_id_of_det_pos_at` and `Milnor.lemma2_of_sec6` restate the result with
the orientation hypothesis tested at an arbitrary point, which is legitimate because the sign of
the Jacobian determinant of a diffeomorphism of `ℝᵐ` is the same at every point
(`Milnor.IsDiffeoSelf.sgn_det_fderiv_const`, a consequence of
`Milnor.sgn_det_fderiv_eq` in `Milnor.Chapter6.DetSign`).

## Placement of this file

The file sits in `Chapter7` only because Milnor's last step needs the `GL⁺` path proved there:
`Milnor.Chapter7.GLplus` may not be imported from `Chapter6`, since `Chapter7` already depends on
`Chapter6`.

**Nothing in the formal development depends on this lemma.**  Milnor uses Lemma 2 to prove Lemma 1
of §6 (invariance of the index under diffeomorphisms); the formalisation replaces that appeal by a
direct sign computation (see `Milnor.Sphere.index_eq_of_diffeo` in `Milnor.Chapter6.Invariance`),
so Lemma 2 is formalised here only because it is a theorem of the book.

## Conventions

A diffeomorphism of `E` is given *unbundled*, as a smooth map together with a smooth two-sided
inverse (`Milnor.IsDiffeoSelf`), in the style of `Milnor.Sphere.index_eq_of_diffeo`.  An isotopy is
a smooth map `H : E × ℝ → E` with `H (·, 0) = f`, `H (·, 1) = g` and **every** time slice
`H (·, t)` a diffeomorphism of `E` (`Milnor.SmoothIsotopicMap`), the shape already used for
`Milnor.Isotopic` in `Milnor.Chapter4.Homogeneity`.

Everything is stated for a finite-dimensional real normed space `E`; Milnor's `ℝᵐ` is the case
`E = EuclideanSpace ℝ (Fin m)`, recorded in `Milnor.lemma2_of_sec6`.
-/

open Set Function Module Matrix Metric
open scoped ContDiff

noncomputable section

namespace Milnor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Self-diffeomorphisms of `E` -/

/-- **A diffeomorphism of `E` onto itself**, unbundled (as in `Milnor.Sphere.index_eq_of_diffeo`):
a smooth map `f : E → E` admitting a smooth two-sided inverse. -/
def IsDiffeoSelf (f : E → E) : Prop :=
  ContDiff ℝ ∞ f ∧ ∃ g : E → E, ContDiff ℝ ∞ g ∧ (∀ x, g (f x) = x) ∧ (∀ x, f (g x) = x)

namespace IsDiffeoSelf

/-- A self-diffeomorphism is smooth. -/
theorem contDiff {f : E → E} (hf : IsDiffeoSelf f) : ContDiff ℝ ∞ f := hf.1

/-- A self-diffeomorphism is a bijection. -/
theorem bijective {f : E → E} (hf : IsDiffeoSelf f) : Bijective f := by
  obtain ⟨-, g, -, hgf, hfg⟩ := hf
  exact ⟨LeftInverse.injective hgf, fun y => ⟨g y, hfg y⟩⟩

/-- Being a self-diffeomorphism only depends on the underlying function. -/
theorem congr {f g : E → E} (hf : IsDiffeoSelf f) (h : ∀ x, g x = f x) : IsDiffeoSelf g := by
  have hfg : g = f := funext h
  rw [hfg]; exact hf

/-- The composite of two self-diffeomorphisms is a self-diffeomorphism. -/
theorem comp {f g : E → E} (hf : IsDiffeoSelf f) (hg : IsDiffeoSelf g) :
    IsDiffeoSelf fun x => f (g x) := by
  obtain ⟨hfs, f', hf's, hf'f, hff'⟩ := hf
  obtain ⟨hgs, g', hg's, hg'g, hgg'⟩ := hg
  exact ⟨hfs.comp hgs, fun y => g' (f' y), hg's.comp hf's,
    fun x => by simp only [hf'f, hg'g], fun y => by simp only [hgg', hff']⟩

/-- **The derivative of a self-diffeomorphism at any point is a linear automorphism.**  This is
the chain rule applied to `g ∘ f = id` and `f ∘ g = id`. -/
theorem bijective_fderiv {f : E → E} (hf : IsDiffeoSelf f) (x : E) :
    Bijective (fderiv ℝ f x) := by
  obtain ⟨hfs, g, hgs, hgf, hfg⟩ := hf
  have hdf : ∀ y, HasFDerivAt f (fderiv ℝ f y) y := fun y =>
    (hfs.differentiable (by simp) y).hasFDerivAt
  have hdg : ∀ y, HasFDerivAt g (fderiv ℝ g y) y := fun y =>
    (hgs.differentiable (by simp) y).hasFDerivAt
  have h1 : (fderiv ℝ g (f x)).comp (fderiv ℝ f x) = ContinuousLinearMap.id ℝ E := by
    have hc := (hdg (f x)).comp x (hdf x)
    rw [show g ∘ f = id from funext hgf] at hc
    exact hc.unique (hasFDerivAt_id x)
  have h2 : (fderiv ℝ f x).comp (fderiv ℝ g (f x)) = ContinuousLinearMap.id ℝ E := by
    have hc := (hdf (g (f x))).comp (f x) (hdg (f x))
    rw [show f ∘ g = id from funext hfg] at hc
    have h3 := hc.unique (hasFDerivAt_id (f x))
    rwa [hgf x] at h3
  have e1 : ∀ a, fderiv ℝ g (f x) (fderiv ℝ f x a) = a := fun a => by
    simpa using ContinuousLinearMap.ext_iff.1 h1 a
  have e2 : ∀ a, fderiv ℝ f x (fderiv ℝ g (f x) a) = a := fun a => by
    simpa using ContinuousLinearMap.ext_iff.1 h2 a
  exact ⟨fun a b hab => by rw [← e1 a, ← e1 b, hab], fun y => ⟨fderiv ℝ g (f x) y, e2 y⟩⟩

end IsDiffeoSelf

/-- The identity is a self-diffeomorphism. -/
theorem isDiffeoSelf_id : IsDiffeoSelf (id : E → E) :=
  ⟨contDiff_id, id, contDiff_id, fun _ => rfl, fun _ => rfl⟩

/-- A translation is a self-diffeomorphism. -/
theorem isDiffeoSelf_sub_const (c : E) : IsDiffeoSelf fun x : E => x - c :=
  ⟨contDiff_id.sub contDiff_const, fun x => x + c, contDiff_id.add contDiff_const,
    fun x => by simp, fun x => by simp⟩

/-- A nonzero scaling is a self-diffeomorphism. -/
theorem isDiffeoSelf_smul {c : ℝ} (hc : c ≠ 0) : IsDiffeoSelf fun x : E => c • x :=
  ⟨contDiff_const.smul contDiff_id, fun x => c⁻¹ • x, contDiff_const.smul contDiff_id,
    fun x => by simp only [smul_smul, inv_mul_cancel₀ hc, one_smul],
    fun x => by simp only [smul_smul, mul_inv_cancel₀ hc, one_smul]⟩

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- A bijective linear self-map of a finite-dimensional space is a self-diffeomorphism: both it
and its inverse are linear, hence continuous, hence smooth. -/
theorem isDiffeoSelf_of_isLinearMap {f : E → E} (hlin : IsLinearMap ℝ f) (hbij : Bijective f) :
    IsDiffeoSelf f := by
  have hLf : IsDiffeoSelf fun x => IsLinearMap.mk' f hlin x := by
    refine ⟨(IsLinearMap.mk' f hlin).toContinuousLinearMap.contDiff,
      fun y => (LinearEquiv.ofBijective (IsLinearMap.mk' f hlin) hbij).symm y, ?_, ?_, ?_⟩
    · exact ((LinearEquiv.ofBijective (IsLinearMap.mk' f hlin)
        hbij).symm.toContinuousLinearEquiv).contDiff
    · intro x
      exact (LinearEquiv.ofBijective (IsLinearMap.mk' f hlin) hbij).symm_apply_apply x
    · intro y
      exact (LinearEquiv.ofBijective (IsLinearMap.mk' f hlin) hbij).apply_symm_apply y
  exact hLf.congr fun x => rfl

/-- A bijective continuous linear self-map of a finite-dimensional space is a
self-diffeomorphism. -/
theorem isDiffeoSelf_clm {L : E →L[ℝ] E} (hbij : Bijective L) : IsDiffeoSelf fun x => L x :=
  isDiffeoSelf_of_isLinearMap ⟨fun x y => L.map_add x y, fun c x => L.map_smul c x⟩ hbij

/-- **The sign of the Jacobian determinant of a self-diffeomorphism of `E` is the same at every
point.**  This is `Milnor.sgn_det_fderiv_eq` applied to the closed ball centred at `y` through
`x`; the whole space is open, and the derivative is everywhere invertible by
`Milnor.IsDiffeoSelf.bijective_fderiv`.  It is why Milnor's hypothesis "orientation preserving"
may be tested at a single point, for instance the origin. -/
theorem IsDiffeoSelf.sgn_det_fderiv_const {f : E → E} (hf : IsDiffeoSelf f) (x y : E) :
    sgn (LinearMap.det (fderiv ℝ f x : E →ₗ[ℝ] E))
      = sgn (LinearMap.det (fderiv ℝ f y : E →ₗ[ℝ] E)) :=
  sgn_det_fderiv_eq (z := y) (r := dist x y) isOpen_univ hf.contDiff.contDiffOn
    (fun z _ => hf.bijective_fderiv z) (subset_univ _) (mem_closedBall.2 le_rfl)

/-- Two reals with the same sign are simultaneously positive. -/
private theorem pos_of_sgn_eq {a b : ℝ} (h : sgn a = sgn b) (hb : 0 < b) : 0 < a := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rw [sgn_neg ha, sgn_pos hb] at h; norm_num at h
  · rw [ha, sgn_zero, sgn_pos hb] at h; norm_num at h
  · exact ha

/-- **For a self-diffeomorphism of `E` the Jacobian determinant is positive at one point exactly
when it is positive at every point**: Milnor's "orientation preserving". -/
theorem IsDiffeoSelf.det_fderiv_pos_iff {f : E → E} (hf : IsDiffeoSelf f) (x y : E) :
    0 < LinearMap.det (fderiv ℝ f x : E →ₗ[ℝ] E) ↔
      0 < LinearMap.det (fderiv ℝ f y : E →ₗ[ℝ] E) :=
  ⟨fun h => pos_of_sgn_eq (hf.sgn_det_fderiv_const y x) h,
    fun h => pos_of_sgn_eq (hf.sgn_det_fderiv_const x y) h⟩

end FiniteDimensional

/-! ### Smooth isotopy of self-diffeomorphisms -/

/-- **`f` and `g` are smoothly isotopic**: there is a smooth `H : E × ℝ → E` with `H (·, 0) = f`,
`H (·, 1) = g`, and *every* time slice `H (·, t)` a diffeomorphism of `E`.  This is the shape used
for `Milnor.Isotopic` in `Milnor.Chapter4.Homogeneity`. -/
def SmoothIsotopicMap (f g : E → E) : Prop :=
  ∃ H : E × ℝ → E, ContDiff ℝ ∞ H ∧ (∀ x, H (x, 0) = f x) ∧ (∀ x, H (x, 1) = g x) ∧
    ∀ t : ℝ, IsDiffeoSelf fun x => H (x, t)

namespace SmoothIsotopicMap

/-- The left end of an isotopy is a diffeomorphism. -/
theorem isDiffeoSelf_left {f g : E → E} (h : SmoothIsotopicMap f g) : IsDiffeoSelf f := by
  obtain ⟨H, -, h0, -, hs⟩ := h
  exact (hs 0).congr fun x => (h0 x).symm

/-- The right end of an isotopy is a diffeomorphism. -/
theorem isDiffeoSelf_right {f g : E → E} (h : SmoothIsotopicMap f g) : IsDiffeoSelf g := by
  obtain ⟨H, -, -, h1, hs⟩ := h
  exact (hs 1).congr fun x => (h1 x).symm

/-- **Reflexivity**: a diffeomorphism is isotopic to itself, by the constant isotopy. -/
theorem refl {f : E → E} (hf : IsDiffeoSelf f) : SmoothIsotopicMap f f :=
  ⟨fun q => f q.1, hf.contDiff.comp contDiff_fst, fun _ => rfl, fun _ => rfl,
    fun _ => hf.congr fun _ => rfl⟩

/-- **Symmetry**: run the isotopy backwards, `t ↦ 1 - t`. -/
theorem symm {f g : E → E} (h : SmoothIsotopicMap f g) : SmoothIsotopicMap g f := by
  obtain ⟨H, hH, h0, h1, hs⟩ := h
  refine ⟨fun q => H (q.1, 1 - q.2),
    hH.comp (contDiff_fst.prodMk (contDiff_const.sub contDiff_snd)), ?_, ?_, ?_⟩
  · intro x; change H (x, 1 - (0 : ℝ)) = g x; rw [sub_zero]; exact h1 x
  · intro x; change H (x, 1 - (1 : ℝ)) = f x; rw [sub_self]; exact h0 x
  · intro t; exact (hs (1 - t)).congr fun x => rfl

/-- **Transitivity**.  Each of the two isotopies is first reparametrised by
`Real.smoothTransition` so that it is *constant in `t`* on a neighbourhood of the join `t = 1/2`:
the first one becomes constant for `t ≥ 1/4`, the second one for `t ≤ 3/4`.  The glued map then
agrees with the (smooth) reparametrised first isotopy on the open half-line `t < 3/4` and with the
(smooth) reparametrised second isotopy on the open half-line `t > 1/4`; these two half-lines cover
`ℝ`, and smoothness is local, so the glued map is smooth. -/
theorem trans {f g h : E → E} (h₁ : SmoothIsotopicMap f g) (h₂ : SmoothIsotopicMap g h) :
    SmoothIsotopicMap f h := by
  classical
  obtain ⟨H₁, hH₁, hH₁0, hH₁1, hs₁⟩ := h₁
  obtain ⟨H₂, hH₂, hH₂0, hH₂1, hs₂⟩ := h₂
  -- the reparametrisations and their plateaux
  have hσ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hρ₁s : ContDiff ℝ ∞ fun t : ℝ => Real.smoothTransition (4 * t) :=
    hσ.comp (contDiff_const.mul contDiff_id)
  have hρ₂s : ContDiff ℝ ∞ fun t : ℝ => Real.smoothTransition (4 * t - 3) :=
    hσ.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hρ₁zero : Real.smoothTransition (4 * (0 : ℝ)) = 0 := by
    rw [mul_zero]; exact Real.smoothTransition.zero
  have hρ₁one : ∀ t : ℝ, 1 / 4 ≤ t → Real.smoothTransition (4 * t) = 1 := fun t ht =>
    Real.smoothTransition.one_of_one_le (by linarith)
  have hρ₂zero : ∀ t : ℝ, t ≤ 3 / 4 → Real.smoothTransition (4 * t - 3) = 0 := fun t ht =>
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hρ₂one : Real.smoothTransition (4 * (1 : ℝ) - 3) = 1 :=
    Real.smoothTransition.one_of_one_le (by norm_num)
  refine ⟨fun q => if q.2 ≤ 1 / 2 then H₁ (q.1, Real.smoothTransition (4 * q.2))
    else H₂ (q.1, Real.smoothTransition (4 * q.2 - 3)), ?_, ?_, ?_, ?_⟩
  · -- smoothness, by locality
    have hA : ∀ q : E × ℝ, q.2 < 3 / 4 →
        (if q.2 ≤ 1 / 2 then H₁ (q.1, Real.smoothTransition (4 * q.2))
          else H₂ (q.1, Real.smoothTransition (4 * q.2 - 3)))
          = H₁ (q.1, Real.smoothTransition (4 * q.2)) := by
      intro q hq
      by_cases h' : q.2 ≤ 1 / 2
      · rw [if_pos h']
      · have h'' : 1 / 2 < q.2 := not_le.1 h'
        rw [if_neg h', hρ₂zero q.2 hq.le, hH₂0, hρ₁one q.2 (by linarith), hH₁1]
    have hB : ∀ q : E × ℝ, 1 / 4 < q.2 →
        (if q.2 ≤ 1 / 2 then H₁ (q.1, Real.smoothTransition (4 * q.2))
          else H₂ (q.1, Real.smoothTransition (4 * q.2 - 3)))
          = H₂ (q.1, Real.smoothTransition (4 * q.2 - 3)) := by
      intro q hq
      by_cases h' : q.2 ≤ 1 / 2
      · rw [if_pos h', hρ₁one q.2 hq.le, hH₁1, hρ₂zero q.2 (by linarith), hH₂0]
      · rw [if_neg h']
    have hsm₁ : ContDiff ℝ ∞ fun q : E × ℝ => H₁ (q.1, Real.smoothTransition (4 * q.2)) :=
      hH₁.comp (contDiff_fst.prodMk (hρ₁s.comp contDiff_snd))
    have hsm₂ : ContDiff ℝ ∞ fun q : E × ℝ => H₂ (q.1, Real.smoothTransition (4 * q.2 - 3)) :=
      hH₂.comp (contDiff_fst.prodMk (hρ₂s.comp contDiff_snd))
    rw [contDiff_iff_contDiffAt]
    intro q
    rcases le_or_gt q.2 (1 / 2 : ℝ) with hq | hq
    · have hopen : IsOpen {r : E × ℝ | r.2 < 3 / 4} := isOpen_lt continuous_snd continuous_const
      have hmem : q ∈ {r : E × ℝ | r.2 < 3 / 4} := show q.2 < 3 / 4 by linarith
      exact hsm₁.contDiffAt.congr_of_eventuallyEq
        (by filter_upwards [hopen.mem_nhds hmem] with r hr using hA r hr)
    · have hopen : IsOpen {r : E × ℝ | 1 / 4 < r.2} := isOpen_lt continuous_const continuous_snd
      have hmem : q ∈ {r : E × ℝ | 1 / 4 < r.2} := show 1 / 4 < q.2 by linarith
      exact hsm₂.contDiffAt.congr_of_eventuallyEq
        (by filter_upwards [hopen.mem_nhds hmem] with r hr using hB r hr)
  · intro x
    change (if (0 : ℝ) ≤ 1 / 2 then H₁ (x, Real.smoothTransition (4 * (0 : ℝ)))
      else H₂ (x, Real.smoothTransition (4 * (0 : ℝ) - 3))) = f x
    rw [if_pos (by norm_num : (0 : ℝ) ≤ 1 / 2), hρ₁zero]
    exact hH₁0 x
  · intro x
    change (if (1 : ℝ) ≤ 1 / 2 then H₁ (x, Real.smoothTransition (4 * (1 : ℝ)))
      else H₂ (x, Real.smoothTransition (4 * (1 : ℝ) - 3))) = h x
    rw [if_neg (by norm_num : ¬ (1 : ℝ) ≤ 1 / 2), hρ₂one]
    exact hH₂1 x
  · intro t
    by_cases ht : t ≤ 1 / 2
    · refine (hs₁ (Real.smoothTransition (4 * t))).congr fun x => ?_
      change (if t ≤ 1 / 2 then H₁ (x, Real.smoothTransition (4 * t))
        else H₂ (x, Real.smoothTransition (4 * t - 3)))
          = H₁ (x, Real.smoothTransition (4 * t))
      rw [if_pos ht]
    · refine (hs₂ (Real.smoothTransition (4 * t - 3))).congr fun x => ?_
      change (if t ≤ 1 / 2 then H₁ (x, Real.smoothTransition (4 * t))
        else H₂ (x, Real.smoothTransition (4 * t - 3)))
          = H₂ (x, Real.smoothTransition (4 * t - 3))
      rw [if_neg ht]

end SmoothIsotopicMap

/-! ### Step 1: translating the image of the origin back to the origin -/

/-- **Step 1 of Milnor's proof** (§6, Lemma 2, p. 33): a diffeomorphism `f` of `E` is smoothly
isotopic to the diffeomorphism `x ↦ f x - f 0`, which fixes the origin.  The isotopy is
`H (x, t) = f x - t · f 0`; every slice is `f` followed by a translation, hence a
diffeomorphism. -/
theorem smoothIsotopicMap_sub_apply_zero {f : E → E} (hf : IsDiffeoSelf f) :
    SmoothIsotopicMap f fun x => f x - f 0 := by
  refine ⟨fun q => f q.1 - q.2 • f 0,
    (hf.contDiff.comp contDiff_fst).sub (contDiff_snd.smul contDiff_const), ?_, ?_, ?_⟩
  · intro x; change f x - (0 : ℝ) • f 0 = f x; rw [zero_smul, sub_zero]
  · intro x; change f x - (1 : ℝ) • f 0 = f x - f 0; rw [one_smul]
  · intro t; exact ((isDiffeoSelf_sub_const (t • f 0)).comp hf).congr fun x => rfl

/-! ### Step 2: a diffeomorphism fixing the origin is isotopic to its derivative there -/

/-- **Step 2 of Milnor's proof** (§6, Lemma 2, p. 33): a diffeomorphism `g` of `E` with `g 0 = 0`
is smoothly isotopic to its derivative `d g₀` at the origin, by Milnor's isotopy

`H (x, t) = g (t x) / t` for `t ≠ 0`,   `H (x, 0) = d g₀ (x)`.

Smoothness of `H`, including at `t = 0`, is Hadamard's lemma (`Milnor.contDiff_ite_smul_inv`).
Each slice with `t ≠ 0` is the scaling by `t`, followed by `g`, followed by the scaling by `t⁻¹`,
hence a diffeomorphism; the slice at `t = 0` is `d g₀`, a linear automorphism because `g` is a
diffeomorphism (`Milnor.IsDiffeoSelf.bijective_fderiv`). -/
theorem smoothIsotopicMap_fderiv [FiniteDimensional ℝ E] {g : E → E} (hg : IsDiffeoSelf g)
    (hg0 : g 0 = 0) : SmoothIsotopicMap (fun x => fderiv ℝ g 0 x) g := by
  classical
  refine ⟨fun q => if q.2 = 0 then fderiv ℝ g 0 q.1 else q.2⁻¹ • g (q.2 • q.1),
    contDiff_ite_smul_inv hg.contDiff hg0, ?_, ?_, ?_⟩
  · intro x
    change (if (0 : ℝ) = 0 then fderiv ℝ g 0 x else (0 : ℝ)⁻¹ • g ((0 : ℝ) • x))
      = fderiv ℝ g 0 x
    rw [if_pos rfl]
  · intro x
    change (if (1 : ℝ) = 0 then fderiv ℝ g 0 x else (1 : ℝ)⁻¹ • g ((1 : ℝ) • x)) = g x
    rw [if_neg one_ne_zero, inv_one, one_smul, one_smul]
  · intro t
    by_cases ht : t = 0
    · subst ht
      refine (isDiffeoSelf_clm (hg.bijective_fderiv 0)).congr fun x => ?_
      change (if (0 : ℝ) = 0 then fderiv ℝ g 0 x else (0 : ℝ)⁻¹ • g ((0 : ℝ) • x))
        = fderiv ℝ g 0 x
      rw [if_pos rfl]
    · refine (((isDiffeoSelf_smul (inv_ne_zero ht)).comp hg).comp
        (isDiffeoSelf_smul ht)).congr fun x => ?_
      change (if t = 0 then fderiv ℝ g 0 x else t⁻¹ • g (t • x)) = t⁻¹ • g (t • x)
      rw [if_neg ht]

/-! ### Step 3: a linear automorphism of positive determinant is isotopic to the identity -/

variable {p : ℕ}

/-- The self-map of `E` which, read in the coordinates of a basis `b`, is multiplication by the
matrix `N`. -/
def matrixAct (b : Basis (Fin p) ℝ E) (N : Matrix (Fin p) (Fin p) ℝ) (x : E) : E :=
  b.equivFunL.symm (N *ᵥ b.equivFunL x)

/-- The identity matrix acts as the identity. -/
@[simp] theorem matrixAct_one (b : Basis (Fin p) ℝ E) (x : E) : matrixAct b 1 x = x := by
  simp [matrixAct, Matrix.one_mulVec]

/-- The action of matrices is multiplicative. -/
theorem matrixAct_mul (b : Basis (Fin p) ℝ E) (N N' : Matrix (Fin p) (Fin p) ℝ) (x : E) :
    matrixAct b N (matrixAct b N' x) = matrixAct b (N * N') x := by
  simp [matrixAct, Matrix.mulVec_mulVec]

/-- `matrixAct b (LinearMap.toMatrix b b A)` is `A`: the matrix of a linear map acts as the map. -/
theorem matrixAct_toMatrix (b : Basis (Fin p) ℝ E) (A : E →ₗ[ℝ] E) (x : E) :
    matrixAct b (LinearMap.toMatrix b b A) x = A x := by
  have e1 : ∀ y : E, ((b.equivFunL y : Fin p → ℝ)) = ⇑(b.repr y) :=
    fun y => funext (b.equivFunL_apply y)
  simp only [matrixAct, e1, LinearMap.toMatrix_mulVec_repr]
  exact b.equivFunL.symm_apply_apply (A x)

/-- Smoothness of `y ↦ matrixAct b (N y) (u y)` for a smooth family `N` of matrices (smoothness
meant entrywise) and a smooth `u`. -/
theorem contDiff_matrixAct_comp (b : Basis (Fin p) ℝ E) {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {N : X → Matrix (Fin p) (Fin p) ℝ}
    (hN : ∀ i j, ContDiff ℝ ∞ fun y => N y i j) {u : X → E} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ fun y => matrixAct b (N y) (u y) := by
  have hε : ContDiff ℝ ∞ fun x : E => b.equivFunL x := b.equivFunL.contDiff
  have h1 : ContDiff ℝ ∞ fun y : X => N y *ᵥ b.equivFunL (u y) := by
    rw [contDiff_pi]
    intro i
    simp only [Matrix.mulVec, dotProduct]
    exact ContDiff.sum fun j _ => (hN i j).mul (contDiff_pi.1 (hε.comp hu) j)
  exact b.equivFunL.symm.contDiff.comp h1

/-- The action of a single matrix is smooth, being linear and continuous. -/
theorem contDiff_matrixAct (b : Basis (Fin p) ℝ E) (N : Matrix (Fin p) (Fin p) ℝ) :
    ContDiff ℝ ∞ (matrixAct b N) :=
  contDiff_matrixAct_comp b (N := fun _ : E => N) (fun _ _ => contDiff_const) contDiff_id

/-- If `N` is invertible then `matrixAct b N` is a self-diffeomorphism, with inverse
`matrixAct b N⁻¹`. -/
theorem isDiffeoSelf_matrixAct (b : Basis (Fin p) ℝ E) {N : Matrix (Fin p) (Fin p) ℝ}
    (hN : IsUnit N.det) : IsDiffeoSelf (matrixAct b N) := by
  refine ⟨contDiff_matrixAct b N, matrixAct b N⁻¹, contDiff_matrixAct b N⁻¹, ?_, ?_⟩
  · intro x; rw [matrixAct_mul, Matrix.nonsing_inv_mul N hN, matrixAct_one]
  · intro x; rw [matrixAct_mul, Matrix.mul_nonsing_inv N hN, matrixAct_one]

/-- **Step 3 of Milnor's proof** (§6, Lemma 2, p. 33): a linear automorphism `A` of `E` with
positive determinant is smoothly isotopic to the identity.

The matrix of `A` in the basis `Module.finBasis ℝ E` is fed to `Milnor.GLp.exists_glPath`, which
gives a path `G` of matrices with smooth entries from that matrix to `1` whose determinant is
positive on `[0, 1]`.  The time is reparametrised by `Real.smoothTransition`, whose values lie in
`[0, 1]`, so that *every* slice has positive determinant and hence is a diffeomorphism. -/
theorem smoothIsotopicMap_id_of_det_pos [FiniteDimensional ℝ E] {A : E →L[ℝ] E}
    (hA : 0 < LinearMap.det (A : E →ₗ[ℝ] E)) : SmoothIsotopicMap (fun x => A x) id := by
  set b : Basis (Fin (finrank ℝ E)) ℝ E := Module.finBasis ℝ E with hb
  obtain ⟨G, hGs, hG0, hG1, hGdet⟩ := GLp.exists_glPath (LinearMap.toMatrix b b (A : E →ₗ[ℝ] E))
    (by rw [LinearMap.det_toMatrix]; exact hA)
  refine ⟨fun q => matrixAct b (G (Real.smoothTransition q.2)) q.1, ?_, ?_, ?_, ?_⟩
  · exact contDiff_matrixAct_comp b
      (fun i j => (hGs i j).comp (Real.smoothTransition.contDiff.comp contDiff_snd)) contDiff_fst
  · intro x
    change matrixAct b (G (Real.smoothTransition (0 : ℝ))) x = (A : E →ₗ[ℝ] E) x
    rw [Real.smoothTransition.zero, hG0, matrixAct_toMatrix]
  · intro x
    change matrixAct b (G (Real.smoothTransition (1 : ℝ))) x = x
    rw [Real.smoothTransition.one, hG1, matrixAct_one]
  · intro t
    refine (isDiffeoSelf_matrixAct b (isUnit_iff_ne_zero.2
      (hGdet (Real.smoothTransition t) (Real.smoothTransition.nonneg t)
        (Real.smoothTransition.le_one t)).ne')).congr fun x => rfl

/-! ### Milnor's Lemma 2 -/

/-- **Milnor's Lemma 2 of §6** (p. 33): a diffeomorphism `f` of a finite-dimensional real normed
space `E` whose derivative at the origin has positive determinant is smoothly isotopic to the
identity.

The three steps are chained: `f` is isotopic to `g : x ↦ f x - f 0`
(`Milnor.smoothIsotopicMap_sub_apply_zero`), which fixes the origin and has the same derivative
there; `g` is isotopic to `d g₀` (`Milnor.smoothIsotopicMap_fderiv`); and `d g₀`, having positive
determinant, is isotopic to the identity (`Milnor.smoothIsotopicMap_id_of_det_pos`). -/
theorem smoothIsotopicMap_id [FiniteDimensional ℝ E] {f : E → E} (hf : IsDiffeoSelf f)
    (hdet : 0 < LinearMap.det (fderiv ℝ f 0 : E →ₗ[ℝ] E)) : SmoothIsotopicMap f id := by
  have hgd : IsDiffeoSelf fun x => f x - f 0 := (isDiffeoSelf_sub_const (f 0)).comp hf
  have hg0 : (fun x => f x - f 0) 0 = 0 := sub_self (f 0)
  have hgf : fderiv ℝ (fun x => f x - f 0) 0 = fderiv ℝ f 0 := fderiv_sub_const (f 0)
  have h1 : SmoothIsotopicMap f fun x => f x - f 0 := smoothIsotopicMap_sub_apply_zero hf
  have h2 : SmoothIsotopicMap (fun x => f x - f 0)
      fun x => fderiv ℝ (fun y => f y - f 0) 0 x := (smoothIsotopicMap_fderiv hgd hg0).symm
  have h3 : SmoothIsotopicMap (fun x => fderiv ℝ (fun y => f y - f 0) 0 x) id := by
    refine smoothIsotopicMap_id_of_det_pos ?_
    rw [hgf]; exact hdet
  exact (h1.trans h2).trans h3

/-- **Milnor's Lemma 2 of §6** (p. 33) with the orientation hypothesis tested at an arbitrary
point: this is legitimate because the sign of the Jacobian determinant of a diffeomorphism of `E`
is the same at every point (`Milnor.IsDiffeoSelf.det_fderiv_pos_iff`). -/
theorem smoothIsotopicMap_id_of_det_pos_at [FiniteDimensional ℝ E] {f : E → E}
    (hf : IsDiffeoSelf f) (x₀ : E)
    (hdet : 0 < LinearMap.det (fderiv ℝ f x₀ : E →ₗ[ℝ] E)) : SmoothIsotopicMap f id :=
  smoothIsotopicMap_id hf ((hf.det_fderiv_pos_iff x₀ 0).1 hdet)

/-- **Milnor's Lemma 2 of §6** (p. 33) in Milnor's own setting: *any orientation preserving
diffeomorphism of `ℝᵐ` is smoothly isotopic to the identity.*  "Orientation preserving" is the
positivity of the Jacobian determinant at one (equivalently, by
`Milnor.IsDiffeoSelf.det_fderiv_pos_iff`, at every) point. -/
theorem lemma2_of_sec6 {m : ℕ} {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    (hf : IsDiffeoSelf f) (x₀ : EuclideanSpace ℝ (Fin m))
    (hdet : 0 < LinearMap.det
      (fderiv ℝ f x₀ : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) :
    SmoothIsotopicMap f id :=
  smoothIsotopicMap_id_of_det_pos_at hf x₀ hdet

end Milnor
