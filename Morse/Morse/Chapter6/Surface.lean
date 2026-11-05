import Morse.Chapter6.Parallel

/-!
Milnor, *Morse Theory*, §8, pp. 49–50 (Lemma 8.7) and §9, p. 52 (Lemma 9.2): parametrized
surfaces in a submanifold `N ⊆ ℝᴷ` with the induced metric.

# Covariant derivatives along parametrized surfaces

## Milnor's text, paraphrased

* A *parametrized surface* is a smooth map `s : ℝ² → M`; a *vector field along `s`* assigns to
  each `(x, y)` a vector `V_{(x,y)} ∈ TM_{s(x,y)}`.  The *velocity fields* are
  `∂s/∂x = s_*(∂/∂x)` and `∂s/∂y`.  For each fixed `y₀`, `V` restricts to a field along the curve
  `x ↦ s(x, y₀)`, whose covariant derivative defines `DV/∂x` at `(x, y₀)`; likewise `DV/∂y`
  (p. 49).
* **Lemma 8.7** (p. 50): for a symmetric connection, `(D/∂x)(∂s/∂y) = (D/∂y)(∂s/∂x)`.  ("Express
  both sides in terms of a local coordinate system, and compute.")
* **Lemma 9.2** (p. 52): `(D/∂y)(D/∂x)V − (D/∂x)(D/∂y)V = R(∂s/∂x, ∂s/∂y)V`.  (Same proof
  indication, using `∂_j ⊢ (∂_i ⊢ ∂_k) − ∂_i ⊢ (∂_j ⊢ ∂_k) = R(∂_i, ∂_j)∂_k`.)

## In the embedded setting

`s : ℝ × ℝ → N` with `(x, y) ↦ s(x, y) ∈ V` smooth.  `Morse.partialX`, `Morse.partialY` are the
partial derivatives of maps on `ℝ²`; `Morse.velX`, `Morse.velY` the velocity fields;
`Morse.covDerivX hN s W`, `Morse.covDerivY hN s W` are Milnor's `DW/∂x`, `DW/∂y`, defined
literally as covariant derivatives along the coordinate curves (`Morse.covDeriv`), and equal to
`P_{s(p)}(∂W/∂x)`, `P_{s(p)}(∂W/∂y)` (`Morse.covDerivX_eq`, `Morse.covDerivY_eq`).

* `Morse.covDerivX_velY`: **Lemma 8.7**, `(D/∂x)(∂s/∂y) = (D/∂y)(∂s/∂x)`: both are
  `P(∂²s/∂x∂y)`.
* `Morse.covDerivY_covDerivX_sub`: **Lemma 9.2**,
  `(D/∂y)(D/∂x)V − (D/∂x)(D/∂y)V = R(∂s/∂x, ∂s/∂y)V`, with `R` the curvature `Morse.curvOp` of
  `Morse/Chapter6/Submanifold.lean`, i.e. `R(x, y) = D_y D_x − D_x D_y`.

## What Milnor leaves implicit

* That `DV/∂x` is smooth in `(x, y)` jointly (needed to apply `D/∂y` to it): Milnor defines it one
  curve at a time.  Here it is `P_{s(p)}(∂V/∂x)`, visibly smooth.
* The computations behind "express both sides in terms of a local coordinate system, and compute":
  for Lemma 8.7, the symmetry of the second derivatives of `s`; for Lemma 9.2, in the embedded
  setting, the identity `P(D_y(∂V/∂x)) = D_y D_x V` for tangent `V` (from `V = PV`, `P D P = 0`
  and the fact that `D_y` maps normal vectors to tangent ones), and the symmetry of the second
  derivatives of `V`.  Lemma 9.2 needs no symmetry of the connection; in the embedded setting this
  shows up as the absence of any use of `Morse.secondFundForm_comm`.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

/-! ### Partial derivatives on `ℝ²` -/

section Partial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The partial derivative `∂F/∂x` of a map on `ℝ²`. -/
def partialX (F : ℝ × ℝ → E) (p : ℝ × ℝ) : E := fderiv ℝ F p (1, 0)

/-- The partial derivative `∂F/∂y` of a map on `ℝ²`. -/
def partialY (F : ℝ × ℝ → E) (p : ℝ × ℝ) : E := fderiv ℝ F p (0, 1)

/-- `∂F/∂x` is the derivative along the horizontal line through `p`. -/
theorem hasDerivAt_partialX {F : ℝ × ℝ → E} {p : ℝ × ℝ} (hF : DifferentiableAt ℝ F p) :
    HasDerivAt (fun x => F (x, p.2)) (partialX F p) p.1 :=
  hF.hasFDerivAt.comp_hasDerivAt (f := fun x => (x, p.2)) p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))

/-- `∂F/∂y` is the derivative along the vertical line through `p`. -/
theorem hasDerivAt_partialY {F : ℝ × ℝ → E} {p : ℝ × ℝ} (hF : DifferentiableAt ℝ F p) :
    HasDerivAt (fun y => F (p.1, y)) (partialY F p) p.2 :=
  hF.hasFDerivAt.comp_hasDerivAt (f := fun y => (p.1, y)) p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))

theorem contDiff_partialX {F : ℝ × ℝ → E} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (partialX F) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem contDiff_partialY {F : ℝ × ℝ → E} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (partialY F) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- The mixed partial derivatives in terms of the second derivative. -/
theorem partialY_partialX_eq {F : ℝ × ℝ → E} (hF : ContDiff ℝ ∞ F) (p : ℝ × ℝ) :
    partialY (partialX F) p = fderiv ℝ (fderiv ℝ F) p (0, 1) (1, 0) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    ((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) p
  change fderiv ℝ (fun q => fderiv ℝ F q ((fun _ => ((1 : ℝ), (0 : ℝ))) q)) p (0, 1) = _
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

theorem partialX_partialY_eq {F : ℝ × ℝ → E} (hF : ContDiff ℝ ∞ F) (p : ℝ × ℝ) :
    partialX (partialY F) p = fderiv ℝ (fderiv ℝ F) p (1, 0) (0, 1) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    ((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) p
  change fderiv ℝ (fun q => fderiv ℝ F q ((fun _ => ((0 : ℝ), (1 : ℝ))) q)) p (1, 0) = _
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

/-- **Symmetry of mixed partial derivatives** (Schwarz). -/
theorem partialY_partialX {F : ℝ × ℝ → E} (hF : ContDiff ℝ ∞ F) (p : ℝ × ℝ) :
    partialY (partialX F) p = partialX (partialY F) p := by
  rw [partialY_partialX_eq hF, partialX_partialY_eq hF]
  exact (hF.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)) _ _

/-- The product rule for `∂/∂x` of an operator-valued map applied to a vector-valued one. -/
theorem partialX_clm_apply {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {A : ℝ × ℝ → E →L[ℝ] E'} {F : ℝ × ℝ → E} {p : ℝ × ℝ} (hA : DifferentiableAt ℝ A p)
    (hF : DifferentiableAt ℝ F p) :
    partialX (fun q => A q (F q)) p = partialX A p (F p) + A p (partialX F p) := by
  rw [partialX, fderiv_clm_apply hA hF, partialX, partialX]
  simp [add_comm]

theorem partialY_clm_apply {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {A : ℝ × ℝ → E →L[ℝ] E'} {F : ℝ × ℝ → E} {p : ℝ × ℝ} (hA : DifferentiableAt ℝ A p)
    (hF : DifferentiableAt ℝ F p) :
    partialY (fun q => A q (F q)) p = partialY A p (F p) + A p (partialY F p) := by
  rw [partialY, fderiv_clm_apply hA hF, partialY, partialY]
  simp [add_comm]

end Partial

/-! ### Parametrized surfaces in `N` -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

variable {s : ℝ × ℝ → N}

/-- The velocity field `∂s/∂x = s_*(∂/∂x)` of a parametrized surface (Milnor p. 49). -/
def velX (s : ℝ × ℝ → N) (p : ℝ × ℝ) : V := partialX (fun q => (s q : V)) p

/-- The velocity field `∂s/∂y = s_*(∂/∂y)` of a parametrized surface (Milnor p. 49). -/
def velY (s : ℝ × ℝ → N) (p : ℝ × ℝ) : V := partialY (fun q => (s q : V)) p

/-- **`DW/∂x` along a parametrized surface** (Milnor p. 49): at `(x, y₀)`, the covariant
derivative of `x ↦ W(x, y₀)` along the curve `x ↦ s(x, y₀)`. -/
def covDerivX (s : ℝ × ℝ → N) (W' : ℝ × ℝ → V) (p : ℝ × ℝ) : V :=
  covDeriv hN (fun x => s (x, p.2)) (fun x => W' (x, p.2)) p.1

/-- **`DW/∂y` along a parametrized surface** (Milnor p. 49). -/
def covDerivY (s : ℝ × ℝ → N) (W' : ℝ × ℝ → V) (p : ℝ × ℝ) : V :=
  covDeriv hN (fun y => s (p.1, y)) (fun y => W' (p.1, y)) p.2

omit [FiniteDimensional ℝ Z] in
theorem covDerivX_eq {W' : ℝ × ℝ → V} {p : ℝ × ℝ} (hW : DifferentiableAt ℝ W' p) :
    covDerivX hN s W' p = tanProj hN (s p) (partialX W' p) := by
  rw [covDerivX, covDeriv, (hasDerivAt_partialX hW).deriv]

omit [FiniteDimensional ℝ Z] in
theorem covDerivY_eq {W' : ℝ × ℝ → V} {p : ℝ × ℝ} (hW : DifferentiableAt ℝ W' p) :
    covDerivY hN s W' p = tanProj hN (s p) (partialY W' p) := by
  rw [covDerivY, covDeriv, (hasDerivAt_partialY hW).deriv]

variable (hs : ContDiff ℝ ∞ (fun p => (s p : V)))
include hs

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] in
theorem velX_mem (p : ℝ × ℝ) : velX s p ∈ tangentSubspace hN (s p) :=
  fderiv_mem_tangentSubspace hN hs p (1, 0)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] in
theorem velY_mem (p : ℝ × ℝ) : velY s p ∈ tangentSubspace hN (s p) :=
  fderiv_mem_tangentSubspace hN hs p (0, 1)

omit [FiniteDimensional ℝ Z] in
/-- **Lemma 8.7** (p. 50): `(D/∂x)(∂s/∂y) = (D/∂y)(∂s/∂x)`. -/
theorem covDerivX_velY (p : ℝ × ℝ) : covDerivX hN s (velY s) p = covDerivY hN s (velX s) p := by
  change covDerivX hN s (partialY fun q => (s q : V)) p =
    covDerivY hN s (partialX fun q => (s q : V)) p
  rw [covDerivX_eq hN ((contDiff_partialY hs).differentiable (by simp) p),
    covDerivY_eq hN ((contDiff_partialX hs).differentiable (by simp) p), partialY_partialX hs]

/-- **Lemma 9.2** (p. 52): `(D/∂y)(D/∂x)V − (D/∂x)(D/∂y)V = R(∂s/∂x, ∂s/∂y)V` for a smooth vector
field `V` along the parametrized surface `s`, with Milnor's curvature `R(x, y) = D_y D_x − D_x D_y`
(`Morse.curvature_eq`). -/
theorem covDerivY_covDerivX_sub {W' : ℝ × ℝ → V} (hW : ContDiff ℝ ∞ W')
    (hWT : ∀ p, W' p ∈ tangentSubspace hN (s p)) (p : ℝ × ℝ) :
    covDerivY hN s (covDerivX hN s W') p - covDerivX hN s (covDerivY hN s W') p =
      curvOp hN (s p) (velX s p) (velY s p) (W' p) := by
  let _ := hN.chartedSpace
  set Pr : ℝ × ℝ → V →L[ℝ] V := fun q => tanProj hN (s q) with hPr
  have hPrs : ContDiff ℝ ∞ Pr := contDiff_comp_map hN hs (contMDiff_tanProj hN)
  have hPrd : ∀ q, DifferentiableAt ℝ Pr q := fun q => (hPrs.differentiable (by simp)) q
  have hWd : ∀ q, DifferentiableAt ℝ W' q := fun q => (hW.differentiable (by simp)) q
  -- the partial derivatives of `Pr` are `D_{∂s/∂x}` and `D_{∂s/∂y}`
  have hPr' := hasFDerivAt_comp_map hN hs (mdifferentiableAt_tanProj hN (s p))
  have hPrx : partialX Pr p = dN hN (tanProj hN) (s p) (velX s p) := by
    rw [partialX, hPr'.fderiv]
    rfl
  have hPry : partialY Pr p = dN hN (tanProj hN) (s p) (velY s p) := by
    rw [partialY, hPr'.fderiv]
    rfl
  -- `DW/∂x = Pr (∂W/∂x)` and `DW/∂y = Pr (∂W/∂y)` everywhere
  have hX : covDerivX hN s W' = fun q => Pr q (partialX W' q) :=
    funext fun q => covDerivX_eq hN (hWd q)
  have hY : covDerivY hN s W' = fun q => Pr q (partialY W' q) :=
    funext fun q => covDerivY_eq hN (hWd q)
  have hWx := contDiff_partialX hW
  have hWy := contDiff_partialY hW
  have hXs : ContDiff ℝ ∞ (fun q => Pr q (partialX W' q)) := hPrs.clm_apply hWx
  have hYs : ContDiff ℝ ∞ (fun q => Pr q (partialY W' q)) := hPrs.clm_apply hWy
  -- `W = PrW`, so `∂W/∂x = D_x W + Pr ∂W/∂x`
  have hWPr : W' = fun q => Pr q (W' q) := funext fun q => (tanProj_eq_self hN (hWT q)).symm
  have hWx' : partialX W' p = dN hN (tanProj hN) (s p) (velX s p) (W' p) +
      Pr p (partialX W' p) := by
    conv_lhs => rw [hWPr]
    rw [partialX_clm_apply (hPrd p) (hWd p), hPrx]
  have hWy' : partialY W' p = dN hN (tanProj hN) (s p) (velY s p) (W' p) +
      Pr p (partialY W' p) := by
    conv_lhs => rw [hWPr]
    rw [partialY_clm_apply (hPrd p) (hWd p), hPry]
  have hvx := velX_mem hN hs p
  have hvy := velY_mem hN hs p
  -- `P(D_y(∂W/∂x)) = D_y D_x W` and `P(D_x(∂W/∂y)) = D_x D_y W`
  have key : ∀ a b : V, a ∈ tangentSubspace hN (s p) → b ∈ tangentSubspace hN (s p) →
      ∀ w, w = dN hN (tanProj hN) (s p) a (W' p) + Pr p w →
      Pr p (dN hN (tanProj hN) (s p) b w) =
        dN hN (tanProj hN) (s p) b (dN hN (tanProj hN) (s p) a (W' p)) := by
    intro a b ha hb w hw
    have hn : dN hN (tanProj hN) (s p) a (W' p) ∈ (tangentSubspace hN (s p))ᗮ :=
      dN_tanProj_mem_orthogonal_of_mem hN ha (hWT p)
    conv_lhs => rw [hw]
    rw [map_add, map_add, tanProj_dN_tanProj hN hb, add_zero]
    exact tanProj_eq_self hN (dN_tanProj_mem_of_mem_orthogonal hN hb hn)
  rw [hX, hY, covDerivY_eq hN (hXs.differentiable (by simp) p),
    covDerivX_eq hN (hYs.differentiable (by simp) p),
    partialY_clm_apply (hPrd p) (hWx.differentiable (by simp) p),
    partialX_clm_apply (hPrd p) (hWy.differentiable (by simp) p), hPrx, hPry, map_add, map_add,
    tanProj_tanProj, tanProj_tanProj, partialY_partialX hW,
    key _ _ hvx hvy _ hWx', key _ _ hvy hvx _ hWy', curvOp_apply]
  simp only [secondFundForm]
  abel

end Morse
