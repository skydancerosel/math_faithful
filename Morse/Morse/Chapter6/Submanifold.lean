import Morse.Chapter6.Projection
import Morse.Chapter6.CurvatureAlgebra

/-!
Milnor, *Morse Theory*, §8 (pp. 43–49) and §9 (pp. 51–54), for a submanifold `N ⊆ ℝᴷ` with the
induced metric.

# The Levi-Civita connection, the second fundamental form and the curvature of `N ⊆ ℝᴷ`

## Milnor's text, paraphrased

* **Affine connections** (pp. 43–44).  An affine connection at `p` assigns to `X_p ∈ TM_p` and a
  vector field `Y` a vector `X_p ⊢ Y ∈ TM_p`, bilinear, with
  `X_p ⊢ (fY) = (X_p f) Y_p + f(p) X_p ⊢ Y`.  A global connection is required to satisfy (1):
  `X ⊢ Y` is smooth for smooth `X, Y`; it then satisfies (2) bilinearity, (3) `(fX) ⊢ Y = f(X ⊢ Y)`,
  (4) `X ⊢ (fY) = (Xf)Y + f(X ⊢ Y)`.
* **Corollary 8.4** (p. 48): for a connection compatible with the metric,
  `X_p⟨Y, Y'⟩ = ⟨X_p ⊢ Y, Y'_p⟩ + ⟨Y_p, X_p ⊢ Y'⟩`.  **Definition 8.5**: the connection is
  *symmetric* if `X ⊢ Y − Y ⊢ X = [X, Y]`, where `[X, Y]f = X(Yf) − Y(Xf)`.
* **Lemma 8.6** (p. 48): a Riemannian manifold has one and only one symmetric connection compatible
  with its metric.  Milnor proves uniqueness with the Christoffel identities (p. 49) and says that,
  conversely, one can verify that the connection they define is symmetric and compatible.
* **The curvature tensor** (p. 51): `R(X, Y)Z = −X ⊢ (Y ⊢ Z) + Y ⊢ (X ⊢ Z) + [X, Y] ⊢ Z`
  (footnote: Nomizu's sign is the opposite one).  **Lemma 9.1**: `R(X, Y)Z` at `p` depends only on
  `X_p, Y_p, Z_p`, trilinearly.  **Lemma 9.3** (p. 53): for the Riemannian connection,
  (1) `R(X, Y)Z + R(Y, X)Z = 0`, (2) `R(X, Y)Z + R(Y, Z)X + R(Z, X)Y = 0`,
  (3) `⟨R(X, Y)Z, W⟩ + ⟨R(X, Y)W, Z⟩ = 0`, (4) `⟨R(X, Y)Z, W⟩ = ⟨R(Z, W)X, Y⟩`.

## The embedded setting

`N ⊆ V` is a slice submanifold of a finite-dimensional inner product space (Milnor's `ℝᴷ`) with
the induced metric; see `Morse/Chapter6/Projection.lean` for `P_q = Morse.tanProj hN q`, the
derivative `Morse.dN` along `N`, and the remark on Nash's embedding theorem.  A vector field is a
map `X : N → V` with `X q ∈ T_qN` (`Morse.IsTangentField`), smooth as a map of manifolds.

* `Morse.covAt hN q v Y = P_q(dY_q(v))` is Milnor's `X_p ⊢ Y` and `Morse.leviCivita hN X Y` is
  `X ⊢ Y`.  Milnor's rules: (1) `Morse.contMDiff_leviCivita`, (2) `Morse.leviCivita_add_left`,
  `Morse.leviCivita_add_right`, (3) `Morse.leviCivita_smul_left`, (4)
  `Morse.leviCivita_smul_right`; **Corollary 8.4**: `Morse.dN_inner_eq_covAt`.
* `Morse.secondFundForm hN q v w = D_v w`, `D_v = dN P q v`: **the second fundamental form**.
  For a tangent field `W` and `v ∈ T_qN`, `II_q(v, W_q) = (1 − P_q)(dW_q(v))`
  (`Morse.secondFundForm_eq_sub_tanProj`): the normal part of `dW_q(v)` depends only on `v` and
  `W_q` (tensoriality, `Morse.sub_tanProj_dN_eq_of_eq`).  `II` is normal
  (`Morse.secondFundForm_mem_orthogonal`), **symmetric** (`Morse.secondFundForm_comm`) and
  self-adjoint in its second argument (`Morse.inner_secondFundForm_comm`).
* `Morse.bracket hN X Y = dY(X) − dX(Y)`, the bracket computed in `V`, is **tangent to `N`**
  (`Morse.bracket_mem`: its normal part is `II(X, Y) − II(Y, X) = 0`), and it is Milnor's Poisson
  bracket: `[X, Y]f = X(Yf) − Y(Xf)` (`Morse.dN_bracket`).  Hence **the induced connection is
  symmetric** (`Morse.leviCivita_sub_leviCivita`).
* **Lemma 8.6** in the embedded setting: `Morse.isSymmCompat_leviCivita` (existence: `P(dY(X))` is
  symmetric and compatible), `Morse.IsSymmCompat.two_mul_inner` (the Koszul formula) and
  `Morse.IsSymmCompat.eq_leviCivita` (uniqueness: any symmetric compatible operation agrees with
  `P(dY(X))` on smooth vector fields).  `Morse/Chapter6/Connection.lean` proves the uniqueness for
  Mathlib's `CovariantDerivative` on an abstract Riemannian manifold; the two are parallel, but the
  bridge (the induced connection as a Mathlib `CovariantDerivative` on the tangent bundle of `N`,
  with the induced metric as a `RiemannianBundle`) is not formalized.
* `Morse.curvature hN X Y Z` is Milnor's `R(X, Y)Z`.  **The curvature of `N`**
  (`Morse.curvature_eq`): for smooth vector fields,
  `R(X, Y)Z = II(Y, II(X, Z)) − II(X, II(Y, Z))`, i.e. `R(X, Y) = D_Y D_X − D_X D_Y` on `T_qN`
  (`Morse.curvOp`).  Consequently:
  - **the Gauss equation** with Milnor's sign (`Morse.inner_curvOp`, `Morse.gauss_equation`):
    `⟨R(X, Y)Z, W⟩ = ⟨II(X, Z), II(Y, W)⟩ − ⟨II(X, W), II(Y, Z)⟩`;
  - **Lemma 9.1**: `Morse.curvTensor hN q`, a trilinear map on `T_qN` with
    `R(X, Y)Z (q) = curvTensor (X q) (Y q) (Z q)` (`Morse.curvature_eq_curvTensor`,
    `Morse.curvature_congr`);
  - **Lemma 9.3**: `curvTensor` satisfies (1)–(3) (`Morse.isCurvatureTensor_curvTensor`), so the
    algebra of `Morse/Chapter6/CurvatureAlgebra.lean` applies to it (pair symmetry, sectional
    curvature, polarization); for vector fields: `Morse.curvature_add_swap`,
    `Morse.curvature_bianchi`, `Morse.inner_curvature_add_inner`,
    `Morse.inner_curvature_comm_pairs`.
  The round sphere is treated in `Morse/Chapter6/SphereCurvature.lean`.

## What Milnor leaves implicit, and gaps in the text

* **Existence in Lemma 8.6** ("one can verify ... symmetric and compatible", p. 49) needs the
  converse of Lemma 8.3 and a patching of the local connections (see
  `Morse/Chapter6/Connection.lean`).  For the induced metric the connection is the global formula
  `P(dY(X))`; compatibility is immediate, but **symmetry is a genuine second-order property of the
  embedding**: it is equivalent to the symmetry of the second fundamental form, which Milnor does
  not mention in Part II (he meets the second fundamental form, as `ℓ_ij`, in §6, p. 34).  It is
  proved here from a slice chart `σ`: on `N`, `T_xN = ker d(σ₂)_x`, so `d(σ₂)_x ∘ P_x = 0`, and
  differentiating gives `d(σ₂)_q(II(v, w)) = −d²(σ₂)_q(v, w)`, symmetric in `v, w`.
* **The bracket.**  Milnor's `[X, Y]` is defined by its action on functions; that for fields on
  `N ⊆ ℝᴷ` it is computed by the ambient formula `dY(X) − dX(Y)`, and that this ambient vector is
  tangent to `N`, are not automatic (`Morse.dN_bracket` uses the symmetry of second derivatives,
  `Morse.bracket_mem` the symmetry of `II`).
* **Lemma 9.1**: "corresponding identities for `Y` and `Z` are easily obtained by similar
  computations" — for `Z` the computation is different (the terms with two derivatives of `f`
  cancel by `[X, Y]f = X(Yf) − Y(Xf)`).  Here tensoriality is read off from the explicit formula
  `R(X, Y) = D_Y D_X − D_X D_Y`, whose proof needs the symmetry of the ambient second derivative of
  a representative of `Z`.
* **Lemma 9.3 (2), (3)**: Milnor reduces to vector fields with vanishing brackets ("since all three
  terms of (2) are tensors, it is sufficient ..."), which requires extending tangent vectors to
  such fields (coordinate fields, cut off by a bump function).  Here no extension is needed: (2) is
  the symmetry of `II` and (3) the self-adjointness of `D_v`.
* **Signs.**  With Milnor's `R` (the negative of Nomizu's), the Gauss equation reads
  `⟨R(X, Y)X, Y⟩ = ⟨II(X, X), II(Y, Y)⟩ − ‖II(X, Y)‖²`, so Milnor's sectional curvature
  `⟨R(A, B)A, B⟩` (p. 100) is Gauss's curvature for a surface in `ℝ³`, positive on the sphere.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

/-! ### Vector fields on `N` -/

/-- A **vector field** on `N` in the embedded picture: a map `X : N → V` with `X q ∈ T_qN` for
every `q`.  It is smooth when it is a smooth map of manifolds `N → V`. -/
def IsTangentField (X : N → V) : Prop := ∀ q, X q ∈ tangentSubspace hN q

/-- The vector field `q ↦ P_q u` obtained by projecting a fixed vector `u ∈ V`. -/
def projField (u : V) (q : N) : V := tanProj hN q u

theorem isTangentField_projField (u : V) : IsTangentField hN (projField hN u) :=
  fun q => tanProj_apply_mem hN q u

theorem contMDiff_projField [FiniteDimensional ℝ Z] (u : V) :
    letI := hN.chartedSpace
    ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ (projField hN u) := by
  let _ := hN.chartedSpace
  exact (contMDiff_tanProj hN).clm_apply contMDiff_const

/-- **Every tangent vector extends to a smooth vector field**: `q ↦ P_q u` takes the value `u` at
`q₀` when `u ∈ T_{q₀}N`. -/
theorem projField_apply_of_mem {q : N} {u : V} (hu : u ∈ tangentSubspace hN q) :
    projField hN u q = u :=
  tanProj_eq_self hN hu

/-! ### The covariant derivative of the induced metric, and Milnor's rules (1)–(4) -/

/-- **Milnor's covariant derivative `X_p ⊢ Y`** (p. 43) for the metric induced from `V`:
`P_q(dY_q(v))` for a tangent vector `v = X_p ∈ T_qN` and a vector field `Y`. -/
def covAt (q : N) (v : V) (Y : N → V) : V := tanProj hN q (dN hN Y q v)

/-- **The Levi-Civita connection of the induced metric**, Milnor's `X ⊢ Y`:
`(X ⊢ Y)_q = P_q(dY_q(X_q))`. -/
def leviCivita (X Y : N → V) (q : N) : V := covAt hN q (X q) Y

/-- **The Lie bracket** of two vector fields on `N`, computed in `V`:
`[X, Y]_q = dY_q(X_q) − dX_q(Y_q)`.  It is tangent to `N` (`Morse.bracket_mem`), and it acts on
functions as Milnor's Poisson bracket `[X, Y]f = X(Yf) − Y(Xf)` (`Morse.dN_bracket`). -/
def bracket (X Y : N → V) (q : N) : V := dN hN Y q (X q) - dN hN X q (Y q)

theorem covAt_mem (q : N) (v : V) (Y : N → V) : covAt hN q v Y ∈ tangentSubspace hN q :=
  tanProj_apply_mem hN q _

theorem leviCivita_mem (X Y : N → V) (q : N) : leviCivita hN X Y q ∈ tangentSubspace hN q :=
  covAt_mem hN q _ Y

theorem isTangentField_leviCivita (X Y : N → V) : IsTangentField hN (leviCivita hN X Y) :=
  leviCivita_mem hN X Y

/-- **Milnor's rule (2)**, additivity in `X`. -/
theorem leviCivita_add_left (X X' Y : N → V) (q : N) :
    leviCivita hN (fun x => X x + X' x) Y q = leviCivita hN X Y q + leviCivita hN X' Y q := by
  simp only [leviCivita, covAt, map_add]

/-- **Milnor's rule (3)**: `(fX) ⊢ Y = f (X ⊢ Y)`. -/
theorem leviCivita_smul_left (f : N → ℝ) (X Y : N → V) (q : N) :
    leviCivita hN (fun x => f x • X x) Y q = f q • leviCivita hN X Y q := by
  simp only [leviCivita, covAt, map_smul]

/-- **Milnor's rule (2)**, additivity in `Y`. -/
theorem leviCivita_add_right (X : N → V) {Y Y' : N → V} {q : N}
    (hY : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, V) Y q)
    (hY' : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, V) Y' q) :
    leviCivita hN X (fun x => Y x + Y' x) q = leviCivita hN X Y q + leviCivita hN X Y' q := by
  simp only [leviCivita, covAt, dN_add hN hY hY', add_apply, map_add]

/-- **Milnor's rule (4)**, the Leibniz rule: `X ⊢ (fY) = (Xf) Y + f (X ⊢ Y)`, where
`Xf = df(X)`. -/
theorem leviCivita_smul_right {f : N → ℝ} {X Y : N → V} {q : N}
    (hf : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) f q)
    (hY : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, V) Y q)
    (hX : X q ∈ tangentSubspace hN q) (hYT : Y q ∈ tangentSubspace hN q) :
    leviCivita hN X (fun x => f x • Y x) q =
      dN hN f q (X q) • Y q + f q • leviCivita hN X Y q := by
  simp only [leviCivita, covAt]
  rw [dN_smul hN hf hY hX, map_add, map_smul, map_smul, tanProj_eq_self hN hYT]

/-- **Compatibility with the metric** in the form of **Milnor's Corollary 8.4** (p. 48):
`X_p⟨Y, Y'⟩ = ⟨X_p ⊢ Y, Y'_p⟩ + ⟨Y_p, X_p ⊢ Y'⟩`. -/
theorem dN_inner_eq_covAt {Y Y' : N → V} {q : N}
    (hY : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, V) Y q)
    (hY' : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, V) Y' q)
    (hYT : Y q ∈ tangentSubspace hN q) (hYT' : Y' q ∈ tangentSubspace hN q) {v : V}
    (hv : v ∈ tangentSubspace hN q) :
    dN hN (fun x => ⟪Y x, Y' x⟫) q v = ⟪covAt hN q v Y, Y' q⟫ + ⟪Y q, covAt hN q v Y'⟫ := by
  rw [dN_inner hN hY hY' hv, covAt, covAt, inner_tanProj_of_mem hN _ hYT', ← inner_tanProj_left,
    tanProj_eq_self hN hYT]

omit [FiniteDimensional ℝ V] in
/-- **Milnor's rule (1)**: the derivative of a smooth map `Y` in the direction of a smooth vector
field `X` is smooth. -/
theorem contMDiff_dN_apply [FiniteDimensional ℝ Z] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {X : N → V} {Y : N → E}
    (hX : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ X)
    (hY : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ Y) (hXT : IsTangentField hN X) :
    letI := hN.chartedSpace
    ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ (fun q => dN hN Y q (X q)) := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  intro q
  obtain ⟨G, U, hU, hqU, hG, hYG⟩ := exists_contDiffOn_rep hN hY q
  have hUN : IsOpen {x : N | x.1 ∈ U} := hU.preimage continuous_subtype_val
  have hG' : ContDiffOn ℝ ∞ (fderiv ℝ G) U := hG.fderiv_of_isOpen hU (by simp)
  have h1 : ContMDiffAt 𝓘(ℝ, Z) 𝓘(ℝ, V →L[ℝ] E) ∞ (fderiv ℝ G ∘ Subtype.val) q :=
    (hG'.contDiffAt (hU.mem_nhds hqU)).comp_contMDiffAt (hN.contMDiff_val q)
  refine (h1.clm_apply (hX q)).congr_of_eventuallyEq ?_
  filter_upwards [hUN.mem_nhds hqU] with x hx
  refine dN_eq_fderiv hN ((hG.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)) ?_ (hXT x)
  filter_upwards [hUN.mem_nhds hx] with y hy
  exact hYG y hy

/-- **Milnor's rule (1)**: `X ⊢ Y` is smooth when `X` and `Y` are. -/
theorem contMDiff_leviCivita [FiniteDimensional ℝ Z] {X Y : N → V}
    (hX : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ X)
    (hY : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ Y) (hXT : IsTangentField hN X) :
    letI := hN.chartedSpace
    ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ (leviCivita hN X Y) := by
  let _ := hN.chartedSpace
  exact (contMDiff_tanProj hN).clm_apply (contMDiff_dN_apply hN hX hY hXT)

/-! ### The second fundamental form -/

variable [FiniteDimensional ℝ Z]

/-- **The second fundamental form** of `N` at `q`: `II_q(v, w) = D_v w`, where `D_v = dN P q v`
is the derivative of the tangent projection in the direction `v`.  For `v, w ∈ T_qN` it is normal
to `N` (`Morse.secondFundForm_mem_orthogonal`) and symmetric (`Morse.secondFundForm_comm`), and
`II_q(v, W_q) = (1 − P_q)(dW_q(v))` for every tangent vector field `W`
(`Morse.secondFundForm_eq_sub_tanProj`). -/
def secondFundForm (q : N) (v w : V) : V := dN hN (tanProj hN) q v w

/-- **Tensoriality of the second fundamental form**: the normal component of the derivative of a
tangent vector field `W` in a tangent direction `v` is `II_q(v, W_q)`; in particular it depends
only on the value `W_q`. -/
theorem secondFundForm_eq_sub_tanProj {W' : N → V} (hW : IsTangentField hN W') {q : N}
    (hWd : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, V) W' q) {v : V}
    (hv : v ∈ tangentSubspace hN q) :
    secondFundForm hN q v (W' q) = dN hN W' q v - tanProj hN q (dN hN W' q v) := by
  have h := dN_clm_apply hN (mdifferentiableAt_tanProj hN q) hWd hv
  have hfun : (fun x => tanProj hN x (W' x)) = W' := funext fun x => tanProj_eq_self hN (hW x)
  rw [hfun] at h
  have h2 := congrArg (fun u => u - tanProj hN q (dN hN W' q v)) h
  simp only [add_sub_cancel_right] at h2
  exact h2.symm

/-- **The normal part of `dW_q(v)` depends only on `v` and `W_q`.** -/
theorem sub_tanProj_dN_eq_of_eq {W₁ W₂ : N → V} (hW₁ : IsTangentField hN W₁)
    (hW₂ : IsTangentField hN W₂) {q : N}
    (hW₁d : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, V) W₁ q)
    (hW₂d : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, V) W₂ q) (h : W₁ q = W₂ q)
    {v : V} (hv : v ∈ tangentSubspace hN q) :
    dN hN W₁ q v - tanProj hN q (dN hN W₁ q v) = dN hN W₂ q v - tanProj hN q (dN hN W₂ q v) := by
  rw [← secondFundForm_eq_sub_tanProj hN hW₁ hW₁d hv,
    ← secondFundForm_eq_sub_tanProj hN hW₂ hW₂d hv, h]

theorem tanProj_secondFundForm {q : N} {v w : V} (hv : v ∈ tangentSubspace hN q)
    (hw : w ∈ tangentSubspace hN q) : tanProj hN q (secondFundForm hN q v w) = 0 :=
  tanProj_dN_tanProj_of_mem hN hv hw

/-- The second fundamental form is normal to `N`. -/
theorem secondFundForm_mem_orthogonal {q : N} {v w : V} (hv : v ∈ tangentSubspace hN q)
    (hw : w ∈ tangentSubspace hN q) : secondFundForm hN q v w ∈ (tangentSubspace hN q)ᗮ :=
  dN_tanProj_mem_orthogonal_of_mem hN hv hw

/-- `II_q(v, ·)` is self-adjoint on `V`. -/
theorem inner_secondFundForm_comm (q : N) (v x y : V) :
    ⟪secondFundForm hN q v x, y⟫ = ⟪x, secondFundForm hN q v y⟫ :=
  inner_dN_tanProj_comm hN q v x y

omit [FiniteDimensional ℝ Z] in
theorem secondFundForm_add_left (q : N) (v v' w : V) :
    secondFundForm hN q (v + v') w = secondFundForm hN q v w + secondFundForm hN q v' w := by
  simp [secondFundForm]

omit [FiniteDimensional ℝ Z] in
theorem secondFundForm_smul_left (q : N) (a : ℝ) (v w : V) :
    secondFundForm hN q (a • v) w = a • secondFundForm hN q v w := by
  simp [secondFundForm]

omit [FiniteDimensional ℝ Z] in
theorem secondFundForm_add_right (q : N) (v w w' : V) :
    secondFundForm hN q v (w + w') = secondFundForm hN q v w + secondFundForm hN q v w' :=
  map_add _ _ _

omit [FiniteDimensional ℝ Z] in
theorem secondFundForm_smul_right (q : N) (a : ℝ) (v w : V) :
    secondFundForm hN q v (a • w) = a • secondFundForm hN q v w :=
  map_smul _ _ _

omit [FiniteDimensional ℝ Z] in
theorem secondFundForm_sub_right (q : N) (v w w' : V) :
    secondFundForm hN q v (w - w') = secondFundForm hN q v w - secondFundForm hN q v w' :=
  map_sub _ _ _

/-- `P_q(II_q(u, dW_q(v))) = II_q(u, II_q(v, W_q))` for a tangent vector field `W` and
`u, v ∈ T_qN`: only the normal part `II_q(v, W_q)` of `dW_q(v)` contributes. -/
theorem tanProj_secondFundForm_dN {W' : N → V} (hW : IsTangentField hN W') {q : N}
    (hWd : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, V) W' q) {u v : V}
    (hu : u ∈ tangentSubspace hN q) (hv : v ∈ tangentSubspace hN q) :
    tanProj hN q (secondFundForm hN q u (dN hN W' q v)) =
      secondFundForm hN q u (secondFundForm hN q v (W' q)) := by
  have h := secondFundForm_eq_sub_tanProj hN hW hWd hv
  have h2 : dN hN W' q v = tanProj hN q (dN hN W' q v) + secondFundForm hN q v (W' q) := by
    rw [h, add_sub_cancel]
  rw [h2, secondFundForm_add_right, map_add]
  have h3 : tanProj hN q (secondFundForm hN q u (tanProj hN q (dN hN W' q v))) = 0 :=
    tanProj_dN_tanProj hN hu _
  rw [h3, zero_add]
  exact tanProj_eq_self hN (dN_tanProj_mem_of_mem_orthogonal hN hu
    (secondFundForm_mem_orthogonal hN hv (hW q)))

variable [FiniteDimensional ℝ W]

/-- **The second fundamental form is symmetric**: `II_q(v, w) = II_q(w, v)` for `v, w ∈ T_qN`.

Proof: in a slice chart `σ`, `T_xN = ker d(σ₂)_x` for `x ∈ N`, so `d(σ₂)_x ∘ P_x = 0` on `N`.
Differentiating along `N` gives `d(σ₂)_q(II(v, w)) = −d²(σ₂)_q(v, w)`, which is symmetric; so
`II(v, w) − II(w, v)` is tangent, and it is also normal. -/
theorem secondFundForm_comm {q : N} {v w : V} (hv : v ∈ tangentSubspace hN q)
    (hw : w ∈ tangentSubspace hN q) : secondFundForm hN q v w = secondFundForm hN q w v := by
  set σ := sliceAt hN q with hσdef
  have hq := mem_sliceAt_source hN q
  set g : V → W := fun y => (σ.φ y).2 with hg
  have hσ : ContDiffAt ℝ ∞ σ.φ q :=
    (Milnor.Problems.sliceChart_contDiffOn σ).contDiffAt (σ.φ.open_source.mem_nhds hq)
  have hgq : ContDiffAt ℝ ∞ g q := contDiff_snd.contDiffAt.comp _ hσ
  -- `dg_y = snd ∘ dσ_y` near `q`
  have hdg : ∀ y ∈ σ.φ.source, fderiv ℝ g y = (ContinuousLinearMap.snd ℝ Z W).comp
      (fderiv ℝ σ.φ y) := fun y hy =>
    ((Milnor.Problems.sliceChart_differentiableAt σ hy).hasFDerivAt.snd).fderiv
  have hB : ContDiffAt ℝ ∞ (fderiv ℝ g) q := hgq.fderiv_right (m := ∞) (by simp)
  have hQ := contDiffAt_projRep σ hq
  have hBd := hB.differentiableAt (by simp)
  have hQd := hQ.differentiableAt (by simp)
  have hH := hBd.hasFDerivAt.clm_comp hQd.hasFDerivAt
  -- `dg_x ∘ P_x = 0` on `N` near `q`
  have h0 : ∀ᶠ x : N in 𝓝 q, (fun y => (fderiv ℝ g y).comp (projRep σ y)) x = 0 := by
    filter_upwards [σ.toChart.open_source.mem_nhds hq] with x hx
    ext u
    simp only [ContinuousLinearMap.comp_apply, zero_apply]
    rw [hdg x hx, projRep_eq hN σ hx]
    exact (Milnor.Problems.sliceChart_mem_tangentSpace_iff hN σ hx _).1 (tanProj_apply_mem hN x u)
  have key : ∀ a b : V, a ∈ tangentSubspace hN q → b ∈ tangentSubspace hN q →
      fderiv ℝ g q (secondFundForm hN q a b) = -fderiv ℝ (fderiv ℝ g) q a b := by
    intro a b ha hb
    have h1 := fderiv_eq_zero_of_eventually hN hH.differentiableAt h0 ha
    rw [hH.fderiv] at h1
    have h2 := DFunLike.congr_fun h1 b
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply, zero_apply] at h2
    rw [projRep_eq hN σ hq, tanProj_eq_self hN hb, ← dN_tanProj_eq_fderiv hN σ hq ha] at h2
    rw [secondFundForm]
    exact eq_neg_of_add_eq_zero_left h2
  have hsymm := (hgq.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)) v w
  have hker : fderiv ℝ g q (secondFundForm hN q v w - secondFundForm hN q w v) = 0 := by
    rw [map_sub, key v w hv hw, key w v hw hv, hsymm, sub_self]
  have hT : secondFundForm hN q v w - secondFundForm hN q w v ∈ tangentSubspace hN q := by
    refine (Milnor.Problems.sliceChart_mem_tangentSpace_iff hN σ hq _).2 ?_
    rw [hdg q hq] at hker
    exact hker
  have hO : secondFundForm hN q v w - secondFundForm hN q w v ∈ (tangentSubspace hN q)ᗮ :=
    Submodule.sub_mem _ (secondFundForm_mem_orthogonal hN hv hw)
      (secondFundForm_mem_orthogonal hN hw hv)
  exact sub_eq_zero.1 (eq_zero_of_mem_of_mem_orthogonal hN hT hO)

/-! ### Symmetry: the bracket of two vector fields is tangent -/

/-- **The Lie bracket of two tangent vector fields, computed in `V`, is tangent to `N`**: its normal
component is `II(X, Y) − II(Y, X) = 0`. -/
theorem bracket_mem {X Y : N → V} (hXT : IsTangentField hN X) (hYT : IsTangentField hN Y)
    {q : N} (hX : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, V) X q)
    (hY : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, V) Y q) :
    bracket hN X Y q ∈ tangentSubspace hN q := by
  have h1 := secondFundForm_eq_sub_tanProj hN hYT hY (hXT q)
  have h2 := secondFundForm_eq_sub_tanProj hN hXT hX (hYT q)
  rw [secondFundForm_comm hN (hXT q) (hYT q)] at h1
  rw [← tanProj_eq_self_iff, bracket, map_sub]
  exact (sub_eq_sub_iff_sub_eq_sub.1 (h1.symm.trans h2)).symm

/-- **The induced connection is symmetric** (Milnor, Definition 8.5, p. 48):
`X ⊢ Y − Y ⊢ X = [X, Y]`. -/
theorem leviCivita_sub_leviCivita {X Y : N → V} (hXT : IsTangentField hN X)
    (hYT : IsTangentField hN Y) {q : N}
    (hX : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, V) X q)
    (hY : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, V) Y q) :
    leviCivita hN X Y q - leviCivita hN Y X q = bracket hN X Y q := by
  rw [leviCivita, leviCivita, covAt, covAt, ← map_sub]
  exact tanProj_eq_self hN (bracket_mem hN hXT hYT hX hY)

/-- **The bracket acts on functions as Milnor's Poisson bracket** (p. 48):
`[X, Y]f = X(Yf) − Y(Xf)`, where `Xf = df(X)`. -/
theorem dN_bracket {f : N → ℝ} {X Y : N → V}
    (hf : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) ∞ f)
    (hX : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ X)
    (hY : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ Y)
    (hXT : IsTangentField hN X) (hYT : IsTangentField hN Y) (q : N) :
    dN hN (fun x => dN hN f x (Y x)) q (X q) - dN hN (fun x => dN hN f x (X x)) q (Y q) =
      dN hN f q (bracket hN X Y q) := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  obtain ⟨G, U, hU, hqU, hG, hfG⟩ := exists_contDiffOn_rep hN hf q
  have hUN : IsOpen {x : N | x.1 ∈ U} := hU.preimage continuous_subtype_val
  have hGq : ContDiffAt ℝ ∞ G q := hG.contDiffAt (hU.mem_nhds hqU)
  have hG' : ContDiffAt ℝ ∞ (fderiv ℝ G) q :=
    (hG.fderiv_of_isOpen hU (by simp)).contDiffAt (hU.mem_nhds hqU)
  have hfG' : ∀ x : N, x.1 ∈ U → ∀ v ∈ tangentSubspace hN x, dN hN f x v = fderiv ℝ G x v := by
    intro x hx v hv
    refine dN_eq_fderiv hN ((hG.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)) ?_ hv
    filter_upwards [hUN.mem_nhds hx] with y hy
    exact hfG y hy
  have hd1 : MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, V →L[ℝ] ℝ) (fun x : N => fderiv ℝ G x) q :=
    ((hG'.differentiableAt (by simp)).mdifferentiableAt).comp q
      (hN.contMDiff_val.mdifferentiableAt (by simp))
  have key : ∀ A B : N → V, IsTangentField hN A →
      (letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ A) → B q ∈ tangentSubspace hN q →
      dN hN (fun x => dN hN f x (A x)) q (B q) =
        fderiv ℝ (fderiv ℝ G) q (B q) (A q) + fderiv ℝ G q (dN hN A q (B q)) := by
    intro A B hAT hA hB
    have hev : (fun x => dN hN f x (A x)) =ᶠ[𝓝 q] fun x => fderiv ℝ G x (A x) := by
      filter_upwards [hUN.mem_nhds hqU] with x hx
      exact hfG' x hx (A x) (hAT x)
    rw [dN_congr hN hev, dN_clm_apply hN hd1 (hA.mdifferentiableAt (by simp)) hB,
      dN_comp_val hN (hG'.differentiableAt (by simp)) hB]
  rw [key Y X hYT hY (hXT q), key X Y hXT hX (hYT q),
    (hGq.isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top))
      (X q) (Y q),
    hfG' q hqU _ (bracket_mem hN hXT hYT (hX.mdifferentiableAt (by simp))
      (hY.mdifferentiableAt (by simp))), bracket, map_sub]
  abel

/-! ### Lemma 8.6: the induced connection is the Levi-Civita connection -/

/-- An operation `D` on vector fields of `N` with the properties of **Lemma 8.6** (p. 48): on
smooth vector fields it is tangent-valued, symmetric (`D X Y − D Y X = [X, Y]`) and compatible with
the metric in the form of Corollary 8.4. -/
structure IsSymmCompat (D : (N → V) → (N → V) → N → V) : Prop where
  mem : ∀ X Y : N → V, (letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ X) →
    (letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ Y) → IsTangentField hN X →
    IsTangentField hN Y → ∀ q, D X Y q ∈ tangentSubspace hN q
  symm : ∀ X Y : N → V, (letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ X) →
    (letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ Y) → IsTangentField hN X →
    IsTangentField hN Y → ∀ q, D X Y q - D Y X q = bracket hN X Y q
  compat : ∀ X Y Y' : N → V, (letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ X) →
    (letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ Y) →
    (letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ Y') → IsTangentField hN X →
    IsTangentField hN Y → IsTangentField hN Y' → ∀ q,
      dN hN (fun x => ⟪Y x, Y' x⟫) q (X q) = ⟪D X Y q, Y' q⟫ + ⟪Y q, D X Y' q⟫

/-- **Lemma 8.6, existence**: the connection `P(dY(X))` induced from `V` is symmetric and
compatible with the metric. -/
theorem isSymmCompat_leviCivita : IsSymmCompat hN (leviCivita hN) where
  mem X Y _ _ _ _ q := leviCivita_mem hN X Y q
  symm X Y hX hY hXT hYT q := by
    let _ := hN.chartedSpace
    exact leviCivita_sub_leviCivita hN hXT hYT (hX.mdifferentiableAt (by simp))
      (hY.mdifferentiableAt (by simp))
  compat X Y Y' _ hY hY' hXT hYT hYT' q := by
    let _ := hN.chartedSpace
    exact dN_inner_eq_covAt hN (hY.mdifferentiableAt (by simp)) (hY'.mdifferentiableAt (by simp))
      (hYT q) (hYT' q) (hXT q)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **The Koszul formula**: for `D` symmetric and compatible,
`2⟨D X Y, Z⟩ = X⟨Y, Z⟩ + Y⟨X, Z⟩ − Z⟨X, Y⟩ + ⟨[X, Y], Z⟩ − ⟨[X, Z], Y⟩ − ⟨[Y, Z], X⟩`.  With
coordinate fields it is Milnor's first Christoffel identity (p. 49). -/
theorem IsSymmCompat.two_mul_inner {D : (N → V) → (N → V) → N → V} (hD : IsSymmCompat hN D)
    {X Y Z' : N → V} (hX : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ X)
    (hY : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ Y)
    (hZ : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ Z') (hXT : IsTangentField hN X)
    (hYT : IsTangentField hN Y) (hZT : IsTangentField hN Z') (q : N) :
    2 * ⟪D X Y q, Z' q⟫ =
      dN hN (fun x => ⟪Y x, Z' x⟫) q (X q) + dN hN (fun x => ⟪X x, Z' x⟫) q (Y q) -
        dN hN (fun x => ⟪X x, Y x⟫) q (Z' q) + ⟪bracket hN X Y q, Z' q⟫ -
        ⟪bracket hN X Z' q, Y q⟫ - ⟪bracket hN Y Z' q, X q⟫ := by
  rw [hD.compat X Y Z' hX hY hZ hXT hYT hZT q, hD.compat Y X Z' hY hX hZ hYT hXT hZT q,
    hD.compat Z' X Y hZ hX hY hZT hXT hYT q, ← hD.symm X Y hX hY hXT hYT q,
    ← hD.symm X Z' hX hZ hXT hZT q, ← hD.symm Y Z' hY hZ hYT hZT q]
  simp only [inner_sub_left, inner_sub_right, real_inner_comm (Y q), real_inner_comm (X q)]
  ring

/-- **Lemma 8.6, uniqueness** (p. 48): a symmetric connection compatible with the metric agrees
with the induced connection `P(dY(X))` on smooth vector fields.  (By the Koszul formula, applied
with `Z` the field `x ↦ P_x(D X Y q − X ⊢ Y q)`.) -/
theorem IsSymmCompat.eq_leviCivita {D : (N → V) → (N → V) → N → V} (hD : IsSymmCompat hN D)
    {X Y : N → V} (hX : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ X)
    (hY : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ Y) (hXT : IsTangentField hN X)
    (hYT : IsTangentField hN Y) (q : N) : D X Y q = leviCivita hN X Y q := by
  set u := D X Y q - leviCivita hN X Y q with hu
  have huT : u ∈ tangentSubspace hN q :=
    Submodule.sub_mem _ (hD.mem X Y hX hY hXT hYT q) (leviCivita_mem hN X Y q)
  have h1 := hD.two_mul_inner hN hX hY (contMDiff_projField hN u) hXT hYT
    (isTangentField_projField hN u) q
  have h2 := (isSymmCompat_leviCivita hN).two_mul_inner hN hX hY (contMDiff_projField hN u) hXT
    hYT (isTangentField_projField hN u) q
  rw [projField_apply_of_mem hN huT] at h1 h2
  have h3 : ⟪u, u⟫ = 0 := by
    rw [hu, inner_sub_left]
    linarith
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h3)

/-! ### The curvature tensor and the Gauss equation -/

/-- **Milnor's curvature** (p. 51), for vector fields:
`R(X, Y)Z = −X ⊢ (Y ⊢ Z) + Y ⊢ (X ⊢ Z) + [X, Y] ⊢ Z`. -/
def curvature (X Y Z' : N → V) (q : N) : V :=
  -leviCivita hN X (leviCivita hN Y Z') q + leviCivita hN Y (leviCivita hN X Z') q +
    leviCivita hN (bracket hN X Y) Z' q

/-- The curvature at `q` in terms of the derivative `D = dN P q` of the projection:
`R_q(x, y) = D_y ∘ D_x − D_x ∘ D_y` (`Morse.curvature_eq`). -/
def curvOp (q : N) (x y : V) : V →L[ℝ] V :=
  (dN hN (tanProj hN) q y).comp (dN hN (tanProj hN) q x) -
    (dN hN (tanProj hN) q x).comp (dN hN (tanProj hN) q y)

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem curvOp_apply (q : N) (x y z : V) :
    curvOp hN q x y z = secondFundForm hN q y (secondFundForm hN q x z) -
      secondFundForm hN q x (secondFundForm hN q y z) := rfl

/-- **The curvature of `N ⊆ V`** (Lemma 9.1 made explicit): for smooth vector fields,
`R(X, Y)Z = II(Y, II(X, Z)) − II(X, II(Y, Z))`, i.e. `R(X, Y) = D_Y D_X − D_X D_Y` at `q`, where
`D_v = dN P q v`.  In particular `R(X, Y)Z` at `q` depends only on `X_q, Y_q, Z_q`.

Proof: with `G` a smooth ambient representative of `Z`, `B ⊢ (A ⊢ Z)` at `q` is
`D_B D_A Z + P(d²G(B, A)) + P(dG(dA(B)))`; the second terms cancel by the symmetry of `d²G`, the
third ones against `[X, Y] ⊢ Z = P(dG([X, Y]))`. -/
theorem curvature_eq {X Y Z' : N → V}
    (hX : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ X)
    (hY : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ Y)
    (hZ : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ Z')
    (hXT : IsTangentField hN X) (hYT : IsTangentField hN Y) (hZT : IsTangentField hN Z')
    (q : N) : curvature hN X Y Z' q = curvOp hN q (X q) (Y q) (Z' q) := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  obtain ⟨G, U, hU, hqU, hG, hZG⟩ := exists_contDiffOn_rep hN hZ q
  have hUN : IsOpen {x : N | x.1 ∈ U} := hU.preimage continuous_subtype_val
  have hGq : ContDiffAt ℝ ∞ G q := hG.contDiffAt (hU.mem_nhds hqU)
  have hG' : ContDiffAt ℝ ∞ (fderiv ℝ G) q :=
    (hG.fderiv_of_isOpen hU (by simp)).contDiffAt (hU.mem_nhds hqU)
  have hZG' : ∀ x : N, x.1 ∈ U → ∀ v ∈ tangentSubspace hN x, dN hN Z' x v = fderiv ℝ G x v := by
    intro x hx v hv
    refine dN_eq_fderiv hN ((hG.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)) ?_ hv
    filter_upwards [hUN.mem_nhds hx] with y hy
    exact hZG y hy
  have hd1 : MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, V →L[ℝ] V) (fun x : N => fderiv ℝ G x) q :=
    ((hG'.differentiableAt (by simp)).mdifferentiableAt).comp q
      (hN.contMDiff_val.mdifferentiableAt (by simp))
  -- `B ⊢ (A ⊢ Z) = D_B D_A Z + P(d²G(B, A)) + P(dG(dA(B)))` at `q`
  have hLL : ∀ A B : N → V, IsTangentField hN A →
      (letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ A) → IsTangentField hN B →
      leviCivita hN B (leviCivita hN A Z') q =
        secondFundForm hN q (B q) (secondFundForm hN q (A q) (Z' q)) +
          tanProj hN q (fderiv ℝ (fderiv ℝ G) q (B q) (A q)) +
          tanProj hN q (fderiv ℝ G q (dN hN A q (B q))) := by
    intro A B hAT hA hBT
    have hev : (fun x => dN hN Z' x (A x)) =ᶠ[𝓝 q] fun x => fderiv ℝ G x (A x) := by
      filter_upwards [hUN.mem_nhds hqU] with x hx
      exact hZG' x hx (A x) (hAT x)
    have hK : dN hN (fun x => dN hN Z' x (A x)) q (B q) =
        fderiv ℝ (fderiv ℝ G) q (B q) (A q) + fderiv ℝ G q (dN hN A q (B q)) := by
      rw [dN_congr hN hev, dN_clm_apply hN hd1 (hA.mdifferentiableAt (by simp)) (hBT q),
        dN_comp_val hN (hG'.differentiableAt (by simp)) (hBT q)]
    have hL : dN hN (leviCivita hN A Z') q (B q) =
        secondFundForm hN q (B q) (dN hN Z' q (A q)) +
          tanProj hN q (dN hN (fun x => dN hN Z' x (A x)) q (B q)) :=
      dN_clm_apply hN (mdifferentiableAt_tanProj hN q)
        ((contMDiff_dN_apply hN hA hZ hAT q).mdifferentiableAt (by simp)) (hBT q)
    rw [leviCivita, covAt, hL, hK, map_add, tanProj_tanProj, map_add,
      tanProj_secondFundForm_dN hN hZT (hZ.mdifferentiableAt (by simp)) (hBT q) (hAT q)]
    abel
  have hXY := hLL Y X hYT hY hXT
  have hYX := hLL X Y hXT hX hYT
  have hbr : leviCivita hN (bracket hN X Y) Z' q =
      tanProj hN q (fderiv ℝ G q (dN hN Y q (X q))) -
        tanProj hN q (fderiv ℝ G q (dN hN X q (Y q))) := by
    rw [leviCivita, covAt, hZG' q hqU _ (bracket_mem hN hXT hYT (hX.mdifferentiableAt (by simp))
      (hY.mdifferentiableAt (by simp))), bracket, map_sub, map_sub]
  have hsymm := (hGq.isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top))
      (X q) (Y q)
  rw [curvature, hXY, hYX, hbr, curvOp_apply, hsymm]
  abel

omit [FiniteDimensional ℝ W] in
/-- **The Gauss equation**, with Milnor's sign:
`⟨R(x, y)z, w⟩ = ⟨II(x, z), II(y, w)⟩ − ⟨II(x, w), II(y, z)⟩`. -/
theorem inner_curvOp (q : N) (x y z w : V) :
    ⟪curvOp hN q x y z, w⟫ = ⟪secondFundForm hN q x z, secondFundForm hN q y w⟫ -
      ⟪secondFundForm hN q x w, secondFundForm hN q y z⟫ := by
  rw [curvOp_apply, inner_sub_left, inner_secondFundForm_comm hN q y (secondFundForm hN q x z) w,
    inner_secondFundForm_comm hN q x (secondFundForm hN q y z) w,
    real_inner_comm (secondFundForm hN q y z)]

/-- **The Gauss equation** for vector fields on `N` (Milnor's sign):
`⟨R(X, Y)Z, W⟩ = ⟨II(X, Z), II(Y, W)⟩ − ⟨II(X, W), II(Y, Z)⟩`. -/
theorem gauss_equation {X Y Z' : N → V}
    (hX : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ X)
    (hY : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ Y)
    (hZ : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ Z')
    (hXT : IsTangentField hN X) (hYT : IsTangentField hN Y) (hZT : IsTangentField hN Z')
    (W' : N → V) (q : N) :
    ⟪curvature hN X Y Z' q, W' q⟫ =
      ⟪secondFundForm hN q (X q) (Z' q), secondFundForm hN q (Y q) (W' q)⟫ -
        ⟪secondFundForm hN q (X q) (W' q), secondFundForm hN q (Y q) (Z' q)⟫ := by
  rw [curvature_eq hN hX hY hZ hXT hYT hZT, inner_curvOp]

/-! ### Lemma 9.1: the curvature tensor on `T_qN`, and the symmetries of Lemma 9.3 -/

omit [FiniteDimensional ℝ W] in
theorem curvOp_mem {q : N} {x y z : V} (hx : x ∈ tangentSubspace hN q)
    (hy : y ∈ tangentSubspace hN q) (hz : z ∈ tangentSubspace hN q) :
    curvOp hN q x y z ∈ tangentSubspace hN q := by
  rw [curvOp_apply]
  exact Submodule.sub_mem _
    (dN_tanProj_mem_of_mem_orthogonal hN hy (secondFundForm_mem_orthogonal hN hx hz))
    (dN_tanProj_mem_of_mem_orthogonal hN hx (secondFundForm_mem_orthogonal hN hy hz))

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem curvOp_add_left (q : N) (x x' y : V) :
    curvOp hN q (x + x') y = curvOp hN q x y + curvOp hN q x' y := by
  ext z
  simp only [add_apply, curvOp_apply, secondFundForm_add_left, secondFundForm_add_right]
  abel

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem curvOp_smul_left (q : N) (a : ℝ) (x y : V) :
    curvOp hN q (a • x) y = a • curvOp hN q x y := by
  ext z
  simp only [smul_apply, curvOp_apply, secondFundForm_smul_left, secondFundForm_smul_right,
    smul_sub]

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem curvOp_add_right (q : N) (x y y' : V) :
    curvOp hN q x (y + y') = curvOp hN q x y + curvOp hN q x y' := by
  ext z
  simp only [add_apply, curvOp_apply, secondFundForm_add_left, secondFundForm_add_right]
  abel

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem curvOp_smul_right (q : N) (a : ℝ) (x y : V) :
    curvOp hN q x (a • y) = a • curvOp hN q x y := by
  ext z
  simp only [smul_apply, curvOp_apply, secondFundForm_smul_left, secondFundForm_smul_right,
    smul_sub]

/-- **The curvature tensor of `N` at `q`** (Lemma 9.1, p. 51), as a trilinear map
`T_qN × T_qN × T_qN → T_qN`: `(x, y, z) ↦ R(x, y)z = II(y, II(x, z)) − II(x, II(y, z))`. -/
def curvTensor (q : N) :
    tangentSubspace hN q →ₗ[ℝ] tangentSubspace hN q →ₗ[ℝ] tangentSubspace hN q →ₗ[ℝ]
      tangentSubspace hN q :=
  LinearMap.mk₂ ℝ
    (fun x y => LinearMap.codRestrict (tangentSubspace hN q)
      ((curvOp hN q x y : V →ₗ[ℝ] V).comp (tangentSubspace hN q).subtype)
      (fun z => curvOp_mem hN x.2 y.2 z.2))
    (fun x x' y => by
      ext z
      simp [curvOp_add_left])
    (fun a x y => by
      ext z
      simp [curvOp_smul_left])
    (fun x y y' => by
      ext z
      simp [curvOp_add_right])
    (fun a x y => by
      ext z
      simp [curvOp_smul_right])

omit [FiniteDimensional ℝ W] in
theorem coe_curvTensor_apply (q : N) (x y z : tangentSubspace hN q) :
    (curvTensor hN q x y z : V) = curvOp hN q x y z := rfl

/-- **Lemma 9.1** (p. 51) for `N ⊆ V`: `R(X, Y)Z` at `q` is the trilinear map `curvTensor hN q`
applied to `X_q, Y_q, Z_q`. -/
theorem curvature_eq_curvTensor {X Y Z' : N → V}
    (hX : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ X)
    (hY : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ Y)
    (hZ : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ Z')
    (hXT : IsTangentField hN X) (hYT : IsTangentField hN Y) (hZT : IsTangentField hN Z')
    (q : N) :
    curvature hN X Y Z' q = curvTensor hN q ⟨X q, hXT q⟩ ⟨Y q, hYT q⟩ ⟨Z' q, hZT q⟩ :=
  curvature_eq hN hX hY hZ hXT hYT hZT q

/-- **Lemma 9.1** (p. 51): the value of `R(X, Y)Z` at `q` depends only on `X_q`, `Y_q`, `Z_q`. -/
theorem curvature_congr {X Y Z' X' Y' Z'' : N → V}
    (hX : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ X)
    (hY : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ Y)
    (hZ : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ Z')
    (hX' : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ X')
    (hY' : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ Y')
    (hZ' : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ Z'')
    (hXT : IsTangentField hN X) (hYT : IsTangentField hN Y) (hZT : IsTangentField hN Z')
    (hXT' : IsTangentField hN X') (hYT' : IsTangentField hN Y') (hZT' : IsTangentField hN Z'')
    {q : N} (h1 : X q = X' q) (h2 : Y q = Y' q) (h3 : Z' q = Z'' q) :
    curvature hN X Y Z' q = curvature hN X' Y' Z'' q := by
  rw [curvature_eq hN hX hY hZ hXT hYT hZT, curvature_eq hN hX' hY' hZ' hXT' hYT' hZT', h1, h2, h3]

/-- **The curvature tensor of `N` satisfies (1), (2), (3) of Lemma 9.3** (p. 53): skew-symmetry
in `(x, y)`, the first Bianchi identity (from the symmetry of `II`) and skew-symmetry of
`⟨R(x, y)z, w⟩` in `(z, w)` (from the self-adjointness of `II(v, ·)`).  So the algebra of
`Morse/Chapter6/CurvatureAlgebra.lean` applies: pair symmetry (4), sectional curvature, and so
on. -/
theorem isCurvatureTensor_curvTensor (q : N) : IsCurvatureTensor (curvTensor hN q) where
  add_swap x y z := by
    ext
    simp only [Submodule.coe_add, coe_curvTensor_apply, curvOp_apply, Submodule.coe_zero]
    abel
  bianchi x y z := by
    ext
    simp only [Submodule.coe_add, coe_curvTensor_apply, curvOp_apply, Submodule.coe_zero]
    rw [secondFundForm_comm hN y.2 x.2, secondFundForm_comm hN z.2 y.2,
      secondFundForm_comm hN x.2 z.2]
    abel
  inner_add_inner x y z w := by
    simp only [Submodule.coe_inner, coe_curvTensor_apply, inner_curvOp]
    ring

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **Lemma 9.3 (1)** (p. 53), for vector fields: `R(X, Y)Z + R(Y, X)Z = 0`.  (No hypothesis is
needed: it follows from `[Y, X] = −[X, Y]`.) -/
theorem curvature_add_swap (X Y Z' : N → V) (q : N) :
    curvature hN X Y Z' q + curvature hN Y X Z' q = 0 := by
  have h : bracket hN Y X q = -bracket hN X Y q := by rw [bracket, bracket, neg_sub]
  simp only [curvature, leviCivita, covAt, h, map_neg]
  abel

/-- **Lemma 9.3 (2)** (p. 53), the first Bianchi identity, for vector fields. -/
theorem curvature_bianchi {X Y Z' : N → V}
    (hX : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ X)
    (hY : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ Y)
    (hZ : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ Z')
    (hXT : IsTangentField hN X) (hYT : IsTangentField hN Y) (hZT : IsTangentField hN Z')
    (q : N) : curvature hN X Y Z' q + curvature hN Y Z' X q + curvature hN Z' X Y q = 0 := by
  rw [curvature_eq_curvTensor hN hX hY hZ hXT hYT hZT,
    curvature_eq_curvTensor hN hY hZ hX hYT hZT hXT,
    curvature_eq_curvTensor hN hZ hX hY hZT hXT hYT, ← Submodule.coe_add, ← Submodule.coe_add,
    (isCurvatureTensor_curvTensor hN q).bianchi, Submodule.coe_zero]

/-- **Lemma 9.3 (3)** (p. 53), for vector fields: `⟨R(X, Y)Z, W⟩ + ⟨R(X, Y)W, Z⟩ = 0`. -/
theorem inner_curvature_add_inner {X Y Z' W' : N → V}
    (hX : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ X)
    (hY : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ Y)
    (hZ : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ Z')
    (hW : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ W')
    (hXT : IsTangentField hN X) (hYT : IsTangentField hN Y) (hZT : IsTangentField hN Z')
    (hWT : IsTangentField hN W') (q : N) :
    ⟪curvature hN X Y Z' q, W' q⟫ + ⟪curvature hN X Y W' q, Z' q⟫ = 0 := by
  have h := (isCurvatureTensor_curvTensor hN q).inner_add_inner ⟨X q, hXT q⟩ ⟨Y q, hYT q⟩
    ⟨Z' q, hZT q⟩ ⟨W' q, hWT q⟩
  rwa [Submodule.coe_inner, Submodule.coe_inner, ← curvature_eq_curvTensor hN hX hY hZ hXT hYT hZT,
    ← curvature_eq_curvTensor hN hX hY hW hXT hYT hWT] at h

/-- **Lemma 9.3 (4)** (p. 53), for vector fields: `⟨R(X, Y)Z, W⟩ = ⟨R(Z, W)X, Y⟩`, by Milnor's
octahedron (`Morse.IsCurvatureTensor.inner_comm_pairs`). -/
theorem inner_curvature_comm_pairs {X Y Z' W' : N → V}
    (hX : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ X)
    (hY : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ Y)
    (hZ : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ Z')
    (hW : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ W')
    (hXT : IsTangentField hN X) (hYT : IsTangentField hN Y) (hZT : IsTangentField hN Z')
    (hWT : IsTangentField hN W') (q : N) :
    ⟪curvature hN X Y Z' q, W' q⟫ = ⟪curvature hN Z' W' X q, Y q⟫ := by
  have h := (isCurvatureTensor_curvTensor hN q).inner_comm_pairs ⟨X q, hXT q⟩ ⟨Y q, hYT q⟩
    ⟨Z' q, hZT q⟩ ⟨W' q, hWT q⟩
  rwa [Submodule.coe_inner, Submodule.coe_inner, ← curvature_eq_curvTensor hN hX hY hZ hXT hYT hZT,
    ← curvature_eq_curvTensor hN hZ hW hX hZT hWT hXT] at h

end Morse
