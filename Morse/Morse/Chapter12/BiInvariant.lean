import Mathlib.Algebra.Lie.InvariantForm
import Mathlib.Algebra.Lie.TraceForm
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
Milnor, *Morse Theory*, §21 (Lie groups as symmetric spaces), pp. 112–117.

# The curvature of a bi-invariant metric, algebraically

Everything Milnor proves about the curvature of a Lie group `G` with a left- and right-invariant
metric is a computation in its Lie algebra `𝔤` of left-invariant fields, once two geometric
facts are granted: left-invariant fields have constant inner products, and their integral curves
are geodesics.  This file does that computation for an abstract real Lie algebra `L` with a
bilinear form `B` (Milnor's `⟨ , ⟩` on `𝔤`).

## Milnor's text, paraphrased

* **Theorem 21.3** (p. 113).  For left-invariant fields `X, Y, Z, W` on a Lie group with a bi-
  invariant metric: (a) `⟨[X,Y],Z⟩ = ⟨X,[Y,Z]⟩`; (b) `R(X,Y)Z = ¼[[X,Y],Z]`;
  (c) `⟨R(X,Y)Z,W⟩ = ¼⟨[X,Y],[Z,W]⟩`.  *Proof* (pp. 113–114): writing `X ⊢ Y` for `∇_X Y`, one
  has `X ⊢ X = 0` because the integral curves of `X` are left translates of one-parameter
  subgroups, hence geodesics; so `(X+Y) ⊢ (X+Y) = 0` gives `X ⊢ Y + Y ⊢ X = 0`, and with
  `X ⊢ Y − Y ⊢ X = [X,Y]` (8.5): (d) `X ⊢ Y = ½[X,Y]`.  Since `⟨X,Z⟩` is constant,
  `0 = Y⟨X,Z⟩ = ⟨Y ⊢ X, Z⟩ + ⟨X, Y ⊢ Z⟩` (8.4), which with (d) is (a).  Substituting (d) into
  `R(X,Y)Z = −X ⊢ (Y ⊢ Z) + Y ⊢ (X ⊢ Z) + [X,Y] ⊢ Z` and using the Jacobi identity gives (b);
  (c) follows from (a) and (b).  *Footnote*: `(X,Y,Z) ↦ ⟨[X,Y],Z⟩` is skew in all three
  variables (Cartan's 3-form).
* **Corollary 21.4** (p. 115).  The sectional curvature `⟨R(X,Y)X,Y⟩ = ¼⟨[X,Y],[X,Y]⟩` is
  `≥ 0`, with equality iff `[X,Y] = 0`.  (Milnor's sign convention for `R` is the opposite of the
  now usual one; in the usual one this reads `⟨R(X,Y)Y,X⟩ = ¼|[X,Y]|²`.)
* **Corollary 21.5** (p. 115).  If moreover the centre of `𝔤` is trivial, `G` is compact with
  finite fundamental group.  *Proof*: the Ricci curvature
  `K(X_1,X_1) = Σ_i ⟨R(X_1,X_i)X_1,X_i⟩` (orthonormal basis, `|X_1| = 1`) is strictly positive,
  since `[X_1,X_i] ≠ 0` for some `i`, and bounded away from `0`; apply Myers (19.5).
* **Corollary 21.6** (pp. 115–116).  For `G` simply connected, `𝔤' = 𝔠^⊥` (`𝔠` the centre) is
  closed under brackets, since `⟨[X,Y],C⟩ = ⟨X,[Y,C]⟩ = 0`; so `𝔤 = 𝔤' ⊕ 𝔠` and `G` splits.
* **Theorem 21.7, proof** (pp. 116–117).  The conjugate points along a geodesic with velocity `V`
  are governed by `K_V(W) = R(V,W)V = ¼[[V,W],V]`, i.e. `K_V = −¼ (Ad V)∘(Ad V)`, with
  `Ad V(W) = [V,W]` skew-symmetric by 21.3(a).  In an orthonormal basis in which `Ad V` is block
  diagonal with blocks `(0 a_i; −a_i 0)`, `(Ad V)²` is `diag(−a_1², −a_1², −a_2², …)`; hence the
  non-zero eigenvalues of `K_V` are positive and occur in pairs, so (20.5) do the conjugate
  points, and every index is even.

## What is formalized

`L` is a real Lie algebra and `B : LinearMap.BilinForm ℝ L`; every hypothesis on `B` (symmetric,
positive definite, ad-invariant) is an explicit argument, so each theorem says exactly what it
uses.  A connection on left-invariant fields is a bilinear `D : L →ₗ L →ₗ L` (`D X Y = X ⊢ Y`).

* `Morse.IsAdInvariant B` is 21.3(a); `Morse.isAdInvariant_iff_lieInvariant`: it is Mathlib's
  `LinearMap.BilinForm.lieInvariant`.
* `Morse.IsLeviCivita B D`: `D` is symmetric (8.5) and compatible with `B` on fields with constant
  inner products (8.4).  `Morse.IsLeviCivita.conn_eq` is (d) and
  `Morse.IsLeviCivita.isAdInvariant` is (a), both from `X ⊢ X = 0`, as in Milnor.
  `Morse.IsLeviCivita.koszul` (the Koszul formula) and
  `Morse.IsLeviCivita.conn_eq_of_isAdInvariant` give the converse route: for an ad-invariant
  non-degenerate `B`, the connection *must* be `½[ , ]`; `Morse.isLeviCivita_halfLie`: and it is
  one.
* `Morse.curv D X Y Z = −D_X D_Y Z + D_Y D_X Z + D_{[X,Y]} Z` (Milnor's sign);
  `Morse.curv_halfLie` is 21.3(b), `Morse.curv_inner` is 21.3(c), `Morse.sectional`,
  `Morse.sectional_nonneg`, `Morse.sectional_eq_zero_iff` are 21.4, `Morse.sectional_std` is
  the usual-sign form; `Morse.cartan_form_swap₁₂`, `Morse.cartan_form_swap₂₃` are the footnote.
* `Morse.jacobiOp V = K_V = −¼ ad_V²`, with `Morse.curv_halfLie_eq_jacobiOp`
  (`K_V(W) = R(V,W)V`), `Morse.ad_skew`, `Morse.jacobiOp_symm` (self-adjoint),
  `Morse.jacobiOp_self` and `Morse.jacobiOp_self_nonneg` (positive semi-definite),
  `Morse.jacobiOp_eq_zero_iff` (kernel = centralizer of `V`), `Morse.eigenvalue_nonneg`,
  `Morse.ad_eigenvalue_eq_zero` (the only real eigenvalue of `ad_V` is `0`).
* **The eigenvalues of `K_V` are `¼` of the squares of those of `ad_V`, up to sign, and occur in
  pairs.**  `Morse.jacobiOp_of_lie_lie`, `Morse.lie_lie_of_jacobiOp`: `K_V W = μ W` iff
  `ad_V² W = −4μ W`.  `Morse.lie_mem_eigenspace`: `ad_V` preserves each eigenspace `E_μ`;
  `Morse.eigenJ`: for `μ > 0`, `(2√μ)⁻¹ ad_V` is a complex structure on `E_μ`
  (`Morse.eigenJ_comp_self`), orthogonal for `B` (`Morse.eigenJ_isometry`), so `ad_V` acts on
  `E_μ` as `2√μ` times a rotation by a right angle, `μ = (2√μ)²/4`;
  `Morse.even_finrank_eigenspace`: every `E_μ`, `μ ≠ 0`, is even-dimensional.  This is exactly
  the content of Milnor's normal form that the proof of 21.7 uses.  (With
  `Morse.even_spectralIndex` of `Morse/Chapter14/IndexCount.lean` it gives that the index is
  even.)
* `Morse.trace_jacobiOp`: the Ricci curvature `tr K_V` is `−¼` times Mathlib's `killingForm`;
  `Morse.trace_jacobiOp_pos`: if the centre is trivial it is `> 0` for `V ≠ 0` (21.5), and
  `Morse.killingForm_neg`: the Killing form is negative definite.
* 21.6: `Morse.centerCompl` is `𝔠^⊥`, a Lie *ideal* (by Mathlib's
  `LieAlgebra.InvariantForm.orthogonal`), `Morse.isCompl_center_centerCompl`: `𝔤 = 𝔠 ⊕ 𝔤'`, and
  `Morse.eq_zero_of_mem_centerCompl`: `𝔤'` has trivial centre.

Not formalized: the passage from the group to the algebra (left-invariant fields, Lemmas 21.1 and
21.2, the fact that `∇_X Y` is left-invariant for left-invariant `X, Y`), the orthonormal block
normal form of `ad_V` itself (only its consequence for eigenspaces), the compactness argument
"bounded away from zero" and everything topological in 21.5–21.7 (Myers, the splitting of `G`,
the CW structure of `Ω(G)`).  For the matrix groups `U(n)`, `SU(n)`, `O(n)`, `SO(n)`, as
submanifolds of `Mₙ(𝕜)` with the induced metric, Lemmas 21.1–21.2 and Theorem 21.3 are proved in
the embedded setting in `Morse/Chapter12/GroupGeodesics.lean`;
`Morse.IsMatrixGroup.curvOp_eq_curv_halfLie` identifies the curvature of the submanifold with
`curv (halfLie 𝔤)` of this file, and `Morse.IsMatrixGroup.curvOp_eq_jacobiOp` with `jacobiOp`.

## Gaps in Milnor's text

* p. 113, "`X ⊢ X = 0`, since the integral curves of `X` are left translates of one-parameter
  subgroups, and therefore are geodesics": this uses Lemma 21.2 and that left translations are
  isometries; and the computation of `R` with (d) needs `Y ⊢ Z` to be left-invariant again,
  which is why `D` is a map `L → L → L` here.
* p. 114, (a) from `Y⟨X,Z⟩ = 0`: `⟨X,Z⟩` is constant because the metric is left-invariant.
* p. 115, 21.5: "`K(X_1,X_1)` must be strictly positive since `[X_1,X_i] ≠ 0` for some `i`" uses
  `⟨R(X_1,X_i)X_1,X_i⟩ = ¼|[X_1,X_i]|² ≥ 0` termwise; here the trace is computed in a
  `B`-orthogonal basis (`Morse.trace_eq_sum_of_isOrtho`).
* p. 115, 21.6: Milnor shows `𝔤'` is a subalgebra; the same line shows it is an ideal, which is
  what the splitting needs.
* p. 117: the block normal form of the skew-symmetric `Ad V` is quoted without proof ("we can
  choose an orthonormal basis"); here it is replaced by the complex structure on each eigenspace,
  which is all that "occur in pairs" needs.
-/

open LinearMap (BilinForm)

noncomputable section

namespace Morse

/-- A finite-dimensional real vector space with a complex structure (`J² = −1`) has even
dimension: `det(J)² = det(−1) = (−1)ⁿ`. -/
theorem even_finrank_of_comp_self_eq_neg_id {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (J : E →ₗ[ℝ] E) (hJ : J ∘ₗ J = -LinearMap.id) :
    Even (Module.finrank ℝ E) := by
  have h := congrArg LinearMap.det hJ
  rw [LinearMap.det_comp, show (-LinearMap.id : E →ₗ[ℝ] E) = (-1 : ℝ) • LinearMap.id by simp,
    LinearMap.det_smul, LinearMap.det_id, mul_one] at h
  rcases Nat.even_or_odd (Module.finrank ℝ E) with he | ho
  · exact he
  · rw [ho.neg_one_pow] at h
    nlinarith [mul_self_nonneg (LinearMap.det J)]

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- Milnor's 21.3(a): `⟨[X,Y],Z⟩ = ⟨X,[Y,Z]⟩` for all `X, Y, Z ∈ 𝔤`. -/
def IsAdInvariant (B : BilinForm ℝ L) : Prop := ∀ X Y Z : L, B ⁅X, Y⁆ Z = B X ⁅Y, Z⁆

theorem isAdInvariant_iff_lieInvariant (B : BilinForm ℝ L) :
    IsAdInvariant B ↔ B.lieInvariant L := by
  constructor
  · intro h x y z
    have := h y x z
    rw [← lie_skew, map_neg, LinearMap.neg_apply] at this
    linarith
  · intro h X Y Z
    have := h Y X Z
    rw [← lie_skew, map_neg, LinearMap.neg_apply] at this
    linarith

/-- A connection `D X Y = X ⊢ Y` on left-invariant fields which is symmetric (Milnor 8.5) and
compatible with the metric (8.4, for fields whose inner products are constant). -/
structure IsLeviCivita (B : BilinForm ℝ L) (D : L →ₗ[ℝ] L →ₗ[ℝ] L) : Prop where
  torsion_free : ∀ X Y, D X Y - D Y X = ⁅X, Y⁆
  metric : ∀ X Y Z, B (D X Y) Z + B Y (D X Z) = 0

variable {B : BilinForm ℝ L} {D : L →ₗ[ℝ] L →ₗ[ℝ] L}

/-- Milnor's (d), p. 114: if left-invariant fields satisfy `X ⊢ X = 0` (their integral curves
are geodesics), then `X ⊢ Y = ½[X,Y]`. -/
theorem IsLeviCivita.conn_eq (hD : IsLeviCivita B D) (hgeod : ∀ X, D X X = 0) (X Y : L) :
    D X Y = (1 / 2 : ℝ) • ⁅X, Y⁆ := by
  have h1 : D X Y + D Y X = 0 := by
    have := hgeod (X + Y)
    simp only [map_add, LinearMap.add_apply, hgeod X, hgeod Y, zero_add, add_zero] at this
    rw [add_comm]; exact this
  have h2 := hD.torsion_free X Y
  have : (2 : ℝ) • D X Y = ⁅X, Y⁆ := by
    rw [two_smul]
    calc D X Y + D X Y = (D X Y + D Y X) + (D X Y - D Y X) := by abel
      _ = ⁅X, Y⁆ := by rw [h1, h2, zero_add]
  rw [← this, smul_smul]; norm_num

/-- **Theorem 21.3(a)**, with Milnor's proof: `0 = Y⟨X,Z⟩ = ⟨Y ⊢ X, Z⟩ + ⟨X, Y ⊢ Z⟩` and (d). -/
theorem IsLeviCivita.isAdInvariant (hD : IsLeviCivita B D) (hgeod : ∀ X, D X X = 0) :
    IsAdInvariant B := by
  intro X Y Z
  have := hD.metric Y X Z
  rw [hD.conn_eq hgeod, hD.conn_eq hgeod, map_smul, LinearMap.smul_apply, map_smul,
    smul_eq_mul, smul_eq_mul, ← lie_skew, map_neg, LinearMap.neg_apply] at this
  linarith

/-- The Koszul formula for left-invariant fields (all inner products constant). -/
theorem IsLeviCivita.koszul (hD : IsLeviCivita B D) (hsymm : ∀ x y, B x y = B y x) (X Y Z : L) :
    2 * B (D X Y) Z = B ⁅X, Y⁆ Z - B ⁅Y, Z⁆ X + B ⁅Z, X⁆ Y := by
  have m1 := hD.metric X Y Z
  have m2 := hD.metric Y Z X
  have m3 := hD.metric Z X Y
  have t1 := congrArg (fun v => B v Z) (hD.torsion_free X Y)
  have t2 := congrArg (fun v => B v X) (hD.torsion_free Y Z)
  have t3 := congrArg (fun v => B v Y) (hD.torsion_free Z X)
  simp only [map_sub, LinearMap.sub_apply] at t1 t2 t3
  rw [hsymm Y (D X Z)] at m1
  rw [hsymm Z (D Y X)] at m2
  rw [hsymm X (D Z Y)] at m3
  linarith

/-- Conversely, for an ad-invariant, symmetric, non-degenerate `B` the Levi-Civita connection on
left-invariant fields is forced to be `½[ , ]` (uniqueness, 8.6). -/
theorem IsLeviCivita.conn_eq_of_isAdInvariant (hD : IsLeviCivita B D) (hB : IsAdInvariant B)
    (hsymm : ∀ x y, B x y = B y x) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (X Y : L) :
    D X Y = (1 / 2 : ℝ) • ⁅X, Y⁆ := by
  rw [← sub_eq_zero]
  apply hnd
  intro Z
  have h := hD.koszul hsymm X Y Z
  have e : B ⁅Y, Z⁆ X = B ⁅Z, X⁆ Y := by
    rw [hB, hsymm]
  rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  linarith


variable (L) in
/-- The connection `X ⊢ Y = ½[X,Y]` of (d). -/
def halfLie : L →ₗ[ℝ] L →ₗ[ℝ] L := (1 / 2 : ℝ) • (LieAlgebra.ad ℝ L : L →ₗ[ℝ] Module.End ℝ L)

@[simp] theorem halfLie_apply (X Y : L) : halfLie L X Y = (1 / 2 : ℝ) • ⁅X, Y⁆ := by
  simp [halfLie]

/-- `½[ , ]` is symmetric and compatible with an ad-invariant `B`. -/
theorem isLeviCivita_halfLie (hB : IsAdInvariant B) : IsLeviCivita B (halfLie L) where
  torsion_free X Y := by
    rw [halfLie_apply, halfLie_apply, ← lie_skew Y X, smul_neg, sub_neg_eq_add, ← add_smul]
    norm_num
  metric X Y Z := by
    rw [halfLie_apply, halfLie_apply, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul,
      smul_eq_mul]
    have := hB Y X Z
    rw [← lie_skew, map_neg, LinearMap.neg_apply] at this
    linarith

/-- Milnor's curvature tensor (§9, his sign):
`R(X,Y)Z = −X ⊢ (Y ⊢ Z) + Y ⊢ (X ⊢ Z) + [X,Y] ⊢ Z`. -/
def curv (D : L →ₗ[ℝ] L →ₗ[ℝ] L) (X Y Z : L) : L := -D X (D Y Z) + D Y (D X Z) + D ⁅X, Y⁆ Z

/-- **Theorem 21.3(b)**: `R(X,Y)Z = ¼[[X,Y],Z]`. -/
theorem curv_halfLie (X Y Z : L) : curv (halfLie L) X Y Z = (1 / 4 : ℝ) • ⁅⁅X, Y⁆, Z⁆ := by
  simp only [curv, halfLie_apply, lie_smul, smul_smul]
  rw [lie_lie]
  module


/-- **Theorem 21.3(c)**: `⟨R(X,Y)Z,W⟩ = ¼⟨[X,Y],[Z,W]⟩`. -/
theorem curv_inner (hB : IsAdInvariant B) (X Y Z W : L) :
    B (curv (halfLie L) X Y Z) W = (1 / 4 : ℝ) * B ⁅X, Y⁆ ⁅Z, W⁆ := by
  rw [curv_halfLie, map_smul, LinearMap.smul_apply, smul_eq_mul, hB]

/-- **Corollary 21.4**: `⟨R(X,Y)X,Y⟩ = ¼⟨[X,Y],[X,Y]⟩`. -/
theorem sectional (hB : IsAdInvariant B) (X Y : L) :
    B (curv (halfLie L) X Y X) Y = (1 / 4 : ℝ) * B ⁅X, Y⁆ ⁅X, Y⁆ := curv_inner hB X Y X Y

/-- `Ad V` is skew-symmetric (p. 117, from 21.3(a)). -/
theorem ad_skew (hB : IsAdInvariant B) (V X Y : L) : B ⁅V, X⁆ Y = -B X ⁅V, Y⁆ := by
  have := hB X V Y
  rw [← lie_skew, map_neg, LinearMap.neg_apply] at this
  linarith

variable (L) in
/-- The operator `K_V(W) = R(V,W)V = −¼ (Ad V)²(W)` of 20.5 and 21.7. -/
def jacobiOp (V : L) : Module.End ℝ L :=
  -(1 / 4 : ℝ) • (LieAlgebra.ad ℝ L V ∘ₗ LieAlgebra.ad ℝ L V)

theorem jacobiOp_apply (V W : L) : jacobiOp L V W = -(1 / 4 : ℝ) • ⁅V, ⁅V, W⁆⁆ := by
  simp [jacobiOp]

/-- `K_V(W) = R(V,W)V = ¼[[V,W],V]` (p. 116). -/
theorem curv_halfLie_eq_jacobiOp (V W : L) : curv (halfLie L) V W V = jacobiOp L V W := by
  rw [curv_halfLie, jacobiOp_apply, ← lie_skew ⁅V, W⁆ V, smul_neg, neg_smul]

/-- `K_V` is self-adjoint (needed for 20.5). -/
theorem jacobiOp_symm (hB : IsAdInvariant B) (V W W' : L) :
    B (jacobiOp L V W) W' = B W (jacobiOp L V W') := by
  rw [jacobiOp_apply, jacobiOp_apply, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul,
    smul_eq_mul, ad_skew hB, ad_skew hB V W ⁅V, W'⁆]
  ring

/-- `⟨K_V W, W⟩ = ¼|[V,W]|²`. -/
theorem jacobiOp_self (hB : IsAdInvariant B) (V W : L) :
    B (jacobiOp L V W) W = (1 / 4 : ℝ) * B ⁅V, W⁆ ⁅V, W⁆ := by
  rw [jacobiOp_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, ad_skew hB V ⁅V, W⁆ W]
  ring


theorem sq_nonneg_of_pos (hpos : ∀ x : L, x ≠ 0 → 0 < B x x) (x : L) : 0 ≤ B x x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact (hpos x hx).le

/-- `K_V` is positive semi-definite. -/
theorem jacobiOp_self_nonneg (hB : IsAdInvariant B) (hpos : ∀ x : L, x ≠ 0 → 0 < B x x) (V W : L) :
    0 ≤ B (jacobiOp L V W) W := by
  rw [jacobiOp_self hB]
  have := sq_nonneg_of_pos hpos ⁅V, W⁆
  positivity

/-- **Corollary 21.4**: the sectional curvature is `≥ 0`. -/
theorem sectional_nonneg (hB : IsAdInvariant B) (hpos : ∀ x : L, x ≠ 0 → 0 < B x x) (X Y : L) :
    0 ≤ B (curv (halfLie L) X Y X) Y := by
  rw [sectional hB]
  have := sq_nonneg_of_pos hpos ⁅X, Y⁆
  positivity

/-- 21.4 in the now usual sign convention `R_std = −R_Milnor`: `⟨R_std(X,Y)Y,X⟩ = ¼|[X,Y]|²`. -/
theorem sectional_std (hB : IsAdInvariant B) (X Y : L) :
    B (-curv (halfLie L) X Y Y) X = (1 / 4 : ℝ) * B ⁅X, Y⁆ ⁅X, Y⁆ := by
  rw [map_neg, LinearMap.neg_apply, curv_inner hB, ← lie_skew Y X, map_neg]
  ring

/-- **Corollary 21.4**: the sectional curvature vanishes iff `[X,Y] = 0`. -/
theorem sectional_eq_zero_iff (hB : IsAdInvariant B) (hpos : ∀ x : L, x ≠ 0 → 0 < B x x)
    (X Y : L) : B (curv (halfLie L) X Y X) Y = 0 ↔ ⁅X, Y⁆ = 0 := by
  rw [sectional hB]
  constructor
  · intro h
    by_contra hne
    have := hpos _ hne
    linarith
  · intro h; simp [h]

/-- The kernel of `K_V` is the centralizer of `V`. -/
theorem jacobiOp_eq_zero_iff (hB : IsAdInvariant B) (hpos : ∀ x : L, x ≠ 0 → 0 < B x x)
    (V W : L) : jacobiOp L V W = 0 ↔ ⁅V, W⁆ = 0 := by
  constructor
  · intro h
    have h1 := jacobiOp_self hB V W
    rw [h, map_zero, LinearMap.zero_apply] at h1
    by_contra hne
    have := hpos _ hne
    linarith
  · intro h; simp [jacobiOp_apply, h]

/-- The eigenvalues of `K_V` are `≥ 0` (p. 117). -/
theorem eigenvalue_nonneg (hB : IsAdInvariant B) (hpos : ∀ x : L, x ≠ 0 → 0 < B x x)
    {V W : L} {μ : ℝ} (hW : W ≠ 0) (h : jacobiOp L V W = μ • W) : 0 ≤ μ := by
  have h1 := jacobiOp_self_nonneg hB hpos V W
  rw [h, map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
  have h2 := hpos W hW
  by_contra hμ
  push Not at hμ
  nlinarith

/-- The skew-symmetric `ad_V` has no real eigenvalue other than `0`. -/
theorem ad_eigenvalue_eq_zero (hB : IsAdInvariant B) (hpos : ∀ x : L, x ≠ 0 → 0 < B x x)
    {V X : L} {a : ℝ} (hX : X ≠ 0) (h : ⁅V, X⁆ = a • X) : a = 0 := by
  have h1 := ad_skew hB V X X
  rw [h] at h1
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
  have h2 := hpos X hX
  have : a * B X X = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact h
  · linarith

/-- If `ad_V² W = −a² W` (`W` in a plane rotated by `ad_V` with speed `a`), then
`K_V W = (a²/4) W`. -/
theorem jacobiOp_of_lie_lie {V W : L} {a : ℝ} (h : ⁅V, ⁅V, W⁆⁆ = -(a ^ 2) • W) :
    jacobiOp L V W = (a ^ 2 / 4) • W := by
  rw [jacobiOp_apply, h, smul_smul]
  congr 1; ring

/-- Conversely `K_V W = μ W` gives `ad_V² W = −4μ W`. -/
theorem lie_lie_of_jacobiOp {V W : L} {μ : ℝ} (h : jacobiOp L V W = μ • W) :
    ⁅V, ⁅V, W⁆⁆ = -(4 * μ) • W := by
  rw [jacobiOp_apply] at h
  have : ⁅V, ⁅V, W⁆⁆ = (-4 : ℝ) • (-(1 / 4 : ℝ) • ⁅V, ⁅V, W⁆⁆) := by
    rw [smul_smul]; norm_num
  rw [this, h, smul_smul]
  congr 1; ring

/-- `ad_V` preserves every eigenspace of `K_V = −¼ ad_V²`. -/
theorem lie_mem_eigenspace {V W : L} {μ : ℝ} (h : W ∈ Module.End.eigenspace (jacobiOp L V) μ) :
    ⁅V, W⁆ ∈ Module.End.eigenspace (jacobiOp L V) μ := by
  rw [Module.End.mem_eigenspace_iff] at h ⊢
  rw [jacobiOp_apply] at h ⊢
  rw [← lie_smul, h, lie_smul]


/-- On the `μ`-eigenspace of `K_V` the map `(2√μ)⁻¹ ad_V`; for `μ > 0` it is a complex
structure (`Morse.eigenJ_comp_self`). -/
def eigenJ (V : L) {μ : ℝ} : Module.End.eigenspace (jacobiOp L V) μ →ₗ[ℝ]
    Module.End.eigenspace (jacobiOp L V) μ :=
  ((2 * Real.sqrt μ)⁻¹ • LieAlgebra.ad ℝ L V).restrict fun W hW => by
    simp only [LinearMap.smul_apply, LieAlgebra.ad_apply]
    exact Submodule.smul_mem _ _ (lie_mem_eigenspace hW)

theorem eigenJ_apply (V : L) {μ : ℝ} (W : Module.End.eigenspace (jacobiOp L V) μ) :
    (eigenJ V W : L) = (2 * Real.sqrt μ)⁻¹ • ⁅V, (W : L)⁆ := rfl

/-- For `μ > 0`, `(2√μ)⁻¹ ad_V` squares to `−1` on `E_μ`. -/
theorem eigenJ_comp_self (V : L) {μ : ℝ} (hμ : 0 < μ) :
    eigenJ V ∘ₗ eigenJ V =
      -LinearMap.id (R := ℝ) (M := Module.End.eigenspace (jacobiOp L V) μ) := by
  ext W
  have hW := W.2
  rw [Module.End.mem_eigenspace_iff] at hW
  have h := lie_lie_of_jacobiOp hW
  simp only [LinearMap.comp_apply, eigenJ_apply, lie_smul, smul_smul, h, LinearMap.neg_apply,
    LinearMap.id_apply, Submodule.coe_neg]
  have hs : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt hμ.le
  have hs0 : Real.sqrt μ ≠ 0 := (Real.sqrt_pos.2 hμ).ne'
  rw [← neg_one_smul ℝ (W : L)]
  congr 1
  field_simp
  nlinarith [hs]

/-- **The non-zero eigenvalues of `K_V` occur in pairs** (proof of 21.7, p. 117): each
eigenspace `E_μ`, `μ ≠ 0`, is even-dimensional. -/
theorem even_finrank_eigenspace [FiniteDimensional ℝ L] (hB : IsAdInvariant B)
    (hpos : ∀ x : L, x ≠ 0 → 0 < B x x) (V : L) {μ : ℝ} (hμ : μ ≠ 0) :
    Even (Module.finrank ℝ (Module.End.eigenspace (jacobiOp L V) μ)) := by
  rcases lt_or_gt_of_ne hμ with hneg | hpos'
  · have : Module.End.eigenspace (jacobiOp L V) μ = ⊥ := by
      rw [eq_bot_iff]
      intro W hW
      rw [Module.End.mem_eigenspace_iff] at hW
      by_contra hW0
      have := eigenvalue_nonneg hB hpos hW0 hW
      linarith
    rw [this, finrank_bot]
    exact ⟨0, rfl⟩
  · exact even_finrank_of_comp_self_eq_neg_id _ (eigenJ_comp_self V hpos')

/-- The complex structure `(2√μ)⁻¹ ad_V` on `E_μ` is orthogonal for `B`, so an orthonormal
basis of `E_μ` can be chosen in pairs `w, Jw` on which `ad_V` has Milnor's blocks
`(0 −2√μ; 2√μ 0)`. -/
theorem eigenJ_isometry (hB : IsAdInvariant B) (V : L) {μ : ℝ} (hμ : 0 < μ)
    (W W' : Module.End.eigenspace (jacobiOp L V) μ) :
    B (eigenJ V W) (eigenJ V W') = B W W' := by
  have hW' := W'.2
  rw [Module.End.mem_eigenspace_iff] at hW'
  have h := lie_lie_of_jacobiOp hW'
  simp only [eigenJ_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [ad_skew hB V (W : L) ⁅V, (W' : L)⁆, h]
  simp only [map_smul, smul_eq_mul]
  have hs : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt hμ.le
  have hs0 : Real.sqrt μ ≠ 0 := (Real.sqrt_pos.2 hμ).ne'
  field_simp
  rw [hs]
  ring

/-- The Ricci curvature `K(V,V) = tr K_V` is `−¼` of the Killing form (p. 115, written with
Mathlib's `killingForm`). -/
theorem trace_jacobiOp (V : L) :
    LinearMap.trace ℝ L (jacobiOp L V) = -(1 / 4 : ℝ) * killingForm ℝ L V V := by
  rw [jacobiOp, LinearMap.map_smul_of_tower, smul_eq_mul, LieModule.traceForm_apply_apply]
  rfl


/-- In a `B`-orthogonal basis the diagonal coefficient of `T` at `bᵢ` is
`B(T bᵢ, bᵢ)/B(bᵢ, bᵢ)`. -/
theorem trace_eq_sum_of_isOrtho {n : ℕ} (b : Module.Basis (Fin n) ℝ L)
    (hb : B.IsOrthoᵢ b) (T : Module.End ℝ L) (i : Fin n) :
    B (T (b i)) (b i) = b.repr (T (b i)) i * B (b i) (b i) := by
  conv_lhs => rw [← b.sum_repr (T (b i))]
  rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single i]
  · rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  · intro j _ hj
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hb hj, mul_zero]
  · simp

/-- **Corollary 21.5**, the algebraic step: if the centre of `𝔤` is trivial, the Ricci curvature
`tr K_V` is `> 0` for every `V ≠ 0`. -/
theorem trace_jacobiOp_pos [FiniteDimensional ℝ L] (hB : IsAdInvariant B)
    (hsymm : ∀ x y : L, B x y = B y x) (hpos : ∀ x : L, x ≠ 0 → 0 < B x x)
    (hc : LieAlgebra.center ℝ L = ⊥) {V : L} (hV : V ≠ 0) :
    0 < LinearMap.trace ℝ L (jacobiOp L V) := by
  have : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (B := B) (LinearMap.BilinForm.isSymm_iff.1 (LinearMap.BilinForm.isSymm_def.2 hsymm))
  rw [LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
  have hbi : ∀ i, 0 < B (b i) (b i) := fun i => hpos _ (b.ne_zero i)
  have hdiag : ∀ i, LinearMap.toMatrix b b (jacobiOp L V) i i =
      B (jacobiOp L V (b i)) (b i) / B (b i) (b i) := by
    intro i
    rw [LinearMap.toMatrix_apply, trace_eq_sum_of_isOrtho b hb, mul_div_cancel_right₀ _
      (hbi i).ne']
  simp only [Matrix.diag_apply, hdiag]
  -- some basis vector does not commute with `V`
  obtain ⟨i, hi⟩ : ∃ i, ⁅V, b i⁆ ≠ 0 := by
    by_contra h
    push Not at h
    have hcen : V ∈ LieAlgebra.center ℝ L := by
      rw [LieAlgebra.center, LieModule.mem_maxTrivSubmodule]
      intro x
      have : LieAlgebra.ad ℝ L V = 0 := b.ext fun i => by simpa using h i
      rw [← lie_skew, neg_eq_zero]
      exact LinearMap.congr_fun this x
    rw [hc] at hcen
    exact hV hcen
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun j =>
    B (jacobiOp L V (b j)) (b j) / B (b j) (b j))
    (fun j _ => div_nonneg (jacobiOp_self_nonneg hB hpos V (b j)) (hbi j).le) (Finset.mem_univ i))
  rw [jacobiOp_self hB]
  have := hpos _ hi
  have := hbi i
  positivity

/-- Equivalently, the Killing form is negative definite. -/
theorem killingForm_neg [FiniteDimensional ℝ L] (hB : IsAdInvariant B)
    (hsymm : ∀ x y : L, B x y = B y x) (hpos : ∀ x : L, x ≠ 0 → 0 < B x x)
    (hc : LieAlgebra.center ℝ L = ⊥) {V : L} (hV : V ≠ 0) :
    killingForm ℝ L V V < 0 := by
  have := trace_jacobiOp_pos hB hsymm hpos hc hV
  rw [trace_jacobiOp] at this
  linarith


/-- **Corollary 21.6**: `𝔤' = 𝔠^⊥`, the orthogonal complement of the centre, is a Lie ideal. -/
def centerCompl (hB : IsAdInvariant B) : LieIdeal ℝ L :=
  LieAlgebra.InvariantForm.orthogonal B ((isAdInvariant_iff_lieInvariant B).1 hB)
    (LieAlgebra.center ℝ L)

theorem mem_centerCompl (hB : IsAdInvariant B) (X : L) :
    X ∈ centerCompl hB ↔ ∀ C ∈ LieAlgebra.center ℝ L, B C X = 0 :=
  LieAlgebra.InvariantForm.mem_orthogonal _ _ _ _

/-- 21.6: `𝔤 = 𝔠 ⊕ 𝔤'`. -/
theorem isCompl_center_centerCompl [FiniteDimensional ℝ L] (hB : IsAdInvariant B)
    (hsymm : ∀ x y : L, B x y = B y x) (hpos : ∀ x : L, x ≠ 0 → 0 < B x x) :
    IsCompl (LieAlgebra.center ℝ L).toSubmodule (centerCompl hB).toSubmodule := by
  rw [centerCompl, LieAlgebra.InvariantForm.orthogonal_toSubmodule,
    LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint
      (LinearMap.BilinForm.isSymm_def.2 hsymm).isRefl]
  rw [Submodule.disjoint_def]
  intro x hx hx'
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx'
  by_contra h
  have := hpos x h
  rw [hx' x hx] at this
  exact lt_irrefl _ this

/-- 21.6: `𝔤'` has trivial centre. -/
theorem eq_zero_of_mem_centerCompl [FiniteDimensional ℝ L] (hB : IsAdInvariant B)
    (hsymm : ∀ x y : L, B x y = B y x) (hpos : ∀ x : L, x ≠ 0 → 0 < B x x) {X : L}
    (hX : X ∈ centerCompl hB) (hcomm : ∀ Y ∈ centerCompl hB, ⁅X, Y⁆ = 0) : X = 0 := by
  have hcompl := isCompl_center_centerCompl hB hsymm hpos
  have hcen : X ∈ LieAlgebra.center ℝ L := by
    rw [LieAlgebra.center, LieModule.mem_maxTrivSubmodule]
    intro Z
    have hZ : Z ∈ (LieAlgebra.center ℝ L).toSubmodule ⊔ (centerCompl hB).toSubmodule := by
      rw [hcompl.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨c, hc, y, hy, rfl⟩ := Submodule.mem_sup.1 hZ
    have hc' : ⁅c, X⁆ = 0 := by
      rw [← lie_skew, (LieModule.mem_maxTrivSubmodule ℝ L L c).1 hc X, neg_zero]
    rw [add_lie, hc', zero_add, ← lie_skew, hcomm y hy, neg_zero]
  have : X ∈ (LieAlgebra.center ℝ L).toSubmodule ⊓ (centerCompl hB).toSubmodule := ⟨hcen, hX⟩
  rw [hcompl.inf_eq_bot] at this
  exact this

/-- Milnor's footnote, p. 114: `(X,Y,Z) ↦ ⟨[X,Y],Z⟩` changes sign under `X ↔ Y` … -/
theorem cartan_form_swap₁₂ (X Y Z : L) : B ⁅Y, X⁆ Z = -B ⁅X, Y⁆ Z := by
  rw [← lie_skew, map_neg, LinearMap.neg_apply]

/-- … and under `Y ↔ Z`, hence is alternating: Cartan's left-invariant 3-form. -/
theorem cartan_form_swap₂₃ (hB : IsAdInvariant B) (X Y Z : L) : B ⁅X, Z⁆ Y = -B ⁅X, Y⁆ Z := by
  rw [hB, hB, ← lie_skew, map_neg]

end Morse
