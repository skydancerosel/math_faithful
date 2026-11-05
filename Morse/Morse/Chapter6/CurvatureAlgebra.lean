import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
Milnor, *Morse Theory*, §9 (The curvature tensor), pp. 51–54, and the remark on sectional
curvature on p. 100 (§19).

# The algebra of the curvature tensor

## Milnor's text, paraphrased

* **Definition** (p. 51).  For an affine connection `⊢` and vector fields `X, Y, Z`,
  `R(X, Y)Z = −X ⊢ (Y ⊢ Z) + Y ⊢ (X ⊢ Z) + [X, Y] ⊢ Z`.  A footnote says that Nomizu uses the
  opposite sign, and that Milnor's sign makes `⟨R(∂_h, ∂_i)∂_j, ∂_k⟩` the classical symbol
  `R_{hijk}`.
* **Lemma 9.1** (p. 51).  `R(X, Y)Z` at `p` depends only on `X_p, Y_p, Z_p`, and is trilinear in
  them: `R` is a tensor.
* **Lemma 9.3** (p. 53).  The curvature tensor of a Riemannian manifold satisfies
  (1) `R(X, Y)Z + R(Y, X)Z = 0`;
  (2) `R(X, Y)Z + R(Y, Z)X + R(Z, X)Y = 0`;
  (3) `⟨R(X, Y)Z, W⟩ + ⟨R(X, Y)W, Z⟩ = 0`;
  (4) `⟨R(X, Y)Z, W⟩ = ⟨R(Z, W)X, Y⟩`.
  (1) is immediate; (2) uses the symmetry of the connection; (3) is "clearly equivalent" to
  `⟨R(X, Y)Z, Z⟩ = 0`, which uses compatibility with the metric; (4) "may be proved from (1),
  (2), and (3)": the six quantities `⟨R(·,·)·,·⟩` are placed at the vertices of an octahedron
  with four shaded faces, each of which is an instance of (2) up to (1) and (3); adding the
  identities of the top two faces and subtracting those of the bottom two shows that twice the
  top vertex minus twice the bottom vertex is zero (p. 54).
* **Sectional curvature** (p. 100, remark after Lemma 19.1).  For orthonormal `A, B ∈ TM_p`,
  `⟨R(A, B)A, B⟩` is the *sectional curvature* determined by `A` and `B`.

## What is formalized here

By Lemma 9.1, at a point `p` the curvature is a trilinear map `TM_p³ → TM_p`, and everything in
Lemma 9.3 (4) and in the theory of sectional curvature is linear algebra on the inner product
space `TM_p`.  Here `E` is any real inner product space and `R : E →ₗ E →ₗ E →ₗ E`, `R X Y Z`
standing for `R(X, Y)Z`.

* `Morse.octahedron`: Milnor's octahedron argument, for any function `T(X, Y, Z, W)` (no linearity
  needed) that is skew in `(X, Y)`, skew in `(Z, W)` and satisfies the cyclic identity in
  `(X, Y, Z)`: then `T(X, Y, Z, W) = T(Z, W, X, Y)`.
* `Morse.IsCurvatureTensor R`: identities (1), (2), (3) of Lemma 9.3;
  `Morse.IsCurvatureTensor.inner_comm_pairs`: identity (4).
* `Morse.inner_add_inner_eq_zero_iff`: (3) for fixed `X, Y` is equivalent to
  `⟨R(X, Y)Z, Z⟩ = 0` for all `Z` (Milnor's "clearly equivalent", p. 53).
* `Morse.sectionalCurvature R X Y = ⟨R(X, Y)X, Y⟩ / (‖X‖²‖Y‖² − ⟨X, Y⟩²)`, Milnor's sign.
  `Morse.IsCurvatureTensor.sectionalCurvature_smul_add`: it depends only on the plane spanned by
  `X` and `Y` (it is unchanged under `(X, Y) ↦ (aX + bY, cX + dY)`, `ad − bc ≠ 0`).
* **Polarization** (`Morse.IsCurvatureTensor.polarization`): `6⟨R(X, Y)Z, W⟩` is an explicit
  combination of the values `k(A, B) = ⟨R(A, B)A, B⟩` at sums of `X, Y, Z, W`.
* **The sectional curvatures determine `R`** (`Morse.IsCurvatureTensor.ext`,
  `Morse.IsCurvatureTensor.ext_of_sectionalCurvature`,
  `Morse.IsCurvatureTensor.ext_of_orthonormal`): two tensors satisfying (1)–(3) with the same
  `⟨R(X, Y)X, Y⟩` for all `X, Y`, or the same sectional curvature on all linearly independent
  pairs, or the same `⟨R(A, B)A, B⟩` on all orthonormal pairs (Milnor's definition), are equal.
* **Constant curvature** (`Morse.curvatureOne`,
  `Morse.IsCurvatureTensor.eq_smul_curvatureOne_of_orthonormal`,
  `Morse.IsCurvatureTensor.apply_eq_of_sectionalCurvature_eq`): if all sectional curvatures equal
  `κ`, then `R(X, Y)Z = κ(⟨X, Z⟩Y − ⟨Y, Z⟩X)`, and this tensor satisfies (1)–(3) and has
  sectional curvature `κ`.

## Sign conventions

Milnor's `R` is the negative of the curvature of Nomizu (and of Kobayashi–Nomizu, Lee and most
modern texts), `R^std(X, Y)Z = ∇_X∇_Y Z − ∇_Y∇_X Z − ∇_{[X,Y]}Z`:
`R_Milnor = −R^std`.  Identities (1)–(4) are invariant under `R ↦ −R`
(`Morse.IsCurvatureTensor.neg`).  The sectional curvature is the same number in both conventions,
written `⟨R(X, Y)X, Y⟩` with Milnor's sign and `⟨R^std(X, Y)Y, X⟩` with the standard one
(`Morse.IsCurvatureTensor.inner_neg_apply_swap`).  In constant curvature `κ`,
`R(X, Y)Z = κ(⟨X, Z⟩Y − ⟨Y, Z⟩X)` with Milnor's sign, `R^std(X, Y)Z = κ(⟨Y, Z⟩X − ⟨X, Z⟩Y)` with
the standard one (`Morse.neg_smul_curvatureOne_apply`).  Mathlib (v4.33.1) does not define the
curvature of a connection (it has the torsion `∇_X Y − ∇_Y X − [X, Y]` and metric compatibility,
see `Morse/Chapter6/Connection.lean`), so there is no Mathlib sign to reconcile yet.

## What Milnor leaves implicit, and how it is handled

* **The octahedron** (p. 54).  Each shaded face is an instance of (2) only after rearranging its
  three vertices with (1) and (3); the signs are left to the reader.  `Morse.octahedron` writes
  out the four face identities: with `T = ⟨R(X,Y)Z,W⟩`, `B = ⟨R(Z,W)X,Y⟩`,
  `L = ⟨R(X,W)Y,Z⟩`, `K = ⟨R(Y,W)Z,X⟩`, `Q = ⟨R(Y,Z)X,W⟩`, `F = ⟨R(Z,X)Y,W⟩` they read
  `T + Q + F = 0`, `T + K + L = 0`, `Q + B + K = 0`, `B + L + F = 0`.  No linearity of `R` is
  used, only the three identities.
* **"Clearly equivalent"** (p. 53).  (3) ⟺ `⟨R(X, Y)Z, Z⟩ = 0` is the polarization of a bilinear
  form; it needs linearity in `Z` (`Morse.inner_add_inner_eq_zero_iff`).
* **Sectional curvature** (p. 100).  Milnor defines it for an orthonormal pair `A, B` and calls
  it the sectional curvature "determined by `A` and `B`"; that it depends only on the plane, and
  that these numbers determine `R`, are not stated in the book.  Both are proved here
  (Lemma 7.1 and Lemma 7.2 of the exposition).
* **Lemma 9.3 (2) and (3) on a manifold.**  Milnor proves (2) and (3) by choosing extensions
  with vanishing brackets and using symmetry, resp. compatibility, of the connection.  Those
  steps are differential-geometric and are not formalized (Mathlib has no curvature tensor):
  here (1)–(3) are hypotheses.
-/

open RealInnerProductSpace

noncomputable section

namespace Morse

/-! ### Milnor's octahedron -/

/-- **Milnor's octahedron** (p. 54).  Let `T(X, Y, Z, W)` be skew-symmetric in `(X, Y)` (Lemma 9.3
(1)), skew-symmetric in `(Z, W)` (Lemma 9.3 (3)) and satisfy the cyclic identity in `(X, Y, Z)`
(Lemma 9.3 (2)).  Then `T(X, Y, Z, W) = T(Z, W, X, Y)` (Lemma 9.3 (4)).  The four face identities
are `fW`, `fZ`, `fX`, `fY`; adding the first two and subtracting the last two gives `2T − 2B = 0`.
No linearity of `T` is needed. -/
theorem octahedron {α : Type*} (T : α → α → α → α → ℝ)
    (h1 : ∀ X Y Z W, T X Y Z W + T Y X Z W = 0)
    (h3 : ∀ X Y Z W, T X Y Z W + T X Y W Z = 0)
    (h2 : ∀ X Y Z W, T X Y Z W + T Y Z X W + T Z X Y W = 0) (X Y Z W : α) :
    T X Y Z W = T Z W X Y := by
  -- face `W`: `T + Q + F = 0`
  have fW := h2 X Y Z W
  -- face `Z`: `−(T + K + L) = 0`
  have fZ := h2 X Y W Z
  have := h3 X Y Z W
  have := h3 Y W Z X
  have := h1 W X Y Z
  -- face `X`: `−(Q + B + K) = 0`
  have fX := h2 Y Z W X
  have := h3 Y Z X W
  have := h3 Z W X Y
  have := h1 W Y Z X
  -- face `Y`: `B + L + F = 0`
  have fY := h2 Z W X Y
  have := h1 W X Z Y
  have := h3 X W Z Y
  have := h1 X Z W Y
  have := h3 Z X W Y
  linarith

/-! ### Curvature tensors on an inner product space -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Milnor's "clearly equivalent"** (p. 53).  For a linear map `T` (here `T = R(X, Y)`), the
bilinear form `⟨T Z, W⟩` is skew-symmetric iff `⟨T Z, Z⟩ = 0` for every `Z`. -/
theorem inner_add_inner_eq_zero_iff (T : E →ₗ[ℝ] E) :
    (∀ Z W, ⟪T Z, W⟫ + ⟪T W, Z⟫ = 0) ↔ ∀ Z, ⟪T Z, Z⟫ = 0 := by
  constructor
  · intro h Z
    linarith [h Z Z]
  · intro h Z W
    have := h (Z + W)
    rw [map_add, inner_add_left, inner_add_right, inner_add_right, h Z, h W] at this
    linarith

/-- The identities (1), (2), (3) of **Lemma 9.3** (p. 53) for a trilinear map `R`, `R X Y Z`
standing for Milnor's `R(X, Y)Z` at a point. -/
structure IsCurvatureTensor (R : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E) : Prop where
  /-- Lemma 9.3 (1): `R(X, Y)Z + R(Y, X)Z = 0`. -/
  add_swap : ∀ X Y Z, R X Y Z + R Y X Z = 0
  /-- Lemma 9.3 (2), the first Bianchi identity: `R(X, Y)Z + R(Y, Z)X + R(Z, X)Y = 0`. -/
  bianchi : ∀ X Y Z, R X Y Z + R Y Z X + R Z X Y = 0
  /-- Lemma 9.3 (3): `⟨R(X, Y)Z, W⟩ + ⟨R(X, Y)W, Z⟩ = 0`. -/
  inner_add_inner : ∀ X Y Z W, ⟪R X Y Z, W⟫ + ⟪R X Y W, Z⟫ = 0

namespace IsCurvatureTensor

variable {R R' : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E}

theorem apply_swap (hR : IsCurvatureTensor R) (X Y Z : E) : R Y X Z = -R X Y Z :=
  eq_neg_of_add_eq_zero_right (hR.add_swap X Y Z)

theorem apply_self (hR : IsCurvatureTensor R) (X : E) : R X X = 0 := by
  ext Z
  have h := hR.add_swap X X Z
  rw [← two_smul ℝ, smul_eq_zero] at h
  simpa using h

theorem inner_swap (hR : IsCurvatureTensor R) (X Y Z W : E) :
    ⟪R X Y W, Z⟫ = -⟪R X Y Z, W⟫ :=
  eq_neg_of_add_eq_zero_right (hR.inner_add_inner X Y Z W)

theorem inner_apply_self (hR : IsCurvatureTensor R) (X Y Z : E) : ⟪R X Y Z, Z⟫ = 0 :=
  (inner_add_inner_eq_zero_iff (R X Y)).1 (hR.inner_add_inner X Y) Z

/-- The first Bianchi identity paired with `W`. -/
theorem inner_bianchi (hR : IsCurvatureTensor R) (X Y Z W : E) :
    ⟪R X Y Z, W⟫ + ⟪R Y Z X, W⟫ + ⟪R Z X Y, W⟫ = 0 := by
  rw [← inner_add_left, ← inner_add_left, hR.bianchi, inner_zero_left]

/-- **Lemma 9.3 (4)** (p. 53): `⟨R(X, Y)Z, W⟩ = ⟨R(Z, W)X, Y⟩`, by Milnor's octahedron. -/
theorem inner_comm_pairs (hR : IsCurvatureTensor R) (X Y Z W : E) :
    ⟪R X Y Z, W⟫ = ⟪R Z W X, Y⟫ :=
  octahedron (fun X Y Z W => ⟪R X Y Z, W⟫)
    (fun X Y Z W => by rw [← inner_add_left, hR.add_swap, inner_zero_left])
    hR.inner_add_inner hR.inner_bianchi X Y Z W

/-- The standard curvature `−R` satisfies (1)–(3) whenever Milnor's `R` does. -/
theorem neg (hR : IsCurvatureTensor R) : IsCurvatureTensor (-R) where
  add_swap X Y Z := by
    simp only [LinearMap.neg_apply]
    rw [← neg_add, hR.add_swap, neg_zero]
  bianchi X Y Z := by
    simp only [LinearMap.neg_apply]
    rw [← neg_add, ← neg_add, hR.bianchi, neg_zero]
  inner_add_inner X Y Z W := by
    simp only [LinearMap.neg_apply, inner_neg_left]
    rw [← neg_add, hR.inner_add_inner, neg_zero]

theorem smul (hR : IsCurvatureTensor R) (c : ℝ) : IsCurvatureTensor (c • R) where
  add_swap X Y Z := by simp [← smul_add, hR.add_swap X Y Z]
  bianchi X Y Z := by simp [← smul_add, hR.bianchi X Y Z]
  inner_add_inner X Y Z W := by
    simp only [LinearMap.smul_apply, inner_smul_left, conj_trivial, ← mul_add,
      hR.inner_add_inner X Y Z W, mul_zero]

/-- **The sectional curvature does not depend on the sign convention**: with the standard
curvature `R^std = −R`, the expression `⟨R^std(X, Y)Y, X⟩` equals Milnor's `⟨R(X, Y)X, Y⟩`. -/
theorem inner_neg_apply_swap (hR : IsCurvatureTensor R) (X Y : E) :
    ⟪(-R) X Y Y, X⟫ = ⟪R X Y X, Y⟫ := by
  simp only [LinearMap.neg_apply, inner_neg_left]
  rw [hR.inner_swap, neg_neg]

end IsCurvatureTensor

/-! ### Sectional curvature -/

/-- **Sectional curvature**, with Milnor's sign (p. 100): for linearly independent `X, Y`,
`K(X, Y) = ⟨R(X, Y)X, Y⟩ / (‖X‖²‖Y‖² − ⟨X, Y⟩²)`.  For an orthonormal pair `A, B` this is
Milnor's `⟨R(A, B)A, B⟩`.  (For linearly dependent `X, Y` the denominator vanishes and Lean's
convention gives `0`.) -/
def sectionalCurvature (R : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E) (X Y : E) : ℝ :=
  ⟪R X Y X, Y⟫ / (‖X‖ ^ 2 * ‖Y‖ ^ 2 - ⟪X, Y⟫ ^ 2)

/-- The Gram determinant of `(aX + bY, cX + dY)` is `(ad − bc)²` times that of `(X, Y)`. -/
theorem gram_smul_add (X Y : E) (a b c d : ℝ) :
    ‖a • X + b • Y‖ ^ 2 * ‖c • X + d • Y‖ ^ 2 - ⟪a • X + b • Y, c • X + d • Y⟫ ^ 2 =
      (a * d - b * c) ^ 2 * (‖X‖ ^ 2 * ‖Y‖ ^ 2 - ⟪X, Y⟫ ^ 2) := by
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_comm X Y]
  ring

/-- The Gram determinant of a linearly independent pair is positive. -/
theorem gram_pos {X Y : E} (h : LinearIndependent ℝ ![X, Y]) :
    0 < ‖X‖ ^ 2 * ‖Y‖ ^ 2 - ⟪X, Y⟫ ^ 2 := by
  rw [LinearIndependent.pair_iff] at h
  have hY : Y ≠ 0 := by
    rintro rfl
    simpa using h 0 1 (by simp)
  set u := ⟪Y, Y⟫ • X - ⟪X, Y⟫ • Y with hu
  have hu0 : u ≠ 0 := by
    intro h0
    have := (h ⟪Y, Y⟫ (-⟪X, Y⟫) (by rw [neg_smul, ← sub_eq_add_neg]; exact h0)).1
    exact hY (inner_self_eq_zero.1 this)
  have key : ⟪u, u⟫ = ⟪Y, Y⟫ * (⟪X, X⟫ * ⟪Y, Y⟫ - ⟪X, Y⟫ ^ 2) := by
    simp only [hu, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm X Y]
    ring
  have hpos : 0 < ⟪u, u⟫ := real_inner_self_pos.2 hu0
  rw [key] at hpos
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hpos
  exact pos_of_mul_pos_right hpos (by positivity)

namespace IsCurvatureTensor

variable {R R' : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E}

/-- `R(aX + bY, cX + dY) = (ad − bc) R(X, Y)`. -/
theorem apply_smul_add (hR : IsCurvatureTensor R) (X Y : E) (a b c d : ℝ) :
    R (a • X + b • Y) (c • X + d • Y) = (a * d - b * c) • R X Y := by
  have hYX : R Y X = -R X Y := by
    ext Z
    simp [hR.apply_swap X Y Z]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hR.apply_self, hYX,
    smul_zero, zero_add, add_zero, smul_neg, smul_smul]
  module

/-- The numerator `⟨R(X, Y)X, Y⟩` of the sectional curvature gets multiplied by `(ad − bc)²`
under `(X, Y) ↦ (aX + bY, cX + dY)`. -/
theorem inner_apply_smul_add (hR : IsCurvatureTensor R) (X Y : E) (a b c d : ℝ) :
    ⟪R (a • X + b • Y) (c • X + d • Y) (a • X + b • Y), c • X + d • Y⟫ =
      (a * d - b * c) ^ 2 * ⟪R X Y X, Y⟫ := by
  rw [hR.apply_smul_add]
  simp only [LinearMap.smul_apply, map_add, map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hR.inner_apply_self, hR.inner_swap X Y Y X]
  ring

/-- `inner_apply_smul_add` with the substitution done by the caller. -/
theorem inner_apply_self_eq (hR : IsCurvatureTensor R) {X Y A B : E} {a b c d : ℝ}
    (hX : X = a • A + b • B) (hY : Y = c • A + d • B) :
    ⟪R X Y X, Y⟫ = (a * d - b * c) ^ 2 * ⟪R A B A, B⟫ := by
  subst hX hY
  exact hR.inner_apply_smul_add A B a b c d

/-- **The sectional curvature depends only on the plane** (exposition, Lemma 7.1): it is
unchanged under `(X, Y) ↦ (aX + bY, cX + dY)` with `ad − bc ≠ 0`. -/
theorem sectionalCurvature_smul_add (hR : IsCurvatureTensor R) (X Y : E) {a b c d : ℝ}
    (h : a * d - b * c ≠ 0) :
    sectionalCurvature R (a • X + b • Y) (c • X + d • Y) = sectionalCurvature R X Y := by
  rw [sectionalCurvature, sectionalCurvature, hR.inner_apply_smul_add, gram_smul_add,
    mul_div_mul_left _ _ (pow_ne_zero 2 h)]

/-- For a linearly dependent pair, `⟨R(X, Y)X, Y⟩ = 0`. -/
theorem inner_apply_self_eq_zero_of_not_linearIndependent (hR : IsCurvatureTensor R) {X Y : E}
    (h : ¬ LinearIndependent ℝ ![X, Y]) : ⟪R X Y X, Y⟫ = 0 := by
  rw [LinearIndependent.pair_iff] at h
  push Not at h
  obtain ⟨s, t, hst, hne⟩ := h
  have hRXY : R X Y = 0 := by
    by_cases hs : s = 0
    · have hY : Y = 0 := by
        rw [hs, zero_smul, zero_add] at hst
        exact (smul_eq_zero.1 hst).resolve_left (hne hs)
      rw [hY, map_zero]
    · have hX : X = (-(t / s)) • Y := by
        have h1 : s • X = -(t • Y) := eq_neg_of_add_eq_zero_left hst
        calc X = s⁻¹ • (s • X) := by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
          _ = (-(t / s)) • Y := by rw [h1, smul_neg, smul_smul, ← neg_smul, inv_mul_eq_div]
      rw [hX, map_smul, LinearMap.smul_apply, hR.apply_self, smul_zero]
  rw [hRXY, LinearMap.zero_apply, inner_zero_left]

end IsCurvatureTensor

/-! ### Polarization: the sectional curvatures determine `R` -/

/-- The second mixed difference of a function `k` of two vectors,
`Δ_{A,C} Δ_{B,D} k = k(A+C, B+D) − k(A, B+D) − k(C, B+D) − k(A+C, B) + k(A, B) + k(C, B)
− k(A+C, D) + k(A, D) + k(C, D)`. -/
def mixedDiff (k : E → E → ℝ) (A C B D : E) : ℝ :=
  k (A + C) (B + D) - k A (B + D) - k C (B + D) - k (A + C) B + k A B + k C B
    - k (A + C) D + k A D + k C D

/-- **Gram–Schmidt for the sectional curvature.**  For any `X, Y`, either `⟨R(X, Y)X, Y⟩ = 0`
for every `R` satisfying (1)–(3) (`X, Y` linearly dependent), or there are an orthonormal pair
`A, B` and a constant `c` with `⟨R(X, Y)X, Y⟩ = c ⟨R(A, B)A, B⟩` for every such `R`
(`A = X/‖X‖`, `B` the normalized component of `Y` orthogonal to `A`). -/
theorem inner_apply_self_eq_zero_or_exists_orthonormal (X Y : E) :
    (∀ R : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E, IsCurvatureTensor R → ⟪R X Y X, Y⟫ = 0) ∨
    ∃ A B : E, ‖A‖ = 1 ∧ ‖B‖ = 1 ∧ ⟪A, B⟫ = 0 ∧ ∃ c : ℝ,
      ∀ R : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E, IsCurvatureTensor R → ⟪R X Y X, Y⟫ = c * ⟪R A B A, B⟫ := by
  by_cases hX : X = 0
  · left
    intro R _
    simp [hX]
  have hXn : ‖X‖ ≠ 0 := norm_ne_zero_iff.2 hX
  obtain ⟨A, hA⟩ : ∃ A : E, A = ‖X‖⁻¹ • X := ⟨_, rfl⟩
  have hAn : ‖A‖ = 1 := by
    rw [hA, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hXn]
  have hAA : ⟪A, A⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hAn, one_pow]
  obtain ⟨Y', hY'⟩ : ∃ Y' : E, Y' = Y - ⟪A, Y⟫ • A := ⟨_, rfl⟩
  by_cases hY'0 : Y' = 0
  · left
    intro R hR
    have hY : Y = (⟪A, Y⟫ * ‖X‖⁻¹) • X := by
      rw [← smul_smul, ← hA]
      exact sub_eq_zero.1 (hY' ▸ hY'0)
    rw [hY]
    simp [hR.apply_self]
  right
  have hY'n : ‖Y'‖ ≠ 0 := norm_ne_zero_iff.2 hY'0
  obtain ⟨B, hB⟩ : ∃ B : E, B = ‖Y'‖⁻¹ • Y' := ⟨_, rfl⟩
  have hBn : ‖B‖ = 1 := by
    rw [hB, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hY'n]
  have hAB : ⟪A, B⟫ = 0 := by
    rw [hB, real_inner_smul_right, hY', inner_sub_right, real_inner_smul_right, hAA, mul_one,
      sub_self, mul_zero]
  have hX' : X = ‖X‖ • A + (0 : ℝ) • B := by
    rw [zero_smul, add_zero, hA, smul_smul, mul_inv_cancel₀ hXn, one_smul]
  have hY : Y = ⟪A, Y⟫ • A + ‖Y'‖ • B := by
    rw [hB, smul_smul, mul_inv_cancel₀ hY'n, one_smul, hY', add_sub_cancel]
  refine ⟨A, B, hAn, hBn, hAB, (‖X‖ * ‖Y'‖ - 0 * ⟪A, Y⟫) ^ 2, fun R hR => ?_⟩
  exact hR.inner_apply_self_eq hX' hY

namespace IsCurvatureTensor

variable {R R' : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E}

/-- The mixed difference of `k(A, B) = ⟨R(A, B)A, B⟩` is `2(⟨R(A, B)C, D⟩ + ⟨R(A, D)C, B⟩)`. -/
theorem mixedDiff_eq (hR : IsCurvatureTensor R) (A C B D : E) :
    mixedDiff (fun X Y => ⟪R X Y X, Y⟫) A C B D = 2 * (⟪R A B C, D⟫ + ⟪R A D C, B⟫) := by
  simp only [mixedDiff, map_add, LinearMap.add_apply, inner_add_left, inner_add_right]
  linarith [hR.inner_comm_pairs C B A D, hR.inner_comm_pairs C D A B]

/-- **Polarization**: `⟨R(X, Y)Z, W⟩` is determined by the values `k(A, B) = ⟨R(A, B)A, B⟩`:
`6⟨R(X, Y)Z, W⟩ = 2 Δ_{X,Z}Δ_{Y,W} k + Δ_{Y,X}Δ_{Z,W} k`. -/
theorem polarization (hR : IsCurvatureTensor R) (X Y Z W : E) :
    6 * ⟪R X Y Z, W⟫ = 2 * mixedDiff (fun A B => ⟪R A B A, B⟫) X Z Y W +
      mixedDiff (fun A B => ⟪R A B A, B⟫) Y X Z W := by
  rw [hR.mixedDiff_eq, hR.mixedDiff_eq]
  have hb : ⟪R X W Z, Y⟫ = -⟪R Y Z X, W⟫ := by
    rw [hR.inner_comm_pairs X W Z Y, hR.apply_swap, inner_neg_left]
  have hc : ⟪R Y W X, Z⟫ = -⟪R Z X Y, W⟫ := by
    rw [hR.inner_comm_pairs Y W X Z, hR.apply_swap, inner_neg_left]
  linarith [hR.inner_bianchi X Y Z W]

/-- **The sectional curvatures determine the curvature tensor** (exposition, Lemma 7.2): two
trilinear maps satisfying (1)–(3) of Lemma 9.3 with `⟨R(X, Y)X, Y⟩ = ⟨R'(X, Y)X, Y⟩` for all
`X, Y` are equal. -/
theorem ext (hR : IsCurvatureTensor R) (hR' : IsCurvatureTensor R')
    (h : ∀ X Y, ⟪R X Y X, Y⟫ = ⟪R' X Y X, Y⟫) : R = R' := by
  have hk : (fun A B => ⟪R A B A, B⟫) = fun A B => ⟪R' A B A, B⟫ := funext₂ h
  ext X Y Z
  refine ext_inner_right ℝ fun W => ?_
  have h1 := hR.polarization X Y Z W
  have h2 := hR'.polarization X Y Z W
  rw [hk] at h1
  linarith

/-- **The sectional curvatures determine the curvature tensor**, in terms of
`sectionalCurvature` on linearly independent pairs. -/
theorem ext_of_sectionalCurvature (hR : IsCurvatureTensor R) (hR' : IsCurvatureTensor R')
    (h : ∀ X Y, LinearIndependent ℝ ![X, Y] →
      sectionalCurvature R X Y = sectionalCurvature R' X Y) : R = R' := by
  refine hR.ext hR' fun X Y => ?_
  by_cases hXY : LinearIndependent ℝ ![X, Y]
  · have hg := (gram_pos hXY).ne'
    have := h X Y hXY
    rw [sectionalCurvature, sectionalCurvature, div_left_inj' hg] at this
    exact this
  · rw [hR.inner_apply_self_eq_zero_of_not_linearIndependent hXY,
      hR'.inner_apply_self_eq_zero_of_not_linearIndependent hXY]

/-- **The sectional curvatures in Milnor's sense determine the curvature tensor** (p. 100): if
`⟨R(A, B)A, B⟩ = ⟨R'(A, B)A, B⟩` for every orthonormal pair `A, B`, then `R = R'`. -/
theorem ext_of_orthonormal (hR : IsCurvatureTensor R) (hR' : IsCurvatureTensor R')
    (h : ∀ A B, ‖A‖ = 1 → ‖B‖ = 1 → ⟪A, B⟫ = 0 → ⟪R A B A, B⟫ = ⟪R' A B A, B⟫) : R = R' := by
  refine hR.ext hR' fun X Y => ?_
  rcases inner_apply_self_eq_zero_or_exists_orthonormal X Y with h0 | ⟨A, B, hA, hB, hAB, c, hc⟩
  · rw [h0 R hR, h0 R' hR']
  · rw [hc R hR, hc R' hR', h A B hA hB hAB]

end IsCurvatureTensor

/-! ### Constant curvature -/

/-- The curvature tensor of constant sectional curvature `1`, with Milnor's sign:
`R₁(X, Y)Z = ⟨X, Z⟩Y − ⟨Y, Z⟩X`. -/
def curvatureOne : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E :=
  LinearMap.mk₂ ℝ (fun X Y => (innerₗ E X).smulRight Y - (innerₗ E Y).smulRight X)
    (fun X X' Y => by ext Z; simp [add_smul]; abel)
    (fun c X Y => by ext Z; simp [smul_sub, smul_smul, mul_comm])
    (fun X Y Y' => by ext Z; simp [add_smul]; abel)
    (fun c X Y => by ext Z; simp [smul_sub, smul_smul, mul_comm])

@[simp] theorem curvatureOne_apply (X Y Z : E) :
    (curvatureOne : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E) X Y Z = ⟪X, Z⟫ • Y - ⟪Y, Z⟫ • X := by
  simp [curvatureOne]

/-- `R₁(X, Y)Z = ⟨X, Z⟩Y − ⟨Y, Z⟩X` satisfies (1)–(3) of Lemma 9.3. -/
theorem isCurvatureTensor_curvatureOne :
    IsCurvatureTensor (curvatureOne : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E) where
  add_swap X Y Z := by simp
  bianchi X Y Z := by
    simp only [curvatureOne_apply, real_inner_comm X Y, real_inner_comm X Z, real_inner_comm Y Z]
    abel
  inner_add_inner X Y Z W := by
    simp only [curvatureOne_apply, inner_sub_left, real_inner_smul_left]
    ring

/-- `⟨R₁(X, Y)X, Y⟩ = ‖X‖²‖Y‖² − ⟨X, Y⟩²`: `R₁` has sectional curvature `1`. -/
theorem inner_curvatureOne_self (X Y : E) :
    ⟪(curvatureOne : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E) X Y X, Y⟫ = ‖X‖ ^ 2 * ‖Y‖ ^ 2 - ⟪X, Y⟫ ^ 2 := by
  simp only [curvatureOne_apply, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, real_inner_comm X Y]
  ring

theorem sectionalCurvature_smul_curvatureOne (κ : ℝ) {X Y : E}
    (h : LinearIndependent ℝ ![X, Y]) :
    sectionalCurvature (κ • (curvatureOne : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E)) X Y = κ := by
  rw [sectionalCurvature, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    real_inner_smul_left, inner_curvatureOne_self, mul_div_assoc, div_self (gram_pos h).ne',
    mul_one]

/-- **Constant curvature with the standard sign**: `−κR₁(X, Y)Z = κ(⟨Y, Z⟩X − ⟨X, Z⟩Y)`. -/
theorem neg_smul_curvatureOne_apply (κ : ℝ) (X Y Z : E) :
    (-(κ • (curvatureOne : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E))) X Y Z = κ • (⟪Y, Z⟫ • X - ⟪X, Z⟫ • Y) := by
  simp only [LinearMap.neg_apply, LinearMap.smul_apply, curvatureOne_apply, ← smul_neg, neg_sub]

namespace IsCurvatureTensor

variable {R : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E}

/-- **Constant curvature** (exposition, Corollary 7.3), with Milnor's definition of sectional
curvature (p. 100): if `⟨R(A, B)A, B⟩ = κ` for every orthonormal pair `A, B`, then
`R = κ R₁`, i.e. `R(X, Y)Z = κ(⟨X, Z⟩Y − ⟨Y, Z⟩X)`. -/
theorem eq_smul_curvatureOne_of_orthonormal (hR : IsCurvatureTensor R) (κ : ℝ)
    (h : ∀ A B, ‖A‖ = 1 → ‖B‖ = 1 → ⟪A, B⟫ = 0 → ⟪R A B A, B⟫ = κ) :
    R = κ • curvatureOne :=
  hR.ext_of_orthonormal (isCurvatureTensor_curvatureOne.smul κ) fun A B hA hB hAB => by
    rw [h A B hA hB hAB, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply,
      real_inner_smul_left, inner_curvatureOne_self, hA, hB, hAB]
    ring

/-- **Constant curvature** (exposition, Corollary 7.3): if `K(X, Y) = κ` for all linearly
independent `X, Y`, then `R(X, Y)Z = κ(⟨X, Z⟩Y − ⟨Y, Z⟩X)` for all `X, Y, Z`. -/
theorem apply_eq_of_sectionalCurvature_eq (hR : IsCurvatureTensor R) (κ : ℝ)
    (h : ∀ X Y, LinearIndependent ℝ ![X, Y] → sectionalCurvature R X Y = κ) (X Y Z : E) :
    R X Y Z = κ • (⟪X, Z⟫ • Y - ⟪Y, Z⟫ • X) := by
  have hR' := hR.ext_of_sectionalCurvature (isCurvatureTensor_curvatureOne.smul κ)
    fun X Y hXY => by rw [h X Y hXY, sectionalCurvature_smul_curvatureOne κ hXY]
  rw [hR']
  simp

end IsCurvatureTensor

end Morse
