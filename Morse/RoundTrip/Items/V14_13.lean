import Morse
import RoundTrip.Check
import RoundTrip.Blind.V14_13

/-!
# V14_13 (Milnor §23, pp. 124–126): `U(n)` and `SU(n)` as compact matrix groups

`A` (universes `0`; `unitaryMap`, `suMap`, `hermitian`, `skewHermitian`, `specialSkewHermitian`,
`IsMatrixGroup` are vocabulary): for every `RCLike 𝕜` (so also `O(n)` for `𝕜 = ℝ`) and every finite
index type, `0` is a regular value of `A ↦ AᴴA − I` (values in the Hermitian matrices), `U(n)` is a
slice submanifold of `Mₙ(𝕜)` modelled on `𝔲(n)` (a regular level set), it is a matrix group
(`IsMatrixGroup`: unitary, closed under products and `ᴴ`, `Ad`-invariant `𝔲`, `exp 𝔲 ⊆ U`,
`dim = dim 𝔲`) and compact; for `n ≥ 1` the same for `SU(n)` through the open piece `Re det > 0`
of the regular level set of `A ↦ (AᴴA − I, Im det A)`; Jacobi's formula `d det_A (AX) = det A·tr X`
at every `A`; `det exp(tX) = 1` for `tr X = 0`.

`B` (blind): for every `n ≥ 0`, over `ℂ` only: `U(n)` compact; at every `g ∈ U(n)` an **exp slice
chart** `A ↦ g·exp A` (a `C^∞` diffeomorphism near `0` with `g exp A ∈ U(n) ↔ A ∈ 𝔲(n)`); tangent
space at `I` (velocities of `C^∞` curves) `= 𝔲(n)`; group axioms and smoothness of `·` and `ᴴ`;
left-invariant fields `g ↦ gX` tangent to `U(n)` with Lie bracket `X_{XY−YX}`; `Re tr(AB*)` symmetric,
bilinear, positive definite, bi-invariant; `det exp X = e^{tr X}` for **all** `X`; `SU(n)` a subgroup
with exp slice charts, tangent space `𝔰𝔲(n)` at `I`, `𝔰𝔲(n)` closed under commutators.

Neither direction is proved (see `V14_13.json`).

* `A → B`: the exp slice charts are not in `A` (the project replaces Milnor's chart (5) by level
  sets).  They need the inverse function theorem for `exp` at `0`, the local injectivity of `exp`
  on a ball invariant under `A ↦ −Aᴴ` (to get `exp A ∈ U ⇒ A ∈ 𝔲`), and for `SU(n)` also
  `det exp = e^{tr}` plus smallness of `tr A`; and all the `C^∞` statements are for the blind's
  entrywise norm, not the project's Frobenius norm.  The Lie bracket of left-invariant vector
  fields and the properties of `Re tr(AB*)` are elementary but absent from `A`.  Some conjuncts do
  follow from `A` with glue: compactness (`compact_of_A`) and `det exp X = e^{tr X}` for all `X`
  from `A`'s traceless case (`det_exp_of_A`, by splitting off the scalar part `(tr X/n)·I`).
* `B → A`: `B` is about complex matrices only, so `A` for `𝕜 = ℝ` (`O(n)`) is out of reach; `B` has
  nothing about the maps `AᴴA − I`, `Im det`, their regular values, the Hermitian complement, the
  project's `Milnor.IsSliceSubmanifold` charts, `Ad`-invariance, or Jacobi's formula at a general
  point.
* Moreover `#rt_check` could never pass for a full direction here: `A`'s own statement mentions
  banned theorems (the type of `isMatrixGroup_unitaryGroup` is
  `IsMatrixGroup isSliceSubmanifold_unitaryGroup (skewHermitian 𝕜 ι)`, and likewise for `SU`).
  The partial lemmas below therefore take only the conjunct they use as hypothesis.
-/

open Matrix

namespace RoundTrip.V14_13

/-- The project's statement (universes `0`). -/
def A : Prop :=
  type_of% @Morse.isRegularValue_unitaryMap.{0, 0} ∧
    type_of% @Morse.isSliceSubmanifold_unitaryGroup.{0, 0} ∧
    type_of% @Morse.isMatrixGroup_unitaryGroup.{0, 0} ∧
    type_of% @Morse.isCompact_unitaryGroup.{0, 0} ∧
    type_of% @Morse.isRegularValue_suMap.{0} ∧
    type_of% @Morse.isSliceSubmanifold_specialUnitaryGroup.{0} ∧
    type_of% @Morse.isMatrixGroup_specialUnitaryGroup.{0} ∧
    type_of% @Morse.isCompact_specialUnitaryGroup.{0} ∧
    type_of% @Morse.fderiv_det_mul.{0, 0} ∧
    type_of% @Morse.det_exp_smul_of_trace_eq_zero.{0, 0}

theorem A_holds : A :=
  ⟨@Morse.isRegularValue_unitaryMap.{0, 0}, @Morse.isSliceSubmanifold_unitaryGroup.{0, 0},
    @Morse.isMatrixGroup_unitaryGroup.{0, 0}, @Morse.isCompact_unitaryGroup.{0, 0},
    @Morse.isRegularValue_suMap.{0}, @Morse.isSliceSubmanifold_specialUnitaryGroup.{0},
    @Morse.isMatrixGroup_specialUnitaryGroup.{0}, @Morse.isCompact_specialUnitaryGroup.{0},
    @Morse.fderiv_det_mul.{0, 0}, @Morse.det_exp_smul_of_trace_eq_zero.{0, 0}⟩

/-! ### Partial bridges (each from the single conjunct of `A` it uses) -/

/-- `B`'s compactness of `U(n)` and of `SU(n)`, from `A`'s `isCompact_unitaryGroup` /
`isCompact_specialUnitaryGroup` (the topologies agree). -/
theorem compact_of_A (h4 : type_of% @Morse.isCompact_unitaryGroup.{0, 0})
    (h8 : type_of% @Morse.isCompact_specialUnitaryGroup.{0}) (n : ℕ) :
    IsCompact (Un n) ∧ IsCompact (SUn n) :=
  ⟨h4, h8⟩

/-- `B`'s `det exp X = e^{tr X}` for every `X`, from `A`'s traceless case: `X = X₀ + (tr X/n)·I`
with `tr X₀ = 0`, and `exp` of the scalar part is `e^{tr X/n}·I`. -/
theorem det_exp_of_A (h10 : type_of% @Morse.det_exp_smul_of_trace_eq_zero.{0, 0}) (n : ℕ)
    (X : Mat n) : (mexp X).det = Complex.exp X.trace := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Matrix.det_isEmpty, Matrix.trace, Finset.univ_eq_empty, Finset.sum_empty,
      Complex.exp_zero]
  · have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    set c : ℂ := X.trace / n with hc
    set X₀ : Mat n := X - Matrix.diagonal fun _ => c with hX₀
    have htr : X₀.trace = 0 := by
      rw [hX₀, Matrix.trace_sub, Matrix.trace_diagonal, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, hc]
      field_simp
      ring
    have hcomm : Commute X₀ (Matrix.diagonal fun _ => c) := by
      rw [show (Matrix.diagonal fun _ : Fin n => c) = c • (1 : Mat n) by
        ext i j; by_cases h : i = j <;> simp [h]]
      exact (Commute.one_right X₀).smul_right c
    have hX : X = X₀ + Matrix.diagonal fun _ => c := by rw [hX₀, sub_add_cancel]
    have h1 : (NormedSpace.exp X₀ : Mat n).det = 1 := by
      have := h10 (𝕜 := ℂ) (ι := Fin n) htr 1
      rwa [one_smul] at this
    rw [mexp, hX, Matrix.exp_add_of_commute _ _ hcomm, Matrix.det_mul, h1, one_mul,
      Matrix.exp_diagonal, Matrix.det_diagonal, Pi.exp_def, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, ← Complex.exp_eq_exp_ℂ, ← Complex.exp_nat_mul, Matrix.trace_add,
      htr, zero_add, Matrix.trace_diagonal, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]

#rt_check RoundTrip.V14_13.compact_of_A [Morse.isRegularValue_unitaryMap, Morse.isSliceSubmanifold_unitaryGroup, Morse.isMatrixGroup_unitaryGroup, Morse.isCompact_unitaryGroup, Morse.isRegularValue_suMap, Morse.isSliceSubmanifold_specialUnitaryGroup, Morse.isMatrixGroup_specialUnitaryGroup, Morse.isCompact_specialUnitaryGroup, Morse.fderiv_det_mul, Morse.det_exp_smul_of_trace_eq_zero]
#rt_check RoundTrip.V14_13.det_exp_of_A [Morse.isRegularValue_unitaryMap, Morse.isSliceSubmanifold_unitaryGroup, Morse.isMatrixGroup_unitaryGroup, Morse.isCompact_unitaryGroup, Morse.isRegularValue_suMap, Morse.isSliceSubmanifold_specialUnitaryGroup, Morse.isMatrixGroup_specialUnitaryGroup, Morse.isCompact_specialUnitaryGroup, Morse.fderiv_det_mul, Morse.det_exp_smul_of_trace_eq_zero]

end RoundTrip.V14_13
