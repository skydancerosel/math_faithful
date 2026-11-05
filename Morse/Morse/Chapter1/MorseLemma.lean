import Mathlib.LinearAlgebra.QuadraticForm.Real
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Morse.Chapter1.Hadamard
import Morse.Chapter1.SquareRoot

/-!
Milnor, *Morse Theory*, §2, pp. 6–8.

# The Lemma of Morse (Lemma 2.2)

**Lemma 2.2** (Lemma of Morse; Milnor, p. 6), paraphrased: if `p` is a non-degenerate critical
point of `f`, there is a local coordinate system `(y¹, …, yⁿ)` on a neighbourhood `U` of `p`, with
all `yⁱ(p) = 0`, in which `f = f(p) − (y¹)² − ⋯ − (y^λ)² + (y^{λ+1})² + ⋯ + (yⁿ)²` on all of `U`,
`λ` being the index of `f` at `p`.

Milnor's proof has two parts.

1. **If there is any such expression for `f`, then `λ` must be the index of `f` at `p`** (p. 6).
   In the coordinates `z`, the matrix of `f_**` is `diag(−2, …, −2, 2, …, 2)`; so there is a
   `λ`-dimensional subspace on which `f_**` is negative definite and an `(n − λ)`-dimensional one
   on which it is positive definite, and a subspace of dimension `> λ` on which `f_**` is
   negative definite would meet the latter.  Here: `Morse.index_eq_of_morse_chart`.  The
   computation of the matrix of `f_**` in the coordinates `z` uses the coordinate independence of
   the Hessian at a critical point (`Morse.index_hessian_comp`), which Milnor takes for granted;
   the dimension count is Mathlib's Sylvester law of inertia
   (`QuadraticForm.sigNeg_weightedSumSquares`).
2. **Existence of the coordinates** (pp. 6–8): by Lemma 2.1 applied twice
   `f = ∑ xᵢ xⱼ hᵢⱼ` with `(hᵢⱼ)` symmetric and `hᵢⱼ(0) = ½ ∂²f/∂xⁱ∂xʲ(0)`
   (`Morse.exists_hadamard_two_on`), and then an induction diagonalizing the form `∑ xᵢ xⱼ hᵢⱼ(x)`
   with smooth coefficients, one square at a time, using square roots of the smooth functions
   `±H_rr` and the inverse function theorem at each step.

## How the existence proof differs from Milnor's

The induction is replaced by one application of the inverse function theorem in the space of
linear maps (`Morse.exists_sqrt_family`, see `Morse/Chapter1/SquareRoot.lean`): writing
`f(p + x) − f(p) = B x (x, x)` with `B` smooth and `B 0 = ½ d²f_p =: B₀`, we find linear maps
`C x`, smooth in `x` near `0`, with `C 0 = id` and `B x (v, v) = B₀(C x v, C x v)`.  Then
`φ(p + x) = C x x` has derivative `id` at `p`, hence (inverse function theorem) is a local
diffeomorphism, and `f = f(p) + ½ d²f_p(φ, φ)` near `p` (`Morse.exists_morse_chart`).  This is the
coordinate-free form of the lemma.  Composing `φ` with a linear isomorphism that diagonalizes the
quadratic form `½ d²f_p` (Sylvester; `Morse.exists_linearEquiv_diagForm`, which also orders the
negative squares first) gives Milnor's form (`Morse.morse_lemma`).

In Milnor's induction, the reduction to `H_rr(0) ≠ 0` by a linear change of the last
`n − r + 1` coordinates is asserted without proof.  It needs: the Hessian of `f` at `0` in the
coordinates `u` is non-degenerate (independence of coordinates); it is block diagonal,
`diag(±2, …, ±2, 2 (H_ij(0))_{i,j ≥ r})`, so the block `(H_ij(0))_{i,j ≥ r}` is non-degenerate,
hence non-zero, hence (polarization) `∑ H_ij(0) vᵢ vⱼ ≠ 0` for some `v`, which is taken as the new
`r`-th coordinate direction.  No such step occurs here.

## Setting and conventions

* `E` is a finite-dimensional real normed space (Milnor's `ℝⁿ`, coordinate free), `f : E → ℝ` is
  `C^∞` on an open set `U ∋ p`.  A local coordinate system on a neighbourhood of `p` is an open
  partial homeomorphism `y : E → ℝⁿ` (`ℝⁿ = Fin n → ℝ`, `n = dim E`) with `p` in its source,
  `y` smooth on its source and `y⁻¹` smooth on its target.
* Milnor's coordinates are numbered `1, …, n`; ours are `0, …, n − 1`, so the negative squares
  are those with index `i < λ`.
-/

open Set Filter Topology Module
open scoped ContDiff

noncomputable section

namespace Morse

/-! ### The normal form -/

section NormalForm

variable {n : ℕ}

/-- The signs of Milnor's normal form: `-1` for the first `k` coordinates, `+1` for the others. -/
def morseSign (k : ℕ) (i : Fin n) : ℝ :=
  if (i : ℕ) < k then -1 else 1

/-- The diagonal bilinear form `(y, z) ↦ ∑ᵢ sᵢ yᵢ zᵢ` on `ℝⁿ`. -/
def diagForm (s : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, s i • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).smulRight
    (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)

theorem diagForm_apply (s : Fin n → ℝ) (y z : Fin n → ℝ) :
    diagForm s y z = ∑ i, s i * y i * z i := by
  simp [diagForm, mul_assoc]

theorem diagForm_symm (s : Fin n → ℝ) (y z : Fin n → ℝ) : diagForm s y z = diagForm s z y := by
  simp only [diagForm_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Milnor's normal form: `diagForm (morseSign k)` evaluated on the diagonal is
`−(y⁰)² − ⋯ − (y^{k−1})² + (y^k)² + ⋯ + (y^{n−1})²`. -/
theorem diagForm_morseSign_apply_self (k : ℕ) (y : Fin n → ℝ) :
    diagForm (morseSign k) y y =
      -∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), y i ^ 2 +
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ (i : ℕ)), y i ^ 2 := by
  rw [diagForm_apply]
  have h : ∀ i : Fin n, morseSign k i * y i * y i =
      if (i : ℕ) < k then -(y i ^ 2) else y i ^ 2 := by
    intro i
    unfold morseSign
    split_ifs <;> ring
  simp only [h, Finset.sum_ite, Finset.sum_neg_distrib, not_lt]

/-- The quadratic form of `diagForm s` is Mathlib's weighted sum of squares. -/
theorem quadForm_diagForm (s : Fin n → ℝ) :
    quadForm (diagForm s) = QuadraticMap.weightedSumSquares ℝ s := by
  ext y
  simp [diagForm_apply, QuadraticMap.weightedSumSquares_apply, mul_assoc]

/-- **The index of Milnor's normal form is `k`** (Milnor, p. 6, first paragraph of the proof of
Lemma 2.2; this is Sylvester's law of inertia). -/
theorem index_diagForm_morseSign {k : ℕ} (hk : k ≤ n) :
    index (diagForm (morseSign (n := n) k)) = k := by
  rw [index, quadForm_diagForm, QuadraticForm.sigNeg_weightedSumSquares]
  have hset : {i : Fin n | morseSign k i < 0} = {i : Fin n | (i : ℕ) < k} := by
    ext i
    simp only [Set.mem_ofPred_eq, morseSign]
    split_ifs with h <;> simp [h]
  rw [hset, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact Fintype.card_fin_lt_of_le hk

end NormalForm

/-! ### Diagonalizing a non-degenerate symmetric bilinear form, negative squares first -/

section Diagonalize

/-- A finite family of weights can be permuted so that its negative entries come first. -/
theorem exists_perm_neg_first {n : ℕ} (w : Fin n → ℝ) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, w (σ i) < 0 ↔ (i : ℕ) < {j | w j < 0}.ncard := by
  classical
  set k := {j | w j < 0}.ncard with hk
  have hkn : k ≤ n := by
    have := Set.ncard_le_card (s := {j : Fin n | w j < 0})
    simpa using this
  have hcard₁ : Fintype.card {i : Fin n // (i : ℕ) < k} = Fintype.card {i : Fin n // w i < 0} := by
    rw [Fintype.card_fin_lt_of_le hkn, hk, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    rfl
  have hcard₂ : Fintype.card {i : Fin n // ¬ (i : ℕ) < k} =
      Fintype.card {i : Fin n // ¬ w i < 0} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hcard₁]
  set e₁ := Fintype.equivOfCardEq hcard₁
  set e₂ := Fintype.equivOfCardEq hcard₂
  refine ⟨Equiv.subtypeCongr e₁ e₂, fun i => ?_⟩
  by_cases hi : (i : ℕ) < k
  · have : Equiv.subtypeCongr e₁ e₂ i = e₁ ⟨i, hi⟩ := by
      simp only [Equiv.subtypeCongr, Equiv.trans_apply]
      rw [Equiv.sumCompl_symm_apply_of_pos (p := fun x : Fin n => (x : ℕ) < k) (a := i) hi]
      rfl
    rw [this]
    exact iff_of_true (e₁ ⟨i, hi⟩).2 hi
  · have : Equiv.subtypeCongr e₁ e₂ i = e₂ ⟨i, hi⟩ := by
      simp only [Equiv.subtypeCongr, Equiv.trans_apply]
      rw [Equiv.sumCompl_symm_apply_of_neg (p := fun x : Fin n => (x : ℕ) < k) (a := i) hi]
      rfl
    rw [this]
    exact iff_of_false (e₂ ⟨i, hi⟩).2 hi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Diagonalization of a non-degenerate symmetric bilinear form** (Sylvester), with the
negative squares first: there is a linear isomorphism `e : E ≃ ℝⁿ` with
`H(v, v) = −(e v)₀² − ⋯ − (e v)²_{λ−1} + (e v)²_λ + ⋯ + (e v)²_{n−1}`, `λ = index H`.
This is the classical diagonalization of quadratic forms that Milnor imitates (p. 7, citing
Birkhoff–MacLane). -/
theorem exists_linearEquiv_diagForm (H : E →L[ℝ] E →L[ℝ] ℝ) (hsymm : ∀ u v, H u v = H v u)
    (hnd : IsNondegenerate H) :
    ∃ e : E ≃L[ℝ] (Fin (finrank ℝ E) → ℝ),
      ∀ v, H v v = diagForm (morseSign (index H)) (e v) (e v) := by
  set Q := quadForm H with hQ
  have hassoc : QuadraticMap.associated Q = ContinuousLinearMap.toLinearMap₁₂ H :=
    QuadraticMap.associated_left_inverse ℝ (B₁ := ContinuousLinearMap.toLinearMap₁₂ H) hsymm
  have hsep : (QuadraticMap.associated Q).SeparatingLeft := by
    rw [hassoc]
    exact isNondegenerate_iff.1 hnd
  obtain ⟨w, hw, ⟨e₀⟩⟩ := QuadraticForm.equivalent_one_neg_one_weighted_sum_squared Q hsep
  have hk : index H = {i | w i < 0}.ncard := QuadraticForm.sigNeg_of_equiv_weightedSumSquares ⟨e₀⟩
  obtain ⟨σ, hσ⟩ := exists_perm_neg_first w
  rw [← hk] at hσ
  have hwσ : ∀ i, w (σ i) = morseSign (index H) i := by
    intro i
    unfold morseSign
    split_ifs with h
    · rcases hw (σ i) with h' | h'
      · exact h'
      · have := (hσ i).2 h; rw [h'] at this; norm_num at this
    · rcases hw (σ i) with h' | h'
      · exact absurd ((hσ i).1 (by rw [h']; norm_num)) h
      · exact h'
  set e : E ≃ₗ[ℝ] (Fin (finrank ℝ E) → ℝ) :=
    e₀.toLinearEquiv.trans (LinearEquiv.funCongrLeft ℝ ℝ σ) with he
  refine ⟨e.toContinuousLinearEquiv, fun v => ?_⟩
  have h1 : H v v = QuadraticMap.weightedSumSquares ℝ w (e₀ v) := by
    rw [e₀.map_app]; rfl
  rw [h1, QuadraticMap.weightedSumSquares_apply, diagForm_apply,
    ← Equiv.sum_comp σ (fun i => w i • (e₀ v i * e₀ v i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hev : e.toContinuousLinearEquiv v i = e₀ v (σ i) := rfl
  rw [hev, hwσ i, smul_eq_mul, mul_assoc]

end Diagonalize

/-! ### The Morse chart, coordinate free -/

section Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_translate (f : E → ℝ) (p y : E) :
    fderiv ℝ (fun y => f (p + y) - f p) y = fderiv ℝ f (p + y) := by
  rw [fderiv_sub_const, fderiv_comp_add_left]

theorem hessian_translate (f : E → ℝ) (p : E) :
    hessian (fun y => f (p + y) - f p) 0 = hessian f p := by
  have h : fderiv ℝ (fun y => f (p + y) - f p) = fun y => fderiv ℝ f (p + y) :=
    funext (fderiv_translate f p)
  rw [hessian, h, fderiv_comp_add_left, add_zero, hessian]

variable [FiniteDimensional ℝ E]

/-- **The Morse lemma, coordinate free.**  Let `f` be smooth on an open set `U ∋ p`, with `p` a
non-degenerate critical point.  Then there is a local diffeomorphism `φ` from a neighbourhood
of `p` in `U` onto an open set of `E`, with `φ p = 0` and `dφ_p = id`, such that
`f = f(p) + ½ d²f_p(φ, φ)` on the source of `φ`. -/
theorem exists_morse_chart {f : E → ℝ} {p : E} {U : Set E} (hU : IsOpen U) (hpU : p ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) (hcrit : IsCriticalPoint f p)
    (hnd : IsNondegenerate (hessian f p)) :
    ∃ φ : OpenPartialHomeomorph E E, p ∈ φ.source ∧ φ.source ⊆ U ∧ φ p = 0 ∧
      HasFDerivAt φ (ContinuousLinearMap.id ℝ E) p ∧
      ContDiffOn ℝ ∞ φ φ.source ∧ ContDiffOn ℝ ∞ φ.symm φ.target ∧
      ∀ x ∈ φ.source, f x = f p + (2 : ℝ)⁻¹ * hessian f p (φ x) (φ x) := by
  -- a ball `p + V` inside `U`
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU p hpU
  set V := Metric.ball (0 : E) r with hV
  have hVo : IsOpen V := Metric.isOpen_ball
  have h0V : (0 : E) ∈ V := Metric.mem_ball_self hr
  have hV0 : StarConvex ℝ 0 V := (convex_ball (0 : E) r).starConvex h0V
  have hpV : ∀ y ∈ V, p + y ∈ U := fun y hy => by
    rw [hV, mem_ball_zero_iff] at hy
    apply hrU
    rwa [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
  -- `g y = f (p + y) - f p` satisfies the hypotheses of Hadamard's lemma to second order
  set g : E → ℝ := fun y => f (p + y) - f p with hg_def
  have hg : ContDiffOn ℝ ∞ g V :=
    (hf.comp (contDiff_const.add contDiff_id).contDiffOn hpV).sub contDiffOn_const
  have hg0 : g 0 = 0 := by simp [g]
  have hdg0 : fderiv ℝ g 0 = 0 := by rw [fderiv_translate, add_zero, hcrit.fderiv_eq]
  obtain ⟨B, hB, hgB, -, hB0⟩ := exists_hadamard_two_on hVo hV0 hg hg0 hdg0
  rw [← hessian, hessian_translate] at hB0
  -- `B₀ = ½ d²f_p` is symmetric and non-degenerate
  set B₀ : E →L[ℝ] E →L[ℝ] ℝ := (2 : ℝ)⁻¹ • hessian f p with hB₀
  have hfC2 : ContDiffAt ℝ 2 f p := (hf.contDiffAt (hU.mem_nhds hpU)).of_le (by norm_cast)
  have hB₀symm : ∀ u v, B₀ u v = B₀ v u := fun u v => by
    simp only [hB₀, smul_apply, hessian_symm hfC2 u v]
  have hB₀nd : IsNondegenerate B₀ := (isNondegenerate_smul_iff (by norm_num) _).2 hnd
  -- the square root `C`
  obtain ⟨C, W, hWo, h0W, hWV, hC, hC0, hCB⟩ := exists_sqrt_family hB₀symm hB₀nd hVo h0V hB hB0
  -- the chart, before inverting: `ψ x = C (x - p) (x - p)`
  set ψ : E → E := fun x => C (x - p) (x - p) with hψ_def
  set W' := (fun x => x - p) ⁻¹' W with hW'
  have hW'o : IsOpen W' := hWo.preimage (continuous_id.sub continuous_const)
  have hpW' : p ∈ W' := by simp [W', h0W]
  have hψ : ContDiffOn ℝ ∞ ψ W' :=
    (hC.comp (contDiff_id.sub contDiff_const).contDiffOn fun x hx => hx).clm_apply
      (contDiff_id.sub contDiff_const).contDiffOn
  have hCd : HasFDerivAt C (fderiv ℝ C (p - p)) (p - p) := by
    rw [sub_self]
    exact ((hC.contDiffAt (hWo.mem_nhds h0W)).differentiableAt (by simp)).hasFDerivAt
  have hψ' : HasFDerivAt ψ
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) p := by
    have h := (HasFDerivAt.comp (f := fun x : E => x - p) p hCd
      ((hasFDerivAt_id p).sub_const p)).clm_apply ((hasFDerivAt_id p).sub_const p)
    refine h.congr_fderiv ?_
    ext v
    simp [hC0]
  obtain ⟨Φ, hΦ, hpΦ, hΦW', hΦs, hΦt⟩ := exists_openPartialHomeomorph_of_contDiffOn
    (hW'o.inter hU) ⟨hpW', hpU⟩ (by simp) (hψ.mono inter_subset_left) hψ'
  refine ⟨Φ, hpΦ, fun x hx => (hΦW' hx).2, ?_, ?_, hΦs, hΦt, ?_⟩
  · rw [hΦ]
    simp [ψ]
  · rw [hΦ]
    simpa using hψ'
  · intro x hx
    have hxW : x - p ∈ W := (hΦW' hx).1
    have hxV : x - p ∈ V := hWV hxW
    have h1 : f x = f p + g (x - p) := by simp [g]
    rw [h1, hgB _ hxV, hCB _ hxW, hΦ]
    simp [B₀, ψ]

end Chart

/-! ### The Lemma of Morse in Milnor's form -/

section Main

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Lemma 2.2 (Lemma of Morse)**, Milnor p. 6.  Let `f` be smooth on an open set `U ∋ p` in a
finite-dimensional real normed space `E` (`n = dim E`), and `p` a non-degenerate critical point
of `f`, of index `λ`.  Then there is a local coordinate system `y = (y⁰, …, yⁿ⁻¹)`, a smooth
partial homeomorphism `E → ℝⁿ` with smooth inverse whose source is a neighbourhood of `p`
contained in `U`, with `y(p) = 0` and
`f = f(p) − (y⁰)² − ⋯ − (y^{λ−1})² + (y^λ)² + ⋯ + (yⁿ⁻¹)²` throughout the source. -/
theorem morse_lemma {f : E → ℝ} {p : E} {U : Set E} (hU : IsOpen U) (hpU : p ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) (hcrit : IsCriticalPoint f p)
    (hnd : IsNondegenerate (hessian f p)) :
    ∃ y : OpenPartialHomeomorph E (Fin (finrank ℝ E) → ℝ),
      p ∈ y.source ∧ y.source ⊆ U ∧ y p = 0 ∧
      ContDiffOn ℝ ∞ y y.source ∧ ContDiffOn ℝ ∞ y.symm y.target ∧
      ∀ x ∈ y.source, f x = f p
        - ∑ i ∈ Finset.univ.filter (fun i : Fin (finrank ℝ E) => (i : ℕ) < index (hessian f p)),
            y x i ^ 2
        + ∑ i ∈ Finset.univ.filter (fun i : Fin (finrank ℝ E) => index (hessian f p) ≤ (i : ℕ)),
            y x i ^ 2 := by
  obtain ⟨φ, hpφ, hφU, hφp, -, hφs, hφt, hfφ⟩ := exists_morse_chart hU hpU hf hcrit hnd
  have hfC2 : ContDiffAt ℝ 2 f p := (hf.contDiffAt (hU.mem_nhds hpU)).of_le (by norm_cast)
  obtain ⟨e, he⟩ := exists_linearEquiv_diagForm (hessian f p) (hessian_symm hfC2) hnd
  -- absorb the factor `½` into the linear change of coordinates
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  set L : E ≃L[ℝ] (Fin (finrank ℝ E) → ℝ) :=
    ((LinearEquiv.smulOfNeZero ℝ E _ (inv_ne_zero hs)).toContinuousLinearEquiv).trans e with hL
  have hLapp : ∀ z, L z = e ((Real.sqrt 2)⁻¹ • z) := fun z => rfl
  have hhalf : ∀ z, (2 : ℝ)⁻¹ * hessian f p z z =
      diagForm (morseSign (index (hessian f p))) (L z) (L z) := by
    intro z
    rw [hLapp, ← he]
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  set y := φ.transHomeomorph L.toHomeomorph with hy
  have hysrc : y.source = φ.source := rfl
  have hyapp : ∀ x, y x = L (φ x) := fun x => rfl
  have hytgt : y.target = L.symm ⁻¹' φ.target := rfl
  refine ⟨y, hysrc ▸ hpφ, hysrc ▸ hφU, by rw [hyapp, hφp, map_zero], ?_, ?_, ?_⟩
  · rw [hysrc]
    exact (L : E →L[ℝ] (Fin (finrank ℝ E) → ℝ)).contDiff.comp_contDiffOn hφs
  · rw [hytgt]
    exact hφt.comp (L.symm : (Fin (finrank ℝ E) → ℝ) →L[ℝ] E).contDiff.contDiffOn
      fun z hz => hz
  · intro x hx
    rw [hysrc] at hx
    rw [hfφ x hx, hhalf, ← hyapp, diagForm_morseSign_apply_self]
    ring

omit [FiniteDimensional ℝ E] in
/-- **The index is forced by the normal form** (Milnor, p. 6, first step of the proof of
Lemma 2.2: any such expression for `f` has `λ` equal to the index).  If `p` is a critical point of
`f` (`f` of class `C²` at `p`) and `z` is a local coordinate system around `p` (a partial
homeomorphism `E → ℝⁿ`, smooth with smooth inverse) with `z(p) = 0` and
`f = f(p) − (z⁰)² − ⋯ − (z^{k−1})² + (z^k)² + ⋯ + (zⁿ⁻¹)²` on its source, `k ≤ n`, then `k` is the
index of `f` at `p`.

As in Milnor: in the coordinates `z` the Hessian is `diag(−2, …, −2, 2, …, 2)`, whose index is `k`
(`Morse.index_diagForm_morseSign`, Sylvester), and the index does not depend on the coordinates
(`Morse.index_hessian_comp`; Milnor uses this without comment when he computes `f_**` in the
coordinates `z`). -/
theorem index_eq_of_morse_chart {f : E → ℝ} {p : E} (hf : ContDiffAt ℝ 2 f p)
    (hcrit : IsCriticalPoint f p) (z : OpenPartialHomeomorph E (Fin (finrank ℝ E) → ℝ))
    (hp : p ∈ z.source) (hzp : z p = 0) (hz : ContDiffOn ℝ ∞ z z.source)
    (hzs : ContDiffOn ℝ ∞ z.symm z.target) {k : ℕ} (hk : k ≤ finrank ℝ E)
    (hfz : ∀ x ∈ z.source, f x = f p
        - ∑ i ∈ Finset.univ.filter (fun i : Fin (finrank ℝ E) => (i : ℕ) < k), z x i ^ 2
        + ∑ i ∈ Finset.univ.filter (fun i : Fin (finrank ℝ E) => k ≤ (i : ℕ)), z x i ^ 2) :
    index (hessian f p) = k := by
  set D := diagForm (morseSign (n := finrank ℝ E) k) with hD
  have h0t : (0 : Fin (finrank ℝ E) → ℝ) ∈ z.target := hzp ▸ z.map_source hp
  have hzs0 : z.symm 0 = p := by rw [← hzp]; exact z.left_inv hp
  -- `f ∘ z⁻¹ = f(p) + D(w, w)` near `0`
  have heq : (f ∘ z.symm) =ᶠ[𝓝 0] fun w => f p + D w w := by
    filter_upwards [z.open_target.mem_nhds h0t] with w hw
    have h1 := hfz (z.symm w) (z.map_target hw)
    rw [z.right_inv hw] at h1
    rw [Function.comp_apply, h1, hD, diagForm_morseSign_apply_self]
    ring
  -- so its Hessian at `0` is `2 D`
  have hH : hessian (f ∘ z.symm) 0 = (2 : ℝ) • D := by
    rw [hessian_congr heq]
    have hc : fderiv ℝ (fun w => f p + D w w) = fderiv ℝ (fun w => D w w) := by
      funext w
      exact fderiv_const_add (f p)
    ext u v
    rw [hessian, hc, ← hessian, hessian_bilinear, hD, diagForm_symm (morseSign k) v u]
    simp only [smul_apply, smul_eq_mul]
    ring
  -- the derivative of `z⁻¹` at `0` is invertible
  have hzC : ContDiffAt ℝ ∞ z p := hz.contDiffAt (z.open_source.mem_nhds hp)
  have hzsC : ContDiffAt ℝ ∞ z.symm 0 := hzs.contDiffAt (z.open_target.mem_nhds h0t)
  have hzd : DifferentiableAt ℝ z p := hzC.differentiableAt (by simp)
  have hzsd : DifferentiableAt ℝ z.symm (z p) := by
    rw [hzp]; exact hzsC.differentiableAt (by simp)
  have hzsd' : DifferentiableAt ℝ z.symm 0 := hzsC.differentiableAt (by simp)
  have hzd' : DifferentiableAt ℝ z (z.symm 0) := by rw [hzs0]; exact hzd
  have hLM : (fderiv ℝ z.symm 0).comp (fderiv ℝ z p) = ContinuousLinearMap.id ℝ E := by
    have h1 : fderiv ℝ (z.symm ∘ z) p = fderiv ℝ z.symm (z p) ∘L fderiv ℝ z p :=
      fderiv_comp p hzsd hzd
    have h2 : fderiv ℝ (z.symm ∘ z) p = ContinuousLinearMap.id ℝ E := by
      have hev : (z.symm ∘ z) =ᶠ[𝓝 p] id := z.eventually_left_inverse hp
      rw [hev.fderiv_eq, fderiv_id]
    rw [← hzp, ← h1, h2]
  have hML : (fderiv ℝ z p).comp (fderiv ℝ z.symm 0) =
      ContinuousLinearMap.id ℝ (Fin (finrank ℝ E) → ℝ) := by
    have h1 : fderiv ℝ (z ∘ z.symm) 0 = fderiv ℝ z (z.symm 0) ∘L fderiv ℝ z.symm 0 :=
      fderiv_comp 0 hzd' hzsd'
    have h2 : fderiv ℝ (z ∘ z.symm) 0 = ContinuousLinearMap.id ℝ (Fin (finrank ℝ E) → ℝ) := by
      have hev : (z ∘ z.symm) =ᶠ[𝓝 0] id := z.eventually_right_inverse h0t
      rw [hev.fderiv_eq, fderiv_id]
    rw [← hzs0, ← h1, h2]
  set Lz : (Fin (finrank ℝ E) → ℝ) ≃L[ℝ] E :=
    ContinuousLinearEquiv.equivOfInverse (fderiv ℝ z.symm 0)
    (fderiv ℝ z p) (fun v => by simpa using congrArg (fun T => T v) hML)
    (fun x => by simpa using congrArg (fun T => T x) hLM) with hLz
  -- the index does not depend on the coordinates
  have hidx := index_hessian_comp (f := f) (ψ := z.symm) (q := 0) (by rw [hzs0]; exact hf)
    (hzsC.of_le (by norm_cast)) (by rw [hzs0]; exact hcrit.fderiv_eq) Lz rfl
  rw [hzs0] at hidx
  rw [← hidx, hH, index_smul (by norm_num), index_diagForm_morseSign hk]

end Main

end Morse
