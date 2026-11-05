import Morse.Chapter15.OmegaKilling

/-!
Milnor, *Morse Theory*, §24, pp. 145–146 (and Lemma 24.2, p. 135); Exposition/Chapter15.md, §6.

# Intertwiners between eigenspaces of `A²` and the count of Killing fields

## Milnor's text, paraphrased

(p. 145) On `M_h` let `J'_h = a_h⁻¹JA`; Lemma 24.8 gives `C : M_h → M_j` commuting with the
`J_α`, anticommuting with `J`, with `CJ'_h = J'_jC`; `B = C` on `M_h`, `−Cᵀ` on `M_j`, is an
eigenvector of `K_A` with eigenvalue `(a_h + a_j)²/4`.

## What is formalized

* `Morse.exp_smul_mul_of_sq`, `Morse.mul_exp_smul_of_sq`: `exp(tA)D = cos(bt)D + sin(bt)AD/b`
  when `A²D = −b²D` (and on the right), by uniqueness for `c' = Ac` (`c' = cA`).
* `Morse.IsInterRel A D a b`: `bDA = −aAD`, `A²D = −b²D`, `DA² = −a²D` (an intertwiner from the
  `−a²`- to the `−b²`-eigenspace, anticommuting with the complex structures `A/a`, `A/b`);
  `Morse.IsInterRel.conjTranspose` (`Dᵀ` goes back), `Morse.IsInterRel.commute_exp`: **`D`
  commutes with `exp(sA)` when `s(a + b) = 2π`** (the conjugate point `t = 2/(a + b)`).
* `Morse.exists_killing_spaces`: **the count**: from intertwiners `D_{j,l}` (`l < r₀`) from one
  piece `M₀` (`a₀ > 1`) to pieces `M_j` (`b_j ≥ 1`), detected by projections, the skew parts
  `X = D − Dᵀ` span spaces `𝒳_τ`, `τ = 2/(a₀ + b_j) ∈ (0, 1)`, of total dimension `r₀ · #j`,
  as required by `Morse.sum_finrank_le_formIndex`.

## What Milnor leaves implicit

* That the eigenvectors of different pairs are independent: here `Q_j[X_{j',l}, A]R` isolates the
  `(M₀ → M_j)` block, `−((a₀ + b_j)/b_j)AD_{j,l}`.
* Oddness of the `a_h` is not needed for the count: `a₀ > 1` and `b_j ≥ 1` give
  `τ_j = 2/(a₀ + b_j) < 1`.
-/

open Matrix Set Filter Topology Module
open scoped Morse.MatrixInner RealInnerProductSpace Manifold ContDiff

noncomputable section

namespace Morse

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Intertwiners between two eigenvalues of `−A²` -/

section Intertwiner

/-- `exp(tA)D = cos(bt) D + sin(bt)/b · AD` when `A²D = −b²D`. -/
theorem exp_smul_mul_of_sq {A D : Matrix ι ι ℝ} {b : ℝ} (hb : 0 < b)
    (h : A * (A * D) = -(b ^ 2) • D) (t : ℝ) :
    NormedSpace.exp (t • A) * D = Real.cos (b * t) • D + (Real.sin (b * t) / b) • (A * D) := by
  set c : ℝ → Matrix ι ι ℝ := fun t =>
    Real.cos (b * t) • D + (Real.sin (b * t) / b) • (A * D) with hcdef
  have hc : ∀ t, HasDerivAt c (A * c t) t := fun t => by
    have h1 : HasDerivAt (fun t => Real.cos (b * t)) (-Real.sin (b * t) * b) t := by
      have := ((hasDerivAt_id t).const_mul b).cos
      refine this.congr_deriv ?_
      simp only [id, mul_one]
    have h2 : HasDerivAt (fun t => Real.sin (b * t) / b) (Real.cos (b * t)) t := by
      have := (((hasDerivAt_id t).const_mul b).sin).div_const b
      refine this.congr_deriv ?_
      simp only [id, mul_one]
      field_simp
    refine ((h1.smul_const D).add (h2.smul_const (A * D))).congr_deriv ?_
    simp only [hcdef, Matrix.mul_add, Matrix.mul_smul, h, smul_smul]
    field_simp
    module
  have := eq_exp_smul_mul_of_hasDerivAt hc t
  simp only [hcdef, mul_zero, Real.cos_zero, Real.sin_zero, zero_div, zero_smul, add_zero,
    one_smul] at this
  exact this.symm

/-- A solution of `c' = cV` is `c(t) = c(0) exp(tV)`. -/
theorem eq_mul_exp_smul_of_hasDerivAt {V : Matrix ι ι ℝ} {c : ℝ → Matrix ι ι ℝ}
    (hc : ∀ t, HasDerivAt c (c t * V) t) (t : ℝ) :
    c t = c 0 * NormedSpace.exp (t • V) := by
  set g : ℝ → Matrix ι ι ℝ := fun s => c s * NormedSpace.exp (s • -V) with hgdef
  have hg : ∀ s, HasDerivAt g 0 s := fun s => by
    have h1 := (hc s).mul (hasDerivAt_exp_smul_const (-V) s)
    refine h1.congr_deriv ?_
    have hcomm : NormedSpace.exp (s • -V) * -V = -V * NormedSpace.exp (s • -V) :=
      exp_smul_mul_self (-V) s
    have hcomm' : V * NormedSpace.exp (s • -V) = NormedSpace.exp (s • -V) * V := by
      have := congrArg Neg.neg hcomm
      simpa only [Matrix.mul_neg, Matrix.neg_mul, neg_neg] using this.symm
    rw [Matrix.mul_assoc, hcomm', Matrix.mul_neg, Matrix.mul_neg, add_neg_cancel]
  have hgc : ∀ s, g s = g 0 := fun s =>
    is_const_of_deriv_eq_zero (fun u => (hg u).differentiableAt) (fun u => (hg u).deriv) s 0
  have h0 : g 0 = c 0 := by simp [hgdef]
  have ht := hgc t
  rw [h0] at ht
  calc c t = c t * NormedSpace.exp (t • -V) * NormedSpace.exp (t • V) := by
        rw [Matrix.mul_assoc, smul_neg, exp_neg_mul_exp (t • V), Matrix.mul_one]
    _ = c 0 * NormedSpace.exp (t • V) := by rw [← ht]

/-- The same on the right: `D exp(tA) = cos(at) D + sin(at)/a · DA` when `DA² = −a²D`. -/
theorem mul_exp_smul_of_sq {A D : Matrix ι ι ℝ} {a : ℝ} (ha : 0 < a)
    (h : D * A * A = -(a ^ 2) • D) (t : ℝ) :
    D * NormedSpace.exp (t • A) = Real.cos (a * t) • D + (Real.sin (a * t) / a) • (D * A) := by
  set c : ℝ → Matrix ι ι ℝ := fun t =>
    Real.cos (a * t) • D + (Real.sin (a * t) / a) • (D * A) with hcdef
  have hc : ∀ t, HasDerivAt c (c t * A) t := fun t => by
    have h1 : HasDerivAt (fun t => Real.cos (a * t)) (-Real.sin (a * t) * a) t := by
      have := ((hasDerivAt_id t).const_mul a).cos
      refine this.congr_deriv ?_
      simp only [id, mul_one]
    have h2 : HasDerivAt (fun t => Real.sin (a * t) / a) (Real.cos (a * t)) t := by
      have := (((hasDerivAt_id t).const_mul a).sin).div_const a
      refine this.congr_deriv ?_
      simp only [id, mul_one]
      field_simp
    refine ((h1.smul_const D).add (h2.smul_const (D * A))).congr_deriv ?_
    simp only [hcdef, Matrix.add_mul, Matrix.smul_mul, h, smul_smul]
    field_simp
    module
  have := eq_mul_exp_smul_of_hasDerivAt hc t
  simp only [hcdef, mul_zero, Real.cos_zero, Real.sin_zero, zero_div, zero_smul, add_zero,
    one_smul] at this
  exact this.symm

/-- **The intertwining relations** between the eigenvalues `−a²` and `−b²` of `A²`:
`b DA = −a AD`, `A²D = −b²D`, `DA² = −a²D` (Milnor p. 145: `D` maps `M_h` to `M_j`
anticommuting with the complex structures `A/a`, `A/b`). -/
structure IsInterRel (A D : Matrix ι ι ℝ) (a b : ℝ) : Prop where
  rel : b • (D * A) = -a • (A * D)
  left : A * (A * D) = -(b ^ 2) • D
  right : D * A * A = -(a ^ 2) • D

omit [DecidableEq ι] in
theorem IsInterRel.conjTranspose {A D : Matrix ι ι ℝ} {a b : ℝ} (hA : Aᴴ = -A)
    (h : IsInterRel A D a b) : IsInterRel A Dᴴ b a where
  rel := by
    have := congrArg Matrix.conjTranspose h.rel
    simp only [conjTranspose_smul, conjTranspose_mul, conjTranspose_neg, star_trivial, hA,
      Matrix.mul_neg, smul_neg, neg_smul, neg_neg] at this
    rw [neg_smul, ← smul_neg, ← Matrix.neg_mul]
    exact this.symm
  left := by
    have := congrArg Matrix.conjTranspose h.right
    simp only [conjTranspose_smul, conjTranspose_mul, star_trivial, hA, Matrix.neg_mul,
      Matrix.mul_neg, neg_neg] at this
    exact this
  right := by
    have := congrArg Matrix.conjTranspose h.left
    simp only [conjTranspose_smul, conjTranspose_mul, star_trivial, hA, Matrix.neg_mul,
      Matrix.mul_neg, neg_neg] at this
    exact this

/-- **An intertwiner commutes with `exp(sA)` when `s(a + b) = 2π`** (Milnor p. 145: the conjugate
point at `t = 1/e`, `e = (a + b)/2`). -/
theorem IsInterRel.commute_exp {A D : Matrix ι ι ℝ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : IsInterRel A D a b) {s : ℝ} (hs : s * (a + b) = 2 * Real.pi) :
    D * NormedSpace.exp (s • A) = NormedSpace.exp (s • A) * D := by
  rw [mul_exp_smul_of_sq ha h.right, exp_smul_mul_of_sq hb h.left]
  have hDA : D * A = -(a / b) • (A * D) := by
    have := congrArg ((b⁻¹ : ℝ) • ·) h.rel
    simp only [smul_smul, inv_mul_cancel₀ hb.ne', one_smul] at this
    rw [this]; congr 1; field_simp
  have has : a * s = 2 * Real.pi - b * s := by linarith
  rw [hDA, has, Real.cos_two_pi_sub, Real.sin_two_pi_sub, smul_smul]
  congr 1
  congr 1
  field_simp

end Intertwiner

/-! ### Counting the Killing fields -/

section Count

variable {J : ℕ → Matrix ι ι ℝ} {k : ℕ} {p : Matrix ι ι ℝ}

/-- The commutator with `A`, as a linear map. -/
def adR (A : Matrix ι ι ℝ) : Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ where
  toFun X := X * A - A * X
  map_add' X Y := by simp only [Matrix.add_mul, Matrix.mul_add]; abel
  map_smul' c X := by simp only [Matrix.smul_mul, Matrix.mul_smul, smul_sub, RingHom.id_apply]

/-- **The count behind Milnor's index bounds** (pp. 145–146): given intertwiners `D_{j,l}` from
one eigenspace `M₀` of `A²` (eigenvalue `−a₀²`, `a₀ > 1`) to pieces `M_j` (eigenvalues `−b_j²`,
`b_j ≥ 1`), detected by projections `R` (onto `M₀`) and `Q_j` (onto `M_j`), with `AD_{j,l}`
independent for each `j`, the Killing fields of the skew parts `X = D − Dᵀ` give spaces `𝒳_τ`
at the parameters `τ_j = 2/(a₀ + b_j) ∈ (0, 1)` of total dimension `r₀ · #j`, satisfying the
hypotheses of `Morse.sum_finrank_le_formIndex` for `V = πA`. -/
theorem exists_killing_spaces {A : Matrix ι ι ℝ} (hA : Aᴴ = -A) {a₀ : ℝ} (ha : 1 < a₀)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (b : κ → ℝ) (hb : ∀ j, 1 ≤ b j) {r₀ : ℕ}
    (D : κ × Fin r₀ → Matrix ι ι ℝ) (hiso : ∀ i, D i - (D i)ᴴ ∈ isoAlg J k p)
    (hrel : ∀ i, IsInterRel A (D i) a₀ (b i.1))
    (R : Matrix ι ι ℝ) (hR : ∀ i, D i * R = D i) (hR' : ∀ i, (D i)ᴴ * R = 0)
    (Q : κ → Matrix ι ι ℝ) (hQ : ∀ j i, Q j * (A * D i) = if i.1 = j then A * D i else 0)
    (hind : ∀ j, LinearIndependent ℝ (fun l : Fin r₀ => A * D (j, l))) :
    ∃ (T : Finset ℝ) (𝒳 : ℝ → Submodule ℝ (Matrix ι ι ℝ)), (∀ τ ∈ T, τ ∈ Ioo (0 : ℝ) 1) ∧
      (∀ τ ∈ T, 𝒳 τ ≤ isoAlg J k p) ∧
      (∀ τ ∈ T, ∀ X ∈ 𝒳 τ, X * NormedSpace.exp (τ • (Real.pi • A)) =
        NormedSpace.exp (τ • (Real.pi • A)) * X) ∧
      (∀ τ ∈ T, ∀ X ∈ 𝒳 τ, X * (Real.pi • A) = (Real.pi • A) * X → X = 0) ∧
      ∑ τ ∈ T, finrank ℝ (𝒳 τ) = r₀ * Fintype.card κ := by
  classical
  have hbpos : ∀ j, 0 < b j := fun j => lt_of_lt_of_le one_pos (hb j)
  have ha0 : 0 < a₀ := lt_trans one_pos ha
  set τf : κ → ℝ := fun j => 2 / (a₀ + b j) with hτf
  set X : κ × Fin r₀ → Matrix ι ι ℝ := fun i => D i - (D i)ᴴ with hX
  set Y : κ × Fin r₀ → Matrix ι ι ℝ := fun i => adR A (X i) with hY
  -- `Y_i R = −((a₀ + b)/b) A D_i`
  have hYR : ∀ i, Y i * R = (-((a₀ + b i.1) / b i.1)) • (A * D i) := fun i => by
    have h1 := (hrel i).rel
    have h2 := ((hrel i).conjTranspose hA).rel
    have hDA : D i * A = (-(a₀ / b i.1)) • (A * D i) := by
      have := congrArg ((b i.1)⁻¹ • ·) h1
      simp only [smul_smul, inv_mul_cancel₀ (hbpos i.1).ne', one_smul] at this
      rw [this]; congr 1; field_simp
    have hDHA : (D i)ᴴ * A = (-(b i.1 / a₀)) • (A * (D i)ᴴ) := by
      have := congrArg (a₀⁻¹ • ·) h2
      simp only [smul_smul, inv_mul_cancel₀ ha0.ne', one_smul] at this
      rw [this]; congr 1; field_simp
    simp only [hY, hX, adR, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sub_mul, Matrix.mul_sub,
      hDA, hDHA, Matrix.smul_mul, Matrix.mul_assoc, hR, hR', Matrix.mul_zero, smul_zero,
      sub_zero]
    have hc : -((a₀ + b i.1) / b i.1) = -(a₀ / b i.1) - 1 := by
      field_simp [(hbpos i.1).ne']; ring
    rw [hc, sub_smul, one_smul]
  -- the `Y_i` are independent
  have hYind : LinearIndependent ℝ Y := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hj : ∑ l : Fin r₀, (g (i.1, l) * -((a₀ + b i.1) / b i.1)) • (A * D (i.1, l)) = 0 := by
      have := congrArg (fun M => Q i.1 * (M * R)) hg
      simp only [Matrix.zero_mul, Matrix.mul_zero] at this
      rw [Finset.sum_mul, Matrix.mul_sum] at this
      simp only [Matrix.smul_mul, Matrix.mul_smul, hYR, hQ, smul_smul] at this
      rw [Fintype.sum_prod_type] at this
      simp only [smul_ite, smul_zero] at this
      rw [Finset.sum_eq_single i.1] at this
      · simpa only [if_true] using this
      · intro j _ hj
        exact Finset.sum_eq_zero fun l _ => if_neg hj
      · intro h; exact absurd (Finset.mem_univ _) h
    have := Fintype.linearIndependent_iff.1 (hind i.1) _ hj i.2
    have hne : -((a₀ + b i.1) / b i.1) ≠ 0 := by
      have : 0 < (a₀ + b i.1) / b i.1 := div_pos (by linarith [hbpos i.1]) (hbpos i.1)
      linarith
    exact (mul_eq_zero.1 this).resolve_right hne
  have hXind : LinearIndependent ℝ X := LinearIndependent.of_comp (adR A) hYind
  -- the commutation of the generators with `exp(τ_j πA)`
  have hτpos : ∀ j, 0 < a₀ + b j := fun j => by linarith [hbpos j]
  have hXcomm : ∀ i, X i * NormedSpace.exp (τf i.1 • (Real.pi • A)) =
      NormedSpace.exp (τf i.1 • (Real.pi • A)) * X i := fun i => by
    have hs : (τf i.1 * Real.pi) * (a₀ + b i.1) = 2 * Real.pi := by
      simp only [hτf]; field_simp [(hτpos i.1).ne']
    rw [smul_smul]
    have e1 := (hrel i).commute_exp ha0 (hbpos i.1) hs
    have e2 := ((hrel i).conjTranspose hA).commute_exp (hbpos i.1) ha0
      (by rw [add_comm]; exact hs)
    simp only [hX, Matrix.sub_mul, Matrix.mul_sub, e1, e2]
  set T := Finset.univ.image τf with hT
  set 𝒳 : ℝ → Submodule ℝ (Matrix ι ι ℝ) := fun τ =>
    Submodule.span ℝ (Set.range fun i : {i : κ × Fin r₀ // τf i.1 = τ} => X i) with h𝒳
  refine ⟨T, 𝒳, ?_, ?_, ?_, ?_, ?_⟩
  · intro τ hτ
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hτ
    refine ⟨div_pos two_pos (hτpos j), (div_lt_one (hτpos j)).2 ?_⟩
    linarith [hb j]
  · intro τ _
    exact Submodule.span_le.2 (Set.range_subset_iff.2 fun i => hiso i.1)
  · intro τ _ M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      have := hXcomm i.1
      rwa [i.2] at this
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.add_mul, Matrix.mul_add, hx, hy]
    | smul c x _ hx => rw [Matrix.smul_mul, Matrix.mul_smul, hx]
  · intro τ _ M hM hMc
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hM
    have hzero : ∑ i, c i • Y i.1 = 0 := by
      have h1 : adR A (∑ i, c i • X i.1) = 0 := by
        simp only [adR, LinearMap.coe_mk, AddHom.coe_mk]
        have := congrArg ((Real.pi)⁻¹ • ·) hMc
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul,
          inv_mul_cancel₀ Real.pi_ne_zero, one_smul] at this
        rw [this, sub_self]
      rw [map_sum] at h1
      simpa only [map_smul] using h1
    have hc := Fintype.linearIndependent_iff.1
      (hYind.comp (Subtype.val : {i : κ × Fin r₀ // τf i.1 = τ} → κ × Fin r₀)
        Subtype.val_injective) c hzero
    simp [hc]
  · have hfin : ∀ τ, finrank ℝ (𝒳 τ) = Fintype.card {i : κ × Fin r₀ // τf i.1 = τ} :=
      fun τ => finrank_span_eq_card (hXind.comp _ Subtype.val_injective)
    simp only [hfin, Fintype.card_subtype]
    rw [← Finset.card_eq_sum_card_fiberwise (f := fun i : κ × Fin r₀ => τf i.1)
      (fun i _ => Finset.mem_image_of_mem τf (Finset.mem_univ _))]
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, mul_comm]

end Count

end Morse
