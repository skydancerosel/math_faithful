import Morse.Chapter15.IndexBound
import Morse.Chapter15.SplittingTwoData

/-!
Milnor, *Morse Theory*, §24, p. 148 (case `k ≡ 2 (mod 4)`); Exposition/Chapter15.md, §6.

# Killing fields for `k ≡ 2 (mod 4)`: several conjugate points per pair of pieces

## Milnor's text, paraphrased

(p. 148) With `C : M_h → M_j` commuting with `i` and anticommuting with `J`, `B = C − Cᵀ` is an
eigenvector of `K_A` with eigenvalue `(a_h − a_j)²/4`; for `a_h > a_j` this gives
`(a_h − a_j)/2 − 1` conjugate points in `(0, 1)`, and the `B`'s of different pairs are
independent, so `2λ ≥ Σ_{a_h > a_j} (a_h − a_j − 2)`.

## What is formalized

* `Morse.IsInterRelI A ii D a b`: `DA = a·Di`, `AD = b·iD`, `Di = iD` (`D : M_a → M_b`);
  `Morse.IsInterRelI.mul_exp`, `Morse.IsInterRelI.exp_mul` (`D exp(sA) = cos(sa)D + sin(sa)Di`
  and on the left), `Morse.IsInterRelI.commute_exp`: **`Di` commutes with `exp(sA)` when
  `s(a − b) ∈ 2πℤ`**, `Morse.IsInterRelI.conjTranspose`.
* `Morse.exists_killing_spaces_gen`: **the count with several parameters per field**: from
  independent `[X_i, V]` and parameters `τ_{i,s} ∈ (0, 1)`, `s < n_i` (distinct for fixed `i`),
  at which `X_i` commutes with `exp(τV)`, spaces `𝒳_τ` of total dimension `Σ n_i`.
* `Morse.exists_killing_spaces_two`: the Killing fields `X_j = D_ji − (D_ji)ᵀ` with
  `τ_{j,s} = 2(s + 1)/(a₀ − b_j)`, `s < (a₀ − b_j)/2 − 1`.

## What Milnor leaves implicit

* The eigenvector `B` is again `[X, A]` for a Killing field: here `X = Di − (Di)ᵀ` commutes with
  `J` and the `J_α` (`D` and `i` both anticommute with `J`), and `[X, A]` restricted to `M₀`
  is `(b − a₀)D`.
-/

open Matrix Set Filter Topology Module
open scoped Morse.MatrixInner RealInnerProductSpace

noncomputable section

namespace Morse

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {J : ℕ → Matrix ι ι ℝ} {k : ℕ}

/-! ### Intertwiners between multiples of `i` -/

section InterI

/-- `D : M_a → M_b` intertwines `A = a·i` with `A = b·i`. -/
structure IsInterRelI (A ii D : Matrix ι ι ℝ) (a b : ℝ) : Prop where
  da : D * A = a • (D * ii)
  ad : A * D = b • (ii * D)
  di : D * ii = ii * D

variable {A ii D : Matrix ι ι ℝ} {a b : ℝ}

/-- `D exp(sA) = cos(sa) D + sin(sa) Di`. -/
theorem IsInterRelI.mul_exp (h : IsInterRelI A ii D a b) (hii : ii * ii = -1)
    (hAi : A * ii = ii * A) (s : ℝ) :
    D * NormedSpace.exp (s • A) = Real.cos (a * s) • D + Real.sin (a * s) • (D * ii) := by
  set c : ℝ → Matrix ι ι ℝ := fun s => Real.cos (a * s) • D + Real.sin (a * s) • (D * ii)
    with hcdef
  have hc : ∀ t, HasDerivAt c (c t * A) t := fun t => by
    have h1 : HasDerivAt (fun t => Real.cos (a * t)) (-Real.sin (a * t) * a) t := by
      simpa using ((hasDerivAt_id t).const_mul a).cos
    have h2 : HasDerivAt (fun t => Real.sin (a * t)) (Real.cos (a * t) * a) t := by
      simpa using ((hasDerivAt_id t).const_mul a).sin
    refine ((h1.smul_const D).add (h2.smul_const (D * ii))).congr_deriv ?_
    simp only [hcdef, Matrix.add_mul, Matrix.smul_mul, h.da, Matrix.mul_assoc, ← hAi,
      ← Matrix.mul_assoc D A ii, Matrix.smul_mul, Matrix.mul_assoc, hii, Matrix.mul_neg,
      Matrix.mul_one, smul_smul]
    module
  have := eq_mul_exp_smul_of_hasDerivAt hc s
  simpa [hcdef] using this.symm

/-- `exp(sA) D = cos(sb) D + sin(sb) iD`. -/
theorem IsInterRelI.exp_mul (h : IsInterRelI A ii D a b) (hii : ii * ii = -1)
    (hAi : A * ii = ii * A) (s : ℝ) :
    NormedSpace.exp (s • A) * D = Real.cos (b * s) • D + Real.sin (b * s) • (ii * D) := by
  set c : ℝ → Matrix ι ι ℝ := fun s => Real.cos (b * s) • D + Real.sin (b * s) • (ii * D)
    with hcdef
  have hc : ∀ t, HasDerivAt c (A * c t) t := fun t => by
    have h1 : HasDerivAt (fun t => Real.cos (b * t)) (-Real.sin (b * t) * b) t := by
      simpa using ((hasDerivAt_id t).const_mul b).cos
    have h2 : HasDerivAt (fun t => Real.sin (b * t)) (Real.cos (b * t) * b) t := by
      simpa using ((hasDerivAt_id t).const_mul b).sin
    refine ((h1.smul_const D).add (h2.smul_const (ii * D))).congr_deriv ?_
    simp only [hcdef, Matrix.mul_add, Matrix.mul_smul, h.ad, ← Matrix.mul_assoc A ii D, hAi,
      Matrix.mul_assoc ii A D, Matrix.mul_smul, ← Matrix.mul_assoc ii ii D, hii,
      Matrix.neg_mul, Matrix.one_mul, smul_smul]
    module
  have := eq_exp_smul_mul_of_hasDerivAt hc s
  simpa [hcdef] using this.symm

/-- **`Di` commutes with `exp(sA)` when `s(a − b) ∈ 2πℤ`** (the conjugate points
`t = 2m/(a − b)` of Milnor p. 148). -/
theorem IsInterRelI.commute_exp (h : IsInterRelI A ii D a b) (hii : ii * ii = -1)
    (hAi : A * ii = ii * A) {s : ℝ} {m : ℤ} (hs : a * s = b * s + m * (2 * Real.pi)) :
    D * ii * NormedSpace.exp (s • A) = NormedSpace.exp (s • A) * (D * ii) := by
  have hc : Commute ii (s • A) := (show Commute ii A from hAi.symm).smul_right s
  have hcomm : ii * NormedSpace.exp (s • A) = NormedSpace.exp (s • A) * ii := hc.exp_right.eq
  rw [Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc, h.mul_exp hii hAi, ← Matrix.mul_assoc,
    h.exp_mul hii hAi, hs, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi, h.di]

omit [DecidableEq ι] in
theorem IsInterRelI.conjTranspose (h : IsInterRelI A ii D a b) (hA : Aᴴ = -A)
    (hiiH : iiᴴ = -ii) : IsInterRelI A ii Dᴴ b a where
  da := by
    have := congrArg Matrix.conjTranspose h.ad
    simp only [conjTranspose_mul, conjTranspose_smul, star_trivial, hA, hiiH, Matrix.mul_neg,
      smul_neg, neg_inj] at this
    exact this
  ad := by
    have := congrArg Matrix.conjTranspose h.da
    simp only [conjTranspose_mul, conjTranspose_smul, star_trivial, hA, hiiH, Matrix.neg_mul,
      smul_neg, neg_inj] at this
    exact this
  di := by
    have := congrArg Matrix.conjTranspose h.di
    simp only [conjTranspose_mul, hiiH, Matrix.mul_neg, Matrix.neg_mul, neg_inj] at this
    exact this.symm

end InterI

/-! ### Counting Killing fields with several parameters each -/

section Count

variable {p : Matrix ι ι ℝ}

/-- **The count of Killing fields** (Milnor p. 148): from fields `X_i ∈ isoAlg` with `[X_i, V]`
independent, and for each `i` distinct parameters `τ_{i,s} ∈ (0, 1)`, `s < n_i`, at which `X_i`
commutes with `exp(τV)`, spaces `𝒳_τ` as in `Morse.sum_finrank_le_formIndex` of total dimension
`Σ n_i`. -/
theorem exists_killing_spaces_gen {V : Matrix ι ι ℝ} {κ : Type*} [Fintype κ]
    (X : κ → Matrix ι ι ℝ) (hiso : ∀ i, X i ∈ isoAlg J k p)
    (hind : LinearIndependent ℝ fun i => adR V (X i)) (n : κ → ℕ)
    (τf : (Σ i, Fin (n i)) → ℝ) (hτ : ∀ x, τf x ∈ Ioo (0 : ℝ) 1)
    (hτinj : ∀ i (s s' : Fin (n i)), τf ⟨i, s⟩ = τf ⟨i, s'⟩ → s = s')
    (hcomm : ∀ x, X x.1 * NormedSpace.exp (τf x • V) = NormedSpace.exp (τf x • V) * X x.1) :
    ∃ (T : Finset ℝ) (𝒳 : ℝ → Submodule ℝ (Matrix ι ι ℝ)), (∀ τ ∈ T, τ ∈ Ioo (0 : ℝ) 1) ∧
      (∀ τ ∈ T, 𝒳 τ ≤ isoAlg J k p) ∧
      (∀ τ ∈ T, ∀ Y ∈ 𝒳 τ, Y * NormedSpace.exp (τ • V) = NormedSpace.exp (τ • V) * Y) ∧
      (∀ τ ∈ T, ∀ Y ∈ 𝒳 τ, Y * V = V * Y → Y = 0) ∧
      ∑ τ ∈ T, finrank ℝ (𝒳 τ) = ∑ i, n i := by
  classical
  have hfib : ∀ τ, Function.Injective (fun x : {x : (Σ i, Fin (n i)) // τf x = τ} => x.1.1) := by
    rintro τ ⟨⟨i, s⟩, hs⟩ ⟨⟨i', s'⟩, hs'⟩ he
    simp only at he
    subst he
    have := hτinj i s s' (hs.trans hs'.symm)
    subst this
    rfl
  have hYfib : ∀ τ, LinearIndependent ℝ
      (fun x : {x : (Σ i, Fin (n i)) // τf x = τ} => adR V (X x.1.1)) := fun τ =>
    hind.comp _ (hfib τ)
  have hXfib : ∀ τ, LinearIndependent ℝ
      (fun x : {x : (Σ i, Fin (n i)) // τf x = τ} => X x.1.1) := fun τ =>
    LinearIndependent.of_comp (adR V) (hYfib τ)
  set T := Finset.univ.image τf with hT
  set 𝒳 : ℝ → Submodule ℝ (Matrix ι ι ℝ) := fun τ =>
    Submodule.span ℝ (Set.range fun x : {x : (Σ i, Fin (n i)) // τf x = τ} => X x.1.1) with h𝒳
  refine ⟨T, 𝒳, ?_, ?_, ?_, ?_, ?_⟩
  · intro τ hτT
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hτT
    exact hτ x
  · intro τ _
    exact Submodule.span_le.2 (Set.range_subset_iff.2 fun x => hiso _)
  · intro τ _ M hM
    induction hM using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, rfl⟩ := hy
      have := hcomm x.1
      rwa [x.2] at this
    | zero => simp
    | add y z _ _ hy hz => rw [Matrix.add_mul, Matrix.mul_add, hy, hz]
    | smul c y _ hy => rw [Matrix.smul_mul, Matrix.mul_smul, hy]
  · intro τ _ M hM hMc
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hM
    have hzero : ∑ x, c x • adR V (X x.1.1) = 0 := by
      have h1 : adR V (∑ x, c x • X x.1.1) = 0 := by
        simp only [adR, LinearMap.coe_mk, AddHom.coe_mk]
        rw [hMc, sub_self]
      rw [map_sum] at h1
      simpa only [map_smul] using h1
    have hc := Fintype.linearIndependent_iff.1 (hYfib τ) c hzero
    simp [hc]
  · have hfin : ∀ τ, finrank ℝ (𝒳 τ) = Fintype.card {x : (Σ i, Fin (n i)) // τf x = τ} :=
      fun τ => finrank_span_eq_card (hXfib τ)
    simp only [hfin, Fintype.card_subtype]
    rw [← Finset.card_eq_sum_card_fiberwise (f := τf)
      (fun x _ => Finset.mem_image_of_mem τf (Finset.mem_univ _))]
    rw [Finset.card_univ, Fintype.card_sigma]
    simp

/-- **The Killing fields of the pairs `(h₀, j)`** (Milnor p. 148): `X_j = D_ji − (D_ji)ᵀ`, with
the parameters `τ_{j,s} = 2(s + 1)/(a₀ − b_j)`, `s < (a₀ − b_j)/2 − 1`, give spaces `𝒳_τ` of
total dimension `Σ_j ((a₀ − b_j)/2 − 1)` for `V = πA`. -/
theorem exists_killing_spaces_two {A ii : Matrix ι ι ℝ} (hA : Aᴴ = -A) (hii : ii * ii = -1)
    (hiiH : iiᴴ = -ii) (hAi : A * ii = ii * A) {κ : Type*} [Fintype κ] [DecidableEq κ]
    (D : κ → Matrix ι ι ℝ) (a₀ : ℤ) (b : κ → ℤ) (hb : ∀ i, b i < a₀)
    (heven : ∀ i, Even (a₀ - b i)) (hrel : ∀ i, IsInterRelI A ii (D i) a₀ (b i))
    (R : Matrix ι ι ℝ) (hR : ∀ i, D i * R = D i) (hR' : ∀ i, (D i)ᴴ * R = 0)
    (hRA : R * A = A * R) (hRi : R * ii = ii * R) (Q : κ → Matrix ι ι ℝ)
    (hQ : ∀ j' i, Q j' * D i = if i = j' then D i else 0) (hD0 : ∀ i, D i ≠ 0)
    (hiso : ∀ i, D i * ii - (D i * ii)ᴴ ∈ isoAlg J k p) :
    ∃ (T : Finset ℝ) (𝒳 : ℝ → Submodule ℝ (Matrix ι ι ℝ)), (∀ τ ∈ T, τ ∈ Ioo (0 : ℝ) 1) ∧
      (∀ τ ∈ T, 𝒳 τ ≤ isoAlg J k p) ∧
      (∀ τ ∈ T, ∀ Y ∈ 𝒳 τ, Y * NormedSpace.exp (τ • (Real.pi • A)) =
        NormedSpace.exp (τ • (Real.pi • A)) * Y) ∧
      (∀ τ ∈ T, ∀ Y ∈ 𝒳 τ, Y * (Real.pi • A) = (Real.pi • A) * Y → Y = 0) ∧
      ∑ τ ∈ T, finrank ℝ (𝒳 τ) = ∑ i, ((a₀ - b i) / 2 - 1).toNat := by
  classical
  set X : κ → Matrix ι ι ℝ := fun i => D i * ii - (D i * ii)ᴴ with hXdef
  have hrelH : ∀ i, IsInterRelI A ii (D i)ᴴ (b i) a₀ := fun i => (hrel i).conjTranspose hA hiiH
  have hX : ∀ i, X i = D i * ii + (D i)ᴴ * ii := fun i => by
    change D i * ii - (D i * ii)ᴴ = _
    rw [conjTranspose_mul, hiiH, Matrix.neg_mul, (hrelH i).di, sub_neg_eq_add]
  -- `[X_i, A] R = (b_i − a₀) D_i`
  have hXR : ∀ i, (X i * A - A * X i) * R = ((b i : ℝ) - a₀) • D i := fun i => by
    have e1 : X i * R = D i * ii := by
      rw [hX, Matrix.add_mul, Matrix.mul_assoc, ← hRi, ← Matrix.mul_assoc, hR,
        Matrix.mul_assoc (D i)ᴴ, ← hRi, ← Matrix.mul_assoc, hR', Matrix.zero_mul, add_zero]
    have e2 : X i * A * R = -((a₀ : ℝ) • D i) := by
      rw [Matrix.mul_assoc, ← hRA, ← Matrix.mul_assoc, e1, Matrix.mul_assoc, ← hAi,
        ← Matrix.mul_assoc, (hrel i).da, Matrix.smul_mul, Matrix.mul_assoc, hii, Matrix.mul_neg,
        Matrix.mul_one, smul_neg]
    have e3 : A * X i * R = -((b i : ℝ) • D i) := by
      rw [Matrix.mul_assoc, e1, ← Matrix.mul_assoc, (hrel i).ad, Matrix.smul_mul,
        Matrix.mul_assoc, (hrel i).di, ← Matrix.mul_assoc, hii, Matrix.neg_mul, Matrix.one_mul,
        smul_neg]
    rw [Matrix.sub_mul, e2, e3, sub_smul]
    abel
  have hind : LinearIndependent ℝ fun i => adR (Real.pi • A) (X i) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j'
    have h1 := congrArg (fun M => Q j' * (M * R)) hc
    simp only [Matrix.zero_mul, Matrix.mul_zero, Finset.sum_mul, Matrix.mul_sum,
      Matrix.smul_mul, Matrix.mul_smul] at h1
    have h2 : ∀ i, adR (Real.pi • A) (X i) * R = (Real.pi * ((b i : ℝ) - a₀)) • D i := fun i => by
      simp only [adR, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_smul, Matrix.smul_mul,
        ← smul_sub]
      rw [hXR i, smul_smul]
    simp only [h2, Matrix.mul_smul, hQ, smul_ite, smul_zero] at h1
    rw [Finset.sum_eq_single j' (fun i _ hi => if_neg hi) (fun h => absurd (Finset.mem_univ _) h),
      if_pos rfl, smul_smul] at h1
    have hne : c j' * (Real.pi * ((b j' : ℝ) - a₀)) ≠ 0 → False := fun h0 =>
      hD0 j' ((smul_eq_zero.1 h1).resolve_left h0)
    by_contra hcj
    apply hne
    have hb' : ((b j' : ℝ) - a₀) ≠ 0 := by
      have : (b j' : ℝ) < a₀ := by exact_mod_cast hb j'
      linarith
    exact mul_ne_zero hcj (mul_ne_zero Real.pi_ne_zero hb')
  set n : κ → ℕ := fun i => ((a₀ - b i) / 2 - 1).toNat with hndef
  set τf : (Σ i, Fin (n i)) → ℝ := fun x => 2 * ((x.2 : ℝ) + 1) / ((a₀ : ℝ) - b x.1) with hτdef
  have hpos : ∀ i, (0 : ℝ) < (a₀ : ℝ) - b i := fun i => by
    have : (b i : ℝ) < a₀ := by exact_mod_cast hb i
    linarith
  have hlt : ∀ x : (Σ i, Fin (n i)), 2 * ((x.2 : ℝ) + 1) < (a₀ : ℝ) - b x.1 := fun x => by
    obtain ⟨m, hm⟩ := heven x.1
    have h2 := x.2.2
    simp only [hndef] at h2
    rw [hm, show (m + m) / 2 = m by omega] at h2
    have h3 : 2 * ((x.2 : ℕ) : ℤ) + 2 < m + m := by omega
    have h4 : (a₀ : ℝ) - b x.1 = ((m + m : ℤ) : ℝ) := by rw [← hm]; push_cast; ring
    rw [h4]
    have h5 : 2 * (((x.2 : ℕ) : ℤ) : ℝ) + 2 < ((m + m : ℤ) : ℝ) := by exact_mod_cast h3
    push_cast at h5 ⊢
    linarith
  obtain ⟨T, 𝒳, h1, h2, h3, h4, h5⟩ := exists_killing_spaces_gen (V := Real.pi • A) X hiso hind
    n τf (fun x => ⟨div_pos (by positivity) (hpos x.1),
      (div_lt_one (hpos x.1)).2 (hlt x)⟩)
    (fun i s s' hss' => by
      simp only [hτdef] at hss'
      rw [div_left_inj' (hpos i).ne'] at hss'
      exact Fin.ext (by exact_mod_cast (show (s : ℝ) = s' by linarith)))
    (fun x => by
      have hs : (a₀ : ℝ) * (τf x * Real.pi) =
          (b x.1 : ℝ) * (τf x * Real.pi) + ((x.2 : ℕ) + 1 : ℤ) * (2 * Real.pi) := by
        simp only [hτdef]; push_cast; field_simp [(hpos x.1).ne']; ring
      have hs' : (b x.1 : ℝ) * (τf x * Real.pi) =
          (a₀ : ℝ) * (τf x * Real.pi) + ((-(((x.2 : ℕ) : ℤ) + 1) : ℤ) : ℝ) * (2 * Real.pi) := by
        rw [hs]; push_cast; ring
      have c1 := (hrel x.1).commute_exp hii hAi hs
      have c2 := (hrelH x.1).commute_exp hii hAi hs'
      rw [smul_smul, hX, Matrix.add_mul, Matrix.mul_add, c1, c2])
  exact ⟨T, 𝒳, h1, h2, h3, h4, h5⟩

end Count

end Morse
