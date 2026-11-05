import Morse.Chapter9.IndexContinuity

/-!
Milnor, *Morse Theory*, §15, pp. 85–87: Assertions (3) and (4) in the proof of the index theorem,
for a submanifold `N ⊆ ℝᴷ` with the induced metric.

# Assertions (3) and (4)

## Milnor's text, paraphrased

* **Assertion (3)** (p. 85): for all sufficiently small `ε > 0`, `λ(τ − ε) = λ(τ)`.
* **Assertion (4)** (p. 86): if `ν` is the nullity of `(E_0^τ)_**`, then
  `λ(τ + ε) = λ(τ) + ν` for all sufficiently small `ε > 0`.  The inequality `≤` comes from the
  continuity of `H_τ` (see `Morse/Chapter9/IndexContinuity.lean`).  For `≥` (p. 87): let
  `W₁, …, W_λ` span a space on which `(E_0^τ)_**` is negative definite, `J₁, …, J_ν` be a basis of
  the Jacobi fields vanishing at `0` and `τ`; the vectors `DJ_h/dt(τ)` are linearly independent,
  so there are fields `X₁, …, X_ν` along `γ_{τ+ε}` with `⟨DJ_h/dt(τ), X_k(τ)⟩ = δ_{hk}`.  Extend
  `W_i`, `J_h` by `0` over `[τ, τ + ε]`; then `E_**(J_h, W_i) = 0` and `E_**(J_h, X_k) = 2δ_{hk}`.
  For small `c`, the `λ + ν` fields `W_i`, `c⁻¹J_h − cX_h` span a space on which `E_**` is
  negative definite: its matrix is `[[(E_**(W_i, W_j)), cA], [cAᵗ, −4I + c²B]]`.

## In the embedded setting

* `Morse.assertion_3`, `Morse.assertion_4_le`, `Morse.assertion_4_ge`, and **Assertion (4)**
  itself, `Morse.assertion_4`.
* `Morse.le_formIndex_of_compound`: the compound-matrix argument as a lemma of linear algebra
  (the matrix at `c = 0` is `diag(N, −4I)`, negative definite, hence so is the matrix for small
  `c ≠ 0` by Lemma 15.A (3); a negative definite Gram matrix makes the fields independent).
* `Morse.energyHessian_cut`: for a Jacobi field `J` vanishing at `0` and `τ`, cut off at `τ`,
  `E_**(J, Z) = 2⟨Z(τ), DJ/dt(τ)⟩` (the second variation formula: the only jump is at `τ`).
* `Morse.exists_dual`: the fields `X_k` exist (a dual basis to the `DJ_h/dt(τ)` in `T_{γ(τ)}N`,
  times a bump function).

## What Milnor leaves implicit

* "It is possible to choose `ν` vector fields `X_1, …, X_ν`": the `DJ_h/dt(τ)` are linearly
  independent (uniqueness of Jacobi fields), so a dual family exists in their span; a bump function
  times the tangent projection of a constant vector gives the fields.
* "If `c` is sufficiently small, this compound matrix is certainly negative definite": openness of
  negative definiteness (Lemma 15.A (3)); and a negative definite Gram matrix forces the
  `λ + ν` fields to be linearly independent, so they span a space of dimension `λ + ν`.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

/-! ### The compound matrix -/

section Compound

variable {P : Type*} [AddCommGroup P] [Module ℝ P]

/-- **Milnor's compound matrix argument** (p. 87), as linear algebra.  Let `E` be symmetric,
`U : ℝ^λ → P` with `E` negative definite on its image (`E(U a, U a) < 0` for `a ≠ 0`), and
`J, X : ℝ^ν → P` with `E(J b, U a) = 0`, `E(J b, J b') = 0`, `E(J b, X b') = 2⟨b, b'⟩`.  Then the
index of `E` is at least `λ + ν`: for small `c ≠ 0`, `E` is negative definite on the image of
`(a, b) ↦ U a + c⁻¹ J b − c X b`. -/
theorem le_formIndex_of_compound {E : LinearMap.BilinForm ℝ P} (hE : E.IsSymm) {k ν : ℕ}
    (U : (Fin k → ℝ) →ₗ[ℝ] P) (J X : (Fin ν → ℝ) →ₗ[ℝ] P)
    (hU : ∀ a, a ≠ 0 → E (U a) (U a) < 0) (hJU : ∀ b a, E (J b) (U a) = 0)
    (hJJ : ∀ b b', E (J b) (J b') = 0) (hJX : ∀ b b', E (J b) (X b') = 2 * ∑ h, b h * b' h) :
    ((k + ν : ℕ) : ℕ∞) ≤ formIndex E := by
  have hsymm := LinearMap.BilinForm.isSymm_def.1 hE
  -- the four bilinear forms of the compound matrix
  set f₁ : ((Fin k → ℝ) × (Fin ν → ℝ)) →ₗ[ℝ] P := U ∘ₗ LinearMap.fst ℝ _ _
  set f₂ : ((Fin k → ℝ) × (Fin ν → ℝ)) →ₗ[ℝ] P := J ∘ₗ LinearMap.snd ℝ _ _
  set f₃ : ((Fin k → ℝ) × (Fin ν → ℝ)) →ₗ[ℝ] P := X ∘ₗ LinearMap.snd ℝ _ _
  have hf₁ : ∀ e, f₁ e = U e.1 := fun _ => rfl
  have hf₂ : ∀ e, f₂ e = J e.2 := fun _ => rfl
  have hf₃ : ∀ e, f₃ e = X e.2 := fun _ => rfl
  set dot : LinearMap.BilinForm ℝ ((Fin k → ℝ) × (Fin ν → ℝ)) :=
    LinearMap.mk₂ ℝ (fun e e' => ∑ h, e.2 h * e'.2 h)
    (fun e e' e'' => by
      simp only [Prod.snd_add, Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun c e e' => by
      simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc])
    (fun e e' e'' => by
      simp only [Prod.snd_add, Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c e e' => by
      simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun h _ => by ring)
  set G : ℝ → LinearMap.BilinForm ℝ ((Fin k → ℝ) × (Fin ν → ℝ)) := fun c => E.compl₁₂ f₁ f₁ -
    c • (E.compl₁₂ f₁ f₃ + E.compl₁₂ f₃ f₁) - (4 : ℝ) • dot + c ^ 2 • E.compl₁₂ f₃ f₃
  have hG : ∀ c e e', G c e e' = E (U e.1) (U e'.1) -
      c * (E (U e.1) (X e'.2) + E (X e.2) (U e'.1)) -
      4 * ∑ h, e.2 h * e'.2 h + c ^ 2 * E (X e.2) (X e'.2) := fun c e e' => by
    simp only [G, dot, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.compl₁₂_apply, smul_eq_mul, LinearMap.mk₂_apply, hf₁, hf₃]
    try ring
  -- `G 0` is negative definite
  have hG0 : IsNegDefOn (G 0) ⊤ := by
    rintro ⟨a, b⟩ - he
    rw [hG]
    have hb : 0 ≤ ∑ h, b h * b h := Finset.sum_nonneg fun h _ => mul_self_nonneg _
    by_cases ha : a = 0
    · have hb0 : b ≠ 0 := fun h => he (by rw [ha, h]; rfl)
      obtain ⟨h₀, hh₀⟩ : ∃ h, b h ≠ 0 := by
        by_contra hall; push Not at hall; exact hb0 (funext hall)
      have hpos : 0 < ∑ h, b h * b h := lt_of_lt_of_le (mul_self_pos.2 hh₀)
        (Finset.single_le_sum (f := fun h => b h * b h) (fun h _ => mul_self_nonneg _)
          (Finset.mem_univ h₀))
      simp only [ha, map_zero, LinearMap.zero_apply]
      norm_num
      linarith
    · have := hU a ha
      norm_num
      linarith
  -- so is `G c` for small `c ≠ 0`
  have hcont : ∀ x ∈ (⊤ : Submodule ℝ ((Fin k → ℝ) × (Fin ν → ℝ))),
      ∀ y ∈ (⊤ : Submodule ℝ ((Fin k → ℝ) × (Fin ν → ℝ))),
      ContinuousAt (fun c => G c x y) 0 := fun x _ y _ => by
    simp only [hG]
    fun_prop
  have hev := eventually_isNegDefOn hcont hG0
  obtain ⟨c, hc, hc0⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : {(0 : ℝ)}ᶜ ∈ 𝓝[≠] (0 : ℝ))).exists
  -- `G c` is the Gram form of the fields `U a + c⁻¹ J b − c X b`
  set Φ : ((Fin k → ℝ) × (Fin ν → ℝ)) →ₗ[ℝ] P := f₁ + c⁻¹ • f₂ - c • f₃
  have hΦ : ∀ e e', E (Φ e) (Φ e') = G c e e' := by
    intro e e'
    have h1 : E (J e.2) (U e'.1) = 0 := hJU _ _
    have h2 : E (U e.1) (J e'.2) = 0 := by rw [hsymm]; exact hJU _ _
    have h3 : E (J e.2) (J e'.2) = 0 := hJJ _ _
    have h4 : E (J e.2) (X e'.2) = 2 * ∑ h, e.2 h * e'.2 h := hJX _ _
    have h5 : E (X e.2) (J e'.2) = 2 * ∑ h, e.2 h * e'.2 h := by
      rw [hsymm, hJX]
      congr 1
      exact Finset.sum_congr rfl fun h _ => mul_comm _ _
    simp only [Φ, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, map_add,
      map_sub, map_smul, smul_eq_mul, hf₁, hf₂, hf₃, h1, h2, h3, h4, h5, hG]
    have hc0' : c ≠ 0 := hc0
    field_simp
    ring
  have hle := formIndex_le_of_map Φ hΦ
  have hge : ((finrank ℝ (⊤ : Submodule ℝ ((Fin k → ℝ) × (Fin ν → ℝ))) : ℕ) : ℕ∞) ≤
      formIndex (G c) := le_formIndex hc
  rw [finrank_top, Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun] at hge
  exact hge.trans hle

end Compound

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N} {γ : ℝ → V}
  (hc : IsSmoothCurveIn hN γ)

/-! ### Assertion (3) -/

/-- The last division point of a fine subdivision of `[0, τ]` lies before `τ`. -/
theorem max_lt_of_isFine {B : Finset ℝ} {τ : ℝ} (hτ : 0 < τ) (hB : IsFine hN γ hc B τ) :
    (insert (0 : ℝ) B).max' (Finset.insert_nonempty _ _) < τ := by
  rcases Finset.mem_insert.1 ((insert (0 : ℝ) B).max'_mem (Finset.insert_nonempty _ _)) with h | h
  · rw [h]; exact hτ
  · exact (hB.1 _ h).2

/-- **Assertion (3)** (Milnor p. 85): `λ` is continuous from the left. -/
theorem assertion_3 {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∀ᶠ τ' in 𝓝[<] τ, indexUpTo hN γ hc τ' = indexUpTo hN γ hc τ := by
  classical
  obtain ⟨B, hB, hlast⟩ := exists_isFine hc hτ
  have h₀ : τ ∈ validFor hN γ hc B := ⟨hB, hτ, hτ1⟩
  set m := (insert (0 : ℝ) B).max' (Finset.insert_nonempty _ _)
  have hmτ : m < τ := max_lt_of_isFine hc hτ hB
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (indexUpTo_lt_top hc hτ hτ1).ne
  obtain ⟨S, hSfin, hSneg, hSk⟩ := exists_isNegDefOn_of_formIndex_eq
    (by rw [formIndex_Hform hc h₀, ← hk])
  have hev := eventually_isNegDefOn_within h₀
    (fun x _ y _ => continuousWithinAt_Hform hc h₀ x y) hSneg
  have hvalid : ∀ τ' ∈ Ioo m τ, τ' ∈ validFor hN γ hc B := fun τ' hτ' =>
    mem_validFor_of_near hc hτ hB hlast (hτ'.2.le.trans hτ1)
      (by linarith [hτ'.2, fineMesh_pos hc]) hτ'.1
  have hmem : validFor hN γ hc B ∈ 𝓝[<] τ :=
    mem_of_superset (Ioo_mem_nhdsLT hmτ) hvalid
  filter_upwards [nhdsWithin_le_of_mem hmem hev, Ioo_mem_nhdsLT hmτ] with τ' hneg hτ'
  refine le_antisymm (indexUpTo_mono hc hτ'.2.le) ?_
  rw [← formIndex_Hform hc (hvalid τ' hτ'), ← hk, ← hSk]
  exact le_formIndex hneg

/-! ### Assertion (4) -/

/-- **Assertion (4), `≤`** (Milnor p. 86): `λ(τ + ε) ≤ λ(τ) + ν` for small `ε > 0`. -/
theorem assertion_4_le {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) :
    ∀ᶠ τ' in 𝓝[>] τ, indexUpTo hN γ hc τ' ≤ indexUpTo hN γ hc τ + conjMultiplicity hN γ hc 0 τ := by
  classical
  obtain ⟨B, hB, hlast⟩ := exists_isFine hc hτ
  have h₀ : τ ∈ validFor hN γ hc B := ⟨hB, hτ, hτ1.le⟩
  set m := (insert (0 : ℝ) B).max' (Finset.insert_nonempty _ _)
  have hmτ : m < τ := max_lt_of_isFine hc hτ hB
  -- Sylvester for `H_τ`
  obtain ⟨P, hPpos, hPdim⟩ := exists_isPosDefOn_add (Hform_isSymm hc B τ)
  rw [finrank_ker_Hform hc h₀] at hPdim
  have hsig : formIndex (Hform hN γ hc B τ) =
      (sigNeg (LinearMap.BilinMap.toQuadraticMap (Hform hN γ hc B τ)) : ℕ∞) :=
    formIndex_eq_sigNeg _
  rw [formIndex_Hform hc h₀] at hsig
  have hev := eventually_isPosDefOn_within h₀
    (fun x _ y _ => continuousWithinAt_Hform hc h₀ x y) hPpos
  set δ := min (τ + fineMesh hN γ hc / 2) 1
  have hτδ : τ < δ := lt_min (by linarith [fineMesh_pos hc]) hτ1
  have hvalid : ∀ τ' ∈ Ioo τ δ, τ' ∈ validFor hN γ hc B := fun τ' hτ' =>
    mem_validFor_of_near hc hτ hB hlast (hτ'.2.le.trans (min_le_right _ _))
      (hτ'.2.trans_le (min_le_left _ _)) (hmτ.trans hτ'.1)
  have hmem : validFor hN γ hc B ∈ 𝓝[>] τ := mem_of_superset (Ioo_mem_nhdsGT hτδ) hvalid
  filter_upwards [nhdsWithin_le_of_mem hmem hev, Ioo_mem_nhdsGT hτδ] with τ' hpos hτ'
  rw [← formIndex_Hform hc (hvalid τ' hτ'), hsig]
  refine formIndex_le fun S _ hneg => ?_
  have := finrank_add_finrank_le hneg hpos
  norm_cast
  omega

/-- The Hessian against a Jacobi field vanishing at `0` and `τ`, cut off at `τ`:
`E_**(J, Z) = 2⟨Z(τ), DJ/dt(τ)⟩` (Milnor p. 87). -/
theorem energyHessian_cut {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) {J : ℝ → V}
    (hJ : J ∈ conjSpace hN γ hc 0 τ) (hJT : (Icc 0 τ).indicator J ∈ pathTangent hN γ)
    (Y : pathTangent hN γ) :
    energyHessian hN hc.mem_pathSpace ⟨_, hJT⟩ Y =
      2 * ⟪(Y : ℝ → V) τ, covAlong hN γ J τ⟫ := by
  classical
  obtain ⟨hJs, hJ0, hJτ⟩ := (mem_conjSpace hc).1 hJ
  have hτ01 : τ ∈ Ioo (0 : ℝ) 1 := ⟨hτ, hτ1⟩
  set X := (Icc 0 τ).indicator J
  have hloc : ∀ t ∈ Ioo (0 : ℝ) 1, t ∉ ({τ} : Finset ℝ) →
      ∃ J', IsJacobiField hN γ J' ∧ X =ᶠ[𝓝 t] J' := by
    intro t ht htτ
    rw [Finset.mem_singleton] at htτ
    rcases lt_or_gt_of_ne htτ with h | h
    · exact ⟨J, hJs.1, eventually_of_mem (Ioo_mem_nhds ht.1 h) fun s hs =>
        indicator_of_mem (Ioo_subset_Icc_self hs) _⟩
    · exact ⟨0, isJacobiField_zero, eventually_of_mem (Ioi_mem_nhds h) fun s hs =>
        indicator_of_notMem (fun h' => absurd h'.2 (not_le.2 hs)) _⟩
  rw [energyHessian_eq_jumps hc.mem_pathSpace ⟨X, hJT⟩ Y hloc]
  rw [Finset.filter_singleton, if_pos hτ01, Finset.sum_singleton]
  -- the jump of the cut-off field at `τ` is `−J'(τ)`
  have hd : HasDerivAt J (deriv J τ) τ :=
    ((hJs.1.contDiffOn.contDiffAt (Icc_mem_nhds hτ hτ1)).differentiableAt (by simp)).hasDerivAt
  have hXτ : X τ = 0 := by
    change (Icc 0 τ).indicator J τ = 0
    rw [indicator_of_mem (show τ ∈ Icc 0 τ from ⟨hτ.le, le_rfl⟩), hJτ]
  have hR : derivWithin X (Ici τ) τ = 0 := by
    have : X =ᶠ[𝓝[Ici τ] τ] fun _ => (0 : V) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      rcases eq_or_lt_of_le (show τ ≤ s from hs) with h | h
      · rw [← h]; exact hXτ
      · exact indicator_of_notMem (fun h' => absurd h'.2 (not_le.2 h)) _
    rw [this.derivWithin_eq hXτ]
    simp
  have hL : derivWithin X (Iic τ) τ = deriv J τ := by
    refine (hd.hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_).derivWithin
      (uniqueDiffWithinAt_Iic τ)
    · filter_upwards [Icc_mem_nhdsLE hτ] with s hs using indicator_of_mem hs _
    · exact indicator_of_mem (show τ ∈ Icc 0 τ from ⟨hτ.le, le_rfl⟩) _
  have hcov : covAlong hN γ J τ = prj hN (γ τ) (deriv J τ) := by
    rw [covAlong, hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one τ
      (Ioo_subset_Icc_self hτ01))]
  change -2 * ⟪(Y : ℝ → V) τ, prj hN (γ τ) (jump X τ)⟫ = _
  rw [jump, hR, hL, zero_sub, map_neg, ← hcov, inner_neg_right]
  ring

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **The fields `X_k`** (Milnor p. 87): linearly independent tangent vectors `d_h` at `γ(τ)` have
a dual family of tangent vectors. -/
theorem exists_dual {ν : ℕ} {x₀ : V} (hx₀ : x₀ ∈ N) {d : Fin ν → V} (hd : LinearIndependent ℝ d)
    (hdT : ∀ h, prj hN x₀ (d h) = d h) :
    ∃ x : Fin ν → V, (∀ k, prj hN x₀ (x k) = x k) ∧
      ∀ h k, ⟪d h, x k⟫ = if h = k then 1 else 0 := by
  classical
  set U := Submodule.span ℝ (Set.range d)
  have hUT : U ≤ tanAt hN x₀ := Submodule.span_le.2 (by
    rintro _ ⟨h, rfl⟩
    exact (mem_tanAt hN hx₀).2 (hdT h))
  set φ : U →ₗ[ℝ] (Fin ν → ℝ) :=
    { toFun := fun u h => ⟪d h, (u : V)⟫
      map_add' := fun u u' => by ext h; simp [inner_add_right]
      map_smul' := fun c u => by ext h; simp [inner_smul_right] }
  have hinj : Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun u hu => ?_
    have hu' : ∀ h, ⟪d h, (u : V)⟫ = 0 := fun h => congrFun hu h
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 u.2
    have : ⟪(u : V), (u : V)⟫ = 0 := by
      nth_rewrite 1 [← hc]
      rw [sum_inner]
      exact Finset.sum_eq_zero fun h _ => by rw [inner_smul_left, hu' h, mul_zero]
    exact Subtype.ext (inner_self_eq_zero.1 this)
  have hsurj : Surjective φ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [finrank_span_eq_card hd, Fintype.card_fin, Module.finrank_fin_fun])).1 hinj
  choose u hu using fun k => hsurj (Pi.single k 1)
  refine ⟨fun k => u k, fun k => (mem_tanAt hN hx₀).1 (hUT (u k).2), fun h k => ?_⟩
  have := congrFun (hu k) h
  simp only [φ, LinearMap.coe_mk, AddHom.coe_mk] at this
  rw [this, Pi.single_apply]

/-- **Assertion (4), `≥`** (Milnor p. 87): `λ(τ') ≥ λ(τ) + ν(τ)` for every `τ' > τ`. -/
theorem assertion_4_ge {τ τ' : ℝ} (hτ : 0 < τ) (hττ' : τ < τ') (hτ'1 : τ' ≤ 1) :
    indexUpTo hN γ hc τ + conjMultiplicity hN γ hc 0 τ ≤ indexUpTo hN γ hc τ' := by
  classical
  have hτ1 : τ < 1 := hττ'.trans_le hτ'1
  have hτ01 : τ ∈ Icc (0 : ℝ) 1 := ⟨hτ.le, hτ1.le⟩
  set E := energyHessian hN hc.mem_pathSpace
  set F := fieldsUpTo hN γ τ'
  have hFF : fieldsUpTo hN γ τ ≤ F := fieldsUpTo_mono hττ'.le
  -- `λ(τ) = k`, realized by a negative definite subspace `S`
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (indexUpTo_lt_top hc hτ hτ1.le).ne
  obtain ⟨S, hSfin, hSneg, hSk⟩ := exists_isNegDefOn_of_formIndex_eq
    (B := (energyHessian hN hc.mem_pathSpace).restrict (fieldsUpTo hN γ τ)) hk.symm
  set ν := conjMultiplicity hN γ hc 0 τ
  let wb := Module.finBasisOfFinrankEq ℝ S hSk
  let Jb := Module.finBasisOfFinrankEq ℝ (conjSpace hN γ hc 0 τ) (rfl : finrank ℝ _ = ν)
  -- `J ↦ DJ/dt(τ)` is injective on the Jacobi fields vanishing at `0` and `τ`
  set L₂ : conjSpace hN γ hc 0 τ →ₗ[ℝ] V := (tanAt hN (γ τ)).subtype ∘ₗ
    (LinearMap.snd ℝ _ _ ∘ₗ ((jacEval hc hτ01) ∘ₗ Submodule.inclusion
      (conjSpace_le_jacobiSpace hc 0 τ)))
  have hL₂ : ∀ J : conjSpace hN γ hc 0 τ, L₂ J = covAlong hN γ (J : ℝ → V) τ := fun J => rfl
  have hL₂inj : Injective L₂ := by
    refine (injective_iff_map_eq_zero L₂).2 fun J hJ => ?_
    rw [hL₂] at hJ
    obtain ⟨hJs, -, hJτ⟩ := (mem_conjSpace hc).1 J.2
    exact Subtype.ext (jacobiSpace_eq_zero hc hJs (hJs.1.eqOn_zero hc hτ01 hJτ hJ))
  set d : Fin ν → V := fun h => covAlong hN γ (Jb h : ℝ → V) τ
  have hd : LinearIndependent ℝ d := by
    have := Jb.linearIndependent.map' L₂ (LinearMap.ker_eq_bot.2 hL₂inj)
    exact this
  have hdT : ∀ h, prj hN (γ τ) (d h) = d h := fun h => prj_prj hN _ _
  obtain ⟨x, hxT, hxd⟩ := exists_dual (hc.mem τ hτ01) hd hdT
  -- the bump function at `τ`
  set r := min τ (τ' - τ)
  have hr : 0 < r := lt_min hτ (sub_pos.2 hττ')
  set φ := bumpAt τ hr
  have hφτ : φ τ = 1 := φ.one_of_mem_closedBall (Metric.mem_closedBall_self (by
    change (0 : ℝ) ≤ r / 2; positivity))
  have hφout : ∀ t, t ∉ Ioo (τ - r) (τ + r) → φ t = 0 := fun t ht => by
    rw [← notMem_support, φ.support_eq, Real.ball_eq_Ioo]
    exact ht
  have hrτ : r ≤ τ := min_le_left _ _
  have hrτ' : r ≤ τ' - τ := min_le_right _ _
  -- the fields `X_k = φ P(x_k)`
  have hXmem : ∀ i, (fun t => φ t • prj hN (γ t) (x i)) ∈ pathTangent hN γ := fun i => by
    have hsm : ContDiffOn ℝ ∞ (fun t => φ t • prj hN (γ t) (x i)) (Icc 0 1) :=
      (φ.contDiff (n := ⊤)).contDiffOn.smul (hc.contDiffOn_prj.clm_apply contDiffOn_const)
    refine ⟨IsPiecewiseSmooth.of_contDiffOn hsm zero_le_one subset_rfl,
      fun t _ => by simp [prj_prj], ?_, ?_⟩
    · simp [hφout 0 fun h => by linarith [h.1]]
    · simp [hφout 1 fun h => by linarith [h.2]]
  set Xf : Fin ν → F := fun i => ⟨⟨_, hXmem i⟩, fun t ht => by
    change φ t • prj hN (γ t) (x i) = 0
    rw [hφout t fun h => ht ⟨by linarith [h.1], by linarith [h.2]⟩, zero_smul]⟩
  have hXfτ : ∀ i, (((Xf i : F) : pathTangent hN γ) : ℝ → V) τ = x i := fun i => by
    change φ τ • prj hN (γ τ) (x i) = x i
    rw [hφτ, one_smul, hxT i]
  -- the cut-off Jacobi fields
  have hJTmem : ∀ h, (Icc 0 τ).indicator (Jb h : ℝ → V) ∈ pathTangent hN γ := fun h =>
    indicator_mem_pathTangent ((mem_conjSpace hc).1 (Jb h).2).1.1 le_rfl hτ.le hτ1.le
      ((mem_conjSpace hc).1 (Jb h).2).2.1 ((mem_conjSpace hc).1 (Jb h).2).2.2
  set Jf : Fin ν → F := fun h => ⟨⟨_, hJTmem h⟩, fun t ht => indicator_of_notMem
    (fun h' => ht ⟨h'.1, h'.2.trans hττ'.le⟩) _⟩
  have hJfτ : ∀ h, (((Jf h : F) : pathTangent hN γ) : ℝ → V) τ = 0 := fun h => by
    change (Icc 0 τ).indicator (Jb h : ℝ → V) τ = 0
    rw [indicator_of_mem (show τ ∈ Icc 0 τ from ⟨hτ.le, le_rfl⟩)]
    exact ((mem_conjSpace hc).1 (Jb h).2).2.2
  have hEJ : ∀ h (Y : pathTangent hN γ), E ((Jf h : F) : pathTangent hN γ) Y =
      2 * ⟪(Y : ℝ → V) τ, d h⟫ := fun h Y =>
    energyHessian_cut hc hτ hτ1 (Jb h).2 (hJTmem h) Y
  -- the three linear maps
  set U : (Fin k → ℝ) →ₗ[ℝ] F := (Submodule.inclusion hFF) ∘ₗ (S.subtype ∘ₗ
    wb.equivFun.symm.toLinearMap)
  set Jm : (Fin ν → ℝ) →ₗ[ℝ] F := Fintype.linearCombination ℝ Jf
  set Xm : (Fin ν → ℝ) →ₗ[ℝ] F := Fintype.linearCombination ℝ Xf
  have hUτ : ∀ a, (((U a : F) : pathTangent hN γ) : ℝ → V) τ = 0 := fun a =>
    fieldsUpTo_apply_self hτ.le hτ1.le (wb.equivFun.symm a : S).1.2
  have hJmZ : ∀ b (Y : pathTangent hN γ), E ((Jm b : F) : pathTangent hN γ) Y =
      2 * ⟪(Y : ℝ → V) τ, ∑ h, b h • d h⟫ := fun b Y => by
    simp only [Jm, Fintype.linearCombination_apply, Submodule.coe_sum, Submodule.coe_smul,
      map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hEJ,
      inner_sum, inner_smul_right, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by ring
  have hJmτ : ∀ b, (((Jm b : F) : pathTangent hN γ) : ℝ → V) τ = 0 := fun b => by
    simp only [Jm, Fintype.linearCombination_apply, Submodule.coe_sum, Submodule.coe_smul,
      Finset.sum_apply, Pi.smul_apply, hJfτ, smul_zero, Finset.sum_const_zero]
  have hXmτ : ∀ b, (((Xm b : F) : pathTangent hN γ) : ℝ → V) τ = ∑ i, b i • x i := fun b => by
    simp only [Xm, Fintype.linearCombination_apply, Submodule.coe_sum, Submodule.coe_smul,
      Finset.sum_apply, Pi.smul_apply, hXfτ]
  have key := le_formIndex_of_compound (E := E.restrict F)
    (LinearMap.BilinForm.isSymm_def.2 fun X Y =>
      LinearMap.BilinForm.isSymm_def.1 (energyHessian_isSymm hN hc.mem_pathSpace) X Y)
    U Jm Xm (fun a ha => ?_) (fun b a => ?_) (fun b b' => ?_) (fun b b' => ?_)
  · have hk' : indexUpTo hN γ hc τ' = formIndex (E.restrict F) := rfl
    rw [hk', ← hk]
    exact_mod_cast key
  · -- `E` is negative definite on `S`
    have ha' : (wb.equivFun.symm a : S) ≠ 0 := fun h => ha (wb.equivFun.symm.injective
      (h.trans (map_zero _).symm))
    exact hSneg _ (wb.equivFun.symm a).2 fun h => ha' (Subtype.ext h)
  · change E ((Jm b : F) : pathTangent hN γ) ((U a : F) : pathTangent hN γ) = 0
    rw [hJmZ, hUτ, inner_zero_left, mul_zero]
  · change E ((Jm b : F) : pathTangent hN γ) ((Jm b' : F) : pathTangent hN γ) = 0
    rw [hJmZ, hJmτ, inner_zero_left, mul_zero]
  · change E ((Jm b : F) : pathTangent hN γ) ((Xm b' : F) : pathTangent hN γ) = _
    rw [hJmZ, hXmτ, sum_inner]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left, inner_sum]
    simp only [inner_smul_right, RCLike.conj_to_real]
    rw [Finset.sum_eq_single i (fun h _ hhi => by
      rw [real_inner_comm, hxd h i, if_neg hhi, mul_zero]) (by simp)]
    rw [real_inner_comm, hxd i i, if_pos rfl]
    ring

/-- **Assertion (4)** (Milnor p. 86): `λ(τ + ε) = λ(τ) + ν(τ)` for all sufficiently small
`ε > 0`; `λ` jumps by `ν` when `t` passes a conjugate point of multiplicity `ν`. -/
theorem assertion_4 {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) :
    ∀ᶠ τ' in 𝓝[>] τ, indexUpTo hN γ hc τ' = indexUpTo hN γ hc τ + conjMultiplicity hN γ hc 0 τ := by
  filter_upwards [assertion_4_le hc hτ hτ1, Ioo_mem_nhdsGT hτ1] with τ' hle hτ'
  exact le_antisymm hle (assertion_4_ge hc hτ hτ'.1 hτ'.2.le)

end Morse
