import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
Milnor, *Morse Theory*, §15, pp. 83–87: the linear algebra behind the index theorem (Lemmas 15.A
and 15.B of the exposition).

# The index of a bilinear form on an infinite dimensional space

Milnor defines the index of the Hessian `E_** : TΩ_γ × TΩ_γ → ℝ` (p. 83) as "the maximum
dimension of a subspace of `TΩ_γ` on which `E_**` is negative definite"; `TΩ_γ` is infinite
dimensional, and that this maximum exists (is finite) is part of Theorem 15.1.  Mathlib's
`QuadraticForm.sigNeg` is only meaningful on finite dimensional spaces (it is `0` otherwise).

* `Morse.formIndex B : ℕ∞`: the supremum of the dimensions of the finite dimensional subspaces
  on which `B` is negative definite (`⊤` if there are arbitrarily large ones).  On a finite
  dimensional space it is `sigNeg` (`Morse.formIndex_eq_sigNeg`).
* `Morse.formIndex_le_of_map`: a linear map preserving the forms does not decrease the index (it
  is automatically injective on negative definite subspaces).
* **Lemma 15.B of the exposition** (Milnor's "the proof is straightforward" for Lemma 15.4):
  `Morse.formIndex_eq_restrict_of_isCompl` and `Morse.ker_eq_map_ker_restrict`: if `X = A ⊕ C`
  with `A ⊥_B C` and `B` positive definite on `C`, then `B` and `B|_A` have the same index and
  the same null space.
* **Sylvester's law of inertia** in the form used on p. 86 (`Morse.exists_isPosDefOn_add`): a
  symmetric form on an `m`-dimensional space is positive definite on a subspace of dimension
  `m − index − nullity`; and **Lemma 15.A (1)** (`Morse.finrank_add_finrank_le`): a negative
  definite and a positive definite subspace meet only in `0`.
* **Lemma 15.A (3)** (Milnor p. 86, "for all `τ'` sufficiently close to `τ` it follows that
  `H_τ'` is negative definite on `𝒱`", and p. 87, "this compound matrix is certainly negative
  definite"): `Morse.eventually_isNegDefOn`, `Morse.eventually_isPosDefOn`: definiteness on a
  finite dimensional subspace persists under continuous perturbation (compactness of the unit
  sphere).
-/

open Set Filter Topology Module

noncomputable section

namespace Morse

section Index

variable {M : Type*} [AddCommGroup M] [Module ℝ M]
  {M' : Type*} [AddCommGroup M'] [Module ℝ M']

/-- `B` is **negative definite** on the subspace `S`. -/
def IsNegDefOn (B : LinearMap.BilinForm ℝ M) (S : Submodule ℝ M) : Prop :=
  ∀ x ∈ S, x ≠ 0 → B x x < 0

/-- `B` is **positive definite** on the subspace `S`. -/
def IsPosDefOn (B : LinearMap.BilinForm ℝ M) (S : Submodule ℝ M) : Prop :=
  ∀ x ∈ S, x ≠ 0 → 0 < B x x

/-- **The index** of a bilinear form (Milnor pp. 5, 83): the supremum, in `ℕ∞`, of the dimensions
of the finite dimensional subspaces on which `B` is negative definite. -/
def formIndex (B : LinearMap.BilinForm ℝ M) : ℕ∞ :=
  ⨆ (S : Submodule ℝ M) (_ : FiniteDimensional ℝ S) (_ : IsNegDefOn B S), (finrank ℝ S : ℕ∞)

theorem le_formIndex {B : LinearMap.BilinForm ℝ M} {S : Submodule ℝ M} [hS : FiniteDimensional ℝ S]
    (hneg : IsNegDefOn B S) : (finrank ℝ S : ℕ∞) ≤ formIndex B :=
  le_iSup₂_of_le (f := fun (S : Submodule ℝ M) (_ : FiniteDimensional ℝ S) =>
    ⨆ (_ : IsNegDefOn B S), (finrank ℝ S : ℕ∞)) S hS (le_iSup_of_le hneg le_rfl)

theorem formIndex_le {B : LinearMap.BilinForm ℝ M} {k : ℕ∞}
    (h : ∀ S : Submodule ℝ M, FiniteDimensional ℝ S → IsNegDefOn B S → (finrank ℝ S : ℕ∞) ≤ k) :
    formIndex B ≤ k :=
  iSup₂_le fun S hS => iSup_le fun hneg => h S hS hneg

/-- The dimension of the image of a subspace under a map injective on it. -/
theorem finrank_map_of_injOn (L : M →ₗ[ℝ] M') (S : Submodule ℝ M)
    (hinj : ∀ x ∈ S, L x = 0 → x = 0) : finrank ℝ (S.map L) = finrank ℝ S := by
  have hker : LinearMap.ker (L.domRestrict S) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hx
    exact (Submodule.mem_bot ℝ).2 (Subtype.ext (hinj x x.2 hx))
  rw [← LinearMap.range_domRestrict]
  exact LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.1 hker)

/-- **A linear map preserving the forms does not decrease the index.**  (It is injective on every
negative definite subspace: a vector mapped to `0` has `B(x, x) = B'(0, 0) = 0`.) -/
theorem formIndex_le_of_map {B : LinearMap.BilinForm ℝ M} {B' : LinearMap.BilinForm ℝ M'}
    (L : M →ₗ[ℝ] M') (hL : ∀ x y, B' (L x) (L y) = B x y) : formIndex B ≤ formIndex B' := by
  refine formIndex_le fun S hS hneg => ?_
  have hinj : ∀ x ∈ S, L x = 0 → x = 0 := fun x hx h0 => by
    by_contra hx0
    have := hneg x hx hx0
    rw [← hL, h0] at this
    simp at this
  have hneg' : IsNegDefOn B' (S.map L) := by
    rintro _ ⟨x, hx, rfl⟩ hx0
    rw [hL]
    exact hneg x hx fun h => hx0 (by rw [h, map_zero])
  have := le_formIndex hneg'
  rwa [finrank_map_of_injOn L S hinj] at this

/-- The index of the restriction to a subspace is at most the index. -/
theorem formIndex_restrict_le (B : LinearMap.BilinForm ℝ M) (A : Submodule ℝ M) :
    formIndex (LinearMap.BilinForm.restrict B A) ≤ formIndex B :=
  formIndex_le_of_map A.subtype fun _ _ => rfl

/-- The index is unchanged by a positive factor. -/
theorem formIndex_smul {c : ℝ} (hc : 0 < c) (B : LinearMap.BilinForm ℝ M) :
    formIndex (c • B) = formIndex B := by
  have h : ∀ S : Submodule ℝ M, IsNegDefOn (c • B) S ↔ IsNegDefOn B S := fun S => by
    simp only [IsNegDefOn, LinearMap.smul_apply, smul_eq_mul]
    exact forall₂_congr fun x _ => imp_congr_right fun _ =>
      ⟨fun h => by nlinarith, fun h => mul_neg_of_pos_of_neg hc h⟩
  simp only [formIndex, h]

/-- **Lemma 15.B of the exposition, the index**: if `X = A ⊕ C`, `A` and `C` are perpendicular for
`B`, and `B` is positive definite on `C`, then `B` and `B|_A` have the same index. -/
theorem formIndex_eq_restrict_of_isCompl {B : LinearMap.BilinForm ℝ M} {A C : Submodule ℝ M}
    (hAC : IsCompl A C) (horth : ∀ a ∈ A, ∀ c ∈ C, B a c = 0)
    (horth' : ∀ a ∈ A, ∀ c ∈ C, B c a = 0) (hpos : IsPosDefOn B C) :
    formIndex B = formIndex (LinearMap.BilinForm.restrict B A) := by
  refine le_antisymm (formIndex_le fun S hS hneg => ?_) (formIndex_restrict_le B A)
  set π := A.projectionOnto C hAC
  have hc : ∀ x, x - (π x : M) ∈ C := fun x => by
    rw [← Submodule.projectionOnto_apply_eq_zero_iff hAC, map_sub,
      Submodule.projectionOnto_apply_left, sub_self]
  have hBc : ∀ x, 0 ≤ B (x - (π x : M)) (x - (π x : M)) := fun x => by
    by_cases h0 : x - (π x : M) = 0
    · rw [h0]; simp
    · exact (hpos _ (hc x) h0).le
  -- `B(x, x) = B(πx, πx) + B(c, c)`
  have hsplit : ∀ x, B x x = B (π x : M) (π x : M) + B (x - (π x : M)) (x - (π x : M)) := by
    intro x
    have h1 := horth _ (π x).2 _ (hc x)
    have h2 := horth' _ (π x).2 _ (hc x)
    have hx : x = (π x : M) + (x - (π x : M)) := by abel
    conv_lhs => rw [hx]
    simp only [map_add, LinearMap.add_apply, h1, h2]
    ring
  have hinj : ∀ x ∈ S, π x = 0 → x = 0 := fun x hx h0 => by
    by_contra hx0
    have h1 := hneg x hx hx0
    have h2 := hBc x
    rw [h0, Submodule.coe_zero, sub_zero] at h2
    exact absurd h1 (not_lt.2 h2)
  have hneg' : IsNegDefOn (LinearMap.BilinForm.restrict B A) (S.map π) := by
    rintro _ ⟨x, hx, rfl⟩ hx0
    have hx0' : x ≠ 0 := fun h => hx0 (by rw [h, map_zero])
    have h1 := hneg x hx hx0'
    rw [hsplit x] at h1
    change B (π x : M) (π x : M) < 0
    linarith [hBc x]
  have := le_formIndex hneg'
  rwa [finrank_map_of_injOn π S hinj] at this

/-- **Lemma 15.B of the exposition, the null space**: under the same hypotheses the null space of
`B` is the null space of `B|_A`. -/
theorem ker_eq_map_ker_restrict {B : LinearMap.BilinForm ℝ M} {A C : Submodule ℝ M}
    (hAC : IsCompl A C) (horth : ∀ a ∈ A, ∀ c ∈ C, B a c = 0) (hpos : IsPosDefOn B C) :
    LinearMap.ker B = (LinearMap.ker (LinearMap.BilinForm.restrict B A)).map A.subtype := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker] at hx
    obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 (hAC.sup_eq_top ▸ Submodule.mem_top :
      x ∈ A ⊔ C)
    have hcc : B c c = 0 := by
      have := congrArg (fun f => f c) hx
      simp only [LinearMap.zero_apply, map_add, LinearMap.add_apply, horth a ha c hc,
        zero_add] at this
      exact this
    have hc0 : c = 0 := by
      by_contra h
      exact (hpos c hc h).ne' hcc
    subst hc0
    refine ⟨⟨a, ha⟩, ?_, by simp⟩
    change _ ∈ LinearMap.ker _
    rw [LinearMap.mem_ker]
    ext a'
    simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
      LinearMap.zero_apply]
    have := congrArg (fun f => f (a' : M)) hx
    simpa using this
  · rintro ⟨a, ha, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker] at ha
    rw [LinearMap.mem_ker]
    ext y
    obtain ⟨a', ha', c', hc', rfl⟩ := Submodule.mem_sup.1 (hAC.sup_eq_top ▸ Submodule.mem_top :
      y ∈ A ⊔ C)
    have h1 := congrArg (fun f => f ⟨a', ha'⟩) ha
    simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
      LinearMap.zero_apply] at h1
    simp only [Submodule.subtype_apply, map_add, LinearMap.zero_apply, h1,
      horth _ a.2 c' hc', add_zero]

/-- A finite index is attained. -/
theorem exists_isNegDefOn_of_formIndex_eq {B : LinearMap.BilinForm ℝ M} {k : ℕ}
    (h : formIndex B = k) :
    ∃ S : Submodule ℝ M, FiniteDimensional ℝ S ∧ IsNegDefOn B S ∧ finrank ℝ S = k := by
  by_contra hne
  push Not at hne
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact hne ⊥ inferInstance (fun x hx hx0 => absurd ((Submodule.mem_bot ℝ).1 hx) hx0)
      (by simp)
  have hle : formIndex B ≤ ((k - 1 : ℕ) : ℕ∞) := by
    refine formIndex_le fun S hS hneg => ?_
    have h1 := le_formIndex (hS := hS) hneg
    rw [h] at h1
    have h2 : finrank ℝ S ≤ k := by exact_mod_cast h1
    have h3 := hne S hS hneg
    exact_mod_cast (show finrank ℝ S ≤ k - 1 by omega)
  rw [h] at hle
  have : k ≤ k - 1 := by exact_mod_cast hle
  omega

/-- The index is invariant under a linear isomorphism carrying one form to the other. -/
theorem formIndex_eq_of_equiv {B : LinearMap.BilinForm ℝ M} {B' : LinearMap.BilinForm ℝ M'}
    (L : M ≃ₗ[ℝ] M') (hL : ∀ x y, B' (L x) (L y) = B x y) : formIndex B = formIndex B' := by
  refine le_antisymm (formIndex_le_of_map (L : M →ₗ[ℝ] M') hL)
    (formIndex_le_of_map (L.symm : M' →ₗ[ℝ] M) fun x y => ?_)
  rw [← hL]
  simp

/-! ### Finite dimensional spaces: Sylvester's law of inertia -/

theorem isNegDefOn_iff_posDef (B : LinearMap.BilinForm ℝ M) (S : Submodule ℝ M) :
    IsNegDefOn B S ↔ ((-LinearMap.BilinMap.toQuadraticMap B).restrict S).PosDef := by
  constructor
  · rintro h ⟨x, hx⟩ hx0
    have hx0' : x ≠ 0 := fun h' => hx0 (Subtype.ext h')
    simpa using h x hx hx0'
  · intro h x hx hx0
    have := h ⟨x, hx⟩ (fun h' => hx0 (congrArg Subtype.val h'))
    simpa using this

theorem isPosDefOn_iff_posDef (B : LinearMap.BilinForm ℝ M) (S : Submodule ℝ M) :
    IsPosDefOn B S ↔ ((LinearMap.BilinMap.toQuadraticMap B).restrict S).PosDef := by
  constructor
  · rintro h ⟨x, hx⟩ hx0
    have hx0' : x ≠ 0 := fun h' => hx0 (Subtype.ext h')
    simpa using h x hx hx0'
  · intro h x hx hx0
    have := h ⟨x, hx⟩ (fun h' => hx0 (congrArg Subtype.val h'))
    simpa using this

/-- On a finite dimensional space the index is Mathlib's `sigNeg` of the quadratic form
`x ↦ B(x, x)`. -/
theorem formIndex_eq_sigNeg [FiniteDimensional ℝ M] (B : LinearMap.BilinForm ℝ M) :
    formIndex B = (sigNeg (LinearMap.BilinMap.toQuadraticMap B) : ℕ∞) := by
  have key := sigNeg_isGreatest (LinearMap.BilinMap.toQuadraticMap B)
  refine le_antisymm (formIndex_le fun S _ hneg => ?_) ?_
  · exact_mod_cast key.2 ⟨S, rfl, (isNegDefOn_iff_posDef B S).1 hneg⟩
  · obtain ⟨S, hS, hpos⟩ := key.1
    rw [← hS]
    exact le_formIndex ((isNegDefOn_iff_posDef B S).2 hpos)

/-- The radical of the quadratic form of a symmetric bilinear form is its null space. -/
theorem radical_toQuadraticMap {B : LinearMap.BilinForm ℝ M} (hB : B.IsSymm) :
    (LinearMap.BilinMap.toQuadraticMap B).radical = LinearMap.ker B := by
  ext x
  rw [QuadraticMap.radical, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_ofPred_eq, LinearMap.mem_ker]
  constructor
  · rintro ⟨-, h⟩
    ext y
    have := congrArg (fun f => f y) h
    simp only [QuadraticMap.polarBilin_apply_apply, LinearMap.zero_apply] at this
    rw [LinearMap.BilinMap.polar_toQuadraticMap] at this
    have h3 : B x y = B y x := LinearMap.BilinForm.isSymm_def.1 hB x y
    simp only [LinearMap.zero_apply]
    linarith
  · intro h
    refine ⟨by simp [h], ?_⟩
    ext y
    simp only [QuadraticMap.polarBilin_apply_apply, LinearMap.zero_apply,
      LinearMap.BilinMap.polar_toQuadraticMap, h, LinearMap.zero_apply, zero_add]
    rw [LinearMap.BilinForm.isSymm_def.1 hB y x, h, LinearMap.zero_apply]

/-- **Sylvester's law of inertia** in the form used on p. 86: a symmetric bilinear form on an
`m`-dimensional space is positive definite on a subspace of dimension
`m − index − nullity`. -/
theorem exists_isPosDefOn_add [FiniteDimensional ℝ M] {B : LinearMap.BilinForm ℝ M}
    (hB : B.IsSymm) :
    ∃ P : Submodule ℝ M, IsPosDefOn B P ∧
      finrank ℝ P + sigNeg (LinearMap.BilinMap.toQuadraticMap B) + finrank ℝ (LinearMap.ker B) =
        finrank ℝ M := by
  obtain ⟨P, hP, hpos⟩ := exists_finrank_eq_sigPos_and_posDef (LinearMap.BilinMap.toQuadraticMap B)
  refine ⟨P, (isPosDefOn_iff_posDef B P).2 hpos, ?_⟩
  rw [hP, ← radical_toQuadraticMap hB]
  exact QuadraticForm.sigPos_add_sigNeg_add_radical

/-- **Lemma 15.A (1)**: a negative definite and a positive definite subspace of a finite
dimensional space meet only in `0`, so their dimensions add up to at most the dimension. -/
theorem finrank_add_finrank_le [FiniteDimensional ℝ M] {B : LinearMap.BilinForm ℝ M}
    {S P : Submodule ℝ M} (hS : IsNegDefOn B S) (hP : IsPosDefOn B P) :
    finrank ℝ S + finrank ℝ P ≤ finrank ℝ M := by
  refine Submodule.finrank_add_finrank_le_of_disjoint ?_
  rw [Submodule.disjoint_def]
  intro x hxS hxP
  by_contra hx0
  exact lt_asymm (hS x hxS hx0) (hP x hxP hx0)

end Index

/-! ### Lemma 15.A (3): definiteness persists under continuous perturbation -/

section Perturb

variable {M : Type*} [AddCommGroup M] [Module ℝ M] {X : Type*} [TopologicalSpace X]

/-- **Lemma 15.A (3)**: if `τ ↦ H τ` is a family of bilinear forms whose values `H τ (x, y)` on
a finite dimensional subspace `S` are continuous at `τ₀`, and `H τ₀` is negative definite on `S`,
then so is `H τ` for all `τ` close to `τ₀`. -/
theorem eventually_isNegDefOn {τ₀ : X} {H : X → LinearMap.BilinForm ℝ M} {S : Submodule ℝ M}
    [FiniteDimensional ℝ S] (hH : ∀ x ∈ S, ∀ y ∈ S, ContinuousAt (fun τ => H τ x y) τ₀)
    (h₀ : IsNegDefOn (H τ₀) S) : ∀ᶠ τ in 𝓝 τ₀, IsNegDefOn (H τ) S := by
  set d := finrank ℝ S
  set b := Module.finBasis ℝ S
  set v : (Fin d → ℝ) → M := fun c => ∑ i, c i • (b i : M) with hv
  have hvS : ∀ c, v c ∈ S := fun c =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2
  have hvsmul : ∀ (r : ℝ) c, v (r • c) = r • v c := fun r c => by
    simp only [hv, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]
  have hv0 : ∀ c, v c = 0 → c = 0 := fun c h => by
    have h' : ∑ i, c i • b i = 0 := by
      apply Subtype.ext
      simpa [hv] using h
    exact funext fun i => (Fintype.linearIndependent_iff.1 b.linearIndependent) c h' i
  have hexp : ∀ τ c, H τ (v c) (v c) = ∑ i, ∑ j, c i * c j * H τ (b i) (b j) := fun τ c => by
    simp only [hv, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  set f : X × (Fin d → ℝ) → ℝ := fun z => H z.1 (v z.2) (v z.2)
  have hfc : ∀ c, ContinuousAt f (τ₀, c) := fun c => by
    have : f = fun z => ∑ i, ∑ j, z.2 i * z.2 j * H z.1 (b i) (b j) := funext fun z => hexp _ _
    rw [this]
    refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
    exact ((((continuous_apply i).comp continuous_snd).continuousAt.mul
      ((continuous_apply j).comp continuous_snd).continuousAt).mul
      (ContinuousAt.comp (x := ((τ₀, c) : X × (Fin d → ℝ))) (hH _ (b i).2 _ (b j).2)
        continuousAt_fst) : ContinuousAt _ _)
  have hK : IsCompact (Metric.sphere (0 : Fin d → ℝ) 1) := isCompact_sphere _ _
  have hev := hK.eventually_forall_of_forall_eventually (x₀ := τ₀)
    (P := fun τ c => f (τ, c) < 0) fun c hc => by
      have hc0 : c ≠ 0 := by
        intro h
        rw [h, mem_sphere_zero_iff_norm, norm_zero] at hc
        exact zero_ne_one hc
      exact (hfc c).eventually (gt_mem_nhds (h₀ _ (hvS c) fun h => hc0 (hv0 c h)))
  filter_upwards [hev] with τ hτ x hx hx0
  set c : Fin d → ℝ := fun i => b.repr ⟨x, hx⟩ i
  have hxc : v c = x := by
    have h2 := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    rw [Submodule.coe_sum] at h2
    rw [hv]
    exact h2
  have hc0 : c ≠ 0 := fun h => hx0 (by rw [← hxc, h]; simp [hv])
  have hnc : 0 < ‖c‖ := norm_pos_iff.2 hc0
  have hmem : ‖c‖⁻¹ • c ∈ Metric.sphere (0 : Fin d → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnc.ne']
  have h1 := hτ _ hmem
  simp only [f, hvsmul, map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
  rw [← hxc]
  have h2 : 0 < ‖c‖⁻¹ * ‖c‖⁻¹ := by positivity
  nlinarith

/-- **Lemma 15.A (3)**, positive definite version. -/
theorem eventually_isPosDefOn {τ₀ : X} {H : X → LinearMap.BilinForm ℝ M} {S : Submodule ℝ M}
    [FiniteDimensional ℝ S] (hH : ∀ x ∈ S, ∀ y ∈ S, ContinuousAt (fun τ => H τ x y) τ₀)
    (h₀ : IsPosDefOn (H τ₀) S) : ∀ᶠ τ in 𝓝 τ₀, IsPosDefOn (H τ) S := by
  have h := eventually_isNegDefOn (H := fun τ => -H τ) (τ₀ := τ₀) (S := S)
    (fun x hx y hy => (hH x hx y hy).neg) fun x hx hx0 => by
      simpa using h₀ x hx hx0
  filter_upwards [h] with τ hτ x hx hx0
  simpa using hτ x hx hx0

end Perturb

end Morse
