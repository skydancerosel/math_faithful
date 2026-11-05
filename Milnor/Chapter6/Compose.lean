import Milnor.Chapter6.LevelMap

/-!
# Degrees of compositions with bijections of constant sign
-/

open Set Module Filter Topology Function
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {G'' : Type*} [TopologicalSpace G''] {K : ModelWithCorners ℝ F' G''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace G'' P] [IsManifold K ∞ P] {n : ℕ}

/-- **Postcomposition with a bijection of constant sign `σ = ±1`** multiplies the degree by
`σ` (evaluated at the corresponding point). -/
theorem degAt_comp_bij_left (hE : finrank ℝ E = n) (hF : finrank ℝ F = n) (oM : Orient I M n)
    (oN : Orient J N n) (oP : Orient K P n) {h : N → P} (hhb : Bijective h)
    (hhd : ∀ y, MDifferentiableAt J K h y) {σ : ℤ} (hσ1 : σ = 1 ∨ σ = -1)
    (hσ : ∀ y, signAt oN oP h y = σ) {f : M → N} (hfd : ∀ x, MDifferentiableAt I J f x)
    {y : N} {z : P} (hy : h y = z) :
    degAt oM oP (fun x => h (f x)) z = σ * degAt oM oN f y := by
  unfold degAt
  have hpre : (fun x => h (f x)) ⁻¹' {z} = f ⁻¹' {y} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff]
    constructor
    · intro hx; exact hhb.1 (hx.trans hy.symm)
    · intro hx; rw [hx, hy]
  rw [hpre]
  have hpt : ∀ x, signAt oM oP (fun x => h (f x)) x = σ * signAt oM oN f x := fun x => by
    rw [signAt_comp' hE hF oM oN oP (hfd x) (hhd (f x)), hσ]
  rcases hσ1 with rfl | rfl
  · simp only [hpt, one_mul]
  · simp only [hpt, neg_one_mul]
    simp_rw [finsum_neg_distrib]

/-- Precomposition with a bijection of constant sign `σ = ±1`. -/
theorem degAt_comp_bij' (hE : finrank ℝ E = n) (hF : finrank ℝ F = n) (oM : Orient I M n)
    (oN : Orient J N n) (oP : Orient K P n) {f : N → P} (hf : ∀ y, MDifferentiableAt J K f y)
    {φ : M → N} (hφb : Bijective φ) (hφd : ∀ x, MDifferentiableAt I J φ x) {σ : ℤ}
    (hσ1 : σ = 1 ∨ σ = -1) (hφ : ∀ x, signAt oM oN φ x = σ) (z : P) :
    degAt oM oP (fun x => f (φ x)) z = σ * degAt oN oP f z := by
  unfold degAt
  have hbij : BijOn φ ((fun x => f (φ x)) ⁻¹' {z}) (f ⁻¹' {z}) := by
    refine ⟨fun x hx => hx, hφb.1.injOn, fun y hy => ?_⟩
    obtain ⟨x, rfl⟩ := hφb.2 y
    exact ⟨x, hy, rfl⟩
  have hpt : ∀ x, signAt oM oP (fun x => f (φ x)) x = σ * signAt oN oP f (φ x) := fun x => by
    rw [signAt_comp' hE hF oM oN oP (hφd x) (hf (φ x)), hφ x, mul_comm]
  rw [finsum_mem_eq_of_bijOn φ (g := fun y => σ * signAt oN oP f y) hbij fun x _ => hpt x]
  rcases hσ1 with rfl | rfl
  · simp only [one_mul]
  · simp only [neg_one_mul]
    simp_rw [finsum_neg_distrib]

end Milnor
