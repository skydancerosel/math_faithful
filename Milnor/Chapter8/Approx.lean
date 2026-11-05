import Milnor.Chapter8.NearMaps
import Milnor.Chapter2.Brouwer

/-!
# Smooth approximation on compact sets (toward Problem 4)

* **Stone–Weierstrass for smooth maps.** A map `G : E → F` between finite-dimensional real normed
  spaces which is continuous on a compact set `S` is, on `S`, a uniform limit of smooth maps
  `E → F`.  This generalizes the approximation on the closed unit ball used for Brouwer's theorem
  (`Milnor.exists_contDiff_approx`): the restrictions to `S` of smooth real functions form a
  subalgebra of `C(S, ℝ)` which separates points (continuous linear functionals do), and one
  approximates the coordinates of `G` in a basis of `F`.
* **Normalizing a nearby vector.** For a unit vector `a` and `q ≠ 0`,
  `‖q / ‖q‖ - a‖ ≤ 2 ‖q - a‖`.
* A smooth homotopy between maps into `Sᵖ` restricts to a continuous homotopy.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

open Sphere

namespace Problems

/-! ### Stone–Weierstrass for smooth maps on a compact set -/

section Approx

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable (E) in
/-- The functions on a set `S ⊆ E` which extend to smooth functions on `E`, as a subalgebra of the
continuous functions on `S`. -/
def smoothSubalgebraOn (S : Set E) : Subalgebra ℝ C(S, ℝ) where
  carrier := {g | ∃ P : E → ℝ, ContDiff ℝ ∞ P ∧ ∀ x : S, g x = P x}
  mul_mem' := by
    rintro g₁ g₂ ⟨P₁, hP₁, h₁⟩ ⟨P₂, hP₂, h₂⟩
    exact ⟨fun x => P₁ x * P₂ x, hP₁.mul hP₂, fun x => by simp [h₁ x, h₂ x]⟩
  add_mem' := by
    rintro g₁ g₂ ⟨P₁, hP₁, h₁⟩ ⟨P₂, hP₂, h₂⟩
    exact ⟨fun x => P₁ x + P₂ x, hP₁.add hP₂, fun x => by simp [h₁ x, h₂ x]⟩
  algebraMap_mem' r := ⟨fun _ => r, contDiff_const, fun x => by simp⟩

/-- Continuous linear functionals separate the points of `S`. -/
theorem smoothSubalgebraOn_separatesPoints (S : Set E) :
    (smoothSubalgebraOn E S).SeparatesPoints := by
  intro x y hxy
  have hne : (x : E) ≠ y := fun h => hxy (Subtype.ext h)
  obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_separating_of_ne (R := ℝ) hne
  have hcont : Continuous fun z : S => ℓ (z : E) := ℓ.continuous.comp continuous_subtype_val
  exact ⟨_, ⟨⟨fun z => ℓ (z : E), hcont⟩, ⟨fun z => ℓ z, ℓ.contDiff, fun _ => rfl⟩, rfl⟩, hℓ⟩

/-- **Stone–Weierstrass**: continuous maps on a compact subset of a finite-dimensional space are
uniform limits of smooth maps. -/
theorem exists_contDiff_approx_of_isCompact {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {S : Set E} (hS : IsCompact S) {G : E → F} (hG : ContinuousOn G S)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : E → F, ContDiff ℝ ∞ Q ∧ ∀ x ∈ S, ‖Q x - G x‖ < ε := by
  classical
  have : CompactSpace S := isCompact_iff_compactSpace.1 hS
  obtain ⟨b⟩ : Nonempty (Basis (Fin (finrank ℝ F)) ℝ F) := ⟨Module.finBasis ℝ F⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ∑ i, ‖b i‖ + 1 := ⟨_, rfl⟩
  have hsum : 0 ≤ ∑ i, ‖b i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hCpos : 0 < C := by rw [hC]; linarith
  obtain ⟨ε', hε'⟩ : ∃ ε' : ℝ, ε' = ε / C := ⟨_, rfl⟩
  have hε'pos : 0 < ε' := by rw [hε']; exact div_pos hε hCpos
  have hcoord : ∀ i, ∃ P : E → ℝ, ContDiff ℝ ∞ P ∧
      ∀ x : S, ‖P x - b.repr (G x) i‖ < ε' := by
    intro i
    have hℓ : Continuous fun v : F => b.repr v i := (b.coord i).continuous_of_finiteDimensional
    have hc : Continuous fun x : S => b.repr (G x.1) i :=
      hℓ.comp (hG.comp_continuous continuous_subtype_val fun x => x.2)
    obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints _
      (smoothSubalgebraOn_separatesPoints S) _ hc ε' hε'pos
    obtain ⟨P, hP, hgP⟩ := g.2
    exact ⟨P, hP, fun x => by rw [← hgP x]; exact hg x⟩
  choose P hP hPG using hcoord
  refine ⟨fun x => ∑ i, P i x • b i, ContDiff.sum fun i _ => (hP i).smul contDiff_const, ?_⟩
  intro x hx
  have hrepr : G x = ∑ i, b.repr (G x) i • b i := (b.sum_repr (G x)).symm
  rw [hrepr, ← Finset.sum_sub_distrib]
  simp_rw [← sub_smul]
  calc ‖∑ i, (P i x - b.repr (G x) i) • b i‖
        ≤ ∑ i, ‖(P i x - b.repr (G x) i) • b i‖ := norm_sum_le _ _
    _ = ∑ i, ‖P i x - b.repr (G x) i‖ * ‖b i‖ := by simp only [norm_smul]
    _ ≤ ∑ i, ε' * ‖b i‖ := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (hPG i ⟨x, hx⟩).le (norm_nonneg _)
    _ = ε' * (C - 1) := by rw [← Finset.mul_sum, hC, add_sub_cancel_right]
    _ < ε' * C := by nlinarith
    _ = ε := by rw [hε']; field_simp

end Approx

/-! ### Normalizing a nearby vector -/

/-- Normalizing a nearby vector: `‖nv0 q - a‖ ≤ 2 ‖q - a‖` for a unit vector `a`. -/
theorem norm_nv0_sub_le {p : ℕ} (a : Sph p) (q : EuclideanSpace ℝ (Fin (p + 1))) (hq : q ≠ 0) :
    ‖(nv0 q).1 - a.1‖ ≤ 2 * ‖q - a.1‖ := by
  rw [nv0_val hq]
  change ‖‖q‖⁻¹ • q - a.1‖ ≤ 2 * ‖q - a.1‖
  have hq0 : 0 < ‖q‖ := norm_pos_iff.2 hq
  have h1 : ‖‖q‖⁻¹ • q - q‖ = |1 - ‖q‖| := by
    have : ‖q‖⁻¹ • q - q = (‖q‖⁻¹ - 1) • q := by rw [sub_smul, one_smul]
    have h3 : (‖q‖⁻¹ - 1) * ‖q‖ = 1 - ‖q‖ := by
      rw [sub_mul, inv_mul_cancel₀ hq0.ne', one_mul]
    rw [this, norm_smul, Real.norm_eq_abs, ← h3, abs_mul, abs_of_pos hq0]
  have h2 : |1 - ‖q‖| ≤ ‖q - a.1‖ := by
    have := abs_norm_sub_norm_le a.1 q
    rwa [norm_sph, norm_sub_rev] at this
  calc ‖‖q‖⁻¹ • q - a.1‖ ≤ ‖‖q‖⁻¹ • q - q‖ + ‖q - a.1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖q - a.1‖ + ‖q - a.1‖ := by rw [h1]; linarith
    _ = 2 * ‖q - a.1‖ := by ring

/-! ### Smooth homotopies are continuous homotopies -/

/-- A smooth homotopy restricts to a continuous homotopy. -/
theorem _root_.Milnor.SmoothHomotopic.homotopic {E H : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {X : Type*}
    [TopologicalSpace X] [ChartedSpace H X] {p : ℕ} {f g : X → Sph p}
    (h : SmoothHomotopic I 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f g) (hf : Continuous f)
    (hg : Continuous g) :
    (⟨f, hf⟩ : C(X, Sph p)).Homotopic ⟨g, hg⟩ := by
  obtain ⟨Hm, hHm, h0, h1⟩ := h
  refine ⟨{ toFun := fun q : unitInterval × X => Hm (q.2, (q.1 : ℝ))
            continuous_toFun := ?_
            map_zero_left := fun x => ?_
            map_one_left := fun x => ?_ }⟩
  · exact hHm.continuous.comp (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
  · exact h0 x
  · exact h1 x

end Problems

end Milnor
