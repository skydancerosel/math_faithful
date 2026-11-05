import Milnor.Chapter5.Degree
import Milnor.Chapter2.Brown

/-!
# Openness of the regular points and of the regular values

For a smooth map between oriented manifolds of the same dimension, the regular points form an
open set (the sign is locally constant near a regular point), so for a compact domain the regular
values form an open (and, by Brown's theorem, dense) set.  Finitely many such maps therefore
have a common regular value.
-/

open Set Module Filter Topology Function
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

universe u

section lin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {n : ℕ}

/-- For maps between spaces of the same dimension, surjectivity of the derivative is
bijectivity. -/
theorem bijective_iff_surjective_of_finrank (hE : finrank ℝ E = n) (hF : finrank ℝ F = n)
    (T : E →L[ℝ] F) : Bijective T ↔ Surjective T := by
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := (T : E →ₗ[ℝ] F))
    (by rw [hE, hF])).2 h

end lin

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] {n : ℕ}
  [IsManifold I ∞ M] [IsManifold J ∞ N] [I.Boundaryless] [J.Boundaryless]

/-- The sign is nonzero exactly at regular points. -/
theorem signAt_ne_zero_iff_isRegularPoint (hE : finrank ℝ E = n) (hF : finrank ℝ F = n)
    (oM : Orient I M n) (oN : Orient J N n) (f : M → N) (x : M) :
    signAt oM oN f x ≠ 0 ↔ IsRegularPoint I J f x := by
  rw [signAt_ne_zero_iff hE hF, bijective_iff_surjective_of_finrank hE hF]
  rfl

/-- **The regular points form an open set.** -/
theorem isOpen_regularPoints (hE : finrank ℝ E = n) (hF : finrank ℝ F = n) (oM : Orient I M n)
    (oN : Orient J N n) {f : M → N} (hf : ContMDiff I J ∞ f) :
    IsOpen {x | IsRegularPoint I J f x} := by
  rw [isOpen_iff_eventually]
  intro x hx
  filter_upwards [eventually_signAt_eq hE hF oM oN hf hx] with y hy
  rw [← signAt_ne_zero_iff_isRegularPoint hE hF oM oN, hy,
    signAt_ne_zero_iff_isRegularPoint hE hF oM oN]
  exact hx

/-- **The regular values of a map with compact domain form an open set.** -/
theorem isOpen_regularValues [CompactSpace M] [T2Space N] (hE : finrank ℝ E = n)
    (hF : finrank ℝ F = n) (oM : Orient I M n) (oN : Orient J N n) {f : M → N}
    (hf : ContMDiff I J ∞ f) : IsOpen (regularValues I J f) := by
  rw [regularValues_eq_compl_image_critPoints]
  have hc : IsClosed (critPoints I J f) := by
    have : critPoints I J f = {x | IsRegularPoint I J f x}ᶜ := rfl
    rw [this]
    exact (isOpen_regularPoints hE hF oM oN hf).isClosed_compl
  exact ((hc.isCompact.image hf.continuous).isClosed).isOpen_compl

/-- **Open and dense regular values** for a compact domain. -/
theorem dense_isOpen_regularValues [CompactSpace M] [T2Space N] [SecondCountableTopology M]
    (hE : finrank ℝ E = n) (hF : finrank ℝ F = n) (oM : Orient I M n) (oN : Orient J N n)
    {f : M → N} (hf : ContMDiff I J ∞ f) :
    Dense (regularValues I J f) ∧ IsOpen (regularValues I J f) :=
  ⟨dense_regularValues hf, isOpen_regularValues hE hF oM oN hf⟩

/-- A dense set meets finitely (countably) many open dense sets in a Baire space. -/
theorem exists_mem_of_dense_of_isOpen {X : Type*} [TopologicalSpace X] [BaireSpace X] [Nonempty X]
    {ι : Type*} [Finite ι] {s : Set X} (hs : Dense s) {t : ι → Set X} (ht : ∀ i, Dense (t i))
    (hto : ∀ i, IsOpen (t i)) : ∃ y, y ∈ s ∧ ∀ i, y ∈ t i := by
  have h1 : Dense (⋂ i, t i) := dense_iInter_of_isOpen hto ht
  have h2 : Dense (s ∩ ⋂ i, t i) := hs.inter_of_isOpen_right h1 (isOpen_iInter_of_finite hto)
  obtain ⟨y, hy⟩ := h2.nonempty
  exact ⟨y, hy.1, fun i => mem_iInter.1 hy.2 i⟩

end Milnor
