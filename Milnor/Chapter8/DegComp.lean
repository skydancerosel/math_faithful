import Milnor.Chapter6.Compose
import Milnor.Chapter6.RegularOpen

/-!
# Problem 1: the degree of a composition

For smooth maps `f : M → N` and `g : N → P` between oriented manifolds of the same dimension
(`M`, `N` compact, `N`, `P` connected), `deg (g ∘ f) = deg g · deg f` (Milnor §8, Problem 1).

Proof: choose `z` which is a regular value both of `g` and of `g ∘ f` (the regular values of `g`
form an open dense set, those of `g ∘ f` a dense set).  By the chain rule every `y ∈ g⁻¹(z)`
is a regular value of `f`, so `degAt f y = deg f`.  Regrouping the signed count over
`(g ∘ f)⁻¹(z)` along the fibres of `f` gives
`deg (g ∘ f) = ∑_{y ∈ g⁻¹(z)} signAt g y · degAt f y = (∑_{y ∈ g⁻¹(z)} signAt g y) · deg f
= deg g · deg f`.

The three model spaces live in one universe because `deg` requires it.
-/

open Set Module Filter Topology Function
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

namespace Problems

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  {F' : Type u} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {G' : Type*} [TopologicalSpace G'] {K : ModelWithCorners ℝ F' G'} [K.Boundaryless]
  {P : Type*} [TopologicalSpace P] [ChartedSpace G' P] [IsManifold K ∞ P] {n : ℕ}

omit [I.Boundaryless] [IsManifold I ∞ M] [J.Boundaryless] [IsManifold J ∞ N] [K.Boundaryless]
  [IsManifold K ∞ P] in
/-- If `z` is a regular value of `g ∘ f` (all three manifolds of the same dimension), then every
`y ∈ g⁻¹(z)` is a regular value of `f`: the derivative of `g ∘ f` is `dg ∘ df`, and if it is
onto then it is one-to-one, hence so is `df`, hence `df` is onto. -/
theorem isRegularValue_of_isRegularValue_comp (hE : finrank ℝ E = n) (hF : finrank ℝ F = n)
    (hF' : finrank ℝ F' = n) {f : M → N} {g : N → P} (hf : ContMDiff I J ∞ f)
    (hg : ContMDiff J K ∞ g) {z : P} (hz : IsRegularValue I K (fun x => g (f x)) z) {y : N}
    (hy : g y = z) : IsRegularValue I J f y := by
  intro x hx
  have hc : mfd I K (fun x => g (f x)) x = (mfd J K g (f x)).comp (mfd I J f x) :=
    HasMFDerivAt.mfd_eq ((hasMFDerivAt_mfd (I := J) (J := K)
      (hg.mdifferentiableAt (x := f x) (by simp))).comp x
      (hasMFDerivAt_mfd (I := I) (J := J) (hf.mdifferentiableAt (by simp))))
  have hsurj : Surjective (mfd I K (fun x => g (f x)) x) := hz x (by simp only [hx, hy])
  rw [hc] at hsurj
  have hinj : Injective ((mfd J K g (f x)).comp (mfd I J f x)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (((mfd J K g (f x)).comp (mfd I J f x) : E →L[ℝ] F') : E →ₗ[ℝ] F'))
      (hE.trans hF'.symm)).2 hsurj
  rw [ContinuousLinearMap.coe_comp] at hinj
  have hinjf : Injective (mfd I J f x) := hinj.of_comp
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (mfd I J f x : E →ₗ[ℝ] F)) (hE.trans hF.symm)).1 hinjf

/-- **Problem 1.** `deg (g ∘ f) = deg g · deg f`. -/
theorem deg_comp [CompactSpace M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace N] [T2Space N] [SecondCountableTopology N] [PreconnectedSpace N]
    [T2Space P] [PreconnectedSpace P]
    (hE : finrank ℝ E = n) (hF : finrank ℝ F = n) (hF' : finrank ℝ F' = n)
    (oM : Orient I M n) (oN : Orient J N n) (oP : Orient K P n)
    {f : M → N} {g : N → P} (hf : ContMDiff I J ∞ f) (hg : ContMDiff J K ∞ g) :
    deg oM oP (fun x => g (f x)) = deg oN oP g * deg oM oN f := by
  have hgf : ContMDiff I K ∞ (fun x => g (f x)) := hg.comp hf
  rcases isEmpty_or_nonempty P with hP | hP
  · -- `P` is empty: there is no regular value, and both sides vanish
    have h1 : ¬ ∃ z, IsRegularValue I K (fun x => g (f x)) z := fun ⟨z, _⟩ => isEmptyElim z
    have h2 : ¬ ∃ z, IsRegularValue J K g z := fun ⟨z, _⟩ => isEmptyElim z
    unfold deg
    rw [dif_neg h1, dif_neg h2, zero_mul]
  -- a common regular value `z` of `g ∘ f` and of `g`
  obtain ⟨z, hzgf, hzg⟩ := (dense_regularValues hgf).exists_mem_open
    (isOpen_regularValues hF hF' oN oP hg) (dense_regularValues hg).nonempty
  change IsRegularValue I K (fun x => g (f x)) z at hzgf
  change IsRegularValue J K g z at hzg
  -- finiteness of the fibres
  have hfin_g : (g ⁻¹' {z}).Finite := hzg.finite_preimage (hF.trans hF'.symm) hg (by simp)
  have hfin_gf : ((fun x => g (f x)) ⁻¹' {z}).Finite :=
    hzgf.finite_preimage (hE.trans hF'.symm) hgf (by simp)
  have hfin_f : ∀ y ∈ g ⁻¹' {z}, (f ⁻¹' {y}).Finite := fun y hy =>
    hfin_gf.subset fun x hx => by
      have hx' : f x = y := hx
      have hy' : g y = z := hy
      show g (f x) = z
      rw [hx', hy']
  -- `(g ∘ f)⁻¹(z)` is the disjoint union of the fibres `f⁻¹(y)`, `y ∈ g⁻¹(z)`
  have hunion : (fun x => g (f x)) ⁻¹' {z} = ⋃ y ∈ g ⁻¹' {z}, f ⁻¹' {y} := by
    ext x
    simp
  have hdisj : (g ⁻¹' {z}).PairwiseDisjoint (fun y => f ⁻¹' {y}) := by
    intro y₁ _ y₂ _ hne
    exact Set.disjoint_left.2 fun x hx1 hx2 => hne ((hx1 : f x = y₁).symm.trans hx2)
  rw [deg_eq hE hF' oM oP hgf hzgf, deg_eq hF hF' oN oP hg hzg]
  unfold degAt
  rw [hunion, finsum_mem_biUnion hdisj hfin_g hfin_f, finsum_mem_mul]
  refine finsum_mem_congr rfl fun y hy => ?_
  have hy' : g y = z := hy
  rw [deg_eq hE hF oM oN hf (isRegularValue_of_isRegularValue_comp hE hF hF' hf hg hzgf hy'),
    degAt, mul_finsum_mem]
  refine finsum_mem_congr rfl fun x hx => ?_
  have hx' : f x = y := hx
  rw [signAt_comp' hE hF oM oN oP (hf.mdifferentiableAt (by simp))
    (hg.mdifferentiableAt (by simp)), hx']

end Problems

end Milnor
