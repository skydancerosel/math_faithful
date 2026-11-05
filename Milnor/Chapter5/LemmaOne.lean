import Milnor.Chapter5.ArcSign
import Milnor.Chapter2.WithBoundary
import Milnor.Appendix.HalfSpace

/-!
# Milnor's Lemma 1 (chapter 5), in ambient form

Let `M` be an oriented `(n+1)`-manifold without boundary, `N` an oriented `n`-manifold without
boundary, `g : M → ℝ` smooth with `0` a regular value, `X = {g ≥ 0}` compact, `f : M → N` smooth,
`y` a regular value of `f` and of `f|_{g = 0}` (the transversality condition `hreg`).  Then

  `∑_{x ∈ f⁻¹(y) ∩ {g = 0}} sign d(f, g)_x = 0`,

the signs being taken relative to the orientation of `M` and the product orientation of `N × ℝ`.
Milnor's Lemma 1 is the case where the sum is read as the degree of `f|∂X` at `y` for the
boundary orientation of `∂X = {g = 0}`; the identification of the two signs is a matter of
convention (see the verification report).

*Proof.* `f⁻¹(y) ∩ X` is a compact 1-manifold with boundary `f⁻¹(y) ∩ {g = 0}` (Lemma 4); by the
Appendix its boundary points are paired by arcs, and the two ends of an arc have opposite signs
(`bdrySign_end_eq_neg`).
-/

open Set Module Filter Topology Function
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N] {n : ℕ}

/-- **Milnor's Lemma 1 (chapter 5), ambient form.**  The signed count of `f⁻¹(y) ∩ {g = 0}`,
with signs those of the pair map `(f, g) : M → N × ℝ`, vanishes. -/
theorem lemmaOne_ambient' (hE : finrank ℝ E = n + 1) (hF : finrank ℝ F = n)
    (oM : Orient I M (n + 1)) (oN : Orient J N n) {f : M → N} (hf : ContMDiff I J ∞ f) {y : N}
    (hy : IsRegularValue I J f y) {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g)
    (hreg : ∀ x, f x = y → g x = 0 → ∃ v, mfd I J f x v = 0 ∧ mfd I 𝓘(ℝ, ℝ) g x v ≠ 0)
    (hX : IsCompact {x : M | f x = y ∧ 0 ≤ g x}) :
    {x : M | f x = y ∧ g x = 0}.Finite ∧
    ∑ᶠ x ∈ {x : M | f x = y ∧ g x = 0}, signAt oM (oN.prodReal hF) (pairMap f g) x = 0 := by
  classical
  -- the level set as a 1-manifold
  have hZ : finrank ℝ ℝ + finrank ℝ F = finrank ℝ E := by
    rw [Module.finrank_self, hF, hE]; ring
  have hS := isSliceSubmanifold_preimage (Z := ℝ) hZ hf hy
  letI := hS.chartedSpace
  haveI := hS.isManifold
  have hZ' : finrank ℝ (⊥ : Submodule ℝ ℝ) + 1 = finrank ℝ ℝ := by simp
  have hreg' : ∀ x, f x = y → g x = 0 →
      ∃ v, mfderiv I J f x v = 0 ∧ mfderiv I 𝓘(ℝ, ℝ) g x v ≠ 0 := hreg
  have hA : IsHalfSliceSubmanifold 𝓘(ℝ, ℝ) (⊥ : Submodule ℝ ℝ) {q : f ⁻¹' {y} | 0 ≤ g q.1}
      {q | g q.1 = 0} :=
    isHalfSliceSubmanifold_levelSet (Z := ℝ) (Z' := (⊥ : Submodule ℝ ℝ)) hZ hZ' hf hy hg hreg'
  set A : Set (f ⁻¹' {y}) := {q | 0 ≤ g q.1} with hA_def
  set B : Set (f ⁻¹' {y}) := {q | g q.1 = 0} with hB_def
  letI := hA.chartedSpace
  -- compactness of `A`
  have hAc : IsCompact A := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    convert hX using 1
    ext x; constructor
    · rintro ⟨q, hq, rfl⟩; exact ⟨q.2, hq⟩
    · rintro ⟨hx1, hx2⟩; exact ⟨⟨x, hx1⟩, hx2, rfl⟩
  haveI : CompactSpace A := isCompact_iff_compactSpace.1 hAc
  have hB := hA.boundaryCompatible
  -- every boundary point has a partner of opposite sign
  have hpart : ∀ p : A, p.1 ∈ B → ∃ q : A, q.1 ∈ B ∧ q ≠ p ∧
      {q : A | q.1 ∈ B} ∩ connectedComponent p = {p, q} ∧
      bdrySign hF oM oN f g p.1.1 = -bdrySign hF oM oN f g q.1.1 := by
    intro p hp
    obtain ⟨Ar, hfrom, hsup⟩ := OneManifold.exists_closed_arc (M := A) halfSpaceHomeomorph hB hp
    refine ⟨Ar.invFun (sSup Ar.target), ?_, ?_, hfrom.boundary_inter_component hsup, ?_⟩
    · have hmem : Ar.invFun (sSup Ar.target) ∈ {q : A | q.1 ∈ B} ∩ connectedComponent p := by
        rw [hfrom.boundary_inter_component hsup]; simp
      exact hmem.1
    · intro h
      have := congrArg Ar.toFun h
      rw [Ar.right_inv hsup, hfrom.2.1] at this
      exact hfrom.pos.ne' this
    · exact bdrySign_end_eq_neg hE hF oM oN hf hy hS.contMDiff_val Subtype.val_injective
        (fun a => a.2) (fun a v => mem_range_mfderiv_val_iff hZ hf hy a v) hg hreg
        (fun a ha => ha) Ar hp hfrom hsup
  choose! ι' hιB hιne hιeq hιsign using hpart
  have hBfin : ({q : A | q.1 ∈ B} : Set A).Finite := OneManifold.finite_boundary hB
  -- `ι'` is an involution of the boundary
  have hinv : ∀ p : A, p.1 ∈ B → ι' (ι' p) = p := by
    intro p hp
    have hq := hιB p hp
    have hK : connectedComponent (ι' p) = connectedComponent p := by
      have : ι' p ∈ {q : A | q.1 ∈ B} ∩ connectedComponent p := by rw [hιeq p hp]; simp
      exact (connectedComponent_eq this.2).symm
    have h1 := hιeq (ι' p) hq
    rw [hK, hιeq p hp] at h1
    have : ι' (ι' p) ∈ ({p, ι' p} : Set A) := by rw [h1]; simp
    rcases this with h | h
    · exact h
    · rw [mem_singleton_iff] at h
      exact absurd h (hιne (ι' p) hq)
  -- the sum over the boundary vanishes
  set ε : A → ℤ := fun q => bdrySign hF oM oN f g q.1.1 with hε
  have hbij : ({q : A | q.1 ∈ B} : Set A).BijOn ι' {q : A | q.1 ∈ B} :=
    ⟨fun q hq => hιB q hq, fun q hq q' hq' h => by rw [← hinv q hq, ← hinv q' hq', h],
      fun q hq => ⟨ι' q, hιB q hq, hinv q hq⟩⟩
  have h1 : ∑ᶠ q ∈ {q : A | q.1 ∈ B}, ε (ι' q) = ∑ᶠ q ∈ {q : A | q.1 ∈ B}, ε q :=
    finsum_mem_eq_of_bijOn ι' hbij (fun _ _ => rfl)
  have h2 : ∑ᶠ q ∈ {q : A | q.1 ∈ B}, ε (ι' q) = ∑ᶠ q ∈ {q : A | q.1 ∈ B}, -ε q :=
    finsum_mem_congr rfl (fun q hq => by simp only [ε]; rw [hιsign q hq]; ring)
  have h3 : ∑ᶠ q ∈ {q : A | q.1 ∈ B}, -ε q = -∑ᶠ q ∈ {q : A | q.1 ∈ B}, ε q :=
    finsum_mem_neg_distrib ε hBfin
  have hsum : ∑ᶠ q ∈ {q : A | q.1 ∈ B}, ε q = 0 := by
    have := h1.symm.trans (h2.trans h3)
    omega
  -- transfer to `M`
  have himg : {x : M | f x = y ∧ g x = 0} = (fun q : A => q.1.1) '' {q : A | q.1 ∈ B} := by
    ext x; constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨⟨⟨x, hx1⟩, le_of_eq hx2.symm⟩, hx2, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.1.2, hq⟩
  have hinj : InjOn (fun q : A => q.1.1) {q : A | q.1 ∈ B} := fun q _ q' _ h =>
    Subtype.ext (Subtype.ext h)
  refine ⟨by rw [himg]; exact hBfin.image _, ?_⟩
  rw [himg, finsum_mem_image hinj]
  exact hsum

/-- **Milnor's Lemma 1 (chapter 5), ambient form.**  The signed count of `f⁻¹(y) ∩ {g = 0}`,
with signs those of the pair map `(f, g) : M → N × ℝ`, vanishes. -/
theorem lemmaOne_ambient (hE : finrank ℝ E = n + 1) (hF : finrank ℝ F = n)
    (oM : Orient I M (n + 1)) (oN : Orient J N n) {f : M → N} (hf : ContMDiff I J ∞ f) {y : N}
    (hy : IsRegularValue I J f y) {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g)
    (hreg : ∀ x, f x = y → g x = 0 → ∃ v, mfd I J f x v = 0 ∧ mfd I 𝓘(ℝ, ℝ) g x v ≠ 0)
    (hX : IsCompact {x : M | f x = y ∧ 0 ≤ g x}) :
    ∑ᶠ x ∈ {x : M | f x = y ∧ g x = 0}, signAt oM (oN.prodReal hF) (pairMap f g) x = 0 :=
  (lemmaOne_ambient' hE hF oM oN hf hy hg hreg hX).2

end Milnor
