import Morse.Chapter2.CellAttach
import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Homotopy.Equiv

/-!
Milnor, *Morse Theory*, §3, pp. 14 and 16: "`e^λ` is attached to `M^{c-ε}` as required".

# `M^{c-ε} ∪ e^λ` is `M^{c-ε}` with a `λ`-cell attached

Milnor's Theorem 3.2 (p. 14) says that `M^{c+ε}` has the homotopy type of `M^{c-ε}` *with a
`λ`-cell attached*, that is, of the space obtained from the disjoint union of `M^{c-ε}` and the
closed disk `D^λ` by identifying each point `u` of the boundary sphere `S^{λ-1}` with its image
under an attaching map `φ : S^{λ-1} → M^{c-ε}`. What his proof produces is the subspace
`M^{c-ε} ∪ e^λ` of `M`, for a cell `e^λ ⊆ M` with `e^λ ∩ M^{c-ε} = ė^λ`; the identification of the
two is the single sentence "Note that `e^λ ∩ M^{c-ε}` is precisely the boundary `ė^λ`, so that
`e^λ` is attached to `M^{c-ε}` as required" (p. 16).

That sentence is Lemma D of the exposition (`Exposition/Chapter2.md`, §2): if a Hausdorff space
`W` is the union of a closed set `A` and the image of a compact disk under a continuous injective
map `χ` with `χ⁻¹(A) = S^{λ-1}`, then `W` is the adjunction space `A ∪_{χ|S^{λ-1}} D^λ`. The proof
is that `A ⊔ D^λ → W` is a closed continuous surjection, hence a quotient map, which identifies
exactly the points `u ∈ S^{λ-1}` and `χ(u) ∈ A`. Here the adjunction space is Mathlib's pushout in
`TopCat` of the inclusion `∂𝔻 λ ⟶ 𝔻 λ` (`TopCat.diskBoundaryInclusion`, the basic cell of
Mathlib's CW complexes, `Mathlib/Topology/CWComplex/Abstract/Basic.lean`) and the attaching map, and
Lemma D is proved by checking the universal property directly: a pair of maps out of `A` and
`D^λ` that agree on `S^{λ-1}` glues to a unique map out of `W`, continuous by the pasting lemma
for the closed cover `W = A ∪ χ(D^λ)`, on whose pieces it is the given map composed with the
inverse of a homeomorphism (`χ` is a closed embedding, compact to Hausdorff).

## What Milnor's text leaves implicit

* The sentence quoted above is all that Milnor says. It uses that `M^{c-ε}` is closed (`f` is
  continuous), that `e^λ` is compact, hence closed (`M` is Hausdorff), and that `χ` is a
  homeomorphism onto `e^λ`.
* The attaching map is an embedding `S^{λ-1} → M^{c-ε}` (`φ` is injective,
  `Morse.theorem_3_2_attach`), and is the restriction of the characteristic map
  `χ(z) = φ⁻¹(√ε z, 0)` of the cell (`Morse/Chapter2/CellAttach.lean`).

## Main results

* `Morse.isPushout_of_cell`: Lemma D in `TopCat`.
* `Morse.exists_isPushout_union_cell`: Lemma D for a cell `χ(D^n)` in a normed space, with
  Mathlib's `𝔻 n` and `∂𝔻 n`.
* `Morse.theorem_3_2_attach`: **Theorem 3.2** in Milnor's words, for `M = E` a finite-dimensional
  real inner product space: for all sufficiently small `ε > 0`, there is an embedding
  `φ : S^{λ-1} → M^{c-ε}` such that `M^{c+ε}` is homotopy equivalent to the pushout of
  `D^λ ← S^{λ-1} → M^{c-ε}`.
-/

open Set CategoryTheory Limits Topology TopCat
open scoped ContDiff

universe u

noncomputable section

namespace Morse

/-- **Lemma D** (attaching a cell inside a space). Let `W` be Hausdorff, `j : A → W` a closed
embedding, `D` compact, `χ : D → W` continuous and injective, and `i : S → D`. Suppose that `W` is
the union of the images of `j` and `χ`, that `χ(d)` lies in the image of `j` only for `d` in the
image of `i`, and that `φ : S → A` satisfies `j ∘ φ = χ ∘ i`. Then the square
`S → A → W`, `S → D → W` is a pushout in `TopCat`: `W` is `A` with `D` attached along `φ`. -/
theorem isPushout_of_cell {W A D S : Type u} [TopologicalSpace W] [TopologicalSpace A]
    [TopologicalSpace D] [TopologicalSpace S] [T2Space W] [CompactSpace D]
    (j : C(A, W)) (hj : IsClosedEmbedding j) (χ : C(D, W)) (hχ : Function.Injective χ)
    (i : C(S, D)) (φ : C(S, A)) (hφ : ∀ s, j (φ s) = χ (i s))
    (hcover : ∀ w, w ∉ range j → w ∈ range χ) (hpre : ∀ d, χ d ∈ range j → d ∈ range i) :
    IsPushout (TopCat.ofHom φ) (TopCat.ofHom i) (TopCat.ofHom j) (TopCat.ofHom χ) := by
  classical
  have hcomm : TopCat.ofHom φ ≫ TopCat.ofHom j = TopCat.ofHom i ≫ TopCat.ofHom χ := by
    ext s
    exact hφ s
  have hχe := χ.continuous.isClosedEmbedding hχ
  -- `j` and `χ` are homeomorphisms onto their (closed) images
  let eχ : D ≃ₜ range χ := hχe.isEmbedding.toHomeomorph
  let ej : A ≃ₜ range j := hj.isEmbedding.toHomeomorph
  have hej : ∀ a, (ej a : W) = j a := fun a => rfl
  have heχ : ∀ d, (eχ d : W) = χ d := fun d => rfl
  -- the glued map
  let g : ∀ s : PushoutCocone (TopCat.ofHom φ) (TopCat.ofHom i), W → s.pt := fun s w =>
    if hw : w ∈ range j then s.inl (ej.symm ⟨w, hw⟩) else s.inr (eχ.symm ⟨w, hcover w hw⟩)
  have hcond : ∀ (s : PushoutCocone (TopCat.ofHom φ) (TopCat.ofHom i)) (s₀ : S),
      s.inl (φ s₀) = s.inr (i s₀) := fun s s₀ =>
    ConcreteCategory.congr_hom s.condition s₀
  have hgj : ∀ (s : PushoutCocone (TopCat.ofHom φ) (TopCat.ofHom i)) (a : A),
      g s (j a) = s.inl a := by
    intro s a
    simp only [g]
    rw [dif_pos ⟨a, rfl⟩]
    exact congrArg s.inl.hom (ej.symm_apply_apply a)
  have hgχ : ∀ (s : PushoutCocone (TopCat.ofHom φ) (TopCat.ofHom i)) (d : D),
      g s (χ d) = s.inr d := by
    intro s d
    by_cases hd : χ d ∈ range j
    · obtain ⟨s₀, rfl⟩ := hpre d hd
      rw [← hφ s₀, hgj, hcond]
    · simp only [g]
      rw [dif_neg hd]
      exact congrArg s.inr.hom (eχ.symm_apply_apply d)
  -- continuity: the pasting lemma for the closed cover `W = j(A) ∪ χ(D)`
  have hgcont : ∀ s : PushoutCocone (TopCat.ofHom φ) (TopCat.ofHom i), Continuous (g s) := by
    intro s
    rw [← continuousOn_univ]
    have hU : range j ∪ range χ = univ := eq_univ_of_forall fun w => by
      by_cases hw : w ∈ range j
      · exact Or.inl hw
      · exact Or.inr (hcover w hw)
    rw [← hU]
    refine ContinuousOn.union_of_isClosed ?_ ?_ hj.isClosed_range hχe.isClosed_range
    · rw [continuousOn_iff_continuous_domRestrict]
      refine (s.inl.hom.continuous.comp ej.symm.continuous).congr fun w => ?_
      obtain ⟨a, ha⟩ := ej.surjective w
      rw [← ha, Function.comp_apply, ej.symm_apply_apply, domRestrict_apply, hej, hgj]
    · rw [continuousOn_iff_continuous_domRestrict]
      refine (s.inr.hom.continuous.comp eχ.symm.continuous).congr fun w => ?_
      obtain ⟨d, hd⟩ := eχ.surjective w
      rw [← hd, Function.comp_apply, eχ.symm_apply_apply, domRestrict_apply, heχ, hgχ]
  refine IsPushout.of_isColimit' ⟨hcomm⟩
    (PushoutCocone.IsColimit.mk hcomm (fun s => TopCat.ofHom ⟨g s, hgcont s⟩) ?_ ?_ ?_)
  · intro s
    ext a
    exact hgj s a
  · intro s
    ext d
    exact hgχ s d
  · intro s m h1 h2
    ext w
    change m w = g s w
    by_cases hw : w ∈ range j
    · obtain ⟨a, rfl⟩ := hw
      rw [hgj]
      exact ConcreteCategory.congr_hom h1 a
    · obtain ⟨d, rfl⟩ := hcover w hw
      rw [hgχ]
      exact ConcreteCategory.congr_hom h2 d

section Normed

variable {E : Type u} [NormedAddCommGroup E]

/-- **Lemma D for a cell in a normed space** (p. 16, "`e^λ` is attached to `M^{c-ε}` as
required"). Let `A ⊆ E` be closed and `χ : ℝⁿ → E` continuous and injective on the closed unit
ball `D^n`, with `χ(z) ∈ A ⟺ ‖z‖ = 1` for `z ∈ D^n`. Then `A ∪ χ(D^n)` is the space obtained from
`A` by attaching an `n`-cell along `φ = χ|S^{n-1}` (an injective map `∂𝔻 n → A`): it is the pushout
in `TopCat` of `φ` and `∂𝔻 n ⟶ 𝔻 n`. -/
theorem exists_isPushout_union_cell {A : Set E} (hA : IsClosed A) {n : ℕ}
    {χ : EuclideanSpace ℝ (Fin n) → E} (hcont : ContinuousOn χ (Metric.closedBall 0 1))
    (hinj : InjOn χ (Metric.closedBall 0 1))
    (hbdry : ∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, χ z ∈ A ↔ ‖z‖ = 1) :
    ∃ (φ : ∂𝔻 n ⟶ TopCat.of A) (χ' : 𝔻 n ⟶ TopCat.of ↥(A ∪ χ '' Metric.closedBall 0 1)),
      Function.Injective φ ∧ (∀ s, (φ s : E) = χ s.down) ∧
      IsPushout φ (diskBoundaryInclusion n)
        (TopCat.ofHom ⟨inclusion subset_union_left, continuous_inclusion subset_union_left⟩)
        χ' := by
  set W := ↥(A ∪ χ '' Metric.closedBall 0 1)
  have hsub : A ⊆ A ∪ χ '' Metric.closedBall 0 1 := subset_union_left
  let j : C(A, W) := ⟨inclusion hsub, continuous_inclusion hsub⟩
  have hj : IsClosedEmbedding j :=
    ⟨IsEmbedding.inclusion hsub, by
      change IsClosed (range (inclusion hsub))
      rw [range_inclusion]
      exact hA.preimage continuous_subtype_val⟩
  let χ' : C(𝔻 n, W) :=
    ⟨fun d => ⟨χ d.down, Or.inr ⟨d.down, d.down.2, rfl⟩⟩,
      (hcont.comp_continuous (continuous_subtype_val.comp continuous_uliftDown)
        fun d => d.down.2).subtype_mk _⟩
  have hχ' : Function.Injective χ' := by
    intro d d' h
    have h' : χ d.down = χ d'.down := congrArg Subtype.val h
    exact ULift.ext _ _ (Subtype.ext (hinj d.down.2 d'.down.2 h'))
  have hmemA : ∀ s : ∂𝔻 n, χ s.down ∈ A := fun s =>
    (hbdry _ (Metric.sphere_subset_closedBall s.down.2)).2 (mem_sphere_zero_iff_norm.1 s.down.2)
  let φ : C(∂𝔻 n, A) :=
    ⟨fun s => ⟨χ s.down, hmemA s⟩,
      ((hcont.comp_continuous (continuous_subtype_val.comp continuous_uliftDown)
        fun s => Metric.sphere_subset_closedBall s.down.2)).subtype_mk _⟩
  have hφ : ∀ s, j (φ s) = χ' ((diskBoundaryInclusion n).hom s) := fun s => rfl
  have hcover : ∀ w, w ∉ range j → w ∈ range χ' := by
    rintro ⟨w, hw⟩ hw'
    rcases hw with hw | ⟨z, hz, rfl⟩
    · exact absurd ⟨⟨w, hw⟩, rfl⟩ hw'
    · exact ⟨ULift.up ⟨z, hz⟩, rfl⟩
  have hpre : ∀ d, χ' d ∈ range j → d ∈ range (diskBoundaryInclusion n).hom := by
    rintro d ⟨a, ha⟩
    have h1 : χ d.down ∈ A := by
      have := congrArg Subtype.val ha
      change (a : E) = χ d.down at this
      rw [← this]
      exact a.2
    have h2 : ‖(d.down : EuclideanSpace ℝ (Fin n))‖ = 1 := (hbdry _ d.down.2).1 h1
    exact ⟨ULift.up ⟨d.down, mem_sphere_zero_iff_norm.2 h2⟩, rfl⟩
  refine ⟨TopCat.ofHom φ, TopCat.ofHom χ', fun s s' h => ?_, fun s => rfl,
    isPushout_of_cell j hj χ' hχ' (diskBoundaryInclusion n).hom φ hφ hcover hpre⟩
  have h' : χ s.down = χ s'.down := congrArg Subtype.val h
  exact ULift.ext _ _ (Subtype.ext (hinj (Metric.sphere_subset_closedBall s.down.2)
    (Metric.sphere_subset_closedBall s'.down.2) h'))

end Normed

section Theorem32

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Theorem 3.2** (Milnor, p. 14), literally: let `f : E → ℝ` be smooth on a finite-dimensional
real inner product space, `p` a non-degenerate critical point of index `λ`, `c = f(p)`, and suppose
that `f⁻¹[c - ε₀, c + ε₀]` is compact and contains no critical point of `f` other than `p`. Then for
all sufficiently small `ε > 0`, `M^{c+ε}` has the homotopy type of `M^{c-ε}` with a `λ`-cell
attached: there is an embedding `φ : S^{λ-1} → M^{c-ε}` such that `M^{c+ε}` is homotopy equivalent
to the pushout of `D^λ ← S^{λ-1} → M^{c-ε}` (Mathlib's `𝔻 λ` and `∂𝔻 λ`). -/
theorem theorem_3_2_attach {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {p : E}
    (hcrit : IsCriticalPoint f p) (hnd : IsNondegenerate (hessian f p)) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hK : IsCompact (f ⁻¹' Icc (f p - ε₀) (f p + ε₀)))
    (honly : ∀ q ∈ f ⁻¹' Icc (f p - ε₀) (f p + ε₀), IsCriticalPoint f q → q = p) :
    ∃ ε₁ > 0, ∀ ε, 0 < ε → ε ≤ ε₁ →
      ∃ φ : ∂𝔻 (index (hessian f p)) ⟶ TopCat.of (sublevel f (f p - ε)),
        Function.Injective φ ∧
          Nonempty (ContinuousMap.HomotopyEquiv (sublevel f (f p + ε))
            ((pushout φ (diskBoundaryInclusion (index (hessian f p))) : TopCat.{u}) : Type u)) := by
  obtain ⟨ε₁, hε₁, H⟩ := theorem_3_2_homotopyEquiv hf hcrit hnd hε₀ hK honly
  refine ⟨ε₁, hε₁, fun ε hε hεε₁ => ?_⟩
  obtain ⟨χ, hcont, hinj, hbdry, -, e, -⟩ := H ε hε hεε₁
  obtain ⟨φ, χ', hφ, -, hpo⟩ :=
    exists_isPushout_union_cell (isClosed_le hf.continuous continuous_const) hcont hinj hbdry
  exact ⟨φ, hφ, ⟨e.symm.trans (homeoOfIso hpo.isoPushout).toHomotopyEquiv⟩⟩

end Theorem32

end Morse
