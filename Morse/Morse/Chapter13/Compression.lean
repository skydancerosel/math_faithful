import Morse.Homotopy.CellAttach
import Morse.Chapter2.SeveralCritical
import Morse.Chapter2.Submanifold

/-!
Milnor, *Morse Theory*, §22, pp. 121–122: the step "`g⁻¹(−∞, c + δ]` has the homotopy type of
`g⁻¹(−∞, 2δ]` with cells of dimension `≥ λ₀` attached; since `r < λ₀`, `h` is homotopic to a map
into `g⁻¹(−∞, 2δ]`" in the proof of Lemma 22.5 (Lemma D and (T4), (T5) of
Exposition/Chapter13.md, §3).

# Pushing maps down past critical levels of high index

## Milnor's text, paraphrased

(p. 122) In the proof of Lemma 22.5, `g` has only non-degenerate critical points in
`g⁻¹[2δ, c + δ]`, all of index `≥ λ₀`; so `g⁻¹(−∞, c + δ]` has the homotopy type of
`g⁻¹(−∞, 2δ]` with cells of dimension `≥ λ₀` attached (§3), and since `r < λ₀` the map
`h : (Iʳ, ∂Iʳ) → (M^{c}, M⁰)` is homotopic, relative to `∂Iʳ`, to a map into `g⁻¹(−∞, 2δ]`.

## What is formalized

* `Morse.PushesInto P A X`: every map `P → T` with values in `X` is homotopic, relative to the
  preimage of `A`, to a map with values in `A` (the homotopy may move in all of `T`).  For
  `P = Iʳ` and maps sending `∂Iʳ` into `A`, this is Milnor's "`π_r(X, A) = 0`" in the strong
  form of Exposition/Chapter13.md, (H1).  Basic properties: `Morse.PushesInto.trans`,
  `Morse.PushesInto.mono`, `Morse.pushesInto_self`.
* `Morse.pushesInto_of_isStrongDeformationRetract`: a strong deformation retract `A` of `X`
  (the conclusions of Theorem 3.1 and Remark 3.3 in the project) pushes maps from any `P`.
* `Morse.pushesInto_union_cells`: **(T5), pushing a disc off cells**: if `A` is closed in a
  Hausdorff space and `e₁, …, e_k` are disjoint embedded cells meeting `A` exactly in their
  boundaries, of dimensions `> dim P` (`P` compact, embedded in a real vector space of
  dimension `< dim eᵢ`), then `A` pushes maps from `P` out of `A ∪ e₁ ∪ ⋯ ∪ e_k`.  From the
  push-off lemma `Morse.Homotopy.compresses_union_cell`.
* `Morse.lemma_D`: **Lemma D** of the exposition, on a slice submanifold `N ⊆ V`: let
  `f = F|N`, `F : V → ℝ` smooth, with `f⁻¹(−∞, a₀]` compact, `a` not a critical value, and every
  critical point `q` with `a < f(q) ≤ a₀` non-degenerate of index `≥ λ₀`.  Then for `b < a₀`,
  `N^a` pushes maps from `P` out of `N^b`, for every compact `P` embedded in a real vector space
  of dimension `< λ₀`.

## What Milnor leaves implicit

* "Has the homotopy type of … with cells attached" is not enough by itself: the argument needs
  deformations fixing the lower level, which Milnor's proofs of Theorems 3.1 and 3.2 provide
  (here: the strong deformation retracts of `Morse.theorem_3_1_submanifold` and
  `Morse.remark_3_3_submanifold`), and the push-off lemma of cellular approximation (Hatcher,
  Lemma 4.10) for "since `r < λ₀`".
* The critical points above `a` are finitely many: they are isolated (non-degenerate) in the
  compact `f⁻¹[a, a₀]`, and cannot accumulate at level `a`, which is regular.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold unitInterval

noncomputable section

namespace Morse

open Morse.Homotopy (homotopyRelMono homotopyRelOfFun)

/-! ### Pushing maps into a subset -/

section Push

variable (P : Type*) [TopologicalSpace P] {T : Type*} [TopologicalSpace T]

/-- **`A` pushes maps from `P` out of `X`**: every map `h : P → T` with values in `X` is
homotopic, relative to `h⁻¹(A)`, to a map with values in `A`. -/
def PushesInto (A X : Set T) : Prop :=
  ∀ h : C(P, T), (∀ p, h p ∈ X) → ∃ h' : C(P, T), (∀ p, h' p ∈ A) ∧ h.HomotopicRel h' (h ⁻¹' A)

variable {P}

theorem pushesInto_self (A : Set T) : PushesInto P A A := fun h hA =>
  ⟨h, hA, ContinuousMap.HomotopicRel.refl h⟩

theorem PushesInto.mono {A X X' : Set T} (h : PushesInto P A X) (hX : X' ⊆ X) :
    PushesInto P A X' := fun g hg => h g fun p => hX (hg p)

/-- **Pushing in two steps.** -/
theorem PushesInto.trans {A B X : Set T} (hAB : A ⊆ B) (h₁ : PushesInto P A B)
    (h₂ : PushesInto P B X) : PushesInto P A X := by
  intro h hX
  obtain ⟨g, hgB, ⟨F⟩⟩ := h₂ h hX
  obtain ⟨g', hg'A, ⟨G⟩⟩ := h₁ g hgB
  have hsub : h ⁻¹' A ⊆ h ⁻¹' B := fun p hp => hAB hp
  have hsub' : h ⁻¹' A ⊆ g ⁻¹' A := fun p hp => by
    change g p ∈ A
    rw [← F.fst_eq_snd (hsub hp)]
    exact hp
  exact ⟨g', hg'A, ⟨(homotopyRelMono F hsub).trans (homotopyRelMono G hsub')⟩⟩

/-- **A strong deformation retract pushes maps from any space**: if the subspace `X` strongly
deformation retracts onto `A ⊆ X`, `A` pushes maps out of `X`. -/
theorem pushesInto_of_isStrongDeformationRetract {A X : Set T} (_hAX : A ⊆ X)
    (hsdr : IsStrongDeformationRetract ((↑) ⁻¹' A : Set X)) : PushesInto P A X := by
  intro h hX
  obtain ⟨r, hr, ⟨G⟩⟩ := hsdr
  let k : C(P, X) := ⟨fun p => ⟨h p, hX p⟩, by fun_prop⟩
  let H : C(I × P, T) := ⟨fun z => (G (z.1, k z.2) : T), by
    have : Continuous fun z : I × P => G (z.1, k z.2) :=
      G.continuous.comp (continuous_fst.prodMk (k.continuous.comp continuous_snd))
    exact continuous_subtype_val.comp this⟩
  let h' : C(P, T) := ⟨fun p => (r (k p) : T), by fun_prop⟩
  refine ⟨h', fun p => hr (k p), ⟨homotopyRelOfFun H (fun p => ?_) (fun p => ?_)
    fun t p hp => ?_⟩⟩
  · change (G (0, k p) : T) = h p
    rw [G.apply_zero]
    rfl
  · change (G (1, k p) : T) = r (k p)
    rw [G.apply_one]
  · change (G (t, k p) : T) = h p
    rw [G.eq_fst t (show k p ∈ ((↑) ⁻¹' A : Set X) from hp)]
    rfl

end Push

/-! ### Pushing off cells -/

section Cells

universe u

variable {T : Type u} [TopologicalSpace T] [T2Space T]
  {P : Type*} [TopologicalSpace P] [CompactSpace P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : P → E} (hι : Continuous ι) (hιinj : Injective ι)
include hι hιinj

/-- **Pushing off one cell** (T5): a closed `A` pushes maps from `P` out of `A ∪ e`, for an
embedded cell `e` of dimension `n > dim P` meeting `A` exactly in its boundary. -/
theorem pushesInto_union_cell {A : Set T} {n : ℕ} {χ : EuclideanSpace ℝ (Fin n) → T}
    (hA : IsClosed A) (hcont : ContinuousOn χ (closedBall 0 1)) (hinj : InjOn χ (closedBall 0 1))
    (hbdry : ∀ z ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, χ z ∈ A ↔ ‖z‖ = 1)
    (hn : finrank ℝ E < n) : PushesInto P A (A ∪ χ '' closedBall 0 1) := by
  intro h hX
  have hc := Morse.Homotopy.compresses_union_cell hA hcont hinj hbdry hn hι hιinj
  let k : C(P, ↥(A ∪ χ '' closedBall 0 1)) := ⟨fun p => ⟨h p, hX p⟩, by fun_prop⟩
  obtain ⟨g, hg, ⟨F⟩⟩ := hc k
  let v : C(↥(A ∪ χ '' closedBall 0 1), T) := ⟨Subtype.val, continuous_subtype_val⟩
  refine ⟨v.comp g, fun p => ?_, ⟨?_⟩⟩
  · obtain ⟨a, ha⟩ := hg p
    change (g p : T) ∈ A
    rw [← ha]
    exact a.2
  · have hS : h ⁻¹' A = k ⁻¹' range (⟨inclusion subset_union_left,
        continuous_inclusion subset_union_left⟩ : C(A, ↥(A ∪ χ '' closedBall 0 1))) := by
      ext p
      simp only [mem_preimage, mem_range]
      constructor
      · intro hp
        exact ⟨⟨h p, hp⟩, rfl⟩
      · rintro ⟨a, ha⟩
        have : (k p : T) = a := (congrArg Subtype.val ha).symm
        change (k p : T) ∈ A
        rw [this]
        exact a.2
    rw [hS]
    exact (F.compContinuousMap v).cast (ContinuousMap.ext fun p => rfl) rfl

/-- **Pushing off finitely many disjoint cells** (T5, applied cell by cell). -/
theorem pushesInto_union_cells {κ : Type*} {n : κ → ℕ}
    {χ : (i : κ) → EuclideanSpace ℝ (Fin (n i)) → T} {A : Set T} (hA : IsClosed A)
    (hcont : ∀ i, ContinuousOn (χ i) (closedBall 0 1)) (hinj : ∀ i, InjOn (χ i) (closedBall 0 1))
    (hbdry : ∀ i, ∀ z ∈ closedBall (0 : EuclideanSpace ℝ (Fin (n i))) 1, χ i z ∈ A ↔ ‖z‖ = 1)
    (hdisj : Pairwise fun i j => Disjoint (χ i '' closedBall 0 1) (χ j '' closedBall 0 1))
    (hn : ∀ i, finrank ℝ E < n i) (l : List κ) (hl : l.Nodup) :
    PushesInto P A (A ∪ ⋃ i ∈ l, χ i '' closedBall 0 1) := by
  induction l with
  | nil => simpa using pushesInto_self (P := P) A
  | cons c l ih =>
    rw [List.nodup_cons] at hl
    have hcl : IsClosed (A ∪ ⋃ i ∈ l, χ i '' closedBall 0 1) := by
      refine hA.union ?_
      have : (⋃ i ∈ l, χ i '' closedBall (0 : EuclideanSpace ℝ (Fin (n i))) 1) =
          ⋃ i ∈ {i | i ∈ l}, χ i '' closedBall 0 1 := rfl
      rw [this]
      exact (List.finite_toSet l).isClosed_biUnion fun i _ =>
        ((isCompact_closedBall 0 1).image_of_continuousOn (hcont i)).isClosed
    have hstep := pushesInto_union_cell hι hιinj hcl (hcont c) (hinj c) (fun z hz => by
      rw [mem_union, ← hbdry c z hz, or_iff_left_iff_imp]
      intro hz'
      obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.1 hz'
      have hic : c ≠ i := fun h => hl.1 (h ▸ hi)
      exact absurd hzi (Set.disjoint_left.1 (hdisj hic) (mem_image_of_mem _ hz)))
      (hn c)
    have heq : A ∪ ⋃ i ∈ c :: l, χ i '' closedBall 0 1 =
        (A ∪ ⋃ i ∈ l, χ i '' closedBall 0 1) ∪ χ c '' closedBall 0 1 := by
      ext x
      simp only [List.mem_cons, iUnion_iUnion_eq_or_left, mem_union, mem_iUnion]
      constructor
      · rintro (h | h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
        · exact Or.inl (Or.inr h)
      · rintro ((h | h) | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inl h)
    rw [heq]
    exact (ih hl.2).trans subset_union_left hstep

end Cells

/-! ### Lemma D: passing critical levels of high index -/

section LemmaD

universe u

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set V}

/-- A finite set of reals has a gap around each point. -/
theorem exists_gap_of_finite {s : Set ℝ} (hs : s.Finite) (c : ℝ) :
    ∃ η > 0, ∀ v ∈ s, |v - c| < η → v = c := by
  have hcl : IsClosed (s \ {c}) := (hs.sdiff (t := {c})).isClosed
  have hc : c ∈ (s \ {c})ᶜ := fun h => h.2 rfl
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hcl.isOpen_compl c hc
  refine ⟨η, hη, fun v hv hvc => ?_⟩
  by_contra hne
  have : v ∈ ball c η := by rwa [mem_ball, Real.dist_eq]
  exact hball this ⟨hv, hne⟩

/-- **Lemma D** (Exposition/Chapter13.md, §3): let `N ⊆ V` be a slice submanifold, `F : V → ℝ`
smooth, `f = F|N`, with `N^{a₀} = f⁻¹(−∞, a₀]` compact; let `a` be a regular value of `f`, and
suppose every critical point `q` of `f` with `a < f(q) ≤ a₀` is non-degenerate of index `≥ λ₀`.
Then for `a ≤ b < a₀`, every map from a compact `P` (embedded in a real vector space of
dimension `< λ₀`) into `N^b` is homotopic in `N`, relative to the preimage of `N^a`, to a map
into `N^a`. -/
theorem lemma_D (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {F : V → ℝ}
    (hF : ContDiff ℝ ∞ F) {a a₀ : ℝ} (hK : IsCompact ((F ∘ Subtype.val : N → ℝ) ⁻¹' Iic a₀))
    {l₀ : ℕ}
    (ha : letI := hN.chartedSpace;
      ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q → F q ≠ a)
    (hcrit : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      a < F q → F q ≤ a₀ →
        IsNondegenerate (hessianM Z (F ∘ Subtype.val) q) ∧ l₀ ≤ indexM Z (F ∘ Subtype.val) q)
    {P : Type*} [TopologicalSpace P] [CompactSpace P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hE : finrank ℝ E < l₀) {ι : P → E} (hι : Continuous ι) (hιinj : Injective ι)
    {b : ℝ} (hab : a ≤ b) (hb : b < a₀) :
    PushesInto P (sublevel (F ∘ Subtype.val : N → ℝ) a) (sublevel (F ∘ Subtype.val) b) := by
  classical
  let _ := hN.chartedSpace
  have := hN.isManifold
  set f : N → ℝ := F ∘ Subtype.val with hf_def
  have hfc : Continuous f := hF.continuous.comp continuous_subtype_val
  have hfs : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) ∞ f := contMDiff_comp_val hN hF
  have hslab : ∀ b b' : ℝ, b' ≤ a₀ → IsCompact (f ⁻¹' Icc b b') := fun b b' hb' =>
    hK.of_isClosed_subset (isClosed_Icc.preimage hfc) fun q hq => (hq.2.trans hb' : f q ≤ a₀)
  -- the critical points in `f⁻¹[a, a₀]` are finitely many
  set K' := f ⁻¹' Icc a a₀ with hK'_def
  have hfin : (K' ∩ {q | IsCriticalPointM Z f q}).Finite := by
    have hC : IsCompact (K' ∩ {x | IsCriticalPointM Z f x}) :=
      (hslab a a₀ le_rfl).inter_right
        (isClosed_setOf_isCriticalPointM (hfs.of_le (by norm_cast)))
    have hD : IsDiscrete (K' ∩ {x | IsCriticalPointM Z f x}) :=
      isDiscrete_inter_setOf_isCriticalPointM (fun x _ => (hfs x).of_le (by norm_cast))
        fun x hx hc => (hcrit x hc (lt_of_le_of_ne hx.1 (ha x hc).symm) hx.2).1
    exact hC.finite hD
  set C := hfin.toFinset with hC_def
  have hmemC : ∀ q, q ∈ C ↔ (a ≤ f q ∧ f q ≤ a₀) ∧ IsCriticalPointM Z f q := fun q => by
    simp only [C, Set.Finite.mem_toFinset, mem_inter_iff, K', mem_preimage, mem_Icc,
      mem_ofPred_eq]
  have hvals : (f '' (K' ∩ {q | IsCriticalPointM Z f q})).Finite := hfin.image f
  suffices key : ∀ m : ℕ, ∀ b : ℝ, a ≤ b → b < a₀ → (C.filter (fun q : N => f q ≤ b)).card = m →
      PushesInto P (sublevel f a) (sublevel f b) from key _ b hab hb rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro b hab hb hm
  have hfilter : ∀ q, IsCriticalPointM Z f q → a ≤ f q → f q ≤ b →
      q ∈ C.filter (fun q : N => f q ≤ b) := fun q hq h1 h2 =>
    Finset.mem_filter.2 ⟨(hmemC q).2 ⟨⟨h1, h2.trans hb.le⟩, hq⟩, h2⟩
  by_cases hS : (C.filter (fun q : N => f q ≤ b)).Nonempty
  · obtain ⟨p, hpS, hpmax⟩ := Finset.exists_max_image _ (fun q : N => f q) hS
    set c := f p with hc_def
    have hpC := (hmemC p).1 (Finset.mem_filter.1 hpS).1
    have hcb : c ≤ b := (Finset.mem_filter.1 hpS).2
    have hac : a < c := lt_of_le_of_ne hpC.1.1 (ha p hpC.2).symm
    have hca₀ : c < a₀ := lt_of_le_of_lt hcb hb
    obtain ⟨η, hη, hgap⟩ := exists_gap_of_finite hvals c
    set ε₀ := min (η / 2) (min ((c - a) / 2) ((a₀ - c) / 2)) with hε₀_def
    have hε₀ : 0 < ε₀ := lt_min (half_pos hη) (lt_min (by linarith) (by linarith))
    have hε₀η : ε₀ < η := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hη)
    have hε₀a : ε₀ ≤ (c - a) / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hε₀a₀ : ε₀ ≤ (a₀ - c) / 2 := (min_le_right _ _).trans (min_le_right _ _)
    set S := C.filter (fun q : N => f q = c) with hS_def
    have hSc : ∀ q ∈ S, IsNondegenerateCriticalPointM Z f q ∧ F q = c := fun q hq => by
      have hqC := (hmemC q).1 (Finset.mem_filter.1 hq).1
      have hqc : f q = c := (Finset.mem_filter.1 hq).2
      exact ⟨⟨hqC.2, (hcrit q hqC.2 (by rw [show F q = f q from rfl, hqc]; exact hac)
        hqC.1.2).1⟩, hqc⟩
    have honly : ∀ q : N, F q ∈ Icc (c - ε₀) (c + ε₀) → IsCriticalPointM Z f q → q ∈ S := by
      intro q hq hcq
      have hqK : q ∈ K' ∩ {q | IsCriticalPointM Z f q} :=
        ⟨⟨by linarith [hq.1, show F q = f q from rfl],
          by linarith [hq.2, show F q = f q from rfl]⟩, hcq⟩
      have hqc : f q = c := hgap _ ⟨q, hqK, rfl⟩ (by
        rw [abs_lt]; constructor <;> linarith [hq.1, hq.2, show F q = f q from rfl])
      exact Finset.mem_filter.2 ⟨(hmemC q).2 ⟨⟨hqK.1.1, hqK.1.2⟩, hcq⟩, hqc⟩
    obtain ⟨ε₁, hε₁, H⟩ := remark_3_3_submanifold hN hF S hSc hε₀
      (hslab _ _ (by linarith)) honly
    set ε := min ε₁ (ε₀ / 2) with hε_def
    have hε : 0 < ε := lt_min hε₁ (half_pos hε₀)
    have hεε₀ : ε < ε₀ := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hε₀)
    obtain ⟨χ, hprops, hdisj, hsdr⟩ := H ε hε (min_le_left _ _)
    -- (i) from `N^b` down to `N^{c+ε}`
    have h1 : PushesInto P (sublevel f (c + ε)) (sublevel f b) := by
      by_cases hbε : b ≤ c + ε
      · exact (pushesInto_self _).mono (sublevel_mono f hbε)
      · push Not at hbε
        have hno : ∀ q : N, F q ∈ Icc (c + ε) b → ¬IsCriticalPointM Z f q := by
          intro q hq hcq
          have := hpmax q (hfilter q hcq (by linarith [hq.1, show F q = f q from rfl])
            hq.2)
          linarith [hq.1, show F q = f q from rfl]
        exact pushesInto_of_isStrongDeformationRetract (sublevel_mono f hbε.le)
          (theorem_3_1_submanifold hN hF hbε.le (hslab _ _ hb.le) hno).2.1
    -- (ii) `N^{c+ε}` retracts onto `N^{c-ε}` with cells attached
    set X₁ := sublevel f (c - ε) ∪ ⋃ q, χ q '' closedBall 0 1 with hX₁_def
    have hX₁ : X₁ ⊆ sublevel f (c + ε) :=
      union_subset (sublevel_mono f (by linarith)) (iUnion_subset fun q => (hprops q).2.2.2)
    have h2 : PushesInto P X₁ (sublevel f (c + ε)) :=
      pushesInto_of_isStrongDeformationRetract hX₁ hsdr
    -- (iii) pushing off the cells
    have h3 : PushesInto P (sublevel f (c - ε)) X₁ := by
      have := pushesInto_union_cells hι hιinj (isClosed_le hfc continuous_const)
        (fun q => (hprops q).1) (fun q => (hprops q).2.1) (fun q => (hprops q).2.2.1) hdisj
        (fun q => hE.trans_le (hcrit q.1 (hSc q.1 q.2).1.1
          (by rw [(hSc q.1 q.2).2]; exact hac) (by rw [(hSc q.1 q.2).2]; exact hca₀.le)).2)
        (Finset.univ : Finset S).toList (Finset.nodup_toList _)
      refine this.mono (union_subset_union_right _ (iUnion_subset fun q => ?_))
      exact subset_biUnion_of_mem (u := fun q => χ q '' closedBall 0 1)
        (Finset.mem_toList.2 (Finset.mem_univ q))
    -- (iv) the induction hypothesis below `c`
    have h4 : PushesInto P (sublevel f a) (sublevel f (c - ε)) := by
      refine ih _ ?_ (c - ε) (by linarith) (by linarith) rfl
      rw [← hm]
      refine Finset.card_lt_card ⟨fun q hq => ?_, fun hsub => ?_⟩
      · have hq' := Finset.mem_filter.1 hq
        exact Finset.mem_filter.2 ⟨hq'.1, by linarith [hq'.2]⟩
      · have := (Finset.mem_filter.1 (hsub hpS)).2
        linarith
    exact ((h4.trans (sublevel_mono f (by linarith)) h3).trans
      ((sublevel_mono f (by linarith)).trans subset_union_left) h2).trans
      (sublevel_mono f (by linarith)) h1
  · -- no critical point in `[a, b]`: Theorem 3.1
    have hno : ∀ q : N, F q ∈ Icc a b → ¬IsCriticalPointM Z f q := fun q hq hcq =>
      hS ⟨q, hfilter q hcq hq.1 hq.2⟩
    exact pushesInto_of_isStrongDeformationRetract (sublevel_mono f hab)
      (theorem_3_1_submanifold hN hF hab (hslab _ _ hb.le) hno).2.1

end LemmaD

end Morse
