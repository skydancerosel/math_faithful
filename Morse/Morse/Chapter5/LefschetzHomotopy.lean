import Morse.Chapter5.ProjectiveSection
import Morse.Chapter13.ManifoldOfMinima

/-!
Milnor, *Morse Theory*, §7, Theorem 7.4 (p. 42); Exposition/Chapter5.md, §5 (Lemmas 5.1, 5.2 and
Step 4 of the proof of Theorem 7.4).

# Theorem 7.4 (Lefschetz): `π_r(V, V ∩ P) = 0` for `r < k`

## Milnor's text, paraphrased

(p. 42) **Theorem 7.4.**  Under the hypotheses of Corollary 7.3, `π_r(V, V ∩ P) = 0` for `r < k`,
provided a neighbourhood `U` of `V ∩ P` can be deformed into `V ∩ P` within `V` (Hypothesis (N)).
*Proof:* `f = 1/L_p` on `V`, `0` on `V ∩ P`, has only non-degenerate critical points of index
`≥ k` outside `V ∩ P`; so `V` is obtained from a neighbourhood `V^ε ⊆ U` of `V ∩ P` by attaching
cells of dimension `≥ k`, and maps of `r`-cubes, `r < k`, can be pushed off them into `U`, then
into `V ∩ P`.

## What is formalized

The abstract pair of `Morse/Chapter5/HyperplaneSection.lean`: `X` compact, `A ⊆ X` closed,
`e : M ≃ₜ X ∖ A` with `M` a closed complex submanifold of `ℂⁿ` of complex dimension `k`,
`‖e⁻¹ y‖ → ∞` as `y → A`, and Hypothesis (N).

* `Morse.lemma_D_slab`: `Morse.lemma_D` (pushing maps down past critical levels of index `≥ λ₀`,
  Lemmas 5.1 and 5.2 of the exposition) when only the slab `f⁻¹[a, a₀]` is compact.
* `Morse.pushesInto_univ_of_isClosed`: **localizing a push**: if every map into a closed `C`
  (from a closed piece of `P`) can be pushed into `Y ⊇ closure Cᶜ`, relative to the part already
  in `Y`, then every map from `P` can.
* `Morse.sectionFun`: Milnor's function `1/(1 + L_p)` on `X` (`0` on `A`), continuous
  (`Morse.continuous_sectionFun`).
* **`Morse.theorem_7_4_of_section`**: for every compact `P` embedded in a real vector space of
  dimension `< k` (e.g. the cube `Iʳ`, `r < k`), every map `P → X` is homotopic, relative to the
  preimage of `A`, to a map into `A` (`Morse.PushesInto P A univ`).  For `P = Iʳ` and maps of
  triples `(Iʳ, ∂Iʳ, J^{r−1}) → (X, A, x₀)` this is the compression criterion for
  `π_r(X, A, x₀) = 0` (Hatcher, §4.1), for every base point.
* `Morse.bijective_homotopyGroupMap_val_of_pushesInto`: compression of cubes and cylinders into
  `A` makes `π_i(A, a) → π_i(X, a)` bijective.
* **`Morse.theorem_7_4`** (cubes `Iʳ`, `r < k`), `Morse.theorem_7_4_of_embedding`: the same for
  `V ⊆ ℂPⁿ` closed with `V − P` a complex submanifold of complex dimension `k`, as in
  `Morse.corollary_7_3`; `Morse.theorem_7_4_bijective`, `Morse.theorem_7_4_surjective`: the
  exact-sequence consequence, **`π_i(V ∩ P, x) → π_i(V, x)` is bijective for `i < k − 1` and onto
  for `i = k − 1`**, at every `x ∈ V ∩ P` (proved directly from the compression).

## Deviations from Milnor, and what he leaves implicit

* The hypotheses of `Morse.corollary_7_3` (pure dimension; "algebraic variety with singular points
  in `P`" replaced by what the proof uses; Hypothesis (N), with `A` fixed during the deformation).
* `π_r(V, V ∩ P)` (not in Mathlib) is expressed through its standard compression criterion, in the
  strong form "relative to the preimage of `A`"; `r = 0` is included (every point is joined to `A`).
* Milnor's `f = 1/L_p` is `1/(1 + L_p)` (finite at `p`), and Morse theory is done for `−L_p` on
  `X ∖ A ≅ M`: the deformations of `M` that push maps down are stationary near `A`, and are glued
  with the identity there (`Morse.pushesInto_univ_of_isClosed`), which is the exposition's
  Lemma 5.1 ("extended by the identity on `V − K`").
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold unitInterval

noncomputable section

namespace Morse

open Morse.Homotopy (homotopyRelOfFun)

/-! ### Lemma D for a compact slab -/

section LemmaDSlab

universe u

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set V}

/-- **Lemma D for a compact slab** (`Morse.lemma_D` with only `f⁻¹[a, a₀]` compact; the proof
is the same, all slabs used lie in `[a, a₀]`): let `N ⊆ V` be a slice submanifold, `F : V → ℝ`
smooth, `f = F|N`, with the slab `f⁻¹[a, a₀]` compact; let `a` be a regular value of `f`, and
suppose every critical point `q` of `f` with `a < f(q) ≤ a₀` is non-degenerate of index `≥ λ₀`.
Then for `a ≤ b < a₀`, every map from a compact `P` (embedded in a real vector space of
dimension `< λ₀`) into `N^b` is homotopic in `N`, relative to the preimage of `N^a`, to a map
into `N^a`. -/
theorem lemma_D_slab (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {F : V → ℝ}
    (hF : ContDiff ℝ ∞ F) {a a₀ : ℝ} (hK : IsCompact ((F ∘ Subtype.val : N → ℝ) ⁻¹' Icc a a₀))
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
  have hslab : ∀ b b' : ℝ, a ≤ b → b' ≤ a₀ → IsCompact (f ⁻¹' Icc b b') := fun b b' hb hb' =>
    hK.of_isClosed_subset (isClosed_Icc.preimage hfc) fun q hq =>
      ⟨hb.trans hq.1, (hq.2.trans hb' : f q ≤ a₀)⟩
  -- the critical points in `f⁻¹[a, a₀]` are finitely many
  set K' := f ⁻¹' Icc a a₀ with hK'_def
  have hfin : (K' ∩ {q | IsCriticalPointM Z f q}).Finite := by
    have hC : IsCompact (K' ∩ {x | IsCriticalPointM Z f x}) :=
      (hslab a a₀ le_rfl le_rfl).inter_right
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
      (hslab _ _ (by linarith) (by linarith)) honly
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
          (theorem_3_1_submanifold hN hF hbε.le (hslab _ _ (by linarith) hb.le) hno).2.1
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
      (theorem_3_1_submanifold hN hF hab (hslab _ _ le_rfl hb.le) hno).2.1

end LemmaDSlab

/-! ### Localizing a push -/

/-- **Localizing a push.**  Let `C ⊆ T` be closed and `Y ⊇ closure Cᶜ`.  If, for every map
`h : P → T`, maps from `h⁻¹(C)` into `C` can be pushed into `Y` (relative to the part in `Y`),
then every map `P → T` is homotopic, relative to the preimage of `Y`, to a map into `Y`. -/
theorem pushesInto_univ_of_isClosed {P T : Type*} [TopologicalSpace P] [TopologicalSpace T]
    {Y C : Set T} (hC : IsClosed C) (hY : closure Cᶜ ⊆ Y)
    (hloc : ∀ h : C(P, T), PushesInto (h ⁻¹' C) Y C) : PushesInto P Y univ := by
  classical
  intro h _
  obtain ⟨g, hgY, ⟨F⟩⟩ := hloc h ⟨fun p => h p.1, by fun_prop⟩ fun p => p.2
  let G : I × P → T := fun z => if hz : h z.2 ∈ C then F (z.1, ⟨z.2, hz⟩) else h z.2
  have hstat : ∀ (t : I) (p : P) (hp : h p ∈ C), h p ∈ Y → F (t, ⟨p, hp⟩) = h p :=
    fun t p hp hY' => F.eq_fst t (show h p ∈ Y from hY')
  have hCc : Cᶜ ⊆ Y := subset_closure.trans hY
  have hG1 : ContinuousOn G {z | h z.2 ∈ C} := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : {z : I × P | h z.2 ∈ C}.domRestrict G = fun z => F (z.1.1, ⟨z.1.2, z.2⟩) :=
      funext fun z => dif_pos z.2
    rw [this]
    fun_prop
  have hG2 : ContinuousOn G {z : I × P | h z.2 ∈ closure Cᶜ} := by
    refine (h.continuous.comp continuous_snd).continuousOn.congr fun z hz => ?_
    change G z = h z.2
    by_cases hzC : h z.2 ∈ C
    · simp only [G, dif_pos hzC]
      exact hstat _ _ hzC (hY hz)
    · simp only [G, dif_neg hzC]
  have hG : Continuous G := by
    rw [← continuousOn_univ]
    have hcov : (univ : Set (I × P)) = {z | h z.2 ∈ C} ∪ {z | h z.2 ∈ closure Cᶜ} := by
      refine (eq_univ_of_forall fun z => ?_).symm
      by_cases hz : h z.2 ∈ C
      · exact Or.inl hz
      · exact Or.inr (subset_closure hz)
    rw [hcov]
    exact hG1.union_of_isClosed hG2 (hC.preimage (h.continuous.comp continuous_snd))
      (isClosed_closure.preimage (h.continuous.comp continuous_snd))
  let Gc : C(I × P, T) := ⟨G, hG⟩
  refine ⟨⟨fun p => G (1, p), by fun_prop⟩, fun p => ?_, ⟨homotopyRelOfFun Gc (fun p => ?_)
    (fun p => rfl) fun t p hp => ?_⟩⟩
  · change G (1, p) ∈ Y
    by_cases hp : h p ∈ C
    · simp only [G, dif_pos hp]
      rw [F.apply_one]
      exact hgY _
    · simp only [G, dif_neg hp]
      exact hCc hp
  · change G (0, p) = h p
    by_cases hp : h p ∈ C
    · simp only [G, dif_pos hp]
      rw [F.apply_zero]
      rfl
    · simp only [G, dif_neg hp]
  · change G (t, p) = h p
    by_cases hpC : h p ∈ C
    · simp only [G, dif_pos hpC]
      exact hstat _ _ hpC hp
    · simp only [G, dif_neg hpC]

/-! ### Milnor's function `1/(1 + L_p)` -/

local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)

section Section

variable {n : ℕ} {M : Set (𝔼 n)} {X : Type*} [TopologicalSpace X] {A : Set X}

open Classical in
/-- **Milnor's function** `f = 1/(1 + L_p)` on `X ∖ A ≅ M`, `0` on `A`. -/
def sectionFun (e : M ≃ₜ (Aᶜ : Set X)) (p : 𝔼 n) (x : X) : ℝ :=
  if hx : x ∈ Aᶜ then (1 + ‖((e.symm ⟨x, hx⟩ : M) : 𝔼 n) - p‖ ^ 2)⁻¹ else 0

theorem sectionFun_of_mem (e : M ≃ₜ (Aᶜ : Set X)) (p : 𝔼 n) {x : X} (hx : x ∈ A) :
    sectionFun e p x = 0 :=
  dif_neg fun h => h hx

theorem sectionFun_apply (e : M ≃ₜ (Aᶜ : Set X)) (p : 𝔼 n) (y : M) :
    sectionFun e p (e y : X) = (1 + ‖(y : 𝔼 n) - p‖ ^ 2)⁻¹ := by
  rw [sectionFun, dif_pos (e y).2]
  simp

theorem sectionFun_nonneg (e : M ≃ₜ (Aᶜ : Set X)) (p : 𝔼 n) (x : X) : 0 ≤ sectionFun e p x := by
  unfold sectionFun
  split_ifs
  · positivity
  · exact le_rfl

/-- **`f` is continuous**: smooth on `X ∖ A`, and `→ 0` at `A` since `L_p → ∞` there. -/
theorem continuous_sectionFun (hA : IsClosed A) (e : M ≃ₜ (Aᶜ : Set X))
    (hinf : ∀ x ∈ A, ∀ R : ℝ, ∀ᶠ y in 𝓝 x, ∀ hy : y ∈ Aᶜ, R ≤ ‖((e.symm ⟨y, hy⟩ : M) : 𝔼 n)‖)
    (p : 𝔼 n) : Continuous (sectionFun e p) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ A
  · rw [ContinuousAt, sectionFun_of_mem e p hx, Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hinf x hx (Real.sqrt ε⁻¹ + ‖p‖)] with y hy
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (sectionFun_nonneg e p y)]
    by_cases hyA : y ∈ Aᶜ
    · rw [sectionFun, dif_pos hyA]
      set z : 𝔼 n := ((e.symm ⟨y, hyA⟩ : M) : 𝔼 n)
      have h1 := hy hyA
      have h2 : Real.sqrt ε⁻¹ ≤ ‖z - p‖ := by
        have := norm_sub_norm_le z p
        linarith
      have h3 : ε⁻¹ ≤ ‖z - p‖ ^ 2 := by
        calc ε⁻¹ = Real.sqrt ε⁻¹ ^ 2 := (Real.sq_sqrt (inv_nonneg.2 hε.le)).symm
          _ ≤ ‖z - p‖ ^ 2 := by gcongr
      rw [inv_lt_comm₀ (by positivity) hε]
      linarith
    · rw [sectionFun, dif_neg hyA]
      exact hε
  · have hon : ContinuousOn (sectionFun e p) Aᶜ := by
      rw [continuousOn_iff_continuous_domRestrict]
      have : Aᶜ.domRestrict (sectionFun e p) =
          fun y => (1 + ‖((e.symm y : M) : 𝔼 n) - p‖ ^ 2)⁻¹ :=
        funext fun y => dif_pos y.2
      rw [this]
      refine Continuous.inv₀ (by fun_prop) fun y => by positivity
    exact hon.continuousAt (hA.isOpen_compl.mem_nhds hx)

end Section

/-! ### Theorem 7.4 for the abstract pair -/

section Main

open Homology

variable {n k w : ℕ} {M : Set (𝔼 n)}
  (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, 𝔼 n) (𝔼 (2 * k)) (𝔼 w) M)

/-- **Theorem 7.4 (Lefschetz), abstract form** (Milnor p. 42): let `X` be compact, `A ⊆ X`
closed, and `X ∖ A` homeomorphic (by `e`) to a closed complex submanifold `M` of `ℂⁿ` of complex
dimension `k`, with `‖e⁻¹ y‖ → ∞` as `y → A`; assume Hypothesis (N).  Then for every compact `P`
embedded in a real vector space of dimension `< k` (e.g. `Iʳ`, `r < k`), every map `P → X` is
homotopic, relative to the preimage of `A`, to a map into `A`: "`π_r(X, A) = 0` for `r < k`". -/
theorem theorem_7_4_of_section {X : Type*} [TopologicalSpace X] [CompactSpace X] {A : Set X}
    (hA : IsClosed A) (hcl : IsClosed M)
    {J : 𝔼 n →L[ℝ] 𝔼 n} (hJ : IsOrthComplexStructure J) (hc : IsComplexSubmanifold hM J)
    (e : M ≃ₜ (Aᶜ : Set X))
    (hinf : ∀ x ∈ A, ∀ R : ℝ, ∀ᶠ y in 𝓝 x, ∀ hy : y ∈ Aᶜ, R ≤ ‖((e.symm ⟨y, hy⟩ : M) : 𝔼 n)‖)
    (hN : HypothesisN A) {P : Type*} [TopologicalSpace P] [CompactSpace P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hE : finrank ℝ E < k) {ι : P → E} (hι : Continuous ι) (hιinj : Injective ι) :
    PushesInto P A univ := by
  classical
  let _ := hM.chartedSpace
  have := hM.isManifold
  obtain ⟨U, hUo, hAU, H, hH0, hH1, hHA⟩ := hN
  obtain ⟨p, hp⟩ := exists_isMorseFunction_normSq_sub (hM := hM)
  set L : 𝔼 n → ℝ := fun y => ‖y - p‖ ^ 2 with hL_def
  have hL : ContDiff ℝ ∞ L := contDiff_normSq_sub p
  set G : 𝔼 n → ℝ := fun y => -L y with hG_def
  have hG : ContDiff ℝ ∞ G := hL.neg
  have hψ : Continuous (sectionFun e p) := continuous_sectionFun hA e hinf p
  have hψA : ∀ x (hx : x ∈ Aᶜ), sectionFun e p x = (1 + L (e.symm ⟨x, hx⟩))⁻¹ :=
    fun x hx => dif_pos hx
  -- a bound for `L ∘ e⁻¹` on the compact set `X ∖ U`
  set φ : (Aᶜ : Set X) → ℝ := fun y => L (e.symm y) with hφ_def
  have hφ : Continuous φ := hL.continuous.comp (continuous_subtype_val.comp e.symm.continuous)
  have hKU : IsCompact ((Subtype.val : (Aᶜ : Set X) → X) ⁻¹' Uᶜ) := by
    refine (Topology.IsInducing.subtypeVal.isCompact_preimage_iff ?_).2
      hUo.isClosed_compl.isCompact
    intro x hx
    exact ⟨⟨x, fun hxA => hx (hAU hxA)⟩, rfl⟩
  obtain ⟨B, hB⟩ := hKU.bddAbove_image hφ.continuousOn
  -- a regular value `R > B` of `L`
  have hK : ∀ a, IsCompact ((L ∘ Subtype.val : M → ℝ) ⁻¹' Set.Iic a) :=
    fun a => isCompact_sublevel_normSq_sub hcl p a
  obtain ⟨a, -, -, ha', hreg⟩ := exists_regular_levels hM hL hK hp.isNondegenerate
    fun _ => sq_nonneg _
  obtain ⟨m, hm⟩ := (ha'.eventually_ge_atTop (max B 0 + 1)).exists
  set R := a m with hR_def
  have hRB : B < R := by have := le_max_left B 0; linarith
  have hR0 : 0 < R := by have := le_max_right B 0; linarith
  -- `V_R = {f ≤ 1/(1 + R)}` lies in `U`; `C = {f ≥ 1/(2 + R)}`
  set VR : Set X := {x | sectionFun e p x ≤ (1 + R)⁻¹} with hVR_def
  set C : Set X := {x | (1 + (R + 1))⁻¹ ≤ sectionFun e p x} with hC_def
  have hAVR : A ⊆ VR := fun x hx => by
    change sectionFun e p x ≤ _
    rw [sectionFun_of_mem e p hx]
    positivity
  have hVRU : VR ⊆ U := by
    intro x hx
    by_contra hxU
    have hxA : x ∈ Aᶜ := fun h => hxU (hAU h)
    have h1 : φ ⟨x, hxA⟩ ≤ B := hB ⟨⟨x, hxA⟩, hxU, rfl⟩
    have h2 : (1 + L (e.symm ⟨x, hxA⟩))⁻¹ ≤ (1 + R)⁻¹ := (hψA x hxA).symm.trans_le hx
    have h3 := (inv_le_inv₀ (by positivity) (by positivity)).1 h2
    change L (e.symm ⟨x, hxA⟩) ≤ B at h1
    linarith
  have hCcl : IsClosed C := isClosed_le continuous_const hψ
  have hclY : closure Cᶜ ⊆ VR := by
    have hCc : Cᶜ = {x | sectionFun e p x < (1 + (R + 1))⁻¹} := by
      ext x; simp [hC_def, not_le]
    rw [hCc]
    refine (closure_lt_subset_le hψ continuous_const).trans fun x hx => ?_
    change sectionFun e p x ≤ (1 + R)⁻¹
    exact hx.trans (inv_anti₀ (by positivity) (by linarith))
  -- Morse theory for `−L` on the compact slab `{L ≤ R}`
  have hKG : IsCompact ((G ∘ Subtype.val : M → ℝ) ⁻¹' Set.Icc (-R) 1) :=
    (hK R).of_isClosed_subset (isClosed_Icc.preimage (hG.continuous.comp
      continuous_subtype_val)) fun y hy => by
        have := hy.1
        simp only [Function.comp_apply, hG_def] at this
        change L y ≤ R
        linarith
  have hcritG : ∀ q : M, IsCriticalPointM (𝔼 (2 * k)) (G ∘ Subtype.val) q ↔
      IsCriticalPointM (𝔼 (2 * k)) (L ∘ Subtype.val) q :=
    fun q => isCriticalPointM_neg_iff (L ∘ Subtype.val : M → ℝ) q
  have hareg : ∀ q : M, IsCriticalPointM (𝔼 (2 * k)) (G ∘ Subtype.val) q → G q ≠ -R :=
    fun q hq h => hreg m q ((hcritG q).1 hq) (by
      have : -L q = -R := h
      change L q = R
      linarith)
  have hcrit : ∀ q : M, IsCriticalPointM (𝔼 (2 * k)) (G ∘ Subtype.val) q → -R < G q → G q ≤ 1 →
      IsNondegenerate (hessianM (𝔼 (2 * k)) (G ∘ Subtype.val) q) ∧
        k ≤ indexM (𝔼 (2 * k)) (G ∘ Subtype.val) q := by
    intro q hq _ _
    have hq' := (hcritG q).1 hq
    refine ⟨?_, le_indexM_neg_normSq_sub hM hJ hc p q hq' (hp.isNondegenerate q hq')⟩
    have := hessianM_neg (E := 𝔼 (2 * k)) (L ∘ Subtype.val : M → ℝ) q
    change IsNondegenerate (hessianM (𝔼 (2 * k)) (fun x => -(L ∘ Subtype.val) x) q)
    rw [this, isNondegenerate_neg_iff]
    exact hp.isNondegenerate q hq'
  -- pushing maps into `C` down into `V_R`
  have hloc : ∀ h : C(P, X), PushesInto (h ⁻¹' C) VR C := by
    intro h
    have : CompactSpace (h ⁻¹' C) :=
      isCompact_iff_compactSpace.1 (hCcl.preimage h.continuous).isCompact
    intro g hgC
    have hgA : ∀ q, g q ∈ Aᶜ := fun q hqA => by
      have h1 : (1 + (R + 1))⁻¹ ≤ sectionFun e p (g q) := hgC q
      rw [sectionFun_of_mem e p hqA] at h1
      have : (0 : ℝ) < (1 + (R + 1))⁻¹ := by positivity
      linarith
    let g₁ : C(h ⁻¹' C, M) :=
      ⟨fun q => e.symm ⟨g q, hgA q⟩, e.symm.continuous.comp (g.continuous.subtype_mk _)⟩
    have hD := lemma_D_slab hM hG (a := -R) (a₀ := 1) hKG (l₀ := k) hareg hcrit
      (P := h ⁻¹' C) hE (ι := ι ∘ Subtype.val) (hι.comp continuous_subtype_val)
      (hιinj.comp Subtype.val_injective) (b := 0) (by linarith) (by norm_num)
    obtain ⟨g₁', hg₁'S, ⟨F₁⟩⟩ := hD g₁ fun q => by
      change -‖((g₁ q : M) : 𝔼 n) - p‖ ^ 2 ≤ 0
      exact neg_nonpos.2 (sq_nonneg _)
    let ev : C(M, X) := ⟨fun y => (e y : X), continuous_subtype_val.comp e.continuous⟩
    refine ⟨ev.comp g₁', fun q => ?_, ⟨homotopyRelOfFun (ev.comp F₁.toContinuousMap)
      (fun q => ?_) (fun q => ?_) fun t q hq => ?_⟩⟩
    · change sectionFun e p (e (g₁' q) : X) ≤ (1 + R)⁻¹
      rw [sectionFun_apply]
      have : -‖((g₁' q : M) : 𝔼 n) - p‖ ^ 2 ≤ -R := hg₁'S q
      exact inv_anti₀ (by positivity) (by linarith)
    · change (e (F₁ (0, q)) : X) = g q
      rw [F₁.apply_zero]
      change (e (e.symm ⟨g q, hgA q⟩) : X) = g q
      rw [Homeomorph.apply_symm_apply]
    · change (e (F₁ (1, q)) : X) = (e (g₁' q) : X)
      rw [F₁.apply_one]
    · have hq' : q ∈ g₁ ⁻¹' sublevel (G ∘ Subtype.val : M → ℝ) (-R) := by
        have h2 : (1 + L (e.symm ⟨g q, hgA q⟩))⁻¹ ≤ (1 + R)⁻¹ :=
          (hψA (g q) (hgA q)).symm.trans_le hq
        have h3 := (inv_le_inv₀ (by positivity) (by positivity)).1 h2
        change -L (e.symm ⟨g q, hgA q⟩) ≤ -R
        linarith
      change (e (F₁ (t, q)) : X) = g q
      rw [F₁.eq_fst t hq']
      change (e (e.symm ⟨g q, hgA q⟩) : X) = g q
      rw [Homeomorph.apply_symm_apply]
  have h1 : PushesInto P VR univ := pushesInto_univ_of_isClosed hCcl hclY hloc
  have h2 : PushesInto P A VR := pushesInto_of_deformation (U := VR)
    ⟨fun q => H (q.1, ⟨q.2, hVRU q.2.2⟩), by fun_prop⟩ (fun u => hH0 _) (fun u => hH1 _)
    (fun t u hu => hHA t ⟨u, hVRU u.2⟩ hu)
  exact PushesInto.trans hAVR h2 h1

end Main

/-! ### Homotopy groups -/

/-- A push of all maps from `P` into `A` is a compression by the inclusion `A → X`. -/
theorem compresses_val_of_pushesInto {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    {A : Set X} (h : PushesInto P A univ) :
    Homotopy.Compresses (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)) P := by
  intro f
  obtain ⟨g, hg, hfg⟩ := h f fun _ => trivial
  refine ⟨g, fun p => ?_, ?_⟩
  · change g p ∈ range (Subtype.val : A → X)
    rw [Subtype.range_coe]
    exact hg p
  · change f.HomotopicRel g (f ⁻¹' range (Subtype.val : A → X))
    rw [Subtype.range_coe]
    exact hfg

/-- **The homotopy exact sequence, from compression**: if every map from `I^N` (resp.
`I × I^N`) into `X` can be pushed into `A`, the inclusion induces surjections (resp.
injections) `π_N(A, a) → π_N(X, a)`. -/
theorem bijective_homotopyGroupMap_val_of_pushesInto {X : Type*} [TopologicalSpace X] {A : Set X}
    {N : Type*} (h₁ : PushesInto (I^N) A univ) (h₂ : PushesInto (I × I^N) A univ) (a : A) :
    Bijective (Homotopy.homotopyGroupMap (N := N)
      (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)) a) :=
  ⟨Homotopy.injective_homotopyGroupMap_of_compresses Topology.IsEmbedding.subtypeVal
    (compresses_val_of_pushesInto h₂) a,
   Homotopy.surjective_homotopyGroupMap_of_compresses Topology.IsEmbedding.subtypeVal
    (compresses_val_of_pushesInto h₁) a⟩

/-! ### Theorem 7.4 for projective varieties -/

open CP Matrix
open scoped Morse.MatrixInner

section Projective

variable {n k w : ℕ} {V : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)}
  (hV : V ⊆ grassmannian (Fin (n + 1)) 1) (hVc : IsClosed V)
  (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n)))
      (EuclideanSpace ℝ (Fin (2 * k))) (EuclideanSpace ℝ (Fin w)) (affinePart V))
  (hc : IsComplexSubmanifold hM (cpxJ n)) (hN : HypothesisN (hyperplaneSection V))
include hV hVc hM hc hN

/-- **Theorem 7.4 (Lefschetz)** for compact `P` of dimension `< k`. -/
theorem theorem_7_4_of_embedding {P : Type*} [TopologicalSpace P] [CompactSpace P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hE : finrank ℝ E < k) {ι : P → E} (hι : Continuous ι) (hιinj : Injective ι) :
    PushesInto P (hyperplaneSection V) univ := by
  have : CompactSpace V := isCompact_iff_compactSpace.1 (CP.isCompact.of_isClosed_subset hVc hV)
  have hA : IsClosed (hyperplaneSection V) :=
    isClosed_eq ((contDiff_entry (𝕜 := ℂ) 0 0).continuous.comp continuous_subtype_val)
      continuous_const
  have hcl : IsClosed (affinePart V) :=
    hVc.preimage (continuous_proj.comp (theta n).symm.continuous)
  exact theorem_7_4_of_section hM hA hcl (isOrthComplexStructure_cpxJ n) hc
    (affineHomeomorph hV) (fun x hx R => tendsto_norm_affineHomeomorph_symm hV x hx R) hN hE hι
    hιinj

/-- **Theorem 7.4 (Lefschetz)** (Milnor p. 42): let `V ⊆ ℂPⁿ` be closed and `P` the hyperplane
`Z₀ = 0`, such that `V − P ⊆ ℂⁿ` is a complex submanifold of complex dimension `k` (`V` of pure
dimension `k`, singular points in `P`), and assume Hypothesis (N).  Then `π_r(V, V ∩ P) = 0` for
`r < k`: every map `Iʳ → V` is homotopic, relative to the preimage of `V ∩ P`, to a map into
`V ∩ P` (for maps of triples `(Iʳ, ∂Iʳ, J^{r−1}) → (V, V ∩ P, x₀)` this is the compression
criterion for the vanishing of `[g] ∈ π_r(V, V ∩ P, x₀)`). -/
theorem theorem_7_4 {r : ℕ} (hr : r < k) : PushesInto (I^(Fin r)) (hyperplaneSection V) univ :=
  theorem_7_4_of_embedding hV hVc hM hc hN (E := Fin r → ℝ)
    (by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]; exact hr)
    Homotopy.continuous_cubeEmb Homotopy.injective_cubeEmb

/-- **Theorem 7.4, the exact sequence** (Milnor p. 42, as in Corollary 7.3): the inclusion
`V ∩ P → V` induces bijections `π_i(V ∩ P, x) → π_i(V, x)` for `i < k − 1`, at every
`x ∈ V ∩ P`. -/
theorem theorem_7_4_bijective {i : ℕ} (hi : i + 1 < k) (x : hyperplaneSection V) :
    Bijective (Homotopy.homotopyGroupMap (N := Fin i)
      (⟨Subtype.val, continuous_subtype_val⟩ : C(hyperplaneSection V, V)) x) :=
  bijective_homotopyGroupMap_val_of_pushesInto
    (theorem_7_4_of_embedding hV hVc hM hc hN (E := Fin i → ℝ)
      (by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]; omega)
      Homotopy.continuous_cubeEmb Homotopy.injective_cubeEmb)
    (theorem_7_4_of_embedding hV hVc hM hc hN (E := ℝ × (Fin i → ℝ))
      (by rw [Module.finrank_prod, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
        Fintype.card_fin]; omega)
      Homotopy.continuous_cylEmb Homotopy.injective_cylEmb) x

/-- **Theorem 7.4, the exact sequence, top degree**: `π_{k−1}(V ∩ P, x) → π_{k−1}(V, x)` is
onto. -/
theorem theorem_7_4_surjective {i : ℕ} (hi : i < k) (x : hyperplaneSection V) :
    Surjective (Homotopy.homotopyGroupMap (N := Fin i)
      (⟨Subtype.val, continuous_subtype_val⟩ : C(hyperplaneSection V, V)) x) :=
  Homotopy.surjective_homotopyGroupMap_of_compresses Topology.IsEmbedding.subtypeVal
    (compresses_val_of_pushesInto (theorem_7_4 hV hVc hM hc hN hi)) x

end Projective

end Morse
