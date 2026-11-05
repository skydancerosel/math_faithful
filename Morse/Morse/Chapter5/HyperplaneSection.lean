import Morse.Chapter5.LefschetzSlab

/-!
Milnor, *Morse Theory*, §7, Corollary 7.3 and Theorem 7.4 (pp. 41–42); Exposition/Chapter5.md, §5
(the hidden hypotheses, Hypothesis (N), and "a proof of Corollary 7.3 without duality").

# Hyperplane sections: the homology vanishing behind Corollary 7.3

## Milnor's text, paraphrased

(p. 41) **Corollary 7.3 (Lefschetz).**  If `V ⊂ ℂPⁿ` is an algebraic variety of complex dimension
`k` and `P` a hyperplane containing the singular points of `V`, then `H_r(V ∩ P) → H_r(V)` is an
isomorphism for `r < k − 1` and onto for `r = k − 1`.  *Proof:* `H_r(V, V ∩ P) ≅ H^{2k−r}(V − P)` by
Lefschetz duality, and `V − P` is a closed complex submanifold of the affine space `ℂPⁿ − P`, so
its cohomology vanishes above `k` (Theorem 7.2).  (p. 42) **Theorem 7.4.**  `π_r(V, V ∩ P) = 0` for
`r < k`, assuming that a neighbourhood `U` of `V ∩ P` can be deformed into `V ∩ P` within `V`
(Hypothesis (N)); *proof:* the function `1/L_p` on `V`, which vanishes on `V ∩ P`, has only
critical points of index `≥ k` outside `V ∩ P`.

## What is formalized

The exposition's proof of Corollary 7.3 without duality, over a field `𝕜`, for an abstract pair:
`X` compact, `A ⊆ X` closed, `e : M ≃ₜ X ∖ A` with `M` a closed complex submanifold of
`ℂⁿ = (𝔼 n, J)` of real dimension `2k` (`Morse.IsComplexSubmanifold`; pure dimension is built into
the model space), with `‖e⁻¹ y‖ → ∞` as `y → A`, and Hypothesis (N) (`Morse.HypothesisN`).  The
projective case is `Morse/Chapter5/ProjectiveSection.lean`.

* `Morse.le_indexM_neg_normSq_sub`: at a non-degenerate critical point of `L_p` on `M`, the index
  of `−L_p` is `2k − index ≥ k` (`Morse.index_neg_add_index`: `index(−H) + index H = dim` for a
  non-degenerate symmetric form; Theorem 7.2's bound `index ≤ k`).
* `Morse.subsingleton_subsetHomology_univ_of_section`: **`H_r(X, A; 𝕜) = 0` for `r < k`.**
* `Morse.corollary_7_3_of_section`: **Corollary 7.3**: `H_r(A; 𝕜) → H_r(X; 𝕜)` is bijective for
  `r < k − 1` and surjective for `r = k − 1`.
* Tools: `Morse.Homology.subsingleton_subsetHomology_of_homeomorph` (a homeomorphism of pairs),
  `Morse.Homology.relHomology_map_eq_zero_of_deform` (a deformation of `B` into `A` fixing `A`
  kills `H_*(B, A) → H_*(C, A)`).

The proof (exposition, §5): choose `p` with `L_p` Morse on `M` (Theorem 6.6), `R` a regular value
of `L_p` so large that `V_R = A ∪ e{L_p ≥ R}` lies in the neighbourhood `U` of (N).  (1) Since
`V_R` deforms into `A` within `X` keeping `A` fixed, `H_r(V_R, A) → H_r(X, A)` is zero.  (2) By
excision of `A` (which lies in the interior of `V_R` because `L_p → ∞` at `A`) and the
homeomorphism `e`, `H_r(X, V_R) ≅ H_r(M, {L_p ≥ R})`, which vanishes for `r < k` by Morse theory
for `−L_p` on the compact slab `{L_p ≤ R}` (`Morse.subsingleton_subsetHomology_slab`): all its
critical points have index `≥ k`.  (3) The exact sequence of the triple `(X, V_R, A)`.

## Deviations from Milnor, and what he leaves implicit

* **Pure dimension** (exposition, §5): Milnor's "complex dimension `k`" must mean that every
  component of `V − P` has dimension `k`; here `M` is modelled on `𝔼 (2k)`.
* **No Lefschetz duality.**  Milnor's proof of 7.3 quotes a duality theorem whose hypotheses he
  does not state; the proof here uses the ingredients of his proof of 7.4 instead, as in the
  exposition.
* **Hypothesis (N)** is an explicit hypothesis, as in Milnor (who says it follows from the
  triangulability of algebraic varieties); the deformation must fix `A` pointwise
  (exposition, "A hidden hypothesis").
* **Homology over a field**, not over `ℤ`, as everywhere in the project.
* **Theorem 7.4** (relative homotopy groups) is in `Morse/Chapter5/LefschetzHomotopy.lean`.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold

noncomputable section

namespace Morse

section Neg

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- For a symmetric non-degenerate form, `index(−H) + index H = dim`. -/
theorem index_neg_add_index (H : E →L[ℝ] E →L[ℝ] ℝ) (hsymm : ∀ v w, H v w = H w v)
    (hnd : IsNondegenerate H) : index (-H) + index H = finrank ℝ E := by
  have hq : quadForm (-H) = -quadForm H := by ext v; simp
  rw [index, index, hq, _root_.sigNeg_neg,
    ← QuadraticForm.sigPos_add_sigNeg_add_radical (Q := quadForm H)]
  have hrad : (quadForm H).radical = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    obtain ⟨-, h2⟩ := hv
    refine (isNondegenerate_iff.1 hnd) v fun w => ?_
    have := congrArg (fun T => T w) h2
    simp only [QuadraticMap.polarBilin_apply_apply, LinearMap.zero_apply, QuadraticMap.polar,
      quadForm_apply, map_add, _root_.add_apply] at this
    rw [hsymm w v] at this
    linarith
  rw [hrad, finrank_bot, add_zero]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

omit [FiniteDimensional ℝ E] in
theorem hessianM_neg (f : M → ℝ) (p : M) :
    hessianM E (fun x => -f x) p = -hessianM E f p := by
  have h1 : localRep E (fun x => -f x) p = fun y => -localRep E f p y := rfl
  have h2 : fderiv ℝ (fun y => -localRep E f p y) = fun y => -fderiv ℝ (localRep E f p) y := by
    funext y; exact fderiv_neg
  rw [hessianM, hessianM, h1, hessian, hessian, h2]
  exact fderiv_neg

omit [FiniteDimensional ℝ E] in
theorem isCriticalPointM_neg_iff [IsManifold 𝓘(ℝ, E) ∞ M] (f : M → ℝ) (p : M) :
    IsCriticalPointM E (fun x => -f x) p ↔ IsCriticalPointM E f p := by
  rw [IsCriticalPointM, IsCriticalPointM]
  have : (fun x => -f x) = -f := rfl
  rw [this, mfderiv_neg]
  exact neg_eq_zero

end Neg


end Morse

namespace Morse.Homology

open CategoryTheory

universe u

variable {𝕜 : Type u} [Field 𝕜] {E E' : Type u} [TopologicalSpace E] [TopologicalSpace E']

/-- **A homeomorphism of pairs** `φ : B ≃ₜ B'` carrying `A` onto `A'`: if `H_i(B', A'; 𝕜) = 0` then
`H_i(B, A; 𝕜) = 0`. -/
theorem subsingleton_subsetHomology_of_homeomorph {A B : Set E} {A' B' : Set E'} (h : A ⊆ B)
    (h' : A' ⊆ B') (φ : B ≃ₜ B') (hφ : ∀ x : B, (x : E) ∈ A ↔ (φ x : E') ∈ A') (i : ℕ)
    (hs : Subsingleton (subsetHomology 𝕜 i h')) : Subsingleton (subsetHomology 𝕜 i h) := by
  let fA : C(A, A') := ⟨fun a => ⟨φ (Set.inclusion h a), (hφ _).1 a.2⟩,
    by fun_prop⟩
  let gA : C(A', A) := ⟨fun a => ⟨φ.symm (Set.inclusion h' a), (hφ _).2 (by simp [a.2])⟩,
    by fun_prop⟩
  let F : subsetPair h ⟶ subsetPair h' :=
    TopPair.ofHom (TopCat.ofHom (φ : C(B, B'))) (TopCat.ofHom fA) (by ext; rfl)
  let G : subsetPair h' ⟶ subsetPair h :=
    TopPair.ofHom (TopCat.ofHom (φ.symm : C(B', B))) (TopCat.ofHom gA) (by ext; rfl)
  have hFG : F ≫ G = 𝟙 _ := by
    ext x
    · have h1 := congrArg Subtype.val (φ.symm_apply_apply (Set.inclusion h x))
      exact Subtype.ext h1
    · exact φ.symm_apply_apply x
  have hmap : (relHomology (ModuleCat.of 𝕜 𝕜) i).map F ≫ (relHomology (ModuleCat.of 𝕜 𝕜) i).map G =
      𝟙 _ := by rw [← CategoryTheory.Functor.map_comp, hFG, CategoryTheory.Functor.map_id]
  constructor
  intro a b
  have ha := congrArg (fun T => T.hom a) hmap
  have hb := congrArg (fun T => T.hom b) hmap
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply]
    at ha hb
  rw [← ha, ← hb, Subsingleton.elim (((relHomology (ModuleCat.of 𝕜 𝕜) i).map F).hom a)
    (((relHomology (ModuleCat.of 𝕜 𝕜) i).map F).hom b)]


open scoped unitInterval in
/-- **A deformation into `A`, fixing `A`, kills `H_*(B, A) → H_*(C, A)`**: if `H : I × B → C`
deforms the inclusion of `B` into `A`, keeping `A` pointwise fixed, then the map
`H_i(B, A; 𝕜) → H_i(C, A; 𝕜)` induced by inclusion is zero. -/
theorem relHomology_map_eq_zero_of_deform {A B C : Set E} (hAB : A ⊆ B) (hBC : B ⊆ C)
    (H : C(I × B, E)) (hH0 : ∀ b, H (0, b) = b) (hH1 : ∀ b, H (1, b) ∈ A)
    (hHA : ∀ t (b : B), (b : E) ∈ A → H (t, b) = b) (hHC : ∀ t b, H (t, b) ∈ C) (i : ℕ) :
    (relHomology (ModuleCat.of 𝕜 𝕜) i).map
      (subsetPairHom hAB (hAB.trans hBC) (subset_refl A) hBC) = 0 := by
  let q : C(B, A) := ⟨fun b => ⟨H (1, b), hH1 b⟩,
    (H.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩
  let Q : subsetPair hAB ⟶ subsetPair (subset_refl A) :=
    TopPair.ofHom (TopCat.ofHom q) (𝟙 _) (by
      ext a
      exact Subtype.ext (hHA 1 (Set.inclusion hAB a) a.2).symm)
  let R : subsetPair (subset_refl A) ⟶ subsetPair (hAB.trans hBC) :=
    subsetPairHom (subset_refl A) (hAB.trans hBC) (subset_refl A) (hAB.trans hBC)
  have hF : TopPair.Homotopic (subsetPairHom hAB (hAB.trans hBC) (subset_refl A) hBC) (Q ≫ R) := by
    refine ⟨{ fst := ?_, snd := ?_, w := ?_ }⟩
    · exact { toFun := fun p => ⟨H p, hHC p.1 p.2⟩
              continuous_toFun := H.continuous.subtype_mk _
              map_zero_left := fun b => Subtype.ext (hH0 b)
              map_one_left := fun b => rfl }
    · exact ContinuousMap.Homotopy.refl _
    · ext ⟨a, t⟩
      exact Subtype.ext (hHA _ (Set.inclusion hAB a) a.2)
  rw [relHomology_map_eq_of_homotopic _ hF, CategoryTheory.Functor.map_comp]
  have hz : CategoryTheory.Limits.IsZero
      ((relHomology (ModuleCat.of 𝕜 𝕜) i).obj (subsetPair (subset_refl A))) :=
    isZero_relHomology_of_isIso _ _ i
  rw [hz.eq_zero_of_tgt ((relHomology (ModuleCat.of 𝕜 𝕜) i).map Q), Limits.zero_comp]

end Morse.Homology

namespace Morse

open Morse.Homology CategoryTheory
open scoped unitInterval

local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)

/-- **Hypothesis (N)** (Milnor p. 42): a neighbourhood `U` of `A` which can be deformed into `A`
within `X`, keeping `A` pointwise fixed. -/
def HypothesisN {X : Type*} [TopologicalSpace X] (A : Set X) : Prop :=
  ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ ∃ H : C(I × U, X), (∀ u, H (0, u) = u) ∧
    (∀ u, H (1, u) ∈ A) ∧ ∀ t (u : U), (u : X) ∈ A → H (t, u) = u

theorem isNondegenerate_neg_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : E →L[ℝ] E →L[ℝ] ℝ) : IsNondegenerate (-H) ↔ IsNondegenerate H := by
  simp only [isNondegenerate_iff, _root_.neg_apply, neg_eq_zero]

variable {n k w : ℕ} {M : Set (𝔼 n)}
  (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, 𝔼 n) (𝔼 (2 * k)) (𝔼 w) M)

theorem hessian_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : E → ℝ) (u : E) :
    hessian (fun z => -g z) u = -hessian g u := by
  have h2 : fderiv ℝ (fun y => -g y) = fun y => -fderiv ℝ g y := by
    funext y; exact fderiv_neg
  rw [hessian, hessian, h2]
  exact fderiv_neg

/-- On a complex submanifold of real dimension `2k`, at a non-degenerate critical point of `L_p`,
`−L_p` has a non-degenerate critical point of index `2k − index ≥ k`. -/
theorem le_indexM_neg_normSq_sub {J : 𝔼 n →L[ℝ] 𝔼 n} (hJ : IsOrthComplexStructure J)
    (hc : IsComplexSubmanifold hM J) (p : 𝔼 n) (q : M)
    (hcrit : letI := hM.chartedSpace;
      IsCriticalPointM (𝔼 (2 * k)) (fun x : M => ‖(x : 𝔼 n) - p‖ ^ 2) q)
    (hnd : letI := hM.chartedSpace;
      IsNondegenerate (hessianM (𝔼 (2 * k)) (fun x : M => ‖(x : 𝔼 n) - p‖ ^ 2) q)) :
    letI := hM.chartedSpace
    k ≤ indexM (𝔼 (2 * k)) (fun x : M => -‖(x : 𝔼 n) - p‖ ^ 2) q := by
  let _ := hM.chartedSpace
  have := hM.isManifold
  obtain ⟨sc, hsc⟩ := hM q q.2
  set L : 𝔼 n → ℝ := fun y => ‖y - p‖ ^ 2 with hL
  have hF : ContDiff ℝ ∞ L := contDiff_normSq_sub p
  have hG : ContDiff ℝ ∞ (fun y => -L y) := hF.neg
  set u := (sc.φ (q : 𝔼 n)).1
  have hsym : ∀ v w, hessian (L ∘ sliceParam sc) u v w = hessian (L ∘ sliceParam sc) u w v :=
    fun v w => hessian_symm ((hF.contDiffAt.comp u (contDiffAt_sliceParam sc
      (toChart_apply_mem_target sc hsc))).of_le (by norm_cast)) v w
  have hnd' := (isNondegenerate_hessian_comp_sliceParam_iff hM sc hsc
    (hF.contDiffAt.of_le (by norm_cast)) hcrit).2 hnd
  have h1 := index_neg_add_index _ hsym hnd'
  have h2 := index_hessian_comp_sliceParam hM sc hsc (hF.contDiffAt.of_le (by norm_cast)) hcrit
  have hcritG : IsCriticalPointM (𝔼 (2 * k)) ((fun y => -L y) ∘ Subtype.val : M → ℝ) q :=
    (isCriticalPointM_neg_iff (L ∘ Subtype.val : M → ℝ) q).2 hcrit
  have h3 := index_hessian_comp_sliceParam hM sc hsc (hG.contDiffAt.of_le (by norm_cast)) hcritG
  have h4 : (fun y => -L y) ∘ sliceParam sc = fun z => -(L ∘ sliceParam sc) z := rfl
  rw [h4, hessian_neg] at h3
  have h5 : indexM (𝔼 (2 * k)) (L ∘ Subtype.val : M → ℝ) q ≤ k :=
    indexM_normSq_sub_le hM hJ hc p q hcrit
  rw [finrank_euclideanSpace_fin, h3, h2] at h1
  change k ≤ indexM (𝔼 (2 * k)) ((fun y => -L y) ∘ Subtype.val : M → ℝ) q
  omega

/-- **The key vanishing of Theorem 7.4 / Corollary 7.3** (Milnor pp. 41–42, the exposition's
proof without duality): let `X` be compact, `A ⊆ X` closed, and `X ∖ A` homeomorphic (by `e`) to
a closed complex submanifold `M` of `ℂⁿ` of complex dimension `k`, with `‖e⁻¹ y‖ → ∞` as `y → A`;
assume Hypothesis (N).  Then `H_r(X, A; 𝕜) = 0` for `r < k`. -/
theorem subsingleton_subsetHomology_univ_of_section {𝕜 : Type} [Field 𝕜] {X : Type}
    [TopologicalSpace X] [CompactSpace X] {A : Set X} (hA : IsClosed A) (hcl : IsClosed M)
    {J : 𝔼 n →L[ℝ] 𝔼 n} (hJ : IsOrthComplexStructure J) (hc : IsComplexSubmanifold hM J)
    (e : M ≃ₜ (Aᶜ : Set X))
    (hinf : ∀ x ∈ A, ∀ R : ℝ, ∀ᶠ y in 𝓝 x, ∀ hy : y ∈ Aᶜ, R ≤ ‖((e.symm ⟨y, hy⟩ : M) : 𝔼 n)‖)
    (hN : HypothesisN A) {r : ℕ} (hr : r < k) :
    Subsingleton (subsetHomology 𝕜 r (subset_univ A)) := by
  classical
  let _ := hM.chartedSpace
  have := hM.isManifold
  obtain ⟨U, hUo, hAU, H, hH0, hH1, hHA⟩ := hN
  obtain ⟨p, hp⟩ := exists_isMorseFunction_normSq_sub (hM := hM)
  set L : 𝔼 n → ℝ := fun y => ‖y - p‖ ^ 2 with hL_def
  have hL : ContDiff ℝ ∞ L := contDiff_normSq_sub p
  set G : 𝔼 n → ℝ := fun y => -L y with hG_def
  have hG : ContDiff ℝ ∞ G := hL.neg
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
  -- the sets `S = {L ≥ R} ⊆ M` and `V_R = A ∪ e(S) ⊆ X`
  set S : Set M := sublevel (G ∘ Subtype.val : M → ℝ) (-R) with hS_def
  have hmemS : ∀ y : M, y ∈ S ↔ R ≤ L y := fun y => by
    simp only [hS_def, mem_sublevel, Function.comp_apply, hG_def]
    constructor <;> intro h <;> linarith
  set VR : Set X := A ∪ {x | ∃ hx : x ∈ Aᶜ, e.symm ⟨x, hx⟩ ∈ S} with hVR_def
  have hAVR : A ⊆ VR := subset_union_left
  have hVRU : VR ⊆ U := by
    rintro x (hx | ⟨hx, hxS⟩)
    · exact hAU hx
    · by_contra hxU
      have h1 : φ ⟨x, hx⟩ ≤ B := hB ⟨⟨x, hx⟩, hxU, rfl⟩
      have h2 := (hmemS _).1 hxS
      change L (e.symm ⟨x, hx⟩) ≤ B at h1
      linarith
  have hint : closure A ⊆ interior VR := by
    rw [hA.closure_eq]
    intro x hx
    rw [mem_interior_iff_mem_nhds]
    filter_upwards [hinf x hx (Real.sqrt R + ‖p‖)] with y hy
    by_cases hyA : y ∈ A
    · exact Or.inl hyA
    · refine Or.inr ⟨hyA, (hmemS _).2 ?_⟩
      have h1 := hy hyA
      set z : 𝔼 n := ((e.symm ⟨y, hyA⟩ : M) : 𝔼 n)
      have h2 : Real.sqrt R ≤ ‖z - p‖ := by
        have := norm_sub_norm_le z p
        linarith
      have h3 : 0 ≤ Real.sqrt R := Real.sqrt_nonneg R
      calc R = Real.sqrt R ^ 2 := (Real.sq_sqrt hR0.le).symm
        _ ≤ ‖z - p‖ ^ 2 := by gcongr
  -- `H_r(M, S) = 0`: Morse theory for `−L` on the compact slab `{L ≤ R}`
  have hT : sublevel (G ∘ Subtype.val : M → ℝ) 1 = univ := by
    refine eq_univ_of_forall fun y => ?_
    simp only [mem_sublevel, Function.comp_apply, hG_def]
    have := sq_nonneg ‖(y : 𝔼 n) - p‖
    linarith
  have hslab : Subsingleton (subsetHomology 𝕜 r
      (sublevel_mono (G ∘ Subtype.val : M → ℝ) (by linarith : -R ≤ 1))) := by
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
    refine subsingleton_subsetHomology_slab hM hG hKG (fun q hq _ _ => ?_) r _ (by linarith) le_rfl
      le_rfl
      rfl (fun q hq h => ?_) (fun q hq h => ?_) (fun q hq _ _ h => ?_)
    · have := hessianM_neg (E := 𝔼 (2 * k)) (L ∘ Subtype.val : M → ℝ) q
      change IsNondegenerate (hessianM (𝔼 (2 * k)) (fun x => -(L ∘ Subtype.val) x) q)
      rw [this, isNondegenerate_neg_iff]
      exact hp.isNondegenerate q ((hcritG q).1 hq)
    · exact hreg m q ((hcritG q).1 hq) (by
        change L q = R
        linarith)
    · have := sq_nonneg ‖(q : 𝔼 n) - p‖
      change -‖(q : 𝔼 n) - p‖ ^ 2 = 1 at h
      linarith
    · have hq' := (hcritG q).1 hq
      have := le_indexM_neg_normSq_sub hM hJ hc p q hq' (hp.isNondegenerate q hq')
      change k ≤ indexM (𝔼 (2 * k)) (G ∘ Subtype.val) q at this
      omega
  -- transport to `H_r(X ∖ A, V_R ∖ A)`
  have hexc : Subsingleton (subsetHomology 𝕜 r (sdiff_subset_sdiff_left (subset_univ VR) :
      VR \ A ⊆ univ \ A)) := by
    have hcompl : (univ \ A : Set X) = Aᶜ := by ext; simp
    let ψ : (univ \ A : Set X) ≃ₜ (sublevel (G ∘ Subtype.val : M → ℝ) 1) :=
      (Homeomorph.setCongr hcompl).trans (e.symm.trans
        ((Homeomorph.Set.univ M).symm.trans (Homeomorph.setCongr hT.symm)))
    refine subsingleton_subsetHomology_of_homeomorph _ _ ψ (fun x => ?_) r hslab
    obtain ⟨x, hx⟩ := x
    have hxA : x ∈ Aᶜ := hx.2
    change x ∈ VR \ A ↔ e.symm ⟨x, hxA⟩ ∈ S
    constructor
    · rintro ⟨hx1 | ⟨hx', hxS⟩, hx2⟩
      · exact absurd hx1 hx2
      · exact hxS
    · intro h
      exact ⟨Or.inr ⟨hxA, h⟩, hxA⟩
  -- excision: `H_r(X, V_R) = 0`
  have hXV : Subsingleton (subsetHomology 𝕜 r (subset_univ VR)) := by
    have hiso := excision_of_closure_subset_interior 𝕜 (subset_univ VR) hint r
    let f := (relHomology (ModuleCat.of 𝕜 𝕜) r).map (subsetPairHom (E := X)
      (sdiff_subset_sdiff_left (subset_univ VR)) (subset_univ VR) (sdiff_subset : VR \ A ⊆ VR)
      (sdiff_subset : (univ : Set X) \ A ⊆ univ))
    have : IsIso f := hiso
    exact (asIso f).toLinearEquiv.toEquiv.symm.subsingleton
  -- Hypothesis (N): `H_r(V_R, A) → H_r(X, A)` is zero
  let H' : C(I × VR, X) := ⟨fun q => H (q.1, ⟨q.2, hVRU q.2.2⟩), by fun_prop⟩
  have hzero := relHomology_map_eq_zero_of_deform (𝕜 := 𝕜) hAVR (subset_univ VR) H'
    (fun b => hH0 _) (fun b => hH1 _) (fun t b hb => hHA t ⟨b, hVRU b.2⟩ hb) (fun _ _ => trivial) r
  -- the exact sequence of the triple `(X, V_R, A)`
  set E := subsetTripleLongExactSeq 𝕜 hAVR (subset_univ VR)
  have hf : E.f r = 0 := by
    change ((relHomology (ModuleCat.of 𝕜 𝕜) r).map _).hom = 0
    erw [hzero]
    rfl
  constructor
  intro x y
  have hx : x ∈ LinearMap.ker (E.g r) := by
    rw [LinearMap.mem_ker]; exact Subsingleton.elim _ _
  have hy : y ∈ LinearMap.ker (E.g r) := by
    rw [LinearMap.mem_ker]; exact Subsingleton.elim _ _
  obtain ⟨x', rfl⟩ := (E.exact_f_g r x).1 hx
  obtain ⟨y', rfl⟩ := (E.exact_f_g r y).1 hy
  rw [hf]
  rfl

/-- **Corollary 7.3 (Lefschetz), abstract form, over a field** (Milnor p. 41; the exposition's proof
without duality): under the hypotheses of `Morse.subsingleton_subsetHomology_univ_of_section`,
the inclusion `A → X` induces isomorphisms `H_r(A; 𝕜) → H_r(X; 𝕜)` for `r < k − 1` and a
surjection for `r = k − 1` (the map `f` of the exact sequence of the triple `∅ ⊆ A ⊆ X`). -/
theorem corollary_7_3_of_section {𝕜 : Type} [Field 𝕜] {X : Type}
    [TopologicalSpace X] [CompactSpace X] {A : Set X} (hA : IsClosed A) (hcl : IsClosed M)
    {J : 𝔼 n →L[ℝ] 𝔼 n} (hJ : IsOrthComplexStructure J) (hc : IsComplexSubmanifold hM J)
    (e : M ≃ₜ (Aᶜ : Set X))
    (hinf : ∀ x ∈ A, ∀ R : ℝ, ∀ᶠ y in 𝓝 x, ∀ hy : y ∈ Aᶜ, R ≤ ‖((e.symm ⟨y, hy⟩ : M) : 𝔼 n)‖)
    (hN : HypothesisN A) (r : ℕ) :
    (r + 1 < k → Bijective ((subsetTripleLongExactSeq 𝕜 (empty_subset A) (subset_univ A)).f r)) ∧
      (r < k → Surjective ((subsetTripleLongExactSeq 𝕜 (empty_subset A) (subset_univ A)).f r)) := by
  set E := subsetTripleLongExactSeq 𝕜 (empty_subset A) (subset_univ A)
  have hvan : ∀ s, s < k → Subsingleton (subsetHomology 𝕜 s (subset_univ A)) := fun s hs =>
    subsingleton_subsetHomology_univ_of_section hM hA hcl hJ hc e hinf hN hs
  have hsurj : r < k → Surjective (E.f r) := fun hr x => by
    have := hvan r hr
    exact (E.exact_f_g r x).1 (Subsingleton.elim _ _)
  refine ⟨fun hr => ⟨?_, hsurj (by omega)⟩, hsurj⟩
  have := hvan (r + 1) hr
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (E.exact_δ_f r x).1 hx
  rw [Subsingleton.elim y 0, map_zero]

end Morse
