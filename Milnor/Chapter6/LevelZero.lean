import Milnor.Chapter6.LevelMap
import Milnor.Chapter6.LevelSignM
import Milnor.Chapter6.Opens

/-!
# Tools for the region lemma

* `Orient.neg`: the opposite orientation, and its effect on signs and degrees.
* `levelOrient_eq_levelOrientM`: the vector-space level-set orientation of Chapter 5 is the
  manifold one for the constant orientation.
* `mfd_mul_of_eq_zero`, `mfd_prod_of_eq_zero`: the product rule at a zero of one factor.
* `exists_mfd_eq_zero_of_isRegularPoint_level`: at a point where both `f` and `f|G⁻¹(0)` are
  regular, the kernel line of `df` is transverse to the level set.
* `degAt_level_eq_zero_of_opens`: Milnor's Lemma 1 (§5) in boundary form for a map smooth only
  on an open set `U` containing the level set.
-/

open Set Module Filter Topology Function TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

universe u

section neg

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] {n : ℕ}

/-- Two orientations with the same orientation at every point are equal. -/
theorem Orient.ext' {o o' : Orient I M n} (h : ∀ x, o.or x = o'.or x) : o = o' := by
  cases o; cases o'
  congr
  funext x
  exact h x

/-- The opposite orientation. -/
def Orient.neg (hE : finrank ℝ E = n) (oM : Orient I M n) : Orient I M n where
  or x := -oM.or x
  cont x := by
    filter_upwards [oM.cont x] with y hy
    rw [orSign_neg_left hE, orSign_neg_right hE, hy]; norm_num

@[simp] theorem Orient.neg_or (hE : finrank ℝ E = n) (oM : Orient I M n) (x : M) :
    (oM.neg hE).or x = -oM.or x := rfl

theorem signAt_neg_left (hE : finrank ℝ E = n) (oM : Orient I M n) (oN : Orient J N n)
    (f : M → N) (x : M) : signAt (oM.neg hE) oN f x = -signAt oM oN f x := by
  unfold signAt; rw [Orient.neg_or, orSign_neg_left hE]

theorem signAt_neg_right (hE : finrank ℝ E = n) (hF : finrank ℝ F = n) (oM : Orient I M n)
    (oN : Orient J N n) (f : M → N) (x : M) :
    signAt oM (oN.neg hF) f x = -signAt oM oN f x := by
  unfold signAt; rw [Orient.neg_or, orSign_neg_right hE]

theorem degAt_neg_left (hE : finrank ℝ E = n) (oM : Orient I M n) (oN : Orient J N n)
    (f : M → N) (y : N) : degAt (oM.neg hE) oN f y = -degAt oM oN f y := by
  unfold degAt
  simp_rw [signAt_neg_left hE oM oN f, finsum_neg_distrib]

theorem deg_neg_left (hE : finrank ℝ E = n) (oM : Orient I M n) (oN : Orient J N n)
    (f : M → N) : deg (oM.neg hE) oN f = -deg oM oN f := by
  unfold deg
  split_ifs with h
  · exact degAt_neg_left hE oM oN f _
  · simp

end neg

section product

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The product rule at a zero of the second factor. -/
theorem mfd_mul_of_eq_zero {c G : M → ℝ} {x : M} (hc : MDifferentiableAt I 𝓘(ℝ, ℝ) c x)
    (hG : MDifferentiableAt I 𝓘(ℝ, ℝ) G x) (h0 : G x = 0) :
    mfd I 𝓘(ℝ, ℝ) (fun y => c y * G y) x = c x • mfd I 𝓘(ℝ, ℝ) G x := by
  have h := (hasMFDerivAt_mfd (I := I) (J := 𝓘(ℝ, ℝ)) hc).mul
    (hasMFDerivAt_mfd (I := I) (J := 𝓘(ℝ, ℝ)) hG)
  have h1 : mfd I 𝓘(ℝ, ℝ) (fun y => c y * G y) x =
      (c x • mfd I 𝓘(ℝ, ℝ) G x + G x • mfd I 𝓘(ℝ, ℝ) c x : E →L[ℝ] ℝ) := HasMFDerivAt.mfd_eq h
  rw [h1, h0, zero_smul, add_zero]

/-- The product rule for a finite product, at a zero of the factor `j`. -/
theorem mfd_prod_of_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {Gf : ι → M → ℝ} {x : M}
    (hs : ∀ j, ContMDiff I 𝓘(ℝ, ℝ) ∞ (Gf j)) (j : ι) (h0 : Gf j x = 0) :
    mfd I 𝓘(ℝ, ℝ) (fun y => ∏ l, Gf l y) x =
      (∏ l ∈ Finset.univ.erase j, Gf l x) • mfd I 𝓘(ℝ, ℝ) (Gf j) x := by
  have hfun : (fun y => ∏ l, Gf l y) =
      fun y => (∏ l ∈ Finset.univ.erase j, Gf l y) * Gf j y := by
    funext y; rw [mul_comm]
    exact (Finset.mul_prod_erase _ (fun l => Gf l y) (Finset.mem_univ j)).symm
  rw [hfun]
  refine mfd_mul_of_eq_zero ?_ ((hs j).mdifferentiableAt (by simp)) h0
  exact (contMDiff_finsetProd fun l _ => hs l).mdifferentiableAt (by simp)

end product

section level

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] {n : ℕ}
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G' : Type*} [TopologicalSpace G'] {J : ModelWithCorners ℝ F G'} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G' N] [IsManifold J ∞ N]

/-- The vector-space level-set orientation of Chapter 5 is the manifold one for the constant
orientation. -/
theorem levelOrient_eq_levelOrientM (hE : finrank ℝ E = n + 1) (hZ : finrank ℝ Z = n)
    (a₀ : Orientation ℝ E (Fin (n + 1))) {g : E → ℝ} (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (h0 : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g 0) :
    letI := (isSliceSubmanifold_preimage (Z := Z) (finrank_Z_add hE hZ) hg h0).chartedSpace
    levelOrient hE hZ a₀ hg h0 = levelOrientM hE hZ (Orient.const a₀) hg h0 := by
  letI := (isSliceSubmanifold_preimage (Z := Z) (finrank_Z_add hE hZ) hg h0).chartedSpace
  refine Orient.ext' fun q => ?_
  show contractOr hZ a₀ (outward hE g q.1) _ = contractOr hZ a₀ (outwardM hE g q.1) _
  have : outward hE g q.1 = outwardM hE g q.1 := by
    simp only [outward, outwardM, mfd, mfderiv_eq_fderiv]
  rw [this]

variable (hE : finrank ℝ E = n + 1) (hZ : finrank ℝ Z = n) (hF : finrank ℝ F = n)
  {g : M → ℝ} (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) (h0 : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g 0)

include hE hZ hF hg h0 in
/-- **Transversality from regularity of the restriction.**  If `f` and `f|g⁻¹(0)` are both
regular at `q`, the kernel line of `df_q` is transverse to the level set. -/
theorem exists_mfd_eq_zero_of_isRegularPoint_level {f : M → N} (q : g ⁻¹' {0})
    (hd : MDifferentiableAt 𝓘(ℝ, E) J f q.1) (hf : IsRegularPoint 𝓘(ℝ, E) J f q.1) :
    letI := (isSliceSubmanifold_preimage (Z := Z) (finrank_Z_add hE hZ) hg h0).chartedSpace
    IsRegularPoint 𝓘(ℝ, Z) J (f ∘ Subtype.val) q →
      ∃ w, mfd 𝓘(ℝ, E) J f q.1 w = 0 ∧ mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g q.1 w ≠ 0 := by
  have hS := isSliceSubmanifold_preimage (Z := Z) (finrank_Z_add hE hZ) hg h0
  letI := hS.chartedSpace
  haveI := hS.isManifold
  intro hfl
  set A := mfd 𝓘(ℝ, E) J f q.1 with hA
  have hker : LinearMap.ker (A : E →ₗ[ℝ] F) ≠ ⊥ := by
    intro hbot
    have h1 := LinearMap.finrank_range_add_finrank_ker (A : E →ₗ[ℝ] F)
    rw [hbot, finrank_bot, add_zero, hE] at h1
    have h2 := Submodule.finrank_le (LinearMap.range (A : E →ₗ[ℝ] F))
    rw [h1, hF] at h2
    omega
  obtain ⟨w, hwmem, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hAw : A w = 0 := LinearMap.mem_ker.1 hwmem
  refine ⟨w, hAw, fun hgw => ?_⟩
  obtain ⟨w', hw'₀⟩ := (mem_range_mfderiv_val_iff (finrank_Z_add hE hZ) hg h0 q w).2 hgw
  have hw' : mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : g ⁻¹' {0} → M) q w' = w := hw'₀
  have hchain : mfd 𝓘(ℝ, Z) J (f ∘ Subtype.val) q =
      A.comp (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : g ⁻¹' {0} → M) q) :=
    HasMFDerivAt.mfd_eq ((hasMFDerivAt_mfd (I := 𝓘(ℝ, E)) (J := J) hd).comp q
      (hasMFDerivAt_mfd (I := 𝓘(ℝ, Z)) (J := 𝓘(ℝ, E)) (hS.contMDiff_val.mdifferentiableAt (by simp))))
  have hsurj : Surjective (mfd 𝓘(ℝ, Z) J (f ∘ Subtype.val) q) := hfl
  have hinj : Injective (mfd 𝓘(ℝ, Z) J (f ∘ Subtype.val) q) :=
    ((bijective_iff_surjective_of_finrank hZ hF _).2 hsurj).1
  have h1 : mfd 𝓘(ℝ, Z) J (f ∘ Subtype.val) q w' = 0 := by
    rw [hchain]
    show A (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : g ⁻¹' {0} → M) q w') = 0
    rw [hw']
    exact hAw
  have hw'0 : w' = 0 := hinj (by rw [h1, map_zero])
  rw [hw'0, map_zero] at hw'
  exact hw0 hw'.symm

include hE hZ hF hg h0 in
/-- **Milnor's Lemma 1 (§5) in boundary form, for a map smooth on an open set `U` containing
the level set.**  If `f` is smooth on `U ⊇ g⁻¹(0)`, `y` is a regular value of `f|U`, the level
set is transverse to `f⁻¹(y)`, and `f⁻¹(y) ∩ {g ≥ 0} ∩ U` is compact, then
`deg (f|g⁻¹(0); y) = 0` for the level-set orientation. -/
theorem degAt_level_eq_zero_of_opens [T2Space M] [T2Space N] (oM : Orient 𝓘(ℝ, E) M (n + 1))
    (oN : Orient J N n) {U : Opens M} {f : M → N} (hf : ContMDiffOn 𝓘(ℝ, E) J ∞ f U)
    (hgU : ∀ x, g x = 0 → x ∈ U) {y : N}
    (hy : IsRegularValue 𝓘(ℝ, E) J (f ∘ (Subtype.val : U → M)) y)
    (hreg : ∀ x, f x = y → g x = 0 →
      ∃ w, mfd 𝓘(ℝ, E) J f x w = 0 ∧ mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x w ≠ 0)
    (hX : IsCompact {x : U | f x.1 = y ∧ 0 ≤ g x.1}) :
    letI := (isSliceSubmanifold_preimage (Z := Z) (finrank_Z_add hE hZ) hg h0).chartedSpace
    ((f ∘ Subtype.val) ⁻¹' {y} : Set (g ⁻¹' {0})).Finite ∧
      degAt (levelOrientM hE hZ oM hg h0) oN (f ∘ Subtype.val) y = 0 := by
  have hS := isSliceSubmanifold_preimage (Z := Z) (finrank_Z_add hE hZ) hg h0
  letI := hS.chartedSpace
  haveI := hS.isManifold
  have hfU : ∀ x : U, MDifferentiableAt 𝓘(ℝ, E) J f x.1 := fun x =>
    (hf.contMDiffAt (U.isOpen.mem_nhds x.2)).mdifferentiableAt (by simp)
  have hf' : ContMDiff 𝓘(ℝ, E) J ∞ (f ∘ (Subtype.val : U → M)) :=
    hf.comp_contMDiff contMDiff_subtype_val (fun x => x.2)
  have hg' : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (g ∘ (Subtype.val : U → M)) :=
    hg.comp contMDiff_subtype_val
  have hreg' : ∀ x : U, (f ∘ Subtype.val) x = y → (g ∘ Subtype.val) x = 0 →
      ∃ w, mfd 𝓘(ℝ, E) J (f ∘ Subtype.val) x w = 0 ∧
        mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (g ∘ Subtype.val) x w ≠ 0 := by
    intro x hfx hgx
    obtain ⟨w, hw1, hw2⟩ := hreg x.1 hfx hgx
    refine ⟨w, ?_, ?_⟩
    · rw [mfd_comp_subtype_val U (hfU x)]; exact hw1
    · rw [mfd_comp_subtype_val U (hg.mdifferentiableAt (by simp))]; exact hw2
  obtain ⟨hfin0, hL⟩ := lemmaOne_ambient' hE hF (oM.restrict U) oN hf' hy hg' hreg' hX
  -- the `U`-sum is the `M`-sum
  have himgU : {x : M | f x = y ∧ g x = 0} =
      Subtype.val '' {x : U | (f ∘ Subtype.val) x = y ∧ (g ∘ Subtype.val) x = 0} := by
    ext x; constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨x, hgU x h2⟩, ⟨h1, h2⟩, rfl⟩
    · rintro ⟨q, ⟨h1, h2⟩, rfl⟩; exact ⟨h1, h2⟩
  have hL' : ∑ᶠ x ∈ {x : M | f x = y ∧ g x = 0}, signAt oM (oN.prodReal hF) (pairMap f g) x = 0 := by
    rw [himgU, finsum_mem_image Subtype.val_injective.injOn, ← hL]
    refine finsum_mem_congr rfl fun x _ => ?_
    have : pairMap (f ∘ Subtype.val) (g ∘ Subtype.val) = pairMap f g ∘ (Subtype.val : U → M) := rfl
    rw [this]
    exact (signAt_restrict oM (oN.prodReal hF) U
      ((hfU x).prodMk (hg.mdifferentiableAt (by simp)))).symm
  have hfinM : {x : M | f x = y ∧ g x = 0}.Finite := by
    rw [himgU]; exact hfin0.image _
  -- the `M`-sum is the level-set sum
  have himg : {x : M | f x = y ∧ g x = 0} =
      Subtype.val '' ((f ∘ Subtype.val) ⁻¹' {y} : Set (g ⁻¹' {0})) := by
    ext x; constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨x, h2⟩, h1, rfl⟩
    · rintro ⟨q, hq, rfl⟩; exact ⟨hq, q.2⟩
  rw [himg] at hfinM hL'
  rw [finsum_mem_image Subtype.val_injective.injOn] at hL'
  have hfin : ((f ∘ Subtype.val) ⁻¹' {y} : Set (g ⁻¹' {0})).Finite :=
    hfinM.of_finite_image Subtype.val_injective.injOn
  refine ⟨hfin, ?_⟩
  unfold degAt
  rw [finsum_mem_congr rfl (fun q _ => signAt_levelOrientM_eq' hE hZ hF oM oN hg h0 q
    (hfU ⟨q.1, hgU q.1 q.2⟩)), ← mul_finsum_mem' _ _ hfin, hL', mul_zero]

end level

end Milnor
