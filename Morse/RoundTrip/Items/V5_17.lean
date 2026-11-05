import Morse
import RoundTrip.Check
import RoundTrip.Blind.V5_17

/-! Round trip V5_17 (Milnor §7, pp. 41–42, the abstract pair).  A ⇒ B is proved: B's
duality half (B1) outright from `Morse.theorem_7_1` (A not used), B's Theorem 7.4 half (B2) from A's
index bound `index(−L_p) ≥ k` by re-running the Morse part of the project's proof of 7.4, with a
collar argument replacing the project's Hypothesis (N) (A fixed) by B's weaker deformation (A
preserved).  B ⇒ A fails genuinely (B's homology statement assumes duality; B2 is homotopy, with
`X` Hausdorff). -/

open Set Filter Topology Function Module Metric CategoryTheory Morse.Homology
open scoped ContDiff Manifold unitInterval

namespace RoundTrip.V5_17

/-- The project's statement (no universe parameters; `𝕜 : Type`, `X : Type`; `HypothesisN` is
vocabulary): the index bound `index(−L_p) ≥ k`, the vanishing `H_r(X, A; 𝕜) = 0` for `r < k`,
and Corollary 7.3 for the abstract pair, over a field, under Hypothesis (N) and
`‖e⁻¹ y‖ → ∞` at `A`. -/
def A : Prop :=
  type_of% @Morse.le_indexM_neg_normSq_sub ∧
    type_of% @Morse.subsingleton_subsetHomology_univ_of_section ∧
    type_of% @Morse.corollary_7_3_of_section

theorem A_holds : A :=
  ⟨@Morse.le_indexM_neg_normSq_sub, @Morse.subsingleton_subsetHomology_univ_of_section,
    @Morse.corollary_7_3_of_section⟩

/-- The first conjunct of B (Corollary 7.3 from Lefschetz duality). -/
def B1 : Prop :=
  ∀ (F : Type) [Field F] (X : Type) [TopologicalSpace X] (A : Set X)
      (K d m k : ℕ) (M : Set (Rn (K + 1)))
      (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M)
      (J : Rn (K + 1) ≃ₗᵢ[ℝ] Rn (K + 1)), IsCplxStr J → IsCplxSub hM J → IsClosed M → d + 1 = 2 * k →
      Nonempty (↥(Aᶜ) ≃ₜ ↥M) →
      (∀ r : ℕ, r ≤ 2 * k → Nonempty (Hom F (Set.subset_univ A) r ≃ₗ[F]
        Module.Dual F (Hom F (Set.empty_subset (Aᶜ)) (2 * k - r)))) →
      ∀ r : ℕ, (r + 1 < k → Function.Bijective (inclF F (Set.subset_univ A) r).hom) ∧
        (r + 1 = k → Function.Surjective (inclF F (Set.subset_univ A) r).hom)

/-- The second conjunct of B (Theorem 7.4 from a deformable neighbourhood). -/
def B2 : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : Set X), IsClosed A →
      ∀ (K d m k : ℕ) (M : Set (Rn (K + 1)))
      (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M)
      (J : Rn (K + 1) ≃ₗᵢ[ℝ] Rn (K + 1)), IsCplxStr J → IsCplxSub hM J → IsClosed M → d + 1 = 2 * k →
      Nonempty (↥(Aᶜ) ≃ₜ ↥M) → Deformable X A →
      ∀ r : ℕ, 1 ≤ r → r < k → RelPiZero X A r

theorem B_iff : B ↔ B1 ∧ B2 := Iff.rfl

/-! ### Glue -/

/-- Theorem 7.1 (over a field) in B's setting, model dimension `D = 2k` as a variable. -/
theorem vanish_7_1 {K D m k : ℕ} (M : Set (Rn (K + 1)))
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn D) (Rn m) M)
    (J : Rn (K + 1) ≃ₗᵢ[ℝ] Rn (K + 1)) (hJ : IsCplxStr J)
    (hc : Morse.IsComplexSubmanifold hM (J.toContinuousLinearEquiv : Rn (K + 1) →L[ℝ] Rn (K + 1)))
    (hD : D = 2 * k) (hcl : IsClosed M) (𝕜 : Type) [Field 𝕜] {i : ℕ} (hi : k < i) :
    Subsingleton (spaceHomology 𝕜 i M) := by
  subst hD
  exact Morse.theorem_7_1 hM hcl (J := (J.toContinuousLinearEquiv : Rn (K + 1) →L[ℝ] Rn (K + 1)))
    ⟨fun v => hJ v, fun v w => J.inner_map_map v w⟩ hc hi

/-- Homology of a subset `S` of `X` homeomorphic to `M` vanishes when that of `M` does. -/
theorem subsingleton_of_homeomorph {𝕜 : Type} [Field 𝕜] {X : Type} [TopologicalSpace X] {S : Set X}
    {Y : Type} [TopologicalSpace Y] (φ : S ≃ₜ Y) (i : ℕ) (h : Subsingleton (spaceHomology 𝕜 i Y)) :
    Subsingleton (subsetHomology 𝕜 i (Set.empty_subset S)) := by
  have h2 : Subsingleton (subsetHomology 𝕜 i (Set.empty_subset (Set.univ : Set Y))) :=
    (subsetHomologyUnivEquiv (𝕜 := 𝕜) Y i).toEquiv.subsingleton
  exact subsingleton_subsetHomology_of_homeomorph (Set.empty_subset _) (Set.empty_subset _)
    (φ.trans (Homeomorph.Set.univ Y).symm) (fun x => by simp) i h2

/-- **B1 holds outright** (without A): Lefschetz duality turns Theorem 7.1 for `X − A ≅ M`
(`Morse.theorem_7_1`, outside the item) into `H_r(X, A; F) = 0` for `r < k`, and the exact
sequence of the pair `(X, A)` gives the conclusion. -/
theorem B1_holds : B1 := by
  intro F _ X _ A K d m k M hM J hJ hc hcl hd ⟨φ⟩ hdual r
  have hvan : ∀ s, s < k → Subsingleton (subsetHomology F s (Set.subset_univ A)) := by
    intro s hs
    obtain ⟨L⟩ := hdual s (by omega)
    have h1 : Subsingleton (spaceHomology F (2 * k - s) M) :=
      vanish_7_1 M hM J hJ (fun q v hv => hc q v hv) hd hcl F (by omega)
    have h2 : Subsingleton (Hom F (Set.empty_subset (Aᶜ)) (2 * k - s)) :=
      subsingleton_of_homeomorph φ _ h1
    have h3 : Subsingleton (Module.Dual F (Hom F (Set.empty_subset (Aᶜ)) (2 * k - s))) :=
      ⟨fun f g => LinearMap.ext fun v => by rw [Subsingleton.elim v 0, map_zero, map_zero]⟩
    exact L.toEquiv.subsingleton
  set E := subsetTripleLongExactSeq F (Set.empty_subset A) (Set.subset_univ A)
  have hsurj : r < k → Surjective (E.f r) := fun hr x => by
    have := hvan r hr
    exact (E.exact_f_g r x).1 (Subsingleton.elim _ _)
  suffices key : (r + 1 < k → Bijective (E.f r)) ∧ (r + 1 = k → Surjective (E.f r)) from key
  refine ⟨fun hr => ⟨?_, hsurj (by omega)⟩, fun hr => hsurj (by omega)⟩
  have := hvan (r + 1) hr
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (E.exact_δ_f r x).1 hx
  rw [Subsingleton.elim y 0, map_zero]

/-- In a Hausdorff `X`, a homeomorphism `e : M ≃ₜ X − A` with `M` closed in a Euclidean space is
proper, so `‖e⁻¹ y‖ → ∞` as `y → A` (the project's hypothesis `hinf`, which B does not state). -/
theorem hinf_of_t2 {X : Type} [TopologicalSpace X] [T2Space X] {A : Set X} {N : ℕ}
    {M : Set (Rn N)} (hcl : IsClosed M) (e : M ≃ₜ (Aᶜ : Set X)) :
    ∀ x ∈ A, ∀ R : ℝ, ∀ᶠ y in 𝓝 x, ∀ hy : y ∈ Aᶜ, R ≤ ‖((e.symm ⟨y, hy⟩ : M) : Rn N)‖ := by
  intro x hx R
  have hK : IsCompact ((Subtype.val : M → Rn N) ⁻¹' closedBall 0 R) :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_closedBall 0 R)
  have hC : IsCompact ((Subtype.val : (Aᶜ : Set X) → X) '' (e '' ((Subtype.val : M → Rn N) ⁻¹'
      closedBall 0 R))) :=
    (hK.image e.continuous).image continuous_subtype_val
  have hxC : x ∉ (Subtype.val : (Aᶜ : Set X) → X) '' (e '' ((Subtype.val : M → Rn N) ⁻¹'
      closedBall 0 R)) := by
    rintro ⟨y, -, rfl⟩
    exact y.2 hx
  filter_upwards [hC.isClosed.isOpen_compl.mem_nhds hxC] with y hyC hy
  by_contra hlt
  replace hlt := not_le.1 hlt
  refine hyC ⟨e (e.symm ⟨y, hy⟩), ⟨e.symm ⟨y, hy⟩, ?_, rfl⟩, by simp⟩
  simp only [mem_preimage, mem_closedBall, dist_zero_right]
  exact hlt.le

/-- **The collar trick**: a map `f : (Dʳ, Sʳ⁻¹) → (X, A)` with values in a set `U` which deforms
into `A` through maps *preserving* `A` (B's `Deformable`, weaker than the project's Hypothesis (N),
which fixes `A` pointwise) is homotopic rel `Sʳ⁻¹` to a map into `A`:
`G(s, c) = H(f(c / max(‖c‖, 1 − s/2)), min(s, 2(1 − ‖c‖)))`. -/
theorem collar {X : Type} [TopologicalSpace X] {A U : Set X} (H : C(U × I, X))
    (hH0 : ∀ x : U, H (x, 0) = x.1) (hH1 : ∀ x : U, H (x, 1) ∈ A)
    (hHA : ∀ (x : U) (t : I), x.1 ∈ A → H (x, t) ∈ A) {r : ℕ} (f : C(Cell r, X))
    (hfU : ∀ c, f c ∈ U) (hfA : ∀ x : Bdry r, f (bdryToCell x) ∈ A) :
    ∃ g : C(Cell r, X), (∀ c, g c ∈ A) ∧ f.HomotopicRel g (Set.range bdryToCell) := by
  have hnc : ∀ c : Cell r, ‖(c : EuclideanSpace ℝ (Fin r))‖ ≤ 1 := fun c =>
    mem_closedBall_zero_iff.1 c.2
  let den : I × Cell r → ℝ := fun q => max ‖(q.2 : EuclideanSpace ℝ (Fin r))‖ (1 - (q.1 : ℝ) / 2)
  have hden : ∀ q, 1 / 2 ≤ den q := fun q => by
    have := q.1.2.2
    exact le_max_of_le_right (by linarith)
  have hdenc : Continuous den := by
    refine (continuous_norm.comp (continuous_subtype_val.comp continuous_snd)).max ?_
    exact continuous_const.sub ((continuous_subtype_val.comp continuous_fst).div_const 2)
  let cpt : I × Cell r → Cell r := fun q => ⟨(den q)⁻¹ • (q.2 : EuclideanSpace ℝ (Fin r)), by
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos (by linarith [hden q])]
    rw [inv_mul_le_iff₀ (by linarith [hden q]), mul_one]
    exact le_max_left _ _⟩
  have hcpt : Continuous cpt := by
    refine Continuous.subtype_mk (Continuous.smul (hdenc.inv₀ fun q => ?_)
      (continuous_subtype_val.comp continuous_snd)) _
    linarith [hden q]
  let tau : I × Cell r → I := fun q => ⟨min (q.1 : ℝ) (2 * (1 - ‖(q.2 : EuclideanSpace ℝ (Fin r))‖)),
    le_min q.1.2.1 (by linarith [hnc q.2]), (min_le_left _ _).trans q.1.2.2⟩
  have htau : Continuous tau := by
    refine Continuous.subtype_mk (Continuous.min (continuous_subtype_val.comp continuous_fst) ?_) _
    exact continuous_const.mul (continuous_const.sub
      (continuous_norm.comp (continuous_subtype_val.comp continuous_snd)))
  let G : C(I × Cell r, X) := ⟨fun q => H (⟨f (cpt q), hfU _⟩, tau q),
    H.continuous.comp ((Continuous.subtype_mk (f.continuous.comp hcpt) _).prodMk htau)⟩
  have hcpt1 : ∀ q : I × Cell r, ‖(q.2 : EuclideanSpace ℝ (Fin r))‖ = 1 ∨ (q.1 : ℝ) = 0 →
      cpt q = q.2 ∧ tau q = 0 := by
    rintro q hq
    have hd : den q = 1 := by
      change max ‖(q.2 : EuclideanSpace ℝ (Fin r))‖ (1 - (q.1 : ℝ) / 2) = 1
      rcases hq with hq | hq
      · rw [hq]
        exact max_eq_left (by linarith [q.1.2.1])
      · rw [hq, zero_div, sub_zero]
        exact max_eq_right (hnc q.2)
    refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
    · change (den q)⁻¹ • (q.2 : EuclideanSpace ℝ (Fin r)) = q.2
      rw [hd, inv_one, one_smul]
    · change min (q.1 : ℝ) (2 * (1 - ‖(q.2 : EuclideanSpace ℝ (Fin r))‖)) = 0
      rcases hq with hq | hq
      · rw [hq]; simp [q.1.2.1]
      · rw [hq]; exact min_eq_left (by linarith [hnc q.2])
  have hG0 : ∀ q : I × Cell r, ‖(q.2 : EuclideanSpace ℝ (Fin r))‖ = 1 ∨ (q.1 : ℝ) = 0 →
      G q = f q.2 := fun q hq => by
    change H (⟨f (cpt q), hfU _⟩, tau q) = f q.2
    obtain ⟨h1, h2⟩ := hcpt1 q hq
    rw [h2, hH0]
    change f (cpt q) = f q.2
    rw [h1]
  let g : C(Cell r, X) := ⟨fun c => G (1, c), by fun_prop⟩
  refine ⟨g, fun c => ?_, ⟨Morse.Homotopy.homotopyRelOfFun G (fun c => hG0 (0, c) (Or.inr rfl))
    (fun c => rfl) fun t c hc => hG0 (t, c) (Or.inl ?_)⟩⟩
  · change H (⟨f (cpt (1, c)), hfU _⟩, tau (1, c)) ∈ A
    by_cases hc : ‖(c : EuclideanSpace ℝ (Fin r))‖ ≤ 1 / 2
    · have : tau (1, c) = 1 := Subtype.ext (by
        change min ((1 : I) : ℝ) (2 * (1 - ‖(c : EuclideanSpace ℝ (Fin r))‖)) = 1
        simp only [Set.Icc.coe_one]
        exact min_eq_left (by linarith))
      rw [this]
      exact hH1 _
    · refine hHA _ _ ?_
      have hd : den (1, c) = ‖(c : EuclideanSpace ℝ (Fin r))‖ := by
        simp only [den, Set.Icc.coe_one]
        exact max_eq_left (by linarith)
      have hcn : ‖(c : EuclideanSpace ℝ (Fin r))‖ ≠ 0 := by linarith
      have hmem : ((cpt (1, c) : Cell r) : EuclideanSpace ℝ (Fin r)) ∈ sphere 0 1 := by
        rw [mem_sphere_zero_iff_norm]
        change ‖(den (1, c))⁻¹ • (c : EuclideanSpace ℝ (Fin r))‖ = 1
        rw [hd, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hcn]
      have : cpt (1, c) = bdryToCell ⟨_, hmem⟩ := rfl
      change f (cpt (1, c)) ∈ A
      rw [this]
      exact hfA _
  · obtain ⟨x, rfl⟩ := hc
    exact mem_sphere_zero_iff_norm.1 x.2

local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)

open Morse in
/-- **B2 from A's index bound.**  The Morse-theoretic half of the project's proof of Theorem 7.4
(`Morse.theorem_7_4_of_section`, re-run here with A's `le_indexM_neg_normSq_sub` as the only
index input): Morse theory for `−L_p` on `X − A ≅ M` pushes every map `Dʳ → X`, `r < k`, into
the region `V_R ⊆ U` rel the part already there; then the collar trick replaces the project's
Hypothesis (N) (which fixes `A`) by B's weaker `Deformable` (which only preserves `A`).  `hinf` is
derived from `T2Space X` (`hinf_of_t2`). -/
theorem B2_core (hA : A) {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {Aset : Set X} (hAc : IsClosed Aset) {n D w k : ℕ} (M : Set (𝔼 n))
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, 𝔼 n) (𝔼 D) (𝔼 w) M)
    {J : 𝔼 n →L[ℝ] 𝔼 n} (hJ : IsOrthComplexStructure J) (hc : IsComplexSubmanifold hM J)
    (hcl : IsClosed M) (hD : D = 2 * k) (e : M ≃ₜ (Asetᶜ : Set X)) (hDef : Deformable X Aset)
    {r : ℕ} (hrk : r < k) : RelPiZero X Aset r := by
  subst hD
  classical
  let _ := hM.chartedSpace
  have := hM.isManifold
  obtain ⟨U, hU, H, hH0, hH1, hHA⟩ := hDef
  obtain ⟨U₀, hU₀o, hAU₀, hU₀U⟩ := mem_nhdsSet_iff_exists.1 hU
  have hinf := hinf_of_t2 hcl e
  obtain ⟨p, hp⟩ := exists_isMorseFunction_normSq_sub (hM := hM)
  set L : 𝔼 n → ℝ := fun y => ‖y - p‖ ^ 2 with hL_def
  have hL : ContDiff ℝ ∞ L := Morse.contDiff_normSq_sub p
  set G : 𝔼 n → ℝ := fun y => -L y with hG_def
  have hG : ContDiff ℝ ∞ G := hL.neg
  have hψ : Continuous (sectionFun e p) := continuous_sectionFun hAc e hinf p
  have hψA : ∀ x (hx : x ∈ Asetᶜ), sectionFun e p x = (1 + L (e.symm ⟨x, hx⟩))⁻¹ :=
    fun x hx => dif_pos hx
  set φ : (Asetᶜ : Set X) → ℝ := fun y => L (e.symm y) with hφ_def
  have hφ : Continuous φ := hL.continuous.comp (continuous_subtype_val.comp e.symm.continuous)
  have hKU : IsCompact ((Subtype.val : (Asetᶜ : Set X) → X) ⁻¹' U₀ᶜ) := by
    refine (Topology.IsInducing.subtypeVal.isCompact_preimage_iff ?_).2
      hU₀o.isClosed_compl.isCompact
    intro x hx
    exact ⟨⟨x, fun hxA => hx (hAU₀ hxA)⟩, rfl⟩
  obtain ⟨B, hB⟩ := hKU.bddAbove_image hφ.continuousOn
  have hK : ∀ a, IsCompact ((L ∘ Subtype.val : M → ℝ) ⁻¹' Set.Iic a) :=
    fun a => isCompact_sublevel_normSq_sub hcl p a
  obtain ⟨a, -, -, ha', hreg⟩ := exists_regular_levels hM hL hK hp.isNondegenerate
    fun _ => sq_nonneg _
  obtain ⟨m, hm⟩ := (ha'.eventually_ge_atTop (max B 0 + 1)).exists
  set R := a m with hR_def
  have hRB : B < R := by have := le_max_left B 0; linarith
  have hR0 : 0 < R := by have := le_max_right B 0; linarith
  set VR : Set X := {x | sectionFun e p x ≤ (1 + R)⁻¹} with hVR_def
  set C : Set X := {x | (1 + (R + 1))⁻¹ ≤ sectionFun e p x} with hC_def
  have hAVR : Aset ⊆ VR := fun x hx => by
    change sectionFun e p x ≤ _
    rw [sectionFun_of_mem e p hx]
    positivity
  have hVRU : VR ⊆ U₀ := by
    intro x hx
    by_contra hxU
    have hxA : x ∈ Asetᶜ := fun h => hxU (hAU₀ h)
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
    refine ⟨?_, hA.1 hM hJ hc p q hq' (hp.isNondegenerate q hq')⟩
    have := hessianM_neg (E := 𝔼 (2 * k)) (L ∘ Subtype.val : M → ℝ) q
    change IsNondegenerate (hessianM (𝔼 (2 * k)) (fun x => -(L ∘ Subtype.val) x) q)
    rw [this, isNondegenerate_neg_iff]
    exact hp.isNondegenerate q hq'
  have hE : finrank ℝ (𝔼 r) < k := by rw [finrank_euclideanSpace_fin]; exact hrk
  have hloc : ∀ h : C(Cell r, X), PushesInto (h ⁻¹' C) VR C := by
    intro h
    have : CompactSpace (h ⁻¹' C) :=
      isCompact_iff_compactSpace.1 (hCcl.preimage h.continuous).isCompact
    intro g hgC
    have hgA : ∀ q, g q ∈ Asetᶜ := fun q hqA => by
      have h1 : (1 + (R + 1))⁻¹ ≤ sectionFun e p (g q) := hgC q
      rw [sectionFun_of_mem e p hqA] at h1
      have : (0 : ℝ) < (1 + (R + 1))⁻¹ := by positivity
      linarith
    let g₁ : C(h ⁻¹' C, M) :=
      ⟨fun q => e.symm ⟨g q, hgA q⟩, e.symm.continuous.comp (g.continuous.subtype_mk _)⟩
    have hD := lemma_D_slab hM hG (a := -R) (a₀ := 1) hKG (l₀ := k) hareg hcrit
      (P := h ⁻¹' C) hE (ι := (Subtype.val : Cell r → 𝔼 r) ∘ Subtype.val)
      (continuous_subtype_val.comp continuous_subtype_val)
      (Subtype.val_injective.comp Subtype.val_injective) (b := 0) (by linarith) (by norm_num)
    obtain ⟨g₁', hg₁'S, ⟨F₁⟩⟩ := hD g₁ fun q => by
      change -‖((g₁ q : M) : 𝔼 n) - p‖ ^ 2 ≤ 0
      exact neg_nonpos.2 (sq_nonneg _)
    let ev : C(M, X) := ⟨fun y => (e y : X), continuous_subtype_val.comp e.continuous⟩
    refine ⟨ev.comp g₁', fun q => ?_, ⟨Morse.Homotopy.homotopyRelOfFun
      (ev.comp F₁.toContinuousMap) (fun q => ?_) (fun q => ?_) fun t q hq => ?_⟩⟩
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
  have h1 : PushesInto (Cell r) VR univ := pushesInto_univ_of_isClosed hCcl hclY hloc
  -- the compression criterion
  intro f hf
  obtain ⟨f₁, hf₁, ⟨F₁⟩⟩ := h1 f fun _ => trivial
  have hbd : Set.range bdryToCell ⊆ f ⁻¹' VR := by
    rintro _ ⟨x, rfl⟩
    exact hAVR (hf x)
  have hf₁A : ∀ x : Bdry r, f₁ (bdryToCell x) ∈ Aset := fun x => by
    rw [← F₁.fst_eq_snd (hbd ⟨x, rfl⟩)]
    exact hf x
  obtain ⟨g, hg, ⟨F₂⟩⟩ := collar H hH0 hH1 hHA f₁ (fun c => hU₀U (hVRU (hf₁ c))) hf₁A
  exact ⟨g, hg, ⟨(Morse.Homotopy.homotopyRelMono F₁ hbd).trans F₂⟩⟩

/-- **B2 follows from A** (its first clause, the index bound). -/
theorem B2_of_A (hA : A) : B2 := by
  intro X _ _ _ Aset hAc K d m k M hM J hJ hc hcl hd ⟨φ⟩ hDef r _ hrk
  exact B2_core hA hAc M hM (J := (J.toContinuousLinearEquiv : Rn (K + 1) →L[ℝ] Rn (K + 1)))
    ⟨fun v => hJ v, fun v w => J.inner_map_map v w⟩ (fun q v hv => hc q v hv) hcl hd φ.symm hDef hrk

/-- **A ⇒ B.**  B1 is proved outright (`B1_holds`: Lefschetz duality + `Morse.theorem_7_1`, A not
used); B2 uses A's index bound `index(−L_p) ≥ k` (`B2_of_A`). -/
theorem A_to_B : A → B := fun hA => ⟨B1_holds, B2_of_A hA⟩

#rt_check RoundTrip.V5_17.A_to_B [Morse.le_indexM_neg_normSq_sub, Morse.subsingleton_subsetHomology_univ_of_section, Morse.corollary_7_3_of_section]
#rt_check RoundTrip.V5_17.B1_holds [Morse.le_indexM_neg_normSq_sub, Morse.subsingleton_subsetHomology_univ_of_section, Morse.corollary_7_3_of_section]

end RoundTrip.V5_17
