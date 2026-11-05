import Morse
import RoundTrip.Check
import RoundTrip.Glue
import RoundTrip.Blind.V3_20

open Set Filter Topology Function Module Morse.Homology
open scoped ContDiff Manifold

namespace RoundTrip.V3_20

/-- The project's statement (the seven listed theorems; no universe parameters). -/
def A : Prop :=
  type_of% @Morse.IsEulerNumber.finsum_eq_of_ambient ∧
  type_of% @Morse.exists_contDiff_comp_val_eq ∧
  type_of% @Morse.IsEulerNumber.finsum_eq ∧
  type_of% @Morse.IsEulerNumber.sum_critCount_eq ∧
  type_of% @Morse.exists_eulerNumber_eq_sum_critCount ∧
  type_of% @Morse.sum_critCount_eq_of_isMorseFunction ∧
  type_of% @Morse.IsEulerNumber.eq_sum_critCount

theorem A_holds : A :=
  ⟨@Morse.IsEulerNumber.finsum_eq_of_ambient, @Morse.exists_contDiff_comp_val_eq,
    @Morse.IsEulerNumber.finsum_eq, @Morse.IsEulerNumber.sum_critCount_eq,
    @Morse.exists_eulerNumber_eq_sum_critCount, @Morse.sum_critCount_eq_of_isMorseFunction,
    @Morse.IsEulerNumber.eq_sum_critCount⟩

/-! ### Glue -/

/-- An index sum over an injective enumeration of the zeros is the `finsum` over the zero set. -/
lemma sum_enum_eq_finsum {α : Type} (S : Set α) (g : α → ℤ) {j : ℕ} (z : Fin j → α)
    (hz : Function.Injective z) (hzS : ∀ q, q ∈ S ↔ ∃ i, q = z i) :
    ∑ i, g (z i) = ∑ᶠ q ∈ S, g q := by
  classical
  have hS : S = Set.range z := by
    ext q; rw [hzS]; exact ⟨fun ⟨i, h⟩ ↦ ⟨i, h.symm⟩, fun ⟨i, h⟩ ↦ ⟨i, h.symm⟩⟩
  rw [hS, finsum_mem_range hz]
  exact (finsum_eq_sum_of_fintype _).symm

/-- A finite set admits an injective enumeration. -/
lemma exists_enum {α : Type} {S : Set α} (hS : S.Finite) :
    ∃ (j : ℕ) (z : Fin j → α), Function.Injective z ∧ ∀ q, q ∈ S ↔ ∃ i, q = z i := by
  classical
  let s := hS.toFinset
  let e := s.equivFin
  refine ⟨s.card, fun i ↦ (e.symm i).1, fun i i' h ↦ e.symm.injective (Subtype.ext h), fun q ↦ ?_⟩
  constructor
  · intro hq
    exact ⟨e ⟨q, hS.mem_toFinset.2 hq⟩, by simp⟩
  · rintro ⟨i, rfl⟩
    exact hS.mem_toFinset.1 (e.symm i).2

section Setting

variable {K d m : ℕ} {N : Set (Rn (K + 1))}
  (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) N)
  (hc : IsCompact N) (hne : N.Nonempty)

include hc in
/-- The zeros of the tangential gradient of an ambient `F` whose restriction has non-degenerate
critical points are finitely many (they are the critical points). -/
lemma finite_zeros {F : Rn (K + 1) → ℝ} (hF : ContDiff ℝ ∞ F)
    (hnd : letI := hN.chartedSpace; ∀ q : N, Morse.IsCriticalPointM (Rn (d + 1)) (F ∘ Subtype.val) q →
      Morse.IsNondegenerate (Morse.hessianM (Rn (d + 1)) (F ∘ Subtype.val) q)) :
    {q : N | Morse.tangentialGradient hN F q = 0}.Finite := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  have : CompactSpace N := isCompact_iff_compactSpace.1 hc
  have hM : Morse.IsMorseFunction (Rn (d + 1)) (F ∘ Subtype.val) :=
    ⟨Morse.contMDiff_comp_val hN hF, hnd⟩
  exact hM.finite_setOf_isCriticalPointM.subset fun q hq ↦
    (Morse.tangentialGradient_eq_zero_iff hN (hF.differentiable (by simp) _)).1 hq

/-- B's first clause for the value `c` says that `c` is an Euler number in the project's sense. -/
lemma isEulerNumber_of {c : ℤ}
    (h1 : letI := hN.chartedSpace; ∀ (v : N → Rn (K + 1))
      (hv : ContMDiff 𝓘(ℝ, Rn (d + 1)) 𝓘(ℝ, Rn (K + 1)) ∞ v),
      (∀ q, v q ∈ Milnor.Tub.tanN hN q) → {q : N | v q = 0}.Finite →
      ∑ᶠ q ∈ {q : N | v q = 0}, Milnor.Tub.indexN hN hc hne v hv q = c) :
    Morse.IsEulerNumber hN hc hne c := by
  intro v hv hvT j z hz hzero
  let _ := hN.chartedSpace
  have hfin : {q : N | v q = 0}.Finite := by
    refine (Set.finite_range z).subset fun q hq ↦ ?_
    obtain ⟨i, rfl⟩ := (hzero q).1 hq
    exact ⟨i, rfl⟩
  rw [sum_enum_eq_finsum {q : N | v q = 0} _ z hz (fun q ↦ hzero q)]
  exact h1 v hv hvT hfin

/-- Conversely an Euler number is the index sum of any one tangent field with finite zeros; with
B's first clause, the Euler number is `c`. The field used is the tangential gradient of a Morse
function `L_p = ‖· - p‖²`. -/
lemma eq_of_isEulerNumber {c χN : ℤ} (hχ : Morse.IsEulerNumber hN hc hne χN)
    (h1 : letI := hN.chartedSpace; ∀ (v : N → Rn (K + 1))
      (hv : ContMDiff 𝓘(ℝ, Rn (d + 1)) 𝓘(ℝ, Rn (K + 1)) ∞ v),
      (∀ q, v q ∈ Milnor.Tub.tanN hN q) → {q : N | v q = 0}.Finite →
      ∑ᶠ q ∈ {q : N | v q = 0}, Milnor.Tub.indexN hN hc hne v hv q = c) :
    χN = c := by
  let _ := hN.chartedSpace
  obtain ⟨p, hp⟩ := Morse.exists_isMorseFunction_normSq_sub (hM := hN)
  have hF := Morse.Homology.contDiff_normSq_sub p
  have hfin := finite_zeros hN hc hF hp.isNondegenerate
  obtain ⟨j, z, hz, hzS⟩ := exists_enum hfin
  have := hχ _ (Morse.contMDiff_tangentialGradient hN hc hne hF)
    (Morse.tangentialGradient_mem_range hN _) z hz hzS
  rw [← this, sum_enum_eq_finsum _ _ z hz hzS]
  exact h1 _ _ (Morse.tangentialGradient_mem_range hN _) hfin

include hc hne in
/-- Every smooth function on `N` is the restriction of a smooth function on `ℝᴷ⁺¹`. This is the
project's `exists_contDiff_comp_val_eq` (one of the listed theorems), re-proved verbatim from the
project's tubular-neighbourhood lemmas (`tubRet`, `Milnor.exists_extension`), which are not among
the listed declarations: B has no counterpart. -/
theorem exists_ext {f : N → ℝ}
    (hf : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Rn (d + 1)) 𝓘(ℝ, ℝ) ∞ f) :
    ∃ F : Rn (K + 1) → ℝ, ContDiff ℝ ∞ F ∧ F ∘ Subtype.val = f := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  set U : TopologicalSpace.Opens (Rn (K + 1)) :=
    ⟨Milnor.Tub.Nε hN hc hne, Milnor.Tub.isOpen_Nε hN hc hne⟩ with hU
  have hrU : ContMDiff 𝓘(ℝ, Rn (K + 1)) 𝓘(ℝ, Rn (K + 1)) ∞
      (fun x : U => Morse.tubRet hN hc hne x.1) := by
    intro x
    have := Morse.contDiffAt_tubRet hN hc hne x.2
    rw [← contMDiffAt_iff_contDiffAt] at this
    exact (contMDiffAt_subtype_iff (I := 𝓘(ℝ, Rn (K + 1))) (I' := 𝓘(ℝ, Rn (K + 1))) (n := ∞)
      (U := U) (f := Morse.tubRet hN hc hne) (x := x)).2 this
  have hrN : ContMDiff 𝓘(ℝ, Rn (K + 1)) 𝓘(ℝ, Rn (d + 1)) ∞
      (fun x : U => Milnor.Tub.tubr hN hc hne x.1) :=
    hN.contMDiff_codRestrict hrU (fun x => Morse.tubRet_mem hN hc hne x.1)
  have hfU : ContMDiff 𝓘(ℝ, Rn (K + 1)) 𝓘(ℝ, ℝ) ∞
      (fun x : U => f (Milnor.Tub.tubr hN hc hne x.1)) := hf.comp hrN
  have hfW : ContMDiffOn 𝓘(ℝ, Rn (K + 1)) 𝓘(ℝ, ℝ) ∞ (fun x => f (Milnor.Tub.tubr hN hc hne x))
      (Milnor.Tub.Nε hN hc hne) := by
    intro x hx
    exact ((contMDiffAt_subtype_iff (I := 𝓘(ℝ, Rn (K + 1))) (I' := 𝓘(ℝ, ℝ)) (n := ∞) (U := U)
      (f := fun x => f (Milnor.Tub.tubr hN hc hne x)) (x := ⟨x, hx⟩)).1
        (hfU ⟨x, hx⟩)).contMDiffWithinAt
  obtain ⟨F, hF, hFeq⟩ := Milnor.exists_extension (Milnor.Tub.isOpen_Nε hN hc hne) hfW
    (Milnor.Tub.isCompact_X hN hc hne) (Milnor.Tub.X_subset_Nε hN hc hne)
  refine ⟨F, contMDiff_iff_contDiff.1 hF, funext fun q => ?_⟩
  have h := hFeq.self_of_nhdsSet q.1 (Milnor.Tub.N_subset_X hN hc hne q.2)
  rw [comp_apply, h, Milnor.Tub.tubr_val hN hc hne q]

end Setting

/-! ### The two directions -/

theorem A_to_B : A → B := by
  classical
  intro hA F' _ K d m N hN hc hne
  let _ := hN.chartedSpace
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · exact (RoundTrip.Glue.no_sliceSubmanifold_R1 hN hc hne).elim
  obtain ⟨χN, hχ⟩ := Morse.exists_isEulerNumber hN hc hne hK
  -- `χN` is the homological Euler characteristic: compare both with `L_p`
  have hχc : χN = chiN F' d N := by
    obtain ⟨p, hp⟩ := Morse.exists_isMorseFunction_normSq_sub (hM := hN)
    have h1 := hA.2.2.2.1 hN hc hne hK hχ hp
    have h2 := sum_bettiNumber_eq_sum_critCount (𝕜 := F') hN hc (contDiff_normSq_sub p)
      hp.isNondegenerate (Homeomorph.refl N)
    rw [finrank_euclideanSpace_fin] at h2
    have h3 : chiN F' d N = ∑ i ∈ Finset.range (d + 1 + 1), (-1 : ℤ) ^ i * (bettiNumber F' N i : ℤ) := by
      unfold chiN
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      congr 2
      exact finrank_subsetHomology_eq_bettiNumber (𝕜 := F') (Set.empty_subset _) rfl rfl i
    rw [← h1, h3]
    exact h2.symm
  have part1 : ∀ (v : N → Rn (K + 1)) (hv : ContMDiff 𝓘(ℝ, Rn (d + 1)) 𝓘(ℝ, Rn (K + 1)) ∞ v),
      (∀ q, v q ∈ Milnor.Tub.tanN hN q) → {q : N | v q = 0}.Finite →
      ∑ᶠ q ∈ {q : N | v q = 0}, Milnor.Tub.indexN hN hc hne v hv q = chiN F' d N := by
    intro v hv hvT hfin
    obtain ⟨j, z, hz, hzS⟩ := exists_enum hfin
    rw [← sum_enum_eq_finsum _ _ z hz hzS, hχ v hv hvT z hz hzS, hχc]
  refine ⟨part1, fun Φ hΦ hnd ↦ ⟨?_, fun hv ↦ ?_⟩⟩
  · have hΦ' : ContDiff ℝ ∞ Φ := contMDiff_iff_contDiff.1 hΦ
    have hM : Morse.IsMorseFunction (Rn (d + 1)) (Φ ∘ Subtype.val : N → ℝ) :=
      ⟨Morse.contMDiff_comp_val hN hΦ', fun q hq ↦ (hnd q hq).2⟩
    rw [← hχc, ← hA.2.2.2.1 hN hc hne hK hχ hM]
    rfl
  · have hΦ' : ContDiff ℝ ∞ Φ := contMDiff_iff_contDiff.1 hΦ
    exact part1 _ hv (Morse.tangentialGradient_mem_range hN Φ)
      (finite_zeros hN hc hΦ' fun q hq ↦ (hnd q hq).2)

theorem B_to_A : B → A := by
  intro hB
  -- the common core: an Euler number is `χ(N; ℚ)`, and `Σ (-1)^λ C_λ(F|N) = χ(N; ℚ)`
  have core : ∀ {K d m : ℕ} {N : Set (Rn (K + 1))}
      (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) N)
      (hc : IsCompact N) (hne : N.Nonempty) {χN : ℤ}, Morse.IsEulerNumber hN hc hne χN →
      χN = chiN ℚ d N := by
    intro K d m N hN hc hne χN hχ
    exact eq_of_isEulerNumber hN hc hne hχ (hB ℚ _ _ _ _ hN hc hne).1
  have sumC : ∀ {K d m : ℕ} {N : Set (Rn (K + 1))}
      (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) N)
      (hc : IsCompact N) (hne : N.Nonempty) {f : N → ℝ},
      (letI := hN.chartedSpace; Morse.IsMorseFunction (Rn (d + 1)) f) →
      (letI := hN.chartedSpace;
        ∑ k ∈ Finset.range (d + 2), (-1 : ℤ) ^ k * Morse.critCount (Rn (d + 1)) f k) =
        chiN ℚ d N := by
    intro K d m N hN hc hne f hf
    let _ := hN.chartedSpace
    obtain ⟨F, hF, rfl⟩ := exists_ext hN hc hne hf.contMDiff
    exact ((hB ℚ _ _ _ _ hN hc hne).2 F (contMDiff_iff_contDiff.2 hF)
      (fun q hq ↦ ⟨hq, hf.isNondegenerate q hq⟩)).1
  have c4 : type_of% @Morse.IsEulerNumber.sum_critCount_eq := by
    intro K d m N hN hc hne hK χN hχ f hf
    rw [sumC hN hc hne hf, core hN hc hne hχ]
  refine ⟨?_, ?_, ?_, c4, ?_, ?_, ?_⟩
  · intro K d m N hN hc hne hK χN hχ F hF hnd
    let _ := hN.chartedSpace
    have := hN.isManifold
    have : CompactSpace N := isCompact_iff_compactSpace.1 hc
    have hM : Morse.IsMorseFunction (Rn (d + 1)) (F ∘ Subtype.val : N → ℝ) :=
      ⟨Morse.contMDiff_comp_val hN hF, hnd⟩
    have h := Morse.finsum_neg_one_pow_indexM_eq_sum_critCount hM.finite_setOf_isCriticalPointM
    rw [finrank_euclideanSpace_fin] at h
    rw [h]
    exact c4 hN hc hne hK hχ hM
  · intro K d m N hN hc hne f hf
    exact exists_ext hN hc hne hf
  · intro K d m N hN hc hne hK χN hχ f hf
    let _ := hN.chartedSpace
    have := hN.isManifold
    have : CompactSpace N := isCompact_iff_compactSpace.1 hc
    have h := Morse.finsum_neg_one_pow_indexM_eq_sum_critCount hf.finite_setOf_isCriticalPointM
    rw [finrank_euclideanSpace_fin] at h
    rw [h]
    exact c4 hN hc hne hK hχ hf
  · intro K d m N hN hc hne hK
    refine ⟨chiN ℚ d N, isEulerNumber_of hN hc hne (hB ℚ _ _ _ _ hN hc hne).1,
      fun f hf ↦ sumC hN hc hne hf⟩
  · intro K d m N hN hc hne hK f g hf hg
    rw [sumC hN hc hne hf, sumC hN hc hne hg]
  · intro K d m N hN hc hne hK χN hχ f hf
    exact (c4 hN hc hne hK hχ hf).symm

#rt_check RoundTrip.V3_20.A_to_B [Morse.IsEulerNumber.finsum_eq_of_ambient,
  Morse.exists_contDiff_comp_val_eq, Morse.IsEulerNumber.finsum_eq,
  Morse.IsEulerNumber.sum_critCount_eq, Morse.exists_eulerNumber_eq_sum_critCount,
  Morse.sum_critCount_eq_of_isMorseFunction, Morse.IsEulerNumber.eq_sum_critCount]
#rt_check RoundTrip.V3_20.B_to_A [Morse.IsEulerNumber.finsum_eq_of_ambient,
  Morse.exists_contDiff_comp_val_eq, Morse.IsEulerNumber.finsum_eq,
  Morse.IsEulerNumber.sum_critCount_eq, Morse.exists_eulerNumber_eq_sum_critCount,
  Morse.sum_critCount_eq_of_isMorseFunction, Morse.IsEulerNumber.eq_sum_critCount]
#rt_overlap RoundTrip.V3_20.B_to_A [Morse.IsEulerNumber.finsum_eq_of_ambient,
  Morse.exists_contDiff_comp_val_eq, Morse.IsEulerNumber.finsum_eq,
  Morse.IsEulerNumber.sum_critCount_eq, Morse.exists_eulerNumber_eq_sum_critCount,
  Morse.sum_critCount_eq_of_isMorseFunction, Morse.IsEulerNumber.eq_sum_critCount]

end RoundTrip.V3_20
