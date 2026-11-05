import Morse
import RoundTrip.Check
import RoundTrip.Glue
import RoundTrip.Blind.V4_19

open Set Module Morse.Homology
open scoped ContDiff Manifold

namespace RoundTrip.V4_19

/-- The project's statement: the seven listed theorems, universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Morse.sum_critCount_eq_of_isMorseFunction_of_compactSpace.{0, 0} ∧
  type_of% @Morse.sum_critCount_eq_eulerNumberM.{0, 0} ∧
  type_of% @Morse.exists_eulerNumber_of_compactSpace.{0, 0} ∧
  type_of% @Morse.sum_critCount_of_finrank_eq_zero.{0, 0} ∧
  type_of% @Morse.IsEulerNumber.eq_eulerNumberM.{0, 0} ∧
  type_of% @Morse.eulerNumberM_eq_of_diffeomorph.{0, 0, 0, 0} ∧
  type_of% @Morse.exists_isEulerNumber_eulerNumberM.{0, 0}

theorem A_holds : A :=
  ⟨@Morse.sum_critCount_eq_of_isMorseFunction_of_compactSpace.{0, 0},
    @Morse.sum_critCount_eq_eulerNumberM.{0, 0}, @Morse.exists_eulerNumber_of_compactSpace.{0, 0},
    @Morse.sum_critCount_of_finrank_eq_zero.{0, 0}, @Morse.IsEulerNumber.eq_eulerNumberM.{0, 0},
    @Morse.eulerNumberM_eq_of_diffeomorph.{0, 0, 0, 0},
    @Morse.exists_isEulerNumber_eulerNumberM.{0, 0}⟩

/-! ### Glue -/

section Setting

variable {K d m : ℕ} {N : Set (Rn (K + 1))}
  (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) N)
  (hc : IsCompact N) (hne : N.Nonempty)

lemma chiN_eq_sum_betti :
    chiN d N = ∑ i ∈ Finset.range (d + 1 + 1), (-1 : ℤ) ^ i * (bettiNumber ℚ N i : ℤ) := by
  unfold chiN
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 2
  exact finrank_subsetHomology_eq_bettiNumber (𝕜 := ℚ) (Set.empty_subset _) rfl rfl i

/-- B's last clause for the value `c` says that `c` is an Euler number in the project's sense. -/
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
  rw [Glue.sum_enum_eq_finsum {q : N | v q = 0} _ z hz (fun q ↦ hzero q)]
  exact h1 v hv hvT hfin

include hc hne in
/-- From B's formula (3) on `N`: for every Morse function `f` on a manifold `M` diffeomorphic to
`N`, `Σ (-1)^λ C_λ(f) = χ(N; ℚ)` (transport to `N`, extend to `ℝ^{K+1}` by the project's
`exists_contDiff_comp_val_eq`, apply B). -/
lemma sum_critCount_eq_chiN (hB : B) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hd : finrank ℝ E = d + 1)
    (Φ : letI := hN.chartedSpace; Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Rn (d + 1)) M N ∞)
    {f : M → ℝ} (hf : Morse.IsMorseFunction E f) :
    ∑ k ∈ Finset.range (finrank ℝ E + 1), (-1 : ℤ) ^ k * (Morse.critCount E f k : ℤ) =
      chiN d N := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  have hg := hf.comp_diffeomorph_symm Φ
  obtain ⟨F, hF, hFg⟩ := Morse.exists_contDiff_comp_val_eq hN hc hne hg.contMDiff
  have h := (hB K d m N hN hc hne).1 F (contMDiff_iff_contDiff.2 hF) (fun q hq ↦ by
    have hq' : Morse.IsCriticalPointM (Rn (d + 1)) (f ∘ Φ.symm) q := by
      rw [← hFg]; exact hq
    have := hg.isNondegenerateCriticalPointM hq'
    rw [← hFg] at this
    exact this)
  rw [h, hd]
  have hC : ∀ l, Cnum (Rn (d + 1)) (fun x : N => F x) l = Morse.critCount E f l := by
    intro l
    rw [← Morse.critCount_comp_symm Φ (hf.contMDiff.of_le (by norm_cast)) l, ← hFg]
    rfl
  simp only [hC]

end Setting

/-- In dimension `0` every point is a critical point of index `0` (re-proved: B has nothing in
dimension `0`). -/
theorem sum_critCount_dim0 : type_of% @Morse.sum_critCount_of_finrank_eq_zero.{0, 0} := by
  intro E _ _ _ M _ _ h0 f
  rw [h0, zero_add, Finset.sum_range_one, pow_zero, one_mul, Morse.critCount]
  have : {p : M | Morse.IsCriticalPointM E f p ∧ Morse.indexM E f p = 0} = univ := by
    refine eq_univ_of_forall fun p ↦ ⟨Morse.isCriticalPointM_of_finrank_eq_zero h0 f p, ?_⟩
    have := Morse.indexM_le_finrank (E := E) f p
    omega
  rw [this, Set.ncard_univ]

/-! ### A ⇒ B -/

/-- **A ⇒ B.** `K = 0` is impossible (`Glue.no_sliceSubmanifold_R1`). An Euler number `χN` of `N`
exists (the project's Poincaré–Hopf theorem `exists_isEulerNumber`, not in the item); by A's
`IsEulerNumber.eq_eulerNumberM` (with the identity diffeomorphism) and `sum_critCount_eq_eulerNumberM`
it is `Σ (-1)^λ C_λ(L_p|N)`, which is `χ(N; ℚ)` by the project's homological
`sum_bettiNumber_eq_sum_critCount` (not in the item). Then (3) and the two index-sum clauses
follow; the gradient index clause is the project's `indexN_tangentialGradient` (not in A). -/
theorem A_to_B : A → B := by
  classical
  intro hA K d m N hN hc hne
  let _ := hN.chartedSpace
  have := hN.isManifold
  have : CompactSpace N := isCompact_iff_compactSpace.1 hc
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · exact (Glue.no_sliceSubmanifold_R1 hN hc hne).elim
  obtain ⟨χN, hχ⟩ := Morse.exists_isEulerNumber hN hc hne hK
  have hχE : χN = Morse.eulerNumberM (Rn (d + 1)) N :=
    hA.2.2.2.2.1 (E := Rn (d + 1)) (M := N) finrank_euclideanSpace_fin hN hc hne hK
      (Diffeomorph.refl _ _ _) hχ
  have hCchi : ∀ F : Rn (K + 1) → ℝ, ContDiff ℝ ∞ F →
      (∀ q : N, Morse.IsCriticalPointM (Rn (d + 1)) (fun x : N => F x) q →
        Morse.IsNondegenerate (Morse.hessianM (Rn (d + 1)) (fun x : N => F x) q)) →
      ∑ l ∈ Finset.range (d + 2), (-1 : ℤ) ^ l * (Cnum (Rn (d + 1)) (fun x : N => F x) l : ℤ) =
        Morse.eulerNumberM (Rn (d + 1)) N := by
    intro F hF hnd
    have h := hA.2.1 (E := Rn (d + 1)) (M := N) (f := fun x : N => F x)
      ⟨Morse.contMDiff_comp_val hN hF, hnd⟩
    rw [finrank_euclideanSpace_fin] at h
    exact h
  have hχc : χN = chiN d N := by
    obtain ⟨p, hp⟩ := Morse.exists_isMorseFunction_normSq_sub (hM := hN)
    have h2 := sum_bettiNumber_eq_sum_critCount' (𝕜' := ℚ) hN hc (contDiff_normSq_sub p)
      hp.isNondegenerate
    rw [finrank_euclideanSpace_fin] at h2
    rw [chiN_eq_sum_betti, h2, hχE, ← hCchi _ (contDiff_normSq_sub p) hp.isNondegenerate]
    rfl
  have part : ∀ (v : N → Rn (K + 1)) (hv : ContMDiff 𝓘(ℝ, Rn (d + 1)) 𝓘(ℝ, Rn (K + 1)) ∞ v),
      (∀ q, v q ∈ Milnor.Tub.tanN hN q) → {q : N | v q = 0}.Finite →
      ∑ᶠ q ∈ {q : N | v q = 0}, Milnor.Tub.indexN hN hc hne v hv q = chiN d N := by
    intro v hv hvT hfin
    obtain ⟨j, z, hz, hzS⟩ := Glue.exists_enum hfin
    rw [← Glue.sum_enum_eq_finsum _ _ z hz hzS, hχ v hv hvT z hz hzS, hχc]
  obtain ⟨p, hp⟩ := Morse.exists_isMorseFunction_normSq_sub (hM := hN)
  refine ⟨fun Φ hΦ hnd ↦ ?_, fun Φ hΦ hv q hq ↦ ?_, ⟨_, Morse.contMDiff_tangentialGradient hN hc
    hne (contDiff_normSq_sub p), Morse.tangentialGradient_mem_range hN _,
    Glue.finite_zeros_tangentialGradient hN hc (contDiff_normSq_sub p) hp.isNondegenerate,
    part _ _ (Morse.tangentialGradient_mem_range hN _)
      (Glue.finite_zeros_tangentialGradient hN hc (contDiff_normSq_sub p) hp.isNondegenerate)⟩,
    part⟩
  · rw [← hχc, hχE, hCchi Φ (contMDiff_iff_contDiff.1 hΦ) fun q hq ↦ (hnd q hq).2]
  · exact Morse.indexN_tangentialGradient hN hc hne hK (contMDiff_iff_contDiff.1 hΦ) hq

/-! ### B ⇒ A -/

/-- **B ⇒ A.** Every clause about an abstract compact manifold `M` of dimension `d + 1` goes
through a Whitney copy `N ⊆ ℝ^{K+1}` (the project's `exists_diffeomorph_sliceSubmanifold`) on
which B's formula (3) gives `Σ (-1)^λ C_λ(f) = χ(N; ℚ)` for every Morse `f`
(`sum_critCount_eq_chiN`); an Euler number of `N` is `χ(N; ℚ)` by B's index-sum clause
(`Glue.eq_of_isEulerNumber`), and `χ(N; ℚ)` is one by `isEulerNumber_of`. Dimension `0`
(`sum_critCount_of_finrank_eq_zero`) is re-proved: B has nothing there. Diffeomorphism invariance
compares the alternating counts directly (`critCount_comp_symm`). -/
theorem B_to_A : B → A := by
  intro hB
  -- (1) independence of the Morse function
  have c1 : type_of% @Morse.sum_critCount_eq_of_isMorseFunction_of_compactSpace.{0, 0} := by
    intro E _ _ _ M _ _ _ _ _ f g hf hg
    obtain ⟨n, hn⟩ : ∃ n, finrank ℝ E = n := ⟨_, rfl⟩
    rcases n with _ | d
    · rw [sum_critCount_dim0 hn f, sum_critCount_dim0 hn g]
    rcases isEmpty_or_nonempty M with hM | hM
    · have h0 : ∀ (h : M → ℝ) (k : ℕ), Morse.critCount E h k = 0 := fun h k ↦ by
        rw [Morse.critCount, Set.eq_empty_of_isEmpty {p : M | _}, Set.ncard_empty]
      simp only [h0]
    obtain ⟨K, m, N, hN, -, hNc, -, ⟨Φ⟩⟩ :=
      Morse.exists_diffeomorph_sliceSubmanifold (E := E) (M := M) hn
    have hne : N.Nonempty := ⟨_, (Φ (Classical.arbitrary M)).2⟩
    rw [sum_critCount_eq_chiN hN hNc hne hB hn Φ hf, sum_critCount_eq_chiN hN hNc hne hB hn Φ hg]
  have c2 : type_of% @Morse.sum_critCount_eq_eulerNumberM.{0, 0} := by
    intro E _ _ _ M _ _ _ _ _ f hf
    have h : ∃ f : M → ℝ, Morse.IsMorseFunction E f := ⟨f, hf⟩
    rw [Morse.eulerNumberM, dif_pos h]
    exact c1 hf h.choose_spec
  refine ⟨c1, c2, fun {E} _ _ _ {M} _ _ _ _ _ ↦ ⟨_, fun f hf ↦ c2 hf⟩, sum_critCount_dim0,
    ?_, ?_, ?_⟩
  · intro E _ _ _ M _ _ _ _ _ K d m hd N hN hNc hne hK Φ χN hχ
    let _ := hN.chartedSpace
    have := hN.isManifold
    have h1 := Glue.eq_of_isEulerNumber hN hNc hne hχ (hB K d m N hN hNc hne).2.2.2
    obtain ⟨f, hf, -⟩ := Morse.exists_isMorseFunction_of_compactSpace (E := E) (M := M)
    rw [h1, ← c2 hf, sum_critCount_eq_chiN hN hNc hne hB hd Φ hf]
  · intro E _ _ _ M _ _ _ _ _ E' _ _ _ M' _ _ _ _ _ g
    obtain ⟨f, hf, -⟩ := Morse.exists_isMorseFunction_of_compactSpace (E := E) (M := M)
    rw [← c2 hf, ← c2 (hf.comp_diffeomorph_symm g)]
    simp only [Morse.critCount_comp_symm g (hf.contMDiff.of_le (by norm_cast))]
    rcases isEmpty_or_nonempty M with hM | ⟨⟨x⟩⟩
    · have h0 : ∀ k : ℕ, Morse.critCount E f k = 0 := fun k ↦ by
        rw [Morse.critCount, Set.eq_empty_of_isEmpty {p : M | _}, Set.ncard_empty]
      simp only [h0, Nat.cast_zero, mul_zero, Finset.sum_const_zero]
    · have : finrank ℝ E = finrank ℝ E' :=
        (g.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv.finrank_eq
      rw [this]
  · intro E _ _ _ M _ _ _ _ _ _ d hd
    obtain ⟨K, m, N, hN, hK, hNc, -, ⟨Φ⟩⟩ :=
      Morse.exists_diffeomorph_sliceSubmanifold (E := E) (M := M) hd
    have hne : N.Nonempty := ⟨_, (Φ (Classical.arbitrary M)).2⟩
    let _ := hN.chartedSpace
    have := hN.isManifold
    obtain ⟨f, hf, -⟩ := Morse.exists_isMorseFunction_of_compactSpace (E := E) (M := M)
    refine ⟨K, m, N, hN, hNc, hne, ⟨Φ⟩, ?_⟩
    rw [← c2 hf, sum_critCount_eq_chiN hN hNc hne hB hd Φ hf]
    exact isEulerNumber_of hN hNc hne (hB K d m N hN hNc hne).2.2.2

#rt_check RoundTrip.V4_19.A_to_B [Morse.sum_critCount_eq_of_isMorseFunction_of_compactSpace,
  Morse.sum_critCount_eq_eulerNumberM, Morse.exists_eulerNumber_of_compactSpace,
  Morse.sum_critCount_of_finrank_eq_zero, Morse.IsEulerNumber.eq_eulerNumberM,
  Morse.eulerNumberM_eq_of_diffeomorph, Morse.exists_isEulerNumber_eulerNumberM]
#rt_check RoundTrip.V4_19.B_to_A [Morse.sum_critCount_eq_of_isMorseFunction_of_compactSpace,
  Morse.sum_critCount_eq_eulerNumberM, Morse.exists_eulerNumber_of_compactSpace,
  Morse.sum_critCount_of_finrank_eq_zero, Morse.IsEulerNumber.eq_eulerNumberM,
  Morse.eulerNumberM_eq_of_diffeomorph, Morse.exists_isEulerNumber_eulerNumberM]
#rt_overlap RoundTrip.V4_19.B_to_A [Morse.sum_critCount_eq_of_isMorseFunction_of_compactSpace,
  Morse.sum_critCount_eq_eulerNumberM, Morse.exists_eulerNumber_of_compactSpace,
  Morse.sum_critCount_of_finrank_eq_zero, Morse.IsEulerNumber.eq_eulerNumberM,
  Morse.eulerNumberM_eq_of_diffeomorph, Morse.exists_isEulerNumber_eulerNumberM]

end RoundTrip.V4_19
