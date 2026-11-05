import Morse
import RoundTrip.Check
import RoundTrip.Blind.V3_6

open Set Metric
open scoped ContDiff Manifold

noncomputable section

namespace RoundTrip.V3_6

/-- The project's statement (Reeb's theorem for compact slice submanifolds), universes
instantiated at `0`. -/
def A : Prop :=
  (type_of% @Morse.reeb.{0, 0, 0}) ∧ (type_of% @Morse.reeb_of_finrank_pos.{0, 0, 0}) ∧
  (type_of% @Morse.reeb_of_finrank_eq_zero.{0, 0, 0}) ∧ (type_of% @Morse.reeb_of_contMDiff)

theorem A_holds : A :=
  ⟨@Morse.reeb.{0, 0, 0}, @Morse.reeb_of_finrank_pos.{0, 0, 0},
    @Morse.reeb_of_finrank_eq_zero.{0, 0, 0}, @Morse.reeb_of_contMDiff⟩

/-- `A ⇒ B`: embed `M` as a compact slice submanifold `N ⊆ ℝᴷ⁺¹` (the project's Whitney embedding,
`Morse.exists_diffeomorph_sliceSubmanifold`, not part of this item) and transport `f`, its
critical points and their non-degeneracy along the diffeomorphism `M ≅ N`. -/
theorem A_to_B : A → B := by
  intro hA n M _ _ _ _ _ f p q hf hpq hp hq honly
  obtain ⟨K, m, N, hN, -, hNc, -, ⟨Φ⟩⟩ :=
    Morse.exists_diffeomorph_sliceSubmanifold (E := EuclideanSpace ℝ (Fin n)) (M := M) (n := n)
      finrank_euclideanSpace_fin
  let _ := hN.chartedSpace
  have := hN.isManifold
  let g : N → ℝ := f ∘ Φ.symm
  have hcritg : ∀ x : N, Morse.IsCriticalPointM (EuclideanSpace ℝ (Fin n)) g x ↔
      Φ.symm x = p ∨ Φ.symm x = q := by
    intro x
    rw [Morse.isCriticalPointM_comp_symm_iff Φ]
    exact ⟨honly _, by rintro (h | h) <;> rw [h]; exacts [hp.1, hq.1]⟩
  have hset : {x : N | Morse.IsCriticalPointM (EuclideanSpace ℝ (Fin n)) g x} = {Φ p, Φ q} := by
    ext x
    simp only [mem_ofPred_eq, hcritg, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro (h | h)
      · left; rw [← h]; simp
      · right; rw [← h]; simp
    · rintro (rfl | rfl) <;> simp
  have htwo : {x : N | Morse.IsCriticalPointM (EuclideanSpace ℝ (Fin n)) g x}.ncard = 2 := by
    rw [hset]
    exact ncard_pair (fun h => hpq (Φ.injective h))
  have hnd : ∀ x : N, Morse.IsCriticalPointM (EuclideanSpace ℝ (Fin n)) g x →
      Morse.IsNondegenerate (Morse.hessianM (EuclideanSpace ℝ (Fin n)) g x) := by
    intro x hx
    have hx' := (Morse.isCriticalPointM_comp_symm_iff Φ).1 hx
    refine (Morse.isNondegenerate_hessianM_comp_symm_iff Φ
      (hf.contMDiffAt.of_le (by norm_cast)) hx').2 ?_
    rcases honly _ hx' with h | h <;> rw [h]
    exacts [hp.2, hq.2]
  have hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ g := hf.comp Φ.symm.contMDiff
  cases n with
  | zero =>
    obtain ⟨e⟩ := hA.2.2.1 hN finrank_euclideanSpace_fin htwo
    exact ⟨Φ.toHomeomorph.trans e⟩
  | succ d =>
    obtain ⟨e⟩ := hA.2.2.2 hN hNc hg htwo hnd
    exact ⟨Φ.toHomeomorph.trans e⟩

#rt_check RoundTrip.V3_6.A_to_B [Morse.reeb, Morse.reeb_of_finrank_pos,
  Morse.reeb_of_finrank_eq_zero, Morse.reeb_of_contMDiff]

/-! ### `B ⇒ A`

Every case of `A` is about a compact slice submanifold `N` modelled on some `Z`. To apply `B`,
which wants a manifold modelled on `ℝⁿ`, re-embed `N` (as an abstract manifold modelled on `Z`)
by the project's Whitney embedding as a slice submanifold `N'` modelled on `ℝⁿ`, and transport `f`
along the diffeomorphism `N ≅ N'`. -/

section Core

variable {V Z W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup Z]
  [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}

theorem core (hB : B) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) [CompactSpace N] {n : ℕ}
    (hn : Module.finrank ℝ Z = n) {f : N → ℝ}
    (hf : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) ∞ f)
    (htwo : letI := hN.chartedSpace; {q : N | Morse.IsCriticalPointM Z f q}.ncard = 2)
    (hnd : letI := hN.chartedSpace; ∀ q : N, Morse.IsCriticalPointM Z f q →
      Morse.IsNondegenerate (Morse.hessianM Z f q)) :
    Nonempty (N ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  obtain ⟨K, m, N', hN', -, hN'c, -, ⟨Φ⟩⟩ :=
    Morse.exists_diffeomorph_sliceSubmanifold (E := Z) (M := N) hn
  let _ := hN'.chartedSpace
  have := hN'.isManifold
  have : CompactSpace N' := isCompact_iff_compactSpace.1 hN'c
  obtain ⟨p, q, hpq, hset⟩ := Set.ncard_eq_two.1 htwo
  have hcr : ∀ x, Morse.IsCriticalPointM Z f x ↔ x = p ∨ x = q := fun x => by
    have h := Set.ext_iff.1 hset x
    simpa using h
  have hnd' : ∀ x, x = p ∨ x = q →
      Morse.IsNondegenerateCriticalPointM (EuclideanSpace ℝ (Fin n)) (f ∘ Φ.symm) (Φ x) := by
    intro x hx
    rw [Morse.isNondegenerateCriticalPointM_comp_symm_iff Φ (by
      rw [Φ.symm_apply_apply]; exact hf.contMDiffAt.of_le (by norm_cast)), Φ.symm_apply_apply]
    have hc := (hcr x).2 hx
    exact ⟨hc, hnd x hc⟩
  obtain ⟨e⟩ := hB n N' (f ∘ Φ.symm) (Φ p) (Φ q) (hf.comp Φ.symm.contMDiff)
    (fun h => hpq (Φ.injective h)) (hnd' p (Or.inl rfl)) (hnd' q (Or.inr rfl)) (fun x hx => by
      rw [Morse.isCriticalPointM_comp_symm_iff Φ, hcr] at hx
      rcases hx with h | h
      · left; rw [← h]; simp
      · right; rw [← h]; simp)
  exact ⟨Φ.toHomeomorph.trans e⟩

end Core

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro V _ _ _ Z _ _ _ W _ _ N hN hNc n hn F hF htwo hnd
    have : CompactSpace N := isCompact_iff_compactSpace.1 hNc
    exact core hB hN hn (Morse.contMDiff_comp_val hN hF) htwo hnd
  · intro V _ _ _ Z _ _ _ W _ _ N hN hNc n hn _ F hF htwo hnd
    have : CompactSpace N := isCompact_iff_compactSpace.1 hNc
    exact core hB hN hn (Morse.contMDiff_comp_val hN hF) htwo hnd
  · intro V _ _ Z _ _ _ W _ _ N hN hZ f htwo
    let _ := hN.chartedSpace
    have hsub : Subsingleton Z := Module.finrank_zero_iff.1 hZ
    -- in dimension `0` every point is critical, so `N` has two points
    have hcrit : ∀ q : N, Morse.IsCriticalPointM Z f q := by
      intro q
      change mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) f q = 0
      ext v
      have hv : v = (0 : TangentSpace 𝓘(ℝ, Z) q) := Subsingleton.elim (α := Z) v 0
      rw [hv, map_zero, map_zero]
    have huniv : {q : N | Morse.IsCriticalPointM Z f q} = univ := eq_univ_of_forall hcrit
    have hfin : (univ : Set N).Finite := by
      rw [← huniv]
      exact Set.finite_of_ncard_pos (by rw [htwo]; norm_num)
    have : Finite N := Set.finite_univ_iff.1 hfin
    have : CompactSpace N := Finite.compactSpace
    -- every function is smooth, every Hessian non-degenerate
    have hf : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) ∞ f := by
      intro x
      rw [Morse.contMDiffAt_iff_contDiffAt_localRep]
      have : Morse.localRep Z f x = fun _ => Morse.localRep Z f x 0 :=
        funext fun z => congrArg _ (Subsingleton.elim z 0)
      rw [this]
      exact contDiffAt_const
    have hnd : ∀ q : N, Morse.IsCriticalPointM Z f q →
        Morse.IsNondegenerate (Morse.hessianM Z f q) := fun q _ =>
      Submodule.eq_bot_of_subsingleton
    obtain ⟨e⟩ := core hB hN hZ hf htwo hnd
    exact ⟨e⟩
  · intro K d m N hN hNc f hf htwo hnd
    have : CompactSpace N := isCompact_iff_compactSpace.1 hNc
    exact core hB hN finrank_euclideanSpace_fin hf htwo hnd

#rt_check RoundTrip.V3_6.B_to_A [Morse.reeb, Morse.reeb_of_finrank_pos,
  Morse.reeb_of_finrank_eq_zero, Morse.reeb_of_contMDiff]
#rt_overlap RoundTrip.V3_6.B_to_A [Morse.reeb, Morse.reeb_of_finrank_pos,
  Morse.reeb_of_finrank_eq_zero, Morse.reeb_of_contMDiff]

end RoundTrip.V3_6

end
