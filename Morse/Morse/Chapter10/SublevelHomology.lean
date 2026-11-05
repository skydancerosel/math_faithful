import Morse.Homology.MorseHomology

/-!
Milnor, *Morse Theory*, §17, p. 96 (the homology of the loop space of `Sⁿ`, read off from the
sublevel sets `Ω^a` of the energy) and §16, pp. 88–91 (the Morse theory of Part I applied to the
manifold `B` of broken geodesics, whose sublevel sets `B^a`, `a < c`, are compact while `B` is
not).

# Homology of an exhaustion, and slabs inside a compact sublevel set

## What is proved here

### Singular homology commutes with exhaustions

Let `𝕜` be a field, `X` a space and `A_0 ⊆ A_1 ⊆ ⋯` subsets of a subset `B ⊆ X` (for instance
`B = X`) such that every compact subset of `B` lies in some `A_k`.

* `Morse.Homology.subsingleton_subsetHomology_of_exhaustion` (`..._univ_of_exhaustion` for
  `B = X`): if `H_j(A_k, A_{k₀}; 𝕜) = 0` for every `k ≥ k₀`, then `H_j(B, A_{k₀}; 𝕜) = 0`.  A
  relative cycle of `(B, A_{k₀})` is a finite combination of singular simplices, whose images are
  compact, so it is a relative cycle of some `(A_k, A_{k₀})`; it bounds there, hence in
  `(B, A_{k₀})`.  The chain-level statement is `Morse.Homology.exactAt_of_injective_of_exists`: a
  complex exhausted by subcomplexes that are exact in degree `j` is exact in degree `j`.  It is
  applied to the concrete quotients `C(A_k) / C(A_{k₀}) ⟶ C(B) / C(A_{k₀})` of
  `Morse/Homology/Excision.lean` (`Morse.Homology.subsingleton_subsetHomology_iff_exactAt`).
* `Morse.Homology.subsingleton_subsetHomology_of_steps`: the hypothesis follows from the vanishing
  of the steps `H_j(A_{k+1}, A_k; 𝕜)`, `k ≥ k₀`.
* `Morse.Homology.spaceHomologyEquivOfExhaustion`,
  `Morse.Homology.nonempty_linearEquiv_spaceHomology_of_exhaustion`: if the groups
  `H_*(A_k, A_{k₀}; 𝕜)` vanish in degrees `i` and `i + 1`, the inclusion induces
  `H_i(A_{k₀}, ∅; 𝕜) ≅ H_i(X; 𝕜)` (exact sequence of the triple `∅ ⊆ A_{k₀} ⊆ X`);
  `Morse.Homology.spaceHomologyEquivOfExhaustion'` is the version with `H_i(A_{k₀}; 𝕜)`,
  `Morse.Homology.bettiNumber_eq_of_exhaustion` and
  `Morse.Homology.finiteDimensional_spaceHomology_of_exhaustion` the consequences for dimensions,
  and `Morse.Homology.spaceHomologyEquivOfSteps`, `Morse.Homology.bettiNumber_eq_of_steps` the
  versions with hypotheses on the steps only.
* `Morse.Homology.exists_subset_sublevel_of_isCompact`: the sublevel sets `X^{a_k}` of a
  continuous function, for levels `a_k` unbounded above, exhaust the compact sets.  For the path
  space with Milnor's metric the energy is continuous (`Morse.PathSp.continuous_energy`).

### The homology of a slab inside a compact sublevel set

`Morse.Homology.sublevel_step_critical_of_isCompact` and
`Morse.Homology.sublevel_step_of_isCompact` are `Morse.Homology.sublevel_step_critical` and
`Morse.Homology.sublevel_step` (`Morse/Homology/MorseHomology.lean`) for a slice submanifold
`N ⊆ V` that need not be compact, when the sublevel set `N^{a₀}` is compact and the slab lies below
`a₀`.  Every slab `f⁻¹[b, b']` with `b' ≤ a₀` is then a closed subset of the compact `N^{a₀}`,
which is all that Theorem 3.1 (`Morse.theorem_3_1_submanifold`) and Remark 3.3
(`Morse.remark_3_3_submanifold`) need.  Only the critical points in `N^{a₀}` are assumed
non-degenerate, and the finite set `P` of `sublevel_step_of_isCompact` only has to consist of the
critical points with value `≤ a` (there may be infinitely many critical points above `a₀`).  The
homotopy-type counterpart is `Morse.IsFiniteCellComplexType.sublevel_step_of_isCompact`
(`Morse/Chapter10/SublevelCW.lean`).

## References

* J. Milnor, *Morse Theory*, §16 (pp. 88–91) and §17 (p. 96).
* A. Hatcher, *Algebraic Topology*: the exact sequence of a triple (§2.1), and the homology of a
  directed union in which every compact set lies in some member (§3.3, Prop. 3.33).

## What Milnor's text leaves implicit

* **From the `Ω^a` to `Ω`.**  Milnor reads off `H_*(ΩSⁿ)` (p. 96) from the cell structure of
  Theorem 17.3, which gives all of `Ω` the homotopy type of a countable CW complex by an argument
  about the homotopy type of an increasing union; how the homology of the `Ω^a` determines that of
  `Ω` is not discussed.  (In this project the topological part of Theorem 17.3,
  `Morse.isCountableCellComplexType_of_sublevel`, gives `Ω` the homotopy type of a mapping
  telescope of finite cell complexes, whose homology is not computed.)  For homology no cell
  structure on `Ω` is needed: singular chains have compact supports, so `H_i(Ω^a) ≅ H_i(Ω)` as
  soon as the pairs `(Ω^{a'}, Ω^a)`, `a' ≥ a`, have no homology in degrees `i` and `i + 1`
  (`Morse.Homology.spaceHomologyEquivOfExhaustion`).  The cellular homology of an infinite CW
  complex rests on the same compactness.
* **Compact subsets of `Ω` have bounded energy.**  This is where the topology of `Ω` enters: every
  compact subset of `Ω` must lie in some `Ω^a`.  It holds for Milnor's metric `d` (p. 88), for
  which the energy is continuous; for the topology of uniform convergence alone, in which the
  energy is only lower semicontinuous, it fails (a uniformly convergent sequence of paths whose
  energies tend to `∞`, together with its limit, is compact).
* **Both degrees, and all pairs.**  The cells give the homology of each step
  `(Ω^{a_{k+1}}, Ω^{a_k})`.  The vanishing for all pairs `(Ω^{a_k}, Ω^{a_{k₀}})` is an induction
  along the exact sequences of triples (`Morse.Homology.subsingleton_subsetHomology_of_steps`),
  and it is needed in degree `i + 1` (injectivity of `H_i(Ω^{a_{k₀}}) → H_i(Ω)`) as well as in
  degree `i` (surjectivity).
* **`B` is not compact.**  Part I computes the homology of a slab (p. 29) on a compact manifold,
  and Milnor applies Part I to `E'` on `B` (p. 90), of which only the sublevel sets `B^a`, `a < c`,
  are compact.  Theorems 3.1 and 3.2 and Remark 3.3 only involve compact slabs, so the computation
  goes through below any level `a₀` with `B^{a₀}` compact, under assumptions on the critical
  points in `B^{a₀}` only.
-/

open CategoryTheory Limits AlgebraicTopology HomologicalComplex Module Set Topology
open scoped ContDiff Manifold

universe u v

noncomputable section

/-! ### Long exact sequences -/

namespace Morse

section LongExactSeq

variable {F : Type*} [Field F] {A B C : ℕ → Type*}
  [∀ i, AddCommGroup (A i)] [∀ i, Module F (A i)]
  [∀ i, AddCommGroup (B i)] [∀ i, Module F (B i)]
  [∀ i, AddCommGroup (C i)] [∀ i, Module F (C i)]

/-- In a long exact sequence `⋯ → A i → B i → C i → A (i - 1) → ⋯`, the map `A i → B i` is
bijective when `C i` and `C (i + 1)` vanish. -/
theorem LongExactSeq.bijective_f_of_subsingleton (E : LongExactSeq F A B C) {i : ℕ}
    (h0 : Subsingleton (C i)) (h1 : Subsingleton (C (i + 1))) : Function.Bijective (E.f i) := by
  refine ⟨(injective_iff_map_eq_zero (E.f i)).2 fun a ha ↦ ?_, fun b ↦ ?_⟩
  · obtain ⟨c, rfl⟩ := (E.exact_δ_f i a).1 ha
    rw [Subsingleton.elim c 0, map_zero]
  · exact (E.exact_f_g i b).1 (Subsingleton.elim _ _)

/-- In a long exact sequence, `B i` vanishes when `A i` and `C i` do. -/
theorem LongExactSeq.subsingleton_B (E : LongExactSeq F A B C) {i : ℕ}
    (hA : Subsingleton (A i)) (hC : Subsingleton (C i)) : Subsingleton (B i) := by
  refine ⟨fun b b' ↦ ?_⟩
  have h : ∀ b : B i, b = 0 := fun b ↦ by
    obtain ⟨a, rfl⟩ := (E.exact_f_g i b).1 (Subsingleton.elim _ _)
    rw [Subsingleton.elim a 0, map_zero]
  rw [h b, h b']

end LongExactSeq

end Morse

namespace Morse.Homology

/-! ### Exactness of an exhausted complex -/

section Abstract

variable {R : Type*} [Ring R] {ι : Type*}

/-- **Exactness passes to an exhausted complex.**  Let `φ_k : Q_k ⟶ Q` be degreewise injective
chain maps of complexes of modules such that every chain of `Q` in degree `j` comes from some
`Q_k`.  If every `Q_k` is exact in degree `j`, so is `Q`. -/
theorem exactAt_of_injective_of_exists {Q : ChainComplex (ModuleCat R) ℕ}
    {Qk : ι → ChainComplex (ModuleCat R) ℕ} (φ : ∀ k, Qk k ⟶ Q)
    (hinj : ∀ k n, Function.Injective ((φ k).f n)) {j : ℕ}
    (hsurj : ∀ x : Q.X j, ∃ k, ∃ y, (φ k).f j y = x) (hex : ∀ k, (Qk k).ExactAt j) :
    Q.ExactAt j := by
  rw [HomologicalComplex.exactAt_iff, ShortComplex.moduleCat_exact_iff]
  intro x hx
  obtain ⟨k, y, rfl⟩ := hsurj x
  -- `y` is a cycle of `Q_k`, since `φ_k` is injective
  have hy : (Qk k).d j ((ComplexShape.down ℕ).next j) y = 0 := by
    apply hinj k
    rw [map_zero, ← ModuleCat.comp_apply, ← (φ k).comm, ModuleCat.comp_apply]
    exact hx
  have h := hex k
  rw [HomologicalComplex.exactAt_iff, ShortComplex.moduleCat_exact_iff] at h
  -- it bounds in `Q_k`, hence in `Q`
  obtain ⟨z, hz⟩ := h y hy
  refine ⟨(φ k).f ((ComplexShape.down ℕ).prev j) z, ?_⟩
  have hc := ConcreteCategory.congr_hom ((φ k).comm ((ComplexShape.down ℕ).prev j) j) z
  exact hc.trans (congrArg ((φ k).f j) hz)

end Abstract

/-! ### Homology of an exhaustion -/

section Exhaustion

variable {𝕜 : Type u} [Field 𝕜] {X : Type u} [TopologicalSpace X]

/-- `H_j(B, A; 𝕜) = 0` iff the concrete quotient complex `C(B) / C_S(B)` (the chains of `B` modulo
those made of simplices in `S`) is exact in degree `j`, where `S ⊆ B` is the image of `A`. -/
theorem subsingleton_subsetHomology_iff_exactAt {A B : Set X} (h : A ⊆ B) {S : Set B}
    (hS : range (Set.inclusion h) = S) (j : ℕ) :
    Subsingleton (subsetHomology 𝕜 j h) ↔ (quotChains 𝕜 (isPrecompClosed_inSet S)).ExactAt j := by
  rw [← ModuleCat.isZero_iff_subsingleton, HomologicalComplex.exactAt_iff_isZero_homology]
  exact Iso.isZero_iff
    (HomologicalComplex.homologyMapIso (relChainsIsoQuot 𝕜 (subsetPair h) S hS) j)

/-- **Homology commutes with exhaustions, relative form** (compact supports; Hatcher Prop. 3.33).
Let `A_0 ⊆ A_1 ⊆ ⋯ ⊆ B` be subsets of a space such that every compact subset of `B` lies in some
`A_k`.  If `H_j(A_k, A_{k₀}; 𝕜) = 0` for all `k ≥ k₀`, then `H_j(B, A_{k₀}; 𝕜) = 0`: a relative
cycle of `(B, A_{k₀})` is a relative cycle of some `(A_k, A_{k₀})`, where it bounds. -/
theorem subsingleton_subsetHomology_of_exhaustion {B : Set X} {A : ℕ → Set X} (hA : Monotone A)
    (hAB : ∀ k, A k ⊆ B) (hcpt : ∀ K ⊆ B, IsCompact K → ∃ k, K ⊆ A k) {j k₀ : ℕ}
    (hrel : ∀ k (hk : k₀ ≤ k), Subsingleton (subsetHomology 𝕜 j (hA hk))) :
    Subsingleton (subsetHomology 𝕜 j (hAB k₀)) := by
  -- the image `S` of `A k₀` in `B`, and the inclusions `A k ↪ B`
  set S : Set B := (↑) ⁻¹' A k₀ with hS_def
  let ι : ∀ k, C(A k, B) := fun k ↦ ⟨Set.inclusion (hAB k), continuous_inclusion (hAB k)⟩
  have hι : ∀ k, IsEmbedding (ι k) := fun k ↦ IsEmbedding.inclusion (hAB k)
  rw [subsingleton_subsetHomology_iff_exactAt (hAB k₀) (S := S) (by rw [range_inclusion]; rfl)]
  refine exactAt_of_injective_of_exists (ι := {k // k₀ ≤ k})
    (fun k ↦ excisionMap 𝕜 S (ι k)) ?_ ?_ fun k ↦ ?_
  · -- `C(A k) / C(A k₀) ⟶ C(B) / C(A k₀)` is injective
    intro k n
    rw [← LinearMap.ker_eq_bot (f := ((excisionMap 𝕜 S (ι k)).f n).hom), eq_bot_iff]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H c =>
      rw [LinearMap.mem_ker] at hx
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      exact (push_mem_supported_iff (hι k).injective S c).1
        ((Submodule.Quotient.mk_eq_zero _).1 hx)
  · -- every chain of `B` is a chain of some `A k`: its simplices have compact images
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H c =>
      have hK : IsCompact (⋃ σ ∈ c.support, (Subtype.val : B → X) '' range σ) :=
        c.support.isCompact_biUnion fun σ _ ↦
          (isCompact_range σ.continuous).image continuous_subtype_val
      obtain ⟨k, hk⟩ := hcpt _ (iUnion₂_subset fun σ _ ↦ by rintro _ ⟨y, -, rfl⟩; exact y.2) hK
      set k' : {k // k₀ ≤ k} := ⟨max k k₀, le_max_right _ _⟩
      have hc : c ∈ LinearMap.range (push (R := 𝕜) (ι k') j) := by
        rw [range_push (hι k'), Finsupp.mem_supported]
        intro σ hσ
        rintro _ ⟨t, rfl⟩
        change σ t ∈ range (Set.inclusion (hAB _))
        rw [range_inclusion]
        exact hA (le_max_left k k₀) (hk (mem_biUnion hσ ⟨σ t, ⟨t, rfl⟩, rfl⟩))
      obtain ⟨c', rfl⟩ := hc
      exact ⟨k', Submodule.Quotient.mk c', rfl⟩
  · -- `C(A k) / C(A k₀)` is exact in degree `j`
    exact (subsingleton_subsetHomology_iff_exactAt (hA k.2) (S := ι k ⁻¹' S)
      (by rw [range_inclusion]; rfl) j).1 (hrel k k.2)

/-- **Homology commutes with exhaustions, relative form**, for an exhaustion of the whole space:
if every compact subset of `X` lies in some `A_k` and `H_j(A_k, A_{k₀}; 𝕜) = 0` for all `k ≥ k₀`,
then `H_j(X, A_{k₀}; 𝕜) = 0`. -/
theorem subsingleton_subsetHomology_univ_of_exhaustion {A : ℕ → Set X} (hA : Monotone A)
    (hcpt : ∀ K : Set X, IsCompact K → ∃ k, K ⊆ A k) {j k₀ : ℕ}
    (hrel : ∀ k (hk : k₀ ≤ k), Subsingleton (subsetHomology 𝕜 j (hA hk))) :
    Subsingleton (subsetHomology 𝕜 j (subset_univ (A k₀))) :=
  subsingleton_subsetHomology_of_exhaustion hA (fun k ↦ subset_univ (A k))
    (fun K _ hK ↦ hcpt K hK) hrel

/-- **From the steps to all pairs**: if `H_j(A_{k+1}, A_k; 𝕜) = 0` for every `k ≥ k₀`, then
`H_j(A_k, A_{k₀}; 𝕜) = 0` for every `k ≥ k₀` (exact sequences of the triples
`A_{k₀} ⊆ A_k ⊆ A_{k+1}`). -/
theorem subsingleton_subsetHomology_of_steps {A : ℕ → Set X} (hA : Monotone A) {j k₀ : ℕ}
    (hstep : ∀ k, k₀ ≤ k → Subsingleton (subsetHomology 𝕜 j (hA (Nat.le_succ k)))) :
    ∀ k (hk : k₀ ≤ k), Subsingleton (subsetHomology 𝕜 j (hA hk)) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact subsingleton_subsetHomology_self j (A k₀)
  | succ k hk ih =>
    exact (subsetTripleLongExactSeq 𝕜 (hA hk) (hA (Nat.le_succ k))).subsingleton_B ih
      (hstep k hk)

/-- `H_i(A, ∅; 𝕜) ≅ H_i(A; 𝕜)` for a subset `A` of a space. -/
def subsetHomologyEmptyEquiv (A : Set X) (i : ℕ) :
    subsetHomology 𝕜 i (empty_subset A) ≃ₗ[𝕜] spaceHomology 𝕜 i A :=
  (asIso (homologyMap (relπ (ModuleCat.of 𝕜 𝕜) (subsetPair (empty_subset A))) i)).symm.toLinearEquiv

/-- **The homology of an exhaustion**: if `H_i` and `H_{i+1}` of the pairs `(A_k, A_{k₀})`,
`k ≥ k₀`, vanish, then the inclusion induces `H_i(A_{k₀}, ∅; 𝕜) ≅ H_i(B, ∅; 𝕜)` (exact sequence
of the triple `∅ ⊆ A_{k₀} ⊆ B`, whose third terms vanish by
`Morse.Homology.subsingleton_subsetHomology_of_exhaustion`). -/
def subsetHomologyEquivOfExhaustion {B : Set X} {A : ℕ → Set X} (hA : Monotone A)
    (hAB : ∀ k, A k ⊆ B) (hcpt : ∀ K ⊆ B, IsCompact K → ∃ k, K ⊆ A k) {i k₀ : ℕ}
    (h0 : ∀ k (hk : k₀ ≤ k), Subsingleton (subsetHomology 𝕜 i (hA hk)))
    (h1 : ∀ k (hk : k₀ ≤ k), Subsingleton (subsetHomology 𝕜 (i + 1) (hA hk))) :
    subsetHomology 𝕜 i (empty_subset (A k₀)) ≃ₗ[𝕜] subsetHomology 𝕜 i (empty_subset B) :=
  LinearEquiv.ofBijective ((subsetTripleLongExactSeq 𝕜 (empty_subset (A k₀)) (hAB k₀)).f i)
    ((subsetTripleLongExactSeq 𝕜 (empty_subset (A k₀)) (hAB k₀)).bijective_f_of_subsingleton
      (subsingleton_subsetHomology_of_exhaustion hA hAB hcpt h0)
      (subsingleton_subsetHomology_of_exhaustion hA hAB hcpt h1))

/-- **The homology of an exhausted space** (Milnor p. 96, from the `Ω^a` to `Ω`): if every compact
subset of `X` lies in some `A_k` and `H_i`, `H_{i+1}` of the pairs `(A_k, A_{k₀})`, `k ≥ k₀`,
vanish, then the inclusion induces `H_i(A_{k₀}, ∅; 𝕜) ≅ H_i(X; 𝕜)`. -/
def spaceHomologyEquivOfExhaustion {A : ℕ → Set X} (hA : Monotone A)
    (hcpt : ∀ K : Set X, IsCompact K → ∃ k, K ⊆ A k) {i k₀ : ℕ}
    (h0 : ∀ k (hk : k₀ ≤ k), Subsingleton (subsetHomology 𝕜 i (hA hk)))
    (h1 : ∀ k (hk : k₀ ≤ k), Subsingleton (subsetHomology 𝕜 (i + 1) (hA hk))) :
    subsetHomology 𝕜 i (empty_subset (A k₀)) ≃ₗ[𝕜] spaceHomology 𝕜 i X :=
  (subsetHomologyEquivOfExhaustion hA (fun k ↦ subset_univ (A k)) (fun K _ hK ↦ hcpt K hK) h0
    h1).trans (subsetHomologyUnivEquiv X i)

/-- **The homology of an exhausted space** (Milnor p. 96): `H_i(A_{k₀}, ∅; 𝕜) ≅ H_i(X; 𝕜)` when
every compact subset of `X` lies in some `A_k` and `H_i`, `H_{i+1}` of the pairs `(A_k, A_{k₀})`,
`k ≥ k₀`, vanish. -/
theorem nonempty_linearEquiv_spaceHomology_of_exhaustion {A : ℕ → Set X} (hA : Monotone A)
    (hcpt : ∀ K : Set X, IsCompact K → ∃ k, K ⊆ A k) {i k₀ : ℕ}
    (h0 : ∀ k (hk : k₀ ≤ k), Subsingleton (subsetHomology 𝕜 i (hA hk)))
    (h1 : ∀ k (hk : k₀ ≤ k), Subsingleton (subsetHomology 𝕜 (i + 1) (hA hk))) :
    Nonempty (subsetHomology 𝕜 i (empty_subset (A k₀)) ≃ₗ[𝕜] spaceHomology 𝕜 i X) :=
  ⟨spaceHomologyEquivOfExhaustion hA hcpt h0 h1⟩

/-- `Morse.Homology.spaceHomologyEquivOfExhaustion` with the absolute homology `H_i(A_{k₀}; 𝕜)`
of the subspace `A_{k₀}`. -/
def spaceHomologyEquivOfExhaustion' {A : ℕ → Set X} (hA : Monotone A)
    (hcpt : ∀ K : Set X, IsCompact K → ∃ k, K ⊆ A k) {i k₀ : ℕ}
    (h0 : ∀ k (hk : k₀ ≤ k), Subsingleton (subsetHomology 𝕜 i (hA hk)))
    (h1 : ∀ k (hk : k₀ ≤ k), Subsingleton (subsetHomology 𝕜 (i + 1) (hA hk))) :
    spaceHomology 𝕜 i (A k₀) ≃ₗ[𝕜] spaceHomology 𝕜 i X :=
  (subsetHomologyEmptyEquiv (A k₀) i).symm.trans (spaceHomologyEquivOfExhaustion hA hcpt h0 h1)

/-- **Betti numbers of an exhausted space**: `b_i(X) = dim H_i(A_{k₀}, ∅; 𝕜)` under the hypotheses
of `Morse.Homology.spaceHomologyEquivOfExhaustion`. -/
theorem bettiNumber_eq_of_exhaustion {A : ℕ → Set X} (hA : Monotone A)
    (hcpt : ∀ K : Set X, IsCompact K → ∃ k, K ⊆ A k) {i k₀ : ℕ}
    (h0 : ∀ k (hk : k₀ ≤ k), Subsingleton (subsetHomology 𝕜 i (hA hk)))
    (h1 : ∀ k (hk : k₀ ≤ k), Subsingleton (subsetHomology 𝕜 (i + 1) (hA hk))) :
    bettiNumber 𝕜 X i = finrank 𝕜 (subsetHomology 𝕜 i (empty_subset (A k₀))) :=
  (spaceHomologyEquivOfExhaustion hA hcpt h0 h1).finrank_eq.symm

/-- `H_i(X; 𝕜)` is finite-dimensional if `H_i(A_{k₀}, ∅; 𝕜)` is, under the hypotheses of
`Morse.Homology.spaceHomologyEquivOfExhaustion`. -/
theorem finiteDimensional_spaceHomology_of_exhaustion {A : ℕ → Set X} (hA : Monotone A)
    (hcpt : ∀ K : Set X, IsCompact K → ∃ k, K ⊆ A k) {i k₀ : ℕ}
    (h0 : ∀ k (hk : k₀ ≤ k), Subsingleton (subsetHomology 𝕜 i (hA hk)))
    (h1 : ∀ k (hk : k₀ ≤ k), Subsingleton (subsetHomology 𝕜 (i + 1) (hA hk)))
    [FiniteDimensional 𝕜 (subsetHomology 𝕜 i (empty_subset (A k₀)))] :
    FiniteDimensional 𝕜 (spaceHomology 𝕜 i X) :=
  (spaceHomologyEquivOfExhaustion hA hcpt h0 h1).finiteDimensional

/-- **The homology of an exhausted space, from the steps**: if every compact subset of `X` lies in
some `A_k` and the steps `(A_{k+1}, A_k)`, `k ≥ k₀`, have no homology in degrees `i` and `i + 1`,
then the inclusion induces `H_i(A_{k₀}, ∅; 𝕜) ≅ H_i(X; 𝕜)`. -/
def spaceHomologyEquivOfSteps {A : ℕ → Set X} (hA : Monotone A)
    (hcpt : ∀ K : Set X, IsCompact K → ∃ k, K ⊆ A k) {i k₀ : ℕ}
    (h0 : ∀ k, k₀ ≤ k → Subsingleton (subsetHomology 𝕜 i (hA (Nat.le_succ k))))
    (h1 : ∀ k, k₀ ≤ k → Subsingleton (subsetHomology 𝕜 (i + 1) (hA (Nat.le_succ k)))) :
    subsetHomology 𝕜 i (empty_subset (A k₀)) ≃ₗ[𝕜] spaceHomology 𝕜 i X :=
  spaceHomologyEquivOfExhaustion hA hcpt (subsingleton_subsetHomology_of_steps hA h0)
    (subsingleton_subsetHomology_of_steps hA h1)

/-- `b_i(X) = dim H_i(A_{k₀}, ∅; 𝕜)` under the hypotheses of
`Morse.Homology.spaceHomologyEquivOfSteps`. -/
theorem bettiNumber_eq_of_steps {A : ℕ → Set X} (hA : Monotone A)
    (hcpt : ∀ K : Set X, IsCompact K → ∃ k, K ⊆ A k) {i k₀ : ℕ}
    (h0 : ∀ k, k₀ ≤ k → Subsingleton (subsetHomology 𝕜 i (hA (Nat.le_succ k))))
    (h1 : ∀ k, k₀ ≤ k → Subsingleton (subsetHomology 𝕜 (i + 1) (hA (Nat.le_succ k)))) :
    bettiNumber 𝕜 X i = finrank 𝕜 (subsetHomology 𝕜 i (empty_subset (A k₀))) :=
  (spaceHomologyEquivOfSteps hA hcpt h0 h1).finrank_eq.symm

/-- The sublevel sets `X^{a_k}` of a continuous function along levels `a_k` that are unbounded
above exhaust the compact sets (the hypothesis of the theorems above for `A_k = X^{a_k}`). -/
theorem exists_subset_sublevel_of_isCompact {f : X → ℝ} (hf : Continuous f) {a : ℕ → ℝ}
    (ha : ∀ r, ∃ k, r ≤ a k) {K : Set X} (hK : IsCompact K) : ∃ k, K ⊆ sublevel f (a k) := by
  obtain ⟨M, hM⟩ := hK.bddAbove_image hf.continuousOn
  obtain ⟨k, hk⟩ := ha M
  exact ⟨k, fun x hx ↦ (hM (mem_image_of_mem f hx)).trans hk⟩

end Exhaustion

/-! ### The homology of a slab inside a compact sublevel set -/

section Submanifold

open Finset

variable {𝕜 : Type u} [Field 𝕜]
  {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set V} {T : Type u} [TopologicalSpace T]

/-- **One critical level inside a compact sublevel set** (Milnor p. 29, with Remark 3.3, for the
manifold `B` of §16): `Morse.Homology.sublevel_step_critical` for a slice submanifold `N` that need
not be compact, when `N^{a₀}` is compact and `a ≤ a₀`.  Let `S` be a finite set of non-degenerate
critical points of `f = F|N`, all on the level `c`, and `a' < c < a ≤ a₀` such that no other
critical value lies in `[a', a]`.  Then `H_i(N^a, N^{a'}; 𝕜)` (read in a space `T` homeomorphic to
`N`) is finite-dimensional, of dimension the number of points of `S` of index `i`.  The slabs
below `a₀` are closed subsets of the compact `N^{a₀}`, so Remark 3.3 and Theorem 3.1 apply. -/
theorem sublevel_step_critical_of_isCompact (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    {F : V → ℝ} (hF : ContDiff ℝ ∞ F) (e : T ≃ₜ N) {a₀ : ℝ}
    (hK : IsCompact ((F ∘ Subtype.val : N → ℝ) ⁻¹' Iic a₀)) {S : Finset N} {c : ℝ}
    (hS : letI := hN.chartedSpace;
      ∀ p ∈ S, IsNondegenerateCriticalPointM Z (F ∘ Subtype.val) p ∧ F p = c)
    {a' a : ℝ} (ha' : a' < c) (ha : c < a) (haa₀ : a ≤ a₀)
    (hother : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q → q ∉ S →
      F q < a' ∨ a < F q) (i : ℕ) :
    letI := hN.chartedSpace
    FiniteDimensional 𝕜 (subsetHomology 𝕜 i (preimage_mono (f := e)
        (sublevel_mono (F ∘ Subtype.val : N → ℝ) (ha'.trans ha).le))) ∧
      finrank 𝕜 (subsetHomology 𝕜 i (preimage_mono (f := e)
        (sublevel_mono (F ∘ Subtype.val : N → ℝ) (ha'.trans ha).le))) =
        #{p ∈ S | indexM Z (F ∘ Subtype.val) p = i} := by
  classical
  let _ := hN.chartedSpace
  -- `N` is a subspace of a normed space, hence Hausdorff
  have : T2Space T := e.isEmbedding.t2Space
  set f : N → ℝ := F ∘ Subtype.val with hf_def
  have hfc : Continuous f := hF.continuous.comp continuous_subtype_val
  -- every slab below `a₀` is compact
  have hslab : ∀ b b' : ℝ, b' ≤ a₀ → IsCompact (f ⁻¹' Icc b b') := fun b b' hb' ↦
    hK.of_isClosed_subset (isClosed_Icc.preimage hfc) fun q hq ↦ (hq.2.trans hb' : f q ≤ a₀)
  set ε₀ := min (c - a') (a - c) with hε₀_def
  have hε₀ : 0 < ε₀ := lt_min (by linarith) (by linarith)
  have hKε : IsCompact (f ⁻¹' Icc (c - ε₀) (c + ε₀)) :=
    hslab _ _ (by linarith [min_le_right (c - a') (a - c)])
  have honly : ∀ q : N, F q ∈ Icc (c - ε₀) (c + ε₀) → IsCriticalPointM Z f q → q ∈ S := by
    intro q hq hc
    by_contra hqS
    rcases hother q hc hqS with h1 | h1
    · linarith [hq.1, min_le_left (c - a') (a - c)]
    · linarith [hq.2, min_le_right (c - a') (a - c)]
  -- Remark 3.3 at the level `c`
  obtain ⟨ε₁, hε₁, H⟩ := remark_3_3_submanifold hN hF S hS hε₀ hKε honly
  set ε := min ε₁ (ε₀ / 2) with hε_def
  have hε : 0 < ε := lt_min hε₁ (by linarith)
  have hεε₀ : ε < ε₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have h1 : ε < c - a' := lt_of_lt_of_le hεε₀ (min_le_left _ _)
  have h2 : ε < a - c := lt_of_lt_of_le hεε₀ (min_le_right _ _)
  obtain ⟨χ, hprops, hdisj, hsdr⟩ := H ε hε (min_le_left _ _)
  -- Theorem 3.1 on the compact slabs `[a', c - ε]` and `[c + ε, a]`
  have hno : ∀ {b b' : ℝ}, a' ≤ b → b' ≤ a → (b' < c ∨ c < b) →
      ∀ q : N, F q ∈ Icc b b' → ¬IsCriticalPointM Z f q := by
    intro b b' hb hb' hbp q hq hc
    by_cases hqS : q ∈ S
    · have := (hS q hqS).2
      rcases hbp with h | h <;> linarith [hq.1, hq.2]
    · rcases hother q hc hqS with h | h <;> linarith [hq.1, hq.2]
  have hsdr₁ := (theorem_3_1_submanifold hN hF (a := a') (b := c - ε) (by linarith)
    (hslab _ _ (by linarith)) (hno le_rfl (by linarith) (Or.inl (by linarith)))).2.1
  have hsdr₂ := (theorem_3_1_submanifold hN hF (a := c + ε) (b := a) (by linarith)
    (hslab _ _ haa₀) (hno (by linarith) le_rfl (Or.inr (by linarith)))).2.1
  -- the cells, indexed by `Fin #S` and carried to `T`
  set σ : Fin #S ≃ S := S.equivFin.symm with hσ
  set χ' : (j : Fin #S) → EuclideanSpace ℝ (Fin (indexM Z f (σ j))) → T :=
    fun j z ↦ e.symm (χ (σ j) z) with hχ'
  have himage : ∀ j, χ' j '' Metric.closedBall 0 1 = e ⁻¹' (χ (σ j) '' Metric.closedBall 0 1) :=
    fun j ↦ by rw [← e.image_symm, ← image_comp]; rfl
  have hunion : e ⁻¹' (sublevel f (c - ε) ∪ ⋃ p, χ p '' Metric.closedBall 0 1) =
      e ⁻¹' sublevel f (c - ε) ∪ ⋃ j, χ' j '' Metric.closedBall 0 1 := by
    rw [preimage_union, preimage_iUnion]
    congr 1
    simp only [himage]
    exact (σ.surjective.iUnion_comp fun p ↦ e ⁻¹' (χ p '' Metric.closedBall 0 1)).symm
  have hcells := finrank_subsetHomology_of_cells (𝕜 := 𝕜) (cellAttachHomology 𝕜) (χ := χ')
    (A := e ⁻¹' sublevel f a') (B := e ⁻¹' sublevel f (c - ε)) (X' := e ⁻¹' sublevel f (c + ε))
    (X := e ⁻¹' sublevel f a)
    ((isClosed_le hfc continuous_const).preimage e.continuous)
    (fun j ↦ ⟨e.symm.continuous.comp_continuousOn (hprops (σ j)).1,
      e.symm.injective.comp_injOn (hprops (σ j)).2.1, fun z hz ↦ by
        change e (e.symm (χ (σ j) z)) ∈ sublevel f (c - ε) ↔ _
        rw [e.apply_symm_apply]
        exact (hprops (σ j)).2.2.1 z hz⟩)
    (fun j j' hjj' ↦ by
      dsimp only
      rw [himage, himage]
      exact ((hdisj (σ.injective.ne hjj')).preimage e))
    (preimage_mono (sublevel_mono f (by linarith)))
    (by
      rw [← hunion]
      exact preimage_mono (union_subset (sublevel_mono f (by linarith))
        (iUnion_subset fun p ↦ (hprops p).2.2.2)))
    (preimage_mono (sublevel_mono f (by linarith)))
    (hsdr₁.preimage_subtype e) (by rw [← hunion]; exact hsdr.preimage_subtype e)
    (hsdr₂.preimage_subtype e)
    (preimage_mono (sublevel_mono f (ha'.trans ha).le)) i
  refine ⟨hcells.1, hcells.2.trans ?_⟩
  rw [card_filter_equiv σ (fun p : S ↦ indexM Z f p = i), Finset.card_filter, Finset.card_filter,
    ← Finset.sum_attach S]
  rfl

/-- **The homology of a slab inside a compact sublevel set** (Milnor p. 29, for the manifold `B`
of §16): `Morse.Homology.sublevel_step` for a slice submanifold `N` that need not be compact, when
`N^{a₀}` is compact and `a ≤ a₀`.  Assume that the critical points of `f = F|N` in `N^{a₀}` are
non-degenerate, that `P` is a finite set whose points with value `≤ a` are exactly the critical
points with value `≤ a` (for instance the critical points in `N^{a₀}`), that `a' ≤ a` are regular
values and that all critical values in `(a', a)` are equal.  Then `H_i(N^a, N^{a'}; 𝕜)` is
finite-dimensional, of dimension the number of critical points of index `i` in `f⁻¹(a', a)`. -/
theorem sublevel_step_of_isCompact (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    {F : V → ℝ} (hF : ContDiff ℝ ∞ F) {a₀ : ℝ}
    (hK : IsCompact ((F ∘ Subtype.val : N → ℝ) ⁻¹' Iic a₀))
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q → F q ≤ a₀ →
      IsNondegenerate (hessianM Z (F ∘ Subtype.val) q)) (e : T ≃ₜ N) {P : Finset N}
    {a' a : ℝ} (haa : a' ≤ a) (haa₀ : a ≤ a₀)
    (hP : letI := hN.chartedSpace;
      ∀ q : N, F q ≤ a → (q ∈ P ↔ IsCriticalPointM Z (F ∘ Subtype.val) q))
    (ha' : ∀ q ∈ P, F q ≠ a') (ha : ∀ q ∈ P, F q ≠ a)
    (hone : ∀ q ∈ P, ∀ q' ∈ P, a' < F q → F q < a → a' < F q' → F q' < a → F q = F q')
    (i : ℕ) :
    letI := hN.chartedSpace
    FiniteDimensional 𝕜 (subsetHomology 𝕜 i (preimage_mono (f := e)
        (sublevel_mono (F ∘ Subtype.val : N → ℝ) haa))) ∧
      finrank 𝕜 (subsetHomology 𝕜 i (preimage_mono (f := e)
        (sublevel_mono (F ∘ Subtype.val : N → ℝ) haa))) =
        #(P.filter fun p : N ↦ (a' < F p ∧ F p < a) ∧ indexM Z (F ∘ Subtype.val) p = i) := by
  classical
  let _ := hN.chartedSpace
  set f : N → ℝ := F ∘ Subtype.val with hf_def
  have hfc : Continuous f := hF.continuous.comp continuous_subtype_val
  by_cases hex : ∃ q ∈ P, a' < F q ∧ F q < a
  · -- one critical level `c` in `(a', a)`: Remark 3.3
    obtain ⟨q₀, hq₀P, hq₀a', hq₀a⟩ := hex
    set c := F q₀ with hc_def
    set S := P.filter (fun p : N ↦ F p = c) with hS_def
    have hS : ∀ p ∈ S, IsNondegenerateCriticalPointM Z f p ∧ F p = c := by
      intro p hp
      obtain ⟨hpP, hpc⟩ := Finset.mem_filter.1 hp
      have hpa : F p ≤ a := by rw [hpc]; exact hq₀a.le
      have hpcrit := (hP p hpa).1 hpP
      exact ⟨⟨hpcrit, hnd p hpcrit (hpa.trans haa₀)⟩, hpc⟩
    have hother : ∀ q : N, IsCriticalPointM Z f q → q ∉ S → F q < a' ∨ a < F q := by
      intro q hq hqS
      by_contra hcon
      push Not at hcon
      have hqP := (hP q hcon.2).2 hq
      have h1 : a' < F q := lt_of_le_of_ne hcon.1 (ha' q hqP).symm
      have h2 : F q < a := lt_of_le_of_ne hcon.2 (ha q hqP)
      exact hqS (Finset.mem_filter.2 ⟨hqP, hone q hqP q₀ hq₀P h1 h2 hq₀a' hq₀a⟩)
    obtain ⟨hfd, hfr⟩ := sublevel_step_critical_of_isCompact (𝕜 := 𝕜) hN hF e hK hS hq₀a' hq₀a
      haa₀ hother i
    refine ⟨hfd, hfr.trans (congrArg Finset.card ?_)⟩
    ext p
    simp only [hS_def, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hpP, hpc⟩, hpi⟩
      exact ⟨hpP, ⟨hpc ▸ hq₀a', hpc ▸ hq₀a⟩, hpi⟩
    · rintro ⟨hpP, ⟨h1, h2⟩, hpi⟩
      exact ⟨⟨hpP, hone p hpP q₀ hq₀P h1 h2 hq₀a' hq₀a⟩, hpi⟩
  · -- no critical value in `[a', a]`: Theorem 3.1 on the compact slab `[a', a]`
    push Not at hex
    have hcrit : ∀ q : N, F q ∈ Icc a' a → ¬IsCriticalPointM Z f q := by
      intro q hq hc
      have hqP := (hP q hq.2).2 hc
      exact absurd (lt_of_le_of_ne hq.2 (ha q hqP))
        (not_lt.2 (hex q hqP (lt_of_le_of_ne hq.1 (ha' q hqP).symm)))
    have hslab : IsCompact (f ⁻¹' Icc a' a) :=
      hK.of_isClosed_subset (isClosed_Icc.preimage hfc) fun q hq ↦ (hq.2.trans haa₀ : f q ≤ a₀)
    have hsdr := ((theorem_3_1_submanifold hN hF haa hslab hcrit).2.1).preimage_subtype e
    have hsub := subsingleton_subsetHomology_of_isSDR (𝕜 := 𝕜)
      (preimage_mono (f := e) (sublevel_mono f haa)) hsdr i
    refine ⟨inferInstance, ?_⟩
    rw [finrank_zero_of_subsingleton, eq_comm, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro p hp ⟨⟨h1, h2⟩, -⟩
    exact absurd h2 (not_lt.2 (hex p hp h1))

end Submanifold

end Morse.Homology
