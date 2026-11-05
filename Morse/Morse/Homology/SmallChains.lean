import Morse.Homology.Subdivision
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Small chains

Let `U : ι → Set X` be a family of subsets of a space `X` whose interiors cover `X`.  A singular
simplex is *`U`-small* if its image lies in some `U i`, and the `U`-small chains form a
subcomplex `C^U(X)` of the singular chain complex (`Morse.Homology.smallChains`).  This file
proves Hatcher's Proposition 2.21 (*Algebraic Topology*, p. 119):

> **The inclusion `C^U(X) ⟶ C(X)` is a chain homotopy equivalence**
> (`Morse.Homology.smallChainsHomotopyEquiv`), with a homotopy inverse `ρ : C(X) ⟶ C^U(X)`
> such that `ρ ∘ ι = 1`; in particular it induces isomorphisms in homology
> (`Morse.Homology.quasiIso_smallChainsι`).

Moreover `ρ` and the homotopy preserve the chains of any subspace `A` (and, more generally, chains
made of simplices with a property stable under precomposition), so for `A` one of the `U i` the
induced map of quotients `C^U(X) / C(A) ⟶ C(X) / C(A)` is again a homotopy equivalence
(`Morse.Homology.smallQuotHomotopyEquiv`).  This is the chain-level input for
excision (`Morse/Homology/Excision.lean`).

## Proof

By the Lebesgue number lemma on the compact metric space `Δⁿ` (Mathlib's
`lebesgue_number_lemma_of_metric`), for each simplex `σ : Δⁿ → X` there is an `m` such that `σ`
maps every closed ball of radius `(n / (n + 1)) ^ m` of `Δⁿ` into some `U i`
(`Morse.Homology.IsFine`, `Morse.Homology.exists_isFine`); by the diameter estimate every simplex
of the `m`-th barycentric subdivision of `Δⁿ` lies in such a ball, so `Sᵐ σ` is `U`-small
(`Morse.Homology.IsFine.ssd_pow_mem`).  Fineness passes to faces, since the face maps
`Δⁿ⁻¹ → Δⁿ` do not increase distances (`Morse.Homology.IsFine.comp_faceMap`).  Let `m(σ)` be the
least such `m` (`Morse.Homology.fineOrder`); then `m(σ ∘ δⁱ) ≤ m(σ)` and `m(σ) = 0` for `U`-small
`σ`.  With `S` and `T` the subdivision operator and homotopy (`∂T + T∂ = 1 - S`), Hatcher
defines
`D σ = ∑_{i < m(σ)} T Sⁱ σ` (`Morse.Homology.smallH`) and `ρ = 1 - ∂D - D∂`
(`Morse.Homology.smallRetr`).  Then `ρ` is a chain map, `1 - ιρ = ∂D + D∂`, `ρ = 1` on `C^U(X)`,
and `ρ σ = Sᵐ⁽σ⁾ σ + ∑ⱼ (-1)ʲ ∑_{m(σⱼ) ≤ i < m(σ)} T Sⁱ σⱼ` is `U`-small
(`Morse.Homology.smallRetr_mem_supported`).

Note on the definition of `m(σ)`: Hatcher takes the least `m` with `Sᵐ σ ∈ C^U(X)`, and uses
`m(σⱼ) ≤ m(σ)` for the faces `σⱼ`.  Since `Sᵐ σ` is a formal sum in which terms may cancel, that
inequality is not obvious for his `m(σ)`; the geometric `m(σ)` used here makes it immediate.
-/

open CategoryTheory Opposite Set Metric

noncomputable section

namespace Morse.Homology

universe u v

variable {R : Type u} [Ring R] {X : Type v} [TopologicalSpace X]

/-! ### Simplices in a subset, small simplices -/

section Small

/-- The singular simplices of `X` lying in a subset `A`. -/
def inSet (A : Set X) (n : ℕ) : Set C(Simplex n, X) := {σ | range σ ⊆ A}

lemma isPrecompClosed_inSet (A : Set X) : IsPrecompClosed (inSet A) :=
  fun _ _ σ τ hσ ↦ (range_comp_subset_range τ σ).trans hσ

variable {ι : Type*} (U : ι → Set X)

/-- The `U`-small singular simplices of `X`: those lying in some `U i`. -/
def smallSet (n : ℕ) : Set C(Simplex n, X) := {σ | ∃ i, range σ ⊆ U i}

lemma isPrecompClosed_smallSet : IsPrecompClosed (smallSet U) :=
  fun _ _ σ τ ⟨i, hi⟩ ↦ ⟨i, (range_comp_subset_range τ σ).trans hi⟩

lemma inSet_subset_smallSet (i : ι) (n : ℕ) : inSet (U i) n ⊆ smallSet U n :=
  fun _ hσ ↦ ⟨i, hσ⟩

end Small

/-- The boundary preserves chains made of simplices in a family closed under precomposition. -/
lemma sbd_mem_supported {P : ∀ n, Set C(Simplex n, X)} (hP : IsPrecompClosed P) {n : ℕ}
    {c : Chains R X (n + 1)} (hc : c ∈ Finsupp.supported R R (P (n + 1))) :
    sbd X n c ∈ Finsupp.supported R R (P n) := by
  refine map_mem_supported (fun σ hσ ↦ ?_) hc
  rw [sbd_single]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_of_tower_mem _ _
    (Finsupp.single_mem_supported R _ (hP σ _ hσ))

lemma sbd_ssd_pow {n : ℕ} (m : ℕ) (c : Chains R X (n + 1)) :
    sbd X n ((ssd R X (n + 1) ^ m) c) = (ssd R X n ^ m) (sbd X n c) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ', Module.End.mul_apply, sbd_ssd, ih, pow_succ', Module.End.mul_apply]

/-! ### Fineness -/

section Fine

variable {ι : Type*} (U : ι → Set X)

/-- The radius `(n / (n + 1)) ^ m`, which bounds the diameters of the simplices of the `m`-th
barycentric subdivision of `Δⁿ`. -/
def subdivRadius (n m : ℕ) : ℝ := ((n : ℝ) / (n + 1)) ^ m

lemma subdivRadius_nonneg (n m : ℕ) : 0 ≤ subdivRadius n m := by
  unfold subdivRadius; positivity

lemma subdivRadius_mono_left (n m : ℕ) : subdivRadius n m ≤ subdivRadius (n + 1) m := by
  unfold subdivRadius
  refine pow_le_pow_left₀ (by positivity) ?_ m
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast
  nlinarith

/-- A simplex `σ : Δⁿ → X` is `m`-fine for `U` if it maps every closed ball of radius
`(n / (n + 1)) ^ m` of `Δⁿ` into some `U i`. -/
def IsFine (m : ℕ) {n : ℕ} (σ : C(Simplex n, X)) : Prop :=
  ∀ x : Simplex n, ∃ i, MapsTo σ (closedBall x (subdivRadius n m)) (U i)

/-- `U`-small simplices are `0`-fine. -/
lemma isFine_zero_of_mem_smallSet {n : ℕ} {σ : C(Simplex n, X)} (hσ : σ ∈ smallSet U n) :
    IsFine U 0 σ := by
  obtain ⟨i, hi⟩ := hσ
  exact fun _ ↦ ⟨i, fun y _ ↦ hi ⟨y, rfl⟩⟩

/-- **Lebesgue number lemma**: if the interiors of the `U i` cover `X`, every simplex is `m`-fine
for some `m`. -/
lemma exists_isFine (hU : ⋃ i, interior (U i) = univ) {n : ℕ} (σ : C(Simplex n, X)) :
    ∃ m, IsFine U m σ := by
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric (c := fun i ↦ σ ⁻¹' interior (U i))
    isCompact_univ (fun i ↦ isOpen_interior.preimage σ.continuous)
    (by rw [← preimage_iUnion, hU, preimage_univ])
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hδ
    (show (n : ℝ) / (n + 1) < 1 by rw [div_lt_one (by positivity)]; linarith)
  refine ⟨m, fun x ↦ ?_⟩
  obtain ⟨i, hi⟩ := hball x (mem_univ x)
  exact ⟨i, fun y hy ↦ interior_subset (hi (closedBall_subset_ball hm hy))⟩

/-- The affine maps `Δᵐ → Δⁿ` induced by injective maps of vertices (such as the faces) do not
increase distances. -/
lemma dist_simplexMap_le {m n : ℕ} {f : Fin (m + 1) → Fin (n + 1)} (hf : Function.Injective f)
    (x y : Simplex m) : dist (simplexMap f x) (simplexMap f y) ≤ dist x y := by
  rw [Subtype.dist_eq, Subtype.dist_eq, dist_pi_le_iff dist_nonneg]
  intro b
  change dist (FunOnFinite.linearMap ℝ ℝ f (x : Fin (m + 1) → ℝ) b)
    (FunOnFinite.linearMap ℝ ℝ f (y : Fin (m + 1) → ℝ) b) ≤ dist (x : Fin (m + 1) → ℝ) y
  rw [FunOnFinite.linearMap_apply_apply, FunOnFinite.linearMap_apply_apply]
  by_cases hb : ∃ j, f j = b
  · obtain ⟨j, rfl⟩ := hb
    have : Finset.univ.filter (fun j' ↦ f j' = f j) = {j} := by
      ext j'
      simp [hf.eq_iff]
    rw [this, Finset.sum_singleton, Finset.sum_singleton]
    exact dist_le_pi_dist (x : Fin (m + 1) → ℝ) y j
  · have : Finset.univ.filter (fun j' ↦ f j' = b) = ∅ := by
      ext j'
      simpa using fun h ↦ hb ⟨j', h⟩
    rw [this, Finset.sum_empty, Finset.sum_empty, dist_self]
    exact dist_nonneg

/-- Fineness passes to faces. -/
lemma IsFine.comp_faceMap {m n : ℕ} {σ : C(Simplex (n + 1), X)} (h : IsFine U m σ)
    (i : Fin (n + 2)) : IsFine U m (σ.comp (faceMap i)) := by
  intro x
  obtain ⟨j, hj⟩ := h (faceMap i x)
  refine ⟨j, fun y hy ↦ hj ?_⟩
  rw [mem_closedBall] at hy ⊢
  exact (dist_simplexMap_le (Fin.succAbove_right_injective) y x).trans
    (hy.trans (subdivRadius_mono_left n m))

/-- **Iterated subdivision of a fine simplex is small**: if `σ` is `m`-fine, then `Sᵐ σ` is a
`U`-small chain. -/
lemma IsFine.ssd_pow_mem {m n : ℕ} {σ : C(Simplex n, X)} (h : IsFine U m σ) :
    (ssd R X n ^ m) (Finsupp.single σ 1) ∈ Finsupp.supported R R (smallSet U n) := by
  rw [ssd_pow_single]
  have hc := bsd_pow_mem_supported (R := R) (convex_simplex n) n m (verts n)
  have h₁ := mapDomain_mem_supported (f := aff (convex_simplex n)) hc
  have h₂ := mapDomain_mem_supported (f := (σ.comp ·)) h₁
  refine Finsupp.supported_mono ?_ h₂
  rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  obtain ⟨i, hi⟩ := h (u 0)
  refine ⟨i, ?_⟩
  rintro _ ⟨t, rfl⟩
  refine hi ?_
  rw [mem_closedBall, Subtype.dist_eq]
  calc dist (aff (convex_simplex n) u t : Fin (n + 1) → ℝ) (u 0 : Fin (n + 1) → ℝ)
      ≤ diam (vset u) := dist_aff_le (convex_simplex n) u t
    _ ≤ _ := hu.2
    _ ≤ subdivRadius n m * 1 :=
      mul_le_mul_of_nonneg_left (diam_vset_verts_le n) (subdivRadius_nonneg n m)
    _ = subdivRadius n m := mul_one _

variable {U} (hU : ⋃ i, interior (U i) = univ)

open Classical in
/-- The **order of fineness** `m(σ)` of a simplex: the least `m` such that `σ` is `m`-fine. -/
def fineOrder {n : ℕ} (σ : C(Simplex n, X)) : ℕ := Nat.find (exists_isFine U hU σ)

lemma isFine_fineOrder {n : ℕ} (σ : C(Simplex n, X)) : IsFine U (fineOrder hU σ) σ := by
  classical
  exact Nat.find_spec (exists_isFine U hU σ)

lemma fineOrder_le {m n : ℕ} {σ : C(Simplex n, X)} (h : IsFine U m σ) : fineOrder hU σ ≤ m := by
  classical
  exact Nat.find_min' (exists_isFine U hU σ) h

lemma fineOrder_comp_faceMap_le {n : ℕ} (σ : C(Simplex (n + 1), X)) (i : Fin (n + 2)) :
    fineOrder hU (σ.comp (faceMap i)) ≤ fineOrder hU σ :=
  fineOrder_le hU ((isFine_fineOrder hU σ).comp_faceMap U i)

lemma fineOrder_eq_zero {n : ℕ} {σ : C(Simplex n, X)} (hσ : σ ∈ smallSet U n) :
    fineOrder hU σ = 0 :=
  Nat.eq_zero_of_le_zero (fineOrder_le hU (isFine_zero_of_mem_smallSet U hσ))

/-- Once `m ≥ m(σ)`, `Sᵐ σ` is `U`-small. -/
lemma ssd_pow_mem_of_le {m n : ℕ} {σ : C(Simplex n, X)} (h : fineOrder hU σ ≤ m) :
    (ssd R X n ^ m) (Finsupp.single σ 1) ∈ Finsupp.supported R R (smallSet U n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm (fineOrder hU σ) k, pow_add, Module.End.mul_apply]
  exact ssd_pow_mem_supported (isPrecompClosed_smallSet U) k
    ((isFine_fineOrder hU σ).ssd_pow_mem U)

end Fine

/-! ### The homotopy `D` and the retraction `ρ` -/

section Retraction

variable {ι : Type*} {U : ι → Set X} (hU : ⋃ i, interior (U i) = univ)

variable (R X) in
/-- The partial sums `∑_{i < m} T Sⁱ`. -/
def partialH (m n : ℕ) : Chains R X n →ₗ[R] Chains R X (n + 1) :=
  ∑ i ∈ Finset.range m, ssdH R X n ∘ₗ ssd R X n ^ i

lemma partialH_apply (m n : ℕ) (c : Chains R X n) :
    partialH R X m n c = ∑ i ∈ Finset.range m, ssdH R X n ((ssd R X n ^ i) c) := by
  simp [partialH]

/-- `∂(∑_{i<m} T Sⁱ) + (∑_{i<m} T Sⁱ)∂ = 1 - Sᵐ`. -/
lemma partialH_telescope (m n : ℕ) (c : Chains R X (n + 1)) :
    sbd X (n + 1) (partialH R X m (n + 1) c) + partialH R X m n (sbd X n c) =
      c - (ssd R X (n + 1) ^ m) c := by
  induction m with
  | zero => simp [partialH]
  | succ m ih =>
    simp only [partialH_apply, Finset.sum_range_succ, map_add] at ih ⊢
    rw [← sbd_ssd_pow]
    have h := sbd_ssdH (R := R) n ((ssd R X (n + 1) ^ m) c)
    rw [pow_succ' (ssd R X (n + 1)) m, Module.End.mul_apply]
    calc _ = (sbd X (n + 1) (∑ i ∈ Finset.range m, ssdH R X (n + 1) ((ssd R X (n + 1) ^ i) c)) +
          ∑ i ∈ Finset.range m, ssdH R X n ((ssd R X n ^ i) (sbd X n c))) +
          (sbd X (n + 1) (ssdH R X (n + 1) ((ssd R X (n + 1) ^ m) c)) +
            ssdH R X n (sbd X n ((ssd R X (n + 1) ^ m) c))) := by abel
      _ = _ := by rw [ih, h]; abel

lemma partialH_zero_degree (m : ℕ) (c : Chains R X 0) : partialH R X m 0 c = 0 := by
  simp [partialH_apply]

/-- `Sⁱ` followed by `T` preserves `U`-small chains once `i ≥ m(σ)`. -/
lemma ssdH_ssd_pow_mem {n i : ℕ} {σ : C(Simplex n, X)} (h : fineOrder hU σ ≤ i) :
    ssdH R X n ((ssd R X n ^ i) (Finsupp.single σ 1)) ∈
      Finsupp.supported R R (smallSet U (n + 1)) :=
  ssdH_mem_supported (isPrecompClosed_smallSet U) (ssd_pow_mem_of_le hU h)

variable (R X U) in
/-- Hatcher's homotopy `D σ = ∑_{i < m(σ)} T Sⁱ σ`. -/
def smallH (n : ℕ) : Chains R X n →ₗ[R] Chains R X (n + 1) :=
  Finsupp.linearCombination R (fun σ ↦ partialH R X (fineOrder hU σ) n (Finsupp.single σ 1))

lemma smallH_single {n : ℕ} (σ : C(Simplex n, X)) (r : R) :
    smallH R X U hU n (Finsupp.single σ r) =
      r • partialH R X (fineOrder hU σ) n (Finsupp.single σ 1) := by
  simp [smallH]

variable (R X U) in
/-- Hatcher's retraction `ρ = 1 - ∂D - D∂` onto the `U`-small chains. -/
def smallRetr : ∀ n : ℕ, (Chains R X n →ₗ[R] Chains R X n)
  | 0 => LinearMap.id - sbd X 0 ∘ₗ smallH R X U hU 0
  | n + 1 => LinearMap.id - sbd X (n + 1) ∘ₗ smallH R X U hU (n + 1) - smallH R X U hU n ∘ₗ sbd X n

lemma smallRetr_zero_apply (c : Chains R X 0) :
    smallRetr R X U hU 0 c = c - sbd X 0 (smallH R X U hU 0 c) := rfl

lemma smallRetr_succ_apply (n : ℕ) (c : Chains R X (n + 1)) :
    smallRetr R X U hU (n + 1) c =
      c - sbd X (n + 1) (smallH R X U hU (n + 1) c) - smallH R X U hU n (sbd X n c) := rfl

/-- In degree `0`, `D = 0` and `ρ = 1`. -/
lemma smallH_zero_degree (c : Chains R X 0) : smallH R X U hU 0 c = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, hc, hd, add_zero]
  | single σ r => rw [smallH_single, partialH_zero_degree, smul_zero]

/-- `ρ` is a chain map. -/
lemma sbd_smallRetr (n : ℕ) (c : Chains R X (n + 1)) :
    sbd X n (smallRetr R X U hU (n + 1) c) = smallRetr R X U hU n (sbd X n c) := by
  cases n with
  | zero =>
    rw [smallRetr_succ_apply, smallRetr_zero_apply, map_sub, map_sub, sbd_sbd]
    abel
  | succ n =>
    rw [smallRetr_succ_apply, smallRetr_succ_apply, map_sub, map_sub, sbd_sbd, sbd_sbd,
      map_zero]
    abel

/-- **`ρ` lands in the small chains** (Hatcher's computation
`ρ σ = Sᵐ⁽σ⁾ σ + ∑ⱼ (-1)ʲ ∑_{m(σⱼ) ≤ i < m(σ)} T Sⁱ σⱼ`). -/
lemma smallRetr_mem_supported (n : ℕ) (c : Chains R X n) :
    smallRetr R X U hU n c ∈ Finsupp.supported R R (smallSet U n) := by
  cases n with
  | zero =>
    rw [smallRetr_zero_apply, smallH_zero_degree, map_zero, sub_zero]
    refine map_mem_supported (φ := LinearMap.id) (fun σ _ ↦ ?_)
      ((Finsupp.mem_supported R c).2 (subset_univ _))
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hU ▸ mem_univ (σ (verts 0 0)) :
      σ (verts 0 0) ∈ ⋃ i, interior (U i))
    refine Finsupp.single_mem_supported R _ ⟨i, ?_⟩
    rintro _ ⟨t, rfl⟩
    have : Subsingleton (Simplex 0) := inferInstanceAs (Subsingleton (stdSimplex ℝ (Fin 1)))
    rw [Subsingleton.elim t (verts 0 0)]
    exact interior_subset hi
  | succ n =>
    refine map_mem_supported (φ := smallRetr R X U hU (n + 1)) (fun σ _ ↦ ?_)
      ((Finsupp.mem_supported R c).2 (subset_univ _))
    set m := fineOrder hU σ
    have htel := partialH_telescope (R := R) m n (Finsupp.single σ 1)
    have key : smallRetr R X U hU (n + 1) (Finsupp.single σ 1) =
        (ssd R X (n + 1) ^ m) (Finsupp.single σ 1) +
          (partialH R X m n (sbd X n (Finsupp.single σ 1)) -
            smallH R X U hU n (sbd X n (Finsupp.single σ 1))) := by
      rw [smallRetr_succ_apply, smallH_single, one_smul, eq_sub_of_add_eq htel]
      abel
    rw [key]
    refine add_mem (ssd_pow_mem_of_le hU le_rfl) ?_
    rw [sbd_single, map_sum, map_sum, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun j _ ↦ ?_
    rw [map_zsmul, map_zsmul, ← smul_sub, smallH_single, one_smul]
    refine Submodule.smul_of_tower_mem _ _ ?_
    rw [partialH_apply, partialH_apply,
      ← Finset.sum_range_add_sum_Ico _ (fineOrder_comp_faceMap_le hU σ j), add_sub_cancel_left]
    refine Submodule.sum_mem _ fun i hi ↦ ssdH_ssd_pow_mem hU (Finset.mem_Ico.1 hi).1

/-- On `U`-small chains, `D = 0`. -/
lemma smallH_eq_zero {n : ℕ} {c : Chains R X n}
    (hc : c ∈ Finsupp.supported R R (smallSet U n)) : smallH R X U hU n c = 0 := by
  have : smallH R X U hU n c ∈ Finsupp.supported R R (∅ : Set C(Simplex (n + 1), X)) :=
    map_mem_supported (fun σ hσ ↦ by
      rw [smallH_single, fineOrder_eq_zero hU hσ, one_smul, partialH_apply, Finset.range_zero,
        Finset.sum_empty]
      exact zero_mem _) hc
  rwa [Finsupp.supported_empty, Submodule.mem_bot] at this

/-- On `U`-small chains, `ρ = 1`. -/
lemma smallRetr_eq_self {n : ℕ} {c : Chains R X n}
    (hc : c ∈ Finsupp.supported R R (smallSet U n)) : smallRetr R X U hU n c = c := by
  cases n with
  | zero => rw [smallRetr_zero_apply, smallH_eq_zero hU hc, map_zero, sub_zero]
  | succ n =>
    rw [smallRetr_succ_apply, smallH_eq_zero hU hc,
      smallH_eq_zero hU (sbd_mem_supported (isPrecompClosed_smallSet U) hc), map_zero, sub_zero,
      sub_zero]

/-- `D` preserves chains made of simplices in a family closed under precomposition. -/
lemma smallH_mem_supported {P : ∀ n, Set C(Simplex n, X)} (hP : IsPrecompClosed P) {n : ℕ}
    {c : Chains R X n} (hc : c ∈ Finsupp.supported R R (P n)) :
    smallH R X U hU n c ∈ Finsupp.supported R R (P (n + 1)) := by
  refine map_mem_supported (fun σ hσ ↦ ?_) hc
  rw [smallH_single, one_smul, partialH_apply]
  exact Submodule.sum_mem _ fun i _ ↦ ssdH_mem_supported hP
    (ssd_pow_mem_supported hP i (Finsupp.single_mem_supported R 1 hσ))

/-- `ρ` preserves chains made of simplices in a family closed under precomposition. -/
lemma smallRetr_mem_supported_of {P : ∀ n, Set C(Simplex n, X)} (hP : IsPrecompClosed P)
    {n : ℕ} {c : Chains R X n} (hc : c ∈ Finsupp.supported R R (P n)) :
    smallRetr R X U hU n c ∈ Finsupp.supported R R (P n) := by
  cases n with
  | zero =>
    rw [smallRetr_zero_apply]
    exact sub_mem hc (sbd_mem_supported hP (smallH_mem_supported hU hP hc))
  | succ n =>
    rw [smallRetr_succ_apply]
    exact sub_mem (sub_mem hc (sbd_mem_supported hP (smallH_mem_supported hU hP hc)))
      (smallH_mem_supported hU hP (sbd_mem_supported hP hc))

end Retraction

/-! ### Subcomplexes of singular chains, and the small chains theorem -/

section Complexes

variable (R) {P : ∀ n, Set C(Simplex n, X)}

variable (X) in
/-- The submodules of chains made of simplices in `P`, a subcomplex when `P` is closed under
precomposition. -/
abbrev supp (P : ∀ n, Set C(Simplex n, X)) (n : ℕ) : Submodule R ((singChains R X).X n) :=
  Finsupp.supported R R (P n)

lemma d_mem_supp (hP : IsPrecompClosed P) (n : ℕ) :
    ∀ x ∈ supp R X P (n + 1), (singChains R X).d (n + 1) n x ∈ supp R X P n :=
  fun x hx ↦ by
    rw [singChains_d]
    exact sbd_mem_supported hP hx

/-- The subcomplex of singular chains made of simplices in `P` (for instance `C(A) ⊆ C(X)` for
`P = inSet A`, or the `U`-small chains). -/
abbrev suppChains (hP : IsPrecompClosed P) : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  subcomplex (singChains R X) (supp R X P) (d_mem_supp R hP)

/-- The quotient of the singular chains by the chains made of simplices in `P` (for instance
`C(X) / C(A)` for `P = inSet A`). -/
abbrev quotChains (hP : IsPrecompClosed P) : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  quotient (singChains R X) (supp R X P) (d_mem_supp R hP)

variable {ι : Type*} (U : ι → Set X)

variable (X) in
/-- The complex `C^U(X)` of `U`-small singular chains. -/
abbrev smallChains : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  suppChains R (isPrecompClosed_smallSet U)

/-- The inclusion `C^U(X) ⟶ C(X)`. -/
abbrev smallChainsι : smallChains R X U ⟶ singChains R X := subcomplexι _ _ _

variable {U} (hU : ⋃ i, interior (U i) = univ)

/-- Hatcher's retraction `ρ : C(X) ⟶ C^U(X)`. -/
def smallRetraction : singChains R X ⟶ smallChains R X U :=
  natHomMk (fun n ↦ ModuleCat.ofHom ((smallRetr R X U hU n).codRestrict
      (supp R X (smallSet U) n) (smallRetr_mem_supported hU n)))
    (fun n ↦ by
      rw [subcomplex_d]
      refine ModuleCat.hom_ext (LinearMap.ext fun (c : Chains R X (n + 1)) ↦ Subtype.ext ?_)
      change (singChains R X).d (n + 1) n (smallRetr R X U hU (n + 1) c) =
        smallRetr R X U hU n ((singChains R X).d (n + 1) n c)
      rw [singChains_d]
      exact sbd_smallRetr hU n c)

lemma smallRetraction_f_apply (n : ℕ) (c : Chains R X n) :
    (show supp R X (smallSet U) n from (smallRetraction R hU).f n c).1 =
      smallRetr R X U hU n c := rfl

/-- `ρ ∘ ι = 1`. -/
lemma smallChainsι_smallRetraction : smallChainsι R U ≫ smallRetraction R hU = 𝟙 _ := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (c : supp R X (smallSet U) n) ↦ Subtype.ext ?_)
  exact smallRetr_eq_self hU c.2

/-- The homotopy `1 ≃ ι ∘ ρ`, `1 - ιρ = ∂D + D∂`. -/
def smallRetractionHomotopy :
    Homotopy (𝟙 (singChains R X)) (smallRetraction R hU ≫ smallChainsι R U) :=
  natHomotopyMk (fun n ↦ ModuleCat.ofHom (smallH R X U hU n))
    (by
      rw [singChains_d]
      refine ModuleCat.hom_ext (LinearMap.ext fun (c : Chains R X 0) ↦ ?_)
      change c = sbd X 0 (smallH R X U hU 0 c) + smallRetr R X U hU 0 c
      rw [smallRetr_zero_apply]
      abel)
    (fun n ↦ by
      rw [singChains_d, singChains_d]
      refine ModuleCat.hom_ext (LinearMap.ext fun (c : Chains R X (n + 1)) ↦ ?_)
      change c = smallH R X U hU n (sbd X n c) + sbd X (n + 1) (smallH R X U hU (n + 1) c) +
        smallRetr R X U hU (n + 1) c
      rw [smallRetr_succ_apply]
      abel)

/-- **The small chains theorem** (Hatcher, Prop. 2.21): if the interiors of the `U i` cover `X`,
the inclusion `C^U(X) ⟶ C(X)` of the `U`-small singular chains is a chain homotopy equivalence,
with homotopy inverse Hatcher's `ρ`. -/
def smallChainsHomotopyEquiv : HomotopyEquiv (smallChains R X U) (singChains R X) where
  hom := smallChainsι R U
  inv := smallRetraction R hU
  homotopyHomInvId := Homotopy.ofEq (smallChainsι_smallRetraction R hU)
  homotopyInvHomId := (smallRetractionHomotopy R hU).symm

include hU in
/-- The inclusion of the `U`-small chains induces isomorphisms in homology. -/
lemma quasiIso_smallChainsι : QuasiIso (smallChainsι R U) :=
  (smallChainsHomotopyEquiv R hU).quasiIso_hom

/-! ### Relative version -/

variable (U) in
/-- The submodules of `U`-small chains made of simplices in `P`. -/
abbrev suppSmall (P : ∀ n, Set C(Simplex n, X)) (n : ℕ) :
    Submodule R ((smallChains R X U).X n) :=
  (supp R X P n).comap (supp R X (smallSet U) n).subtype

omit hU in
variable (U) in
lemma d_mem_suppSmall (hP : IsPrecompClosed P) (n : ℕ) :
    ∀ x ∈ suppSmall R U P (n + 1), (smallChains R X U).d (n + 1) n x ∈ suppSmall R U P n :=
  fun x hx ↦ by
    change (((smallChains R X U).d (n + 1) n x : supp R X (smallSet U) n) : Chains R X n) ∈
      supp R X P n
    rw [subcomplex_d_apply]
    exact d_mem_supp R hP n _ hx

variable (U) in
/-- The quotient `C^U(X) / (C^U(X) ∩ C_P(X))`, for instance `C^U(X) / C(A)`. -/
abbrev smallQuotChains (hP : IsPrecompClosed P) : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  quotient (smallChains R X U) (suppSmall R U P) (d_mem_suppSmall R U hP)

variable (U) in
/-- The map `C^U(X) / C_P ⟶ C(X) / C_P` induced by the inclusion. -/
def smallQuotMap (hP : IsPrecompClosed P) : smallQuotChains R U hP ⟶ quotChains R hP :=
  quotientMap (smallChainsι R U) (fun _ _ hx ↦ hx)

/-- The map `C(X) / C_P ⟶ C^U(X) / C_P` induced by `ρ`. -/
def smallQuotRetraction (hP : IsPrecompClosed P) : quotChains R hP ⟶ smallQuotChains R U hP :=
  quotientMap (smallRetraction R hU) (fun _ _ hx ↦ smallRetr_mem_supported_of hU hP hx)

/-- **The relative small chains theorem**: if `P` is closed under precomposition (for instance
the simplices in a subspace `A`), the map `C^U(X) / C_P(X) ⟶ C(X) / C_P(X)` is a chain homotopy
equivalence. -/
def smallQuotHomotopyEquiv (hP : IsPrecompClosed P) :
    HomotopyEquiv (smallQuotChains R U hP) (quotChains R hP) where
  hom := smallQuotMap R U hP
  inv := smallQuotRetraction R hU hP
  homotopyHomInvId := Homotopy.ofEq (by
    ext n : 1
    refine ModuleCat.hom_ext (Submodule.linearMap_qext _
      (LinearMap.ext fun (c : supp R X (smallSet U) n) ↦ ?_))
    change (suppSmall R U P n).mkQ _ = (suppSmall R U P n).mkQ c
    congr 1
    exact Subtype.ext (smallRetr_eq_self hU c.2))
  homotopyInvHomId := by
    refine (Homotopy.ofEq (quotientMap_comp _ _ _ _).symm).trans ?_
    refine (quotientHomotopy (smallRetractionHomotopy R hU).symm _ _ ?_).trans
      (Homotopy.ofEq quotientMap_id)
    intro n x hx
    have : ((smallRetractionHomotopy R hU).symm.hom n (n + 1)) x = -(smallH R X U hU n x) := by
      simp [smallRetractionHomotopy]
    rw [this]
    exact neg_mem (smallH_mem_supported hU hP hx)

include hU in
lemma quasiIso_smallQuotMap (hP : IsPrecompClosed P) : QuasiIso (smallQuotMap R U hP) :=
  (smallQuotHomotopyEquiv R hU hP).quasiIso_hom

end Complexes

end Morse.Homology
