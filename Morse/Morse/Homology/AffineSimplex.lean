import Morse.Homology.LinearChains
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Affine simplices in a convex set, barycentres, and the diameter estimate

Let `s` be a convex set in a real vector space `E`.  A tuple `w : Fin (k + 1) → s` spans the
*affine (linear) simplex* `Morse.Homology.aff hs w : C(Δᵏ, s)`, `t ↦ ∑ᵢ tᵢ wᵢ` (Hatcher's
`[w₀, …, w_k]`), and has the *barycentre* `Morse.Homology.bary hs w = ∑ᵢ wᵢ / (k + 1)`, the image
of the barycentre of `Δᵏ`.  This file provides the geometric input to the combinatorial
subdivision of `Morse/Homology/LinearChains.lean`.

## Main definitions and results

* `Morse.Homology.aff_comp_aff`: affine simplices compose — the composite of `Δᵐ → Δⁿ` spanned by
  `v` and `Δⁿ → s` spanned by `u` is spanned by the images of the vertices, `aff u ∘ v`.  Every
  `simplexMap f : Δᵐ → Δⁿ` is affine (`Morse.Homology.simplexMap_eq_aff`), and the barycentre is
  preserved by affine maps (`Morse.Homology.aff_bary`).
* `Morse.Homology.realize hs : tuples s ⟶ sing s`, the morphism of simplicial sets `w ↦ aff hs w`;
  on chains it gives `Morse.Homology.lreal`, a chain map from linear chains to singular chains
  (`Morse.Homology.sbd_lreal`).
* `Morse.Homology.bsd hs` and `Morse.Homology.bsdH hs`: barycentric subdivision of linear chains in
  `s` and its homotopy (the operators `sd`, `sdH` with the barycentre of `s`), natural with respect
  to affine simplices (`Morse.Homology.lmap_aff_bsd`, `Morse.Homology.lmap_aff_bsdH`).
* **The diameter estimate** (Hatcher, step (1) of the proof of Prop. 2.21):
  `Morse.Homology.bsd_pow_mem_supported` — for `E` normed, every simplex `u` of the `m`-th
  barycentric subdivision of a linear `n`-simplex `w` lies in the convex hull of `w`, and its
  vertex set has diameter at most `(n / (n + 1)) ^ m` times that of `w`; the image of the affine
  simplex `aff hs u` has the same diameter as its vertex set (`Morse.Homology.diam_range_aff`).

The key inequality is `Morse.Homology.dist_bary_le`: the barycentre `b` of `n + 1` points is at
distance at most `n / (n + 1)` times their diameter from each point of their convex hull, since
`wⱼ - b = (∑ᵢ (wⱼ - wᵢ)) / (n + 1)` has `n` nonzero terms each of norm at most the diameter.
-/

open CategoryTheory Opposite Set Metric

noncomputable section

namespace Morse.Homology

universe u v

/-! ### Affine simplices and barycentres -/

section Affine

variable {E : Type v} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] {s : Set E} (hs : Convex ℝ s)

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
include hs in
lemma sum_smul_mem {k : ℕ} (w : Fin (k + 1) → s) (t : Simplex k) : ∑ i, t i • (w i : E) ∈ s :=
  hs.sum_mem (fun i _ ↦ stdSimplex.zero_le t i) (stdSimplex.sum_eq_one t) (fun i _ ↦ (w i).2)

/-- The affine simplex `[w₀, …, w_k] : Δᵏ → s`, `t ↦ ∑ᵢ tᵢ wᵢ`, spanned by a tuple of points of a
convex set `s`. -/
def aff {k : ℕ} (w : Fin (k + 1) → s) : C(Simplex k, s) where
  toFun t := ⟨∑ i, t i • (w i : E), sum_smul_mem hs w t⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_finsetSum _ fun i _ ↦ ?_) _
    exact ((continuous_apply i).comp continuous_subtype_val).smul continuous_const

@[simp]
lemma coe_aff_apply {k : ℕ} (w : Fin (k + 1) → s) (t : Simplex k) :
    (aff hs w t : E) = ∑ i, t i • (w i : E) := rfl

/-- The vertex `eᵢ` of `Δᵏ` is mapped to `wᵢ`. -/
@[simp]
lemma aff_vertex {k : ℕ} (w : Fin (k + 1) → s) (i : Fin (k + 1)) :
    aff hs w (stdSimplex.vertex i) = w i := by
  ext
  simp [Pi.single_apply]

/-- The standard simplex is convex. -/
lemma convex_simplex (n : ℕ) : Convex ℝ (Simplex n) := convex_stdSimplex ℝ _

/-- The vertices `e₀, …, eₙ` of the standard simplex. -/
abbrev verts (n : ℕ) : Fin (n + 1) → Simplex n := fun i ↦ stdSimplex.vertex i

lemma coe_simplex_eq_sum {n : ℕ} (t : Simplex n) :
    (t : Fin (n + 1) → ℝ) = ∑ i, t i • ((verts n i : Simplex n) : Fin (n + 1) → ℝ) := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

/-- **Affine simplices compose**: `[u] ∘ [v] = [[u] ∘ v]`. -/
lemma aff_comp_aff {m n : ℕ} (u : Fin (n + 1) → s) (v : Fin (m + 1) → Simplex n) :
    (aff hs u).comp (aff (convex_simplex n) v) = aff hs (aff hs u ∘ v) := by
  ext t : 2
  simp only [ContinuousMap.comp_apply, coe_aff_apply, Function.comp_apply]
  change ∑ i, (∑ j, t j • (v j : Fin (n + 1) → ℝ)) i • (u i : E) = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul, Finset.smul_sum,
    smul_smul]
  exact Finset.sum_comm

/-- The identity of `Δⁿ` is the affine simplex spanned by its vertices. -/
@[simp]
lemma aff_verts (n : ℕ) : aff (convex_simplex n) (verts n) = ContinuousMap.id _ := by
  ext t : 2
  exact (coe_simplex_eq_sum t).symm

/-- The affine map `simplexMap f : Δᵐ → Δⁿ` is the affine simplex spanned by the vertices
`e_{f 0}, …, e_{f m}`. -/
lemma simplexMap_eq_aff {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) :
    simplexMap f = aff (convex_simplex n) (verts n ∘ f) := by
  ext t i
  change ((simplexMap f t : Simplex n) : Fin (n + 1) → ℝ) i =
    (∑ j, t j • ((verts n (f j) : Simplex n) : Fin (n + 1) → ℝ)) i
  simp only [simplexMap_apply, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp [Pi.single_apply, eq_comm]

/-- Precomposing an affine simplex with `simplexMap f` reorders (or repeats) its vertices. -/
lemma aff_comp_simplexMap {m n : ℕ} (w : Fin (n + 1) → s) (f : Fin (m + 1) → Fin (n + 1)) :
    (aff hs w).comp (simplexMap f) = aff hs (w ∘ f) := by
  rw [simplexMap_eq_aff, aff_comp_aff]
  congr 1
  ext i : 1
  simp

/-- The barycentre `(w₀ + ⋯ + w_k) / (k + 1)` of a tuple of points of a convex set. -/
def bary {k : ℕ} (w : Fin (k + 1) → s) : s := aff hs w stdSimplex.barycenter

lemma coe_bary {k : ℕ} (w : Fin (k + 1) → s) :
    (bary hs w : E) = ((k : ℝ) + 1)⁻¹ • ∑ i, (w i : E) := by
  simp [bary, Finset.smul_sum, stdSimplex.barycenter]
  rfl

/-- Affine simplices preserve barycentres. -/
lemma aff_bary {m n : ℕ} (u : Fin (n + 1) → s) (v : Fin (m + 1) → Simplex n) :
    aff hs u (bary (convex_simplex n) v) = bary hs (aff hs u ∘ v) := by
  rw [bary, bary, ← aff_comp_aff]
  rfl

/-- The realization of linear simplices as affine singular simplices, a morphism of simplicial
sets `tuples s ⟶ sing s`. -/
def realize : tuples s ⟶ sing s where
  app _ := ↾fun w ↦ aff hs w
  naturality _ _ f := by
    ext w : 3
    exact (aff_comp_simplexMap hs w f.unop.toOrderHom).symm

/-- The realization of linear chains as singular chains, `[w] ↦ aff w`. -/
def lreal (R : Type u) [Ring R] (k : ℕ) : LinChain R s k →ₗ[R] Chains R s k :=
  Finsupp.lmapDomain R R (aff hs)

variable {R : Type u} [Ring R]

@[simp]
lemma lreal_single {k : ℕ} (w : Fin (k + 1) → s) (r : R) :
    lreal hs R k (Finsupp.single w r) = Finsupp.single (aff hs w) r :=
  Finsupp.mapDomain_single

/-- The realization of linear chains is a chain map. -/
lemma sbd_lreal (k : ℕ) (c : LinChain R s (k + 1)) :
    sbd s k (lreal hs R (k + 1) c) = lreal hs R k (lbd k c) :=
  (lmapDomain_bd R (realize hs) k c).symm

/-- Pushing forward the realization of a linear chain in `Δⁿ` along an affine simplex. -/
lemma push_aff_lreal {m n : ℕ} (u : Fin (n + 1) → s) (c : LinChain R (Simplex n) m) :
    push (aff hs u) m (lreal (convex_simplex n) R m c) = lreal hs R m (lmap (aff hs u) m c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single w r => simp [aff_comp_aff]

/-- Barycentric subdivision of linear chains in a convex set. -/
abbrev bsd (k : ℕ) : LinChain R s k →ₗ[R] LinChain R s k := sd (fun _ ↦ bary hs) k

/-- The homotopy between the identity and barycentric subdivision of linear chains in a convex
set. -/
abbrev bsdH (k : ℕ) : LinChain R s k →ₗ[R] LinChain R s (k + 1) := sdH (fun _ ↦ bary hs) k

/-- Barycentric subdivision is natural with respect to affine simplices. -/
lemma lmap_aff_bsd {n : ℕ} (u : Fin (n + 1) → s) (k : ℕ) (c : LinChain R (Simplex n) k) :
    lmap (aff hs u) k (bsd (convex_simplex n) k c) = bsd hs k (lmap (aff hs u) k c) :=
  lmap_sd _ _ _ (fun _ w ↦ aff_bary hs u w) k c

/-- The subdivision homotopy is natural with respect to affine simplices. -/
lemma lmap_aff_bsdH {n : ℕ} (u : Fin (n + 1) → s) (k : ℕ) (c : LinChain R (Simplex n) k) :
    lmap (aff hs u) (k + 1) (bsdH (convex_simplex n) k c) = bsdH hs k (lmap (aff hs u) k c) :=
  lmap_sdH _ _ _ (fun _ w ↦ aff_bary hs u w) k c

end Affine

/-! ### Supports -/

section Support

variable {R : Type u} [Ring R] {α β : Type*}

/-- To show that a linear map between free modules sends chains supported in `P` to chains
supported in `Q`, it suffices to check it on the generators in `P`. -/
lemma map_mem_supported {φ : (α →₀ R) →ₗ[R] (β →₀ R)} {P : Set α} {Q : Set β}
    (h : ∀ a ∈ P, φ (Finsupp.single a 1) ∈ Finsupp.supported R R Q) {c : α →₀ R}
    (hc : c ∈ Finsupp.supported R R P) : φ c ∈ Finsupp.supported R R Q := by
  rw [Finsupp.supported_eq_span_single] at hc
  refine Submodule.span_induction (fun x hx ↦ ?_) (by simp) (fun x y _ _ hx hy ↦ ?_)
    (fun r x _ hx ↦ ?_) hc
  · obtain ⟨a, ha, rfl⟩ := hx
    exact h a ha
  · rw [map_add]; exact add_mem hx hy
  · rw [map_smul]; exact Submodule.smul_mem _ r hx

lemma single_mem_supported_iff [Nontrivial R] {a : α} {P : Set α} :
    Finsupp.single a (1 : R) ∈ Finsupp.supported R R P ↔ a ∈ P := by
  refine ⟨fun h ↦ ?_, fun h ↦ Finsupp.single_mem_supported R 1 h⟩
  rw [Finsupp.mem_supported] at h
  exact h (by simp)

lemma mapDomain_mem_supported {f : α → β} {P : Set α} {c : α →₀ R}
    (hc : c ∈ Finsupp.supported R R P) :
    Finsupp.lmapDomain R R f c ∈ Finsupp.supported R R (f '' P) :=
  map_mem_supported (fun a ha ↦ by
    simpa using Finsupp.single_mem_supported R (1 : R) (Set.mem_image_of_mem f ha)) hc

end Support

/-! ### The diameter estimate -/

section Diameter

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} (hs : Convex ℝ s)

/-- The vertex set of a tuple of points of `s`, as a subset of `E`. -/
abbrev vset {k : ℕ} (w : Fin (k + 1) → s) : Set E := Set.range fun i ↦ (w i : E)

omit [NormedSpace ℝ E] in
lemma isBounded_vset {k : ℕ} (w : Fin (k + 1) → s) : Bornology.IsBounded (vset w) :=
  (Set.finite_range _).isBounded

lemma vset_subset_convexHull {k : ℕ} (w : Fin (k + 1) → s) :
    vset w ⊆ convexHull ℝ (vset w) :=
  subset_convexHull ℝ _

/-- The image of an affine simplex lies in the convex hull of its vertices. -/
lemma range_aff_subset {k : ℕ} (w : Fin (k + 1) → s) :
    Set.range (fun t ↦ (aff hs w t : E)) ⊆ convexHull ℝ (vset w) := by
  rintro _ ⟨t, rfl⟩
  exact (convex_convexHull ℝ _).sum_mem (fun i _ ↦ stdSimplex.zero_le t i)
    (stdSimplex.sum_eq_one t) (fun i _ ↦ subset_convexHull ℝ _ ⟨i, rfl⟩)

/-- The image of an affine simplex has the same diameter as its vertex set. -/
lemma diam_range_aff_le {k : ℕ} (w : Fin (k + 1) → s) :
    diam (Set.range (fun t ↦ (aff hs w t : E))) ≤ diam (vset w) := by
  rw [← convexHull_diam (vset w)]
  exact diam_mono (range_aff_subset hs w) (isBounded_convexHull.2 (isBounded_vset w))

lemma bary_mem_convexHull {k : ℕ} (w : Fin (k + 1) → s) :
    (bary hs w : E) ∈ convexHull ℝ (vset w) :=
  range_aff_subset hs w ⟨_, rfl⟩

/-- **The barycentre is close to the convex hull**: the barycentre of `n + 1` points is at
distance at most `n / (n + 1)` times their diameter from every point of their convex hull. -/
lemma dist_bary_le {n : ℕ} (w : Fin (n + 1) → s) {x : E} (hx : x ∈ convexHull ℝ (vset w)) :
    dist x (bary hs w) ≤ n / (n + 1) * diam (vset w) := by
  obtain ⟨_, ⟨j, rfl⟩, hj⟩ := convexHull_exists_dist_ge hx (bary hs w : E)
  refine hj.trans ?_
  have hn : (0 : ℝ) < n + 1 := by positivity
  have key : (w j : E) - bary hs w = ((n : ℝ) + 1)⁻¹ • ∑ i, ((w j : E) - w i) := by
    rw [coe_bary, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_sub, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    push_cast
    rw [inv_mul_cancel₀ hn.ne', one_smul]
  rw [dist_eq_norm, key, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hn,
    ← le_div_iff₀' (inv_pos.2 hn), div_inv_eq_mul, div_mul_eq_mul_div, mul_comm,
    ← mul_div_assoc, mul_div_cancel_left₀ _ hn.ne']
  calc ‖∑ i, ((w j : E) - w i)‖ ≤ ∑ i, ‖(w j : E) - w i‖ := norm_sum_le _ _
    _ = ∑ i ∈ Finset.univ.erase j, ‖(w j : E) - w i‖ :=
      (Finset.sum_erase _ (by simp)).symm
    _ ≤ (Finset.univ.erase j).card • diam (vset w) := by
      refine Finset.sum_le_card_nsmul _ _ _ fun i _ ↦ ?_
      rw [← dist_eq_norm]
      exact dist_le_diam_of_mem (isBounded_vset w) ⟨j, rfl⟩ ⟨i, rfl⟩
    _ = n * diam (vset w) := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      simp

/-- The tuples whose vertices lie in the convex hull of `w` and have diameter at most `r`. -/
def Shrunk {k n : ℕ} (w : Fin (n + 1) → s) (r : ℝ) : Set (Fin (k + 1) → s) :=
  {u | vset u ⊆ convexHull ℝ (vset w) ∧ diam (vset u) ≤ r}

lemma Shrunk.mono {k n m : ℕ} {w : Fin (n + 1) → s} {w' : Fin (m + 1) → s} {r r' : ℝ}
    (hw : convexHull ℝ (vset w) ⊆ convexHull ℝ (vset w')) (hr : r ≤ r') :
    (Shrunk (k := k) w r) ⊆ Shrunk w' r' :=
  fun _ hu ↦ ⟨hu.1.trans hw, hu.2.trans hr⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma vset_comp_subset {k n : ℕ} (w : Fin (n + 1) → s) (f : Fin (k + 1) → Fin (n + 1)) :
    vset (w ∘ f) ⊆ vset w :=
  Set.range_comp_subset_range f (fun i ↦ (w i : E))

lemma convexHull_vset_comp_subset {k n : ℕ} (w : Fin (n + 1) → s)
    (f : Fin (k + 1) → Fin (n + 1)) : convexHull ℝ (vset (w ∘ f)) ⊆ convexHull ℝ (vset w) :=
  convexHull_mono (vset_comp_subset w f)

omit [NormedSpace ℝ E] in
lemma diam_vset_comp_le {k n : ℕ} (w : Fin (n + 1) → s) (f : Fin (k + 1) → Fin (n + 1)) :
    diam (vset (w ∘ f)) ≤ diam (vset w) :=
  diam_mono (vset_comp_subset w f) (isBounded_vset w)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma vset_cons {k : ℕ} (b : s) (u : Fin (k + 1) → s) :
    vset (Fin.cons b u : Fin (k + 2) → s) = insert (b : E) (vset u) := by
  ext x
  simp [vset, Fin.exists_fin_succ, eq_comm]

variable {R : Type u} [Ring R]

/-- **One step of the diameter estimate**: every simplex of the barycentric subdivision of a
linear `n`-simplex `w` lies in the convex hull of `w` and has diameter at most `n / (n + 1)`
times the diameter of `w`. -/
lemma bsd_mem_supported (n : ℕ) (w : Fin (n + 1) → s) :
    bsd hs n (Finsupp.single w (1 : R)) ∈
      Finsupp.supported R R (Shrunk w (n / (n + 1) * diam (vset w))) := by
  induction n with
  | zero =>
    refine Finsupp.single_mem_supported R _ ⟨subset_convexHull ℝ _, ?_⟩
    have : vset w = {(w 0 : E)} := by
      ext x
      simp [vset, eq_comm, Fin.exists_fin_one]
    simp [this]
  | succ k ih =>
    rw [sd_succ_single, one_smul]
    set b := bary hs w
    set D := diam (vset w)
    -- the subdivided faces are fine relative to `w`
    have hfaces : bsd hs k (lbd k (Finsupp.single w (1 : R))) ∈
        Finsupp.supported R R (Shrunk w (k / (k + 1) * D)) := by
      rw [lbd_single, map_sum]
      refine Submodule.sum_mem _ fun i _ ↦ ?_
      rw [map_zsmul]
      refine Submodule.smul_of_tower_mem _ _ ?_
      refine Finsupp.supported_mono ?_ (ih (w ∘ Fin.succAbove i))
      refine Shrunk.mono (convexHull_vset_comp_subset w _) ?_
      exact mul_le_mul_of_nonneg_left (diam_vset_comp_le w _) (by positivity)
    refine map_mem_supported (fun u hu ↦ ?_) hfaces
    rw [cone_single]
    refine Finsupp.single_mem_supported R _ ⟨?_, ?_⟩
    · rw [vset_cons]
      exact Set.insert_subset_iff.2 ⟨bary_mem_convexHull hs w, hu.1⟩
    · rw [vset_cons]
      have hD : 0 ≤ D := diam_nonneg
      have hk : (k : ℝ) / (k + 1) ≤ ((k + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) + 1) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        push_cast
        nlinarith
      have hS : ∀ y ∈ vset u, dist y (b : E) ≤ ((k + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) + 1) * D :=
        fun y hy ↦ dist_bary_le hs w (hu.1 hy)
      refine diam_le_of_forall_dist_le (by positivity) fun x hx y hy ↦ ?_
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · simp only [dist_self]
        positivity
      · rw [dist_comm]
        exact hS y hy
      · exact hS x hx
      · exact (dist_le_diam_of_mem (isBounded_vset u) hx hy).trans
          (hu.2.trans (mul_le_mul_of_nonneg_right hk hD))

/-- **The diameter estimate** (Hatcher, step (1) of the proof of Prop. 2.21): every simplex of
the `m`-th barycentric subdivision of a linear `n`-simplex `w` lies in the convex hull of `w`, and
its vertex set has diameter at most `(n / (n + 1)) ^ m` times that of `w`. -/
theorem bsd_pow_mem_supported (n m : ℕ) (w : Fin (n + 1) → s) :
    (bsd hs n ^ m) (Finsupp.single w (1 : R)) ∈
      Finsupp.supported R R (Shrunk w ((n / (n + 1)) ^ m * diam (vset w))) := by
  induction m with
  | zero =>
    rw [pow_zero (bsd hs n), Module.End.one_apply, pow_zero, one_mul]
    exact Finsupp.single_mem_supported R _ ⟨subset_convexHull ℝ _, le_rfl⟩
  | succ m ih =>
    rw [pow_succ' (bsd hs n), Module.End.mul_apply]
    refine map_mem_supported (fun u hu ↦ ?_) ih
    refine Finsupp.supported_mono (Shrunk.mono ?_ ?_) (bsd_mem_supported hs n u)
    · exact convexHull_min hu.1 (convex_convexHull ℝ _)
    · calc (n : ℝ) / (n + 1) * diam (vset u)
          ≤ n / (n + 1) * ((n / (n + 1)) ^ m * diam (vset w)) :=
            mul_le_mul_of_nonneg_left hu.2 (by positivity)
        _ = _ := by ring

/-- Every point of an affine simplex is within the diameter of its vertex set from its first
vertex. -/
lemma dist_aff_le {k : ℕ} (u : Fin (k + 1) → s) (t : Simplex k) :
    dist (aff hs u t : E) (u 0 : E) ≤ diam (vset u) := by
  rw [← convexHull_diam]
  exact dist_le_diam_of_mem (isBounded_convexHull.2 (isBounded_vset u))
    (range_aff_subset hs u ⟨t, rfl⟩) (subset_convexHull ℝ _ ⟨0, rfl⟩)

/-- The image of an affine simplex has the same diameter as its vertex set. -/
lemma diam_range_aff {k : ℕ} (w : Fin (k + 1) → s) :
    diam (Set.range (fun t ↦ (aff hs w t : E))) = diam (vset w) := by
  refine le_antisymm (diam_range_aff_le hs w) (diam_mono ?_ ?_)
  · rintro _ ⟨i, rfl⟩
    exact ⟨stdSimplex.vertex i, by simp⟩
  · exact (isBounded_convexHull.2 (isBounded_vset w)).subset (range_aff_subset hs w)

/-- **The diameter estimate**, for the images of the simplices: every simplex `u` of the `m`-th
barycentric subdivision of a linear `n`-simplex `w` satisfies
`diam [u] ≤ (n / (n + 1)) ^ m * diam [w]`, where `[u]` is the image of the affine simplex. -/
theorem diam_range_aff_le_of_mem_support (n m : ℕ) (w : Fin (n + 1) → s) {u : Fin (n + 1) → s}
    (hu : u ∈ ((bsd hs n ^ m) (Finsupp.single w (1 : R))).support) :
    diam (Set.range (fun t ↦ (aff hs u t : E))) ≤
      (n / (n + 1)) ^ m * diam (Set.range (fun t ↦ (aff hs w t : E))) := by
  rw [diam_range_aff, diam_range_aff]
  exact ((Finsupp.mem_supported R _).1 (bsd_pow_mem_supported hs n m w) hu).2

/-- The vertices of the standard simplex are at distance at most `1` from each other. -/
lemma diam_vset_verts_le (n : ℕ) : diam (vset (verts n)) ≤ 1 := by
  refine (diam_mono ?_ (bounded_stdSimplex _)).trans diam_stdSimplex_le
  rintro _ ⟨i, rfl⟩
  exact (verts n i).2

end Diameter

end Morse.Homology
