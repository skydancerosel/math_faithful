import Morse.Chapter5.HyperplaneSection
import Morse.Chapter3.ProjectiveSpace

/-!
Milnor, *Morse Theory*, §7, Corollary 7.3 (p. 41); Exposition/Chapter5.md, §5.

# Corollary 7.3 for projective varieties

## Milnor's text, paraphrased

(p. 41) Let `V ⊂ ℂPⁿ` be an algebraic variety of complex dimension `k` and `P ⊂ ℂPⁿ` a hyperplane
which contains all singular points of `V`.  Then the inclusion `V ∩ P → V` induces isomorphisms
`H_r(V ∩ P) → H_r(V)` for `r < k − 1` and a surjection for `r = k − 1`.  `ℂPⁿ − P` is an affine
space `ℂⁿ`, in which `V − P` is a closed complex submanifold.

## What is formalized

`ℂPⁿ` is the set of Hermitian projections of trace one (`Morse/Chapter3/ProjectiveSpace.lean`), and
`P = {Z₀ = 0} = {Q₀₀ = 0}` (Milnor's "after a linear change of coordinates"; a unitary change of
coordinates carries any hyperplane to this one).

* `Morse.CP.aff`, `Morse.CP.proj`: **the affine chart** `ℂPⁿ − P → ℂⁿ`,
  `Q ↦ (Q_{j0}/Q_{00})_j` (`= (Z_j/Z₀)_j`), and its inverse `u ↦` the projection onto the line of
  `(1, u)`; `Morse.CP.proj_aff_and_norm`: they are inverse, and `‖aff Q‖² = (1 − Q₀₀)/Q₀₀`.
* `Morse.CP.theta`, `Morse.CP.cpxJ`, `Morse.CP.isOrthComplexStructure_cpxJ`: `ℂⁿ` as the Euclidean
  space `𝔼 (2n)` with its complex structure (multiplication by `i`).
* `Morse.CP.affinePart V ⊆ 𝔼 (2n)`, `Morse.CP.hyperplaneSection V ⊆ V`: `V − P` in the affine chart,
  and `V ∩ P`; `Morse.CP.affineHomeomorph`: `V − P ≅ affinePart V`;
  `Morse.CP.tendsto_norm_affineHomeomorph_symm`: the affine coordinates tend to `∞` at `V ∩ P`.
* `Morse.corollary_7_3`: **Corollary 7.3 over a field**, for closed `V ⊆ ℂPⁿ` whose affine part is
  a complex submanifold of complex dimension `k`, under Hypothesis (N); from
  `Morse.corollary_7_3_of_section` (`Morse/Chapter5/HyperplaneSection.lean`).

## Deviations from Milnor, and what he leaves implicit

* **"Algebraic variety with singular points in `P`"** is replaced by what the proof uses: `V`
  closed in `ℂPⁿ`, and `V − P` a complex submanifold of the affine space (for a projective variety
  the zero set is closed, and away from the singular points it is a complex submanifold; that is
  not formalized).  Its real dimension is `2k` everywhere, the *pure dimension* hypothesis that
  Milnor omits (exposition, §5: the counterexample `Π ∪ L` in `ℂP₄`).
* **Hypothesis (N)** (`Morse.HypothesisN`) is assumed, as Milnor does in Theorem 7.4: it follows
  from the triangulability of `(V, V ∩ P)` (Łojasiewicz), which is not formalized.  Milnor's own
  proof of 7.3 uses Lefschetz duality instead; the duality-free proof is the exposition's.
* **Homology over a field**, not over `ℤ`.
* **Theorem 7.4** (`π_r(V, V ∩ P) = 0` for `r < k`) is `Morse.theorem_7_4`
  (`Morse/Chapter5/LefschetzHomotopy.lean`).
-/

open Matrix Set Filter Topology Function Module
open scoped ContDiff Manifold Morse.MatrixInner

noncomputable section

namespace Morse

namespace CP

variable {n : ℕ}

/-- `ℂⁿ` as a real inner product space. -/
abbrev Cn (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-- **The affine chart** of `ℂPⁿ − P`, `P = {Z₀ = 0}`: `[Z] ↦ (Z_j / Z₀)_{j ≥ 1}`, read on
projections as `Q ↦ (Q_{j0} / Q_{00})_j`. -/
def aff (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : Cn n :=
  WithLp.toLp 2 fun i => Q i.succ 0 / Q 0 0

/-- The vector `(1, u)`. -/
def lift (u : Cn n) : Fin (n + 1) → ℂ := Fin.cons 1 fun i => u i

/-- `1 + ‖u‖²`, as a complex number. -/
def nc (u : Cn n) : ℂ := ((1 + ‖u‖ ^ 2 : ℝ) : ℂ)

theorem nc_ne_zero (u : Cn n) : nc u ≠ 0 := by
  unfold nc; exact_mod_cast (by positivity : (0 : ℝ) < 1 + ‖u‖ ^ 2).ne'

/-- **The inverse of the affine chart**: `u ↦` the projection onto the line of `(1, u)`. -/
def proj (u : Cn n) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.of fun a b => lift u a * star (lift u b) / nc u

theorem sum_lift (u : Cn n) : ∑ a, lift u a * star (lift u a) = nc u := by
  rw [Fin.sum_univ_succ, nc, EuclideanSpace.norm_sq_eq]
  simp only [lift, Fin.cons_zero, Fin.cons_succ, star_one, mul_one]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast; rfl

theorem proj_mem (u : Cn n) : proj u ∈ grassmannian (Fin (n + 1)) 1 := by
  have hc := nc_ne_zero u
  refine ⟨?_, ?_, ?_⟩
  · ext a b
    simp only [proj, conjTranspose_apply, of_apply, star_div₀, star_mul', star_star]
    rw [mul_comm]
    congr 1
    simp [nc, Complex.conj_ofReal]
  · ext a b
    simp only [proj, mul_apply, of_apply]
    have : ∀ c, lift u a * star (lift u c) / nc u * (lift u c * star (lift u b) / nc u) =
        lift u a * star (lift u b) / nc u * (lift u c * star (lift u c)) / nc u := fun c => by
      ring
    simp only [this, ← Finset.sum_div, ← Finset.mul_sum, sum_lift]
    field_simp
  · simp only [trace, diag, proj, of_apply]
    rw [← Finset.sum_div, sum_lift, div_self hc, Nat.cast_one]

theorem proj_zero_zero (u : Cn n) : proj u 0 0 = 1 / nc u := by
  simp [proj, lift]

theorem aff_proj (u : Cn n) : aff (proj u) = u := by
  have hc := nc_ne_zero u
  ext i
  simp only [aff, proj_zero_zero]
  simp only [proj, of_apply, lift, Fin.cons_succ, Fin.cons_zero, star_one, mul_one]
  field_simp

/-- On `ℂPⁿ`, `Q₀₀ = |f₀|²` is real and non-negative. -/
theorem zero_zero_eq {Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hQ : Q ∈ grassmannian (Fin (n + 1)) 1) : Q 0 0 = ((Q 0 0).re : ℂ) ∧ 0 ≤ (Q 0 0).re := by
  obtain ⟨f, -, hf⟩ := exists_vec_of_mem hQ
  rw [hf, Complex.star_def, Complex.mul_conj]
  exact ⟨by simp, by simp [Complex.normSq_nonneg]⟩

/-- **The affine chart and its inverse**: `proj (aff Q) = Q` on `ℂPⁿ − P`, and
`‖aff Q‖² = (1 − Q₀₀)/Q₀₀`. -/
theorem proj_aff_and_norm {Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hQ : Q ∈ grassmannian (Fin (n + 1)) 1) (h0 : Q 0 0 ≠ 0) :
    proj (aff Q) = Q ∧ ‖aff Q‖ ^ 2 = (1 - (Q 0 0).re) / (Q 0 0).re := by
  obtain ⟨f, hf1, hf⟩ := exists_vec_of_mem hQ
  have hf0 : f 0 ≠ 0 := fun h => h0 (by rw [hf, h, zero_mul])
  have hns : Complex.normSq (f 0) ≠ 0 := (Complex.normSq_pos.2 hf0).ne'
  have hQ00 : (Q 0 0).re = Complex.normSq (f 0) := by
    rw [hf, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
  have haff : ∀ i, aff Q i = f i.succ / f 0 := fun i => by
    simp only [aff, hf, Complex.star_def]
    field_simp [map_ne_zero (starRingEnd ℂ) |>.2 hf0]
  have hnorm : ‖aff Q‖ ^ 2 = (1 - Complex.normSq (f 0)) / Complex.normSq (f 0) := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [haff, norm_div, div_pow]
    rw [← Finset.sum_div, ← hf1, Fin.sum_univ_succ]
    simp only [Complex.normSq_eq_norm_sq, add_sub_cancel_left]
  refine ⟨?_, by rw [hnorm, hQ00]⟩
  have hnc : nc (aff Q) = ((1 / Complex.normSq (f 0) : ℝ) : ℂ) := by
    rw [nc, hnorm]
    congr 1
    field_simp
    ring
  have hlift : lift (aff Q) = fun a => f a / f 0 := by
    funext a
    refine Fin.cases ?_ (fun i => ?_) a
    · simp [lift, hf0]
    · simp [lift, haff]
  ext a b
  simp only [proj, of_apply, hlift, hnc, hf, star_div₀]
  have h2 : (f 0 : ℂ) * star (f 0) = (Complex.normSq (f 0) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj]
  have hstar : star (f 0) ≠ 0 := star_ne_zero.2 hf0
  have hns' : (Complex.normSq (f 0) : ℂ) ≠ 0 := by exact_mod_cast hns
  push_cast
  rw [← h2]
  field_simp

local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)

theorem finrank_Cn (n : ℕ) : finrank ℝ (Cn n) = 2 * n := by
  rw [finrank_real_of_complex, finrank_euclideanSpace_fin]

/-- **`ℂⁿ = ℝ²ⁿ`**: a real linear isometry `ℂⁿ ≃ 𝔼 (2n)`. -/
def theta (n : ℕ) : Cn n ≃ₗᵢ[ℝ] 𝔼 (2 * n) :=
  ((stdOrthonormalBasis ℝ (Cn n)).reindex (finCongr (finrank_Cn n))).repr

/-- Multiplication by `i` on `ℂⁿ`, as a real linear map. -/
def mulI (n : ℕ) : Cn n →L[ℝ] Cn n :=
  (Complex.I • ContinuousLinearMap.id ℂ (Cn n)).restrictScalars ℝ

/-- **The complex structure of `ℂⁿ` on `𝔼 (2n)`**: multiplication by `i` read through `theta`. -/
def cpxJ (n : ℕ) : 𝔼 (2 * n) →L[ℝ] 𝔼 (2 * n) :=
  ((theta n).toContinuousLinearEquiv : Cn n →L[ℝ] 𝔼 (2 * n)).comp
    ((mulI n).comp ((theta n).symm.toContinuousLinearEquiv : 𝔼 (2 * n) →L[ℝ] Cn n))

theorem cpxJ_apply (v : 𝔼 (2 * n)) : cpxJ n v = theta n (Complex.I • (theta n).symm v) := rfl

theorem isOrthComplexStructure_cpxJ (n : ℕ) : IsOrthComplexStructure (cpxJ n) where
  sq v := by
    rw [cpxJ_apply, cpxJ_apply, LinearIsometryEquiv.symm_apply_apply, smul_smul, Complex.I_mul_I,
      neg_one_smul, map_neg, LinearIsometryEquiv.apply_symm_apply]
  inner v w := by
    rw [cpxJ_apply, cpxJ_apply, LinearIsometryEquiv.inner_map_map,
      real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
      real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two v w,
      ← smul_add, norm_smul, norm_smul, norm_smul, Complex.norm_I, one_mul, one_mul, one_mul,
      ← map_add, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map,
      LinearIsometryEquiv.norm_map]

theorem continuous_lift (a : Fin (n + 1)) : Continuous fun u : Cn n => lift u a := by
  refine Fin.cases ?_ (fun i => ?_) a
  · simp only [lift, Fin.cons_zero]; exact continuous_const
  · simp only [lift, Fin.cons_succ]; exact PiLp.continuous_apply 2 _ i

theorem continuous_proj : Continuous (proj : Cn n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  have : (proj : Cn n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      fun u => ofCLM (fun a b => lift u a * star (lift u b) / nc u) := rfl
  rw [this]
  refine ofCLM.continuous.comp (continuous_pi fun a => continuous_pi fun b => ?_)
  refine ((continuous_lift a).mul ((continuous_lift b).star)).div ?_ fun u => nc_ne_zero u
  exact Complex.continuous_ofReal.comp (continuous_const.add (continuous_norm.pow 2))

theorem continuousOn_aff :
    ContinuousOn (aff : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → Cn n) {Q | Q 0 0 ≠ 0} := by
  refine (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.2 fun i => ?_)
  exact ((contDiff_entry (𝕜 := ℂ) i.succ 0).continuous.continuousOn).div
    (contDiff_entry (𝕜 := ℂ) 0 0).continuous.continuousOn fun Q hQ => hQ

variable (V : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))

/-- **The affine part `V − P`** of `V ⊆ ℂPⁿ`, read in `ℂⁿ = 𝔼 (2n)` through the affine chart. -/
def affinePart : Set (𝔼 (2 * n)) := {x | proj ((theta n).symm x) ∈ V}

/-- **The hyperplane section `V ∩ P`**, `P = {Z₀ = 0}`, as a subset of `V`. -/
def hyperplaneSection : Set V := {x | (x : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) 0 0 = 0}

variable {V}

theorem proj_zero_zero_ne (u : Cn n) : proj u 0 0 ≠ 0 := by
  rw [proj_zero_zero]; exact one_div_ne_zero (nc_ne_zero u)

/-- **The affine chart identifies `V − P` with its affine part.** -/
def affineHomeomorph (hV : V ⊆ grassmannian (Fin (n + 1)) 1) :
    affinePart V ≃ₜ ((hyperplaneSection V)ᶜ : Set V) where
  toFun x := ⟨⟨proj ((theta n).symm x), x.2⟩, proj_zero_zero_ne _⟩
  invFun y := ⟨theta n (aff y), by
    change proj ((theta n).symm (theta n (aff y))) ∈ V
    rw [LinearIsometryEquiv.symm_apply_apply, (proj_aff_and_norm (hV y.1.2) y.2).1]
    exact y.1.2⟩
  left_inv x := Subtype.ext (by
    change theta n (aff (proj ((theta n).symm x))) = x
    rw [aff_proj, LinearIsometryEquiv.apply_symm_apply])
  right_inv y := Subtype.ext (Subtype.ext (by
    change proj ((theta n).symm (theta n (aff y))) = y
    rw [LinearIsometryEquiv.symm_apply_apply, (proj_aff_and_norm (hV y.1.2) y.2).1]))
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact continuous_proj.comp ((theta n).symm.continuous.comp continuous_subtype_val)
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    refine (theta n).continuous.comp ?_
    refine continuousOn_aff.comp_continuous (continuous_subtype_val.comp continuous_subtype_val)
      fun y => y.2

/-- **`L_p → ∞` at the hyperplane section**: near a point of `V ∩ P`, the affine coordinates of
the points of `V − P` are large (`‖aff Q‖² = (1 − Q₀₀)/Q₀₀` and `Q₀₀ → 0`). -/
theorem tendsto_norm_affineHomeomorph_symm (hV : V ⊆ grassmannian (Fin (n + 1)) 1)
    (x : V) (hx : x ∈ hyperplaneSection V) (R : ℝ) :
    ∀ᶠ y in 𝓝 x, ∀ hy : y ∈ (hyperplaneSection V)ᶜ,
      R ≤ ‖(((affineHomeomorph hV).symm ⟨y, hy⟩ : affinePart V) : 𝔼 (2 * n))‖ := by
  set δ : ℝ := 1 / (1 + R ^ 2) with hδ
  have hδ0 : 0 < δ := by positivity
  have hc : Continuous fun y : V => ((y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) 0 0).re :=
    Complex.continuous_re.comp ((contDiff_entry (𝕜 := ℂ) 0 0).continuous.comp
      continuous_subtype_val)
  have hx0 : ((x : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) 0 0).re < δ := by
    rw [show (x : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) 0 0 = 0 from hx, Complex.zero_re]
    exact hδ0
  filter_upwards [hc.continuousAt.eventually (gt_mem_nhds hx0)] with y hy hyA
  have hy0 : (y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) 0 0 ≠ 0 := hyA
  obtain ⟨-, hnorm⟩ := proj_aff_and_norm (hV y.2) hy0
  obtain ⟨hre, hpos⟩ := zero_zero_eq (hV y.2)
  set t := ((y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) 0 0).re
  have ht : 0 < t := lt_of_le_of_ne hpos fun h => hy0 (by rw [hre, ← h, Complex.ofReal_zero])
  change R ≤ ‖theta n (aff (y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))‖
  rw [LinearIsometryEquiv.norm_map]
  have hR2 : R ^ 2 ≤ ‖aff (y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)‖ ^ 2 := by
    rw [hnorm]
    have h1 : t * (1 + R ^ 2) < 1 := by
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 1 + R ^ 2)).1 (hy.trans_eq (by rw [hδ]))
      linarith
    rw [le_div_iff₀ ht]
    nlinarith
  exact (abs_le_of_sq_le_sq' hR2 (norm_nonneg _)).2

end CP

open CP Homology

/-- **Corollary 7.3 (Lefschetz)** (Milnor p. 41), over a field: let `V ⊆ ℂPⁿ` be closed and `P` the
hyperplane `Z₀ = 0`, such that the affine part `V − P ⊆ ℂⁿ = 𝔼 (2n)` is a complex submanifold of
complex dimension `k` (`V` of pure dimension `k`, with all its singular points in `P`), and assume
Hypothesis (N) for `V ∩ P ⊆ V`.  Then `H_r(V ∩ P; 𝕜) → H_r(V; 𝕜)` is an isomorphism for
`r < k − 1` and onto for `r = k − 1`. -/
theorem corollary_7_3 {n k w : ℕ} {V : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)}
    (hV : V ⊆ grassmannian (Fin (n + 1)) 1) (hVc : IsClosed V)
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n)))
      (EuclideanSpace ℝ (Fin (2 * k))) (EuclideanSpace ℝ (Fin w)) (affinePart V))
    (hc : IsComplexSubmanifold hM (cpxJ n)) (hN : HypothesisN (hyperplaneSection V))
    {𝕜 : Type} [Field 𝕜] (r : ℕ) :
    (r + 1 < k → Bijective ((subsetTripleLongExactSeq 𝕜 (empty_subset (hyperplaneSection V))
        (subset_univ (hyperplaneSection V))).f r)) ∧
      (r < k → Surjective ((subsetTripleLongExactSeq 𝕜 (empty_subset (hyperplaneSection V))
        (subset_univ (hyperplaneSection V))).f r)) := by
  have : CompactSpace V := isCompact_iff_compactSpace.1 (CP.isCompact.of_isClosed_subset hVc hV)
  have hA : IsClosed (hyperplaneSection V) :=
    isClosed_eq ((contDiff_entry (𝕜 := ℂ) 0 0).continuous.comp continuous_subtype_val)
      continuous_const
  have hcl : IsClosed (affinePart V) :=
    hVc.preimage (continuous_proj.comp (theta n).symm.continuous)
  exact corollary_7_3_of_section hM hA hcl (isOrthComplexStructure_cpxJ n) hc
    (affineHomeomorph hV) (fun x hx R => tendsto_norm_affineHomeomorph_symm hV x hx R) hN r

end Morse
