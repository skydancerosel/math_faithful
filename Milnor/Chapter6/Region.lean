import Milnor.Chapter6.Index
import Milnor.Chapter6.LevelZero

/-!
# The index sum over a region (Milnor pp. 33–34)

For a smooth vector field `v` on `ℝⁿ⁺¹` and a compact region `X = {G ≥ 0}` with smooth boundary
`∂X = G⁻¹(0)`, if the zeros of `v` in `X` are the centres `z₁, …, z_k` of disjoint closed balls
of radius `ε` contained in the interior, then the sum of the indices of `v` at the `zᵢ` is the
degree of the Gauss map `v/|v| : ∂X → Sⁿ`.  This is the key step of Milnor's proof of Lemma 3
(Hopf) and of the Poincaré–Hopf theorem.
-/

open Set Module Filter Topology Function TopologicalSpace
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

namespace Sphere

variable {n : ℕ}

/-- A base point of the sphere. -/
def sphPt : Sph n := ⟨EuclideanSpace.single 0 1, by rw [mem_iff_norm]; simp⟩

/-- Normalization into the sphere (a fixed point at `0`). -/
def nv0 (y : EuclideanSpace ℝ (Fin (n + 1))) : Sph n :=
  open Classical in
  if h : y ≠ 0 then ⟨normalize y, normalize_mem h⟩ else sphPt

theorem nv0_val {y : EuclideanSpace ℝ (Fin (n + 1))} (h : y ≠ 0) : (nv0 y).1 = normalize y := by
  unfold nv0; rw [dif_pos h]

theorem sphMap_eq_nv0 {v : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {z : EuclideanSpace ℝ (Fin (n + 1))} {ε : ℝ} {u : Sph n} (h : v (z + ε • u.1) ≠ 0) :
    sphMap v z ε u = nv0 (v (z + ε • u.1)) := by
  apply Subtype.ext; rw [sphMap_val h, nv0_val h]

/-- Smoothness of `nv0 ∘ w` for a smooth nonvanishing `w`. -/
theorem contMDiff_nv0_comp {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    {w : M' → EuclideanSpace ℝ (Fin (n + 1))}
    (hw : ContMDiff I' 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ w) (hne : ∀ x, w x ≠ 0) :
    ContMDiff I' 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (fun x => nv0 (w x)) := by
  set F : M' → EuclideanSpace ℝ (Fin (n + 1)) := fun x => normalize (w x) with hFdef
  have hFS : ∀ x, F x ∈ Sph n := fun x => normalize_mem (hne x)
  have hF : ContMDiff I' 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ F := by
    intro x
    exact (contDiffAt_normalize (hne x)).contMDiffAt.comp x hw.contMDiffAt
  have heq : (fun x => nv0 (w x)) = fun x => ⟨F x, hFS x⟩ := by
    funext x; exact Subtype.ext (nv0_val (hne x))
  rw [heq]
  exact (sphS n).contMDiff_codRestrict hF hFS

/-! ### The defining function of a sphere of radius `ε` about `z` -/

/-- `Gsph z ε x = |x - z|²/ε² - 1`. -/
def Gsph (z : EuclideanSpace ℝ (Fin (n + 1))) (ε : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  sphG (ε⁻¹ • (x - z))

theorem contMDiff_Gsph (z : EuclideanSpace ℝ (Fin (n + 1))) (ε : ℝ) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) ∞ (Gsph z ε) := by
  have h : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin (n + 1)) => ε⁻¹ • (x - z)) :=
    (contDiff_id.sub contDiff_const).const_smul ε⁻¹
  exact contMDiff_sphG.comp (contMDiff_iff_contDiff.2 h)

/-- The affine map `u ↦ z + ε u`. -/
def aff (z : EuclideanSpace ℝ (Fin (n + 1))) (ε : ℝ) (u : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin (n + 1)) := z + ε • u

theorem Gsph_aff {z : EuclideanSpace ℝ (Fin (n + 1))} {ε : ℝ} (hε : ε ≠ 0)
    (u : EuclideanSpace ℝ (Fin (n + 1))) : Gsph z ε (aff z ε u) = sphG u := by
  simp [Gsph, aff, smul_smul, inv_mul_cancel₀ hε]

theorem contMDiff_aff (z : EuclideanSpace ℝ (Fin (n + 1))) (ε : ℝ) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞
      (aff z ε) :=
  contMDiff_iff_contDiff.2 (contDiff_const.add (contDiff_id.const_smul ε))

theorem mfd_aff (z : EuclideanSpace ℝ (Fin (n + 1))) (ε : ℝ) (u : EuclideanSpace ℝ (Fin (n + 1))) :
    mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (aff z ε) u =
      ε • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n + 1))) :=
  HasMFDerivAt.mfd_eq (((hasFDerivAt_id u).const_smul ε).const_add z).hasMFDerivAt

theorem Gsph_eq {z : EuclideanSpace ℝ (Fin (n + 1))} {ε : ℝ} (hε : 0 < ε)
    (x : EuclideanSpace ℝ (Fin (n + 1))) : Gsph z ε x = (dist x z / ε) ^ 2 - 1 := by
  simp only [Gsph, sphG, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hε, dist_eq_norm]
  ring

theorem Gsph_neg_iff {z : EuclideanSpace ℝ (Fin (n + 1))} {ε : ℝ} (hε : 0 < ε)
    (x : EuclideanSpace ℝ (Fin (n + 1))) : Gsph z ε x < 0 ↔ dist x z < ε := by
  rw [Gsph_eq hε, sub_neg, pow_lt_one_iff_of_nonneg (div_nonneg dist_nonneg hε.le) two_ne_zero,
    div_lt_one hε]

theorem Gsph_eq_zero_iff {z : EuclideanSpace ℝ (Fin (n + 1))} {ε : ℝ} (hε : 0 < ε)
    (x : EuclideanSpace ℝ (Fin (n + 1))) : Gsph z ε x = 0 ↔ dist x z = ε := by
  rw [Gsph_eq hε, sub_eq_zero, pow_eq_one_iff_of_nonneg (div_nonneg dist_nonneg hε.le) two_ne_zero,
    div_eq_one_iff_eq hε.ne']

theorem Gsph_pos_iff {z : EuclideanSpace ℝ (Fin (n + 1))} {ε : ℝ} (hε : 0 < ε)
    (x : EuclideanSpace ℝ (Fin (n + 1))) : 0 < Gsph z ε x ↔ ε < dist x z := by
  rw [Gsph_eq hε, sub_pos, one_lt_pow_iff_of_nonneg (div_nonneg dist_nonneg hε.le) two_ne_zero,
    one_lt_div hε]

theorem Gsph_nonneg_iff {z : EuclideanSpace ℝ (Fin (n + 1))} {ε : ℝ} (hε : 0 < ε)
    (x : EuclideanSpace ℝ (Fin (n + 1))) : 0 ≤ Gsph z ε x ↔ ε ≤ dist x z := by
  rw [← not_lt, ← not_lt, Gsph_neg_iff hε]

theorem isRegularValue_Gsph {z : EuclideanSpace ℝ (Fin (n + 1))} {ε : ℝ} (hε : 0 < ε) :
    IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) (Gsph z ε) 0 := by
  intro x hx
  set A : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun x => ε⁻¹ • (x - z) with hA
  have hAd : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      A x (ε⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n + 1)))) :=
    (((hasFDerivAt_id x).sub_const z).const_smul ε⁻¹).hasMFDerivAt
  have hsG : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) sphG (A x)
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) sphG (A x) :) :=
    hasMFDerivAt_mfd (contMDiff_sphG.mdifferentiableAt (by simp))
  have hchain := HasMFDerivAt.mfd_eq (hsG.comp x hAd)
  show Function.Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) (Gsph z ε) x)
  have : Gsph z ε = sphG ∘ A := rfl
  rw [this, hchain]
  have hsurj : Function.Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) sphG (A x)) :=
    isRegularValue_sphG (A x) hx
  refine hsurj.comp fun y => ⟨ε • y, ?_⟩
  show ε⁻¹ • (ε • y) = y
  rw [smul_smul, inv_mul_cancel₀ hε.ne', one_smul]

/-- The ambient sign of the affine map `u ↦ z + εu` is `+1` for `ε > 0`. -/
theorem signAt_aff {z : EuclideanSpace ℝ (Fin (n + 1))} {ε : ℝ} (hε : 0 < ε)
    (a : Orientation ℝ (EuclideanSpace ℝ (Fin (n + 1))) (Fin (n + 1)))
    (u : EuclideanSpace ℝ (Fin (n + 1))) :
    signAt (Orient.const a) (Orient.const a) (aff z ε) u = 1 := by
  unfold signAt
  rw [Orient.const_or, Orient.const_or, mfd_aff, orSign_self_eq_sgn_det hE]
  simp only [ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.coe_id, LinearMap.det_smul,
    LinearMap.det_id, mul_one, hE]
  exact sgn_pos (pow_pos hε _)

/-! ### The level functions of a region with balls removed -/

section region

variable {k : ℕ}

/-- The level functions: `G` and the sphere functions `Gsph (z i) ε`. -/
def Gf (G : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (z : Fin k → EuclideanSpace ℝ (Fin (n + 1)))
    (ε : ℝ) : Option (Fin k) → EuclideanSpace ℝ (Fin (n + 1)) → ℝ
  | none => G
  | some i => Gsph (z i) ε

/-- The product of the level functions: `X = {gProd ≥ 0}` is the region with the balls removed. -/
def gProd (G : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (z : Fin k → EuclideanSpace ℝ (Fin (n + 1)))
    (ε : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))) : ℝ := ∏ j, Gf G z ε j x

variable {G : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {z : Fin k → EuclideanSpace ℝ (Fin (n + 1))}
  {ε : ℝ}

/-- At a zero of one level function, the others are positive. -/
theorem Gf_pos_of_ne (hε : 0 < ε) (hzin : ∀ i x, dist x (z i) ≤ ε → 0 < G x)
    (hdisj : ∀ i j, i ≠ j → 2 * ε < dist (z i) (z j)) {x : EuclideanSpace ℝ (Fin (n + 1))}
    {j l : Option (Fin k)} (hj : Gf G z ε j x = 0) (hl : l ≠ j) : 0 < Gf G z ε l x := by
  cases j with
  | none =>
    cases l with
    | none => exact absurd rfl hl
    | some i =>
      show 0 < Gsph (z i) ε x
      rw [Gsph_pos_iff hε]
      by_contra h
      push_neg at h
      have := hzin i x h
      change G x = 0 at hj
      linarith
  | some i =>
    change Gsph (z i) ε x = 0 at hj
    rw [Gsph_eq_zero_iff hε] at hj
    cases l with
    | none => exact hzin i x hj.le
    | some i' =>
      have hii : i ≠ i' := fun h => hl (by rw [h])
      show 0 < Gsph (z i') ε x
      rw [Gsph_pos_iff hε]
      have h1 := hdisj i i' hii
      have h2 := dist_triangle (z i) x (z i')
      rw [dist_comm (z i) x, hj] at h2
      linarith

theorem gProd_eq_zero_iff {x : EuclideanSpace ℝ (Fin (n + 1))} :
    gProd G z ε x = 0 ↔ ∃ j, Gf G z ε j x = 0 := by
  rw [gProd, Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and]

theorem gProd_eq_mul (x : EuclideanSpace ℝ (Fin (n + 1))) :
    gProd G z ε x = G x * ∏ i, Gsph (z i) ε x := by
  unfold gProd; rw [Fintype.prod_option]; rfl

/-- The vector field does not vanish on the boundary of the region with the balls removed. -/
theorem ne_zero_of_gProd_eq_zero (hε : 0 < ε) (hzin : ∀ i x, dist x (z i) ≤ ε → 0 < G x)
    (hdisj : ∀ i j, i ≠ j → 2 * ε < dist (z i) (z j))
    {v : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hzero : ∀ x, 0 ≤ G x → v x = 0 → ∃ i, x = z i) {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : gProd G z ε x = 0) : v x ≠ 0 := by
  obtain ⟨j, hj⟩ := gProd_eq_zero_iff.1 hx
  have hG : 0 ≤ G x := by
    cases j with
    | none => exact le_of_eq (id hj).symm
    | some i => exact (Gf_pos_of_ne hε hzin hdisj hj (by simp) : 0 < Gf G z ε none x).le
  intro hv
  obtain ⟨i₀, rfl⟩ := hzero x hG hv
  have hneg : Gsph (z i₀) ε (z i₀) < 0 := (Gsph_neg_iff hε _).2 (by rw [dist_self]; exact hε)
  by_cases hji : j = some i₀
  · subst hji
    change Gsph (z i₀) ε (z i₀) = 0 at hj
    linarith
  · have := Gf_pos_of_ne hε hzin hdisj hj (fun h => hji h.symm)
    change 0 < Gsph (z i₀) ε (z i₀) at this
    linarith

/-- Where `gProd ≥ 0`, we are in the region and outside the open balls. -/
theorem mem_K_of_gProd_nonneg (hε : 0 < ε) (hzin : ∀ i x, dist x (z i) ≤ ε → 0 < G x)
    (hdisj : ∀ i j, i ≠ j → 2 * ε < dist (z i) (z j)) {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : 0 ≤ gProd G z ε x) : 0 ≤ G x ∧ ∀ i, ε ≤ dist x (z i) := by
  have hball : ∀ i, ε ≤ dist x (z i) := by
    intro i
    by_contra h
    push_neg at h
    have hneg : Gf G z ε (some i) x < 0 := (Gsph_neg_iff hε x).2 h
    have hpos : ∀ l ∈ Finset.univ.erase (some i), 0 < Gf G z ε l x := by
      intro l hl
      have hl' : l ≠ some i := Finset.ne_of_mem_erase hl
      cases l with
      | none => exact hzin i x h.le
      | some i' =>
        have hii : i ≠ i' := fun heq => hl' (by rw [heq])
        show 0 < Gsph (z i') ε x
        rw [Gsph_pos_iff hε]
        have h1 := hdisj i i' hii
        have h2 := dist_triangle (z i) x (z i')
        rw [dist_comm (z i) x] at h2
        linarith
    have : gProd G z ε x < 0 := by
      unfold gProd
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (some i))]
      exact mul_neg_of_neg_of_pos hneg (Finset.prod_pos hpos)
    linarith
  refine ⟨?_, hball⟩
  by_contra hG
  push_neg at hG
  have hpos : ∀ i, 0 < Gsph (z i) ε x := fun i => by
    rw [Gsph_pos_iff hε]
    refine lt_of_le_of_ne (hball i) fun heq => ?_
    have := hzin i x heq.symm.le
    linarith
  have : gProd G z ε x < 0 := by
    rw [gProd_eq_mul]
    exact mul_neg_of_neg_of_pos hG (Finset.prod_pos fun i _ => hpos i)
  linarith

/-- **The index sum over a region** (Milnor pp. 33–34).  Let `X = {G ≥ 0}` be a compact region
of `ℝⁿ⁺¹` (`n ≥ 1`) with `0` a regular value of `G`, and let the closed `ε`-balls about
`z₁, …, z_k` be pairwise disjoint and contained in `{G > 0}`.  If the zeros of the smooth vector
field `v` in `X` are exactly the `zᵢ`, then the sum of the indices of `v` at the `zᵢ` (at radius
`ε`) is the degree of the Gauss map `v/|v| : ∂X → Sⁿ`, where `∂X = G⁻¹(0)` carries the
orientation induced as the boundary of the *complement* of `X` (the same convention as the
orientation `sphOr` of `Sⁿ`, so this is Milnor's degree with both boundary orientations reversed,
i.e. Milnor's degree itself). -/
theorem sum_indexAt_eq_deg (hn : 0 < n)
    {v : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hv : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ v)
    (hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) ∞ G)
    (h0 : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) G 0)
    (hX : IsCompact {x | 0 ≤ G x}) (hε : 0 < ε)
    (hzin : ∀ i x, dist x (z i) ≤ ε → 0 < G x)
    (hdisj : ∀ i j, i ≠ j → 2 * ε < dist (z i) (z j))
    (hzero : ∀ x, 0 ≤ G x → v x = 0 → ∃ i, x = z i) :
    letI := (isSliceSubmanifold_preimage (Z := EuclideanSpace ℝ (Fin n)) (finrank_Z_add hE hZ)
      hG h0).chartedSpace
    ∑ i, indexAt v (z i) ε =
      deg ((levelOrientM hE hZ (Orient.const (finBasisOfFinrankEq ℝ _ hE).orientation) hG h0).neg hZ)
        (sphOr n) (fun q : G ⁻¹' {0} => nv0 (v q.1)) := by
  classical
  have hS := isSliceSubmanifold_preimage (Z := EuclideanSpace ℝ (Fin n)) (finrank_Z_add hE hZ) hG h0
  letI := hS.chartedSpace
  haveI := hS.isManifold
  haveI : PreconnectedSpace (Sph n) := preconnectedSpace hn
  set a₀ := (finBasisOfFinrankEq ℝ (EuclideanSpace ℝ (Fin (n + 1))) hE).orientation with ha₀
  set oE : Orient 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin (n + 1))) (n + 1) :=
    Orient.const a₀ with hoE
  have hsphOr : sphOr n = levelOrientM hE hZ oE contMDiff_sphG isRegularValue_sphG :=
    levelOrient_eq_levelOrientM hE hZ a₀ contMDiff_sphG isRegularValue_sphG
  -- the level functions
  have hGfs : ∀ j, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) ∞ (Gf G z ε j) := by
    intro j; cases j
    · exact hG
    · exact contMDiff_Gsph _ _
  have hGfr : ∀ j, IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) (Gf G z ε j) 0 := by
    intro j; cases j
    · exact h0
    · exact isRegularValue_Gsph hε
  have hgs : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) ∞ (gProd G z ε) :=
    contMDiff_finsetProd fun j _ => hGfs j
  have hcpos : ∀ x j, Gf G z ε j x = 0 → 0 < ∏ l ∈ Finset.univ.erase j, Gf G z ε l x :=
    fun x j hj => Finset.prod_pos fun l hl =>
      Gf_pos_of_ne hε hzin hdisj hj (Finset.ne_of_mem_erase hl)
  have hgd : ∀ x j, Gf G z ε j x = 0 →
      mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) (gProd G z ε) x =
        (∏ l ∈ Finset.univ.erase j, Gf G z ε l x) •
          mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) (Gf G z ε j) x :=
    fun x j hj => mfd_prod_of_eq_zero hGfs j hj
  have hgr : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) (gProd G z ε) 0 := by
    intro x hx
    obtain ⟨j, hj⟩ := gProd_eq_zero_iff.1 hx
    show Function.Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) (gProd G z ε) x)
    rw [hgd x j hj]
    have hsj : Function.Surjective
        (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) (Gf G z ε j) x) := hGfr j x hj
    intro t
    obtain ⟨w, hw⟩ := hsj t
    refine ⟨(∏ l ∈ Finset.univ.erase j, Gf G z ε l x)⁻¹ • w, ?_⟩
    simp only [ContinuousLinearMap.smul_apply, map_smul, hw, smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (hcpos x j hj).ne', one_mul]
  -- the vector field does not vanish on the level sets
  have hvne : ∀ x, gProd G z ε x = 0 → v x ≠ 0 := fun x hx =>
    ne_zero_of_gProd_eq_zero hε hzin hdisj hzero hx
  have hvj : ∀ j x, Gf G z ε j x = 0 → v x ≠ 0 := fun j x hj =>
    hvne x (gProd_eq_zero_iff.2 ⟨j, hj⟩)
  have hne : ∀ i (u : Sph n), v (aff (z i) ε u.1) ≠ 0 := fun i u =>
    hvj (some i) _ (by show Gsph (z i) ε (aff (z i) ε u.1) = 0; rw [Gsph_aff hε.ne']; exact u.2)
  -- the open set where `v ≠ 0`
  set U : Opens (EuclideanSpace ℝ (Fin (n + 1))) :=
    ⟨{x | v x ≠ 0}, isOpen_ne_fun hv.continuous continuous_const⟩ with hU
  have hnvU : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (fun x : U => nv0 (v x.1)) :=
    contMDiff_nv0_comp (hv.comp contMDiff_subtype_val) (fun x => x.2)
  have hnvOn : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (fun x => nv0 (v x)) U := fun x hx =>
    ((contMDiffAt_subtype_iff (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) (U := U) (f := fun x => nv0 (v x))
      (x := ⟨x, hx⟩)).1 (hnvU ⟨x, hx⟩)).contMDiffWithinAt
  -- the level-set manifolds
  have hSg := isSliceSubmanifold_preimage (Z := EuclideanSpace ℝ (Fin n)) (finrank_Z_add hE hZ)
    hgs hgr
  letI := hSg.chartedSpace
  haveI := hSg.isManifold
  have hSj : ∀ j, IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin n)) ℝ ((Gf G z ε j) ⁻¹' {0}) := fun j =>
    isSliceSubmanifold_preimage (Z := EuclideanSpace ℝ (Fin n)) (finrank_Z_add hE hZ)
      (hGfs j) (hGfr j)
  -- compactness
  haveI hGc : CompactSpace (G ⁻¹' {0}) := isCompact_iff_compactSpace.1
    (hX.of_isClosed_subset (isClosed_singleton.preimage hG.continuous)
      (fun x hx => le_of_eq (mem_singleton_iff.1 hx).symm))
  have hKc : IsCompact ({x | 0 ≤ G x} ∩ ⋂ i, {x | ε ≤ dist x (z i)}) :=
    hX.inter_right (isClosed_iInter fun i =>
      isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hKU : ∀ x ∈ {x | 0 ≤ G x} ∩ ⋂ i, {x | ε ≤ dist x (z i)}, v x ≠ 0 := by
    rintro x ⟨hx1, hx2⟩ hv0
    obtain ⟨i, rfl⟩ := hzero x hx1 hv0
    have := mem_iInter.1 hx2 i
    simp only [mem_setOf_eq, dist_self] at this
    linarith
  -- the maps into the sphere
  have hFg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (fun q : (gProd G z ε) ⁻¹' {0} => nv0 (v q.1)) :=
    contMDiff_nv0_comp (hv.comp hSg.contMDiff_val) (fun q => hvne q.1 q.2)
  have hFj : ∀ j, letI := (hSj j).chartedSpace;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
        (fun q : (Gf G z ε j) ⁻¹' {0} => nv0 (v q.1)) := fun j => by
    letI := (hSj j).chartedSpace
    haveI := (hSj j).isManifold
    exact contMDiff_nv0_comp (hv.comp (hSj j).contMDiff_val) (fun q => hvj j q.1 q.2)
  -- the maps `ψᵢ : Sⁿ → S_ε(zᵢ)`
  have hψmem : ∀ i (u : Sph n), aff (z i) ε u.1 ∈ (Gf G z ε (some i)) ⁻¹' {0} := fun i u => by
    show Gsph (z i) ε (aff (z i) ε u.1) = 0
    rw [Gsph_aff hε.ne']; exact u.2
  set ψ : ∀ i, Sph n → (Gf G z ε (some i)) ⁻¹' {0} := fun i u => ⟨aff (z i) ε u.1, hψmem i u⟩
    with hψ
  have hψs : ∀ i, letI := (hSj (some i)).chartedSpace;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (ψ i) := fun i =>
    (hSj (some i)).contMDiff_codRestrict ((contMDiff_aff (z i) ε).comp contMDiff_val) (hψmem i)
  have hψbij : ∀ i, Function.Bijective (ψ i) := fun i => by
    constructor
    · intro u u' h
      have := congrArg Subtype.val h
      simp only [ψ, aff, add_right_inj] at this
      exact Subtype.ext (smul_right_injective _ hε.ne' this)
    · intro q
      have hq : sphG (ε⁻¹ • (q.1 - z i)) = 0 := q.2
      refine ⟨⟨ε⁻¹ • (q.1 - z i), hq⟩, Subtype.ext ?_⟩
      show z i + ε • (ε⁻¹ • (q.1 - z i)) = q.1
      rw [smul_smul, mul_inv_cancel₀ hε.ne', one_smul, add_sub_cancel]
  have hFψ : ∀ i, (fun u => nv0 (v (ψ i u).1)) = sphMap v (z i) ε := fun i => by
    funext u; exact (sphMap_eq_nv0 (hne i u)).symm
  -- signs of `ψᵢ` and of the inclusions
  have hsψ : ∀ i, letI := (hSj (some i)).chartedSpace; ∀ u : Sph n,
      signAt (sphOr n) (levelOrientM hE hZ oE (hGfs (some i)) (hGfr (some i))) (ψ i) u = 1 := by
    intro i
    letI := (hSj (some i)).chartedSpace
    intro u
    rw [hsphOr]
    have hdc : (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) (Gf G z ε (some i)) (aff (z i) ε u.1)).comp
        (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (aff (z i) ε) u.1) =
        (1 : ℝ) • mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) sphG u.1 := by
      rw [one_smul]
      have h1 := HasMFDerivAt.mfd_eq ((hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
        (J := 𝓘(ℝ, ℝ)) ((hGfs (some i)).mdifferentiableAt (by simp) : MDifferentiableAt _ _ (Gf G z ε (some i)) (aff (z i) ε u.1))).comp u.1
        (hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
          (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) ((contMDiff_aff (z i) ε).mdifferentiableAt (by simp))))
      have h2 : Gf G z ε (some i) ∘ aff (z i) ε = sphG := funext fun x => Gsph_aff hε.ne' x
      rw [h2] at h1
      exact h1.symm
    have := signAt_levelOrientM_map hE hZ oE oE contMDiff_sphG isRegularValue_sphG (hGfs (some i))
      (hGfr (some i)) (Φ := aff (z i) ε) (fun x hx => hψmem i ⟨x, hx⟩)
      ((contMDiff_aff (z i) ε).comp contMDiff_val) u
      ((contMDiff_aff (z i) ε).mdifferentiableAt (by simp)) ⟨1, one_pos, hdc⟩
    rw [signAt_aff hε a₀ u.1] at this
    exact this
  set ι : ∀ j, (Gf G z ε j) ⁻¹' {0} → (gProd G z ε) ⁻¹' {0} :=
    fun j q => ⟨q.1, gProd_eq_zero_iff.2 ⟨j, q.2⟩⟩ with hι
  have hιinj : ∀ j, Function.Injective (ι j) := fun j q q' h =>
    Subtype.ext (by have := congrArg Subtype.val h; exact this)
  have hιs : ∀ j, letI := (hSj j).chartedSpace;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (ι j) := fun j => by
    letI := (hSj j).chartedSpace
    haveI := (hSj j).isManifold
    exact hSg.contMDiff_codRestrict (hSj j).contMDiff_val (fun q => gProd_eq_zero_iff.2 ⟨j, q.2⟩)
  have hsι : ∀ j, letI := (hSj j).chartedSpace; ∀ q,
      signAt (levelOrientM hE hZ oE (hGfs j) (hGfr j)) (levelOrientM hE hZ oE hgs hgr) (ι j) q = 1 := by
    intro j
    letI := (hSj j).chartedSpace
    intro q
    have hid : mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        (id : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) q.1 =
        ContinuousLinearMap.id ℝ _ :=
      HasMFDerivAt.mfd_eq (hasMFDerivAt_id (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) q.1)
    have hdc : (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) (gProd G z ε) (id q.1)).comp
        (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) id q.1) =
        (∏ l ∈ Finset.univ.erase j, Gf G z ε l q.1) •
          mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) (Gf G z ε j) q.1 := by
      rw [hid, ContinuousLinearMap.comp_id]
      exact hgd q.1 j q.2
    have := signAt_levelOrientM_map hE hZ oE oE (hGfs j) (hGfr j) hgs hgr (Φ := id)
      (fun x hx => gProd_eq_zero_iff.2 ⟨j, hx⟩) (hSj j).contMDiff_val q mdifferentiableAt_id
      ⟨_, hcpos q.1 j q.2, hdc⟩
    rw [signAt_id oE q.1] at this
    exact this
  -- a common regular value
  set t : Option (Fin k) → Set (Sph n) := fun j => Option.casesOn j
    (regularValues 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (fun q : G ⁻¹' {0} => nv0 (v q.1)))
    (fun i => regularValues 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (sphMap v (z i) ε)) with ht
  have hdo : ∀ j, Dense (t j) ∧ IsOpen (t j) := by
    intro j
    cases j with
    | none =>
      exact dense_isOpen_regularValues hZ hZ (levelOrientM hE hZ oE hG h0) (sphOr n) (hFj none)
    | some i =>
      exact dense_isOpen_regularValues hZ hZ (sphOr n) (sphOr n) (contMDiff_sphMap hv (z i) (hne i))
  obtain ⟨y, hyU, hyt⟩ := exists_mem_of_dense_of_isOpen (dense_regularValues hnvU)
    (fun j => (hdo j).1) (fun j => (hdo j).2)
  have hy0 : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (fun q : G ⁻¹' {0} => nv0 (v q.1)) y := hyt none
  have hyi : ∀ i, IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (sphMap v (z i) ε) y := fun i => hyt (some i)
  have hyUU : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (fun x : U => nv0 (v x.1)) y := hyU
  -- regularity of the restrictions to the level sets
  have hregj : ∀ j, letI := (hSj j).chartedSpace;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (fun q : (Gf G z ε j) ⁻¹' {0} => nv0 (v q.1)) y := by
    intro j
    letI := (hSj j).chartedSpace
    haveI := (hSj j).isManifold
    cases j with
    | none => exact hy0
    | some i =>
      intro q hq
      obtain ⟨u, rfl⟩ := (hψbij i).2 q
      have h1 : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          ((fun q : (Gf G z ε (some i)) ⁻¹' {0} => nv0 (v q.1)) ∘ ψ i) u
          ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
            (fun q : (Gf G z ε (some i)) ⁻¹' {0} => nv0 (v q.1)) (ψ i u)).comp
            (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (ψ i) u)) :=
        (hasMFDerivAt_mfd ((hFj (some i)).mdifferentiableAt (by simp))).comp u
          (hasMFDerivAt_mfd ((hψs i).mdifferentiableAt (by simp)))
      have h2 : ((fun q : (Gf G z ε (some i)) ⁻¹' {0} => nv0 (v q.1)) ∘ ψ i) = sphMap v (z i) ε :=
        hFψ i
      rw [h2] at h1
      have h3 := HasMFDerivAt.mfd_eq h1
      have hsurj : Function.Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (sphMap v (z i) ε) u) := hyi i u (by rw [← hFψ i]; exact hq)
      rw [h3] at hsurj
      exact Function.Surjective.of_comp hsurj
  -- transversality
  have hreg : ∀ x, nv0 (v x) = y → gProd G z ε x = 0 →
      ∃ w, mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (fun x => nv0 (v x)) x w = 0 ∧
        mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) (gProd G z ε) x w ≠ 0 := by
    intro x hfx hgx
    obtain ⟨j, hj⟩ := gProd_eq_zero_iff.1 hgx
    letI := (hSj j).chartedSpace
    haveI := (hSj j).isManifold
    have hxU : x ∈ U := hvne x hgx
    have hd : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (fun x => nv0 (v x)) x :=
      (hnvOn.contMDiffAt (U.isOpen.mem_nhds hxU)).mdifferentiableAt (by simp)
    have hf : IsRegularPoint 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (fun x => nv0 (v x)) x := by
      have h1 := hyUU ⟨x, hxU⟩ hfx
      have h2 := mfd_comp_subtype_val U (y := ⟨x, hxU⟩) hd
      show Function.Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (fun x => nv0 (v x)) x)
      have h3 : mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          (fun x => nv0 (v x)) x = mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((fun x => nv0 (v x)) ∘ Subtype.val) ⟨x, hxU⟩ := h2.symm
      rw [h3]
      exact h1
    obtain ⟨w, hw1, hw2⟩ := exists_mfd_eq_zero_of_isRegularPoint_level hE hZ hZ (hGfs j) (hGfr j)
      (⟨x, hj⟩ : (Gf G z ε j) ⁻¹' {0}) hd hf (hregj j ⟨x, hj⟩ hfx)
    refine ⟨w, hw1, ?_⟩
    rw [hgd x j hj]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact mul_ne_zero (hcpos x j hj).ne' hw2
  -- compactness of the relevant set in `U`
  have hXc : IsCompact {x : U | nv0 (v x.1) = y ∧ 0 ≤ gProd G z ε x.1} := by
    rw [Subtype.isCompact_iff]
    set K := {x | 0 ≤ G x} ∩ ⋂ i, {x | ε ≤ dist x (z i)} with hK
    have hKsub : K ⊆ U := fun x hx => hKU x hx
    have himg : Subtype.val '' {x : U | nv0 (v x.1) = y ∧ 0 ≤ gProd G z ε x.1} =
        (K ∩ (fun x => nv0 (v x)) ⁻¹' {y}) ∩ {x | 0 ≤ gProd G z ε x} := by
      ext x; constructor
      · rintro ⟨⟨x, hxU⟩, ⟨h1, h2⟩, rfl⟩
        obtain ⟨hG1, hG2⟩ := mem_K_of_gProd_nonneg hε hzin hdisj h2
        exact ⟨⟨⟨hG1, mem_iInter.2 hG2⟩, h1⟩, h2⟩
      · rintro ⟨⟨hxK, h1⟩, h2⟩
        exact ⟨⟨x, hKsub hxK⟩, ⟨h1, h2⟩, rfl⟩
    rw [himg]
    refine hKc.of_isClosed_subset ?_ (inter_subset_left.trans inter_subset_left)
    refine IsClosed.inter ?_ (isClosed_le continuous_const hgs.continuous)
    exact ContinuousOn.preimage_isClosed_of_isClosed (hnvOn.continuousOn.mono hKsub) hKc.isClosed
      isClosed_singleton
  -- Lemma 1: the total degree over `∂X` vanishes
  obtain ⟨hfinP, hdeg0⟩ := degAt_level_eq_zero_of_opens hE hZ hZ hgs hgr oE (sphOr n) (U := U)
    hnvOn (fun x hx => hvne x hx) hyUU hreg hXc
  -- decomposition of the level set of `gProd`
  set P : Set ((gProd G z ε) ⁻¹' {0}) :=
    ((fun x => nv0 (v x)) ∘ (Subtype.val : (gProd G z ε) ⁻¹' {0} → EuclideanSpace ℝ (Fin (n + 1)))) ⁻¹' {y} with hP
  set Pj : ∀ j, Set ((Gf G z ε j) ⁻¹' {0}) :=
    fun j => (fun q : (Gf G z ε j) ⁻¹' {0} => nv0 (v q.1)) ⁻¹' {y} with hPj
  have hunion : P = ⋃ j, ι j '' Pj j := by
    ext q; constructor
    · intro hq
      obtain ⟨j, hj⟩ := gProd_eq_zero_iff.1 q.2
      exact mem_iUnion.2 ⟨j, ⟨q.1, hj⟩, hq, rfl⟩
    · intro hq
      obtain ⟨j, q', hq', rfl⟩ := mem_iUnion.1 hq
      exact hq'
  have hpd : Pairwise (Disjoint on fun j => ι j '' Pj j) := by
    intro j l hjl
    rw [Function.onFun, Set.disjoint_left]
    rintro q ⟨q₁, -, rfl⟩ ⟨q₂, -, hq⟩
    have h1 : Gf G z ε j q₁.1 = 0 := q₁.2
    have h2 : Gf G z ε l q₁.1 = 0 := by
      have := q₂.2
      have hval : q₂.1 = q₁.1 := by have := congrArg Subtype.val hq; exact this
      rw [hval] at this
      exact this
    have := Gf_pos_of_ne hε hzin hdisj h1 hjl.symm
    linarith
  have hpiece : ∀ j, letI := (hSj j).chartedSpace;
      ∑ᶠ q ∈ ι j '' Pj j, signAt (levelOrientM hE hZ oE hgs hgr) (sphOr n)
        ((fun x => nv0 (v x)) ∘ (Subtype.val : (gProd G z ε) ⁻¹' {0} → EuclideanSpace ℝ (Fin (n + 1)))) q =
      degAt (levelOrientM hE hZ oE (hGfs j) (hGfr j)) (sphOr n)
        (fun q : (Gf G z ε j) ⁻¹' {0} => nv0 (v q.1)) y := by
    intro j
    letI := (hSj j).chartedSpace
    haveI := (hSj j).isManifold
    rw [finsum_mem_image (hιinj j).injOn]
    unfold degAt
    refine finsum_mem_congr rfl fun q _ => ?_
    have := signAt_comp' hZ hZ (levelOrientM hE hZ oE (hGfs j) (hGfr j))
      (levelOrientM hE hZ oE hgs hgr) (sphOr n) (f := ι j)
      (h := (fun x => nv0 (v x)) ∘ (Subtype.val : (gProd G z ε) ⁻¹' {0} → EuclideanSpace ℝ (Fin (n + 1)))) (x := q)
      ((hιs j).mdifferentiableAt (by simp)) (hFg.mdifferentiableAt (by simp))
    rw [hsι j q, mul_one] at this
    exact this.symm
  set D : Option (Fin k) → ℤ := fun j => letI := (hSj j).chartedSpace;
    degAt (levelOrientM hE hZ oE (hGfs j) (hGfr j)) (sphOr n)
      (fun q : (Gf G z ε j) ⁻¹' {0} => nv0 (v q.1)) y with hD
  have hsum : degAt (levelOrientM hE hZ oE hgs hgr) (sphOr n)
      ((fun x => nv0 (v x)) ∘ (Subtype.val : (gProd G z ε) ⁻¹' {0} → EuclideanSpace ℝ (Fin (n + 1)))) y =
      ∑ j, D j := by
    have hfin : ∀ j, (ι j '' Pj j).Finite := fun j =>
      hfinP.subset (by show ι j '' Pj j ⊆ P; rw [hunion]; exact subset_iUnion (fun j => ι j '' Pj j) j)
    have hL : degAt (levelOrientM hE hZ oE hgs hgr) (sphOr n)
        ((fun x => nv0 (v x)) ∘ (Subtype.val : (gProd G z ε) ⁻¹' {0} → EuclideanSpace ℝ (Fin (n + 1)))) y =
        ∑ᶠ q ∈ P, signAt (levelOrientM hE hZ oE hgs hgr) (sphOr n)
          ((fun x => nv0 (v x)) ∘ (Subtype.val : (gProd G z ε) ⁻¹' {0} → EuclideanSpace ℝ (Fin (n + 1)))) q := rfl
    rw [hL, hunion, finsum_mem_iUnion hpd hfin, finsum_eq_sum_of_fintype]
    exact Finset.sum_congr rfl fun j _ => hpiece j
  -- the pieces
  have hnone : D none = deg (levelOrientM hE hZ oE hG h0) (sphOr n)
      (fun q : G ⁻¹' {0} => nv0 (v q.1)) := by
    letI := (hSj none).chartedSpace
    haveI := (hSj none).isManifold
    haveI : CompactSpace ((Gf G z ε none) ⁻¹' {0}) := hGc
    exact (deg_eq hZ hZ (levelOrientM hE hZ oE (hGfs none) (hGfr none)) (sphOr n) (hFj none) hy0).symm
  have hsome : ∀ i, D (some i) = indexAt v (z i) ε := by
    intro i
    letI := (hSj (some i)).chartedSpace
    haveI := (hSj (some i)).isManifold
    have h1 := degAt_comp_bij hZ hZ (sphOr n) (levelOrientM hE hZ oE (hGfs (some i)) (hGfr (some i)))
      (sphOr n) (f := fun q : (Gf G z ε (some i)) ⁻¹' {0} => nv0 (v q.1))
      (fun q => (hFj (some i)).mdifferentiableAt (by simp)) (hψbij i)
      (fun u => (hψs i).mdifferentiableAt (by simp)) (hsψ i) y
    show degAt (levelOrientM hE hZ oE (hGfs (some i)) (hGfr (some i))) (sphOr n)
      (fun q : (Gf G z ε (some i)) ⁻¹' {0} => nv0 (v q.1)) y = _
    rw [← h1]
    have h2 : (fun u => nv0 (v (ψ i u).1)) = sphMap v (z i) ε := hFψ i
    simp only [h2]
    exact (deg_eq hZ hZ (sphOr n) (sphOr n) (contMDiff_sphMap hv (z i) (hne i)) (hyi i)).symm
  -- conclusion
  rw [hsum, Fintype.sum_option, hnone] at hdeg0
  simp only [hsome] at hdeg0
  rw [deg_neg_left]
  linarith

end region

end Sphere

end Milnor
