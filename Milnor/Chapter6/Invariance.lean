import Milnor.Chapter6.Invariance1

/-!
# Milnor's Lemma 1 (§6): the index is invariant under diffeomorphisms

Let `f : U → U'` be a diffeomorphism between open subsets of `ℝⁿ⁺¹` (`n ≥ 1`), `v` a smooth
vector field on `U` with an isolated zero at `z`, and `w = f_* v = df ∘ v ∘ f⁻¹` the transported
field on `U'`.  Then the index of `w` at `f z` equals the index of `v` at `z`.

The proof avoids Milnor's Lemma 2 (isotopy through `GL⁺`): the index of `w` at `f z` is computed
by the region lemma over the boundary `f(S_r(z))`; the diffeomorphism `f|` carries this to the
sphere `S_r(z)` with sign `-σ` (`σ = sgn det df`), the affine map `ψ` carries it to the unit
sphere with sign `+1`, the homotopy `df_{z + t r u} → df_z` reduces to the linear map `A = df_z`,
whose normalization on the sphere has sign `σ` (`signAt_nv0_linear`); the two factors `σ`
cancel.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

namespace Sphere

variable {n : ℕ}

theorem nv0_of_mem (u : Sph n) : nv0 u.1 = u := by
  have hu : ‖u.1‖ = 1 := mem_iff_norm.1 u.2
  have hu0 : u.1 ≠ 0 := fun h => by rw [h, norm_zero] at hu; exact zero_ne_one hu
  apply Subtype.ext
  rw [nv0_val hu0, normalize, hu, inv_one, one_smul]

/-- **Milnor's Lemma 1 (§6): invariance of the index under diffeomorphisms.** -/
theorem index_eq_of_diffeo (hn : 0 < n)
    {U U' : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hU : IsOpen U) (hU' : IsOpen U')
    {f g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U') (hfU : MapsTo f U U') (hgU : MapsTo g U' U)
    (hgf : ∀ x ∈ U, g (f x) = x) (hfg : ∀ y ∈ U', f (g y) = y)
    {v : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hv : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ v)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {r : ℝ} (hr : 0 < r) (hball : closedBall z r ⊆ U)
    (hiso : IsolatedZero v z r)
    {w : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hw : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ w)
    (hwv : ∀ y ∈ f '' closedBall z r, w y = fderiv ℝ f (g y) (v (g y))) :
    index w (f z) = index v z := by
  classical
  haveI : PreconnectedSpace (Sph n) := preconnectedSpace hn
  set B := closedBall z r with hB
  have hzB : z ∈ B := mem_closedBall_self hr.le
  have hzU : z ∈ U := hball hzB
  -- derivatives
  have hdf : ∀ x ∈ U, HasFDerivAt f (fderiv ℝ f x) x := fun x hx =>
    (((hf.differentiableOn (by simp)) x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hdg : ∀ y ∈ U', HasFDerivAt g (fderiv ℝ g y) y := fun y hy =>
    (((hg.differentiableOn (by simp)) y hy).differentiableAt (hU'.mem_nhds hy)).hasFDerivAt
  have hgf_d : ∀ x ∈ U, (fderiv ℝ g (f x)).comp (fderiv ℝ f x) = ContinuousLinearMap.id ℝ _ := by
    intro x hx
    have h1 := (hdg (f x) (hfU hx)).comp x (hdf x hx)
    have h2 : (g ∘ f) =ᶠ[𝓝 x] id := by
      filter_upwards [hU.mem_nhds hx] with y hy; exact hgf y hy
    exact (h1.congr_of_eventuallyEq h2.symm).unique (hasFDerivAt_id x)
  have hfg_d : ∀ y ∈ U', (fderiv ℝ f (g y)).comp (fderiv ℝ g y) = ContinuousLinearMap.id ℝ _ := by
    intro y hy
    have h1 := (hdf (g y) (hgU hy)).comp y (hdg y hy)
    have h2 : (f ∘ g) =ᶠ[𝓝 y] id := by
      filter_upwards [hU'.mem_nhds hy] with x hx; exact hfg x hx
    exact (h1.congr_of_eventuallyEq h2.symm).unique (hasFDerivAt_id y)
  have hinvf : ∀ x ∈ U, Bijective (fderiv ℝ f x) := by
    intro x hx
    refine ⟨fun a b hab => ?_, fun c => ?_⟩
    · have ha := congrArg (fun L => L a) (hgf_d x hx)
      have hb := congrArg (fun L => L b) (hgf_d x hx)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_id', id_eq] at ha hb
      rw [← ha, ← hb, hab]
    · have h := hfg_d (f x) (hfU hx)
      rw [hgf x hx] at h
      refine ⟨fderiv ℝ g (f x) c, ?_⟩
      have := congrArg (fun L => L c) h
      simpa using this
  have hfM : ∀ x ∈ U, MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) f x := fun x hx =>
    (hf.contDiffAt (hU.mem_nhds hx)).contMDiffAt.mdifferentiableAt (by simp)
  have hmfdf : ∀ x, mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) f x = fderiv ℝ f x := fun x => mfderiv_eq_fderiv
  -- the sign of the Jacobian
  set σ : ℤ := sgn (LinearMap.det (fderiv ℝ f z :
    EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))) with hσ
  have hdet : ∀ x ∈ B, sgn (LinearMap.det (fderiv ℝ f x :
      EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))) = σ :=
    fun x hx => sgn_det_fderiv_eq hU hf hinvf hball hx
  have hσ1 : σ = 1 ∨ σ = -1 := by
    rcases lt_or_gt_of_ne (det_ne_zero_of_bijective (hinvf z hzU)) with h | h
    · right; exact sgn_neg h
    · left; exact sgn_pos h
  have hσσ : σ * σ = 1 := by rcases hσ1 with h | h <;> simp [h]
  have hσ1' : -σ = 1 ∨ -σ = -1 := by rcases hσ1 with h | h <;> simp [h]
  -- the region `X' = f(B)`
  set X' := f '' B with hX'
  have hX'c : IsCompact X' := (isCompact_closedBall z r).image_of_continuousOn (hf.continuousOn.mono hball)
  have hX'U' : X' ⊆ U' := by rintro _ ⟨x, hx, rfl⟩; exact hfU (hball hx)
  set G₀ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := fun y => r ^ 2 - ‖g y - z‖ ^ 2 with hG₀
  have hG₀s : ContDiffOn ℝ ∞ G₀ U' :=
    contDiffOn_const.sub (ContDiffOn.norm_sq (𝕜 := ℝ) (hg.sub contDiffOn_const))
  have hXG : ∀ y ∈ U', y ∈ X' ↔ 0 ≤ G₀ y := by
    intro y hy
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [hG₀, hgf x (hball hx)]
      have : ‖x - z‖ ≤ r := by rw [← dist_eq_norm]; exact hx
      nlinarith [norm_nonneg (x - z)]
    · intro h
      refine ⟨g y, ?_, hfg y hy⟩
      show dist (g y) z ≤ r
      rw [dist_eq_norm]
      have h2 : ‖g y - z‖ ^ 2 ≤ r ^ 2 := by simp only [hG₀] at h; linarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) hr.le two_ne_zero).1 h2
  obtain ⟨G', hG', hG'X, hG'G⟩ := exists_region_fun hU' hX'c hX'U' hG₀s hXG
  have hG'X' : ∀ y ∈ X', G' y = G₀ y := fun y hy => hG'G.self_of_nhdsSet y hy
  -- points of the level set of `G'`
  have hlevel : ∀ y, G' y = 0 → ∃ x ∈ B, y = f x ∧ ‖x - z‖ = r := by
    intro y hy
    have hyX : y ∈ X' := by rw [← hG'X]; exact le_of_eq hy.symm
    obtain ⟨x, hx, rfl⟩ := hyX
    refine ⟨x, hx, rfl, ?_⟩
    have := hG'X' _ ⟨x, hx, rfl⟩
    rw [hy] at this
    simp only [hG₀, hgf x (hball hx)] at this
    have h2 : ‖x - z‖ ^ 2 = r ^ 2 := by linarith
    exact (pow_left_inj₀ (norm_nonneg _) hr.le two_ne_zero).1 h2
  -- `0` is a regular value of `G'`
  have hG'0 : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) G' 0 := by
    intro y hy
    have hy0 : G' y = 0 := hy
    obtain ⟨x, hxB, rfl, hxr⟩ := hlevel y hy0
    have hyX : f x ∈ X' := ⟨x, hxB, rfl⟩
    have hyU' := hX'U' hyX
    have hev : G' =ᶠ[𝓝 (f x)] G₀ := eventually_nhdsSet_iff_forall.1 hG'G _ hyX
    show Function.Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) G' (f x))
    rw [show mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) G' (f x) = fderiv ℝ G' (f x) from
      mfderiv_eq_fderiv, hev.fderiv_eq]
    have hd : HasFDerivAt G₀ (-(2 • (innerSL ℝ (g (f x) - z)).comp (fderiv ℝ g (f x)))) (f x) := by
      have := ((hdg (f x) hyU').sub_const z).norm_sq
      have h2 := (hasFDerivAt_const (r ^ 2) (f x)).sub this
      rw [zero_sub] at h2
      exact h2
    rw [hd.fderiv]
    have hgd : fderiv ℝ g (f x) (fderiv ℝ f x (x - z)) = x - z := by
      have := congrArg (fun L => L (x - z)) (hgf_d x (hball hxB))
      simpa using this
    have hne : x - z ≠ 0 := by
      intro h; rw [h, norm_zero] at hxr; exact hr.ne' hxr.symm
    intro t
    refine ⟨(t / (-2 * ‖x - z‖ ^ 2)) • fderiv ℝ f x (x - z), ?_⟩
    simp only [map_smul, ContinuousLinearMap.neg_apply, smul_apply, ContinuousLinearMap.comp_apply,
      hgf x (hball hxB), hgd, innerSL_apply_apply, real_inner_self_eq_norm_sq, nsmul_eq_mul,
      Nat.cast_ofNat, smul_eq_mul]
    have : -2 * ‖x - z‖ ^ 2 ≠ 0 := by
      have := norm_pos_iff.2 hne
      positivity
    field_simp
  have hX'c' : IsCompact {y | 0 ≤ G' y} := by rw [hG'X]; exact hX'c
  -- the transported field on `X'`
  have hwX : ∀ x ∈ B, w (f x) = fderiv ℝ f x (v x) := fun x hx => by
    rw [hwv _ ⟨x, hx, rfl⟩, hgf x (hball hx)]
  have hwne : ∀ y, G' y = 0 → w y ≠ 0 := by
    intro y hy
    obtain ⟨x, hxB, rfl, hxr⟩ := hlevel y hy
    rw [hwX x hxB]
    have hxz : x ≠ z := by
      intro h; rw [h, sub_self, norm_zero] at hxr; exact hr.ne' hxr.symm
    intro h0
    exact hiso.2 x hxB hxz ((hinvf x (hball hxB)).1 (by rw [h0, map_zero]))
  -- the small ball about `f z`
  have hopen : IsOpen (f '' ball z r) := by
    have : f '' ball z r = U' ∩ g ⁻¹' (ball z r) := by
      ext y; constructor
      · rintro ⟨x, hx, rfl⟩
        have hxU := hball (ball_subset_closedBall hx)
        exact ⟨hfU hxU, by simp only [mem_preimage, hgf x hxU]; exact hx⟩
      · rintro ⟨hy, hgy⟩
        exact ⟨g y, hgy, hfg y hy⟩
    rw [this]
    exact hg.continuousOn.isOpen_inter_preimage hU' isOpen_ball
  obtain ⟨ε', hε', hε'ball⟩ := Metric.isOpen_iff.1 hopen (f z) ⟨z, mem_ball_self hr, rfl⟩
  set ε := ε' / 2 with hε
  have hε0 : 0 < ε := by positivity
  have hmemball : ∀ y, dist y (f z) ≤ ε → ∃ x ∈ ball z r, y = f x := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hε'ball (mem_ball.2 (lt_of_le_of_lt hy (by linarith)))
    exact ⟨x, hx, rfl⟩
  have hzin : ∀ i : Fin 1, ∀ y, dist y ((fun _ => f z) i) ≤ ε → 0 < G' y := by
    intro i y hy
    obtain ⟨x, hx, rfl⟩ := hmemball y hy
    have hxB : x ∈ B := ball_subset_closedBall hx
    rw [hG'X' _ ⟨x, hxB, rfl⟩]
    simp only [hG₀, hgf x (hball hxB)]
    have : ‖x - z‖ < r := by rw [← dist_eq_norm]; exact hx
    nlinarith [norm_nonneg (x - z)]
  have hdisj : ∀ i j : Fin 1, i ≠ j → 2 * ε < dist ((fun _ => f z) i) ((fun _ => f z) j) :=
    fun i j h => absurd (Subsingleton.elim i j) h
  have hzero' : ∀ y, 0 ≤ G' y → w y = 0 → ∃ i : Fin 1, y = (fun _ => f z) i := by
    intro y hy hwy
    have hyX : y ∈ X' := by rw [← hG'X]; exact hy
    obtain ⟨x, hxB, rfl⟩ := hyX
    rw [hwX x hxB] at hwy
    have hv0 : v x = 0 := (hinvf x (hball hxB)).1 (by rw [hwy, map_zero])
    have hx : x = z := by by_contra h; exact hiso.2 x hxB h hv0
    exact ⟨0, by rw [hx]⟩
  have hreg := sum_indexAt_eq_deg hn hw hG'.contMDiff hG'0 hX'c' hε0 hzin hdisj hzero'
  rw [Fin.sum_univ_one] at hreg
  -- the level-set manifolds
  have hSL := isSliceSubmanifold_preimage (Z := EuclideanSpace ℝ (Fin n)) (finrank_Z_add hE hZ)
    hG'.contMDiff hG'0
  letI := hSL.chartedSpace
  haveI := hSL.isManifold
  have hSS := isSliceSubmanifold_preimage (Z := EuclideanSpace ℝ (Fin n)) (finrank_Z_add hE hZ)
    (contMDiff_Gsph z r) (isRegularValue_Gsph hr)
  letI := hSS.chartedSpace
  haveI := hSS.isManifold
  haveI : CompactSpace (G' ⁻¹' {0}) := isCompact_iff_compactSpace.1
    (hX'c'.of_isClosed_subset (isClosed_singleton.preimage hG'.continuous)
      (fun y hy => le_of_eq (mem_singleton_iff.1 hy).symm))
  haveI : CompactSpace ((Gsph z r) ⁻¹' {0}) := by
    rw [← isCompact_iff_compactSpace]
    have : (Gsph z r) ⁻¹' {0} = sphere z r := by
      ext x; simp only [mem_preimage, mem_singleton_iff, mem_sphere, Gsph_eq_zero_iff hr]
    rw [this]; exact isCompact_sphere z r
  set a₀ := (finBasisOfFinrankEq ℝ (EuclideanSpace ℝ (Fin (n + 1))) hE).orientation with ha₀
  set oE : Orient 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin (n + 1))) (n + 1) :=
    Orient.const a₀ with hoE
  set loG' := levelOrientM hE hZ oE hG'.contMDiff hG'0 with hloG'
  set loS := levelOrientM hE hZ oE (contMDiff_Gsph z r) (isRegularValue_Gsph hr) with hloS
  set F' : G' ⁻¹' {0} → Sph n := fun q => nv0 (w q.1) with hF'
  have hF's : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ F' :=
    contMDiff_nv0_comp (hw.comp hSL.contMDiff_val) (fun q => hwne q.1 q.2)
  -- the restriction `fr : S → L'` of `f`
  have hSB : ∀ x, Gsph z r x = 0 → x ∈ B := fun x hx => by
    show dist x z ≤ r; exact le_of_eq ((Gsph_eq_zero_iff hr x).1 hx)
  have hfS : ∀ x, Gsph z r x = 0 → G' (f x) = 0 := by
    intro x hx
    have hxB := hSB x hx
    rw [hG'X' _ ⟨x, hxB, rfl⟩]
    simp only [hG₀, hgf x (hball hxB)]
    rw [← dist_eq_norm, (Gsph_eq_zero_iff hr x).1 hx]; ring
  set fr : (Gsph z r) ⁻¹' {0} → G' ⁻¹' {0} := fun q => ⟨f q.1, hfS q.1 q.2⟩ with hfr
  have hfrs : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞
      (fun q : (Gsph z r) ⁻¹' {0} => f q.1) := by
    have hfc : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ f U := contMDiffOn_iff_contDiffOn.2 hf
    exact hfc.comp_contMDiff hSS.contMDiff_val (fun q => hball (hSB q.1 q.2))
  have hfrM : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ fr :=
    hSL.contMDiff_codRestrict hfrs (fun q => hfS q.1 q.2)
  have hfr_sign : ∀ q, signAt loS loG' fr q = -σ := by
    intro q
    have hqB : q.1 ∈ B := hSB q.1 q.2
    have hdc : (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) G' (f q.1)).comp
        (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) f q.1) =
        (-(r ^ 2)) • mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) (Gsph z r) q.1 := by
      obtain ⟨V, hVo, hXV, hV⟩ := eventually_nhdsSet_iff_exists.1 hG'G
      have hfc : ContinuousAt f q.1 := hf.continuousOn.continuousAt (hU.mem_nhds (hball hqB))
      have hev : (fun x => -(r ^ 2) * Gsph z r x) =ᶠ[𝓝 q.1] (G' ∘ f) := by
        filter_upwards [hU.mem_nhds (hball hqB),
          hfc.preimage_mem_nhds (hVo.mem_nhds (hXV ⟨q.1, hqB, rfl⟩))] with x hxU hxV
        simp only [Function.comp, hV _ hxV, hG₀, hgf x hxU, Gsph_eq hr, dist_eq_norm]
        field_simp
        ring
      have h1 := ((hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) (J := 𝓘(ℝ, ℝ))
        (hG'.contMDiff.mdifferentiableAt (by simp) : MDifferentiableAt _ _ G' (f q.1))).comp q.1
        (hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
          (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) (hfM q.1 (hball hqB)))).congr_of_eventuallyEq hev
      have h2 := (hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) (J := 𝓘(ℝ, ℝ))
        ((contMDiff_Gsph z r).mdifferentiableAt (by simp) :
          MDifferentiableAt _ _ (Gsph z r) q.1)).const_smul (-(r ^ 2))
      exact hasMFDerivAt_unique h1 h2
    have := signAt_levelOrientM_map' hE hZ oE oE (contMDiff_Gsph z r) (isRegularValue_Gsph hr)
      hG'.contMDiff hG'0 (Φ := f) hfS hfrs q (hfM q.1 (hball hqB)) (-(r ^ 2))
      (neg_ne_zero.2 (pow_ne_zero 2 hr.ne')) hdc
    rw [sgn_neg (neg_lt_zero.2 (pow_pos hr 2))] at this
    have hs : signAt oE oE f q.1 = σ := by
      unfold signAt
      rw [Orient.const_or, Orient.const_or, orSign_self_eq_sgn_det hE, hmfdf, hdet q.1 hqB]
    rw [hs, neg_one_mul] at this
    exact this
  have hfr_bij : Bijective fr := by
    constructor
    · intro q q' h
      have h1 : f q.1 = f q'.1 := congrArg Subtype.val h
      apply Subtype.ext
      rw [← hgf q.1 (hball (hSB q.1 q.2)), ← hgf q'.1 (hball (hSB q'.1 q'.2)), h1]
    · intro q'
      obtain ⟨x, hxB, hx, hxr⟩ := hlevel q'.1 q'.2
      refine ⟨⟨x, ?_⟩, Subtype.ext hx.symm⟩
      show Gsph z r x = 0
      rw [Gsph_eq_zero_iff hr, dist_eq_norm, hxr]
  have hfr_surjd : ∀ q, Function.Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) fr q) := fun q => by
    have := (signAt_ne_zero_iff hZ hZ loS loG' fr q).1 (by rw [hfr_sign]; rcases hσ1 with h | h <;> simp [h])
    exact this.2
  -- the affine map `ψ : Sⁿ → S`
  have hψ_surjd : ∀ u, Function.Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (ψaff z hr) u) := fun u => by
    have := (signAt_ne_zero_iff hZ hZ (sphOr n) loS (ψaff z hr) u).1 (by rw [signAt_ψaff z hr u]; decide)
    exact this.2
  -- the homotopy `df_{z + t r u} (v (z + r u))`
  set ρ : ℝ → ℝ := Real.smoothTransition with hρ
  set Hm : Sph n × ℝ → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun p => fderiv ℝ f (z + (ρ p.2 * r) • p.1.1) (v (z + r • p.1.1)) with hHm
  have hbase : ∀ p : Sph n × ℝ, z + (ρ p.2 * r) • p.1.1 ∈ B := by
    intro p
    show dist (z + (ρ p.2 * r) • p.1.1) z ≤ r
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, mem_iff_norm.1 p.1.2, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.smoothTransition.nonneg _) hr.le)]
    have := Real.smoothTransition.le_one p.2
    nlinarith
  have hsph : ∀ u : Sph n, z + r • u.1 ∈ B ∧ z + r • u.1 ≠ z := by
    intro u
    have hu : ‖u.1‖ = 1 := mem_iff_norm.1 u.2
    constructor
    · show dist (z + r • u.1) z ≤ r
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_pos hr]
    · intro h
      have : r • u.1 = 0 := by simpa using congrArg (· - z) h
      rw [smul_eq_zero] at this
      rcases this with h1 | h1
      · exact hr.ne' h1
      · rw [h1, norm_zero] at hu; exact zero_ne_one hu
  have hHmne : ∀ p, Hm p ≠ 0 := by
    intro p h0
    have hv0 : v (z + r • p.1.1) = 0 :=
      (hinvf _ (hball (hbase p))).1 (by rw [map_zero]; exact h0)
    exact hiso.2 _ (hsph p.1).1 (hsph p.1).2 hv0
  have hHms : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ Hm := by
    have hρs : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : Sph n × ℝ => ρ p.2 * r) :=
      (Real.smoothTransition.contDiff.contMDiff.comp contMDiff_snd).mul contMDiff_const
    have hu : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ (fun p : Sph n × ℝ => p.1.1) :=
      contMDiff_val.comp contMDiff_fst
    have hb : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ (fun p : Sph n × ℝ => z + (ρ p.2 * r) • p.1.1) :=
      contMDiff_const.add (hρs.smul hu)
    have hdfs : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) ∞ (fderiv ℝ f) U :=
      contMDiffOn_iff_contDiffOn.2 (hf.fderiv_of_isOpen hU (by simp))
    have hA : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) ∞
        (fun p : Sph n × ℝ => fderiv ℝ f (z + (ρ p.2 * r) • p.1.1)) :=
      hdfs.comp_contMDiff hb (fun p => hball (hbase p))
    have hrs : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun _ : Sph n × ℝ => r) := contMDiff_const
    have hvs : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ (fun p : Sph n × ℝ => v (z + r • p.1.1)) :=
      hv.comp (contMDiff_const.add (hrs.smul hu))
    exact hA.clm_apply hvs
  have hhom := deg_eq_of_homotopy hZ hZ (sphOr n) (sphOr n) (contMDiff_nv0_comp hHms hHmne)
  -- identify the two ends of the homotopy
  set A := fderiv ℝ f z with hA
  have hA' : Bijective A := hinvf z hzU
  set h : Sph n → Sph n := fun u => nv0 (A u.1) with hh
  have hend0 : (fun u : Sph n => nv0 (Hm (u, 0))) = fun u => h (sphMap v z r u) := by
    funext u
    simp only [Hm, hρ, Real.smoothTransition.zero, zero_mul, zero_smul, add_zero, h]
    rw [sphMap_eq_nv0 (by
      intro h0; exact hiso.2 _ (hsph u).1 (hsph u).2 h0)]
    have hv0 : v (z + r • u.1) ≠ 0 := fun h0 => hiso.2 _ (hsph u).1 (hsph u).2 h0
    rw [nv0_val hv0, normalize, map_smul, nv0_smul (inv_pos.2 (norm_pos_iff.2 hv0))]
  have hend1 : (fun u : Sph n => nv0 (Hm (u, 1))) = fun u => F' (fr (ψaff z hr u)) := by
    funext u
    simp only [Hm, hρ, Real.smoothTransition.one, one_mul, F', fr, ψaff, aff]
    rw [hwX _ (hsph u).1]
  rw [hend0, hend1] at hhom
  -- degrees
  obtain ⟨y, hy⟩ := (dense_regularValues hF's).nonempty
  have hyF' : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) F' y := hy
  have hyfr : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (fun q => F' (fr q)) y :=
    IsRegularValue.comp_of_surjective (fun q => hF's.mdifferentiableAt (by simp))
      (fun q => hfrM.mdifferentiableAt (by simp)) hfr_surjd hyF'
  have hyψ : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (fun u => F' (fr (ψaff z hr u))) y :=
    IsRegularValue.comp_of_surjective (f := fun q => F' (fr q)) (φ := ψaff z hr)
      (fun q => (hF's.comp hfrM).mdifferentiableAt (by simp))
      (fun u => (contMDiff_ψaff z hr).mdifferentiableAt (by simp)) hψ_surjd hyfr
  have hd1 : deg loG' (sphOr n) F' = degAt loG' (sphOr n) F' y := deg_eq hZ hZ _ _ hF's hyF'
  have hd2 : degAt loS (sphOr n) (fun q => F' (fr q)) y = (-σ) * degAt loG' (sphOr n) F' y :=
    degAt_comp_bij' hZ hZ loS loG' (sphOr n) (fun q => hF's.mdifferentiableAt (by simp)) hfr_bij
      (fun q => hfrM.mdifferentiableAt (by simp)) hσ1' hfr_sign y
  have hd3 : degAt (sphOr n) (sphOr n) (fun u => F' (fr (ψaff z hr u))) y =
      degAt loS (sphOr n) (fun q => F' (fr q)) y :=
    degAt_comp_bij hZ hZ (sphOr n) loS (sphOr n) (fun q => (hF's.comp hfrM).mdifferentiableAt (by simp))
      (ψaff_bijective z hr) (fun u => (contMDiff_ψaff z hr).mdifferentiableAt (by simp))
      (signAt_ψaff z hr) y
  have hd4 : deg (sphOr n) (sphOr n) (fun u => F' (fr (ψaff z hr u))) =
      degAt (sphOr n) (sphOr n) (fun u => F' (fr (ψaff z hr u))) y :=
    deg_eq hZ hZ _ _ ((hF's.comp hfrM).comp (contMDiff_ψaff z hr)) hyψ
  -- the linear end
  have hune : ∀ u : Sph n, u.1 ≠ 0 := fun u h => by
    have := mem_iff_norm.1 u.2
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hhs : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ h :=
    contMDiff_nv0_comp (A.contMDiff.comp contMDiff_val) (fun u => A_ne_zero hA' (hune u))
  have hhsign : ∀ u, signAt (sphOr n) (sphOr n) h u = σ := fun u => signAt_nv0_linear hA' u
  set Ae := ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.2 hA'.1)
    (LinearMap.range_eq_top.2 hA'.2) with hAe_def
  have hAe : ∀ x, Ae x = A x := fun x => by
    have := ContinuousLinearEquiv.coe_ofBijective A (LinearMap.ker_eq_bot.2 hA'.1)
      (LinearMap.range_eq_top.2 hA'.2)
    exact congrArg (fun L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) =>
      L x) this
  have hAeA : ∀ x, Ae.symm (A x) = x := fun x => by rw [← hAe]; exact Ae.symm_apply_apply x
  have hAAe : ∀ y, A (Ae.symm y) = y := fun y => by rw [← hAe]; exact Ae.apply_symm_apply y
  have hhbij : Bijective h := by
    refine Function.bijective_iff_has_inverse.2 ⟨fun u => nv0 (Ae.symm u.1), fun u => ?_, fun u => ?_⟩
    · show nv0 (Ae.symm (nv0 (A u.1)).1) = u
      rw [nv0_val (A_ne_zero hA' (hune u)), normalize, map_smul, hAeA,
        nv0_smul (inv_pos.2 (norm_pos_iff.2 (A_ne_zero hA' (hune u)))), nv0_of_mem]
    · show nv0 (A (nv0 (Ae.symm u.1)).1) = u
      have hne' : Ae.symm u.1 ≠ 0 := fun h0 => hune u (by
        have := congrArg Ae h0
        rwa [Ae.apply_symm_apply, map_zero] at this)
      rw [nv0_val hne', normalize, map_smul, hAAe,
        nv0_smul (inv_pos.2 (norm_pos_iff.2 hne')), nv0_of_mem]
  have hh_injd : ∀ u, Injective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) h u) := fun u =>
    ((signAt_ne_zero_iff hZ hZ (sphOr n) (sphOr n) h u).1
      (by rw [hhsign]; rcases hσ1 with h | h <;> simp [h])).1
  have hss : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (sphMap v z r) :=
    contMDiff_sphMap hv z (fun u h0 => hiso.2 _ (hsph u).1 (hsph u).2 h0)
  obtain ⟨y'', hy''⟩ := (dense_regularValues (hhs.comp hss)).nonempty
  have hy''r : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (fun u => h (sphMap v z r u)) y'' := hy''
  obtain ⟨y₀, rfl⟩ := hhbij.2 y''
  have hy₀ : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (sphMap v z r) y₀ :=
    IsRegularValue.of_comp_injective (fun u => hhs.mdifferentiableAt (by simp))
      (fun u => hss.mdifferentiableAt (by simp)) hh_injd hhbij.1 hy''r
  have hd5 : deg (sphOr n) (sphOr n) (fun u => h (sphMap v z r u)) =
      degAt (sphOr n) (sphOr n) (fun u => h (sphMap v z r u)) (h y₀) :=
    deg_eq hZ hZ _ _ (hhs.comp hss) hy''r
  have hd6 : degAt (sphOr n) (sphOr n) (fun u => h (sphMap v z r u)) (h y₀) =
      σ * degAt (sphOr n) (sphOr n) (sphMap v z r) y₀ :=
    degAt_comp_bij_left hZ hZ (sphOr n) (sphOr n) (sphOr n) hhbij
      (fun u => hhs.mdifferentiableAt (by simp)) hσ1 hhsign
      (fun u => hss.mdifferentiableAt (by simp)) rfl
  have hd7 : deg (sphOr n) (sphOr n) (sphMap v z r) = degAt (sphOr n) (sphOr n) (sphMap v z r) y₀ :=
    deg_eq hZ hZ _ _ hss hy₀
  -- the transported field has an isolated zero at `f z`
  have hisow : IsolatedZero w (f z) ε := by
    refine ⟨?_, fun y hy hyz hwy => ?_⟩
    · rw [hwX z hzB, hiso.1, map_zero]
    · obtain ⟨x, hx, rfl⟩ := hmemball y hy
      have hxB : x ∈ B := ball_subset_closedBall hx
      rw [hwX x hxB] at hwy
      have hv0 : v x = 0 := (hinvf x (hball hxB)).1 (by rw [hwy, map_zero])
      have hxz : x ≠ z := fun h => hyz (by rw [h])
      exact hiso.2 x hxB hxz hv0
  -- assemble
  have key : (-σ) * degAt loG' (sphOr n) F' y = σ * degAt (sphOr n) (sphOr n) (sphMap v z r) y₀ := by
    rw [← hd2, ← hd3, ← hd4, ← hhom, hd5, hd6]
  rw [index_eq hn hw hε0 hisow hε0 le_rfl, hreg, deg_neg_left, hd1,
    index_eq hn hv hr hiso hr le_rfl]
  show -degAt loG' (sphOr n) F' y = deg (sphOr n) (sphOr n) (sphMap v z r)
  rw [hd7]
  rcases hσ1 with h | h <;> simp only [h] at key <;> linarith

end Sphere

end Milnor
