import Milnor.Chapter7.Main
import Milnor.Chapter7.AddPoint

/-!
# The Hopf theorem (Milnor §7, p. 51)

For a compact connected oriented `m`-dimensional submanifold `M ⊆ ℝᴷ⁺¹` (`m ≥ 1`), two smooth
maps `M → Sᵐ` are smoothly homotopic if and only if they have the same degree.  The "only if"
is Theorem A of §5 (`deg_eq_of_homotopy`); the "if" is proved here: the Pontryagin manifolds
have equal signed counts (the degrees), hence are framed cobordant
(`framedCobordant_of_count_eq`), hence the maps are homotopic (Theorem A of §7).
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace Classical

noncomputable section

namespace Milnor

open Sphere

namespace Framed

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  (hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M) (hMc : IsCompact M) (hne : M.Nonempty)

include hMc hne in
/-- **The Hopf theorem, homotopy from equal degree.** -/
theorem hopf_homotopic (hm : 0 < m) (hconn : letI := hM.chartedSpace; ConnectedSpace M)
    (oM : letI := hM.chartedSpace; Orient 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) M m)
    {f g : M → Sph m}
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ f)
    (hg : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ g)
    (hdeg : letI := hM.chartedSpace; deg oM (sphOr m) f = deg oM (sphOr m) g) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    SmoothHomotopic 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) f g := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  obtain ⟨y, hy⟩ := (dense_regularValues hf).nonempty
  obtain ⟨y', hy'⟩ := (dense_regularValues hg).nonempty
  obtain ⟨e, he⟩ := exists_posBasis hm y
  obtain ⟨e', he'⟩ := exists_posBasis hm y'
  have h1 := count_pontryagin hM hMc hne hm oM hf hy e he
  have h2 := count_pontryagin hM hMc hne hm oM hg hy' e' he'
  have hcob := framedCobordant_of_count_eq hMc hne (oM := oM) hm hconn _
    (pontryagin hM hMc hne hf hy (zero_add m) e e.linearIndependent)
    (pontryagin hM hMc hne hg hy' (zero_add m) e' e'.linearIndependent) rfl
    (by rw [h1, h2]; exact hdeg)
  exact smoothHomotopic_of_framedCobordant hM hMc hne (zero_add m) hm hf hg hy hy' e he e' he' hcob

/-! ### Maps of every degree -/

/-- The empty framed `0`-manifold. -/
def emptyFramed : FramedSub hM 0 m where
  N := ∅
  hN := by intro p hp; exact absurd hp (notMem_empty p)
  dim := zero_add m
  compact := isCompact_empty
  v := fun _ _ => 0
  smooth := fun _ => by intro x; exact absurd x.2 (notMem_empty _)
  tangent := fun _ x => absurd x.2 (notMem_empty _)
  normal := fun _ x => absurd x.2 (notMem_empty _)
  indep := fun x => absurd x.2 (notMem_empty _)

include hM hne in
/-- `M` is infinite: a finite set misses some point. -/
theorem exists_notMem_finite (hm : 0 < m) {P : Set M} (hP : P.Finite) : ∃ x : M, x ∉ P := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  obtain ⟨y₀, hy₀⟩ := hne
  set y : M := ⟨y₀, hy₀⟩
  set φ := extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) y with hφ
  obtain ⟨r, hr, hrt, -⟩ := exists_ballU_subset (hM := hM) y (S := univ) univ_mem
  set e : EuclideanSpace ℝ (Fin m) := EuclideanSpace.single ⟨0, hm⟩ 1 with he
  have hen : ‖e‖ = 1 := by simp [he]
  set g : ℝ → M := fun t => φ.symm (φ y + t • e) with hg
  have hmem : ∀ t ∈ Ioo (0 : ℝ) r, φ y + t • e ∈ φ.target := by
    intro t ht
    apply hrt
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, hen, mul_one,
      Real.norm_eq_abs, abs_of_pos ht.1]
    exact ht.2.le
  have hinj : InjOn g (Ioo 0 r) := by
    intro t ht t' ht' h
    have h1 := congrArg φ h
    simp only [hg] at h1
    rw [φ.right_inv (hmem t ht), φ.right_inv (hmem t' ht')] at h1
    have h2 : t • e = t' • e := add_left_cancel h1
    have h3 : (t - t') • e = 0 := by rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.1 h3 with h4 | h4
    · exact sub_eq_zero.1 h4
    · exact absurd (by rw [h4, norm_zero] at hen; exact hen) zero_ne_one
  have hinf : (g '' Ioo 0 r).Infinite := (Set.Ioo_infinite hr).image hinj
  obtain ⟨x, -, hx⟩ := hinf.exists_notMem_finite hP
  exact ⟨x, hx⟩

include hMc hne in
/-- Framed `0`-manifolds with `d` points of sign `s`. -/
theorem exists_framedSub_of_card (hm : 0 < m)
    (oM : letI := hM.chartedSpace; Orient 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) M m) {s : ℤ}
    (hs : s = 1 ∨ s = -1) :
    ∀ d : ℕ, ∃ F : FramedSub hM 0 m, F.finite_N.toFinset.card = d ∧
      ∀ x (hx : x ∈ F.N), frameSign hM oM (fun i => F.v i ⟨x, hx⟩) x = s := by
  intro d
  induction d with
  | zero =>
    refine ⟨emptyFramed hM, ?_, fun x hx => absurd hx (notMem_empty x)⟩
    rw [Finset.card_eq_zero, Set.Finite.toFinset_eq_empty]
    rfl
  | succ d ih =>
    obtain ⟨F, hcard, hFs⟩ := ih
    obtain ⟨x_c, hx_c⟩ := exists_notMem_finite hM hne hm F.finite_N
    obtain ⟨v, hvT, hv, hvs⟩ := exists_frame_of_sign hm oM x_c hs
    obtain ⟨F', hN', hoff, hvx⟩ := exists_add_point hMc hne hm F hx_c hvT hv
    refine ⟨F', ?_, ?_⟩
    · have : F'.finite_N.toFinset = insert x_c F.finite_N.toFinset := by
        ext y; simp only [Set.Finite.mem_toFinset, hN', mem_union, mem_singleton_iff,
          Finset.mem_insert]; tauto
      rw [this, Finset.card_insert_of_notMem (by
        rw [Set.Finite.mem_toFinset]; exact hx_c)]
      omega
    · intro x hx
      by_cases hxc : x = x_c
      · subst hxc
        have : (fun i => F'.v i ⟨x, hx⟩) = v := funext fun i => hvx i hx
        rw [this]; exact hvs
      · have hxF : x ∈ F.N := by
          rw [hN'] at hx
          rcases hx with h | h
          · exact h
          · exact absurd h hxc
        have : (fun i => F'.v i ⟨x, hx⟩) = fun i => F.v i ⟨x, hxF⟩ :=
          funext fun i => hoff i x hxF hx
        rw [this]; exact hFs x hxF

/-- Scaling a frame by a positive scalar does not change its sign. -/
theorem frameSign_smul (oM : letI := hM.chartedSpace; Orient 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) M m)
    {v : Fin m → EuclideanSpace ℝ (Fin (K + 1))} {x : M} (hvT : ∀ i, v i ∈ tangentM hM x)
    {c : ℝ} (hc : 0 < c) : frameSign hM oM (fun i => c • v i) x = frameSign hM oM v x := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hcc : ∀ i, chartCoord hM x (c • v i) = c • chartCoord hM x (v i) := by
    intro i
    have h1 : c • v i = mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
        (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) x (c • chartCoord hM x (v i)) := by
      rw [map_smul, mfd_val_chartCoord hM (hvT i)]
    rw [h1, chartCoord_mfd_val]
  unfold frameSign
  simp only [hcc]
  rw [basisCLM_smul]
  have hT : (c • basisCLM (fun i => chartCoord hM x (v i))) =
      (basisCLM (fun i => chartCoord hM x (v i))).comp
        (c • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m))) := by
    ext z; simp
  rw [hT, orSign_comp finrank_E finrank_E (stdOr m) (stdOr m) (oM.or x),
    orSign_self_eq_sgn_det finrank_E]
  have hdet : LinearMap.det ((c • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m)) :
      EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
      EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) = c ^ m := by
    rw [ContinuousLinearMap.coe_smul, ContinuousLinearMap.coe_id, LinearMap.det_smul,
      LinearMap.det_id, mul_one, finrank_E]
  rw [hdet, sgn_pos (pow_pos hc m), mul_one]

/-- The count of a Pontryagin manifold does not change when the basis is scaled. -/
theorem count_pontryagin_smul
    (oM : letI := hM.chartedSpace; Orient 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) M m) {f : M → Sph m}
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ f)
    {y : Sph m}
    (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) f y)
    {b : Fin m → EuclideanSpace ℝ (Fin m)} (hb : LinearIndependent ℝ b) {c : ℝ} (hc : 0 < c)
    (hcb : LinearIndependent ℝ (fun i => c • b i)) :
    count hM oM (pontryagin hM hMc hne hf hy (zero_add m) (fun i => c • b i) hcb) =
      count hM oM (pontryagin hM hMc hne hf hy (zero_add m) b hb) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  rw [count_eq_sum, count_eq_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Set.Finite.mem_toFinset] at hx
  rw [sgnAt_of_mem oM (pontryagin hM hMc hne hf hy (zero_add m) (fun i => c • b i) hcb) hx,
    sgnAt_of_mem oM (pontryagin hM hMc hne hf hy (zero_add m) b hb) hx]
  have hsm : (fun i => (pontryagin hM hMc hne hf hy (zero_add m) (fun i => c • b i) hcb).v i ⟨x, hx⟩) =
      fun i => c • (pontryagin hM hMc hne hf hy (zero_add m) b hb).v i ⟨x, hx⟩ := by
    funext i
    show pinv (At hM hMc hne f y x.1) (c • b i) = c • pinv (At hM hMc hne f y x.1) (b i)
    exact map_smul _ _ _
  rw [hsm]
  exact frameSign_smul hM oM (fun i => (pontryagin hM hMc hne hf hy (zero_add m) b hb).tangent i ⟨x, hx⟩) hc

include hMc hne in
/-- **Every integer is a degree.** -/
theorem exists_map_of_deg (hm : 0 < m)
    (oM : letI := hM.chartedSpace; Orient 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) M m) (d : ℤ) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    ∃ f : M → Sph m, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ f ∧
      deg oM (sphOr m) f = d := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  obtain ⟨e', he'⟩ := exists_posBasis hm north
  set s : ℤ := if 0 ≤ d then 1 else -1 with hsdef
  have hs : s = 1 ∨ s = -1 := by
    rw [hsdef]; split_ifs <;> simp
  obtain ⟨F, hcard, hFs⟩ := exists_framedSub_of_card hM hMc hne hm oM hs d.natAbs
  obtain ⟨k, hk, hkn, c, hc, hcb, -, hkF, -⟩ := exists_map_of_framedSub_subset hM hMc hne F e'
    e'.linearIndependent univ isOpen_univ (subset_univ _) 0
  have hkF' : pontryagin hM hMc hne hk hkn (zero_add m) (fun i => c • e' i) hcb = F := hkF
  refine ⟨k, hk, ?_⟩
  rw [← count_pontryagin hM hMc hne hm oM hk hkn e' he',
    ← count_pontryagin_smul hM hMc hne oM hk hkn e'.linearIndependent hc hcb, hkF',
    count_of_const_sign oM F hFs, hcard, hsdef]
  split_ifs with h <;> omega

end Framed

end Milnor
