import Milnor.Chapter7.ThmB

/-!
# Packaging the product neighbourhood of a framed submanifold

The data produced in the proof of Theorem B (a clamp `λ`, a radius `ε`, the tube map
`G = Gx λ : N × ℝᵖ → M`, injective with bijective derivative on `N × B_ε`, and its inverse) is
collected in a structure `TubeData F`, so that it can be reused (for the deformation lemma).
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace Classical

noncomputable section

namespace Milnor

open Sphere

namespace Framed

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  {hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M} (hMc : IsCompact M) (hne : M.Nonempty)
  {n p : ℕ}

/-- The product neighbourhood data of a framed submanifold. -/
structure TubeData (F : FramedSub hM n p) where
  lam : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)
  hlam : ContDiff ℝ ∞ lam
  a₀ : ℝ
  ha₀ : 0 < a₀
  hlam_id : ∀ t, ‖t‖ ≤ a₀ → lam t = t
  hmem : ∀ q, Gamb F lam q ∈ Tub.Nε hM hMc hne
  ε : ℝ
  hε : 0 < ε
  hεa : ε ≤ a₀
  hinj : InjOn (Gx hMc hne F lam) (PN.tube F.N p ε)
  hbij : letI := hM.chartedSpace; haveI := hM.isManifold; letI := F.hN.chartedSpace;
    ∀ q ∈ PN.tube F.N p ε, Bijective (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod
      𝓘(ℝ, EuclideanSpace ℝ (Fin p))) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (Gx hMc hne F lam) q)

variable {F : FramedSub hM n p}

namespace TubeData

variable {hMc hne}
variable (T : TubeData hMc hne F)

/-- The tube map. -/
def G : F.N × EuclideanSpace ℝ (Fin p) → M := Gx hMc hne F T.lam

theorem hlam0 : T.lam 0 = 0 := T.hlam_id 0 (by rw [norm_zero]; exact T.ha₀.le)

theorem hlam_ev : ∀ᶠ t in 𝓝 (0 : EuclideanSpace ℝ (Fin p)), T.lam t = t := by
  filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin p)) T.ha₀] with t ht
  exact T.hlam_id t (mem_ball_zero_iff.1 ht).le

theorem hG : letI := hM.chartedSpace; haveI := hM.isManifold; letI := F.hN.chartedSpace;
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ T.G :=
  contMDiff_Gx hMc hne F T.hlam T.hmem

theorem G_zero (x : F.N) : T.G (x, 0) = x.1 := Gx_zero hMc hne F T.hlam0 x

/-- The image of the tube. -/
def V : Set M := T.G '' PN.tube F.N p T.ε

theorem isOpen_V : IsOpen T.V := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := F.hN.chartedSpace
  haveI := F.hN.isManifold
  exact PN.isOpen_image_tube T.hG T.hbij

/-- The inverse of the tube map. -/
def Ginv [Nonempty F.N] : M → F.N × EuclideanSpace ℝ (Fin p) := PN.Ginv T.G T.ε

theorem Ginv_G [Nonempty F.N] {q} (hq : q ∈ PN.tube F.N p T.ε) : T.Ginv (T.G q) = q :=
  PN.Ginv_G T.hinj hq

theorem G_Ginv [Nonempty F.N] {z} (hz : z ∈ T.V) : T.G (T.Ginv z) = z := PN.G_Ginv hz

theorem Ginv_mem [Nonempty F.N] {z} (hz : z ∈ T.V) : T.Ginv z ∈ PN.tube F.N p T.ε := PN.Ginv_mem hz

theorem contMDiffAt_Ginv [Nonempty F.N] {z} (hz : z ∈ T.V) :
    letI := hM.chartedSpace; haveI := hM.isManifold; letI := F.hN.chartedSpace;
    ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) ∞ T.Ginv z := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := F.hN.chartedSpace
  haveI := F.hN.isManifold
  exact PN.contMDiffAt_Ginv T.hG T.hbij T.hinj hz

/-- Points of `N` lie in `V` and are inverted to `(x, 0)`. -/
theorem mem_V (x : F.N) : x.1 ∈ T.V :=
  ⟨(x, 0), by show ‖(0 : EuclideanSpace ℝ (Fin p))‖ < T.ε; rw [norm_zero]; exact T.hε, T.G_zero x⟩

theorem Ginv_of_mem [Nonempty F.N] (x : F.N) : T.Ginv x.1 = (x, 0) := by
  have h := T.Ginv_G (q := (x, 0)) (by show ‖(0 : EuclideanSpace ℝ (Fin p))‖ < T.ε; rw [norm_zero]; exact T.hε)
  rwa [T.G_zero] at h

/-- The tube map along the framing direction is the retraction of the line `x + s vᵢ(x)`. -/
theorem G_line (x : F.N) (i : Fin p) {s : ℝ} (hs : |s| ≤ T.a₀) :
    T.G (x, s • EuclideanSpace.single i (1 : ℝ)) = Tub.tubr hM hMc hne (x.1.1 + s • F.v i x) := by
  have hs1 : ‖s • EuclideanSpace.single i (1 : ℝ)‖ = |s| := by
    rw [norm_smul, EuclideanSpace.norm_single, norm_one, mul_one, Real.norm_eq_abs]
  unfold G Gx Gamb
  congr 1
  rw [T.hlam_id _ (by rw [hs1]; exact hs)]
  simp [emb, EuclideanSpace.single_apply, Finset.sum_ite_eq']

end TubeData

/-- The raw tube map along a framing line. -/
theorem Gx_line (F : FramedSub hM n p) {lam : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    {a₀ : ℝ} (hlam_id : ∀ t, ‖t‖ ≤ a₀ → lam t = t) (x : F.N) (i : Fin p) {s : ℝ} (hs : |s| ≤ a₀) :
    Gx hMc hne F lam (x, s • EuclideanSpace.single i (1 : ℝ)) =
      Tub.tubr hM hMc hne (x.1.1 + s • F.v i x) := by
  have hs1 : ‖s • EuclideanSpace.single i (1 : ℝ)‖ = |s| := by
    rw [norm_smul, EuclideanSpace.norm_single, norm_one, mul_one, Real.norm_eq_abs]
  unfold Gx Gamb
  congr 1
  rw [hlam_id _ (by rw [hs1]; exact hs)]
  simp [emb, EuclideanSpace.single_apply, Finset.sum_ite_eq']

/-- **Existence of the product neighbourhood data** for a prescribed clamp. -/
theorem exists_tubeData_of_lam (F : FramedSub hM n p)
    {lam : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)} (hlam : ContDiff ℝ ∞ lam)
    {a₀ : ℝ} (ha₀ : 0 < a₀) (hlam_id : ∀ t, ‖t‖ ≤ a₀ → lam t = t)
    (hmem : ∀ q, Gamb F lam q ∈ Tub.Nε hM hMc hne) :
    ∃ T : TubeData hMc hne F, T.lam = lam ∧ T.a₀ = a₀ := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := F.hN.chartedSpace
  haveI := F.hN.isManifold
  have hlam_ev : ∀ᶠ t in 𝓝 (0 : EuclideanSpace ℝ (Fin p)), lam t = t := by
    filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin p)) ha₀] with t ht
    exact hlam_id t (mem_ball_zero_iff.1 ht).le
  have hlam0 : lam 0 = 0 := hlam_ev.self_of_nhds
  have hG : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
    𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ (Gx hMc hne F lam) := contMDiff_Gx hMc hne F hlam hmem
  have hbij0 := bijective_mfd_Gx_zero hMc hne F hlam hlam_ev hmem
  haveI : CompactSpace F.N := isCompact_iff_compactSpace.1 F.compact
  obtain ⟨ε₁, hε₁, hb₁⟩ := PN.exists_ball_bijective hG univ isCompact_univ (fun x _ => hbij0 x)
  obtain ⟨ε, hε, hεle, hinj⟩ := PN.exists_injOn hG univ isCompact_univ (ε₀ := min ε₁ a₀)
    (lt_min hε₁ ha₀) (fun x _ => hbij0 x) (Gx_zero_injective hMc hne F hlam0)
    (fun q q' _ _ hq _ => absurd (mem_univ q.1) hq)
  refine ⟨{ lam := lam, hlam := hlam, a₀ := a₀, ha₀ := ha₀, hlam_id := hlam_id, hmem := hmem
            ε := ε, hε := hε, hεa := hεle.trans (min_le_right _ _)
            hinj := fun q hq q' hq' h => hinj q q' hq hq' h
            hbij := ?_ }, rfl, rfl⟩
  rintro ⟨x, t⟩ hq
  exact hb₁ x (mem_univ _) t (lt_of_lt_of_le hq (hεle.trans (min_le_left _ _)))

/-- **Existence of the product neighbourhood data** (extracted from the proof of Theorem B). -/
theorem exists_tubeData (F : FramedSub hM n p) : Nonempty (TubeData hMc hne F) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_v F
  set tε := Tub.tubε hM hMc hne with htε
  have htε0 : 0 < tε := Tub.tubε_pos hM hMc hne
  set a₀ : ℝ := tε / (8 * (p * C + 1)) with ha₀def
  have ha₀ : 0 < a₀ := by positivity
  obtain ⟨lam, hlam, hlam_id, hlam_b, -⟩ :=
    exists_clamp (E := EuclideanSpace ℝ (Fin p)) ha₀ (le_refl (2 * a₀))
  have hbC : p * (2 * a₀ * C) < tε := by
    rw [ha₀def]
    have h1 : (p : ℝ) * (2 * (tε / (8 * (p * C + 1))) * C) =
        tε * (2 * p * C) / (8 * (p * C + 1)) := by
      field_simp
    rw [h1, div_lt_iff₀ (by positivity)]
    have hpc : (0 : ℝ) ≤ p * C := by positivity
    exact mul_lt_mul_of_pos_left (by nlinarith [hpc]) htε0
  have hmem : ∀ q, Gamb F lam q ∈ Tub.Nε hM hMc hne :=
    Gamb_mem_Nε hMc hne F hC hlam_b hC0.le hbC
  obtain ⟨T, -, -⟩ := exists_tubeData_of_lam hMc hne F hlam ha₀ hlam_id hmem
  exact ⟨T⟩

end Framed

end Milnor
