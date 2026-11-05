import Milnor.Chapter7.Deform
import Milnor.Chapter7.Stereo
import Milnor.Chapter7.Homotopy

/-!
# Maps with the same Pontryagin manifold are homotopic (Milnor §7, p. 48)

If `f, g : M → Sᵖ` have the same Pontryagin manifold at `y` (for proportional bases `b`,
`c • b`), then they are smoothly homotopic: deform both to the standard form near `N`
(`Deform.lean`), then join them by the straight-line homotopy in stereographic coordinates
away from `N` (`Stereo.lean`).
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

theorem FramedSub.v_congr {F G : FramedSub hM n p} (h : F = G) (i : Fin p) (x : F.N) :
    F.v i x = G.v i ⟨x.1, h ▸ x.2⟩ := by
  subst h; rfl

/-- **Same Pontryagin manifold ⇒ homotopic.** -/
theorem smoothHomotopic_of_pontryagin_eq (hnp : n + p = m) {f g : M → Sph p}
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
    (hg : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ g)
    {y : Sph p}
    (hyf : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f y)
    (hyg : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) g y)
    {b : Fin p → EuclideanSpace ℝ (Fin p)} (hb : LinearIndependent ℝ b) {c : ℝ} (hc : 0 < c)
    (hcb : LinearIndependent ℝ (fun i => c • b i))
    (h : pontryagin hM hMc hne hf hyf hnp b hb =
      pontryagin hM hMc hne hg hyg hnp (fun i => c • b i) hcb) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    SmoothHomotopic 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f g := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  set F : FramedSub hM n p := pontryagin hM hMc hne hf hyf hnp b hb with hFdef
  have hFN : F.N = f ⁻¹' {y} := rfl
  have hGN : F.N = g ⁻¹' {y} := congrArg FramedSub.N h
  have hkN_f : ∀ z : M, f z = y ↔ z ∈ F.N := fun z => Iff.rfl
  have hkN_g : ∀ z : M, g z = y ↔ z ∈ F.N := fun z => by rw [hGN]; exact Iff.rfl
  by_cases hNe : Nonempty F.N
  swap
  · -- no preimage of `y`: both maps avoid `y`
    have hempty : ∀ z : M, z ∉ F.N := fun z hz => hNe ⟨⟨z, hz⟩⟩
    obtain ⟨H, hH, hH0, hH1, -⟩ := exists_homotopy_of_eqOn (IX := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (y := y) hf hg (U := ∅) isOpen_empty (fun x hx => absurd hx (notMem_empty x))
      (fun x _ hfx => hempty x ((hkN_f x).1 hfx)) (fun x _ hgx => hempty x ((hkN_g x).1 hgx))
    exact ⟨H, hH, hH0, hH1⟩
  obtain ⟨T⟩ := exists_tubeData hMc hne F
  -- the derivatives along the framing
  have hAf : ∀ (x : F.N) (i : Fin p), At hM hMc hne f y x.1.1 (F.v i x) = (1 : ℝ) • b i := by
    intro x i
    rw [one_smul]
    exact At_pontV hM hMc hne hf hyf b i x
  have hAg : ∀ (x : F.N) (i : Fin p), At hM hMc hne g y x.1.1 (F.v i x) = c • b i := by
    intro x i
    rw [FramedSub.v_congr h i x]
    have hxg : x.1 ∈ g ⁻¹' {y} := by rw [← hGN]; exact x.2
    show At hM hMc hne g y x.1.1 (pontV hM hMc hne g y (fun i => c • b i) i ⟨x.1, hxg⟩) = c • b i
    exact At_pontV hM hMc hne hg hyg (fun i => c • b i) i ⟨x.1, hxg⟩
  obtain ⟨Hf, δf, hδf, hδfε, hHf, hHf0, hHf1, hHfy⟩ :=
    exists_deform hMc hne T hf hkN_f hb one_pos hAf
  obtain ⟨Hg, δg, hδg, hδgε, hHg, hHg0, hHg1, hHgy⟩ :=
    exists_deform hMc hne T hg hkN_g hb hc hAg
  -- the deformed maps
  have hf' : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
      (fun z => Hf (z, 1)) := hHf.comp (contMDiff_id.prodMk contMDiff_const)
  have hg' : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
      (fun z => Hg (z, 1)) := hHg.comp (contMDiff_id.prodMk contMDiff_const)
  -- the common tube
  set δ := min δf δg with hδ
  have hδpos : 0 < δ := lt_min hδf hδg
  set U : Set M := T.G '' PN.tube F.N p δ with hU
  have hsub : PN.tube F.N p δ ⊆ PN.tube F.N p T.ε := fun q hq =>
    lt_of_lt_of_le hq ((min_le_left _ _).trans hδfε)
  have hUo : IsOpen U := by
    letI := F.hN.chartedSpace
    haveI := F.hN.isManifold
    exact PN.isOpen_image_tube T.hG (fun q hq => T.hbij q (hsub hq))
  have hNU : ∀ x : F.N, x.1 ∈ U := fun x =>
    ⟨(x, 0), by show ‖(0 : EuclideanSpace ℝ (Fin p))‖ < δ; rw [norm_zero]; exact hδpos, T.G_zero x⟩
  have hfg : ∀ z ∈ U, Hf (z, 1) = Hg (z, 1) := by
    rintro _ ⟨⟨x, s⟩, hq, rfl⟩
    have hs : ‖s‖ < δ := hq
    rw [hHf1 x s (hs.trans_le (min_le_left _ _)), hHg1 x s (hs.trans_le (min_le_right _ _))]
  have hfy : ∀ z, z ∉ U → Hf (z, 1) ≠ y := fun z hz =>
    hHfy z (fun hzN => hz (hNU ⟨z, hzN⟩))
  have hgy : ∀ z, z ∉ U → Hg (z, 1) ≠ y := fun z hz =>
    hHgy z (fun hzN => hz (hNU ⟨z, hzN⟩))
  obtain ⟨H₂, hH₂, hH₂0, hH₂1, -⟩ := exists_homotopy_of_eqOn (IX := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
    (y := y) hf' hg' hUo hfg hfy hgy
  have h1 : SmoothHomotopic 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f
      (fun z => Hf (z, 1)) := ⟨Hf, hHf, hHf0, fun x => rfl⟩
  have h2 : SmoothHomotopic 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (fun z => Hf (z, 1)) (fun z => Hg (z, 1)) := ⟨H₂, hH₂, hH₂0, hH₂1⟩
  have h3 : SmoothHomotopic 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) g
      (fun z => Hg (z, 1)) := ⟨Hg, hHg, hHg0, fun x => rfl⟩
  exact (h1.trans h2).trans h3.symm

end Framed

end Milnor
