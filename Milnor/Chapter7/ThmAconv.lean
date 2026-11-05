import Milnor.Chapter7.CobMap
import Milnor.Chapter7.SamePont
import Milnor.Chapter7.Lemma2
import Milnor.Chapter7.Homotopy

/-!
# Framed cobordant Pontryagin manifolds come from homotopic maps (Milnor §7, Theorem A)

If the Pontryagin manifolds of `f` and `g` (at regular values `y`, `y'`, with positive bases)
are framed cobordant, then `f` and `g` are smoothly homotopic.  Proof: rotate both regular
values to the north pole (a homotopy through rotations, which changes the Pontryagin manifold
only by an orientation-preserving change of basis), use Lemma 1 to make the bases agree, build
the map `H : M × ℝ → Sᵖ` of the cobordism (`CobMap.lean`), and use that maps with the same
Pontryagin manifold are homotopic (`SamePont.lean`).
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
  {n p : ℕ}

/-- Rotating the regular value to the north pole: `f` is homotopic to `r ∘ f`, and the
Pontryagin manifold of `r ∘ f` at `north` (with the rotated basis) is that of `f` at `y`. -/
theorem exists_rotate_to_north (hnp : n + p = m) (hp : 1 ≤ p) {f : M → Sph p}
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
    {y : Sph p}
    (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f y)
    (e : Basis (Fin p) ℝ (EuclideanSpace ℝ (Fin p))) (he : e.orientation = (sphOr p).or y) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    ∃ (f' : M → Sph p)
      (hf' : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f')
      (hy' : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f' north)
      (e₁ : Basis (Fin p) ℝ (EuclideanSpace ℝ (Fin p))),
      SmoothHomotopic 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f f' ∧
      e₁.orientation = (sphOr p).or north ∧
      pontryagin hM hMc hne hf' hy' hnp e₁ e₁.linearIndependent =
        pontryagin hM hMc hne hf hy hnp e e.linearIndependent := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  obtain ⟨u, v, θ₀, hu, hv, huv, -, -, hyn, -⟩ := exists_rotation_path hp y north
  have hry : rotS u v θ₀ y = north := Subtype.ext (by rw [rotS_val hu hv huv]; exact hyn)
  have hr := contMDiff_rotS hu hv huv θ₀
  have hbij := mfd_rotS_bijective hu hv huv θ₀ y
  have hsign := signAt_rotS hu hv huv θ₀ y
  have hinj : ∀ q, rotS u v θ₀ (f q) = rotS u v θ₀ y → f q = y := fun q h => by
    have := congrArg (rotS u v (-θ₀)) h
    rwa [rotS_neg_rotS hu hv huv, rotS_neg_rotS hu hv huv] at this
  have hf' : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
    (fun q => rotS u v θ₀ (f q)) := hr.comp hf
  have hyr := isRegularValue_comp hM hf hr y hy hbij hinj
  have hyn' : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (fun q => rotS u v θ₀ (f q)) north := by rw [← hry]; exact hyr
  -- the homotopy through rotations
  have hε : (0 : ℝ) < 1 / 4 := by norm_num
  have hε' : (1 / 4 : ℝ) < 1 / 2 := by norm_num
  obtain ⟨F', hF', hF0, hF1, -⟩ := exists_rotHomotopy hM hu hv huv hf θ₀ hε hε'
  have hhom : SmoothHomotopic 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f
      (fun q => rotS u v θ₀ (f q)) :=
    ⟨F', hF', fun x => hF0 x 0 (by norm_num), fun x => hF1 x 1 (by norm_num)⟩
  -- the rotated basis
  set L := LinearEquiv.ofBijective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
    𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (rotS u v θ₀) y : EuclideanSpace ℝ (Fin p) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin p)) hbij with hL
  set e₁ : Basis (Fin p) ℝ (EuclideanSpace ℝ (Fin p)) := e.map L with he₁def
  have he₁ : e₁.orientation = (sphOr p).or north := by
    rw [he₁def, Basis.orientation_map, he, ← hry]
    exact orientation_map_of_orSign_eq_one hZ hbij hsign
  -- the Pontryagin manifold of the rotated map at `r y`
  have hN : (fun q => rotS u v θ₀ (f q)) ⁻¹' {rotS u v θ₀ y} = f ⁻¹' {y} := by
    ext q
    constructor
    · intro h; exact hinj q h
    · intro h
      show rotS u v θ₀ (f q) = rotS u v θ₀ y
      have : f q = y := h
      rw [this]
  have heq : pontryagin hM hMc hne hf' hyr hnp e₁ e₁.linearIndependent =
      pontryagin hM hMc hne hf hy hnp e e.linearIndependent := by
    refine FramedSub.ext' hM hN ?_
    intro i x hx hx'
    have hfx : f x = y := hx'
    show pontV hM hMc hne (fun q => rotS u v θ₀ (f q)) (rotS u v θ₀ y) e₁ i ⟨x, hx⟩ =
      pontV hM hMc hne f y e i ⟨x, hx'⟩
    rw [pontV_comp hM hMc hne hf hr y hy hbij e₁ i x hfx hx hx']
    have hfun : (fun j => L.symm (e₁ j)) = ⇑e := by
      funext j
      rw [he₁def, Basis.map_apply, LinearEquiv.symm_apply_apply]
    show pontV hM hMc hne f y (fun j => L.symm (e₁ j)) i ⟨x, hx'⟩ = _
    rw [hfun]
  refine ⟨_, hf', hyn', e₁, hhom, he₁, ?_⟩
  rw [← heq]
  exact (pontryagin_congr hM hMc hne hf' hry hyr hyn' hnp e₁ e₁.linearIndependent).symm

/-- **Theorem A (second half).**  If the Pontryagin manifolds of `f` and `g` are framed
cobordant, then `f` and `g` are smoothly homotopic. -/
theorem smoothHomotopic_of_framedCobordant (hnp : n + p = m) (hp : 1 ≤ p) {f g : M → Sph p}
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
    (hg : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ g)
    {y y' : Sph p}
    (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f y)
    (hy' : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) g y')
    (e : Basis (Fin p) ℝ (EuclideanSpace ℝ (Fin p))) (he : e.orientation = (sphOr p).or y)
    (e' : Basis (Fin p) ℝ (EuclideanSpace ℝ (Fin p))) (he' : e'.orientation = (sphOr p).or y')
    (h : FramedCobordant hM (pontryagin hM hMc hne hf hy hnp e e.linearIndependent)
      (pontryagin hM hMc hne hg hy' hnp e' e'.linearIndependent)) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    SmoothHomotopic 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f g := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  obtain ⟨f', hf', hyf', e₁, hff', he₁, heqf⟩ := exists_rotate_to_north hM hMc hne hnp hp hf hy e he
  obtain ⟨g', hg', hyg', e₂, hgg', he₂, heqg⟩ := exists_rotate_to_north hM hMc hne hnp hp hg hy' e' he'
  rw [← heqf, ← heqg] at h
  -- make the bases agree (Lemma 1)
  have h1 := framedCobordant_of_orientation_eq hM hMc hne hnp hg' hyg' e₂ e₁ (he₂.trans he₁.symm)
  obtain ⟨X⟩ := h.trans h1.symm
  -- the map of the cobordism
  obtain ⟨H, hH, c, hc, hcb, hy0, hy1, heq0, heq1⟩ :=
    exists_cobMap hMc hne X e₁ e₁.linearIndependent
  have h2 : SmoothHomotopic 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f'
      (fun z => H (z, 0)) :=
    smoothHomotopic_of_pontryagin_eq hMc hne hnp hf' (hH.comp (contMDiff_id.prodMk contMDiff_const))
      hyf' hy0 e₁.linearIndependent hc hcb heq0.symm
  have h3 : SmoothHomotopic 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) g'
      (fun z => H (z, 1)) :=
    smoothHomotopic_of_pontryagin_eq hMc hne hnp hg' (hH.comp (contMDiff_id.prodMk contMDiff_const))
      hyg' hy1 e₁.linearIndependent hc hcb heq1.symm
  have h4 : SmoothHomotopic 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (fun z => H (z, 0)) (fun z => H (z, 1)) := ⟨H, hH, fun x => rfl, fun x => rfl⟩
  exact ((((hff'.trans h2).trans h4).trans h3.symm).trans hgg'.symm)

end Framed

end Milnor
