import Milnor.Chapter7.Lemma2

/-!
# Homotopic maps have framed cobordant Pontryagin manifolds (Milnor §7, Theorem A, first half)

Combining Lemma 2, Lemma 3 and the reparametrization of a homotopy: if `f` and `g` are
smoothly homotopic, `y` is a regular value of `f` and `z` one of `g`, then `f⁻¹(y)` and `g⁻¹(z)`
(with positive framings) are framed cobordant.  By Sard's theorem the homotopy `F`, `f` and `g`
have a common regular value `z'`; Lemma 3 gives `f⁻¹(z') ∼ g⁻¹(z')`, and Lemma 2 moves the
regular values.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

open Sphere

namespace Framed

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  (hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M) (hMc : IsCompact M) (hne : M.Nonempty)
  {p n : ℕ}

/-- **Theorem A (first half).**  Homotopic maps have framed cobordant Pontryagin manifolds. -/
theorem framedCobordant_of_homotopic (hnp : n + p = m) (hp : 1 ≤ p) {F : M × ℝ → Sph p}
    (hF : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ F)
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ (fun x => F (x, 0)))
    (hg : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ (fun x => F (x, 1)))
    {y z : Sph p}
    (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
        (fun x => F (x, 0)) y)
    (hz : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
        (fun x => F (x, 1)) z)
    (e₀ : Basis (Fin p) ℝ (EuclideanSpace ℝ (Fin p))) (he₀ : e₀.orientation = (sphOr p).or y)
    (e : Basis (Fin p) ℝ (EuclideanSpace ℝ (Fin p))) (he : e.orientation = (sphOr p).or z) :
    FramedCobordant hM (pontryagin hM hMc hne hf hy hnp e₀ e₀.linearIndependent)
      (pontryagin hM hMc hne hg hz hnp e e.linearIndependent) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  haveI : CompactSpace M := isCompact_iff_compactSpace.1 hMc
  have hε : (0 : ℝ) < 1 / 4 := by norm_num
  have hε' : (1 / 4 : ℝ) < 1 / 2 := by norm_num
  -- a common regular value `z'` of `F`, `f`, `g`
  have hd1 := dense_regularValues hF
  have hd2 := dense_regularValues hf
  have hd3 := dense_regularValues hg
  have ho2 := isOpen_regularValues_sph' hM hMc hne hf
  have ho3 := isOpen_regularValues_sph' hM hMc hne hg
  have hd := (hd1.inter_of_isOpen_right hd2 ho2).inter_of_isOpen_right hd3 ho3
  obtain ⟨z', ⟨hz'F, hz'f⟩, hz'g⟩ := hd.nonempty
  have hz'F' : IsRegularValue (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
    𝓘(ℝ, EuclideanSpace ℝ (Fin p)) F z' := hz'F
  have hz'f' : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
    (fun x => F (x, 0)) z' := hz'f
  have hz'g' : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
    (fun x => F (x, 1)) z' := hz'g
  -- reparametrize the homotopy
  obtain ⟨F', hF', hF'0, hF'1, hz'F''⟩ := exists_reparam hM hF hz'F' hz'f' hz'g' hε hε'
  obtain ⟨e', he'⟩ := exists_posBasis hp z'
  have h3 := framedCobordant_of_homotopy hM hMc hne (f := fun x => F (x, 0)) (g := fun x => F (x, 1))
    hnp hε hε' hF' hz'F'' hF'0 hF'1 hf hz'f' hg hz'g' e' e'.linearIndependent
  have h2 := framedCobordant_of_regularValues hM hMc hne hf hnp hp hy hz'f' e₀ he₀ e' he'
  have h2' := framedCobordant_of_regularValues hM hMc hne hg hnp hp hz'g' hz e' he' e he
  exact (h2.trans h3).trans h2'

end Framed

end Milnor
