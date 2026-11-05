import Milnor.Chapter7.RotHomotopy
import Milnor.Chapter7.RegOpen
import Milnor.Chapter7.Equiv

/-!
# The Pontryagin manifold does not depend on the regular value (Milnor §7, Lemma 2)

If `y` and `z` are regular values of `f : M → Sᵖ` (with positive bases `e₀` at `y`, `e` at `z`),
the Pontryagin manifolds `f⁻¹(y)` and `f⁻¹(z)` are framed cobordant.

Milnor's proof, followed here: rotate the sphere.  If `z` is close to `y` (all points of the
great-circle arc from `y` to `z` are regular values), the homotopy `r_{θ ρ(t)} ∘ f` has `z` as a
regular value, so Lemma 3 gives `f⁻¹(z) ∼ (r ∘ f)⁻¹(z)`, and `(r ∘ f)⁻¹(z) = f⁻¹(y)` with the
framing pulled back through the orientation-preserving `dr_y`, which is framed cobordant to the
Pontryagin framing at `y` by Lemma 1.  For general `y`, `z`: choose the rotation `r` with
`r y = z`; by Sard's theorem there is a common regular value `z'` of `f`, `r ∘ f` and the homotopy
arbitrarily close to `z`, and `y' = r⁻¹ z'` is close to `y`; since the regular values form an
open set, the two small arcs `y → y'` and `z' → z` consist of regular values.  Then
`f⁻¹(y) ∼ f⁻¹(y') ∼ (r ∘ f)⁻¹(z') ∼ f⁻¹(z') ∼ f⁻¹(z)`, using symmetry and transitivity.
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

/-- Every point of the sphere has a positive basis (for the model space at that point). -/
theorem exists_posBasis (hp : 1 ≤ p) (y : Sph p) :
    ∃ e : Basis (Fin p) ℝ (EuclideanSpace ℝ (Fin p)), e.orientation = (sphOr p).or y :=
  haveI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  ⟨((sphOr p).or y).someBasis (by simp), Orientation.someBasis_orientation _ _⟩

variable {f : M → Sph p}
  (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)

/-- The Pontryagin manifold only depends on the point (not on the proof of regularity). -/
theorem pontryagin_congr {y y' : Sph p} (h : y = y')
    (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f y)
    (hy' : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f y')
    (hnp : n + p = m) (e : Fin p → EuclideanSpace ℝ (Fin p)) (he : LinearIndependent ℝ e) :
    pontryagin hM hMc hne hf hy hnp e he = pontryagin hM hMc hne hf hy' hnp e he := by
  subst h; rfl

/-- The chord bound along the whole arc `0 ≤ τ ≤ θ₁`. -/
theorem arc_bound {u v : EuclideanSpace ℝ (Fin (p + 1))} {θ₁ D : ℝ} (hθ₁ : 0 ≤ θ₁)
    {y : EuclideanSpace ℝ (Fin (p + 1))}
    (h : ∀ t, 0 ≤ t → t ≤ 1 → dist (rotCLM u v (t * θ₁) y) y ≤ D) {τ : ℝ} (h0 : 0 ≤ τ)
    (hτ : τ ≤ θ₁) : dist (rotCLM u v τ y) y ≤ D := by
  by_cases hθ : θ₁ = 0
  · have hτ0 : τ = 0 := le_antisymm (hτ.trans_eq hθ) h0
    have := h 0 le_rfl zero_le_one
    rwa [zero_mul, ← hτ0] at this
  · have hpos : 0 < θ₁ := lt_of_le_of_ne hθ₁ (Ne.symm hθ)
    have := h (τ / θ₁) (div_nonneg h0 hθ₁) ((div_le_one hpos).2 hτ)
    rwa [div_mul_cancel₀ _ hθ] at this

include hf in
/-- **Lemma 2, along an arc of regular values.** -/
theorem framedCobordant_arc (hnp : n + p = m) {u v : EuclideanSpace ℝ (Fin (p + 1))}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫ = 0) {θ₀ : ℝ} (hθ₀ : 0 ≤ θ₀) (y : Sph p)
    (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f y)
    (harc : letI := hM.chartedSpace; haveI := hM.isManifold; ∀ τ, 0 ≤ τ → τ ≤ θ₀ →
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f
        (rotS u v τ y))
    (hz : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f
        (rotS u v θ₀ y))
    (e : Basis (Fin p) ℝ (EuclideanSpace ℝ (Fin p)))
    (he : e.orientation = (sphOr p).or (rotS u v θ₀ y))
    (e₀ : Basis (Fin p) ℝ (EuclideanSpace ℝ (Fin p))) (he₀ : e₀.orientation = (sphOr p).or y) :
    FramedCobordant hM (pontryagin hM hMc hne hf hz hnp e e.linearIndependent)
      (pontryagin hM hMc hne hf hy hnp e₀ e₀.linearIndependent) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hε : (0 : ℝ) < 1 / 4 := by norm_num
  have hε' : (1 / 4 : ℝ) < 1 / 2 := by norm_num
  obtain ⟨F', hF', hF0, hF1, hFreg⟩ := exists_rotHomotopy hM hu hv huv hf θ₀ hε hε'
  have hzF := hFreg y hθ₀ harc
  have hr := contMDiff_rotS hu hv huv θ₀
  have hbij := mfd_rotS_bijective hu hv huv θ₀ y
  have hinj : ∀ q, rotS u v θ₀ (f q) = rotS u v θ₀ y → f q = y := fun q h => by
    have := congrArg (rotS u v (-θ₀)) h
    rwa [rotS_neg_rotS hu hv huv, rotS_neg_rotS hu hv huv] at this
  have hzg := isRegularValue_comp hM hf hr y hy hbij hinj
  have h1 := framedCobordant_of_homotopy hM hMc hne (g := fun q => rotS u v θ₀ (f q)) hnp hε hε'
    hF' hzF hF0 hF1 hf hz (hr.comp hf) hzg e e.linearIndependent
  have h2 := framedCobordant_comp hM hMc hne hf hr y hnp hy hbij (signAt_rotS hu hv huv θ₀ y)
    hinj e he e₀ he₀
  exact h1.trans h2

include hf in
/-- **Lemma 2 of §7.**  For regular values `y`, `z` of `f` and positive bases `e₀` at `y`, `e`
at `z`, the Pontryagin manifolds `f⁻¹(y)` and `f⁻¹(z)` are framed cobordant (`p ≥ 1`). -/
theorem framedCobordant_of_regularValues (hnp : n + p = m) (hp : 1 ≤ p) {y z : Sph p}
    (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f y)
    (hz : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f z)
    (e₀ : Basis (Fin p) ℝ (EuclideanSpace ℝ (Fin p))) (he₀ : e₀.orientation = (sphOr p).or y)
    (e : Basis (Fin p) ℝ (EuclideanSpace ℝ (Fin p))) (he : e.orientation = (sphOr p).or z) :
    FramedCobordant hM (pontryagin hM hMc hne hf hy hnp e₀ e₀.linearIndependent)
      (pontryagin hM hMc hne hf hz hnp e e.linearIndependent) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  haveI : CompactSpace M := isCompact_iff_compactSpace.1 hMc
  have hε : (0 : ℝ) < 1 / 4 := by norm_num
  have hε' : (1 / 4 : ℝ) < 1 / 2 := by norm_num
  -- the open set of regular values
  have hV : IsOpen {w : Sph p | IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f w} := isOpen_regularValues_sph hM hMc hne hf
  obtain ⟨δy, hδy, hby⟩ := Metric.isOpen_iff.1 hV y hy
  obtain ⟨δz, hδz, hbz⟩ := Metric.isOpen_iff.1 hV z hz
  have hδpos : 0 < min δy δz := lt_min hδy hδz
  -- the rotation carrying `y` to `z`
  obtain ⟨u, v, θ₀, hu, hv, huv, hθ₀, -, hyz, -⟩ := exists_rotation_path hp y z
  have hyz' : rotS u v θ₀ y = z := Subtype.ext (by rw [rotS_val hu hv huv]; exact hyz)
  obtain ⟨F', hF', hF0, hF1, -⟩ := exists_rotHomotopy hM hu hv huv hf θ₀ hε hε'
  have hr := contMDiff_rotS hu hv huv θ₀
  have hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
    (fun q => rotS u v θ₀ (f q)) := hr.comp hf
  -- Sard: a common regular value `z'` near `z`
  have hd1 := dense_regularValues hF'
  have hd2 := dense_regularValues hf
  have hd3 := dense_regularValues hg
  have ho2 := isOpen_regularValues_sph' hM hMc hne hf
  have ho3 := isOpen_regularValues_sph' hM hMc hne hg
  have hd := (hd1.inter_of_isOpen_right hd2 ho2).inter_of_isOpen_right hd3 ho3
  obtain ⟨z', ⟨⟨hz'F, hz'f⟩, hz'g⟩, hz'ball⟩ :=
    hd.exists_mem_open Metric.isOpen_ball ⟨z, Metric.mem_ball_self hδpos⟩
  have hz'F' : IsRegularValue (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
    𝓘(ℝ, EuclideanSpace ℝ (Fin p)) F' z' := hz'F
  have hz'f' : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f z' :=
    hz'f
  have hz'g' : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
    (fun q => rotS u v θ₀ (f q)) z' := hz'g
  have hdz' : dist z' z < min δy δz := Metric.mem_ball.1 hz'ball
  -- `y' = r⁻¹ z'` is near `y`
  set y' := rotS u v (-θ₀) z' with hy'def
  have hry' : rotS u v θ₀ y' = z' := rotS_rotS_neg hu hv huv θ₀ z'
  have hdy' : dist y' y < min δy δz := by
    calc dist y' y = dist (rotS u v θ₀ y') (rotS u v θ₀ y) := (dist_rotS hu hv huv θ₀ y' y).symm
      _ = dist z' z := by rw [hry', hyz']
      _ < min δy δz := hdz'
  have hy' : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f y' :=
    hby (Metric.mem_ball.2 (hdy'.trans_le (min_le_left _ _)))
  -- positive bases at `y'` and `z'`
  obtain ⟨e₁, he₁⟩ := exists_posBasis hp y'
  obtain ⟨e₂, he₂⟩ := exists_posBasis hp z'
  -- Step 1: the arc from `y` to `y'`
  have step1 : FramedCobordant hM (pontryagin hM hMc hne hf hy hnp e₀ e₀.linearIndependent)
      (pontryagin hM hMc hne hf hy' hnp e₁ e₁.linearIndependent) := by
    obtain ⟨u₁, v₁, θ₁, hu₁, hv₁, huv₁, hθ₁, -, hyy', hchord⟩ := exists_rotation_path hp y y'
    have hyy'' : rotS u₁ v₁ θ₁ y = y' := Subtype.ext (by rw [rotS_val hu₁ hv₁ huv₁]; exact hyy')
    have harc : ∀ τ, 0 ≤ τ → τ ≤ θ₁ → IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
        𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f (rotS u₁ v₁ τ y) := by
      intro τ h0 hτ
      apply hby
      rw [Metric.mem_ball, Subtype.dist_eq, rotS_val hu₁ hv₁ huv₁]
      have hb := arc_bound hθ₁ hchord h0 hτ
      rw [← Subtype.dist_eq] at hb
      exact hb.trans_lt (hdy'.trans_le (min_le_left _ _))
    have hy'' : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f
      (rotS u₁ v₁ θ₁ y) := harc θ₁ hθ₁ le_rfl
    have he₁' : e₁.orientation = (sphOr p).or (rotS u₁ v₁ θ₁ y) := by rw [hyy'']; exact he₁
    have h := framedCobordant_arc hM hMc hne hf hnp hu₁ hv₁ huv₁ hθ₁ y hy harc hy'' e₁ he₁' e₀ he₀
    rw [pontryagin_congr hM hMc hne hf hyy'' hy'' hy'] at h
    exact h.symm
  -- Step 2: `(r ∘ f)⁻¹(z') ∼ f⁻¹(y')`
  have step2 : FramedCobordant hM (pontryagin hM hMc hne hf hy' hnp e₁ e₁.linearIndependent)
      (pontryagin hM hMc hne (f := fun q => rotS u v θ₀ (f q)) hg hz'g' hnp e₂
        e₂.linearIndependent) := by
    have hbij := mfd_rotS_bijective hu hv huv θ₀ y'
    have hinj : ∀ q, rotS u v θ₀ (f q) = rotS u v θ₀ y' → f q = y' := fun q h => by
      have := congrArg (rotS u v (-θ₀)) h
      rwa [rotS_neg_rotS hu hv huv, rotS_neg_rotS hu hv huv] at this
    have he₂' : e₂.orientation = (sphOr p).or (rotS u v θ₀ y') := by rw [hry']; exact he₂
    have h := framedCobordant_comp hM hMc hne hf hr y' hnp hy' hbij (signAt_rotS hu hv huv θ₀ y')
      hinj e₂ he₂' e₁ he₁
    rw [pontryagin_congr hM hMc hne hg hry' (isRegularValue_comp hM hf hr y' hy' hbij hinj)
      hz'g'] at h
    exact h.symm
  -- Step 3: Lemma 3 for the rotation homotopy at the regular value `z'`
  have step3 : FramedCobordant hM
      (pontryagin hM hMc hne (f := fun q => rotS u v θ₀ (f q)) hg hz'g' hnp e₂ e₂.linearIndependent)
      (pontryagin hM hMc hne hf hz'f' hnp e₂ e₂.linearIndependent) :=
    (framedCobordant_of_homotopy hM hMc hne (g := fun q => rotS u v θ₀ (f q)) hnp hε hε' hF'
      hz'F' hF0 hF1 hf hz'f' hg hz'g' e₂ e₂.linearIndependent).symm
  -- Step 4: the arc from `z` to `z'`
  have step4 : FramedCobordant hM (pontryagin hM hMc hne hf hz'f' hnp e₂ e₂.linearIndependent)
      (pontryagin hM hMc hne hf hz hnp e e.linearIndependent) := by
    obtain ⟨u₂, v₂, θ₂, hu₂, hv₂, huv₂, hθ₂, -, hzz', hchord⟩ := exists_rotation_path hp z z'
    have hzz'' : rotS u₂ v₂ θ₂ z = z' := Subtype.ext (by rw [rotS_val hu₂ hv₂ huv₂]; exact hzz')
    have harc : ∀ τ, 0 ≤ τ → τ ≤ θ₂ → IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
        𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f (rotS u₂ v₂ τ z) := by
      intro τ h0 hτ
      apply hbz
      rw [Metric.mem_ball, Subtype.dist_eq, rotS_val hu₂ hv₂ huv₂]
      have hb := arc_bound hθ₂ hchord h0 hτ
      rw [← Subtype.dist_eq] at hb
      exact hb.trans_lt (hdz'.trans_le (min_le_right _ _))
    have hz'' : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f
      (rotS u₂ v₂ θ₂ z) := harc θ₂ hθ₂ le_rfl
    have he₂' : e₂.orientation = (sphOr p).or (rotS u₂ v₂ θ₂ z) := by rw [hzz'']; exact he₂
    have h := framedCobordant_arc hM hMc hne hf hnp hu₂ hv₂ huv₂ hθ₂ z hz harc hz'' e₂ he₂' e he
    rw [pontryagin_congr hM hMc hne hf hzz'' hz'' hz'f'] at h
    exact h
  exact ((step1.trans step2).trans step3).trans step4

end Framed

end Milnor
