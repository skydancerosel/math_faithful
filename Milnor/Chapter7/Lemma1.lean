import Milnor.Chapter7.Cobordism
import Milnor.Chapter7.BasisPath

/-!
# The Pontryagin manifold does not depend on the positive basis (Milnor §7, Lemma 1)

If two bases `b`, `b'` of `T_ySᵖ` are related by a matrix of positive determinant (equivalently,
determine the same orientation), the Pontryagin manifolds `(f⁻¹(y), f^*b)` and `(f⁻¹(y), f^*b')`
are framed cobordant.  The cobordism is `f⁻¹(y) × ℝ ⊆ M × ℝ`, framed by pulling back a smooth
path of bases `B t` from `b'` to `b` (constant near the ends of `[0,1]`), which exists because
`GL⁺(p, ℝ)` is connected by smooth paths (`GLp.exists_glPath`).
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

section timeDep

variable {F' : M × ℝ → Sph p}
  (hF' : letI := hM.chartedSpace; haveI := hM.isManifold;
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ F')
  {z : Sph p}
  (hz : letI := hM.chartedSpace; haveI := hM.isManifold;
    IsRegularValue (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) F' z)

/-- The framing pulled back from a time-dependent basis `B t`. -/
def uht (F' : M × ℝ → Sph p) (z : Sph p) (B : ℝ → Fin p → EuclideanSpace ℝ (Fin p)) (i : Fin p)
    (q : F' ⁻¹' {z}) : EuclideanSpace ℝ (Fin (K + 1)) × ℝ :=
  pinvXR (Ah hM hMc hne F' z (embXR q.1)) (B q.1.2 i)

theorem uht_eq_uh (B : ℝ → Fin p → EuclideanSpace ℝ (Fin p)) (i : Fin p) (q : F' ⁻¹' {z}) :
    uht hM hMc hne F' z B i q = uh hM hMc hne F' z (B q.1.2) i q := rfl

include hF' hz in
theorem contMDiff_uht (hnp : n + p = m) (B : ℝ → Fin p → EuclideanSpace ℝ (Fin p))
    (hB : ContDiff ℝ ∞ B) (i : Fin p) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    letI := (isSliceSubmanifold_levelXR hM hF' hz hnp).chartedSpace;
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) ∞
      (uht hM hMc hne F' z B i) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hS := isSliceSubmanifold_levelXR hM hF' hz hnp
  letI := hS.chartedSpace
  haveI := hS.isManifold
  intro q
  have hsrc : F' (⟨q.1.1.1, q.1.1.2⟩, q.1.2) ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) z).source := by
    rw [Subtype.coe_eta]
    have : F' q.1 = z := q.2
    rw [Prod.mk.eta, this]; exact mem_extChartAt_source z
  have hq : embXR q.1 ∈ Wh hM hMc hne F' z := mem_Wh_of_mem hM hMc hne q.1.1.2 q.1.2 hsrc
  have hA : ContDiffAt ℝ ∞ (Ah hM hMc hne F' z) (embXR q.1) :=
    (contDiffOn_Ah hM hMc hne hF').contDiffAt ((isOpen_Wh hM hMc hne hF').mem_nhds hq)
  have hAd : ContDiffAt ℝ ∞ (fun w => adjXR (Ah hM hMc hne F' z w)) (embXR q.1) :=
    ((adjXRL (k := K + 1) (p := p)).contDiff.contDiffAt).comp (embXR q.1) hA
  have hAA : ContDiffAt ℝ ∞ (fun w => (Ah hM hMc hne F' z w).comp (adjXR (Ah hM hMc hne F' z w)))
      (embXR q.1) := hA.clm_comp hAd
  obtain ⟨u, hu⟩ := isUnit_comp_adjXR (surjective_Ah hM hMc hne hF' hz q.1 q.2)
  have hinv : ContDiffAt ℝ ∞ (fun w => Ring.inverse ((Ah hM hMc hne F' z w).comp
      (adjXR (Ah hM hMc hne F' z w)))) (embXR q.1) := by
    have := contDiffAt_ringInverse ℝ (n := ∞) u
    rw [hu] at this
    exact this.comp (embXR q.1) hAA
  have hBi : ContDiffAt ℝ ∞ (fun w : EuclideanSpace ℝ (Fin (K + 1)) × ℝ => B w.2 i) (embXR q.1) :=
    ((contDiff_pi.1 hB i).comp contDiff_snd).contDiffAt
  have hpinv : ContDiffAt ℝ ∞ (fun w => pinvXR (Ah hM hMc hne F' z w) (B w.2 i)) (embXR q.1) := by
    unfold pinvXR
    exact (hAd.clm_comp hinv).clm_apply hBi
  have hemb : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) ∞
      (fun r : F' ⁻¹' {z} => embXR r.1) := (contMDiff_embXR hM).comp hS.contMDiff_val
  show ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) ∞
    ((fun w => pinvXR (Ah hM hMc hne F' z w) (B w.2 i)) ∘ fun r : F' ⁻¹' {z} => embXR r.1) q
  exact ContMDiffAt.comp q hpinv.contMDiffAt hemb.contMDiffAt

end timeDep

section main

variable {f : M → Sph p} {y : Sph p}

/-- A regular value of `f` is a regular value of the constant homotopy `(x, t) ↦ f x`. -/
theorem isRegularValue_comp_fst
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
    (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f y) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    IsRegularValue (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (fun q : M × ℝ => f q.1) y := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  intro q hq
  have hfd := hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
    (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) (hf.mdifferentiableAt (by simp) :
      MDifferentiableAt _ _ f q.1)
  have hchain := HasMFDerivAt.mfd_eq (hfd.comp q (hasMFDerivAt_fst (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (I' := 𝓘(ℝ, ℝ)) (M := M) (M' := ℝ) q))
  have h4 : (f ∘ Prod.fst) = fun q : M × ℝ => f q.1 := rfl
  rw [h4] at hchain
  show Surjective (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
    𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (fun q : M × ℝ => f q.1) q)
  rw [hchain]
  have hs1 : Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f q.1) :=
    hy q.1 hq
  have hs2 : Surjective (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin m)) ℝ) := by
    rw [ContinuousLinearMap.coe_fst']; exact Prod.fst_surjective
  exact hs1.comp hs2

/-- **Lemma 1 of §7, general form.**  If `g⁻¹(z) = f⁻¹(y)` and the framing of `g` at `z` by `c`
is the framing of `f` at `y` by `A · b` with `det A > 0`, the Pontryagin manifolds are framed
cobordant.  The cobordism is `f⁻¹(y) × ℝ`, framed through a smooth path of bases. -/
theorem framedCobordant_of_det_pos' (hnp : n + p = m)
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
    (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f y)
    {g : M → Sph p} {z : Sph p}
    (hg : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ g)
    (hz : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) g z)
    {b c : Fin p → EuclideanSpace ℝ (Fin p)} (hb : LinearIndependent ℝ b)
    (hc : LinearIndependent ℝ c) {A : Matrix (Fin p) (Fin p) ℝ} (hA : 0 < A.det)
    (hN : g ⁻¹' {z} = f ⁻¹' {y})
    (hv : ∀ i (x : M) (hx : x ∈ f ⁻¹' {y}) (hx' : x ∈ g ⁻¹' {z}),
      pontV hM hMc hne g z c i ⟨x, hx'⟩ = pontV hM hMc hne f y (GLp.mulTuple A b) i ⟨x, hx⟩) :
    FramedCobordant hM (pontryagin hM hMc hne hg hz hnp c hc) (pontryagin hM hMc hne hf hy hnp b hb) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  haveI : CompactSpace M := isCompact_iff_compactSpace.1 hMc
  have hε : (0 : ℝ) < 1 / 4 := by norm_num
  have hε' : (1 / 4 : ℝ) < 1 / 2 := by norm_num
  obtain ⟨B, hBs, hB0, hB1, hBind⟩ := GLp.exists_basisPath hb hA hε hε'
  have hF' : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
      (fun q : M × ℝ => f q.1) := hf.comp contMDiff_fst
  have hz' := isRegularValue_comp_fst hM hf hy
  refine ⟨{ S := (fun q : M × ℝ => f q.1) ⁻¹' {y}
            hS := isSliceSubmanifold_levelXR hM hF' hz' hnp
            ε := 1 / 4
            hε := hε
            hε' := hε'
            end0 := fun q _ => by
              show q.1 ∈ f ⁻¹' {y} ↔ q.1 ∈ g ⁻¹' {z}
              rw [hN]
            end1 := fun q _ => Iff.rfl
            compact := ?_
            u := uht hM hMc hne (fun q : M × ℝ => f q.1) y B
            smooth := fun i => contMDiff_uht hM hMc hne hF' hz' hnp B hBs i
            tangent := fun i q => uh_tangent hM hMc hne hF' (B q.1.2) i q
            normal := fun i q w hw => uh_normal hM hMc hne hF' hz' hnp (B q.1.2) i q w hw
            indep := fun q => uh_indep hM hMc hne hF' hz' (hBind q.1.2) q
            u_end0 := ?_
            u_end1 := ?_ }⟩
  · have hset : {q ∈ (fun q : M × ℝ => f q.1) ⁻¹' {y} | 0 ≤ q.2 ∧ q.2 ≤ 1} =
        (fun q : M × ℝ => f q.1) ⁻¹' {y} ∩ ({q : M × ℝ | 0 ≤ q.2} ∩ {q | q.2 ≤ 1}) := by
      ext q; simp [and_assoc]
    rw [hset]
    refine (isCompact_univ.prod (isCompact_Icc (a := (0 : ℝ)) (b := 1))).of_isClosed_subset ?_ ?_
    · exact (isClosed_singleton.preimage hF'.continuous).inter
        ((isClosed_le continuous_const continuous_snd).inter (isClosed_le continuous_snd continuous_const))
    · rintro q ⟨-, h1, h2⟩
      exact ⟨mem_univ _, h1, h2⟩
  · intro i q hq ht
    have hq' : q.1.1 ∈ f ⁻¹' {y} := hN ▸ hq
    rw [uht_eq_uh, uh_end hM hMc hne hF' hf isOpen_Iio (fun _ _ _ => rfl) (B q.1.2) i q hq' ht]
    show (pontV hM hMc hne f y (B q.1.2) i ⟨q.1.1, hq'⟩, (0 : ℝ)) =
      (pontV hM hMc hne g z c i ⟨q.1.1, hq⟩, 0)
    rw [hv i q.1.1 hq' hq, hB0 q.1.2 ht.le]
  · intro i q hq ht
    rw [uht_eq_uh, uh_end hM hMc hne hF' hf isOpen_Ioi (fun _ _ _ => rfl) (B q.1.2) i q hq ht]
    show (pontV hM hMc hne f y (B q.1.2) i ⟨q.1.1, hq⟩, (0 : ℝ)) =
      (pontV hM hMc hne f y b i ⟨q.1.1, hq⟩, 0)
    rw [hB1 q.1.2 ht.le]

/-- **Lemma 1 of §7.**  Bases related by a matrix of positive determinant give framed cobordant
Pontryagin manifolds. -/
theorem framedCobordant_of_det_pos (hnp : n + p = m)
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
    (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f y)
    {b b' : Fin p → EuclideanSpace ℝ (Fin p)} (hb : LinearIndependent ℝ b)
    (hb' : LinearIndependent ℝ b') {A : Matrix (Fin p) (Fin p) ℝ} (hA : 0 < A.det)
    (hbA : GLp.mulTuple A b = b') :
    FramedCobordant hM (pontryagin hM hMc hne hf hy hnp b' hb') (pontryagin hM hMc hne hf hy hnp b hb) :=
  framedCobordant_of_det_pos' hM hMc hne hnp hf hy hf hy hb hb' hA rfl
    (fun i x hx hx' => by rw [hbA])

/-- **Lemma 1 of §7**, orientation form: two bases determining the same orientation of `T_ySᵖ`
give framed cobordant Pontryagin manifolds. -/
theorem framedCobordant_of_orientation_eq (hnp : n + p = m)
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
    (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f y)
    (e e' : Basis (Fin p) ℝ (EuclideanSpace ℝ (Fin p))) (h : e.orientation = e'.orientation) :
    FramedCobordant hM (pontryagin hM hMc hne hf hy hnp e' e'.linearIndependent)
      (pontryagin hM hMc hne hf hy hnp e e.linearIndependent) := by
  obtain ⟨A, hA, hAe⟩ := GLp.exists_det_pos_of_orientation_eq e e' h
  exact framedCobordant_of_det_pos hM hMc hne hnp hf hy _ _ hA hAe

end main

end Framed

end Milnor
