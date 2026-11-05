import Milnor.Chapter7.Transport

/-!
# Framed cobordism is an equivalence relation (Milnor §7, p. 43)

Symmetry: reverse time, `(x, t) ↦ (x, 1 - t)`, and flip the `t`-component of the framing.
Transitivity: shift the second cobordism by `1`, glue along the common product end
`N₁ × (1 - ε₁, 1 + ε₂)`, and rescale time by `1/2`; the framing's `t`-component scales
accordingly.  The infrastructure (transport of tangent spaces, gluing of submanifolds) is in
`Transport.lean`.
-/

open Set Filter Topology Function Module Metric TopologicalSpace
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

namespace Framed

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  {hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M} {n p : ℕ}

/-- A framing of a submanifold `S ⊆ M × ℝ` (no conditions at the ends). -/
structure Framing (S : Set (M × ℝ))
    (hS : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsSliceSubmanifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
        (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin p)) S) where
  u : Fin p → S → EuclideanSpace ℝ (Fin (K + 1)) × ℝ
  smooth : ∀ i, letI := hM.chartedSpace; haveI := hM.isManifold; letI := hS.chartedSpace;
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) ∞ (u i)
  tangent : ∀ i q, (u i q).1 ∈ tangentM hM q.1.1
  normal : ∀ i q, ∀ w ∈ tangentS hM hS q, ipXR (u i q) w = 0
  indep : ∀ q, LinearIndependent ℝ (fun i => u i q)

/-- The framing of a framed cobordism. -/
def FramedCob.framing {F₀ F₁ : FramedSub hM n p} (X : FramedCob hM F₀ F₁) :
    Framing (hM := hM) X.S X.hS :=
  ⟨X.u, X.smooth, X.tangent, X.normal, X.indep⟩

theorem ipXR_dtXR (a : ℝ) (u w : EuclideanSpace ℝ (Fin (K + 1)) × ℝ) :
    ipXR (dtXR a u) w = ipXR u (dtXR a w) := by
  simp only [ipXR, dtXR_apply]; ring

theorem dtXR_injective {a : ℝ} (ha : a ≠ 0) : Injective (dtXR (K := K) a) := by
  intro x y h
  simp only [dtXR_apply, Prod.mk.injEq] at h
  exact Prod.ext h.1 (mul_left_cancel₀ ha h.2)

section transport

variable {S : Set (M × ℝ)}
  {hS : letI := hM.chartedSpace; haveI := hM.isManifold;
    IsSliceSubmanifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin p)) S}

/-- **Transport of a framing** under the affine time change. -/
def Framing.transport (Φ : Framing (hM := hM) S hS) (a c : ℝ) (ha : a ≠ 0) :
    Framing (hM := hM) (affFun a c ⁻¹' S) (isSliceSubmanifold_preimage_affine hM hS a c ha) where
  u i q := dtXR a (Φ.u i (ιaff (S := S) a c q))
  smooth i := by
    letI := hM.chartedSpace
    haveI := hM.isManifold
    have hS' := isSliceSubmanifold_preimage_affine hM hS a c ha
    letI := hS'.chartedSpace
    letI := hS.chartedSpace
    exact (contMDiff_iff_contDiff.2 (dtXR (K := K) a).contDiff).comp
      ((Φ.smooth i).comp (contMDiff_ιaff hM hS a c ha))
  tangent i q := Φ.tangent i (ιaff (S := S) a c q)
  normal i q w hw := by
    have hw' : dtXR a w ∈ tangentS hM hS (ιaff (S := S) a c q) := by
      rw [tangentS_affine hM hS a c ha q]
      exact Submodule.mem_map_of_mem hw
    rw [ipXR_dtXR]
    exact Φ.normal i (ιaff (S := S) a c q) _ hw'
  indep q := by
    have := (Φ.indep (ιaff (S := S) a c q)).map'
      (dtXR (K := K) a : EuclideanSpace ℝ (Fin (K + 1)) × ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin (K + 1)) × ℝ)
      (LinearMap.ker_eq_bot.2 (dtXR_injective ha))
    exact this

@[simp] theorem Framing.transport_u (Φ : Framing (hM := hM) S hS) (a c : ℝ) (ha : a ≠ 0) (i) (q) :
    (Φ.transport a c ha).u i q = dtXR a (Φ.u i (ιaff (S := S) a c q)) := rfl

end transport

section glue

variable {S₁ S₂ : Set (M × ℝ)}
  {hS₁ : letI := hM.chartedSpace; haveI := hM.isManifold;
    IsSliceSubmanifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin p)) S₁}
  {hS₂ : letI := hM.chartedSpace; haveI := hM.isManifold;
    IsSliceSubmanifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin p)) S₂}
  {c' c c₀ : ℝ}
  (hov : ∀ q : M × ℝ, c' < q.2 → q.2 < c → (q ∈ S₁ ↔ q ∈ S₂))

include hov in
theorem mem_S₁_of_glueS {r : M × ℝ} (hr : r ∈ glueS S₁ S₂ c' c) (h : r.2 < c) : r ∈ S₁ := by
  have : r ∈ glueS S₁ S₂ c' c ∩ {q | q.2 < c} := ⟨hr, h⟩
  rw [glueS_inter_left hov] at this; exact this.1

include hov in
theorem mem_S₂_of_glueS {r : M × ℝ} (hr : r ∈ glueS S₁ S₂ c' c) (h : c' < r.2) : r ∈ S₂ := by
  have : r ∈ glueS S₁ S₂ c' c ∩ {q | c' < q.2} := ⟨hr, h⟩
  rw [glueS_inter_right hov] at this; exact this.1

variable (h1 : c' < c₀) (h2 : c₀ < c)

/-- The glued framing, cut at time `c₀`. -/
def glueU (u₁ : Fin p → S₁ → EuclideanSpace ℝ (Fin (K + 1)) × ℝ)
    (u₂ : Fin p → S₂ → EuclideanSpace ℝ (Fin (K + 1)) × ℝ) (i : Fin p) (r : glueS S₁ S₂ c' c) :
    EuclideanSpace ℝ (Fin (K + 1)) × ℝ :=
  if h : r.1.2 < c₀ then u₁ i ⟨r.1, mem_S₁_of_glueS hov r.2 (h.trans h2)⟩
  else u₂ i ⟨r.1, mem_S₂_of_glueS hov r.2 (h1.trans_le (not_lt.1 h))⟩

/-- **Gluing of framings** that agree on the overlap strip. -/
def Framing.glue (Φ₁ : Framing (hM := hM) S₁ hS₁) (Φ₂ : Framing (hM := hM) S₂ hS₂)
    (hagree : ∀ i (q : M × ℝ) (hq₁ : q ∈ S₁) (hq₂ : q ∈ S₂), c' < q.2 → q.2 < c →
      Φ₁.u i ⟨q, hq₁⟩ = Φ₂.u i ⟨q, hq₂⟩) :
    Framing (hM := hM) (glueS S₁ S₂ c' c) (isSliceSubmanifold_glueS hM hS₁ hS₂ hov) where
  u := glueU hov h1 h2 Φ₁.u Φ₂.u
  smooth i := by
    letI := hM.chartedSpace
    haveI := hM.isManifold
    have hSg := isSliceSubmanifold_glueS hM hS₁ hS₂ hov
    letI := hSg.chartedSpace
    haveI := hSg.isManifold
    letI := hS₁.chartedSpace
    haveI := hS₁.isManifold
    letI := hS₂.chartedSpace
    haveI := hS₂.isManifold
    intro r
    by_cases hr : r.1.2 < c₀
    · set U : Opens (glueS S₁ S₂ c' c) :=
        ⟨{s | s.1.2 < c₀}, (isOpen_lt continuous_snd continuous_const).preimage continuous_subtype_val⟩
        with hU
      set κ : U → S₁ := fun s => ⟨s.1.1, mem_S₁_of_glueS hov s.1.2 (s.2.trans h2)⟩ with hκ
      have hκs : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ κ :=
        hS₁.contMDiff_codRestrict (F := fun s : U => s.1.1)
          (hSg.contMDiff_val.comp (contMDiff_subtype_val (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))))
          (fun s => mem_S₁_of_glueS hov s.1.2 (s.2.trans h2))
      have heq : (fun s : U => glueU hov h1 h2 Φ₁.u Φ₂.u i s.1) = Φ₁.u i ∘ κ := by
        funext s
        show glueU hov h1 h2 Φ₁.u Φ₂.u i s.1 = Φ₁.u i (κ s)
        unfold glueU
        have hs : s.1.1.2 < c₀ := s.2
        rw [dif_pos hs]
      refine (contMDiffAt_subtype_iff (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ)) (n := ∞) (U := U)
        (f := glueU hov h1 h2 Φ₁.u Φ₂.u i) (x := ⟨r, hr⟩)).1 ?_
      rw [heq]
      exact ((Φ₁.smooth i).comp hκs).contMDiffAt
    · set U : Opens (glueS S₁ S₂ c' c) :=
        ⟨{s | c' < s.1.2}, (isOpen_lt continuous_const continuous_snd).preimage continuous_subtype_val⟩
        with hU
      set κ : U → S₂ := fun s => ⟨s.1.1, mem_S₂_of_glueS hov s.1.2 s.2⟩ with hκ
      have hκs : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ κ :=
        hS₂.contMDiff_codRestrict (F := fun s : U => s.1.1)
          (hSg.contMDiff_val.comp (contMDiff_subtype_val (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))))
          (fun s => mem_S₂_of_glueS hov s.1.2 s.2)
      have heq : (fun s : U => glueU hov h1 h2 Φ₁.u Φ₂.u i s.1) = Φ₂.u i ∘ κ := by
        funext s
        show glueU hov h1 h2 Φ₁.u Φ₂.u i s.1 = Φ₂.u i (κ s)
        unfold glueU
        by_cases h : s.1.1.2 < c₀
        · rw [dif_pos h]
          exact hagree i s.1.1 _ _ s.2 (h.trans h2)
        · rw [dif_neg h]
      have hrU : c' < r.1.2 := h1.trans_le (not_lt.1 hr)
      refine (contMDiffAt_subtype_iff (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ)) (n := ∞) (U := U)
        (f := glueU hov h1 h2 Φ₁.u Φ₂.u i) (x := ⟨r, hrU⟩)).1 ?_
      rw [heq]
      exact ((Φ₂.smooth i).comp hκs).contMDiffAt
  tangent i r := by
    unfold glueU
    split_ifs with h
    · exact Φ₁.tangent i ⟨r.1, _⟩
    · exact Φ₂.tangent i ⟨r.1, _⟩
  normal i r w hw := by
    unfold glueU
    split_ifs with h
    · have hE := tangentS_eq_of_inter_eq hM (isSliceSubmanifold_glueS hM hS₁ hS₂ hov) hS₁
        (isOpen_lt continuous_snd continuous_const) (glueS_inter_left hov) r (h.trans h2)
        (mem_S₁_of_glueS hov r.2 (h.trans h2))
      rw [hE] at hw
      exact Φ₁.normal i _ w hw
    · have hrU : c' < r.1.2 := h1.trans_le (not_lt.1 h)
      have hE := tangentS_eq_of_inter_eq hM (isSliceSubmanifold_glueS hM hS₁ hS₂ hov) hS₂
        (isOpen_lt continuous_const continuous_snd) (glueS_inter_right hov) r hrU
        (mem_S₂_of_glueS hov r.2 hrU)
      rw [hE] at hw
      exact Φ₂.normal i _ w hw
  indep r := by
    by_cases h : r.1.2 < c₀
    · simp only [glueU, dif_pos h]
      exact Φ₁.indep _
    · simp only [glueU, dif_neg h]
      exact Φ₂.indep _

end glue

/-! ### Symmetry -/

theorem affFun_neg_one_involutive (q : M × ℝ) : affFun (-1) 1 (affFun (-1) 1 q) = q := by
  unfold affFun
  ext
  · rfl
  · show -1 * (-1 * q.2 + 1) + 1 = q.2
    ring

theorem continuous_affFun {X : Type*} [TopologicalSpace X] (a c : ℝ) :
    Continuous (affFun (X := X) a c) :=
  continuous_fst.prodMk ((continuous_const.mul continuous_snd).add continuous_const)

theorem continuous_affInv {X : Type*} [TopologicalSpace X] (a c : ℝ) :
    Continuous (affInv (X := X) a c) :=
  continuous_fst.prodMk ((continuous_snd.sub continuous_const).div_const a)

/-- **Framed cobordism is symmetric.** -/
theorem FramedCobordant.symm {F₀ F₁ : FramedSub hM n p} (h : FramedCobordant hM F₀ F₁) :
    FramedCobordant hM F₁ F₀ := by
  obtain ⟨X⟩ := h
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have ha : (-1 : ℝ) ≠ 0 := by norm_num
  set Φ := X.framing.transport (-1) 1 ha with hΦ
  refine ⟨{ S := affFun (-1) 1 ⁻¹' X.S
            hS := isSliceSubmanifold_preimage_affine hM X.hS (-1) 1 ha
            ε := X.ε
            hε := X.hε
            hε' := X.hε'
            end0 := ?_
            end1 := ?_
            compact := ?_
            u := Φ.u
            smooth := Φ.smooth
            tangent := Φ.tangent
            normal := Φ.normal
            indep := Φ.indep
            u_end0 := ?_
            u_end1 := ?_ }⟩
  · intro q hq
    show affFun (-1) 1 q ∈ X.S ↔ q.1 ∈ F₁.N
    exact X.end1 (affFun (-1) 1 q) (by show 1 - X.ε < -1 * q.2 + 1; linarith)
  · intro q hq
    show affFun (-1) 1 q ∈ X.S ↔ q.1 ∈ F₀.N
    exact X.end0 (affFun (-1) 1 q) (by show -1 * q.2 + 1 < X.ε; linarith)
  · have hset : {q ∈ affFun (-1) 1 ⁻¹' X.S | 0 ≤ q.2 ∧ q.2 ≤ 1} =
        affFun (-1) 1 '' {q ∈ X.S | 0 ≤ q.2 ∧ q.2 ≤ 1} := by
      ext q
      constructor
      · rintro ⟨hq, h0, h1⟩
        refine ⟨affFun (-1) 1 q, ⟨hq, ?_, ?_⟩, affFun_neg_one_involutive q⟩
        · show 0 ≤ -1 * q.2 + 1; linarith
        · show -1 * q.2 + 1 ≤ 1; linarith
      · rintro ⟨r, ⟨hr, h0, h1⟩, rfl⟩
        refine ⟨?_, ?_, ?_⟩
        · show affFun (-1) 1 (affFun (-1) 1 r) ∈ X.S
          rw [affFun_neg_one_involutive]; exact hr
        · show 0 ≤ -1 * r.2 + 1; linarith
        · show -1 * r.2 + 1 ≤ 1; linarith
    rw [hset]
    exact X.compact.image (continuous_affFun _ _)
  · intro i q hq ht
    show dtXR (-1) (X.u i (ιaff (S := X.S) (-1) 1 q)) =
      (F₁.v i ⟨(ιaff (S := X.S) (-1) 1 q).1.1, hq⟩, 0)
    rw [X.u_end1 i (ιaff (S := X.S) (-1) 1 q) hq (by show 1 - X.ε < -1 * q.1.2 + 1; linarith)]
    simp only [dtXR_apply, mul_zero]
  · intro i q hq ht
    show dtXR (-1) (X.u i (ιaff (S := X.S) (-1) 1 q)) =
      (F₀.v i ⟨(ιaff (S := X.S) (-1) 1 q).1.1, hq⟩, 0)
    rw [X.u_end0 i (ιaff (S := X.S) (-1) 1 q) hq (by show -1 * q.1.2 + 1 < X.ε; linarith)]
    simp only [dtXR_apply, mul_zero]

/-! ### Transitivity -/

/-- **Framed cobordism is transitive.** -/
theorem FramedCobordant.trans {F₀ F₁ F₂ : FramedSub hM n p} (h₁ : FramedCobordant hM F₀ F₁)
    (h₂ : FramedCobordant hM F₁ F₂) : FramedCobordant hM F₀ F₂ := by
  obtain ⟨X⟩ := h₁
  obtain ⟨Y⟩ := h₂
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hε₁ := X.hε
  have hε₁' := X.hε'
  have hε₂ := Y.hε
  have hε₂' := Y.hε'
  -- the shifted second cobordism
  set S₂' : Set (M × ℝ) := affFun 1 (-1) ⁻¹' Y.S with hS₂'def
  have hS₂' := isSliceSubmanifold_preimage_affine hM Y.hS 1 (-1) one_ne_zero
  set Φ₂ := Y.framing.transport 1 (-1) one_ne_zero with hΦ₂
  -- the overlap
  have hov : ∀ q : M × ℝ, 1 - X.ε < q.2 → q.2 < 1 + Y.ε → (q ∈ X.S ↔ q ∈ S₂') := by
    intro q hq1 hq2
    rw [X.end1 q hq1]
    show _ ↔ affFun 1 (-1) q ∈ Y.S
    rw [Y.end0 (affFun 1 (-1) q) (by show 1 * q.2 + -1 < Y.ε; linarith)]
    exact Iff.rfl
  have hc₀ : 1 - X.ε < (1 : ℝ) := by linarith
  have hc₀' : (1 : ℝ) < 1 + Y.ε := by linarith
  have hagree : ∀ i (q : M × ℝ) (hq₁ : q ∈ X.S) (hq₂ : q ∈ S₂'), 1 - X.ε < q.2 → q.2 < 1 + Y.ε →
      X.framing.u i ⟨q, hq₁⟩ = Φ₂.u i ⟨q, hq₂⟩ := by
    intro i q hq₁ hq₂ hq1 hq2
    have hN : q.1 ∈ F₁.N := (X.end1 q hq1).1 hq₁
    have hN' : (ιaff (S := Y.S) 1 (-1) ⟨q, hq₂⟩).1.1 ∈ F₁.N := hN
    show X.u i ⟨q, hq₁⟩ = dtXR 1 (Y.u i (ιaff (S := Y.S) 1 (-1) ⟨q, hq₂⟩))
    rw [X.u_end1 i ⟨q, hq₁⟩ hN hq1,
      Y.u_end0 i (ιaff (S := Y.S) 1 (-1) ⟨q, hq₂⟩) hN' (by show 1 * q.2 + -1 < Y.ε; linarith)]
    simp only [dtXR_apply, mul_zero]
    rfl
  set Sg := glueS X.S S₂' (1 - X.ε) (1 + Y.ε) with hSg
  have hSgS := isSliceSubmanifold_glueS hM X.hS hS₂' hov
  set Φg := X.framing.glue hov hc₀ hc₀' Φ₂ hagree with hΦg
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  set Φ := Φg.transport 2 0 h2 with hΦ
  set ε := min X.ε Y.ε / 2 with hε
  have hεX : ε ≤ X.ε / 2 := by rw [hε]; linarith [min_le_left X.ε Y.ε]
  have hεY : ε ≤ Y.ε / 2 := by rw [hε]; linarith [min_le_right X.ε Y.ε]
  have hεpos : 0 < ε := by rw [hε]; exact half_pos (lt_min hε₁ hε₂)
  -- compactness of the glued piece on `[0, 2]`
  have hcg : IsCompact {r ∈ Sg | 0 ≤ r.2 ∧ r.2 ≤ 2} := by
    have hset : {r ∈ Sg | 0 ≤ r.2 ∧ r.2 ≤ 2} =
        {r ∈ X.S | 0 ≤ r.2 ∧ r.2 ≤ 1} ∪ affInv 1 (-1) '' {s ∈ Y.S | 0 ≤ s.2 ∧ s.2 ≤ 1} := by
      ext r
      constructor
      · rintro ⟨hr, h0, h2r⟩
        by_cases hr1 : r.2 ≤ 1
        · exact Or.inl ⟨mem_S₁_of_glueS hov hr (by linarith), h0, hr1⟩
        · refine Or.inr ⟨affFun 1 (-1) r, ⟨mem_S₂_of_glueS hov hr (by linarith), ?_, ?_⟩,
            affInv_affFun (-1) one_ne_zero r⟩
          · show 0 ≤ 1 * r.2 + -1; linarith
          · show 1 * r.2 + -1 ≤ 1; linarith
      · rintro (⟨hr, h0, h1⟩ | ⟨s, ⟨hs, h0, h1⟩, rfl⟩)
        · exact ⟨Or.inl ⟨hr, by linarith⟩, h0, by linarith⟩
        · have hs2 : (affInv 1 (-1) s).2 = s.2 + 1 := by
            show (s.2 - -1) / 1 = s.2 + 1; ring
          refine ⟨Or.inr ⟨?_, ?_⟩, ?_, ?_⟩
          · show affFun 1 (-1) (affInv 1 (-1) s) ∈ Y.S
            rw [affFun_affInv (-1) one_ne_zero]; exact hs
          · show 1 - X.ε < (affInv 1 (-1) s).2
            rw [hs2]; linarith
          · rw [hs2]; linarith
          · rw [hs2]; linarith
    rw [hset]
    exact X.compact.union (Y.compact.image (continuous_affInv _ _))
  refine ⟨{ S := affFun 2 0 ⁻¹' Sg
            hS := isSliceSubmanifold_preimage_affine hM hSgS 2 0 h2
            ε := ε
            hε := hεpos
            hε' := by linarith
            end0 := ?_
            end1 := ?_
            compact := ?_
            u := Φ.u
            smooth := Φ.smooth
            tangent := Φ.tangent
            normal := Φ.normal
            indep := Φ.indep
            u_end0 := ?_
            u_end1 := ?_ }⟩
  · intro q hq
    show affFun 2 0 q ∈ Sg ↔ q.1 ∈ F₀.N
    have hlt : (affFun 2 0 q).2 < 1 + Y.ε := by show 2 * q.2 + 0 < 1 + Y.ε; linarith
    have hlt' : (affFun 2 0 q).2 < X.ε := by show 2 * q.2 + 0 < X.ε; linarith
    constructor
    · intro h
      exact (X.end0 (affFun 2 0 q) hlt').1 (mem_S₁_of_glueS hov h hlt)
    · intro h
      exact Or.inl ⟨(X.end0 (affFun 2 0 q) hlt').2 h, hlt⟩
  · intro q hq
    show affFun 2 0 q ∈ Sg ↔ q.1 ∈ F₂.N
    have hgt : 1 - X.ε < (affFun 2 0 q).2 := by show 1 - X.ε < 2 * q.2 + 0; linarith
    have hgt' : 1 - Y.ε < (affFun 1 (-1) (affFun 2 0 q)).2 := by
      show 1 - Y.ε < 1 * (2 * q.2 + 0) + -1; linarith
    constructor
    · intro h
      have := mem_S₂_of_glueS hov h hgt
      exact (Y.end1 _ hgt').1 this
    · intro h
      exact Or.inr ⟨(Y.end1 _ hgt').2 h, hgt⟩
  · have hset : {q ∈ affFun 2 0 ⁻¹' Sg | 0 ≤ q.2 ∧ q.2 ≤ 1} =
        affInv 2 0 '' {r ∈ Sg | 0 ≤ r.2 ∧ r.2 ≤ 2} := by
      ext q
      constructor
      · rintro ⟨hq, h0, h1⟩
        refine ⟨affFun 2 0 q, ⟨hq, ?_, ?_⟩, affInv_affFun 0 h2 q⟩
        · show 0 ≤ 2 * q.2 + 0; linarith
        · show 2 * q.2 + 0 ≤ 2; linarith
      · rintro ⟨r, ⟨hr, h0, h2r⟩, rfl⟩
        have hr2 : (affInv 2 0 r).2 = r.2 / 2 := by show (r.2 - 0) / 2 = r.2 / 2; ring
        refine ⟨?_, ?_, ?_⟩
        · show affFun 2 0 (affInv 2 0 r) ∈ Sg
          rw [affFun_affInv 0 h2]; exact hr
        · rw [hr2]; linarith
        · rw [hr2]; linarith
    rw [hset]
    exact hcg.image (continuous_affInv _ _)
  · intro i q hq ht
    have hlt : (affFun 2 0 q.1).2 < 1 := by show 2 * q.1.2 + 0 < 1; linarith
    have hlt' : (affFun 2 0 q.1).2 < X.ε := by show 2 * q.1.2 + 0 < X.ε; linarith
    show dtXR 2 (glueU hov hc₀ hc₀' X.framing.u Φ₂.u i (ιaff (S := Sg) 2 0 q)) = (F₀.v i ⟨q.1.1, hq⟩, 0)
    unfold glueU
    have hlt2 : (ιaff (S := Sg) 2 0 q).1.2 < 1 := hlt
    rw [dif_pos hlt2]
    have hq' : (affFun 2 0 q.1).1 ∈ F₀.N := hq
    have hmem : affFun 2 0 q.1 ∈ X.S := mem_S₁_of_glueS hov q.2 (hlt.trans hc₀')
    have key := X.u_end0 i ⟨affFun 2 0 q.1, hmem⟩ hq' hlt'
    show dtXR 2 (X.u i ⟨affFun 2 0 q.1, hmem⟩) = (F₀.v i ⟨(affFun 2 0 q.1).1, hq'⟩, 0)
    rw [key]
    simp only [dtXR_apply, mul_zero]
  · intro i q hq ht
    have hnlt : ¬ (affFun 2 0 q.1).2 < 1 := by show ¬ 2 * q.1.2 + 0 < 1; linarith
    have hgt' : 1 - Y.ε < (affFun 1 (-1) (affFun 2 0 q.1)).2 := by
      show 1 - Y.ε < 1 * (2 * q.1.2 + 0) + -1; linarith
    show dtXR 2 (glueU hov hc₀ hc₀' X.framing.u Φ₂.u i (ιaff (S := Sg) 2 0 q)) = (F₂.v i ⟨q.1.1, hq⟩, 0)
    unfold glueU
    have hnlt2 : ¬ (ιaff (S := Sg) 2 0 q).1.2 < 1 := hnlt
    rw [dif_neg hnlt2]
    have hq' : (ιaff (S := Y.S) 1 (-1) ⟨affFun 2 0 q.1, mem_S₂_of_glueS hov (ιaff (S := Sg) 2 0 q).2
      (hc₀.trans_le (not_lt.1 hnlt2))⟩).1.1 ∈ F₂.N := hq
    show dtXR 2 (dtXR 1 (Y.u i (ιaff (S := Y.S) 1 (-1) ⟨affFun 2 0 q.1, _⟩))) =
      (F₂.v i ⟨(ιaff (S := Y.S) 1 (-1) ⟨affFun 2 0 q.1, _⟩).1.1, hq'⟩, 0)
    rw [Y.u_end1 i (ιaff (S := Y.S) 1 (-1) ⟨affFun 2 0 q.1, _⟩) hq' hgt']
    simp only [dtXR_apply, mul_zero]

end Framed

end Milnor
