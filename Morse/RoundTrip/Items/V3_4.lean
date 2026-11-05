import Morse
import RoundTrip.Check
import RoundTrip.Blind.V3_4

open Set Metric
open scoped ContDiff Manifold

noncomputable section

namespace RoundTrip.V3_4

/-- The project's statement (Theorem 3.1 carrying the level set, for slice submanifolds, and the
abstract slab-flow lemma), universes instantiated at `0`. -/
def A : Prop :=
  (type_of% @Morse.exists_diffeomorph_image_sublevel_level.{0, 0, 0}) ∧
  (type_of% @Morse.IsSlabFlow.image_level.{0})

theorem A_holds : A :=
  ⟨@Morse.exists_diffeomorph_image_sublevel_level.{0, 0, 0}, @Morse.IsSlabFlow.image_level.{0}⟩

/-! ### Glue -/

section Glue

variable {X : Type} [TopologicalSpace X] {k : ℕ}

instance : CompactSpace (closedBall (0 : EuclideanSpace ℝ (Fin k)) 1) :=
  isCompact_iff_compactSpace.1 (isCompact_closedBall _ _)

/-- An injective map, continuous on the closed ball, into a Hausdorff space is a homeomorphism of
the ball onto its image. -/
def homeoImage [T2Space X] (h : EuclideanSpace ℝ (Fin k) → X)
    (hc : ContinuousOn h (closedBall 0 1)) (hi : InjOn h (closedBall 0 1)) :
    closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 ≃ₜ (h '' closedBall 0 1) :=
  have hcont : Continuous (fun z : closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 =>
      (⟨h z.1, mem_image_of_mem h z.2⟩ : h '' closedBall 0 1)) :=
    (continuousOn_iff_continuous_domRestrict.1 hc).subtype_mk _
  hcont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ ⟨fun a b hab =>
    Subtype.ext (hi a.2 b.2 (congrArg Subtype.val hab)), fun ⟨_, z, hz, rfl⟩ => ⟨⟨z, hz⟩, rfl⟩⟩)

/-- Balls of equal dimension. -/
def ballCongr {k m : ℕ} (h : k = m) :
    closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 ≃ₜ closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 := by
  subst h; exact Homeomorph.refl _

theorem norm_ballCongr {k m : ℕ} (h : k = m) (z : closedBall (0 : EuclideanSpace ℝ (Fin k)) 1) :
    ‖(ballCongr h z).1‖ = ‖z.1‖ := by
  subst h; rfl

/-- A parametrised cell: the ball of `ℝᵐ` (any `k = m`) is homeomorphic to `S = χ(ball)`, the unit
sphere going to `L = χ(sphere)`. -/
theorem exists_cellHomeo [T2Space X] {m : ℕ} (hkm : k = m) (χ : EuclideanSpace ℝ (Fin k) → X)
    (hc : ContinuousOn χ (closedBall 0 1)) (hi : InjOn χ (closedBall 0 1)) {S L : Set X}
    (hS : χ '' closedBall 0 1 = S) (hL : χ '' sphere 0 1 = L) :
    ∃ e : closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 ≃ₜ S, ∀ z, ‖z.1‖ = 1 ↔ (e z).1 ∈ L := by
  refine ⟨(ballCongr hkm).symm.trans ((homeoImage χ hc hi).trans (Homeomorph.setCongr hS)),
    fun z => ?_⟩
  set w := (ballCongr hkm).symm z
  have hw : ‖w.1‖ = ‖z.1‖ := by
    rw [← norm_ballCongr hkm w]; simp [w]
  change ‖z.1‖ = 1 ↔ χ w.1 ∈ L
  rw [← hw, ← hL]
  constructor
  · intro h1
    exact mem_image_of_mem χ (by simpa using h1)
  · rintro ⟨v, hv, hvw⟩
    rw [← hi (sphere_subset_closedBall hv) w.2 hvw]
    simpa using hv

end Glue

section Main

variable {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  {f : M → ℝ} {p q : M}

omit [T2Space M] [CompactSpace M] in
/-- In dimension `0` every point is critical. -/
theorem isCriticalPointM_of_zero (f : M → ℝ) (hn : n = 0) (x : M) :
    Morse.IsCriticalPointM (EuclideanSpace ℝ (Fin n)) f x := by
  subst hn
  change mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) 𝓘(ℝ, ℝ) f x = 0
  ext v
  have hv : v = 0 := Subsingleton.elim (α := EuclideanSpace ℝ (Fin 0)) v 0
  rw [hv, map_zero, map_zero]

/-- The slab part, from `A`'s first conjunct through an embedding of `M`: for `0 < ε < 1/2`,
`M^ε ≃ₜ M^{1-ε}`, the level `ε` going to the level `1 - ε`. -/
theorem slab (hA : A) (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ f)
    (honly : ∀ x, Morse.IsCriticalPointM (EuclideanSpace ℝ (Fin n)) f x → x = p ∨ x = q)
    (hp0 : f p = 0) (hq1 : f q = 1) {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ∃ H : {x : M // f x ≤ ε} ≃ₜ {x : M // f x ≤ 1 - ε},
      ∀ x, f x.1 = ε ↔ f (H x).1 = 1 - ε := by
  have hcr : ∀ x, Morse.IsCriticalPointM (EuclideanSpace ℝ (Fin n)) f x → f x = 0 ∨ f x = 1 := by
    intro x hx
    rcases honly x hx with rfl | rfl
    exacts [Or.inl hp0, Or.inr hq1]
  cases n with
  | zero =>
    have hval : ∀ x, f x = 0 ∨ f x = 1 := fun x => hcr x (isCriticalPointM_of_zero f rfl x)
    have hset : {x : M | f x ≤ ε} = {x : M | f x ≤ 1 - ε} := by
      ext x
      rcases hval x with h | h <;> simp only [mem_ofPred_eq, h] <;> constructor <;> intro <;> linarith
    refine ⟨Homeomorph.setCongr hset, fun x => ?_⟩
    change f x.1 = ε ↔ f x.1 = 1 - ε
    rcases hval x.1 with h | h <;> rw [h] <;> constructor <;> intro <;> linarith
  | succ d =>
    obtain ⟨K, m, N, hN, -, hNc, -, ⟨Φ⟩⟩ :=
      Morse.exists_diffeomorph_sliceSubmanifold (E := EuclideanSpace ℝ (Fin (d + 1))) (M := M)
        (n := d + 1) finrank_euclideanSpace_fin
    let _ := hN.chartedSpace
    have := hN.isManifold
    have : CompactSpace N := isCompact_iff_compactSpace.1 hNc
    obtain ⟨F, hF, hFf⟩ := Morse.exists_contDiff_comp_val_eq hN hNc ⟨(Φ p).1, (Φ p).2⟩
      (f := f ∘ Φ.symm) (hf.comp Φ.symm.contMDiff)
    have hg : ∀ u : N, (F ∘ Subtype.val) u = f (Φ.symm u) := fun u => congrFun hFf u
    have hgc : Continuous (F ∘ Subtype.val : N → ℝ) := hF.continuous.comp continuous_subtype_val
    obtain ⟨h31, -⟩ := hA
    obtain ⟨Ψ, hΨs, hΨl⟩ := h31 hN hF (a := ε) (b := 1 - ε) (by linarith)
      ((isClosed_Icc.preimage hgc).isCompact) (fun u hu hc => by
        rw [hFf, Morse.isCriticalPointM_comp_symm_iff Φ] at hc
        have hu' : f (Φ.symm u) ∈ Icc ε (1 - ε) := hg u ▸ hu
        rcases hcr _ hc with h | h <;> rw [h] at hu' <;> linarith [hu'.1, hu'.2])
    -- membership transfers
    have hfw : ∀ x : M, (F ∘ Subtype.val) (Φ x) = f x := fun x => by rw [hg, Φ.symm_apply_apply]
    have fwd : ∀ x : M, f x ≤ ε → f (Φ.symm (Ψ (Φ x))) ≤ 1 - ε := by
      intro x hx
      have : Ψ (Φ x) ∈ Morse.sublevel (F ∘ Subtype.val) (1 - ε) :=
        hΨs ▸ mem_image_of_mem Ψ (show Φ x ∈ Morse.sublevel (F ∘ Subtype.val) ε by
          rw [Morse.sublevel, mem_ofPred_eq, hfw]; exact hx)
      rw [Morse.sublevel, mem_ofPred_eq, hg] at this
      exact this
    have bwd : ∀ y : M, f y ≤ 1 - ε → f (Φ.symm (Ψ.symm (Φ y))) ≤ ε := by
      intro y hy
      have : Φ y ∈ Ψ '' Morse.sublevel (F ∘ Subtype.val) ε := by
        rw [hΨs, Morse.sublevel, mem_ofPred_eq, hfw]; exact hy
      obtain ⟨u, hu, hΨu⟩ := this
      rw [← hΨu, Ψ.symm_apply_apply, ← hg]
      exact hu
    let H : {x : M // f x ≤ ε} ≃ₜ {x : M // f x ≤ 1 - ε} :=
      { toFun := fun x => ⟨Φ.symm (Ψ (Φ x.1)), fwd x.1 x.2⟩
        invFun := fun y => ⟨Φ.symm (Ψ.symm (Φ y.1)), bwd y.1 y.2⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun y => Subtype.ext (by simp)
        continuous_toFun := (Φ.symm.continuous.comp (Ψ.continuous.comp
          (Φ.continuous.comp continuous_subtype_val))).subtype_mk _
        continuous_invFun := (Φ.symm.continuous.comp (Ψ.symm.continuous.comp
          (Φ.continuous.comp continuous_subtype_val))).subtype_mk _ }
    refine ⟨H, fun x => ?_⟩
    change f x.1 = ε ↔ f (Φ.symm (Ψ (Φ x.1))) = 1 - ε
    rw [← hg, ← hfw x.1]
    constructor
    · intro h
      have : Ψ (Φ x.1) ∈ (F ∘ Subtype.val) ⁻¹' {1 - ε} :=
        hΨl ▸ mem_image_of_mem Ψ (show Φ x.1 ∈ (F ∘ Subtype.val) ⁻¹' {ε} from h)
      exact this
    · intro h
      have : Ψ (Φ x.1) ∈ Ψ '' ((F ∘ Subtype.val) ⁻¹' {ε}) := by
        rw [hΨl]; exact h
      obtain ⟨u, hu, hΨu⟩ := this
      rw [← Ψ.injective hΨu]
      exact hu

end Main

theorem A_to_B : A → B := by
  intro hA n M _ _ _ _ _ f p q hf hpq hp hq honly hp0 hq1 hbd
  have hfc : Continuous f := hf.continuous
  have hfU : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ f univ := hf.contMDiffOn
  -- `p` is the strict minimum, `q` the strict maximum
  have hpmin : ∀ x, x ≠ p → f p < f x := by
    intro x hx
    refine lt_of_le_of_ne (hbd x).1 fun hfx => ?_
    have hc := Morse.isCriticalPointM_of_isLocalMin (E := EuclideanSpace ℝ (Fin n))
      (Filter.Eventually.of_forall fun y => hfx ▸ (hbd y).1 : IsLocalMin f x)
    rcases honly x hc with rfl | rfl
    · exact hx rfl
    · rw [hp0, hq1] at hfx; norm_num at hfx
  have hqmax : ∀ x, x ≠ q → f x < f q := by
    intro x hx
    refine lt_of_le_of_ne (hbd x).2 fun hfx => ?_
    have hc := Morse.isCriticalPointM_of_isLocalMin (E := EuclideanSpace ℝ (Fin n))
      (f := fun y => -f y)
      (Filter.Eventually.of_forall fun y => by simp only [neg_le_neg_iff]; exact hfx ▸ (hbd y).2)
    have hc' : Morse.IsCriticalPointM (EuclideanSpace ℝ (Fin n)) f x := by
      have h1 : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) (fun y => -f y) x = 0 := hc
      have h2 : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) (fun y => -f y) x =
          -mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) f x :=
        (((hf.mdifferentiable (by simp)) x).hasMFDerivAt.neg).mfderiv
      change mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) f x = 0
      rw [h2] at h1
      exact neg_eq_zero.1 h1
    rcases honly x hc' with rfl | rfl
    · rw [hp0, hq1] at hfx; norm_num at hfx
    · exact hx rfl
  -- Morse charts at the extrema and the small cells
  obtain ⟨y₁, -, hp₁, -, hy₁0, hy₁⟩ := Morse.exists_morse_chart_of_isLocalMin isOpen_univ
    (mem_univ p) hfU hp (Filter.Eventually.of_forall fun x => (hbd x).1)
  obtain ⟨y₂, -, hq₂, -, hy₂0, hy₂⟩ := Morse.exists_morse_chart_of_isLocalMax isOpen_univ
    (mem_univ q) hfU hq (Filter.Eventually.of_forall fun x => (hbd x).2)
  obtain ⟨δ₁, hδ₁, h₁⟩ := Morse.exists_image_closedBall_eq_sublevel hfc hpmin y₁ hp₁ hy₁0 hy₁
  obtain ⟨δ₂, hδ₂, h₂⟩ := Morse.exists_image_closedBall_eq_sublevel (f := fun x => -f x) hfc.neg
    (fun x hx => neg_lt_neg (hqmax x hx)) y₂ hq₂ hy₂0
    (fun x hx => by rw [hy₂ x hx]; ring)
  refine ⟨min (min δ₁ δ₂) (1 / 2), lt_min (lt_min hδ₁ hδ₂) (by norm_num), fun ε hε hεδ => ?_⟩
  have hε₁ : ε < δ₁ := hεδ.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hε₂ : ε < δ₂ := hεδ.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hε3 : ε < 1 / 2 := hεδ.trans_le (min_le_right _ _)
  obtain ⟨H, hH⟩ := slab hA hf honly hp0 hq1 hε hε3
  -- the cell `M^ε`
  obtain ⟨hc₁, hi₁, him₁, hsp₁⟩ := h₁ ε hε hε₁
  rw [hp0, zero_add] at him₁ hsp₁
  obtain ⟨e₁, he₁⟩ := exists_cellHomeo finrank_euclideanSpace_fin _ hc₁ hi₁ him₁ hsp₁
  -- the cell `f ≥ 1 - ε`
  obtain ⟨hc₂, hi₂, him₂, hsp₂⟩ := h₂ ε hε hε₂
  have him₂' : (fun v => y₂.symm (√ε • v)) '' closedBall 0 1 = {x | 1 - ε ≤ f x} := by
    rw [him₂, hq1]; ext x; simp only [mem_ofPred_eq]; constructor <;> intro h <;> linarith
  have hsp₂' : (fun v => y₂.symm (√ε • v)) '' sphere 0 1 = {x | f x = 1 - ε} := by
    rw [hsp₂, hq1]; ext x; simp only [mem_ofPred_eq]; constructor <;> intro h <;> linarith
  obtain ⟨e₂, he₂⟩ := exists_cellHomeo finrank_euclideanSpace_fin _ hc₂ hi₂ him₂' hsp₂'
  refine ⟨⟨H⟩, fun x => le_total _ _, (H.symm.trans e₁.symm), e₂.symm, fun x => ?_, fun x => ?_⟩
  · change ‖(e₁.symm (H.symm x)).1‖ = 1 ↔ _
    rw [he₁, Homeomorph.apply_symm_apply]
    change f (H.symm x).1 = ε ↔ _
    rw [hH, Homeomorph.apply_symm_apply]
  · change ‖(e₂.symm x).1‖ = 1 ↔ _
    rw [he₂, Homeomorph.apply_symm_apply]
    rfl

#rt_check RoundTrip.V3_4.A_to_B [Morse.exists_diffeomorph_image_sublevel_level,
  Morse.IsSlabFlow.image_level]

end RoundTrip.V3_4

end
