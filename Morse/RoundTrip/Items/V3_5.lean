import Morse
import RoundTrip.Check
import RoundTrip.Blind.V3_5

open Set Metric

noncomputable section

namespace RoundTrip.V3_5

/-- The project's statement (the gluing theorem behind Reeb's theorem), universe instantiated at
`0`. (`Morse.alexanderConeHomeomorph` is a definition: vocabulary.) -/
def A : Prop := type_of% @Morse.nonempty_homeomorph_sphere_of_union_closedBall.{0}

theorem A_holds : A := @Morse.nonempty_homeomorph_sphere_of_union_closedBall.{0}

/-! ### Glue -/

section Glue

variable {X : Type} [TopologicalSpace X]

/-- A space covered by two closed Hausdorff subspaces is Hausdorff. -/
theorem t2Space_of_union {S T : Set X} (hS : IsClosed S) (hT : IsClosed T) (hST : S ∪ T = univ)
    [T2Space S] [T2Space T] : T2Space X := by
  -- separate `x ≠ y` "relative to `R`": open `U ∋ x`, `V ∋ y` with `U ∩ V ∩ R = ∅`
  have sep : ∀ (R : Set X), IsClosed R → T2Space R → ∀ x y : X, x ≠ y →
      ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ U ∩ V ∩ R = ∅ := by
    intro R hR _ x y hxy
    by_cases hx : x ∈ R
    · by_cases hy : y ∈ R
      · obtain ⟨U', V', hU', hV', hxU', hyV', hUV'⟩ :=
          t2_separation (x := (⟨x, hx⟩ : R)) (y := ⟨y, hy⟩) (fun h => hxy (congrArg Subtype.val h))
        obtain ⟨U, hU, rfl⟩ := isOpen_induced_iff.1 hU'
        obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.1 hV'
        refine ⟨U, V, hU, hV, hxU', hyV', eq_empty_iff_forall_notMem.2 fun z ⟨⟨hzU, hzV⟩, hzR⟩ => ?_⟩
        exact Set.disjoint_left.1 hUV' (show (⟨z, hzR⟩ : R) ∈ Subtype.val ⁻¹' U from hzU) hzV
      · exact ⟨univ, Rᶜ, isOpen_univ, hR.isOpen_compl, trivial, hy, by simp⟩
    · exact ⟨Rᶜ, univ, hR.isOpen_compl, isOpen_univ, hx, trivial, by simp⟩
  refine ⟨fun x y hxy => ?_⟩
  obtain ⟨U₁, V₁, hU₁, hV₁, hx₁, hy₁, h₁⟩ := sep S hS inferInstance x y hxy
  obtain ⟨U₂, V₂, hU₂, hV₂, hx₂, hy₂, h₂⟩ := sep T hT inferInstance x y hxy
  refine ⟨U₁ ∩ U₂, V₁ ∩ V₂, hU₁.inter hU₂, hV₁.inter hV₂, ⟨hx₁, hx₂⟩, ⟨hy₁, hy₂⟩, ?_⟩
  rw [Set.disjoint_iff]
  rintro z ⟨⟨hz1, hz2⟩, hz3, hz4⟩
  have : z ∈ S ∪ T := hST ▸ trivial
  rcases this with hz | hz
  · exact (eq_empty_iff_forall_notMem.1 h₁) z ⟨⟨hz1, hz3⟩, hz⟩
  · exact (eq_empty_iff_forall_notMem.1 h₂) z ⟨⟨hz2, hz4⟩, hz⟩

variable {n : ℕ}

local notation "cb" => closedBall (0 : EuclideanSpace ℝ (Fin n)) 1

instance : CompactSpace cb := isCompact_iff_compactSpace.1 (isCompact_closedBall _ _)

/-- An injective map, continuous on the closed ball, into a Hausdorff space is a homeomorphism of
the ball onto its image. -/
def homeoImage [T2Space X] (h : EuclideanSpace ℝ (Fin n) → X) (hc : ContinuousOn h cb)
    (hi : InjOn h cb) : cb ≃ₜ (h '' cb) :=
  have hcont : Continuous (fun z : cb => (⟨h z.1, mem_image_of_mem h z.2⟩ : h '' cb)) :=
    (continuousOn_iff_continuous_domRestrict.1 hc).subtype_mk _
  hcont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ ⟨fun a b hab =>
    Subtype.ext (hi a.2 b.2 (congrArg Subtype.val hab)), fun ⟨_, z, hz, rfl⟩ => ⟨⟨z, hz⟩, rfl⟩⟩)

theorem homeoImage_apply [T2Space X] (h : EuclideanSpace ℝ (Fin n) → X) (hc : ContinuousOn h cb)
    (hi : InjOn h cb) (z : cb) : (homeoImage h hc hi z).1 = h z.1 := rfl

/-- A homeomorphism `S ≃ₜ e^n` read as a map `ℝⁿ → X`, defined on the ball. -/
def ext {S : Set X} (e : S ≃ₜ cb) (z : EuclideanSpace ℝ (Fin n)) : X :=
  open Classical in
  if hz : z ∈ cb then (e.symm ⟨z, hz⟩).1 else (e.symm ⟨0, mem_closedBall_self zero_le_one⟩).1

theorem ext_of_mem {S : Set X} (e : S ≃ₜ cb) {z} (hz : z ∈ cb) : ext e z = (e.symm ⟨z, hz⟩).1 := by
  rw [ext, dif_pos hz]

theorem continuousOn_ext {S : Set X} (e : S ≃ₜ cb) : ContinuousOn (ext e) cb := by
  rw [continuousOn_iff_continuous_domRestrict]
  have : (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).domRestrict (ext e) = fun z => (e.symm z).1 := funext fun z => ext_of_mem e z.2
  rw [this]
  exact continuous_subtype_val.comp e.symm.continuous

theorem injOn_ext {S : Set X} (e : S ≃ₜ cb) : InjOn (ext e) cb := by
  intro a ha b hb hab
  rw [ext_of_mem e ha, ext_of_mem e hb] at hab
  exact congrArg Subtype.val (e.symm.injective (Subtype.ext hab))

theorem image_ext {S : Set X} (e : S ≃ₜ cb) : ext e '' cb = S := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [ext_of_mem e hz]
    exact (e.symm _).2
  · intro hx
    refine ⟨(e ⟨x, hx⟩).1, (e ⟨x, hx⟩).2, ?_⟩
    rw [ext_of_mem e (e ⟨x, hx⟩).2]
    simp

theorem image_sphere_ext {S : Set X} (e : S ≃ₜ cb) :
    ext e '' sphere 0 1 = {x | ∃ hx : x ∈ S, ‖(e ⟨x, hx⟩).1‖ = 1} := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : z ∈ cb := sphere_subset_closedBall hz
    rw [ext_of_mem e hz']
    refine ⟨(e.symm _).2, ?_⟩
    simp only [Subtype.coe_eta, Homeomorph.apply_symm_apply]
    simpa using hz
  · rintro ⟨hx, hn⟩
    refine ⟨(e ⟨x, hx⟩).1, by simpa using hn, ?_⟩
    rw [ext_of_mem e (e ⟨x, hx⟩).2]
    simp

end Glue

theorem A_to_B : A → B := by
  intro hA n X _ S T hS hT hST e₁ e₂ hb₁ hb₂
  have : T2Space S := e₁.isEmbedding.t2Space
  have : T2Space T := e₂.isEmbedding.t2Space
  have : T2Space X := t2Space_of_union hS hT hST
  have hi₁ : ext e₁ '' sphere 0 1 = S ∩ T := by
    rw [image_sphere_ext]
    ext x
    exact ⟨fun ⟨hx, hn⟩ => ⟨hx, (hb₁ ⟨x, hx⟩).2 hn⟩, fun ⟨hx, hxT⟩ => ⟨hx, (hb₁ ⟨x, hx⟩).1 hxT⟩⟩
  have hi₂ : ext e₂ '' sphere 0 1 = S ∩ T := by
    rw [image_sphere_ext]
    ext x
    exact ⟨fun ⟨hx, hn⟩ => ⟨(hb₂ ⟨x, hx⟩).2 hn, hx⟩, fun ⟨hxS, hx⟩ => ⟨hx, (hb₂ ⟨x, hx⟩).1 hxS⟩⟩
  exact hA (continuousOn_ext e₁) (continuousOn_ext e₂) (injOn_ext e₁) (injOn_ext e₂)
    (by rw [image_ext, image_ext, hST]) (by rw [image_ext, image_ext, hi₁])
    (by rw [hi₁, hi₂])

theorem B_to_A : B → A := by
  intro hB X _ _ n h₁ h₂ hc₁ hc₂ hi₁ hi₂ hcover hinter hbdry
  have hcb : IsCompact (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := isCompact_closedBall _ _
  let e₁ := homeoImage h₁ hc₁ hi₁
  let e₂ := homeoImage h₂ hc₂ hi₂
  refine hB n X _ _ (hcb.image_of_continuousOn hc₁).isClosed (hcb.image_of_continuousOn hc₂).isClosed
    hcover e₁.symm e₂.symm (fun x => ?_) (fun x => ?_)
  · -- `x = h₁ z`
    obtain ⟨z, rfl⟩ := e₁.surjective x
    rw [Homeomorph.symm_apply_apply, homeoImage_apply]
    constructor
    · intro hx
      have hmem : h₁ z.1 ∈ h₁ '' closedBall 0 1 ∩ h₂ '' closedBall 0 1 :=
        ⟨mem_image_of_mem h₁ z.2, hx⟩
      rw [hinter] at hmem
      obtain ⟨w, hw, hwz⟩ := hmem
      have := hi₁ (sphere_subset_closedBall hw) z.2 hwz
      rw [← this]
      simpa using hw
    · intro hz
      have : h₁ z.1 ∈ h₂ '' sphere 0 1 := hbdry ▸ mem_image_of_mem h₁ (by simpa using hz)
      exact image_mono sphere_subset_closedBall this
  · obtain ⟨z, rfl⟩ := e₂.surjective x
    rw [Homeomorph.symm_apply_apply, homeoImage_apply]
    constructor
    · intro hx
      have h1 : h₂ z.1 ∈ h₂ '' sphere 0 1 := by
        rw [hbdry, ← hinter]
        exact ⟨hx, mem_image_of_mem h₂ z.2⟩
      obtain ⟨w, hw, hwz⟩ := h1
      have := hi₂ (sphere_subset_closedBall hw) z.2 hwz
      rw [← this]
      simpa using hw
    · intro hz
      have : h₂ z.1 ∈ h₁ '' sphere 0 1 := hbdry ▸ mem_image_of_mem h₂ (by simpa using hz)
      exact image_mono sphere_subset_closedBall this

#rt_check RoundTrip.V3_5.A_to_B [Morse.nonempty_homeomorph_sphere_of_union_closedBall]
#rt_check RoundTrip.V3_5.B_to_A [Morse.nonempty_homeomorph_sphere_of_union_closedBall]
#rt_overlap RoundTrip.V3_5.B_to_A [Morse.nonempty_homeomorph_sphere_of_union_closedBall]

end RoundTrip.V3_5

end
