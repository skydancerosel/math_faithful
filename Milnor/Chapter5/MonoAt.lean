import Milnor.Appendix.OneManifold

/-!
# The local monotonicity sign of a real function

For `h : ℝ → ℝ` and an interval `s ∋ t₀`, `monoAt h s t₀` is `1` if `h` is strictly increasing on
`s` near `t₀` and `-1` otherwise.  When `h` is continuous and injective near `t₀` it is strictly
monotone there (Appendix), so `-1` means strictly decreasing.  We record how the sign behaves
under composition with a monotone map, how it is locally constant, and its value at an endpoint
of `s` which is a minimum of `h`.
-/

open Set Filter Topology

namespace Milnor

/-- `1` if `h` is strictly increasing on `s` near `t₀`, `-1` otherwise. -/
noncomputable def monoAt (h : ℝ → ℝ) (s : Set ℝ) (t₀ : ℝ) : ℤ :=
  open Classical in
  if ∃ δ > 0, StrictMonoOn h (s ∩ Ioo (t₀ - δ) (t₀ + δ)) then 1 else -1

variable {h : ℝ → ℝ} {s : Set ℝ} {t₀ : ℝ}

theorem monoAt_eq_one_iff :
    monoAt h s t₀ = 1 ↔ ∃ δ > 0, StrictMonoOn h (s ∩ Ioo (t₀ - δ) (t₀ + δ)) := by
  unfold monoAt; split_ifs with hm <;> simp [hm]

theorem monoAt_eq_neg_one_iff_not :
    monoAt h s t₀ = -1 ↔ ¬ ∃ δ > 0, StrictMonoOn h (s ∩ Ioo (t₀ - δ) (t₀ + δ)) := by
  unfold monoAt; split_ifs with hm <;> simp [hm]

theorem monoAt_mem : monoAt h s t₀ = 1 ∨ monoAt h s t₀ = -1 := by
  unfold monoAt; split_ifs <;> simp

theorem monoAt_ne_zero : monoAt h s t₀ ≠ 0 := by
  rcases monoAt_mem (h := h) (s := s) (t₀ := t₀) with h1 | h1 <;> rw [h1] <;> decide

theorem monoAt_mul_self : monoAt h s t₀ * monoAt h s t₀ = 1 := by
  rcases monoAt_mem (h := h) (s := s) (t₀ := t₀) with h1 | h1 <;> rw [h1] <;> decide

/-- A nontrivial interval containing `t₀` meets every neighbourhood of `t₀` in a nontrivial set. -/
theorem nontrivial_inter_Ioo (hs : s.OrdConnected) (hsn : s.Nontrivial) (ht₀ : t₀ ∈ s) {δ : ℝ}
    (hδ : 0 < δ) : (s ∩ Ioo (t₀ - δ) (t₀ + δ)).Nontrivial := by
  obtain ⟨a, ha, b, hb, hab⟩ := hsn
  have hex : ∃ t₁ ∈ s, t₁ ≠ t₀ := by
    by_cases h : a = t₀
    · exact ⟨b, hb, fun hb' => hab (h.trans hb'.symm)⟩
    · exact ⟨a, ha, h⟩
  obtain ⟨t₁, ht₁, hne⟩ := hex
  have hself : t₀ ∈ s ∩ Ioo (t₀ - δ) (t₀ + δ) := ⟨ht₀, by constructor <;> linarith⟩
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hu : max t₁ (t₀ - δ / 2) < t₀ := max_lt hlt (by linarith)
    refine ⟨t₀, hself, max t₁ (t₀ - δ / 2), ⟨?_, ?_⟩, hu.ne'⟩
    · exact hs.out ht₁ ht₀ ⟨le_max_left _ _, hu.le⟩
    · exact ⟨lt_of_lt_of_le (by linarith) (le_max_right _ _), by linarith⟩
  · have hu : t₀ < min t₁ (t₀ + δ / 2) := lt_min hgt (by linarith)
    refine ⟨t₀, hself, min t₁ (t₀ + δ / 2), ⟨?_, ?_⟩, hu.ne⟩
    · exact hs.out ht₀ ht₁ ⟨hu.le, min_le_left _ _⟩
    · exact ⟨by linarith, lt_of_le_of_lt (min_le_right _ _) (by linarith)⟩

theorem inter_Ioo_ordConnected (hs : s.OrdConnected) {a b : ℝ} : (s ∩ Ioo a b).OrdConnected :=
  hs.inter ordConnected_Ioo

/-- Strictly increasing and strictly decreasing on a nontrivial set are incompatible. -/
theorem not_strictMonoOn_and_strictAntiOn {C : Set ℝ} (hC : C.Nontrivial)
    (h1 : StrictMonoOn h C) (h2 : StrictAntiOn h C) : False := by
  obtain ⟨a, ha, b, hb, hab⟩ := hC
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · exact lt_asymm (h1 ha hb hlt) (h2 ha hb hlt)
  · exact lt_asymm (h1 hb ha hlt) (h2 hb ha hlt)

theorem monoAt_eq_neg_one_of_strictAntiOn (hs : s.OrdConnected) (hsn : s.Nontrivial) (ht₀ : t₀ ∈ s)
    {δ : ℝ} (hδ : 0 < δ) (hanti : StrictAntiOn h (s ∩ Ioo (t₀ - δ) (t₀ + δ))) :
    monoAt h s t₀ = -1 := by
  rw [monoAt_eq_neg_one_iff_not]
  rintro ⟨δ', hδ', hmono⟩
  have hsub1 : s ∩ Ioo (t₀ - min δ δ') (t₀ + min δ δ') ⊆ s ∩ Ioo (t₀ - δ) (t₀ + δ) :=
    inter_subset_inter_right _ (Ioo_subset_Ioo (by linarith [min_le_left δ δ'])
      (by linarith [min_le_left δ δ']))
  have hsub2 : s ∩ Ioo (t₀ - min δ δ') (t₀ + min δ δ') ⊆ s ∩ Ioo (t₀ - δ') (t₀ + δ') :=
    inter_subset_inter_right _ (Ioo_subset_Ioo (by linarith [min_le_right δ δ'])
      (by linarith [min_le_right δ δ']))
  exact not_strictMonoOn_and_strictAntiOn (nontrivial_inter_Ioo hs hsn ht₀ (lt_min hδ hδ'))
    (hmono.mono hsub2) (hanti.mono hsub1)

/-- If `h` is continuous and injective on `s` near `t₀`, then `monoAt = -1` means strictly
decreasing near `t₀`. -/
theorem exists_strictAntiOn_of_monoAt_eq_neg_one (hs : s.OrdConnected) (hsn : s.Nontrivial)
    (ht₀ : t₀ ∈ s) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hcont : ContinuousOn h (s ∩ Ioo (t₀ - δ₀) (t₀ + δ₀)))
    (hinj : InjOn h (s ∩ Ioo (t₀ - δ₀) (t₀ + δ₀))) (hm : monoAt h s t₀ = -1) :
    ∃ δ > 0, StrictAntiOn h (s ∩ Ioo (t₀ - δ) (t₀ + δ)) := by
  rw [monoAt_eq_neg_one_iff_not] at hm
  rcases OneManifold.strictMonoOn_or_strictAntiOn_of_ordConnected (inter_Ioo_ordConnected hs)
    (nontrivial_inter_Ioo hs hsn ht₀ hδ₀) hcont hinj with h1 | h1
  · exact absurd ⟨δ₀, hδ₀, h1⟩ hm
  · exact ⟨δ₀, hδ₀, h1⟩

/-- The dichotomy near `t₀` for a continuous injective `h`. -/
theorem strictMonoOn_or_strictAntiOn_near (hs : s.OrdConnected) (hsn : s.Nontrivial)
    (ht₀ : t₀ ∈ s) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hcont : ContinuousOn h (s ∩ Ioo (t₀ - δ₀) (t₀ + δ₀)))
    (hinj : InjOn h (s ∩ Ioo (t₀ - δ₀) (t₀ + δ₀))) :
    StrictMonoOn h (s ∩ Ioo (t₀ - δ₀) (t₀ + δ₀)) ∨ StrictAntiOn h (s ∩ Ioo (t₀ - δ₀) (t₀ + δ₀)) :=
  OneManifold.strictMonoOn_or_strictAntiOn_of_ordConnected (inter_Ioo_ordConnected hs)
    (nontrivial_inter_Ioo hs hsn ht₀ hδ₀) hcont hinj

theorem Ioo_half_subset {t t₀ δ : ℝ} (ht : |t - t₀| < δ / 2) :
    Ioo (t - δ / 2) (t + δ / 2) ⊆ Ioo (t₀ - δ) (t₀ + δ) := by
  rw [abs_lt] at ht
  exact Ioo_subset_Ioo (by linarith) (by linarith)

/-- **Locality**: the sign is constant near `t₀` once `h` is strictly monotone near `t₀`. -/
theorem monoAt_eq_of_near (hs : s.OrdConnected) (hsn : s.Nontrivial) (ht₀ : t₀ ∈ s) {δ : ℝ}
    (hδ : 0 < δ)
    (hor : StrictMonoOn h (s ∩ Ioo (t₀ - δ) (t₀ + δ)) ∨ StrictAntiOn h (s ∩ Ioo (t₀ - δ) (t₀ + δ)))
    {t : ℝ} (ht : t ∈ s) (htδ : |t - t₀| < δ / 2) : monoAt h s t = monoAt h s t₀ := by
  have hsub : s ∩ Ioo (t - δ / 2) (t + δ / 2) ⊆ s ∩ Ioo (t₀ - δ) (t₀ + δ) :=
    inter_subset_inter_right _ (Ioo_half_subset htδ)
  rcases hor with h1 | h1
  · rw [monoAt_eq_one_iff.2 ⟨δ, hδ, h1⟩, monoAt_eq_one_iff.2 ⟨δ / 2, by linarith, h1.mono hsub⟩]
  · rw [monoAt_eq_neg_one_of_strictAntiOn hs hsn ht₀ hδ h1,
      monoAt_eq_neg_one_of_strictAntiOn hs hsn ht (by linarith) (h1.mono hsub)]

/-- The sign only depends on the function near `t₀`. -/
theorem monoAt_congr (hs : s.OrdConnected) (hsn : s.Nontrivial) (ht₀ : t₀ ∈ s) {δ : ℝ}
    (hδ : 0 < δ) {h₁ h₂ : ℝ → ℝ} (heq : EqOn h₁ h₂ (s ∩ Ioo (t₀ - δ) (t₀ + δ)))
    (hor : StrictMonoOn h₁ (s ∩ Ioo (t₀ - δ) (t₀ + δ)) ∨
      StrictAntiOn h₁ (s ∩ Ioo (t₀ - δ) (t₀ + δ))) :
    monoAt h₁ s t₀ = monoAt h₂ s t₀ := by
  rcases hor with h1 | h1
  · have h2 : StrictMonoOn h₂ (s ∩ Ioo (t₀ - δ) (t₀ + δ)) := fun a ha b hb hab => by
      rw [← heq ha, ← heq hb]; exact h1 ha hb hab
    rw [monoAt_eq_one_iff.2 ⟨δ, hδ, h1⟩, monoAt_eq_one_iff.2 ⟨δ, hδ, h2⟩]
  · have h2 : StrictAntiOn h₂ (s ∩ Ioo (t₀ - δ) (t₀ + δ)) := fun a ha b hb hab => by
      rw [← heq ha, ← heq hb]; exact h1 ha hb hab
    rw [monoAt_eq_neg_one_of_strictAntiOn hs hsn ht₀ hδ h1,
      monoAt_eq_neg_one_of_strictAntiOn hs hsn ht₀ hδ h2]

/-- **Composition** with a strictly increasing map preserves the sign. -/
theorem monoAt_comp_of_strictMonoOn (hs : s.OrdConnected) (hsn : s.Nontrivial) (ht₀ : t₀ ∈ s)
    {δ : ℝ} (hδ : 0 < δ)
    (hor : StrictMonoOn h (s ∩ Ioo (t₀ - δ) (t₀ + δ)) ∨ StrictAntiOn h (s ∩ Ioo (t₀ - δ) (t₀ + δ)))
    {k : ℝ → ℝ} {D : Set ℝ} (hk : StrictMonoOn k D) (hD : MapsTo h (s ∩ Ioo (t₀ - δ) (t₀ + δ)) D) :
    monoAt (k ∘ h) s t₀ = monoAt h s t₀ := by
  rcases hor with h1 | h1
  · rw [monoAt_eq_one_iff.2 ⟨δ, hδ, h1⟩, monoAt_eq_one_iff.2 ⟨δ, hδ, hk.comp h1 hD⟩]
  · rw [monoAt_eq_neg_one_of_strictAntiOn hs hsn ht₀ hδ h1,
      monoAt_eq_neg_one_of_strictAntiOn hs hsn ht₀ hδ (hk.comp_strictAntiOn h1 hD)]

/-- **Composition** with a strictly decreasing map reverses the sign. -/
theorem monoAt_comp_of_strictAntiOn (hs : s.OrdConnected) (hsn : s.Nontrivial) (ht₀ : t₀ ∈ s)
    {δ : ℝ} (hδ : 0 < δ)
    (hor : StrictMonoOn h (s ∩ Ioo (t₀ - δ) (t₀ + δ)) ∨ StrictAntiOn h (s ∩ Ioo (t₀ - δ) (t₀ + δ)))
    {k : ℝ → ℝ} {D : Set ℝ} (hk : StrictAntiOn k D) (hD : MapsTo h (s ∩ Ioo (t₀ - δ) (t₀ + δ)) D) :
    monoAt (k ∘ h) s t₀ = -monoAt h s t₀ := by
  rcases hor with h1 | h1
  · rw [monoAt_eq_one_iff.2 ⟨δ, hδ, h1⟩,
      monoAt_eq_neg_one_of_strictAntiOn hs hsn ht₀ hδ (hk.comp_strictMonoOn h1 hD)]
  · rw [monoAt_eq_neg_one_of_strictAntiOn hs hsn ht₀ hδ h1,
      monoAt_eq_one_iff.2 ⟨δ, hδ, hk.comp h1 hD⟩]
    decide

/-- At a left endpoint which is a minimum, a continuous injective `h` is increasing. -/
theorem monoAt_eq_one_of_left_min (hs : s.OrdConnected) (hsn : s.Nontrivial) (ht₀ : t₀ ∈ s)
    {δ : ℝ} (hδ : 0 < δ) (hcont : ContinuousOn h (s ∩ Ioo (t₀ - δ) (t₀ + δ)))
    (hinj : InjOn h (s ∩ Ioo (t₀ - δ) (t₀ + δ))) (hmin : ∀ t ∈ s, h t₀ ≤ h t)
    (hleft : ∀ t ∈ s, t₀ ≤ t) : monoAt h s t₀ = 1 := by
  rcases strictMonoOn_or_strictAntiOn_near hs hsn ht₀ hδ hcont hinj with h1 | h1
  · exact monoAt_eq_one_iff.2 ⟨δ, hδ, h1⟩
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := nontrivial_inter_Ioo hs hsn ht₀ hδ
    have hself : t₀ ∈ s ∩ Ioo (t₀ - δ) (t₀ + δ) := ⟨ht₀, by constructor <;> linarith⟩
    have key : ∀ t ∈ s ∩ Ioo (t₀ - δ) (t₀ + δ), t ≠ t₀ → False := fun t ht hne => by
      have hlt : t₀ < t := lt_of_le_of_ne (hleft t ht.1) hne.symm
      exact absurd (h1 hself ht hlt) (not_lt.2 (hmin t ht.1))
    by_cases hat : a = t₀
    · exact key b hb (fun hbt => hab (hat.trans hbt.symm))
    · exact key a ha hat

/-- At a right endpoint which is a minimum, a continuous injective `h` is decreasing. -/
theorem monoAt_eq_neg_one_of_right_min (hs : s.OrdConnected) (hsn : s.Nontrivial) (ht₀ : t₀ ∈ s)
    {δ : ℝ} (hδ : 0 < δ) (hcont : ContinuousOn h (s ∩ Ioo (t₀ - δ) (t₀ + δ)))
    (hinj : InjOn h (s ∩ Ioo (t₀ - δ) (t₀ + δ))) (hmin : ∀ t ∈ s, h t₀ ≤ h t)
    (hright : ∀ t ∈ s, t ≤ t₀) : monoAt h s t₀ = -1 := by
  rcases strictMonoOn_or_strictAntiOn_near hs hsn ht₀ hδ hcont hinj with h1 | h1
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := nontrivial_inter_Ioo hs hsn ht₀ hδ
    have hself : t₀ ∈ s ∩ Ioo (t₀ - δ) (t₀ + δ) := ⟨ht₀, by constructor <;> linarith⟩
    have key : ∀ t ∈ s ∩ Ioo (t₀ - δ) (t₀ + δ), t ≠ t₀ → False := fun t ht hne => by
      have hlt : t < t₀ := lt_of_le_of_ne (hright t ht.1) hne
      exact absurd (h1 ht hself hlt) (not_lt.2 (hmin t ht.1))
    by_cases hat : a = t₀
    · exact key b hb (fun hbt => hab (hat.trans hbt.symm))
    · exact key a ha hat
  · exact monoAt_eq_neg_one_of_strictAntiOn hs hsn ht₀ hδ h1

/-- The `±1` algebra used for well-definedness along an arc. -/
theorem pm_mul_eq {a b c d : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) (hc : c = 1 ∨ c = -1)
    (hd : d = 1 ∨ d = -1) (h : a * c = b * d) : a * b = c * d := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hd with rfl | rfl <;> omega

end Milnor
