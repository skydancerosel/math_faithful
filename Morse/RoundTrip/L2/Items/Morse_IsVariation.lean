import Morse
import RoundTrip.L2.Blind.Morse_IsVariation

/-! Layer-2 check of `Morse.IsVariation N U α B` (`U` open, `0 ∈ U`, `α u t ∈ N` on
`U × [0, 1]`, end points `α u 0 = α 0 0`, `α u 1 = α 0 1`, and `(u, t) ↦ α u t` `C^∞` on every
closed strip `U × [s, t] ⊆ U × [0, 1]` whose interior misses `B`) against the blind textbook
definition (the same, with smoothness on the strips `U × [s, s']` between consecutive points of
`{0, 1} ∪ (B ∩ (0, 1))`).

Equal for all arguments. `strips_iff`: a strip between consecutive points misses `B` in its
interior; conversely a break-free `[s, s'] ⊆ [0, 1]` lies between the last point `≤ s` and the
first point `≥ s'`, which are consecutive. -/

namespace RoundTrip.L2.Morse_IsVariation

open Set
open scoped ContDiff

theorem mem_pts {B : Finset ℝ} {x : ℝ} : x ∈ pts B ↔ x = 0 ∨ x = 1 ∨ (x ∈ B ∧ x ∈ Ioo 0 1) := by
  simp [pts, or_assoc]

theorem pts_subset {B : Finset ℝ} {x : ℝ} (hx : x ∈ pts B) : x ∈ Icc (0 : ℝ) 1 := by
  rcases mem_pts.1 hx with rfl | rfl | ⟨-, h⟩
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨zero_le_one, le_rfl⟩
  · exact Ioo_subset_Icc_self h

/-- **Break sets versus consecutive subdivision points**, for any property `Q` of closed
intervals inherited by subintervals. -/
theorem strips_iff (B : Finset ℝ) {Q : ℝ → ℝ → Prop}
    (hQ : ∀ s₀ s₁ s s', s₀ ≤ s → s' ≤ s₁ → Q s₀ s₁ → Q s s') :
    (∀ s s', 0 ≤ s → s < s' → s' ≤ 1 → (∀ x ∈ B, x ∉ Ioo s s') → Q s s') ↔
      ∀ s ∈ pts B, ∀ s' ∈ pts B, s < s' → (∀ r ∈ pts B, r ∉ Ioo s s') → Q s s' := by
  classical
  constructor
  · intro h s hs s' hs' hss' hr
    exact h s s' (pts_subset hs).1 hss' (pts_subset hs').2 fun x hx hx' =>
      hr x (mem_pts.2 (Or.inr (Or.inr ⟨hx, (pts_subset hs).1.trans_lt hx'.1,
        hx'.2.trans_le (pts_subset hs').2⟩))) hx'
  · intro h s s' hs hss' hs' hB
    set F : Finset ℝ := insert 0 (insert 1 (B.filter (· ∈ Ioo (0 : ℝ) 1))) with hF
    have hFmem : ∀ x, x ∈ F ↔ x ∈ pts B := fun x => by
      simp [hF, mem_pts]
    set G₀ := F.filter (· ≤ s)
    set G₁ := F.filter (s' ≤ ·)
    have hG₀ : G₀.Nonempty := ⟨0, Finset.mem_filter.2 ⟨(hFmem 0).2 (mem_pts.2 (Or.inl rfl)), hs⟩⟩
    have hG₁ : G₁.Nonempty := ⟨1, Finset.mem_filter.2
      ⟨(hFmem 1).2 (mem_pts.2 (Or.inr (Or.inl rfl))), hs'⟩⟩
    have h0 := Finset.mem_filter.1 (G₀.max'_mem hG₀)
    have h1 := Finset.mem_filter.1 (G₁.min'_mem hG₁)
    refine hQ _ _ s s' h0.2 h1.2 (h _ ((hFmem _).1 h0.1) _ ((hFmem _).1 h1.1)
      (h0.2.trans_lt (hss'.trans_le h1.2)) fun r hr hr' => ?_)
    by_cases hrs : r ≤ s
    · exact absurd (G₀.le_max' r (Finset.mem_filter.2 ⟨(hFmem r).2 hr, hrs⟩)) (not_le.2 hr'.1)
    by_cases hrs' : s' ≤ r
    · exact absurd (G₁.min'_le r (Finset.mem_filter.2 ⟨(hFmem r).2 hr, hrs'⟩)) (not_le.2 hr'.2)
    rw [not_le] at hrs hrs'
    rcases mem_pts.1 hr with rfl | rfl | ⟨hrB, -⟩
    · linarith
    · linarith
    · exact hB r hrB ⟨hrs, hrs'⟩

/-- **Agreement**: equal for all arguments. -/
theorem agree {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (N : Set V) {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] (U : Set P) (α : P → ℝ → V) (B : Finset ℝ) :
    Morse.IsVariation N U α B ↔ T N U α B := by
  have hQ : ∀ s₀ s₁ s s', s₀ ≤ s → s' ≤ s₁ →
      ContDiffOn ℝ ∞ (fun x : P × ℝ => α x.1 x.2) (U ×ˢ Icc s₀ s₁) →
      ContDiffOn ℝ ∞ (fun x : P × ℝ => α x.1 x.2) (U ×ˢ Icc s s') :=
    fun _ _ _ _ h1 h2 h => h.mono (prod_mono subset_rfl (Icc_subset_Icc h1 h2))
  constructor
  · intro h
    exact ⟨h.isOpen, h.zero_mem, h.mem, fun u hu => ⟨h.start u hu, h.finish u hu⟩,
      (strips_iff B hQ).1 h.smooth⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, fun u hu => (h4 u hu).1, fun u hu => (h4 u hu).2,
      (strips_iff B hQ).2 h5⟩

end RoundTrip.L2.Morse_IsVariation
