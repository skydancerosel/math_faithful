import Morse
import RoundTrip.L2.Blind.Morse_IsCriticalPath

/-! Layer-2 check of `Morse.IsCriticalPath N c` (for every variation `α` of `c`, i.e.
`Morse.IsVariation N U α B` with `α 0 = c` on `[0, 1]`, `U ⊆ ℝ` open `∋ 0`, the function
`u ↦ E(α u)` has derivative `0` at `0`) against the blind textbook definition (`c ∈ Ω(N; c 0, c 1)`,
and the same condition for the variations on `(−ε, ε)`, with smoothness on the strips between
consecutive points of `{0, 1} ∪ (B ∩ (0, 1))`).

* `agree_of`: equal for every `c ∈ Ω(N; p, q)` (Milnor's hypothesis: critical paths are elements
  of `Ω`). Open `U ∋ 0` versus `(−ε, ε)`: a variation on `U` restricts to one on some
  `(−ε, ε) ⊆ U`, and `u ↦ E(α u)` is the same function (its derivative at `0` is local);
  the strip conditions are equivalent (`strips_iff`, copied from the item `Morse_IsVariation`),
  and so are the two path spaces (`isPiecewiseSmooth_iff`, copied from `Morse_IsPiecewiseSmooth`).
* `differ`: the project does not require `c ∈ Ω`; for `c ∉ Ω` there is no variation of `c` (its
  paths lie in `Ω`) and the project condition holds vacuously, the blind one fails. Example:
  `N = ∅`. Harmless: outside the textbook's domain. -/

namespace RoundTrip.L2.Morse_IsCriticalPath

open Set
open scoped ContDiff

/-- **Break sets versus subdivisions**, for any property `Q` of closed intervals inherited by
subintervals. -/
theorem pieces_iff {Q : ℝ → ℝ → Prop} (hQ : ∀ s₀ s₁ s s', s₀ ≤ s → s' ≤ s₁ → Q s₀ s₁ → Q s s')
    {a b : ℝ} :
    (a ≤ b ∧ ∃ B : Finset ℝ, ∀ s s', a ≤ s → s < s' → s' ≤ b → (∀ x ∈ B, x ∉ Ioo s s') →
        Q s s') ↔
      ∃ k : ℕ, ∃ t : Fin (k + 1) → ℝ, StrictMono t ∧ t 0 = a ∧ t (Fin.last k) = b ∧
        ∀ i : Fin k, Q (t i.castSucc) (t i.succ) := by
  classical
  constructor
  · rintro ⟨hab, B, hB⟩
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact ⟨0, fun _ => a, fun i j hij => absurd hij (by simp [Fin.lt_def]), rfl, rfl, fun i => i.elim0⟩
    set F : Finset ℝ := insert a (insert b (B.filter (· ∈ Ioo a b))) with hF
    have hFmem : ∀ x ∈ F, x ∈ Icc a b := by
      intro x hx
      simp only [hF, Finset.mem_insert, Finset.mem_filter] at hx
      rcases hx with rfl | rfl | ⟨-, hx⟩
      · exact ⟨le_rfl, hab⟩
      · exact ⟨hab, le_rfl⟩
      · exact Ioo_subset_Icc_self hx
    have haF : a ∈ F := Finset.mem_insert_self _ _
    have hbF : b ∈ F := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    obtain ⟨k, hk⟩ : ∃ k, F.card = k + 1 :=
      Nat.exists_eq_succ_of_ne_zero (Finset.card_pos.2 ⟨a, haF⟩).ne'
    set e := F.orderEmbOfFin hk with he
    have hmem : ∀ j, e j ∈ F := fun j => Finset.orderEmbOfFin_mem F hk j
    refine ⟨k, e, e.strictMono, ?_, ?_, fun i => ?_⟩
    · have h1 := Finset.orderEmbOfFin_zero hk (Nat.succ_pos k)
      refine (h1.trans ?_)
      exact le_antisymm (F.min'_le a haF) (F.le_min' _ _ fun y hy => (hFmem y hy).1)
    · have h1 := Finset.orderEmbOfFin_last hk (Nat.succ_pos k)
      have h2 : (Fin.last k) = ⟨k + 1 - 1, by omega⟩ := Fin.ext (by simp)
      rw [h2, h1]
      exact le_antisymm (F.max'_le _ _ fun y hy => (hFmem y hy).2) (F.le_max' b hbF)
    · refine hB _ _ (hFmem _ (hmem _)).1 (e.strictMono Fin.castSucc_lt_succ)
        (hFmem _ (hmem _)).2 fun x hx hx' => ?_
      have hxF : x ∈ F := by
        refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hx, ?_⟩))
        exact ⟨(hFmem _ (hmem _)).1.trans_lt hx'.1, hx'.2.trans_le (hFmem _ (hmem _)).2⟩
      have : x ∈ Set.range e := by rw [he, Finset.range_orderEmbOfFin]; exact hxF
      obtain ⟨j, rfl⟩ := this
      have h1 := e.strictMono.lt_iff_lt.1 hx'.1
      have h2 := e.strictMono.lt_iff_lt.1 hx'.2
      rw [Fin.lt_def] at h1 h2
      simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
      omega
  · rintro ⟨k, t, ht, h0, hk, hQ'⟩
    have hab : a ≤ b := h0 ▸ hk ▸ ht.monotone (Fin.zero_le _)
    refine ⟨hab, Finset.univ.image t, fun s s' has hss' hs'b hB => ?_⟩
    set G := Finset.univ.filter (fun j => t j ≤ s) with hG
    have hGne : G.Nonempty := ⟨0, by simp [hG, h0, has]⟩
    set j := G.max' hGne
    have hjG : t j ≤ s := (Finset.mem_filter.1 (G.max'_mem hGne)).2
    have hjk : j.val < k := by
      by_contra hcon
      have : j = Fin.last k := Fin.ext (by have := j.isLt; simp; omega)
      rw [this, hk] at hjG
      linarith
    set i : Fin k := ⟨j.val, hjk⟩
    have hij : i.castSucc = j := Fin.ext rfl
    have hs1 : s < t i.succ := by
      by_contra hcon
      have hmemG : i.succ ∈ G := Finset.mem_filter.2 ⟨Finset.mem_univ _, not_lt.1 hcon⟩
      have := G.le_max' _ hmemG
      rw [Fin.le_def] at this
      simp [i, j] at this
    have hs2 : s' ≤ t i.succ := by
      by_contra hcon
      exact hB (t i.succ) (Finset.mem_image_of_mem _ (Finset.mem_univ _)) ⟨hs1, not_le.1 hcon⟩
    exact hQ _ _ _ _ (hij ▸ hjG) hs2 (hQ' i)

/-- The project's break-set formulation is the blind subdivision formulation. -/
theorem isPiecewiseSmooth_iff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (c : ℝ → V)
    (a b : ℝ) :
    Morse.IsPiecewiseSmooth c a b ↔
      ContinuousOn c (Icc a b) ∧
        ∃ k : ℕ, ∃ t : Fin (k + 1) → ℝ, StrictMono t ∧ t 0 = a ∧ t (Fin.last k) = b ∧
          ∀ i : Fin k, ContDiffOn ℝ ∞ c (Icc (t i.castSucc) (t i.succ)) := by
  have hQ : ∀ s₀ s₁ s s', s₀ ≤ s → s' ≤ s₁ → ContDiffOn ℝ ∞ c (Icc s₀ s₁) →
      ContDiffOn ℝ ∞ c (Icc s s') := fun _ _ _ _ h1 h2 h => h.mono (Icc_subset_Icc h1 h2)
  constructor
  · rintro ⟨hab, hcont, B, hB⟩
    exact ⟨hcont, (pieces_iff hQ).1 ⟨hab, B, hB⟩⟩
  · rintro ⟨hcont, h⟩
    obtain ⟨hab, B, hB⟩ := (pieces_iff hQ).2 h
    exact ⟨hab, hcont, B, hB⟩

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

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem mem_pathSpace_iff {N : Set V} {p q : V} {c : ℝ → V} :
    c ∈ Morse.pathSpace N p q ↔ c ∈ pathSpace N p q := by
  simp only [Morse.pathSpace, pathSpace, IsPiecewiseSmooth, mem_ofPred_eq, isPiecewiseSmooth_iff]
  exact ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h1, fun t ht => h2 t ht, h3, h4⟩,
    fun ⟨h1, h2, h3, h4⟩ => ⟨h1, fun t ht => h2 ht, h3, h4⟩⟩

/-- **Agreement on `Ω`**: for `c ∈ Ω(N; p, q)` the two notions agree. -/
theorem agree_of {N : Set V} {c : ℝ → V} {p q : V}
    (hc : c ∈ Morse.pathSpace N p q) : Morse.IsCriticalPath N c ↔ T N c := by
  have hc' : c ∈ Morse.pathSpace N (c 0) (c 1) := by
    obtain ⟨h1, h2, h3, h4⟩ := hc
    exact ⟨h1, h2, rfl, rfl⟩
  constructor
  · intro hP
    refine ⟨mem_pathSpace_iff.1 hc', fun ε hε α B hα => ?_⟩
    obtain ⟨h0, hmem, hends, hsmooth⟩ := hα
    have h00 : α 0 0 = c 0 := h0 0 ⟨le_rfl, zero_le_one⟩
    have h01 : α 0 1 = c 1 := h0 1 ⟨zero_le_one, le_rfl⟩
    have hQ : ∀ s₀ s₁ s s', s₀ ≤ s → s' ≤ s₁ →
        ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => α x.1 x.2) (Ioo (-ε) ε ×ˢ Icc s₀ s₁) →
        ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => α x.1 x.2) (Ioo (-ε) ε ×ˢ Icc s s') :=
      fun _ _ _ _ h1 h2 h => h.mono (prod_mono subset_rfl (Icc_subset_Icc h1 h2))
    have hvar : Morse.IsVariation N (Ioo (-ε) ε) α B :=
      { isOpen := isOpen_Ioo
        zero_mem := ⟨by linarith, hε⟩
        mem := hmem
        start := fun u hu => (hends u hu).1.trans h00.symm
        finish := fun u hu => (hends u hu).2.trans h01.symm
        smooth := (strips_iff B hQ).2 hsmooth }
    exact hP _ α B hvar h0
  · rintro ⟨-, hT⟩ U α B hα hαc
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hα.isOpen 0 hα.zero_mem
    have hsub : Ioo (-ε) ε ⊆ U := by
      intro u hu
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      exact hu
    have hQ : ∀ s₀ s₁ s s', s₀ ≤ s → s' ≤ s₁ →
        ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => α x.1 x.2) (Ioo (-ε) ε ×ˢ Icc s₀ s₁) →
        ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => α x.1 x.2) (Ioo (-ε) ε ×ˢ Icc s s') :=
      fun _ _ _ _ h1 h2 h => h.mono (prod_mono subset_rfl (Icc_subset_Icc h1 h2))
    have h00 : α 0 0 = c 0 := hαc 0 ⟨le_rfl, zero_le_one⟩
    have h01 : α 0 1 = c 1 := hαc 1 ⟨zero_le_one, le_rfl⟩
    refine hT ε hε α B ⟨hαc, fun u hu t ht => hα.mem u (hsub hu) t ht,
      fun u hu => ⟨(hα.start u (hsub hu)).trans h00, (hα.finish u (hsub hu)).trans h01⟩,
      (strips_iff B hQ).1 fun s s' h1 h2 h3 h4 => ?_⟩
    exact (hα.smooth s s' h1 h2 h3 h4).mono (prod_mono hsub subset_rfl)

/-- **Difference off `Ω`**: with `N = ∅` the project notion holds vacuously (there is no
variation), the blind one fails (`c ∉ Ω`). -/
theorem differ : Morse.IsCriticalPath (∅ : Set ℝ) (fun _ => 0) ∧ ¬ T (∅ : Set ℝ) (fun _ => 0) := by
  refine ⟨fun U α B hα _ => ?_, fun h => ?_⟩
  · exact absurd (hα.mem 0 hα.zero_mem 0 ⟨le_rfl, zero_le_one⟩) (notMem_empty _)
  · exact notMem_empty _ (h.1.2.1 (⟨le_rfl, zero_le_one⟩ : (0 : ℝ) ∈ Icc 0 1))

end RoundTrip.L2.Morse_IsCriticalPath
