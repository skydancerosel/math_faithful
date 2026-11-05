import Morse
import RoundTrip.L2.Blind.Morse_pathSpace

/-! Layer-2 check of `Morse.pathSpace N p q` (`Ω(N; p, q)`: maps `ℝ → V`, `Morse.IsPiecewiseSmooth`
on `[0, 1]`, values in `N` on `[0, 1]`, `c 0 = p`, `c 1 = q`) against the blind textbook
definition (the same, with piecewise smoothness via a strictly increasing subdivision).

Equal for all `N`, `p`, `q`: the only difference is the formulation of piecewise smoothness
(finite break set versus subdivision), equivalent by `isPiecewiseSmooth_iff` (copied from the
layer-2 item `Morse_IsPiecewiseSmooth`). -/

namespace RoundTrip.L2.Morse_pathSpace

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

/-- **Agreement**: equal for all `N`, `p`, `q`. -/
theorem agree {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (N : Set V) (p q : V) :
    Morse.pathSpace N p q = T N p q := by
  ext c
  simp only [Morse.pathSpace, T, IsPiecewiseSmooth, mem_ofPred_eq, isPiecewiseSmooth_iff]
  exact ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h1, fun t ht => h2 t ht, h3, h4⟩,
    fun ⟨h1, h2, h3, h4⟩ => ⟨h1, fun t ht => h2 ht, h3, h4⟩⟩

end RoundTrip.L2.Morse_pathSpace
