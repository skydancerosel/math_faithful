import Morse
import RoundTrip.Check
import RoundTrip.Blind.VA_5

/-! # Round trip for VA_5 (Milnor, Appendix p. 152: the truncations `X^n_Σ`, (T2))

`A` is the conjunction of the types, universes at `0`, of `Morse.isClosed_truncation`,
`Morse.isHomotopyEquiv_truncIncl` (`x ↦ (x, n)` is a homotopy equivalence `X_n → X^n_Σ`),
`Morse.isHomotopyEquiv_truncProj` (`(x, τ) ↦ x` is one `X^n_Σ → X_n`) and
`Morse.level_le_of_stripMap` (a map of telescope shape — strip `n` to levels `≤ n + 1`, bottom
`X_n × {n}` to levels `≤ n` — carries `X^m_Σ` to levels `≤ m`).

`B` = (a) `X^n_Σ = X₀×[0,1] ∪ ⋯ ∪ X_{n-1}×[n-1,n] ∪ X_n×[n]`; (b) `X_n × [n]` is a STRONG
deformation retract of `X^n_Σ` (in `X × ℝ`); (c) Milnor's `G f_Σ` carries `X^n_Σ` into itself.

* `A ⇒ B`: (c) is `A`'s `level_le_of_stripMap` for `F = G f_Σ` (transported along the identity
  homeomorphism `tel S ≃ₜ telescope S`), with the strip bounds from the elementary estimate
  `level(G w) ≤ ⌈τ(w)⌉`; (a) and (b) are proved outright (`A` only states a homotopy
  equivalence, not the strong deformation retraction, and does not describe the set).
* `B ⇒ A`: both homotopy-equivalence clauses from `B`(b) (the end `H₁` of the strong deformation
  retraction gives a homotopy inverse `ρ` of `x ↦ (x, n)` with `ρ ∘ ι = id`); closedness of the
  truncation and the general `level_le_of_stripMap` (of which `B`(c) is one instance) are proved
  outright. -/

namespace RoundTrip.VA_5

open Set
open scoped unitInterval

/-- `A`: the four listed theorems, universes at `0`. -/
def A : Prop :=
  (type_of% @Morse.isClosed_truncation.{0}) ∧ (type_of% @Morse.isHomotopyEquiv_truncIncl.{0}) ∧
    (type_of% @Morse.isHomotopyEquiv_truncProj.{0}) ∧
      (type_of% @Morse.level_le_of_stripMap.{0, 0})

theorem A_holds : A :=
  ⟨Morse.isClosed_truncation, Morse.isHomotopyEquiv_truncIncl, Morse.isHomotopyEquiv_truncProj,
    Morse.level_le_of_stripMap⟩

/-! ### Glue -/

section Glue

variable {X : Type} [TopologicalSpace X]

omit [TopologicalSpace X] in
theorem tel_eq_telescope (S : ℕ → Set X) : tel S = Morse.telescope S := by
  ext z
  simp only [tel, Morse.telescope, mem_iUnion, mem_prod, mem_Icc]; rfl

/-- The identity homeomorphism `tel S ≃ₜ telescope S`. -/
noncomputable def telHomeo (S : ℕ → Set X) : ↥(tel S) ≃ₜ ↥(Morse.telescope S) :=
  Homeomorph.setCongr (tel_eq_telescope S)

omit [TopologicalSpace X] in
theorem mem_tel_of_le {S : ℕ → Set X} (hS : Monotone S) {x : X} {τ τ' : ℝ}
    (h : (x, τ) ∈ tel S) (hle : τ ≤ τ') : (x, τ') ∈ tel S := by
  rw [tel_eq_telescope] at h ⊢
  exact Morse.mem_telescope_of_le hS h hle

omit [TopologicalSpace X] in
theorem nonneg_of_mem_tel {S : ℕ → Set X} {z : X × ℝ} (hz : z ∈ tel S) : 0 ≤ z.2 := by
  obtain ⟨i, -, hi, -⟩ := hz
  exact le_trans (Nat.cast_nonneg i) hi

end Glue

/-! ### `B`(a), `B`(b) hold outright -/

theorem partA {X : Type} (S : ℕ → Set X) (hS : Monotone S) (n : ℕ) :
    truncSet S n = (⋃ i ∈ Finset.range n, S i ×ˢ Set.Icc (i : ℝ) (i + 1)) ∪ (S n ×ˢ {(n : ℝ)}) := by
  ext ⟨x, τ⟩
  simp only [truncSet, mem_ofPred_eq, mem_union, mem_iUnion, mem_prod, mem_Icc, Finset.mem_range,
    mem_singleton_iff, exists_prop]
  constructor
  · rintro ⟨hz, hτ⟩
    have hx := mem_floor hS hz
    have h0 := nonneg_of_mem_tel hz
    rcases eq_or_lt_of_le hτ with h | h
    · right
      refine ⟨?_, h⟩
      have : ⌊τ⌋₊ = n := by rw [h]; exact Nat.floor_natCast n
      rwa [this] at hx
    · left
      have hk : ⌊τ⌋₊ < n := Nat.floor_lt h0 |>.2 h
      exact ⟨⌊τ⌋₊, hk, hx, Nat.floor_le h0, (Nat.lt_floor_add_one τ).le⟩
  · rintro (⟨i, hi, hx, h1, h2⟩ | ⟨hx, rfl⟩)
    · refine ⟨⟨i, hx, h1, h2⟩, le_trans h2 ?_⟩
      exact_mod_cast hi
    · exact ⟨⟨n, hx, le_rfl, by linarith⟩, le_rfl⟩

theorem partB {X : Type} [TopologicalSpace X] (S : ℕ → Set X) (hS : Monotone S) (n : ℕ) :
    IsDefRetract (truncSet S n) (S n ×ˢ {(n : ℝ)}) := by
  refine ⟨?_, fun s z => (z.1, (1 - (s : ℝ)) * z.2 + s * n), ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨x, τ⟩ ⟨hx, rfl⟩
    exact ⟨⟨n, hx, le_rfl, by simp only; linarith⟩, le_rfl⟩
  · refine Continuous.continuousOn ?_
    exact (continuous_fst.comp continuous_snd).prodMk
      (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (continuous_snd.comp continuous_snd)).add
        ((continuous_subtype_val.comp continuous_fst).mul continuous_const))
  · intro z _
    simp
  · rintro z ⟨hz, hτ⟩
    refine ⟨hS (Nat.floor_le_of_le hτ) (mem_floor hS hz), ?_⟩
    simp
  · rintro z ⟨hz, hτ⟩ s
    have h1 := s.2.1
    have h2 := s.2.2
    refine ⟨mem_tel_of_le hS hz (by nlinarith), ?_⟩
    change (1 - (s : ℝ)) * z.2 + s * n ≤ n
    nlinarith
  · rintro ⟨x, τ⟩ ⟨-, h⟩ s
    simp only [mem_singleton_iff] at h
    subst h
    simp only [Prod.mk.injEq, true_and]
    ring

/-! ### Milnor's `G` -/

section G

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem Gmap_mem {f : C(X, Y)} {S : ℕ → Set X} {T : ℕ → Set Y} (D : Case2 f S T) (w : ↥(tel T)) :
    Gmap D w ∈ tel S := by
  have h0 := nonneg_of_mem_tel w.2
  have hk : (⌊w.1.2⌋₊ : ℝ) ≤ w.1.2 := Nat.floor_le h0
  unfold Gmap
  split_ifs with h
  · exact ⟨⌊w.1.2⌋₊, (D.g _ _).2, by simp only; linarith, by simp only; linarith⟩
  · exact ⟨⌊w.1.2⌋₊ + 1, (D.H _ _).2, by push_cast; exact le_rfl, by push_cast; linarith⟩

/-- The level of `G(w)` is at most `⌈τ(w)⌉`. -/
theorem Gmap_snd_le {f : C(X, Y)} {S : ℕ → Set X} {T : ℕ → Set Y} (D : Case2 f S T)
    (w : ↥(tel T)) : (Gmap D w).2 ≤ ⌈w.1.2⌉₊ := by
  have h0 := nonneg_of_mem_tel w.2
  have hk : (⌊w.1.2⌋₊ : ℝ) ≤ w.1.2 := Nat.floor_le h0
  rcases eq_or_lt_of_le hk with heq | hlt
  · have hh : w.1.2 - ⌊w.1.2⌋₊ ≤ 1 / 2 := by rw [← heq]; norm_num
    unfold Gmap
    rw [if_pos hh]
    have := Nat.le_ceil w.1.2
    simp only
    linarith
  · have hc : (⌊w.1.2⌋₊ : ℝ) + 1 ≤ ⌈w.1.2⌉₊ := by
      have := Nat.lt_ceil.2 hlt
      exact_mod_cast this
    unfold Gmap
    split_ifs with h
    · simp only; linarith
    · simp only; linarith

end G

/-! ### `A ⇒ B` -/

/-- `A ⇒ B`: (c) from `A`'s `level_le_of_stripMap`; (a), (b) outright. -/
theorem A_to_B : A → B := by
  rintro ⟨-, -, -, hlev⟩
  refine ⟨fun X _ S hS n => ⟨partA S hS n, partB S hS n⟩, ?_⟩
  intro X Y _ _ f S T D n z hz
  refine ⟨Gmap_mem D _, ?_⟩
  have key := hlev (X := X) (A := S) D.hS (Z := X × ℝ) Prod.snd
    (fun w => Gmap D (fSig f D.hf ((telHomeo S).symm w)))
    (fun k x t => by
      refine le_trans (Gmap_snd_le D _) ?_
      have : ((fSig f D.hf ((telHomeo S).symm (Morse.stripMap S k (x, t)))).1.2) = k + t := rfl
      rw [this]
      exact_mod_cast Nat.ceil_le.2 (by push_cast; linarith [t.2.2]))
    (fun k x => by
      refine le_trans (Gmap_snd_le D _) ?_
      have : ((fSig f D.hf ((telHomeo S).symm (Morse.stripMap S k (x, 0)))).1.2) = k := by
        change (k : ℝ) + ((0 : I) : ℝ) = k
        simp
      rw [this, Nat.ceil_natCast])
    (m := n) (z := telHomeo S z) hz
  simpa using key

/-! ### `B ⇒ A` -/

/-- From `B`(b): the inclusion `X_n → X^n_Σ` and the projection `X^n_Σ → X_n` are homotopy
equivalences. -/
theorem he_of_dr {X : Type} [TopologicalSpace X] {S : ℕ → Set X} (hS : Monotone S) (n : ℕ)
    (hdr : IsDefRetract (truncSet S n) (S n ×ˢ {(n : ℝ)})) :
    Morse.IsHomotopyEquiv (Morse.truncIncl S n) ∧ Morse.IsHomotopyEquiv (Morse.truncProj hS n) := by
  obtain ⟨-, H, hHc, hH0, hH1, hHmem, hHfix⟩ := hdr
  have hT := tel_eq_telescope S
  have hTT : ∀ y : X × ℝ, y ∈ tel S → y ∈ Morse.telescope S := fun y hy => hT ▸ hy
  have hw : ∀ w : Morse.truncation S n, ((w : Morse.telescope S) : X × ℝ) ∈ truncSet S n :=
    fun w => ⟨by rw [hT]; exact w.1.2, w.2⟩
  have hFc : Continuous fun q : I × Morse.truncation S n => H q.1 ((q.2 : Morse.telescope S) :
      X × ℝ) :=
    hHc.comp_continuous (continuous_fst.prodMk
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)))
      fun q => ⟨mem_univ _, hw q.2⟩
  let F : C(I × Morse.truncation S n, Morse.truncation S n) :=
    ⟨fun q => ⟨⟨H q.1 q.2, hTT _ (hHmem _ (hw q.2) q.1).1⟩, (hHmem _ (hw q.2) q.1).2⟩,
      (hFc.subtype_mk _).subtype_mk _⟩
  have hρc : Continuous fun w : Morse.truncation S n => (H 1 ((w : Morse.telescope S) :
      X × ℝ)).1 :=
    continuous_fst.comp (hFc.comp (continuous_const.prodMk continuous_id))
  let ρ : C(Morse.truncation S n, S n) :=
    ⟨fun w => ⟨(H 1 ((w : Morse.telescope S) : X × ℝ)).1, (hH1 _ (hw w)).1⟩, hρc.subtype_mk _⟩
  have hρι : ρ.comp (Morse.truncIncl S n) = ContinuousMap.id _ := by
    ext x
    change (H 1 (((x : X)), (n : ℝ) + ((0 : I) : ℝ))).1 = x
    rw [show ((x : X), (n : ℝ) + ((0 : I) : ℝ)) = ((x : X), (n : ℝ)) by simp,
      hHfix ((x : X), (n : ℝ)) (Set.mk_mem_prod x.2 rfl) 1]
  have hιρ : ((Morse.truncIncl S n).comp ρ).Homotopic (ContinuousMap.id _) := by
    refine ContinuousMap.Homotopic.symm ⟨⟨F, fun w => ?_, fun w => ?_⟩⟩
    · exact Subtype.ext (Subtype.ext (hH0 _ (hw w)))
    · refine Subtype.ext (Subtype.ext (Prod.ext rfl ?_))
      have h2 := (hH1 _ (hw w)).2
      simp only [mem_singleton_iff] at h2
      change (H 1 ((w : Morse.telescope S) : X × ℝ)).2 = (n : ℝ) + ((0 : I) : ℝ)
      rw [h2]
      simp
  have hι : Morse.IsHomotopyEquiv (Morse.truncIncl S n) :=
    ⟨ρ, by rw [hρι], hιρ⟩
  refine ⟨hι, ?_⟩
  have hρ : Morse.IsHomotopyEquiv ρ :=
    Morse.IsHomotopyEquiv.of_inverse (by rw [hρι]) hιρ
  refine hρ.of_homotopic ?_
  have := (ContinuousMap.Homotopic.refl (Morse.truncProj hS n)).comp hιρ
  rw [ContinuousMap.comp_id] at this
  have e : (Morse.truncProj hS n).comp ((Morse.truncIncl S n).comp ρ) = ρ := by
    ext w; rfl
  rw [e] at this
  exact this

/-- `level_le_of_stripMap`, re-proved outright (`B`(c) is only one instance of it). -/
theorem level_le {X : Type} {A : ℕ → Set X} [TopologicalSpace X] (hA : Monotone A) {Z : Type}
    (ℓ : Z → ℝ) (F : ↑(Morse.telescope A) → Z)
    (h₁ : ∀ (n : ℕ) (x : ↑(A n)) (t : I), ℓ (F ((Morse.stripMap A n) (x, t))) ≤ n + 1)
    (h₀ : ∀ (n : ℕ) (x : ↑(A n)), ℓ (F ((Morse.stripMap A n) (x, 0))) ≤ n) {m : ℕ}
    {z : ↑(Morse.telescope A)} (hz : (z : X × ℝ).2 ≤ m) : ℓ (F z) ≤ m := by
  obtain ⟨n, x, t, ht1, rfl⟩ := Morse.exists_stripMap_lt_one hA z
  simp only [Morse.stripMap_apply_snd] at hz
  rcases eq_or_lt_of_le t.2.1 with ht0 | ht0
  · have : t = 0 := Subtype.ext ht0.symm
    subst this
    refine (h₀ n x).trans ?_
    simpa using hz
  · have hnm : (n : ℝ) < m := by linarith
    have hnm' : n + 1 ≤ m := by exact_mod_cast hnm
    refine (h₁ n x t).trans ?_
    exact_mod_cast hnm'

/-- `B ⇒ A`: the two homotopy equivalences from `B`(b); closedness and the general level lemma
outright. -/
theorem B_to_A : B → A := by
  rintro ⟨hB, -⟩
  refine ⟨fun n => isClosed_le (continuous_snd.comp continuous_subtype_val) continuous_const,
    fun hS n => (he_of_dr hS n (hB _ _ hS n).2).1, fun hS n => (he_of_dr hS n (hB _ _ hS n).2).2,
    fun hA => level_le hA⟩

#rt_check RoundTrip.VA_5.A_to_B [Morse.isClosed_truncation, Morse.isHomotopyEquiv_truncIncl, Morse.isHomotopyEquiv_truncProj, Morse.level_le_of_stripMap]
#rt_check RoundTrip.VA_5.B_to_A [Morse.isClosed_truncation, Morse.isHomotopyEquiv_truncIncl, Morse.isHomotopyEquiv_truncProj, Morse.level_le_of_stripMap]
#rt_overlap RoundTrip.VA_5.B_to_A [Morse.isClosed_truncation, Morse.isHomotopyEquiv_truncIncl, Morse.isHomotopyEquiv_truncProj, Morse.level_le_of_stripMap]
#rt_overlap RoundTrip.VA_5.A_to_B [Morse.isClosed_truncation, Morse.isHomotopyEquiv_truncIncl, Morse.isHomotopyEquiv_truncProj, Morse.level_le_of_stripMap]

end RoundTrip.VA_5
