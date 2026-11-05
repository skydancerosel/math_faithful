import Morse
import RoundTrip.Check
import RoundTrip.Blind.VA_6

/-! # Round trip for VA_6 (Milnor, Appendix: Example 1's mechanism, p. 149; end of Case 2, p. 153)

`A` is the conjunction of the types, universes at `0`, of `Morse.isHomotopyDirectLimit_of_level`
(Lemma 2.1: a level function `f ≥ 0` with `f ≥ i + 1` off `X_i` makes `X` a homotopy direct limit
of an increasing sequence) and `Morse.isHomotopyDirectLimit_truncation` (Lemma 2.2: `X_Σ` is the
homotopy direct limit of its truncations, for ANY sequence `A`).

`B` = (1) for increasing `S` and such an `f`: the graph of `f` lies in `X_Σ`, `x ↦ (x, f x)` is an
embedding, and its image is a strong deformation retract of `X_Σ`; (2) for increasing `S`, `X_Σ` is
the homotopy direct limit of `{X_Σ^n}`.

* `A ⇒ B`: (1) is proved outright (straight-line homotopy in `τ`, upward closure (T1),
  Mathlib's `isEmbedding_graph`); (2) is `A`'s Lemma 2.1 applied to the space `X_Σ`, the sequence
  `truncSub S` and `f(x, τ) = τ + 1`.
* `B ⇒ A`: both clauses from `B`(1): a strong deformation retraction `H` of `X_Σ` onto the graph
  makes the section `σ(x) = (x, f x)` a homotopy equivalence (`p σ = id`, `σ (p H₁) = H₁ ≃ id`), so
  `p` is one too; Lemma 2.2 is `B`(1) for the (always increasing) truncations of an arbitrary
  sequence and `f(z) = τ + 1`. -/

namespace RoundTrip.VA_6

open Set

/-- `A`: the two listed theorems, universes at `0`. -/
def A : Prop :=
  (type_of% @Morse.isHomotopyDirectLimit_of_level.{0}) ∧
    (type_of% @Morse.isHomotopyDirectLimit_truncation.{0})

theorem A_holds : A :=
  ⟨Morse.isHomotopyDirectLimit_of_level, Morse.isHomotopyDirectLimit_truncation⟩

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

theorem telProj_eq (S : ℕ → Set X) :
    telProj S = (Morse.telescopeProj S).comp (telHomeo S : C(↥(tel S), ↥(Morse.telescope S))) :=
  rfl

theorem isHE_iff {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q] (f : C(P, Q)) :
    IsHE f ↔ Morse.IsHomotopyEquiv f :=
  ⟨fun ⟨g, h₁, h₂⟩ => ⟨g, h₂, h₁⟩, fun ⟨g, h₁, h₂⟩ => ⟨g, h₂, h₁⟩⟩

theorem isHomotopyEquiv_comp_homeo_iff {P P' Q : Type} [TopologicalSpace P] [TopologicalSpace P']
    [TopologicalSpace Q] (f : C(P, Q)) (e : P' ≃ₜ P) :
    Morse.IsHomotopyEquiv (f.comp (e : C(P', P))) ↔ Morse.IsHomotopyEquiv f := by
  constructor
  · intro h
    have h' := (Morse.IsHomotopyEquiv.of_homeomorph e.symm).comp h
    have : (f.comp (e : C(P', P))).comp (e.symm : C(P, P')) = f := by
      ext x; simp
    rwa [this] at h'
  · intro h
    exact (Morse.IsHomotopyEquiv.of_homeomorph e).comp h

theorem isHDL_iff (S : ℕ → Set X) :
    IsHDL S ↔ Monotone S ∧ Morse.IsHomotopyDirectLimit S := by
  unfold IsHDL Morse.IsHomotopyDirectLimit
  rw [isHE_iff, telProj_eq, isHomotopyEquiv_comp_homeo_iff]

omit [TopologicalSpace X] in
/-- Upward closure (T1) for the blind telescope. -/
theorem mem_tel_of_le {S : ℕ → Set X} (hS : Monotone S) {x : X} {τ τ' : ℝ}
    (h : (x, τ) ∈ tel S) (hle : τ ≤ τ') : (x, τ') ∈ tel S := by
  rw [tel_eq_telescope] at h ⊢
  exact Morse.mem_telescope_of_le hS h hle

omit [TopologicalSpace X] in
theorem graph_mem_tel {S : ℕ → Set X} (f : X → ℝ)
    (hf : ∀ (i : ℕ) (x : X), x ∉ S i → (i : ℝ) + 1 ≤ f x) (hf0 : ∀ x, 0 ≤ f x) (x : X) :
    (x, f x) ∈ tel S := by
  refine ⟨⌊f x⌋₊, ?_, Nat.floor_le (hf0 x), (Nat.lt_floor_add_one (f x)).le⟩
  by_contra h
  linarith [hf _ x h, Nat.lt_floor_add_one (f x)]

end Glue

/-! ### `B`(1) holds outright -/

/-- Claim (1) of `B`, proved without any hypothesis. -/
theorem claim1_holds {X : Type} [TopologicalSpace X] (S : ℕ → Set X) (hS : Monotone S)
    (f : X → ℝ) (hfc : Continuous f) (hf : ∀ (i : ℕ) (x : X), x ∉ S i → (i : ℝ) + 1 ≤ f x)
    (hf0 : ∀ x, 0 ≤ f x) :
    (∀ x, (x, f x) ∈ tel S) ∧ Topology.IsEmbedding (fun x => (x, f x)) ∧
      IsDefRetract (tel S) (Set.range (fun x => (x, f x))) := by
  have hσ := graph_mem_tel f hf hf0
  refine ⟨hσ, isEmbedding_graph hfc, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hσ x
  refine ⟨fun s z => (z.1, (1 - (s : ℝ)) * z.2 + s * f z.1), ?_, ?_, ?_, ?_, ?_⟩
  · refine Continuous.continuousOn ?_
    exact (continuous_fst.comp continuous_snd).prodMk
      (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (continuous_snd.comp continuous_snd)).add
        ((continuous_subtype_val.comp continuous_fst).mul
          (hfc.comp (continuous_fst.comp continuous_snd))))
  · intro z _
    simp
  · intro z _
    exact ⟨z.1, by simp⟩
  · intro z hz s
    have h1 := s.2.1
    have h2 := s.2.2
    rcases le_total z.2 (f z.1) with h | h
    · exact mem_tel_of_le hS hz (by nlinarith)
    · exact mem_tel_of_le hS (hσ z.1) (by nlinarith)
  · rintro _ ⟨x, rfl⟩ s
    simp only [Prod.mk.injEq, true_and]
    ring

/-! ### `A ⇒ B` -/

/-- `A ⇒ B`: claim (1) outright; claim (2) is `A`'s Lemma 2.1 for the space `X_Σ`, the
truncations and `f(x, τ) = τ + 1`. -/
theorem A_to_B : A → B := by
  rintro ⟨hlev, -⟩
  refine ⟨fun X _ S hS f hfc hf hf0 => claim1_holds S hS f hfc hf hf0, ?_⟩
  intro X _ S _
  have hmono : Monotone (truncSub S) := fun m n h z (hz : z.1.2 ≤ m) => by
    change z.1.2 ≤ (n : ℝ)
    exact le_trans hz (by exact_mod_cast h)
  rw [isHDL_iff]
  refine ⟨hmono, hlev hmono ⟨fun z : ↥(tel S) => z.1.2 + 1,
    (continuous_snd.comp continuous_subtype_val).add continuous_const⟩ ?_ ?_⟩
  · intro z
    obtain ⟨i, -, hi, -⟩ := z.2
    change 0 ≤ z.1.2 + 1
    linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  · intro n z hz
    have : (n : ℝ) < z.1.2 := not_le.1 hz
    change (n : ℝ) + 1 ≤ z.1.2 + 1
    linarith

/-! ### `B ⇒ A` -/

/-- From `B`(1): a strong deformation retraction onto the graph of a level function makes the
projection a homotopy equivalence. -/
theorem hdl_of_claim1
    (h1 : ∀ (X : Type) [TopologicalSpace X] (S : ℕ → Set X), Monotone S → ∀ f : X → ℝ,
      Continuous f → (∀ (i : ℕ) (x : X), x ∉ S i → (i : ℝ) + 1 ≤ f x) → (∀ x, 0 ≤ f x) →
        (∀ x, (x, f x) ∈ tel S) ∧ Topology.IsEmbedding (fun x => (x, f x)) ∧
          IsDefRetract (tel S) (Set.range (fun x => (x, f x))))
    {X : Type} [TopologicalSpace X] {S : ℕ → Set X} (hS : Monotone S) (f : C(X, ℝ))
    (hf0 : ∀ x, 0 ≤ f x) (hf : ∀ (n : ℕ), ∀ x ∉ S n, (n : ℝ) + 1 ≤ f x) :
    Morse.IsHomotopyDirectLimit S := by
  obtain ⟨hσ, -, -, H, hHc, hH0, hH1, hHmem, -⟩ :=
    h1 X S hS f f.continuous (fun i x hx => hf i x hx) hf0
  have hT := tel_eq_telescope S
  have hTT : ∀ y : X × ℝ, y ∈ tel S → y ∈ Morse.telescope S := fun y hy => hT ▸ hy
  have hσ' : ∀ x, (x, f x) ∈ Morse.telescope S := fun x => hTT _ (hσ x)
  let σ : C(X, Morse.telescope S) :=
    ⟨fun x => ⟨(x, f x), hσ' x⟩, (continuous_id.prodMk f.continuous).subtype_mk _⟩
  let p := Morse.telescopeProj S
  have hzT : ∀ z : Morse.telescope S, (z : X × ℝ) ∈ tel S := fun z => by rw [hT]; exact z.2
  have hFc : Continuous fun q : unitInterval × Morse.telescope S => H q.1 (q.2 : X × ℝ) := by
    refine hHc.comp_continuous (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      fun q => ⟨mem_univ _, hzT q.2⟩
  let F : C(unitInterval × Morse.telescope S, Morse.telescope S) :=
    ⟨fun q => ⟨H q.1 q.2, hTT _ (hHmem _ (hzT q.2) q.1)⟩, hFc.subtype_mk _⟩
  let r : C(Morse.telescope S, Morse.telescope S) :=
    F.comp ((ContinuousMap.const _ (1 : unitInterval)).prodMk (ContinuousMap.id _))
  have hr : (ContinuousMap.id (Morse.telescope S)).Homotopic r :=
    ⟨⟨F, fun z => Subtype.ext (hH0 _ (hzT z)), fun z => rfl⟩⟩
  have hσpr : σ.comp (p.comp r) = r := by
    ext z
    · obtain ⟨x, hx⟩ := hH1 _ (hzT z)
      change (H 1 (z : X × ℝ)).1 = (H 1 (z : X × ℝ)).1
      rfl
    · obtain ⟨x, hx⟩ := hH1 _ (hzT z)
      change f (H 1 (z : X × ℝ)).1 = (H 1 (z : X × ℝ)).2
      rw [← hx]
  have hσe : Morse.IsHomotopyEquiv σ :=
    Morse.IsHomotopyEquiv.of_leftInv_rightInv (L := p) (R := p.comp r)
      (ContinuousMap.Homotopic.refl _) (by rw [hσpr]; exact hr.symm)
  obtain ⟨g, hg1, hg2⟩ := hσe
  have hg : Morse.IsHomotopyEquiv g := Morse.IsHomotopyEquiv.of_inverse hg1 hg2
  refine hg.of_homotopic ?_
  have := (ContinuousMap.Homotopic.refl p).comp hg2
  rw [ContinuousMap.comp_id] at this
  have e : p.comp (σ.comp g) = g := by ext z; rfl
  rw [e] at this
  exact this

/-- `B ⇒ A`: both clauses from `B`(1). -/
theorem B_to_A : B → A := by
  rintro ⟨h1, -⟩
  refine ⟨fun hS f hf0 hf => hdl_of_claim1 h1 hS f hf0 hf, ?_⟩
  intro X S _
  have hmono : Monotone (Morse.truncation S) := fun m n h z (hz : (z : X × ℝ).2 ≤ m) => by
    change (z : X × ℝ).2 ≤ (n : ℝ)
    exact le_trans hz (by exact_mod_cast h)
  refine hdl_of_claim1 h1 hmono ⟨fun z : Morse.telescope S => (z : X × ℝ).2 + 1,
    (continuous_snd.comp continuous_subtype_val).add continuous_const⟩ ?_ ?_
  · intro z
    have := Morse.nonneg_of_mem_telescope z.2
    change 0 ≤ (z : X × ℝ).2 + 1
    linarith
  · intro n z hz
    have : (n : ℝ) < (z : X × ℝ).2 := not_le.1 hz
    change (n : ℝ) + 1 ≤ (z : X × ℝ).2 + 1
    linarith

#rt_check RoundTrip.VA_6.A_to_B [Morse.isHomotopyDirectLimit_of_level, Morse.isHomotopyDirectLimit_truncation]
#rt_check RoundTrip.VA_6.B_to_A [Morse.isHomotopyDirectLimit_of_level, Morse.isHomotopyDirectLimit_truncation]
#rt_overlap RoundTrip.VA_6.B_to_A [Morse.isHomotopyDirectLimit_of_level, Morse.isHomotopyDirectLimit_truncation]
#rt_overlap RoundTrip.VA_6.A_to_B [Morse.isHomotopyDirectLimit_of_level, Morse.isHomotopyDirectLimit_truncation]

end RoundTrip.VA_6
