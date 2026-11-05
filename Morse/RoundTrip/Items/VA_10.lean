import Morse
import RoundTrip.Check
import RoundTrip.Blind.VA_10

/-! # Round trip for VA_10 (Milnor, Appendix pp. 150–152: Theorem A, Case 1; the misprint)

`A` is the conjunction of the types, universes at `0`, of `Morse.case1Map_zero`
(`h_0 = f_Σ ∘ R₂`), `Morse.case1Map_one` (`h_1` has Milnor's two properties) and
`Morse.theoremA_case1` (Case 1: `f_Σ` is a homotopy equivalence). All three assume every `X_n`
CLOSED; the project's `h_u` (`Morse.case1Fun`) has the misprint corrected (`(4t − 3)u`).

`B` (blind, misprint also corrected, so no `not_B`): for an increasing `S`, with NO closedness,
(a) `f_Σ` is a homotopy equivalence; (b) Milnor's formula `h_u` defines a continuous homotopy
`K` from `k₀` to `k₁`; (c) `k₀ ≃ f_Σ`; (d) `k₁` has the properties of VA.9.

* `B ⇒ A`: `theoremA_case1` is `B`(a) for closed sets (glue: `tel S ≃ₜ telescope S`, `resC` vs
  `restrictTo`); `case1Map_zero` and `case1Map_one` are identities/properties of the project's
  own map `case1Map`, re-proved outright (`B` speaks of its own `K`, not of `case1Map`).
* `A ⇒ B`: `B` drops closedness, so `A` cannot be applied to `S` itself.
  (a) `A`'s `theoremA_case1` is applied to the space `X_Σ` and its truncations `X^n_Σ` (always
  closed), on which `f_Σ` is homotopic to the identity through (T2); then `X_Σ` is the homotopy
  direct limit of its truncations (Lemma 2.2) and `of_telescopeMap` (VA_4) gives `f_Σ`.
  (b)–(d) are proved directly: the continuity of `h_u` WITHOUT closedness holds because near an
  integer level `m` all points lie over `X_m` and the formula only involves `h^m` there (the last
  piece `h^{m}_{(4t−3)u}` of strip `m − 1` and the first piece `h^m_u` of strip `m` paste along
  `τ = m`), while inside a strip the project's `Morse.continuous_case1Fun` applies. -/

namespace RoundTrip.VA_10

open Set Filter Topology
open scoped unitInterval

/-- `A`: the three listed theorems, universes at `0`. -/
def A : Prop :=
  (type_of% @Morse.case1Map_zero.{0}) ∧ (type_of% @Morse.case1Map_one.{0}) ∧
    (type_of% @Morse.theoremA_case1.{0})

theorem A_holds : A :=
  ⟨Morse.case1Map_zero, Morse.case1Map_one, Morse.theoremA_case1⟩

/-! ### Glue -/

section Glue

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

omit [TopologicalSpace X] in
theorem tel_eq_telescope (S : ℕ → Set X) : tel S = Morse.telescope S := by
  ext z
  simp only [tel, Morse.telescope, mem_iUnion, mem_prod, mem_Icc]; rfl

/-- The identity homeomorphism `tel S ≃ₜ telescope S`. -/
noncomputable def telHomeo (S : ℕ → Set X) : ↥(tel S) ≃ₜ ↥(Morse.telescope S) :=
  Homeomorph.setCongr (tel_eq_telescope S)

theorem fSig_eq (f : C(X, Y)) {S : ℕ → Set X} {T : ℕ → Set Y} (h : ∀ i, ∀ x ∈ S i, f x ∈ T i) :
    fSig f h = ((telHomeo T).symm : C(↥(Morse.telescope T), ↥(tel T))).comp
      ((Morse.telescopeMap f (fun i _ hx => h i _ hx)).comp
        (telHomeo S : C(↥(tel S), ↥(Morse.telescope S)))) :=
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

theorem isHomotopyEquiv_homeo_comp_iff {P Q Q' : Type} [TopologicalSpace P] [TopologicalSpace Q']
    [TopologicalSpace Q] (f : C(P, Q)) (e : Q ≃ₜ Q') :
    Morse.IsHomotopyEquiv ((e : C(Q, Q')).comp f) ↔ Morse.IsHomotopyEquiv f := by
  constructor
  · intro h
    have h' := h.comp (Morse.IsHomotopyEquiv.of_homeomorph e.symm)
    have : (e.symm : C(Q', Q)).comp ((e : C(Q, Q')).comp f) = f := by
      ext x; simp
    rwa [this] at h'
  · intro h
    exact h.comp (Morse.IsHomotopyEquiv.of_homeomorph e)

theorem isHE_fSig_iff (f : C(X, Y)) {S : ℕ → Set X} {T : ℕ → Set Y}
    (h : ∀ i, ∀ x ∈ S i, f x ∈ T i) :
    IsHE (fSig f h) ↔ Morse.IsHomotopyEquiv (Morse.telescopeMap f (fun i _ hx => h i _ hx)) := by
  rw [isHE_iff, fSig_eq, isHomotopyEquiv_homeo_comp_iff, isHomotopyEquiv_comp_homeo_iff]

end Glue

/-! ### `B ⇒ A` -/

section BtoA

open Morse

variable {X : Type} [TopologicalSpace X] {S : ℕ → Set X} {φ : C(X, X)}
  {hφ : ∀ n, MapsTo φ (S n) (S n)}

/-- `case1Map_zero`, re-proved outright (a computation on the strips). -/
theorem case1Map_zero' (hA : Monotone S) (hAc : ∀ n, IsClosed (S n))
    (H : ∀ n, (restrictTo φ (hφ n)).Homotopy (ContinuousMap.id (S n))) :
    case1Map hA hAc H 0 = (telescopeMap φ hφ).comp (scaleMap hA hAc 2 (by norm_num)) := by
  refine telescope_ext' fun n x t => ?_
  rw [case1Map_stripMap, ContinuousMap.comp_apply, scaleMap_stripMap, telescopeMap_stripMap]
  unfold case1Fun
  split_ifs with h1 h2
  · rw [(H n).apply_zero]
  · rw [Set.Icc.coe_zero, mul_zero, clampI_zero, (H n).apply_zero, ← stripMap_one hA,
      clampI_of_one_le (by linarith)]
  · rw [Set.Icc.coe_zero, mul_zero, clampI_zero, (H (n + 1)).apply_zero,
      clampI_of_one_le (by linarith), stripMap_one hA]
    rfl

/-- `case1Map_one`, re-proved outright. -/
theorem case1Map_one' (hA : Monotone S) (hAc : ∀ n, IsClosed (S n))
    (H : ∀ n, (restrictTo φ (hφ n)).Homotopy (ContinuousMap.id (S n))) :
    IsMilnorMap (case1Map hA hAc H 1) where
  low n x t ht := by
    rw [case1Map_stripMap]
    unfold case1Fun
    rw [if_pos ht, (H n).apply_one]
    rfl
  high n x t ht := by
    rw [case1Map_stripMap]
    unfold case1Fun
    split_ifs with h1 h2
    · rw [stripMap_apply_snd, show (t : ℝ) = 1 / 2 by linarith,
        show (2 : ℝ) * (1 / 2) = 1 by norm_num, clampI_one]
      simp
    · simp
    · simp

end BtoA

/-- `B ⇒ A`: Case 1 from `B`(a) (closed sets are a special case); the two strip computations
outright. -/
theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun hA hAc H => case1Map_zero' hA hAc H, fun hA hAc H => case1Map_one' hA hAc H, ?_⟩
  intro X _ S φ hφ hA _ hφe
  have hf : ∀ i, ∀ x ∈ S i, φ x ∈ S i := fun i x hx => hφ i hx
  have := (hB X S hA φ hf (fun n => (hφe n).some)).1
  exact (isHE_fSig_iff φ hf).1 this

#rt_check RoundTrip.VA_10.B_to_A [Morse.case1Map_zero, Morse.case1Map_one, Morse.theoremA_case1]
#rt_overlap RoundTrip.VA_10.B_to_A [Morse.case1Map_zero, Morse.case1Map_one, Morse.theoremA_case1]

/-! ### `A ⇒ B` -/

section AtoB

variable {X : Type} [TopologicalSpace X] {S : ℕ → Set X} (hS : Monotone S) (f : C(X, X))
  (hf : ∀ i, ∀ x ∈ S i, f x ∈ S i)
  (H : ∀ n, ContinuousMap.Homotopy (resC f (hf n)) (ContinuousMap.id ↥(S n)))

include hS H in
/-- (a) `f_Σ` is a homotopy equivalence, for any increasing `S`: `A`'s Case 1 applied to the space
`X_Σ` and its (closed) truncations. -/
theorem he_fSig (hcase1 : type_of% @Morse.theoremA_case1.{0}) : IsHE (fSig f hf) := by
  rw [isHE_fSig_iff]
  set F := Morse.telescopeMap f (fun i _ hx => hf i _ hx)
  have hF : ∀ m, MapsTo F (Morse.truncation S m) (Morse.truncation S m) := fun m z hz => hz
  refine Morse.IsHomotopyEquiv.of_telescopeMap (hf := hF) Morse.isHomotopyDirectLimit_truncation
    Morse.isHomotopyDirectLimit_truncation
      (hcase1 (hφ := hF) Morse.monotone_truncation Morse.isClosed_truncation ?_)
  intro m
  set ι := Morse.truncIncl S m
  set r := Morse.truncProj hS m
  set Fm := Morse.restrictTo F (hF m)
  have hT2 := Morse.truncIncl_comp_truncProj hS m
  have hcomm : Fm.comp ι = ι.comp (resC f (hf m)) := ContinuousMap.ext fun x => rfl
  have h1 : Fm.Homotopic ((Fm.comp ι).comp r) := by
    have := (ContinuousMap.Homotopic.refl Fm).comp hT2.symm
    rwa [ContinuousMap.comp_id] at this
  have h2 : ((ι.comp (resC f (hf m))).comp r).Homotopic (ι.comp r) := by
    have := ((ContinuousMap.Homotopic.refl ι).comp ⟨H m⟩).comp (ContinuousMap.Homotopic.refl r)
    rwa [ContinuousMap.comp_id] at this
  rw [hcomm] at h1
  exact (h1.trans h2).trans hT2

omit [TopologicalSpace X] in
theorem nonneg_of_tel {z : X × ℝ} (hz : z ∈ tel S) : 0 ≤ z.2 := by
  obtain ⟨i, -, hi, -⟩ := hz
  exact le_trans (Nat.cast_nonneg i) hi

include hS in
omit [TopologicalSpace X] in
theorem mem_of_lt {z : X × ℝ} (hz : z ∈ tel S) {m : ℕ} (h : z.2 < m + 1) : z.1 ∈ S m := by
  obtain ⟨i, hi, h1, -⟩ := hz
  have : (i : ℝ) < m + 1 := lt_of_le_of_lt h1 h
  have : i < m + 1 := by exact_mod_cast this
  exact hS (by omega) hi

/-- Milnor's `h_u` written with an explicit level `n = ⌊τ⌋`. -/
theorem hmapSig_of_floor (u : I) (z : ↥(tel S)) (n : ℕ) (hn : ⌊z.1.2⌋₊ = n)
    (hx : z.1.1 ∈ S n) :
    hmapSig hS f hf H u z =
      if z.1.2 - n ≤ 1 / 2 then (((H n (u, ⟨z.1.1, hx⟩)) : X), (n : ℝ) + 2 * (z.1.2 - n))
      else if z.1.2 - n ≤ 3 / 4 then
        (((H n (Set.projIcc (0 : ℝ) 1 zero_le_one ((3 - 4 * (z.1.2 - n)) * u), ⟨z.1.1, hx⟩)) : X),
          (n : ℝ) + 1)
      else (((H (n + 1) (Set.projIcc (0 : ℝ) 1 zero_le_one ((4 * (z.1.2 - n) - 3) * u),
          ⟨z.1.1, hS (Nat.le_succ n) hx⟩)) : X), (n : ℝ) + 1) := by
  subst hn
  rfl

theorem hmapSig_mem (u : I) (z : ↥(tel S)) : hmapSig hS f hf H u z ∈ tel S := by
  have h0 := nonneg_of_tel z.2
  have hk : (⌊z.1.2⌋₊ : ℝ) ≤ z.1.2 := Nat.floor_le h0
  unfold hmapSig
  split_ifs with h1 h2
  · exact ⟨⌊z.1.2⌋₊, (H _ _).2, by simp only; linarith, by simp only; linarith⟩
  · exact ⟨⌊z.1.2⌋₊, (H _ _).2, by simp only; linarith, le_rfl⟩
  · exact ⟨⌊z.1.2⌋₊ + 1, (H _ _).2, by push_cast; exact le_rfl, by push_cast; linarith⟩

/-- The local formula of `h_u` near the integer level `m` (only `h^m` is involved). -/
noncomputable def Phi (m : ℕ) (q : I × (↥(S m) × ℝ)) : X × ℝ :=
  (((H m (Set.projIcc (0 : ℝ) 1 zero_le_one ((q.1 : ℝ) * min 1 (4 * (q.2.2 - m) + 1)), q.2.1)) :
    X), max (m : ℝ) (m + 2 * (q.2.2 - m)))

theorem continuous_Phi (m : ℕ) : Continuous (Phi f hf H m) := by
  have hτ : Continuous fun q : I × (↥(S m) × ℝ) => q.2.2 := continuous_snd.comp continuous_snd
  refine Continuous.prodMk ?_ (continuous_const.max (continuous_const.add
    (continuous_const.mul (hτ.sub continuous_const))))
  refine continuous_subtype_val.comp ((H m).continuous.comp (Continuous.prodMk ?_
    (continuous_fst.comp continuous_snd)))
  exact continuous_projIcc.comp ((continuous_subtype_val.comp continuous_fst).mul
    (continuous_const.min ((continuous_const.mul (hτ.sub continuous_const)).add continuous_const)))

theorem hmapSig_eq_Phi (u : I) (z : ↥(tel S)) (m : ℕ) (h1 : (m : ℝ) - 1 / 4 < z.1.2)
    (h2 : z.1.2 < m + 1 / 4) (hx : z.1.1 ∈ S m) :
    hmapSig hS f hf H u z = Phi f hf H m (u, (⟨z.1.1, hx⟩, z.1.2)) := by
  have h0 := nonneg_of_tel z.2
  rcases lt_or_ge z.1.2 m with hlt | hge
  · -- just below the level `m = k + 1`: last piece of strip `k`
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := by
      rcases m with _ | k
      · exfalso; simp at hlt; linarith
      · exact ⟨k, rfl⟩
    push_cast at h1 h2 hlt ⊢
    have hfl : ⌊z.1.2⌋₊ = k := by
      rw [Nat.floor_eq_iff h0]
      constructor <;> linarith
    have hxk : z.1.1 ∈ S k := mem_of_lt hS z.2 (by linarith)
    rw [hmapSig_of_floor hS f hf H u z k hfl hxk, if_neg (by linarith), if_neg (by linarith)]
    unfold Phi
    simp only
    have hmin : min (1 : ℝ) (4 * (z.1.2 - (k + 1 : ℕ)) + 1) = 4 * (z.1.2 - k) - 3 := by
      push_cast
      rw [min_eq_right (by linarith)]
      ring
    have hmax : max ((k + 1 : ℕ) : ℝ) ((k + 1 : ℕ) + 2 * (z.1.2 - (k + 1 : ℕ))) = k + 1 := by
      push_cast
      rw [max_eq_left (by linarith)]
    rw [hmin, hmax, mul_comm]
  · -- at or just above the level `m`: first piece of strip `m`
    have hfl : ⌊z.1.2⌋₊ = m := by
      rw [Nat.floor_eq_iff h0]
      constructor <;> linarith
    rw [hmapSig_of_floor hS f hf H u z m hfl hx, if_pos (by linarith)]
    unfold Phi
    simp only
    have hmin : min (1 : ℝ) (4 * (z.1.2 - m) + 1) = 1 := min_eq_left (by linarith)
    have hmax : max (m : ℝ) (m + 2 * (z.1.2 - m)) = m + 2 * (z.1.2 - m) :=
      max_eq_right (by linarith)
    rw [hmin, hmax, mul_one, Set.projIcc_of_mem _ ⟨u.2.1, u.2.2⟩]

/-- Inside a strip, `h_u` is the project's strip formula `Morse.case1Fun`. -/
theorem hmapSig_eq_case1Fun (u : I) (z : ↥(tel S)) (k : ℕ) (h1 : (k : ℝ) < z.1.2)
    (h2 : z.1.2 < k + 1) (hx : z.1.1 ∈ S k) :
    hmapSig hS f hf H u z = ((Morse.case1Fun (φ := f) (hφ := fun n x hx => hf n x hx) hS H k
      (u, (⟨z.1.1, hx⟩, ⟨z.1.2 - k, by linarith, by linarith⟩)) : ↥(Morse.telescope S)) :
        X × ℝ) := by
  have h0 := nonneg_of_tel z.2
  have hfl : ⌊z.1.2⌋₊ = k := by
    rw [Nat.floor_eq_iff h0]
    constructor <;> linarith
  rw [hmapSig_of_floor hS f hf H u z k hfl hx]
  unfold Morse.case1Fun
  dsimp only
  split_ifs with ha hb
  · refine Prod.ext rfl ?_
    change (k : ℝ) + 2 * (z.1.2 - k) = k + (Morse.clampI (2 * (z.1.2 - k)) : ℝ)
    rw [Morse.clampI_val (by linarith) (by linarith)]
  · refine Prod.ext rfl ?_
    change (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) + ((0 : I) : ℝ)
    push_cast; simp
  · refine Prod.ext rfl ?_
    change (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) + ((0 : I) : ℝ)
    push_cast; simp

theorem continuous_hmap : Continuous fun q : I × ↥(tel S) => hmapSig hS f hf H q.1 q.2 := by
  have hτ : Continuous fun q : I × ↥(tel S) => q.2.1.2 :=
    continuous_snd.comp (continuous_subtype_val.comp continuous_snd)
  have hxc : Continuous fun q : I × ↥(tel S) => q.2.1.1 :=
    continuous_fst.comp (continuous_subtype_val.comp continuous_snd)
  rw [continuous_iff_continuousAt]
  rintro ⟨u₀, z₀⟩
  have h0 := nonneg_of_tel z₀.2
  by_cases hint : ∃ m : ℕ, z₀.1.2 = m
  · obtain ⟨m, hm⟩ := hint
    let W : Set (I × ↥(tel S)) := {q | (m : ℝ) - 1 / 4 < q.2.1.2 ∧ q.2.1.2 < m + 1 / 4}
    have hWo : IsOpen W := (isOpen_lt continuous_const hτ).inter (isOpen_lt hτ continuous_const)
    have hW0 : (u₀, z₀) ∈ W := by
      change (m : ℝ) - 1 / 4 < z₀.1.2 ∧ z₀.1.2 < m + 1 / 4
      rw [hm]; constructor <;> linarith
    refine ContinuousOn.continuousAt ?_ (hWo.mem_nhds hW0)
    rw [continuousOn_iff_continuous_domRestrict]
    have hxm : ∀ q : W, q.1.2.1.1 ∈ S m := fun q => mem_of_lt hS q.1.2.2 (by linarith [q.2.2])
    have heq : W.domRestrict (fun q : I × ↥(tel S) => hmapSig hS f hf H q.1 q.2) =
        fun q : W => Phi f hf H m (q.1.1, (⟨q.1.2.1.1, hxm q⟩, q.1.2.1.2)) := by
      funext q
      exact hmapSig_eq_Phi hS f hf H q.1.1 q.1.2 m q.2.1 q.2.2 (hxm q)
    rw [heq]
    refine (continuous_Phi f hf H m).comp ((continuous_fst.comp continuous_subtype_val).prodMk
      (Continuous.prodMk ?_ (hτ.comp continuous_subtype_val)))
    exact (hxc.comp continuous_subtype_val).subtype_mk _
  · push Not at hint
    set k := ⌊z₀.1.2⌋₊ with hkdef
    have hk1 : (k : ℝ) < z₀.1.2 := lt_of_le_of_ne (Nat.floor_le h0) (fun h => hint k h.symm)
    have hk2 : z₀.1.2 < k + 1 := Nat.lt_floor_add_one _
    let W : Set (I × ↥(tel S)) := {q | (k : ℝ) < q.2.1.2 ∧ q.2.1.2 < k + 1}
    have hWo : IsOpen W := (isOpen_lt continuous_const hτ).inter (isOpen_lt hτ continuous_const)
    have hW0 : (u₀, z₀) ∈ W := ⟨hk1, hk2⟩
    refine ContinuousOn.continuousAt ?_ (hWo.mem_nhds hW0)
    rw [continuousOn_iff_continuous_domRestrict]
    have hxk : ∀ q : W, q.1.2.1.1 ∈ S k := fun q => mem_of_lt hS q.1.2.2 q.2.2
    have heq : W.domRestrict (fun q : I × ↥(tel S) => hmapSig hS f hf H q.1 q.2) =
        fun q : W => ((Morse.case1Fun (φ := f) (hφ := fun n x hx => hf n x hx) hS H k
          (q.1.1, (⟨q.1.2.1.1, hxk q⟩, ⟨q.1.2.1.2 - k, by linarith [q.2.1], by linarith [q.2.2]⟩)) :
            ↥(Morse.telescope S)) : X × ℝ) := by
      funext q
      exact hmapSig_eq_case1Fun hS f hf H q.1.1 q.1.2 k q.2.1 q.2.2 (hxk q)
    rw [heq]
    refine continuous_subtype_val.comp ((Morse.continuous_case1Fun (φ := f)
      (hφ := fun n x hx => hf n x hx) hS H k).comp ((continuous_fst.comp
        continuous_subtype_val).prodMk (Continuous.prodMk ?_ ?_)))
    · exact (hxc.comp continuous_subtype_val).subtype_mk _
    · exact ((hτ.comp continuous_subtype_val).sub continuous_const).subtype_mk _

/-- Milnor's homotopy `(u, z) ↦ h_u(z)`, continuous without any closedness. -/
noncomputable def Kmap : C(I × ↥(tel S), ↥(tel S)) :=
  ⟨fun q => ⟨hmapSig hS f hf H q.1 q.2, hmapSig_mem hS f hf H q.1 q.2⟩,
    (continuous_hmap hS f hf H).subtype_mk _⟩

/-- `h_u` at a fixed time. -/
noncomputable def kAt (u : I) : C(↥(tel S), ↥(tel S)) :=
  (Kmap hS f hf H).comp ((ContinuousMap.const _ u).prodMk (ContinuousMap.id _))

/-- The homotopy `h_0 ≃ h_1`. -/
noncomputable def Khom : (kAt hS f hf H 0).Homotopy (kAt hS f hf H 1) :=
  ⟨Kmap hS f hf H, fun _ => rfl, fun _ => rfl⟩

omit [TopologicalSpace X] in
include hS in
theorem mem_tel_of_le {x : X} {τ τ' : ℝ} (h : (x, τ) ∈ tel S) (hle : τ ≤ τ') :
    (x, τ') ∈ tel S := by
  rw [tel_eq_telescope] at h ⊢
  exact Morse.mem_telescope_of_le hS h hle

theorem hmap_zero (z : ↥(tel S)) :
    (hmapSig hS f hf H 0 z).1 = f z.1.1 ∧ z.1.2 ≤ (hmapSig hS f hf H 0 z).2 := by
  have h0 := nonneg_of_tel z.2
  have hk : (⌊z.1.2⌋₊ : ℝ) ≤ z.1.2 := Nat.floor_le h0
  have hk1 : z.1.2 < ⌊z.1.2⌋₊ + 1 := Nat.lt_floor_add_one _
  have hp : ∀ c : ℝ, Set.projIcc (0 : ℝ) 1 zero_le_one (c * ((0 : I) : ℝ)) = 0 := fun c => by
    rw [Set.Icc.coe_zero, mul_zero, Set.projIcc_left]; rfl
  unfold hmapSig
  split_ifs with h1 h2
  · refine ⟨?_, by simp only; linarith⟩
    simp only
    rw [(H _).apply_zero]
    rfl
  · refine ⟨?_, by simp only; linarith⟩
    simp only
    rw [hp, (H _).apply_zero]
    rfl
  · refine ⟨?_, by simp only; linarith⟩
    simp only
    rw [hp, (H _).apply_zero]
    rfl

/-- (c) `h_0 ≃ f_Σ`: straight-line homotopy in the level (`h_0(x, τ) = (f x, ρ(τ))`, `ρ(τ) ≥ τ`). -/
theorem kAt_zero_homotopic : (kAt hS f hf H 0).Homotopic (fSig f hf) := by
  have hL : Continuous fun z : ↥(tel S) => (hmapSig hS f hf H 0 z).2 :=
    continuous_snd.comp ((continuous_hmap hS f hf H).comp
      (continuous_const.prodMk continuous_id))
  have hmem : ∀ q : I × ↥(tel S), (f q.2.1.1, (1 - (q.1 : ℝ)) * (hmapSig hS f hf H 0 q.2).2 +
      q.1 * q.2.1.2) ∈ tel S := by
    intro q
    refine mem_tel_of_le hS (fSig_mem f hf q.2) ?_
    have := (hmap_zero hS f hf H q.2).2
    nlinarith [q.1.2.1, q.1.2.2]
  refine ⟨⟨⟨fun q => ⟨_, hmem q⟩, ?_⟩, fun z => ?_, fun z => ?_⟩⟩
  · refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
    · exact f.continuous.comp (continuous_fst.comp (continuous_subtype_val.comp continuous_snd))
    · exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (hL.comp continuous_snd)).add ((continuous_subtype_val.comp continuous_fst).mul
          (continuous_snd.comp (continuous_subtype_val.comp continuous_snd)))
  · refine Subtype.ext (Prod.ext ?_ ?_)
    · exact ((hmap_zero hS f hf H z).1).symm
    · change (1 - ((0 : I) : ℝ)) * (hmapSig hS f hf H 0 z).2 + ((0 : I) : ℝ) * z.1.2 =
        (hmapSig hS f hf H 0 z).2
      simp
  · refine Subtype.ext (Prod.ext rfl ?_)
    change (1 - ((1 : I) : ℝ)) * (hmapSig hS f hf H 0 z).2 + ((1 : I) : ℝ) * z.1.2 = z.1.2
    simp

/-- (d) `h_1` has Milnor's properties (VA.9). -/
theorem isH1_kAt_one : IsH1 S (kAt hS f hf H 1) := by
  constructor
  · intro z n t ht0 ht1 hzt
    have hfl : ⌊z.1.2⌋₊ = n := by
      rw [Nat.floor_eq_iff (nonneg_of_tel z.2), hzt]
      constructor <;> linarith
    have hx : z.1.1 ∈ S n := mem_of_lt hS z.2 (by rw [hzt]; linarith)
    change hmapSig hS f hf H 1 z = _
    rw [hmapSig_of_floor hS f hf H 1 z n hfl hx, if_pos (by rw [hzt]; linarith), (H n).apply_one,
      hzt]
    simp only [ContinuousMap.id_apply, Prod.mk.injEq, true_and]
    ring
  · intro z n t ht0 ht1 hzt
    change (hmapSig hS f hf H 1 z).1 ∈ S (n + 1) ∧ (hmapSig hS f hf H 1 z).2 = n + 1
    rcases eq_or_lt_of_le ht1 with rfl | ht1'
    · have hfl : ⌊z.1.2⌋₊ = n + 1 := by
        rw [Nat.floor_eq_iff (nonneg_of_tel z.2), hzt]
        push_cast; constructor <;> linarith
      have hx : z.1.1 ∈ S (n + 1) := mem_of_lt hS z.2 (by rw [hzt]; push_cast; linarith)
      rw [hmapSig_of_floor hS f hf H 1 z (n + 1) hfl hx,
        if_pos (by rw [hzt]; push_cast; linarith), (H _).apply_one]
      refine ⟨hx, ?_⟩
      simp only [hzt]
      push_cast; ring
    · have hfl : ⌊z.1.2⌋₊ = n := by
        rw [Nat.floor_eq_iff (nonneg_of_tel z.2), hzt]
        constructor <;> linarith
      have hx : z.1.1 ∈ S n := mem_of_lt hS z.2 (by rw [hzt]; linarith)
      rw [hmapSig_of_floor hS f hf H 1 z n hfl hx]
      split_ifs with h1 h2
      · refine ⟨hS (Nat.le_succ n) (H n _).2, ?_⟩
        simp only
        rw [hzt] at h1 ⊢
        have : t = 1 / 2 := by linarith
        subst this; ring
      · exact ⟨hS (Nat.le_succ n) (H n _).2, rfl⟩
      · exact ⟨(H (n + 1) _).2, rfl⟩

end AtoB

/-- **`A ⇒ B`** (`B` has no closedness hypothesis): (a) from `A`'s `theoremA_case1` applied to the
truncations; (b)–(d) directly (continuity of `h_u` by a local argument, without closedness). -/
theorem A_to_B : A → B := by
  rintro ⟨-, -, hcase1⟩ X _ S hS f hf H
  exact ⟨he_fSig hS f hf H hcase1, kAt hS f hf H 0, kAt hS f hf H 1, Khom hS f hf H,
    fun _ _ => rfl, kAt_zero_homotopic hS f hf H, isH1_kAt_one hS f hf H⟩

#rt_check RoundTrip.VA_10.A_to_B [Morse.case1Map_zero, Morse.case1Map_one, Morse.theoremA_case1]
#rt_overlap RoundTrip.VA_10.A_to_B [Morse.case1Map_zero, Morse.case1Map_one, Morse.theoremA_case1]

end RoundTrip.VA_10
